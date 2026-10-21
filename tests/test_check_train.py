#!/usr/bin/env python3
"""Check trains in temporary git repositories, without Lean or network access.

    python3 -I tests/test_check_train.py

Fixtures use hash-object, mktree and commit-tree. They do not stage files, create
branches or alter the source repository's history.
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

sys.dont_write_bytecode = True
SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
import check_train as train  # noqa: E402


LEAN = "Elements/BookI/Prop01.lean"
CHECK = "scripts/check_sample.py"
ENTRY = "docs/decisions/2026-10-20-sample.md"


def member_row(head: str, branch: str = "content/one", **cells) -> dict:
    """A written row whose evidence names the supplied head."""
    return {
        "branch": branch,
        "head": head,
        "code_review": f"Independent reader at {head}: PASS, no findings.",
        "security_review": "Not required: no protected path changed.",
        "no_mistakes": f"passed at {head} (run local-01)",
        **cells,
    }


def body(rows: list[dict], new: str = "- propositions: I.1") -> str:
    """The two required sections, with the supplied rows and declarations."""
    lines = ["## Members", "", "| " + " | ".join(train.HEADINGS) + " |",
             "|---|---|---|---|---|"]
    lines.extend("| " + " | ".join(row[key] for key in train.FIELDS) + " |" for row in rows)
    return "\n".join(lines) + "\n\n## What is new\n\n" + new + "\n"


class Repository(unittest.TestCase):
    """Each test owns an isolated object database and its git configuration."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        env.update({
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_AUTHOR_NAME": "Train fixture",
            "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
            "GIT_COMMITTER_NAME": "Train fixture",
            "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
            "GIT_AUTHOR_DATE": "2026-10-20T12:00:00+00:00",
            "GIT_COMMITTER_DATE": "2026-10-20T12:00:00+00:00",
            "GIT_TERMINAL_PROMPT": "0",
            "GIT_ALLOW_PROTOCOL": "",
        })
        environment = patch.dict(os.environ, env, clear=True)
        environment.start()
        self.addCleanup(environment.stop)
        self.git("init", "--bare", "--quiet", "--initial-branch=main")
        self.trees = {}
        self.serial = 0
        self.base = self.commit([], {
            LEAN: "-- source at the base\n",
            CHECK: "print('base')\n",
            train.DECISIONS: "## 20 October 2026\n\nA previous decision.\n",
            # Main has the decision entries' directory, as once tooling/decision-entries
            # lands; test_decision_entries_need_their_directory_on_main removes it.
            "docs/decisions/README.md": "Decision entries, one to a file.\n",
            "docs/STYLE.md": "The guide at the base.\n",
            "facts.json": "{}\n",
            "tests/model/MODEL.md": "The account at the base.\n",
        })
        self.member = self.commit([self.base], {LEAN: "-- reviewed source\n"})
        self.head = self.merge(self.base, self.member)
        self.row = member_row(self.member)
        self.body = body([self.row])

    def git(self, *args: str, data: str | None = None, codes=(0,)) -> str:
        """Run only a local fixture command, raising on an unexpected status."""
        result = subprocess.run(["git", *args], cwd=self.repo, input=data,
                                capture_output=True, text=True)
        if result.returncode not in codes:
            raise AssertionError(f"git {args!r}: {result.returncode}: {result.stderr}")
        return result.stdout

    def tree(self, files: dict) -> str:
        """Build nested trees from file text without an index or a checkout."""
        root = {}
        for path, text in files.items():
            node = root
            parts = path.split("/")
            for part in parts[:-1]:
                node = node.setdefault(part, {})
            node[parts[-1]] = text

        def write(node):
            entries = []
            for name, value in sorted(node.items()):
                if isinstance(value, dict):
                    oid, mode, kind = write(value), "040000", "tree"
                else:
                    oid = self.git("hash-object", "-w", "--stdin", data=value).strip()
                    mode, kind = "100644", "blob"
                entries.append(f"{mode} {kind} {oid}\t{name}\0")
            return self.git("mktree", "-z", data="".join(entries)).strip()

        return write(root)

    def commit(self, parents: list[str], changes: dict | None = None, tree=None) -> str:
        """Write one fixture commit, optionally with an explicitly chosen tree."""
        files = dict(self.trees[parents[0]]) if parents else {}
        for path, value in (changes or {}).items():
            if value is None:
                files.pop(path, None)
            else:
                files[path] = value
        if tree is None:
            tree = self.tree(files)
        else:
            paths = self.git("ls-tree", "-r", "--name-only", "-z", tree).split("\0")
            files = {path: self.git("show", f"{tree}:{path}") for path in paths if path}
        self.serial += 1
        args = ["commit-tree", tree]
        for parent in parents:
            args.extend(("-p", parent))
        sha = self.git(*args, data=f"Fixture {self.serial}\n").strip()
        self.trees[sha] = files
        return sha

    def merge(self, first: str, second: str) -> str:
        """Write a clean two-parent merge with git's automatic tree."""
        tree = self.git("merge-tree", "--write-tree", first, second).strip()
        return self.commit([first, second], tree=tree)

    def problems(self, head=None, text=None, base=None) -> list[str]:
        """Run the public check against the chosen fixture revision and body."""
        return train.check_train(self.repo, base or self.base, head or self.head,
                                 self.body if text is None else text)

    def refused(self, message: str, **kwargs):
        """A planted fault must be refused with its own diagnostic."""
        problems = self.problems(**kwargs)
        self.assertTrue(any(message in problem for problem in problems), problems)

    def cli(self, text=None, head=None, missing=False, raw=None):
        """Run the real command-line entry point in the fixture repository."""
        path = self.root / "body.md"
        if not missing:
            path.write_bytes(raw if raw is not None else
                             (self.body if text is None else text).encode())
        return subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPTS / "check_train.py"),
             "--base", self.base, "--head", head or self.head, "--body-file", str(path)],
            cwd=self.repo, capture_output=True, text=True)


class TrainChecks(Repository):
    """Each structural rule is checked against real commit and tree objects."""

    def test_good_train(self):
        self.assertEqual(self.problems(), [])
        self.assertEqual(train.body_problems(self.body), [])

    def test_member_history_is_not_coordinator_work(self):
        member = self.commit([self.member], {LEAN: "-- another reviewed change\n"})
        head = self.merge(self.base, member)
        self.assertEqual(self.problems(head=head, text=body([member_row(member)])), [])

    def test_squashed_member(self):
        head = self.commit([self.base], {LEAN: self.trees[self.member][LEAN]})
        self.refused("row has no unique member merge", head=head)
        self.refused("coordinator commit", head=head)

    def test_fast_forwarded_member(self):
        self.refused("row has no unique member merge", head=self.member)
        self.refused("coordinator commit", head=self.member)

    def test_member_merged_twice(self):
        head = self.commit([self.head, self.member])
        self.refused("merged more than once", head=head)

    def test_row_without_member(self):
        extra = member_row(self.base, "content/absent")
        self.refused("row has no unique member merge", text=body([self.row, extra]))

    def test_member_without_row(self):
        member = self.commit([self.base], {"mishnah/I/02.md": "Reviewed commentary.\n"})
        head = self.merge(self.head, member)
        self.refused(f"member {member[:12]} has no Members row", head=head,
                     text=body([self.row], "- propositions: I.1, I.2"))

    def test_duplicate_member_row(self):
        extra = member_row(self.member, "content/duplicate")
        self.refused("has more than one Members row", text=body([self.row, extra]))

    def test_octopus_merge(self):
        other = self.commit([self.base], {"facts.json": '{"new": true}\n'})
        head = self.commit([self.head, self.member, other])
        self.refused("expected exactly two parents", head=head)

    def test_evil_merge_adds_lean(self):
        head = self.commit([self.base, self.member],
                           {LEAN: self.trees[self.member][LEAN] + "-- unchecked line\n"})
        self.refused(f"resolution or added content outside generated files and decisions: "
                     f"{LEAN}", head=head)

    def test_conflict_is_refused_even_when_its_tree_is_automatic(self):
        member = self.commit([self.base], {LEAN: "-- conflicting reviewed source\n"})
        automatic = self.git("merge-tree", "--write-tree", "--name-only", self.head,
                             member, codes=(1,)).splitlines()[0]
        head = self.commit([self.head, member], tree=automatic)
        self.refused(f"resolution or added content outside generated files and decisions: "
                     f"{LEAN}", head=head,
                     text=body([self.row, member_row(member, "content/two")]))

    def test_member_s_own_merge_of_main_with_a_resolution_is_the_member_s(self):
        # WORKFLOW, section 10: a branch merges main, never rebases. Its resolution is in
        # the member's reviewed diff, judged by its reviews, not again by the train.
        main = self.commit([self.base], {LEAN: "-- main moved on\n"})
        work = self.commit([self.base], {LEAN: "-- the member's first version\n"})
        resolved = self.commit([work, main], {LEAN: "-- the member's resolution\n"})
        head = self.merge(main, resolved)
        self.assertEqual(self.problems(head=head, base=main,
                                       text=body([member_row(resolved)])), [])

    def test_a_conflict_is_resolved_in_a_member_that_holds_both_sides(self):
        # WORKFLOW, "Building a train that passes": two members change the same line. The
        # resolution is made in a branch that merges one into the other and is reviewed
        # at that head; the train merges it with one row, the member it holds merged
        # before it with its own row or not at all.
        other = self.commit([self.base], {LEAN: "-- the other member's source\n"})
        both = self.commit([self.member, other], {LEAN: "-- both members, resolved\n"})
        alone = self.merge(self.base, both)
        self.assertEqual(self.problems(head=alone, text=body([member_row(both)])), [])
        first = self.merge(self.base, other)
        after = self.merge(first, both)
        rows = [member_row(other, "content/two"), member_row(both, "content/both")]
        self.assertEqual(self.problems(head=after, text=body(rows)), [])

    def test_readme_prose_is_not_the_coordinator_s(self):
        readme = ("Prose by hand.\n<!-- scope:I -->\nGenerated row.\n<!-- /scope:I -->\n")
        base = self.commit([self.base], {"README.md": readme})
        member = self.commit([base], {LEAN: "-- reviewed source\n"})
        merged = self.merge(base, member)
        text = body([member_row(member)])
        rows = self.commit([merged], {"README.md": readme.replace("Generated row.",
                                                                  "A new generated row.")})
        self.assertEqual(self.problems(head=rows, base=base, text=text), [])
        prose = self.commit([merged], {"README.md": readme.replace("Prose by hand.",
                                                                   "Prose rewritten.")})
        self.assertTrue(any("changes forbidden path: README.md" in problem for problem in
                            self.problems(head=prose, base=base, text=text)))

    def test_coordinator_changes_lean(self):
        head = self.commit([self.head], {LEAN: "-- unchecked coordinator source\n"})
        self.refused("coordinator commit", head=head)
        self.refused(f"changes forbidden path: {LEAN}", head=head)

    def test_coordinator_cannot_hide_a_change_by_reverting_it(self):
        bad = self.commit([self.head], {LEAN: "-- unchecked coordinator source\n"})
        head = self.commit([bad], {LEAN: self.trees[self.head][LEAN]})
        self.refused("coordinator commit", head=head)

    def test_member_descent_cannot_hide_a_first_parent_coordinator_commit(self):
        coordinator = self.commit([self.base], {LEAN: "-- unchecked coordinator source\n"})
        member = self.commit([coordinator], {"mishnah/I/01.md": "Reviewed commentary.\n"})
        head = self.merge(coordinator, member)
        problems = self.problems(head=head, text=body([member_row(member)]))
        self.assertIn(f"coordinator commit {coordinator[:12]} changes forbidden path: "
                      f"{LEAN}", problems)

    def test_generated_and_decision_changes_are_allowed(self):
        for path in ("facts.json", "book/I/1.html", train.DECISIONS, ENTRY):
            with self.subTest(path=path):
                changes = {path: "An integration change.\n"}
                merge_changes = {**self.trees[self.member], **changes}
                head = self.commit([self.base, self.member], merge_changes)
                self.assertEqual(self.problems(head=head), [])
                head = self.commit([self.head], changes)
                self.assertEqual(self.problems(head=head), [])

    def test_non_markdown_decision_file_is_not_exempt(self):
        head = self.commit([self.head], {"docs/decisions/run.py": "print('unchecked')\n"})
        self.refused("changes forbidden path: docs/decisions/run.py", head=head)

    def test_decision_entries_need_their_directory_on_main(self):
        # While origin/main has no docs/decisions/ directory (absent, or a file of that
        # name), an entry file has no allowance: in a merge or in the train's own commits.
        for name, change in (("absent", None), ("a file", "Not a directory.\n")):
            with self.subTest(main=name):
                base = self.commit([self.base], {"docs/decisions/README.md": None})
                # The entry needs a directory in the train, so the file of that name goes.
                gone = {}
                if change is not None:
                    base = self.commit([base], {"docs/decisions": change})
                    gone = {"docs/decisions": None}
                member = self.commit([base], {LEAN: "-- reviewed source\n"})
                merged = self.merge(base, member)
                text = body([member_row(member)])
                self.assertEqual(self.problems(base=base, head=merged, text=text), [])
                own = self.commit([merged], {**gone, ENTRY: "An entry written in the train.\n"})
                self.assertIn(f"coordinator commit {own[:12]} changes forbidden path: "
                              f"{ENTRY}", self.problems(base=base, head=own, text=text))
                resolved = self.commit([base, member], {
                    **self.trees[member], **gone, ENTRY: "An entry added in the merge.\n"})
                self.assertIn(f"merge {resolved[:12]}: resolution or added content outside "
                              f"generated files and decisions: {ENTRY}",
                              self.problems(base=base, head=resolved, text=text))
                self.assertEqual(self.problems(base=base, head=self.commit(
                    [merged], {train.DECISIONS: "The page itself.\n"}), text=text), [])

    def test_conflicted_generated_and_decision_files_are_allowed(self):
        for path in ("facts.json", train.DECISIONS, ENTRY):
            with self.subTest(path=path):
                first = self.commit([self.base], {path: "First reviewed version.\n"})
                second = self.commit([self.base], {path: "Second reviewed version.\n"})
                merge = self.merge(self.base, first)
                head = self.commit([merge, second], {path: "Combined version.\n"})
                text = body([member_row(first, "docs/one"), member_row(second, "docs/two")],
                            "None.")
                self.assertEqual(self.problems(head=head, text=text), [])

    def test_main_merge_needs_no_member_row(self):
        base = self.commit([self.base], {"docs/STYLE.md": "Updated main guide.\n"})
        head = self.merge(self.head, base)
        self.assertEqual(self.problems(base=base, head=head), [])

    def test_main_merge_is_also_checked_for_added_content(self):
        base = self.commit([self.base], {"docs/STYLE.md": "Updated main guide.\n"})
        head = self.commit([self.head, base],
                           {LEAN: "-- hidden in the merge of main\n",
                            "docs/STYLE.md": "Updated main guide.\n"})
        self.refused(f"resolution or added content outside generated files and decisions: "
                     f"{LEAN}", base=base, head=head)

    def test_base_must_be_in_the_train(self):
        base = self.commit([self.base], {"docs/STYLE.md": "Later main.\n"})
        self.refused("train head does not contain the supplied base", base=base)

    def test_no_mistakes_names_another_sha(self):
        row = {**self.row, "no_mistakes": f"passed at {self.base}"}
        self.refused("/no-mistakes names another head", text=body([row]))

    def test_longer_evidence_must_match_the_actual_member(self):
        wrong = self.member[:12] + ("0" if self.member[12] != "0" else "1") + self.member[13:]
        row = {**self.row, "head": self.member[:12], "no_mistakes": f"passed at {wrong}"}
        self.assertEqual(train.body_problems(body([row])), [])
        self.refused("/no-mistakes names another head", text=body([row]))

    def test_short_reason(self):
        row = {**self.row, "no_mistakes": "not run: time was short"}
        self.refused("reason needs at least five words", text=body([row]))

    def test_review_cells_that_say_the_review_is_to_come_refuse(self):
        for cell in ("pending", "Not run yet.", "TBD", "awaiting review", "WIP", "N/A",
                     "none", "?", "queued", "skipped", "Will run after merge."):
            for key in ("code_review", "security_review"):
                with self.subTest(cell=cell, key=key):
                    row = dict(self.row, **{key: cell})
                    self.refused("is not written, or says the review is not done",
                                 text=body([row]))

    def test_review_cells_must_name_the_reviewed_commit(self):
        for key, cell in (("code_review", "In progress: a reader is on it."),
                          ("security_review", "In progress: a reader is on it."),
                          ("code_review", "Independent reader: PASS, no findings."),
                          ("code_review", "Not required: a documentation change."),
                          ("code_review", f"Reviewed at {self.member[:6]}: no findings."),
                          ("code_review", "Reviewed at ABCDEF1: no findings."),
                          ("security_review", "Reviewed by hand: no findings."),
                          # A commit no reader sees names none (the fourth review).
                          ("code_review", f"<span title='{self.member[:12]}'>clean</span>"),
                          ("security_review",
                           f"<a href='#{self.member[:12]}'>Pass</a>: no findings."),
                          ("code_review",
                           f"[Pass, no findings](https://example.invalid/{self.member})"),
                          ("code_review",
                           f"[Reviewed](https://example.invalid/(note)/{self.member})"),
                          ("security_review",
                           f"[Reviewed](https://example.invalid/a\\(b\\)/{self.member})"),
                          ("code_review",
                           f"[Reviewed](https://example.invalid/&#41;{self.member})"),
                          ("code_review",
                           f'<span title="> {self.member}">Reviewed</span>')):
            with self.subTest(key=key, cell=cell):
                label = "/code-review" if key == "code_review" else "/security-review"
                self.refused(f"{label} names no reviewed commit",
                             text=body([dict(self.row, **{key: cell})]))

    def test_review_cells_need_visible_content_beyond_the_commit(self):
        for cell in (self.member, f"`{self.member}`.", f"({self.member})!", f"{self.member} 123",
                     f"{self.member} \N{HANGUL FILLER}", f"{self.member} \u1160",
                     f"{self.member} &#12644;",
                     f"**[{self.member}]**", f"<span>{self.member}</span>",
                     f"[{self.member}](https://example.invalid/review)"):
            for key in ("code_review", "security_review"):
                with self.subTest(cell=cell, key=key):
                    row = dict(self.row, **{key: cell})
                    self.refused("gives no visible review verdict or findings beyond the "
                                 "reviewed commit", text=body([row]))
        for cell in (f"{self.member}: pass", f"{self.member}: one finding",
                     f"{self.member}: révisé", f"{self.member}: 审查完毕"):
            for key in ("code_review", "security_review"):
                with self.subTest(cell=cell, key=key):
                    row = dict(self.row, **{key: cell})
                    self.assertEqual(self.problems(text=body([row])), [])
        for cell in (f"[Reviewed {self.member}: no findings](https://example.invalid/(note))",
                     f"[Reviewed {self.member}: no findings]"
                     "(https://example.invalid/&#41;)",
                     f'<span title="> note">Reviewed {self.member}: no findings</span>'):
            with self.subTest(cell=cell):
                row = dict(self.row, code_review=cell)
                self.assertEqual(self.problems(text=body([row])), [])

    def test_review_commit_must_use_visible_ascii_hex(self):
        token = self.member[:12]
        fullwidth = "".join(chr(ord(character) + 0xFEE0) for character in token)
        hidden = (
            f"\\`[reviewed](https://example.invalid/{token})\\`",
            f"[reviewed](https://example.invalid/{token})",
            f"Reviewed {fullwidth}: no findings",
        )
        visible = (
            f"`reviewed {token}: no findings\\`",
            f"\\\\`reviewed {token}: no findings`",
            f"<https://example.invalid/{token}>: pass",
            f"\\[review](https://example.invalid/{token}) pass",
        )
        for key, label in (("code_review", "/code-review"),
                           ("security_review", "/security-review")):
            for cell in hidden:
                with self.subTest(key=key, hidden=cell):
                    self.refused(f"{label} names no reviewed commit",
                                 text=body([dict(self.row, **{key: cell})]))
            for cell in visible:
                with self.subTest(key=key, visible=cell):
                    self.assertEqual(self.problems(text=body(
                        [dict(self.row, **{key: cell})])), [])

    def test_multiline_html_does_not_hide_block_sections(self):
        wrapped = '<span title="\n' + body([self.row]) + '\n">x</span>'
        self.assertEqual(train.members_table(wrapped), [self.row])

    def test_malformed_markup_and_link_titles_hide_no_review_commit(self):
        cells = (
            f'<" <span title="{self.member}">Reviewed</span>',
            f"[x]( [Reviewed](https://example.invalid/{self.member})",
            f'[Reviewed](https://example.invalid "note ) {self.member}")',
            f"x][[Reviewed](https://example.invalid/{self.member})",
            f'[Reviewed](a"b "c) {self.member}")',
            f"[Reviewed](</) {self.member}>)",
            f"[Reviewed][x](https://example.invalid/{self.member})",
            f"[Reviewed](https://example.invalid/<b(>){self.member})",
            f"<?x {self.member} ?>Reviewed",
            f"<!X {self.member}>Reviewed",
            f"<![CDATA[ {self.member} ]]>Reviewed",
            f"![{self.member}](review.png) Reviewed",
        )
        for cell in cells:
            for key, label in (("code_review", "/code-review"),
                               ("security_review", "/security-review")):
                with self.subTest(cell=cell, key=key):
                    self.refused(f"{label} names no reviewed commit",
                                 text=body([dict(self.row, **{key: cell})]))
        for cell in (
                f'<" <span title="note">Reviewed {self.member}: no findings</span>',
                f"x][[Reviewed {self.member}: no findings](https://example.invalid/review)",
                f"[Elements](https://en.wikipedia.org/wiki/Euclid's_Elements) reviewed "
                f"at {self.member}: no findings"):
            with self.subTest(visible=cell):
                self.assertEqual(self.problems(text=body(
                    [dict(self.row, code_review=cell)])), [])

    def test_code_spans_preserve_literal_review_evidence(self):
        visible = (
            f"`[review](https://example.invalid/{self.member})` no findings",
            f"`` `[review](https://example.invalid/{self.member})` `` no findings",
            f"`<span title='{self.member}'>reviewed</span>` no findings",
        )
        hidden = (
            f"`reviewed [x](https://example.invalid/{self.member})",
            f"`reviewed` [x](https://example.invalid/{self.member})",
            f"[review](https://example.invalid/`{self.member}`) no findings",
            f"<span title='`{self.member}`'>reviewed</span>",
        )
        for key, label in (("code_review", "/code-review"),
                           ("security_review", "/security-review")):
            for cell in visible:
                with self.subTest(key=key, visible=cell):
                    self.assertEqual(self.problems(text=body(
                        [dict(self.row, **{key: cell})])), [])
            for cell in hidden:
                with self.subTest(key=key, hidden=cell):
                    self.refused(f"{label} names no reviewed commit",
                                 text=body([dict(self.row, **{key: cell})]))

    def test_footnotes_and_images_supply_no_review_evidence(self):
        prefix = self.member[:12]
        hidden = (
            (f"[^{prefix}-reviewed]", f"[^{prefix}-reviewed]: a note"),
            (f"![{prefix} reviewed](proof.png)", ""),
            (f"![{prefix} reviewed][proof]", "[proof]: proof.png"),
            (f"![{prefix} reviewed][]", f"[{prefix} reviewed]: proof.png"),
            (f"![{prefix} reviewed]", f"[{prefix} reviewed]: proof.png"),
        )
        hidden_verdicts = (
            (f"{prefix} [^reviewed]", "[^reviewed]: a note"),
            (f"{prefix} ![reviewed](proof.png)", ""),
            (f"{prefix} ![reviewed][proof]", "[proof]: proof.png"),
            (f"{prefix} ![reviewed][]", "[reviewed]: proof.png"),
            (f"{prefix} ![reviewed]", "[reviewed]: proof.png"),
        )
        for key, label in (("code_review", "/code-review"),
                           ("security_review", "/security-review")):
            for cell, definition in hidden:
                with self.subTest(key=key, hidden=cell):
                    text = body([dict(self.row, **{key: cell})])
                    text += f"\n## References\n\n{definition}\n"
                    self.refused(f"{label} names no reviewed commit", text=text)
            for cell, definition in hidden_verdicts:
                with self.subTest(key=key, hidden_verdict=cell):
                    text = body([dict(self.row, **{key: cell})])
                    text += f"\n## References\n\n{definition}\n"
                    self.refused("gives no visible review verdict or findings beyond the "
                                 "reviewed commit", text=text)

        for cell, definition in (
                (f"[Reviewed {prefix}: no findings][review]",
                 "[review]: https://example.invalid/review"),
                (f"[Reviewed {prefix}: no findings]",
                 f"[Reviewed {prefix}: no findings]: https://example.invalid/review")):
            with self.subTest(visible=cell):
                text = body([dict(self.row, code_review=cell)])
                text += f"\n## References\n\n{definition}\n"
                self.assertEqual(self.problems(text=text), [])

    def test_long_review_cells_are_read_in_linear_time(self):
        # 200,000 characters of openings that never close, which a regular expression
        # rescanning to the end from each would read in quadratic time (3.4 s at 65,536
        # characters of "<!--"), and of separators after a placeholder word's start.
        size = 200_000
        for cell in ("<!--" * (size // 4), "<a" * (size // 2), "](" * (size // 2),
                     "][" * (size // 2), '[Reviewed](x "' + ")" * size,
                     "`" * size,
                     "n" + "/" * size, "to" + " " * size,
                     "not" + "-" * size + "x", ("n" + " " * 50) * (size // 51 + 1)):
            with self.subTest(cell=cell[:12]):
                self.assertGreaterEqual(len(cell), size)
                started = time.perf_counter()
                train._review_content(f"{self.member} {cell}")
                train._placeholder_word(f"{self.member} {cell}")
                self.assertLess(time.perf_counter() - started, 1.0)

    def test_findings_that_begin_like_a_placeholder_pass(self):
        for cell in (f"To do so, the reader re-ran the checks at {self.member[:7]}: no "
                     "findings.",
                     f"Later commits after {self.member[:8]} change only the record's "
                     "stamp: no findings.",
                     f"Skipped nothing: every check re-ran at `{self.member[:10]}`.",
                     f"Depending on the base, the reader re-ran {self.member[:9]}: no "
                     "findings; the outcome is now known."):
            for key in ("code_review", "security_review"):
                with self.subTest(cell=cell, key=key):
                    row = dict(self.row, **{key: cell})
                    self.assertEqual(self.problems(text=body([row])), [])

    def test_review_cells_may_hold_no_placeholder_word_anywhere(self):
        # Beside the member's own commit too, and in a protected member's security cell.
        own = self.member[:12]
        cells = (f"pending {own}", f"Not needed ({own})", f"TBD {own}",
                 f"Reviewed {own}: pass; a second review to come.", f"{own}: N/A",
                 f"Reviewed {own}: PENDING.", f"{own}: pass. Pending items: none.",
                 f"{own}: pass; n / a for the rest.", f"{own}: not&#32;needed again.",
                 # Casefolding the dotted capital I adds a mark (the fourth review).
                 f"Reviewed {own}: PENDİNG.", f"{own}: pass; \N{MATHEMATICAL BOLD CAPITAL N}/A.",
                 f"Reviewed {own}: pass, to-come notes aside.", f"Reviewed {own}: t\N{ZERO WIDTH SPACE}bd.")
        for cell in cells:
            for key, label in (("code_review", "/code-review"),
                               ("security_review", "/security-review")):
                with self.subTest(cell=cell, key=key):
                    self.refused(f"{label} says", text=body([dict(self.row, **{key: cell})]))
                    self.assertIn("a review cell may not say", "\n".join(
                        train.body_problems(body([dict(self.row, **{key: cell})]))))
        for filler in train.INVISIBLE_LETTERS:
            for suffix in (filler, f"&#{ord(filler)};"):
                cell = f"{own}: pending{suffix}"
                for key, label in (("code_review", "/code-review"),
                                   ("security_review", "/security-review")):
                    with self.subTest(key=key, filler=ord(filler), entity="&" in suffix):
                        self.refused(f"{label} says", text=body(
                            [dict(self.row, **{key: cell})]))
        member = self.commit([self.base], {CHECK: "print('reviewed check')\n"})
        head = self.merge(self.base, member)
        for cell in (f"Security reader at {member}: PASS; a second pass is pending.",
                     f"Not needed ({member[:12]})", f"TBD {member[:12]}"):
            with self.subTest(protected=cell):
                self.refused("/security-review says", head=head, text=body(
                    [member_row(member, security_review=cell)], f"- check: {CHECK}"))

    def own(self, cell: str, commit: str) -> str:
        """The cell as written, its first commit name standing for `commit`, by as many
        digits: the other names, the coordinator's or other members', stay as written."""
        return train.COMMIT.sub(lambda match: commit[:len(match.group())], cell, count=1)

    def test_the_coordinator_s_written_rows_pass(self):
        # Rows as the coordinator's body writer gives them: one line each, "|" written
        # "/", the commit named by seven or eight digits somewhere in the finding. The
        # commit each names first is the member's, here this fixture's member.
        rows = (
            ("Ship H's bosun passed it at d6243923; its one editorial suggestion (qualify "
             "the helper fields) adopted in 005281b7; the captain re-ran fidelity.",
             "Not required: no protected path."),
            ("Stand-in outside review (Codex, read-only) of d532116: 1 error and 2 "
             "should-fix items, all fixed in 7916e6d; a second pass found nothing.",
             "/security-review at 99b0ef4: not required. No protected path changed."),
            ("Records review by an independent reviewer, stamped at 2ac1625. One findings "
             "round; all items pass.",
             "Not required. review/I/02..05.toml only; no protected path."),
            ("Independent Codex review (Standards and Spec) of d5c4f98f: no blocking or "
             "material defect; its one editorial finding (a decisions sentence saying "
             "negative_tests was unchanged) fixed in 0806e32c. Independent re-review of "
             "d5c4f98f..601e13f3: nothing; main's judged_files is empty and all 15 "
             "protected files are named. The coordinator's commit 0e205986 changes the "
             "decisions entry's approval wording only (the owner's words of 19 and 20 "
             "October, and #168).",
             "Independent Codex security review of d5c4f98f: nothing blocking, material or "
             "minor; it noted one authorised weakening, 5d200cf's pin drop, which the owner "
             "approved on 19 October and the decisions page records. Re-review at "
             "601e13f3: nothing. Needs the label security-review."),
            ("Eight rounds through R3-rr8-letter (ab8e2e93); R4-rr2-letterdtd passed "
             "(a062cbeb); its /no-mistakes commits 072d3609, 383c6c8e, 7f1f4003, 640efbb7 "
             "passed review (R4-rr5-H10).",
             "c32002b1 and f6e2b382 found the <use> and square-cap gaps, fixed; R4-rr3-H10 "
             "found DTD and entity expansion (23bc3b2a), R4-rr-letterdtd the pure-Python "
             "parser gap (a062cbeb); R4-rr2-letterdtd and R4-rr5-H10 pass."),
        )
        for code, security in rows:
            with self.subTest(code=code):
                row = dict(self.row, code_review=code, security_review=security)
                self.assertEqual(train.body_problems(body([row])), [])
                row = dict(row, code_review=self.own(code, self.member),
                           security_review=self.own(security, self.member))
                self.assertEqual(self.problems(text=body([row])), [])

    def test_the_coordinator_s_protected_row_passes(self):
        # A member that changes protected paths, with the coordinator's written security
        # cell, its commit the member's head.
        member = self.commit([self.base], {CHECK: "print('reviewed check')\n"})
        head = self.merge(self.base, member)
        security = self.own(
            "Protected paths .github/workflows/ci.yml, scripts/check_acceptance.py, "
            "scripts/copy_acceptance_checks.sh and tests/test_check_acceptance.py, each "
            "named in the decisions entry. Ship Q's independent Codex reader: PASS at "
            "e0ca0c80; nothing loosened, no required check or pre-flight check changed, the "
            "job reads only the repository. The PR needs the label security-review.", member)
        code = self.own(
            "Independent reviews through the lane (the ratchet's staged-statement case and a "
            "misspelt gate found and fixed at 109a29f8, 6dbdd3c9); ship Q's Codex reviewer "
            "passed the fixture fix at ba0a803f and the merged head e0ca0c80, Standards "
            "PASS, Spec PASS.", member)
        row = member_row(member, code_review=code, security_review=security)
        self.assertEqual(self.problems(head=head, text=body([row], f"- check: {CHECK}")), [])

    def test_review_cells_must_name_a_commit_of_the_member_s_own_history(self):
        later = self.commit([self.member], {LEAN: "-- a later, unreviewed change\n"})
        other = self.commit([self.base], {"docs/STYLE.md": "Another branch's guide.\n"})
        blob = self.git("rev-parse", f"{self.member}:{LEAN}").strip()
        tree = self.git("rev-parse", f"{self.member}^{{tree}}").strip()
        # A ref whose name is hex digits resolves by name to a commit they do not begin.
        name = "abcdef1" if not self.base.startswith("abcdef1") else "abcdef2"
        self.git("update-ref", f"refs/tags/{name}", self.member)
        for cell in (
                "Not needed (1234567)", "skipped at 1234567", "0000000", "pending 1234567",
                f"Reviewed the file's blob {blob[:10]}: no findings.",
                f"Reviewed the tree {tree[:10]}: no findings.",
                f"Reviewed main's {self.base[:10]}: no findings.",
                f"Reviewed {other[:10]}, another branch: no findings.",
                f"Reviewed {later[:10]}, a later commit than the member's head.",
                f"Reviewed {self.head[:10]}, the train: no findings.",
                f"Reviewed {name}: no findings."):
            for key, label in (("code_review", "/code-review"),
                               ("security_review", "/security-review")):
                with self.subTest(cell=cell, key=key):
                    self.refused(f"{label} names no commit of the member's own history",
                                 text=body([dict(self.row, **{key: cell})]))
        earlier = self.commit([self.base], {LEAN: "-- the version first reviewed\n"})
        member = self.commit([earlier], {LEAN: "-- reviewed source\n"})
        head = self.merge(self.base, member)
        for commit in (member, earlier):
            with self.subTest(commit=commit):
                cell = f"Reviewed {commit[:7]}: no findings; 0000000 is no commit."
                self.assertEqual(self.problems(head=head, text=body([member_row(
                    member, code_review=cell, security_review=cell)])), [])

    def test_protected_member_may_not_say_not_required_anywhere(self):
        member = self.commit([self.base], {CHECK: "print('reviewed check')\n"})
        head = self.merge(self.base, member)
        text = f"- check: {CHECK}"
        for said in ("Not required", "not required", "NOT REQUIRED", "not  required",
                     "not-required", "not_required", "Notrequired", "not required",
                     "Not&nbsp;required", "Not&#32;required", "not​required",
                     "**Not** required", "Ｎot required",
                     # Casefolding the dotted capital I adds a mark (the fourth review); a
                     # compatibility capital folds only after NFKC.
                     "NOT REQUİRED", "Not \N{BLACK-LETTER CAPITAL R}equired",
                     "\N{MATHEMATICAL BOLD CAPITAL N}ot required"):
            with self.subTest(said=said):
                cell = f"Security reader at {member}: PASS; a second pass is {said}."
                self.refused("/security-review says Not required for protected paths",
                             head=head, text=body([member_row(member, security_review=cell)],
                                                  text))
        cell = f"Security reader at {member}: PASS; nothing is required of the next pass."
        self.assertEqual(self.problems(head=head, text=body(
            [member_row(member, security_review=cell)], text)), [])

    def test_recorded_reason(self):
        row = {**self.row, "no_mistakes": "not run: the required runner was unavailable"}
        self.assertEqual(self.problems(text=body([row])), [])

    def test_matching_prefixes(self):
        row = {**self.row, "head": self.member[:16],
               "no_mistakes": f"passed at {self.member[:12]}"}
        self.assertEqual(self.problems(text=body([row])), [])

    def test_protected_member_requires_security_review(self):
        member = self.commit([self.base], {CHECK: "print('reviewed check')\n"})
        head = self.merge(self.base, member)
        self.refused("/security-review says Not required for protected paths",
                     head=head, text=body([member_row(member)], f"- check: {CHECK}"))
        row = member_row(member, security_review=f"Security reader at {member}: PASS.")
        self.assertEqual(self.problems(head=head, text=body([row], f"- check: {CHECK}")), [])

    def test_criss_cross_member_reads_protected_paths_against_every_merge_base(self):
        # Main merged the member's first commit while the member merged main's: the two
        # have two merge bases. The protected change shows against one base only, and
        # counts.
        ahead = self.commit([self.base], {"docs/STYLE.md": "Main's guide.\n"})
        first = self.commit([self.base], {CHECK: "print('reviewed check')\n"})
        main = self.merge(ahead, first)
        member = self.commit([self.merge(first, ahead)], {LEAN: "-- reviewed source\n"})
        self.assertEqual(len(self.git("merge-base", "--all", main, member).split()), 2)
        head = self.merge(main, member)
        self.refused("/security-review says Not required for protected paths: "
                     f"{CHECK}", base=main, head=head, text=body([member_row(member)]))
        row = member_row(member, security_review=f"Security reader at {member}: PASS.")
        self.assertEqual(self.problems(base=main, head=head, text=body([row])), [])

    def test_unreadable_member_merge_base_names_the_member(self):
        with patch.object(train, "_merge_bases",
                          side_effect=ValueError("could not read a merge base")):
            with self.assertRaisesRegex(ValueError, f"Members: content/one "
                                        rf"\({self.member[:12]}\): could not read"):
                self.problems()

    def test_member_attributes_cannot_make_a_resolution_automatic(self):
        # A member's .gitattributes says merge=union. In a checkout of the train, git's
        # own merge reads it and takes the coordinator's union as automatic; the check
        # reads attributes from the base, so the resolution is still refused.
        other = self.commit([self.base], {LEAN: "-- another reviewed source\n",
                                          ".gitattributes": f"{LEAN} merge=union\n"})
        checkout = self.root / "checkout"
        self.git("worktree", "add", "--quiet", "--detach", str(checkout), other)
        union = subprocess.run(["git", "merge-tree", "--write-tree", self.head, other],
                               cwd=checkout, capture_output=True, text=True)
        self.assertEqual(union.returncode, 0, union.stdout + union.stderr)
        head = self.commit([self.head, other], tree=union.stdout.strip())
        self.assertIn("-- reviewed source\n", self.trees[head][LEAN])
        self.assertIn("-- another reviewed source\n", self.trees[head][LEAN])
        rows = [self.row, member_row(other, "content/two",
                                     security_review=f"Security reader at {other}: PASS.")]
        problems = train.check_train(checkout, self.base, head, body(rows))
        self.assertIn(f"merge {head[:12]}: resolution or added content outside generated "
                      f"files and decisions: {LEAN}", problems)

    def test_check_change_with_judged_content_across_members(self):
        member = self.commit([self.base], {CHECK: "print('reviewed check')\n"})
        head = self.merge(self.head, member)
        row = member_row(member, "tooling/check",
                         security_review=f"Security reader at {member}: PASS.")
        self.refused("check changes must be kept apart from judged content", head=head,
                     text=body([self.row, row], f"- check: {CHECK}\n- propositions: I.1"))

    def test_check_change_with_decision_entry(self):
        member = self.commit([self.base], {CHECK: "print('reviewed check')\n"})
        merged = self.merge(self.base, member)
        head = self.commit([merged], {ENTRY: "The reason for the check change.\n"})
        row = member_row(member, security_review=f"Security reader at {member}: PASS.")
        self.assertEqual(self.problems(head=head, text=body([row], f"- check: {CHECK}")), [])

    def test_pinned_values_can_move_with_content(self):
        path = "tests/model/MODEL.md"
        member = self.commit([self.member], {path: "A revised account.\n"})
        head = self.merge(self.base, member)
        row = member_row(member, security_review=f"Security reader at {member}: PASS.")
        self.assertEqual(self.problems(head=head,
                         text=body([row], f"- check: {path}\n- propositions: I.1")), [])

    def test_undeclared_changed_check(self):
        member = self.commit([self.base], {CHECK: "print('reviewed check')\n"})
        head = self.merge(self.base, member)
        row = member_row(member, security_review=f"Security reader at {member}: PASS.")
        self.refused(f"undeclared check: {CHECK}", head=head, text=body([row], "None."))

    def test_undeclared_changed_proposition(self):
        self.refused("undeclared proposition: I.1", text=body([self.row], "None."))

    def test_undeclared_foundation(self):
        path = "Elements/Foundations/Plane.lean"
        member = self.commit([self.base], {path: "-- reviewed foundation text\n"})
        head = self.merge(self.base, member)
        self.refused(f"undeclared foundation: {path}", head=head,
                     text=body([member_row(member)], "None."))


class BodyChecks(unittest.TestCase):
    """Only visible, written evidence and declarations count."""

    def setUp(self):
        self.row = member_row("0123456789abcdef0123456789abcdef01234567")
        self.body = body([self.row])

    def test_public_row_shape(self):
        self.assertEqual(train.members_table(self.body), [self.row])

    def test_public_declaration_shape(self):
        text = body([self.row], "- check: scripts/example.py\n"
                    "- rule: trains go through the merge queue\n"
                    "- propositions: I.5, II.3\n"
                    "- foundations: Elements/Foundations/Plane.lean")
        self.assertEqual(train.declared_new(text), {
            "checks": {"scripts/example.py"},
            "rules": ["trains go through the merge queue"],
            "propositions": {"I.5", "II.3"},
            "foundations": {"Elements/Foundations/Plane.lean"},
            "none": False,
        })
        self.assertEqual(train.declared_new(body([self.row], "None.")),
                         {"checks": set(), "rules": [], "propositions": set(),
                          "foundations": set(), "none": True})

    def test_hidden_sections_do_not_count(self):
        variants = [
            f"```\n{self.body}\n```\n",
            f"<!--\n{self.body}\n-->\n",
            f"<pre>\n{self.body}\n</pre>\n",
            "\n".join("    " + line for line in self.body.splitlines()),
            f"<!-- safe_push:preflight begin -->\n{self.body}"
            "<!-- safe_push:preflight end -->\n",
        ]
        for text in variants:
            with self.subTest(text=text):
                self.assertTrue(train.body_problems(text))
                with self.assertRaises(ValueError):
                    train.members_table(text)

    def test_hidden_cell_is_not_written(self):
        row = {**self.row, "code_review": "<!-- not visible -->"}
        self.assertIn("/code-review is not written",
                      "\n".join(train.body_problems(body([row]))))

    def test_placeholders_and_bad_heads(self):
        cases = [
            ("code_review", "TODO", "/code-review is not written"),
            ("security_review", "_tbd_", "/security-review is not written"),
            ("head", "ABCDEF012345", "lower-case hex digits"),
            ("head", "abcdef", "12 to 40"),
            ("no_mistakes", "passed at 0123456789ab0z", "must say passed at"),
            ("no_mistakes", "not run: - - - - -", "at least five words"),
        ]
        for key, value, message in cases:
            with self.subTest(key=key, value=value):
                self.assertIn(message, "\n".join(train.body_problems(
                    body([{**self.row, key: value}]))))

    def test_duplicate_sections_are_unreadable(self):
        for name in ("Members", "What is new"):
            with self.subTest(name=name):
                text = self.body + f"\n## {name}\n\nNone.\n"
                self.assertIn(f'expected one written "{name}" section',
                              "\n".join(train.body_problems(text)))

    def test_malformed_table_is_unreadable(self):
        for text in (self.body.replace("|---|---|---|---|---|", "|---|---|"),
                     self.body.replace("| Head |", "| Revision |"),
                     self.body.replace("| content/one |", "| content/one | extra |"),
                     body([])):
            with self.subTest(text=text), self.assertRaises(ValueError):
                train.members_table(text)

    def test_malformed_declarations_are_unreadable(self):
        for new in ("None.\n- propositions: I.1", "- unknown: scripts/x.py",
                    "check: scripts/x.py", "- propositions: I.1,",
                    "- check: ../scripts/x.py", "- check: /scripts/x.py",
                    "- rule: TODO", "```\n- propositions: I.1\n```"):
            with self.subTest(new=new), self.assertRaises(ValueError):
                train.declared_new(body([self.row], new))

    def test_extra_declarations_are_allowed(self):
        derived = train.declared_new(self.body)
        declared = train.declared_new(body([self.row], "- propositions: I.1, III.9\n"
                                          "- check: tests/test_future.py"))
        self.assertEqual(train.undeclared(derived, declared), [])


class CoverageAndCLI(Repository):
    """The shared coverage interface and the three command-line outcomes."""

    def test_derives_all_path_families_including_deletions(self):
        changes = {
            LEAN: None,
            "Elements/BookII/Prop03.lean": "-- reviewed source\n",
            "review/III/04.toml": 'scope = "full"\n',
            "heath/I/05.md": "Source text.\n",
            "mishnah/II/06.md": "Commentary.\n",
            "figures/III/07-modern.svg": "<svg/>\n",
            "scripts/new.py": "print('check')\n",
            "tests/test_new.py": "print('test')\n",
            ".github/workflows/sample.yml": "name: sample\n",
            "Elements/Foundations/Plane.lean": "-- reviewed foundation text\n",
            "Certificate/axioms.lock": "# fixture lock\n",
            "model/Model/Example.lean": "-- reviewed model text\n",
        }
        head = self.commit([self.base], changes)
        derived = train.derive_new(self.repo, self.base, head)
        self.assertEqual(derived, {
            "checks": {"scripts/new.py", "tests/test_new.py", ".github/workflows/sample.yml"},
            "rules": [],
            "propositions": {"I.1", "II.3", "III.4", "I.5", "II.6", "III.7"},
            "foundations": {"Elements/Foundations/Plane.lean", "Certificate/axioms.lock",
                            "model/Model/Example.lean"},
            "none": False,
        })
        self.assertTrue(train.derive_new(self.repo, self.base, self.base)["none"])

    def test_rename_covers_old_and_new_propositions(self):
        head = self.commit([self.base],
                           {LEAN: None, "Elements/BookII/Prop09.lean": self.trees[self.base][LEAN]})
        self.assertEqual(train.derive_new(self.repo, self.base, head)["propositions"],
                         {"I.1", "II.9"})

    def test_cli_passes(self):
        result = self.cli()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("train: PASS", result.stdout)

    def test_cli_refuses(self):
        result = self.cli(text=body([self.row], "None."))
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("undeclared proposition: I.1", result.stdout)

    def test_cli_missing_body_is_unreadable(self):
        result = self.cli(missing=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("could not read", result.stderr)

    def test_cli_bad_utf8_is_unreadable(self):
        result = self.cli(raw=b"\xff")
        self.assertEqual(result.returncode, 2)
        self.assertIn("could not read", result.stderr)

    def test_cli_bad_revision_is_unreadable(self):
        result = self.cli(head="missing-revision")
        self.assertEqual(result.returncode, 2)
        self.assertIn("could not read", result.stderr)

    def test_cli_malformed_body_is_unreadable(self):
        result = self.cli(text="No train table.\n")
        self.assertEqual(result.returncode, 2)
        self.assertIn("could not read", result.stderr)

    def test_cli_incomplete_history_is_unreadable(self):
        (self.repo / "shallow").write_text(self.member + "\n")
        result = self.cli()
        self.assertEqual(result.returncode, 2)
        self.assertIn("complete history", result.stderr)

    def test_failed_merge_tree_is_unreadable(self):
        original = train.run

        def fail(args, cwd, **kwargs):
            if args[0] == "git" and "merge-tree" in args:
                return subprocess.CompletedProcess(args, 128, "", "cannot read tree")
            return original(args, cwd, **kwargs)

        with patch.object(train, "run", side_effect=fail):
            with self.assertRaisesRegex(ValueError, "could not read automatic merge"):
                self.problems()


if __name__ == "__main__":
    unittest.main(verbosity=2)
