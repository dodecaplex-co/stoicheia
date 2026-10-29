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
            # Main's reader of count markers: the model's page moves with content only
            # while its markers stand, as that reader reads them at the base, and with no
            # reader nothing is pinned (safe_push.counts_moved, #187).
            "scripts/generated_counts.py": (SCRIPTS / "generated_counts.py").read_text(
                encoding="utf-8"),
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
                           f"[Pass, no findings](https://example.invalid/{self.member})")):
            with self.subTest(key=key, cell=cell):
                label = "/code-review" if key == "code_review" else "/security-review"
                self.refused(f"{label} names no reviewed commit",
                             text=body([dict(self.row, **{key: cell})]))

    def test_review_cells_need_visible_content_beyond_the_commit(self):
        for cell in (self.member, f"`{self.member}`.", f"({self.member})!", f"{self.member} 123",
                     f"**[{self.member}]**", f"<span>{self.member}</span>",
                     f"[{self.member}](https://example.invalid/review)"):
            for key in ("code_review", "security_review"):
                with self.subTest(cell=cell, key=key):
                    row = dict(self.row, **{key: cell})
                    self.refused("gives no visible review verdict or findings beyond the "
                                 "reviewed commit", text=body([row]))
        for cell in (f"{self.member}: pass", f"{self.member}: one finding"):
            for key in ("code_review", "security_review"):
                with self.subTest(cell=cell, key=key):
                    row = dict(self.row, **{key: cell})
                    self.assertEqual(self.problems(text=body([row])), [])

    def test_long_review_cells_are_read_in_linear_time(self):
        # 200,000 characters of openings that never close, which a regular expression
        # rescanning to the end from each would read in quadratic time (3.4 s at 65,536
        # characters of "<!--"), and of separators after a placeholder word's start.
        size = 200_000
        for cell in ("<!--" * (size // 4), "<a" * (size // 2), "](" * (size // 2),
                     "][" * (size // 2), "n" + "/" * size, "to" + " " * size,
                     "not" + "-" * size + "x", ("n" + " " * 50) * (size // 51 + 1)):
            with self.subTest(cell=cell[:12]):
                self.assertGreaterEqual(len(cell), size)
                started = time.perf_counter()
                train._review_content(f"{self.member} {cell}")
                train._placeholder_word(f"{self.member} {cell}")
                self.assertLess(time.perf_counter() - started, 1.0)

    def test_the_incompletion_and_verdict_readings_are_linear(self):
        # 200,000 characters of separators after each new phrase's start, of phrases
        # that never end, and of verdicts each read back to its phrase.
        size = 200_000
        for cell in ("to follow" + " " * size + "x", "to be" + " " * size + "x",
                     "after the" + " " * size + "x", "after merge" + " " * size + "x",
                     "later" + " " * size + "x", "review not" + "-" * size + "x",
                     "review in" + " " * size + "x", " " + "-" * size, "? " * (size // 2),
                     "review, " * (size // 8), "found" + " " * size + "x",
                     "no " + "nor " * (size // 4) + "x", "pass " * (size // 5),
                     ("not " * 30 + "passed ") * (size // 127), "w<i></i>" * (size // 8)):
            with self.subTest(cell=cell[:12]):
                self.assertGreaterEqual(len(cell), size - 200)
                started = time.perf_counter()
                train._placeholder_word(f"{self.member} {cell}")
                train._review_content(f"{self.member} {cell}", security=True)
                train._says_not_required(f"{self.member} {cell}")
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
        member = self.commit([self.base], {CHECK: "print('reviewed check')\n"})
        head = self.merge(self.base, member)
        for cell in (f"Security reader at {member}: PASS; a second pass is pending.",
                     f"Not needed ({member[:12]})", f"TBD {member[:12]}"):
            with self.subTest(protected=cell):
                self.refused("/security-review says", head=head, text=body(
                    [member_row(member, security_review=cell)], f"- check: {CHECK}"))

    def test_review_cells_that_say_the_review_is_incomplete_refuse(self):
        # #259: "Findings will be added later at <sha>" passed, since any letter beyond
        # the commit counted. Each refuses beside a verdict too, and markup inside a word,
        # HTML or Markdown, or an invisible letter, hides it from no reading. Then the 27
        # October review's cells (its B1 and B2), each passed by the first fix.
        own = self.member[:12]
        cells = (f"{own}: PASS; review\N{INVISIBLE SEPARATOR}\u2065pending.",
                 f"{own}: PASS; review\u2065pending.", f"{own}: PASS; findings\u2065tbd.",
                 f"{own}: PASS; findings\U000E0002to come.", f"{own}: PASS; x\ufff0n/a",
                 f"Did {own} pass?Unknown.",
                 f"{own}: PASS; findings pen[d](#x)ing.", f"{own}: PASS; w[i](#x)ll be added.",
                 f"{own}: PASS; [pen](#x)ding.", f"{own}: PASS; to [co](#x)me.",
                 f"{own}: PASS; review [incom](#x)plete.",
                 f"Findings will be added later at {own}",
                 f"A first pass over {own}; the full review follows.",
                 f"{own}: PASS, with findings to be reported after the merge",
                 f"Review of {own} is incomplete: no findings.",
                 f"Quick pass at {own}, full review after the merge.",
                 f"{own}: PASS (review deferred)", f"{own}: PASS, the rest is outstanding",
                 f"Did {own} pass? Unknown.", f"{own}: PASS; the rest to be done.",
                 f"{own}: PASS; the security review is unfinished.",
                 f"{own}: PASS; a partial review.",
                 f"{own}: PASS; the review is not yet done.", f"{own}: PASS; findings to come.",
                 f"Findings w<i></i>ill be added la<i></i>ter at {own}: PASS.",
                 f"PASS at {own}; the review is pen<i></i>ding.",
                 f"PASS at {own}; the review is de<b></b>ferred.",
                 f"{own}: no findings yet.", f"{own}: PASS (preliminary).",
                 f"{own}: PASS; not finished.", f"{own}: TODO; approved for now.",
                 f"{own}: passed, more to do.", f"{own}: PASS (to be continued).",
                 f"{own}: PASS; the second commit is not reviewed.",
                 f"{own}: passed lens A; lens B not started.",
                 f"{own}: passed the first half; the second half is unreviewed.",
                 f"{own}: passed on a skim; the full read is tomorrow.",
                 f"{own}: interim verdict: pass.",
                 f"{own}: provisional PASS, subject to the security reader's sign-off.",
                 f"{own}: approved in principle; details next week.",
                 f"{own}: PASS; the review is still running.",
                 f"{own}: no findings yet; the review continues.",
                 f"the earlier commit passed at {own}, this one is unread",
                 f"{own}: no findings as of now; reading continues.",
                 f"{own}: PASS; haven't read tests/ yet.", f"{own}: PASS; reading continues.",
                 f"{own}: no findings at this point, review continuing.",
                 f"{own}: PASS, review half done.", f"{own}: PASS. Second lens: TBA.",
                 f"{own}: passed up to scripts/; tests/ still unread.",
                 f"{own}: PASS; findings w*i*ll be added la*t*er.",
                 f"{own}: PASS; the review is pen**d**ing.",
                 f"{own}: PASS; the review is in*complete*.",
                 f"{own}: PASS; findings to co`m`e.",
                 f"{own}: PASS; the review is out**stand**ing.",
                 f"{own}: PASS; findings _will_ be added.",
                 f"{own}: PASS; findings ~~w~~ill be added.",
                 *(f"{own}: PASS; findings wi{mark}ll be added, the review pend{mark}ing."
                   for mark in ("\N{HANGUL FILLER}", "\N{HANGUL CHOSEONG FILLER}",
                                "\N{HANGUL JUNGSEONG FILLER}",
                                "\N{HALFWIDTH HANGUL FILLER}", "⁥", "￰",
                                "\U000e0002", "\N{COMBINING GRAPHEME JOINER}")))
        for cell in cells:
            for key, label in (("code_review", "/code-review"),
                               ("security_review", "/security-review")):
                with self.subTest(cell=cell, key=key):
                    text = body([dict(self.row, **{key: cell})])
                    self.refused(f"{label} says", text=text)
                    self.assertIn("a review cell may not say",
                                  "\n".join(train.body_problems(text)))
        # The rest of the review's B1 cells, which name no listed word: no verdict stands
        # in the clause that names the commit.
        for cell in (f"Started at {own}; CI passed.",
                     f"{own}: findings to be written up at the merge; PASS.",
                     f"{own}: passed (partial).", f"{own}: PASS, incomplete."):
            for key, label in (("code_review", "/code-review"),
                               ("security_review", "/security-review")):
                with self.subTest(cell=cell, key=key):
                    self.refused(f"{label} gives no visible review verdict",
                                 text=body([dict(self.row, **{key: cell})]))

    def test_review_cells_must_give_a_verdict_that_stands(self):
        # A verdict, not any letter: none negated, hedged or as a noun ("pass" after "a
        # first" or "quick"), and none that either reading lacks or negates.
        own = self.member[:12]
        cells = (f"Findings at {own}: see the thread.", f"Reviewed {own}.",
                 f"{own}: may have passed", f"{own}: almost passed",
                 f"{own}: would have passed", f"{own}: not fully passed",
                 f"{own}: hasn't actually passed", f"{own}: never really approved",
                 f"{own}: nothing passes", f"{own}: didnt pass",
                 f"{own}: hasn\N{MODIFIER LETTER APOSTROPHE}t actually passed",
                 f"A first pass at {own}.", f"Quick pass at {own}: clean.",
                 f"{own}: two passes.", f"{own}: n<i></i>ot passed.",
                 f"{own}: <span title='PASS'>notes</span>",
                 f"{own}: <span title='not'></span> passed.",
                 # Markdown inside a word hides no negation, and a struck verdict is none.
                 f"{own}: ne**v**er passed.", f"{own}: n_o_t passed.", f"{own}: ~~passed~~",
                 f"{own}: ~PASS~, no notes.", f"{own}: ~~PASS, no findings~~ (see thread)",
                 # A verdict beside capitals, which name no commit as the commit is read.
                 f"Reviewed {own}; ABCDEF1: PASS.")
        for cell in cells:
            for key, label in (("code_review", "/code-review"),
                               ("security_review", "/security-review")):
                with self.subTest(cell=cell, key=key):
                    self.refused(f"{label} gives no visible review verdict",
                                 text=body([dict(self.row, **{key: cell})]))
        self.refused("/code-review gives no visible review verdict",
                     text=body([dict(self.row, code_review=f"{own}: not required.")]))
        for cell in (f"{own}: not in scope, fixed.", f"Final PASS at {own}.",
                     f"{own}: the second pass found nothing.",
                     f"Re-review after the merge of main at {own}: PASS.",
                     f"{own}: PASS; two minors sent to follow-up #245."):
            with self.subTest(cell=cell):
                self.assertEqual(self.problems(text=body([dict(self.row, code_review=cell)])),
                                 [])

    def test_each_listed_word_refuses_alone(self):
        # Each word of the lists, the only one in its cell, after a verdict that stands
        # beside the commit: the refusal names that word, so no word can leave a list
        # unnoticed, and "later" is read before each word that says when.
        own = self.member[:12]
        words = (
            ("the review is pending", "pending"), ("TBD", "tbd"), ("TBC", "tbc"),
            ("TBA", "tba"), ("WIP", "wip"), ("findings will be added", "will"),
            ("findings to come", "to come"), ("not needed", "not needed"),
            ("the rest is outstanding", "outstanding"), ("in progress", "in progress"),
            ("under way", "under way"), ("underway", "underway"), ("ongoing", "ongoing"),
            ("awaiting the lens", "awaiting"), ("waiting on CI", "waiting"),
            ("so far", "so far"), ("still to read tests/", "still to"),
            ("lens B not started", "not started"), ("not finished", "not finished"),
            ("tests/ not reviewed", "not reviewed"), ("tests/ unreviewed", "unreviewed"),
            ("preliminary", "preliminary"), ("provisional", "provisional"),
            ("the read continues", "continues"), ("the read continuing", "continuing"),
            ("the read resumes", "resumes"), ("the rest tomorrow", "tomorrow"),
            ("details next week", "next week"), ("approved for now", "for now"),
            ("CI still running", "still running"), ("half done", "half done"),
            ("in principle", "in principle"), ("N/A", "n/a"), ("TODO", "todo"),
            ("more to do", "to do"), ("notes to follow", "to follow"),
            ("no findings yet", "yet"), ("tests/ still unread", "still unread"),
            ("tests/ is unread", "is unread"), ("tests/ are unread", "are unread"),
            ("tests/ remains unread", "remains unread"),
            ("tests/ remain unread", "remain unread"), ("tests/ stays unread", "stays unread"),
            ("tests/ stay unread", "stay unread"), ("tests/ left unread", "left unread"),
            ("tests/ marked as unread", "as unread"),
            ("notes after the merge", "after the merge"), ("notes after merge", "after merge"),
            ("notes later", "later"), ("which run?", "?"),
            *((f"notes to be {verb}", f"to be {verb}") for verb in (
                "added", "given", "reported", "reviewed", "read", "run", "completed",
                "finished", "confirmed", "decided", "determined", "continued")),
            *((f"notes later {when} noon", "later") for when in (
                "at", "on", "in", "by", "today", "tonight", "tomorrow", "this", "next",
                "when", "once", "after", "with", "for", "if", "and", "or", "but")))
        for fragment, word in words:
            with self.subTest(fragment=fragment):
                self.refused(f"/code-review says {word!r}",
                             text=body([dict(self.row, code_review=f"{own}: PASS; {fragment}.")]))

    def test_a_negation_or_hedge_alone_unseats_a_verdict(self):
        # Each negation, modal or hedge alone before the cell's one verdict, and one three
        # words before it: the verdict is none.
        own = self.member[:12]
        cells = (f"{own}: not really fully passed.", f"{own}: hasn't passed.",
                 *(f"{own}: {word} passed." for word in (
                     "not", "no", "never", "neither", "nor", "nothing", "cannot", "without",
                     "to", "be", "being", "would", "could", "should", "might", "may",
                     "must", "can", "shall", "if", "unless", "until", "once", "when",
                     "whether", "almost", "nearly", "hardly", "barely", "probably",
                     "possibly", "perhaps", "maybe", "likely", "aint", "arent", "cant",
                     "couldnt", "didnt", "doesnt", "dont", "hadnt", "hasnt", "havent",
                     "isnt", "mightnt", "mustnt", "neednt", "shant", "shouldnt", "wasnt",
                     "werent", "wont", "wouldnt")))
        for cell in cells:
            with self.subTest(cell=cell):
                self.refused("/code-review gives no visible review verdict",
                             text=body([dict(self.row, code_review=cell)]))

    def test_the_third_reading_and_the_clauses_are_linear(self):
        # 200,000 characters of struck spans that never close, of Markdown markers, of
        # invisible letters, of clauses each holding a verdict, and of separators after a
        # verdict that an unfinished word might follow.
        size = 200_000
        for cell in ("~" * size, "~~" + "x" * size, "*" * size, "`" * size, "_" * size,
                     "~a" * (size // 2), "passed. " * (size // 8),
                     "abcdef1 passed; " * (size // 16), "pass ~" * (size // 6),
                     "\N{HANGUL FILLER}" * size, "\U000e0100" * size,
                     "passed (" + " " * size + "x", "pass in" + " " * size + "x",
                     "<p " * (size // 3), "<p" * (size // 2), "<br " * (size // 4),
                     "[a](" * (size // 4)):
            with self.subTest(cell=cell[:12]):
                self.assertGreaterEqual(len(cell), size - 200)
                started = time.perf_counter()
                train._placeholder_word(f"{self.member} {cell}")
                train._review_content(f"{self.member} {cell}", security=True)
                train._says_not_required(f"{self.member} {cell}")
                self.assertLess(time.perf_counter() - started, 1.0)

    def test_markup_hides_not_required_from_neither_reading(self):
        # A protected member's security cell, "not required" split by markup that a
        # reader does not see.
        member = self.commit([self.base], {CHECK: "print('reviewed check')\n"})
        head = self.merge(self.base, member)
        for cell in (f"Security reader at {member}: not <em>required</em>.",
                     f"Security reader at {member}: PASS; not<i></i> required.",
                     f"Security reader at {member}: PASS; not[](#x) required.",
                     f"Security reader at {member}: PASS; n*o*t required.",
                     f"Security reader at {member}: PASS; no`t` required.",
                     f"Security reader at {member}: PASS; ~~not~~ required.",
                     f"Security reader at {member}: PASS; n[o](#x)t required.",
                     f"Security reader at {member}: PASS; not\N{HANGUL FILLER}required."):
            with self.subTest(cell=cell):
                self.refused("/security-review says Not required for protected paths",
                             head=head, text=body([member_row(member, security_review=cell)],
                                                  f"- check: {CHECK}"))

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

    def test_the_coordinator_s_fed_rows_pass(self):
        # Completed cells from the coordinator's fed rows, as written, each with a verdict
        # in a clause that names a commit: words that say other work is deferred, follows,
        # is interim, is not done or went unread ("the deferred hardening", "the write
        # follows", "#116's interim texts", "promotion, not done", "the records were
        # unread", "#240 unread", "notes ... went unread"), another file's run line "to be
        # written at the merge", "found no" as the only verdict, and "final PASS". The
        # commit each names first is the member's, here this fixture's member.
        cells = (
            ("security_review",
             "Independent security reviews (Claude crew): at 2a39c2b7 (PF-sec1) nothing "
             "blocking, three material (bytecode could run in place of a plant or the "
             "runner; a linked plants folder took plants off the protected paths; a plant "
             "could rebind the runner) and five minor; at 5bf660e4 (PF-sec2) two blocking "
             "false claims (the entry status was taken after the regressions load the "
             "plants; exit claims overstated) and one material (the name guard catches "
             "mistakes, not deceit). All fixed by 7afb9a1e; the deferred hardening is filed "
             "as #221, #222 and #223. Protected files: scripts/negative_tests.py, "
             "tests/test_negative_tests.py and the 44 plant files, all named in the "
             "decision entry. Needs the label security-review."),
            ("security_review",
             "Independent security review (C7-scaf-rev) at f3a0b097: pass. No check "
             "weakened or bypassed: signature strings, docstrings, one comment and a rename "
             "in a hand-run tool that no check, test, CI job or harness imports; no new file "
             "input; scripts/scaffold_book.py named in the decisions entry (guard_protected "
             "ok); keep_apart refuses nothing; secret scan ok. One minor finding in older "
             "code (B1: the book argument used before it is checked, and the write follows "
             "a dangling symlink) for a check change of its own before Book IV's scaffold "
             "step. safe_push dry run of d299e04a with origin/main 0a05f96f merged "
             "(314166b9): passed every check, steps 1 to 4, both origin/main's and the "
             "commit's checks and negative tests (1509 s). Needs the label security-review."),
            ("code_review",
             "Independent reviews (Claude crew). Lean: every proof read in full by a reader "
             "who wrote none of it (G2-rd-cut, rd-cells, rd-loops2, rd-arr, rd-cover, "
             "rd-diag, rd-extract, rd-fan, rd-bound, rd-polish, and rd-proto for ship G's 19 "
             "October prototype): all approve or approve with minor findings, save rd-bound "
             "(changes required: two false module notes, fixed in G2-polish and re-read by "
             "rd-polish, approve with minor). Standards (G2-cr-std, at b2c0580a, the final "
             "Lean, unchanged since): changes required; B1 (no recorded approval for proofs "
             "in Staging) answered by the decision entry, which records the coordinator's "
             "assignment of 20 October; M2 (stale brief) fixed by the docs rounds; M3 met "
             "(#116, blocks-release, named under Unfinished work); M1 (outline_bounded's "
             "I.23 import reaches Outline.lean's importers) recorded as an owner approval "
             "item for promotion, not done, since moving a staged statement needs approval; "
             "its minors are on the brief's before-promotion list. Spec (G2-cr-spec, at "
             "e8db9f89): changes required, F1 material (the approvals list missed #116's "
             "interim texts) and F2-F5 minor, all fixed. Docs: rd-docs and rd-docs2 asked "
             "for changes (fixed in two rounds, G2-docs2 to G2-docs5b); G2-rd-docs3 at "
             "76cb183a approve with minor (no blocking or material); the entry's move to "
             "docs/decisions/ (#254), G2-rd-entry at d1a02ed4, approve with minor. "
             "Remaining minors go to a follow-up card (text given to the coordinator)."),
            ("code_review",
             "Independent crew review, Claude Opus 5.5 (ER-cr126, Standards and Spec) at "
             "527dddc7: Standards FAIL (Book III's brief contradicted by the Lean; the entry "
             "and addendum said the records were unread after they were stamped; "
             "Touching.Near is Surrounds by rfl and no text said so), Spec PASS (all "
             "eighteen moved declarations equal the staged ones by Lean; no staged theorem "
             "duplicates a fact of Elements). Fixed in a245221b1; delta re-review ER-cr126b "
             "at 2c4499d6a: Standards PASS, Spec PASS, two wording minors in the entry fixed "
             "in de8d97152 (the second and last fix round); /no-mistakes passed again there. "
             "Proposals and minors left to cards: define Touching.Near through Surrounds "
             "before release (the owner's); FORMALIZATION's row for touching circles and the "
             "rule for companions; the steps' namespaces."),
            ("code_review",
             "Independent Claude crew code review, Standards and Spec, of "
             "8fbee723..fe1118b0 (RT-cr6): Standards PASS with minor findings, Spec FAIL on "
             "two false sentences in the addendum and #240 unread; fix round 1 (f87bd4e4) "
             "re-reviewed (RT-cr7): one blocking point, a sign-off count against moving "
             "branches; fix round 2 (8f404de2) re-reviewed (RT-cr8): PASS, no blocking "
             "point. Minors left for follow-up cards: chapter notes for six works in the "
             "reading list, Prop23.lean line 55's wording, I.18's re-stamp after its reading "
             "line's change."),
            ("security_review",
             "Independent security review in both rounds (Claude crew), told to find any "
             "path by which a file on disk, an environment variable set by the commit's "
             "code, or a moved main lets step 4 be skipped. Round 0: no such route; "
             "material, notes for the security review went unread with --land (now held), "
             "and the harness check re-read the disk so a moved main's harness could be "
             "matched by a rewritten copy (now a moved main is refused before the harness). "
             "Confirmation at 9765c407: PASS; a differential probe of keep_apart over 4000 "
             "reports identical before and after; no route opened. Pre-existing in both "
             "flows, to cards: train_check re-reading safe_push.py from disk (A), fetch "
             "redirection by git settings (B), planted modules and PATH shims. Protected "
             "files named in the entry: scripts/safe_push.py, scripts/test_safe_push.py, "
             "scripts/hooks/safe-push. Needs the label security-review. The commits "
             "accepted at dabd4ebd change only what --land prints and its exit status when "
             "interrupted or refused before the merge: no check, guard or trust decision "
             "moves."),
            ("code_review",
             "Independent Claude crew code review (RT-cr35), Standards and Spec, at "
             "5ed77255: Standards PASS with one minor finding (the run line, to be written "
             "at the merge with text/cross-family-signoff-B, as the intro gives), Spec "
             "PASS. Every -- line identical; the mishnah blob identical to a557715d's; no "
             "other place on I.35's page over-credits Proclus. Since then only the merge of "
             "main at 31e2ab77, whose one hand-resolved file (review/I/35.toml) takes "
             "exactly the stamps and run line that review proposed."),
            ("security_review",
             "Independent security reviews (Claude crew), both rounds: the new step's "
             "routes were checked (root pip.py or pip package: closed by -P; sitecustomize, "
             "usercustomize, .pth, PYTHONSTARTUP, pip.conf in the checkout: not routes; a "
             "changed requirements file: runs code, but the file is under the protected "
             "scripts/, so it needs a decision entry and security-review). Nothing weakened. "
             "Protected files: checks/24-lane-condition.toml, .github/workflows/ci.yml, "
             "scripts/test_safe_push.py, each named in the entry. Needs the label "
             "security-review. RE-POST: the confirmation review at 5499d312 found no new "
             "route: only the exact parser line with the exact string ${{ runner.temp }} may "
             "have a working directory (planted on the other steps: refused; variants such "
             "as ${{runner.temp}}, ${{ runner.temp }}/.., lists, mappings: refused); -I from "
             "runner.temp keeps a root pip.py or pip/ out (planted and run); "
             "$GITHUB_WORKSPACE is the runner's, and no earlier step can rewrite it. "
             "Protected files now also tests/test_check_queue.py, named in the entry."),
            ("security_review",
             "Independent security review (Claude crew) in all three rounds, final PASS at "
             "3533f4f8: the scan refuses at least what it refused before on every file (its "
             "output over the tree is byte-identical to main's); the plant writes only to "
             "temporary trees. Protected paths scripts/check_fidelity.py and "
             "scripts/negative_tests.py, named in the decisions entry; safe_push.py and "
             "ci.yml untouched. Needs the label security-review."),
        )
        for key, cell in cells:
            with self.subTest(cell=cell[:40]):
                self.assertEqual(train.body_problems(body([dict(self.row, **{key: cell})])),
                                 [])
                row = dict(self.row, **{key: self.own(cell, self.member)})
                self.assertEqual(self.problems(text=body([row])), [])
        # Two fed cells that give the verdict only in a sentence of their own, the commit
        # in another: no verdict stands beside the commit, so each refuses.
        for cell in (
                "C7-g-rev, lens B: pass. Nothing weakened against main or the guard at "
                "344423f; losing centre_unique from the pinned absences is no weakening, "
                "since it is a theorem after wave one and cannot appear; a pin on the "
                "proved rules each entry uses is #168's. Both protected paths named whole "
                "in the dated entry. Needs the label security-review.",
                "C7-t429-rev lens C: PASS. The form is strictly additive: kept_expectations "
                "holds from origin/main and from 1e0619d2; dropping the pin, dropping or "
                "changing every, changing field, adding a ref or shrinking excludes all "
                "read as not kept. origin/main's checker fails on this tree only on the "
                "unknown key every; judged_files is empty (both pages change in generated "
                "parts only) and pinned(EXPECTATIONS) holds, so keep_apart notes it and "
                "does not refuse. Each protected file approved in a sentence of its own; no "
                "owner's decision claimed. Needs the label security-review."):
            with self.subTest(refused=cell[:40]):
                row = dict(self.row, security_review=self.own(cell, self.member))
                self.refused("/security-review gives no visible review verdict",
                             text=body([row]))

    def test_a_look_around_cut_short_unseats_a_verdict(self):
        # The look-back reads 60 characters; a negation beyond them, still among the three
        # words before the verdict, leaves it unread, so the verdict does not stand.
        long = "x" * 70
        for cell in (f"1a2b3c4: not {long} fully passed.", f"1a2b3c4: never {long} passed."):
            with self.subTest(refused=cell[:24]):
                row = dict(self.row, code_review=self.own(cell, self.member))
                self.refused("/code-review gives no visible review verdict", text=body([row]))
        # Likewise after it: the 20 characters read there must not end inside separators.
        for cell in ("1a2b3c4: passed" + " " * 21 + "(partial).",
                     "1a2b3c4: passed" + " " * 40 + "(partial)."):
            with self.subTest(refused=cell[:24]):
                row = dict(self.row, code_review=self.own(cell, self.member))
                self.refused("/code-review gives no visible review verdict", text=body([row]))
        cell = f"1a2b3c4: read {long} and the rest: passed."
        row = dict(self.row, code_review=self.own(cell, self.member))
        self.assertEqual(self.problems(text=body([row])), [])

    def test_a_stop_inside_a_name_or_number_ends_no_clause(self):
        # Reviewers' cells name their model and files beside the commit ("Claude Opus
        # 5.5", "review/SCHEMA.md", as four fed cells do); a stop between two letters or
        # digits ends no clause, while one before a space, as between sentences, does.
        for cell in ("Independent reader, Claude Opus 5.5, at 1a2b3c4: PASS.",
                     "Reviewed review/SCHEMA.md and docs/ACCEPTANCE.md at 1a2b3c4: PASS.",
                     "1a2b3c4 (v1.2.3): no findings."):
            with self.subTest(passes=cell):
                row = dict(self.row, code_review=self.own(cell, self.member))
                self.assertEqual(self.problems(text=body([row])), [])
        for cell in ("Run https://example.org/runs/1?pr=2 of 1a2b3c4: PASS!",
                     "1a2b3c4 (run https://example.org/runs/1?pr=2): PASS"):
            with self.subTest(passes=cell):
                row = dict(self.row, code_review=self.own(cell, self.member))
                self.assertEqual(self.problems(text=body([row])), [])
        # But an exclamation or question mark, or a stop of another script, ends a clause
        # wherever it stands, as does a line break a reader sees.
        for cell in ("Started at 1a2b3c4. CI passed.", "Started at 1a2b3c4! CI passed.",
                     "Started at 1a2b3c4 .CI passed.", "Started at 1a2b3c4!CI passed.",
                     "Started at 1a2b3c4?CI passed.",
                     "Started at 1a2b3c4\N{IDEOGRAPHIC FULL STOP} CI passed.",
                     "Started at 1a2b3c4\N{ARABIC FULL STOP} CI passed.",
                     "Lens A at 1a2b3c4: started<br>Lens B: PASS",
                     "Lens A at 1a2b3c4: started<br/>Lens B: PASS",
                     "Lens A at 1a2b3c4: started<p>Lens B: PASS",
                     'Lens A at 1a2b3c4: started<br class="x">Lens B: PASS',
                     "Lens A at 1a2b3c4: started<br/ >Lens B: PASS",
                     "Lens A at 1a2b3c4: started<div>Lens B: PASS",
                     "Lens A at 1a2b3c4: started<hr>Lens B: PASS",
                     "Lens A at 1a2b3c4: started<ul><li>Lens B: PASS",
                     "Lens A at 1a2b3c4: started<h4>Lens B: PASS",
                     "Lens A at 1a2b3c4: started<blockquote>Lens B: PASS",
                     "Lens A at 1a2b3c4: started<dd>Lens B: PASS"):
            with self.subTest(refused=cell):
                row = dict(self.row, code_review=self.own(cell, self.member))
                self.refused("/code-review gives no visible review verdict or findings "
                             "beyond the reviewed commit: it must say the review is done "
                             "(pass, approved, fixed, no findings, a number of findings), "
                             "not negated, in the clause that names the commit, which ends "
                             "at every ';', '!', <br> and block tag, every '?' but one "
                             "before a name and '=' (as in a link's query), and every '.' "
                             "but one between two letters or digits (SCHEMA.md, 5.5)",
                             text=body([row]))

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

    def test_workflow_change_with_judged_content_across_members(self):
        workflow = ".github/workflows/ci.yml"
        member = self.commit([self.base], {workflow: "name: reviewed workflow\n"})
        head = self.merge(self.head, member)
        row = member_row(member, "tooling/workflow",
                         security_review=f"Security reader at {member}: PASS.")
        self.refused("check changes must be kept apart from judged content", head=head,
                     text=body([self.row, row],
                               f"- check: {workflow}\n- propositions: I.1"))

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
