#!/usr/bin/env python3
"""Exercise queue refusals in throwaway git repositories, without network or Lean.

    python3 -I tests/test_check_queue.py

Fixtures write objects with hash-object, mktree and commit-tree. Their own index
and checkout use read-tree; the source repository's index and history never move.
Every CLI invocation supplies --github-json, so missing fixture data cannot cause
a GitHub request.
"""

from __future__ import annotations

import copy
import json
import os
import shutil
import subprocess
import sys
import tempfile
import textwrap
import time
import unittest
from pathlib import Path
from unittest.mock import patch

sys.dont_write_bytecode = True
SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
import check_queue as queue

PAGE = queue.safe_push.DECISIONS
TEXT = "notes/first.txt"
SECOND = "notes/second.txt"
CHECK = "scripts/check_sample.py"
TEST = "tests/test_check_sample.py"
BOT = "revert-fixture[bot]"
REVIEW = "Independent reader at"


def harness_source(comment, extra=()):
    """A fixture harness: a comment, and CHECKS and NEGATIVE lists naming the real checks
    (and any extra ones), as check_queue reads them by ast."""
    checks = [name for name, _ in queue.safe_push.CHECKS] + list(extra)
    negative = [name for name, _ in queue.safe_push.NEGATIVE]
    return (f"# {comment}\n"
            + "CHECKS = [\n" + "".join(f"    ({n!r}, None),\n" for n in checks) + "]\n"
            + "NEGATIVE = [\n" + "".join(f"    ({n!r}, None),\n" for n in negative) + "]\n")

class QueueTests(unittest.TestCase):
    """Build two real trains and GitHub-style group merges for each test."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        env = {key: value for key, value in os.environ.items()
               if not key.startswith(("GIT_", "GH_", "GITHUB_", "STOICHEIA_REVERT_"))
               and key != "ACCEPTANCE_VERDICTS"}
        env.update({
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_AUTHOR_NAME": "Queue fixture",
            "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
            "GIT_COMMITTER_NAME": "Queue fixture",
            "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
            "GIT_AUTHOR_DATE": "2026-10-20T12:00:00+00:00",
            "GIT_COMMITTER_DATE": "2026-10-20T12:00:00+00:00",
            "GIT_TERMINAL_PROMPT": "0",
            "GIT_ALLOW_PROTOCOL": "",
            "STOICHEIA_REVERT_BOT": BOT,
        })
        self.enterContext(patch.dict(os.environ, env, clear=True))
        self.git("init", "--quiet", "--initial-branch=main")
        self.trees, self.serial = {}, 0
        self.base = self.make([], {
            TEXT: "Before the first train.\n",
            SECOND: "Before the second train.\n",
            PAGE: "## 20 October 2026\n\nA previous decision.\n",
            "Elements/BookI/Prop01.lean": "-- A fixture source.\n",
            "scripts/safe_push.py": harness_source("The fixture's trusted base harness."),
            "scripts/render.py": "print('fixture renderer ran')\n",
            CHECK: "print('old check')\n",
            TEST: "print('old sample test')\n",
            "scripts/test_safe_push.py": "print('safe push test ran')\n",
            "facts.json": "{}\n",
        })
        self.snapshot = {
            "main": {"sha": self.base},
            "pull_requests": {},
            "queue": {"data": {"repository": {"mergeQueue": {"entries": {
                "nodes": [], "pageInfo": {"hasNextPage": False},
            }}}}},
        }
        self.one = self.train(1, {TEXT: "The first train's reviewed line.\n"})
        self.two = self.train(2, {SECOND: "The second train's reviewed line.\n"})
        self.first = self.merge(self.base, self.one, 1)
        self.head = self.merge(self.first, self.two, 2)
        self.fixture = self.root / "github.json"

    def git(self, *args, data=None, codes=(0,)):
        result = subprocess.run(["git", *args], cwd=self.repo, input=data,
                                capture_output=True, text=True)
        if result.returncode not in codes:
            raise AssertionError(f"git {args!r}: {result.returncode}: {result.stderr}")
        return result.stdout

    def tree(self, files):
        nested = {}
        for path, text in files.items():
            current = nested
            parts = path.split("/")
            for part in parts[:-1]:
                current = current.setdefault(part, {})
            current[parts[-1]] = text

        def write(node):
            entries = []
            for name, value in sorted(node.items()):
                if isinstance(value, dict):
                    sha, mode, kind = write(value), "040000", "tree"
                else:
                    sha = self.git("hash-object", "-w", "--stdin", data=value).strip()
                    mode, kind = "100644", "blob"
                entries.append(f"{mode} {kind} {sha}\t{name}\0")
            return self.git("mktree", "-z", data="".join(entries)).strip()

        return write(nested)

    def make(self, parents, changes=None, tree=None, subject=None):
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
            files = {p: self.git("show", f"{tree}:{p}") for p in paths if p}
        args = ["commit-tree", tree]
        for parent in parents:
            args.extend(("-p", parent))
        self.serial += 1
        sha = self.git(*args, data=(subject or f"Fixture {self.serial}") + "\n").strip()
        self.trees[sha] = files
        return sha

    def merge(self, first, second, number=None, changes=None, subject=None):
        if changes is None:
            tree = self.git("merge-tree", "--write-tree", first, second).strip()
            return self.make([first, second], tree=tree, subject=subject or (
                f"Merge pull request #{number} from owner/train-{number}" if number
                else "Merge reviewed member"))
        return self.make([first, second], changes, subject=(
            f"Merge pull request #{number} from owner/train-{number}"))

    def block(self, head, base=None, harness=None, harness_commit=None, legacy=False):
        base = base or self.base
        harness_commit = harness_commit or base
        blob = self.git("rev-parse", f"{harness_commit}:scripts/safe_push.py").strip()
        harness = harness or f"origin/main's `scripts/safe_push.py` (blob `{blob[:12]}`)"
        marker = "" if legacy else f" harness={harness_commit}"
        lines = [f"<!-- safe_push:preflight begin sha={head} base={base}{marker} -->",
                 f"Pre-flight of `{head[:12]}` against origin/main `{base[:12]}`, by {harness}.",
                 "", "Verdict: PASS.", "", "| Step | Outcome | Seconds |", "|---|---|---|"]
        lines.extend(f"| 4. {name} | ok | 1.0 |"
                     for name, _ in (*queue.safe_push.CHECKS, *queue.safe_push.NEGATIVE))
        return "\n".join([*lines, "<!-- safe_push:preflight end -->"])

    def train(self, number, changes, start=None, new="None."):
        start = start or self.base
        member = self.make([start], changes)
        head = self.merge(start, member)
        body = (
            "## Members\n\n"
            "| Branch | Head | /code-review | /security-review | /no-mistakes |\n"
            "|---|---|---|---|---|\n"
            f"| content/{number} | {member} | {REVIEW} {member[:12]}: pass, no findings. | "
            f"{REVIEW} {member[:12]}: pass, no findings. | passed at {member} |\n\n"
            f"## What is new\n\n{new}\n\n" + self.block(head)
        )
        self.pr(number, head, f"train/area-{number}", body)
        return head

    def pr(self, number, head, ref, body, labels=None, author=None):
        self.snapshot["pull_requests"][str(number)] = {
            "number": number,
            "head": {"sha": head, "ref": ref, "repo": {"full_name": "owner/repository"}},
            "body": body,
            "labels": [{"name": label} for label in (labels or ["tooling"])],
            "state": "open", "merged": False, "merge_commit_sha": None,
            "user": author or {"login": "fixture", "type": "User"},
        }
        nodes = self.nodes()
        for node in nodes:
            if node["pullRequest"]["number"] == number:
                node["pullRequest"]["headRefOid"] = head
                break
        else:
            nodes.append({"position": len(nodes) + 1,
                          "enqueuer": {"__typename": "User", "login": "fixture"},
                          "pullRequest": {"number": number, "headRefOid": head,
                                          "editor": None}})

    def nodes(self):
        return self.snapshot["queue"]["data"]["repository"]["mergeQueue"]["entries"]["nodes"]

    def body(self, number=1):
        return self.snapshot["pull_requests"][str(number)]["body"]

    def set_body(self, body, number=1):
        self.snapshot["pull_requests"][str(number)]["body"] = body

    def checkout(self, head):
        self.git("read-tree", "--reset", "-u", head)
        self.git("update-ref", "HEAD", head)

    def cli(self, *extra, head=None, tree=False, prepare=True, snapshot=True):
        head = head or self.head
        if prepare:
            self.checkout(head)
        if snapshot:
            self.fixture.write_text(json.dumps(self.snapshot), encoding="utf-8")
        args = ["--tree", str(self.repo)] if tree else [
            "--head", head, "--base", self.base, "--repo", "owner/repository",
            "--github-json", str(self.fixture),
        ]
        return subprocess.run([sys.executable, "-I", str(SCRIPTS / "check_queue.py"),
                               *args, *extra], cwd=self.repo, capture_output=True, text=True)

    def verdict(self, result, code, *messages):
        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, code, output)
        for message in messages:
            self.assertIn(message, output)
        return output

    def test_two_trains_pass(self):
        self.verdict(self.cli(), 0, "queue: PASS")

    def test_later_train_overwrites_reviewed_line(self):
        second = self.train(2, {TEXT: "A later train overwrote the reviewed line.\n"},
                            start=self.one)
        group = self.merge(self.first, second, 2)
        self.verdict(self.cli(head=group), 1, "not overwriting", TEXT, "overwritten")

    def test_later_train_restores_original_content(self):
        two = self.train(2, {TEXT: self.trees[self.base][TEXT]}, start=self.one)
        self.verdict(self.cli(head=self.merge(self.first, two, 2)), 1,
                     "not overwriting", TEXT)

    def test_later_train_removes_added_file(self):
        path = "notes/added.txt"
        one = self.train(1, {path: "An added line.\n"})
        first = self.merge(self.base, one, 1)
        two = self.train(2, {path: None}, start=one)
        self.verdict(self.cli(head=self.merge(first, two, 2)), 1, "not overwriting", path)

    def test_later_train_restores_deleted_file(self):
        one = self.train(1, {TEXT: None})
        first = self.merge(self.base, one, 1)
        two = self.train(2, {TEXT: self.trees[self.base][TEXT]}, start=one)
        self.verdict(self.cli(head=self.merge(first, two, 2)), 1, "not overwriting", TEXT)

    def test_current_members_cannot_name_the_base_or_an_unrelated_head(self):
        original = self.body()
        member = queue.parents(self.repo, self.one)[1]
        unrelated = self.make([self.base], {"notes/unrelated.txt": "Unrelated.\n"})
        for replacement in (self.base, unrelated):
            with self.subTest(replacement=replacement):
                self.set_body(original.replace(member, replacement))
                self.verdict(self.cli(), 1, "row has no unique member merge")

    def test_current_members_cannot_omit_a_merged_member(self):
        extra = self.make([self.base], {"notes/extra.txt": "Another member.\n"})
        head = self.merge(self.one, extra)
        body = self.body().replace(self.block(self.one), self.block(head))
        self.pr(1, head, "train/area-1", body)
        first = self.merge(self.base, head, 1)
        self.verdict(self.cli(head=self.merge(first, self.two, 2)), 1,
                     "has no Members row")

    def test_decisions_loses_an_earlier_added_line(self):
        original = self.trees[self.base][PAGE]
        one = self.train(1, {PAGE: original + "\nThe first train's decision.\n"})
        first = self.merge(self.base, one, 1)
        two = self.train(2, {PAGE: original + "\nThe second train's decision.\n"}, start=one)
        group = self.merge(first, two, 2)
        self.verdict(self.cli(head=group), 1, "decisions added lines are missing or out of order")

    def test_decisions_added_lines_must_keep_order_and_multiplicity(self):
        original = self.trees[self.base][PAGE]
        for later in ("\nBeta.\nAlpha.\nAlpha.\n", "\nAlpha.\nBeta.\n"):
            with self.subTest(later=later):
                one = self.train(1, {PAGE: original + "\nAlpha.\nBeta.\nAlpha.\n"})
                first = self.merge(self.base, one, 1)
                two = self.train(2, {PAGE: original + later}, start=one)
                self.verdict(self.cli(head=self.merge(first, two, 2)), 1,
                             "decisions added lines are missing or out of order")

    def test_preflight_names_another_head(self):
        self.set_body(self.body().replace(f"sha={self.one}", f"sha={self.two}"))
        self.verdict(self.cli(), 1, "pre-flight: sha differs")

    def test_preflight_is_missing(self):
        self.set_body(queue.PREFLIGHT.sub("", self.body()))
        self.verdict(self.cli(), 1, "pre-flight: missing or malformed block")

    def test_preflight_names_another_harness_blob(self):
        old = self.git("rev-parse", f"{self.base}:scripts/safe_push.py").strip()
        wrong = self.git("rev-parse", f"{self.base}:{TEXT}").strip()
        self.set_body(self.body().replace(old[:12], wrong[:12]))
        self.verdict(self.cli(), 1,
                     "harness blob is not the recorded harness commit's safe_push.py")

    def test_preflight_hidden_duplicated_or_malformed_refuses(self):
        original = self.body()
        block = queue.PREFLIGHT.search(original).group()
        for replacement in ("```\n" + block + "\n```", "<!-- hidden\n" + block + "\n-->",
                            block + "\n" + block, block.replace("sha=", "sha=BAD")):
            with self.subTest(replacement=replacement[:30]):
                self.set_body(original.replace(block, replacement))
                self.verdict(self.cli(), 1, "pre-flight:")

    def test_preflight_skipped_full_checks_refuses(self):
        self.set_body(self.body().replace("by origin/main's",
                                          "full checks skipped; by origin/main's"))
        self.verdict(self.cli(), 1, "full checks skipped")

    def test_preflight_uses_its_recorded_base_harness(self):
        old_base = self.base
        self.base = self.make([old_base], {
            "scripts/safe_push.py": harness_source('A newer main harness.'),
        })
        self.snapshot["main"]["sha"] = self.base
        first = self.merge(self.base, self.one, 1)
        self.verdict(self.cli(head=self.merge(first, self.two, 2)), 0, "queue: PASS")

    def test_legacy_preflight_uses_its_base_as_harness_commit(self):
        for number, head in ((1, self.one), (2, self.two)):
            self.set_body(queue.PREFLIGHT.sub(self.block(head, legacy=True), self.body(number)),
                          number)
        self.verdict(self.cli(), 0, "queue: PASS")

    def test_preflight_harness_may_be_newer_than_its_comparison_base(self):
        old_base = self.base
        self.base = self.make([old_base], {
            "scripts/safe_push.py": harness_source('Updated main harness.')})
        self.snapshot["main"]["sha"] = self.base
        for number, head in ((1, self.one), (2, self.two)):
            block = self.block(head, base=old_base, harness_commit=self.base)
            self.set_body(queue.PREFLIGHT.sub(block, self.body(number)), number)
        first = self.merge(self.base, self.one, 1)
        self.verdict(self.cli(head=self.merge(first, self.two, 2)), 0, "queue: PASS")

    def test_preflight_harness_must_have_been_on_main(self):
        off_main = self.make([self.base], {
            "scripts/safe_push.py": harness_source('Untrusted harness.')})
        self.set_body(queue.PREFLIGHT.sub(self.block(self.one, harness_commit=off_main),
                                          self.body()))
        self.verdict(self.cli(), 1, "harness commit was never main")

    def test_preflight_is_judged_by_its_own_harness_checks(self):
        # A check added to main after the pre-flight is not asked of it: CI runs it on
        # the group; the pre-flight is held to the checks its own harness ran.
        old_base = self.base
        self.base = self.make([old_base], {"scripts/safe_push.py": harness_source(
            "A newer harness with a new check.", extra=["python3 scripts/new_check.py"])})
        self.snapshot["main"]["sha"] = self.base
        first = self.merge(self.base, self.one, 1)
        self.verdict(self.cli(head=self.merge(first, self.two, 2)), 0, "queue: PASS")

    def test_preflight_missing_one_of_its_harness_checks_refuses(self):
        name = queue.safe_push.CHECKS[0][0]
        self.set_body(self.body().replace(f"| 4. {name} | ok | 1.0 |\n", ""))
        self.verdict(self.cli(), 1, "steps must run the full checks")

    def test_preflight_harness_without_check_lists_refuses(self):
        old_base = self.base
        self.base = self.make([old_base], {"scripts/safe_push.py": "# No lists.\n"})
        self.snapshot["main"]["sha"] = self.base
        for number, head in ((1, self.one), (2, self.two)):
            block = self.block(head, base=old_base, harness_commit=self.base)
            self.set_body(queue.PREFLIGHT.sub(block, self.body(number)), number)
        first = self.merge(self.base, self.one, 1)
        self.verdict(self.cli(head=self.merge(first, self.two, 2)), 1,
                     "harness's checks could not be read")

    def test_preflight_requires_passing_summary_and_full_steps(self):
        original = self.body()
        for body, message in (
            (original.replace("Verdict: PASS.\n", ""), "one passing verdict"),
            (original.replace("Verdict: PASS.", "Verdict: FAIL."), "one passing verdict"),
            (original.replace("| ok |", "| FAIL |", 1), "contains a FAIL row"),
            (original.replace("| 4. lake build | ok | 1.0 |\n", ""), "run the full checks"),
        ):
            with self.subTest(message=message):
                self.set_body(body)
                self.verdict(self.cli(), 1, message)

    def test_preflight_minimal_forged_block_refuses(self):
        block = self.block(self.one).split("\n\n", 1)[0]
        block += "\n<!-- safe_push:preflight end -->"
        self.set_body(queue.PREFLIGHT.sub(block, self.body()))
        self.verdict(self.cli(), 1, "one passing verdict")

    def test_preflight_record_row_does_not_stand_in_for_the_full_checks(self):
        body = self.body()
        rows = "\n".join(line for line in body.splitlines() if not line.startswith("| 4."))
        record = f"{self.one}-{self.base}.json"
        self.set_body(rows.replace("\n|---|---|---|\n", "\n|---|---|---|\n"
                                   f"| 4. full local checks (record {record}) | skip | |\n"))
        self.verdict(self.cli(), 1, "steps must run the full checks")

    def test_preflight_note_repeating_the_harness_passes(self):
        # safe_push's notes (a record that stood in at the merge) can quote the harness
        # phrase again; only the summary's first line names the harness.
        blob = self.git("rev-parse", f"{self.base}:scripts/safe_push.py").strip()
        note = (f"Notes: full local checks: run on {self.one[:12]} by origin/main's "
                f"`scripts/safe_push.py` (blob `{blob[:12]}`), forged time.")
        self.set_body(self.body().replace("<!-- safe_push:preflight end -->",
                                          note + "\n<!-- safe_push:preflight end -->"))
        self.verdict(self.cli(), 0, "queue: PASS")

    def test_harness_must_have_been_main_itself(self):
        side = self.make([self.base], {"scripts/safe_push.py": harness_source("A side harness.")})
        joined = self.merge(self.base, side)
        self.base = joined
        self.snapshot["main"]["sha"] = self.base
        for number, head in ((1, self.one), (2, self.two)):
            block = self.block(head, base=self.git("merge-base", head, joined).strip(),
                               harness_commit=side)
            self.set_body(queue.PREFLIGHT.sub(block, self.body(number)), number)
        first = self.merge(self.base, self.one, 1)
        self.verdict(self.cli(head=self.merge(first, self.two, 2)), 1,
                     "harness commit was never main")

    def test_preflight_harness_older_than_its_base_refuses(self):
        # The block names a harness on main's chain, but one older than the base it
        # compared against: a harness that lacked checks main ran by then.
        old_base = self.base
        self.base = self.make([old_base], {
            "scripts/safe_push.py": harness_source("A newer main harness.")})
        self.snapshot["main"]["sha"] = self.base
        self.nodes().clear()
        one = self.train(1, {TEXT: "A train pre-flighted on the newer main.\n"})
        self.set_body(queue.PREFLIGHT.sub(self.block(one, harness_commit=old_base),
                                          self.body()))
        self.verdict(self.cli(head=self.merge(self.base, one, 1)), 1,
                     "harness commit is older than the recorded base")

    def test_preflight_base_older_than_the_head_s_newest_main_refuses(self):
        # The block names an old main commit as both base and harness (as b7aac65f of
        # 17 October, whose harness lacks later checks), for a head built on a newer
        # main: safe_push records origin/main's tip, the newest main the head contains.
        old_base = self.base
        self.base = self.make([old_base], {
            "scripts/safe_push.py": harness_source("A newer main harness.")})
        self.snapshot["main"]["sha"] = self.base
        self.nodes().clear()
        one = self.train(1, {TEXT: "A train pre-flighted on the newer main.\n"})
        group = self.merge(self.base, one, 1)
        self.verdict(self.cli(head=group), 0, "queue: PASS")
        self.set_body(queue.PREFLIGHT.sub(self.block(one, base=old_base,
                                                     harness_commit=old_base), self.body()))
        self.verdict(self.cli(head=group), 1, "recorded base is not the newest commit of "
                     "main's first-parent chain that the head contains")

    def test_preflight_base_must_have_been_main(self):
        # The block's base is an ancestor of the group's base, but by a merge's second
        # parent: it was never main's tip.
        side = self.make([self.base], {"notes/side.txt": "A side commit.\n"})
        joined = self.merge(self.base, side)
        self.nodes().clear()
        one = self.train(1, {TEXT: "A train built on the side commit.\n"}, start=side)
        self.base = joined
        self.snapshot["main"]["sha"] = joined
        self.set_body(queue.PREFLIGHT.sub(self.block(one, base=side, harness_commit=joined),
                                          self.body()))
        self.verdict(self.cli(head=self.merge(joined, one, 1)), 1,
                     "recorded base was never main")

    def test_entry_attributes_cannot_make_a_conflicted_merge_automatic(self):
        # The second train adds merge=union for the first train's file. In the group's
        # checkout git's own merge reads it and takes both lines as automatic; the judge
        # reads attributes from the group's base, where the merge conflicts.
        two = self.train(2, {TEXT: "The second train's competing line.\n",
                             ".gitattributes": f"{TEXT} merge=union\n"})
        self.checkout(two)
        union = self.git("merge-tree", "--write-tree", self.first, two).strip()
        group = self.make([self.first, two], tree=union,
                          subject="Merge pull request #2 from owner/train-2")
        self.assertIn("The first train's reviewed line.\n", self.trees[group][TEXT])
        self.assertIn("The second train's competing line.\n", self.trees[group][TEXT])
        self.verdict(self.cli(head=group), 1,
                     f"batching: merge {group[:12]} has conflicts or extra content")

    def test_criss_cross_entry_is_checked_against_every_merge_base(self):
        ahead = self.make([self.base], {"notes/main.txt": "Main's line.\n"})
        early = self.make([self.base], {SECOND: "The entry's early line.\n"})
        main = self.merge(ahead, early)
        entry = self.make([self.merge(early, ahead)], {TEXT: "The entry's reviewed line.\n"})
        self.assertEqual(len(queue.merge_bases(self.repo, entry, main, 3)), 2)
        group = self.merge(main, entry, 3)
        queue.intact(self.repo, main, group, {"number": 3, "head": entry})
        later = self.make([group], {TEXT: "A later entry's overwrite.\n"})
        with self.assertRaisesRegex(queue.Refused,
                                    f"#3 changed lines were overwritten: {TEXT}"):
            queue.intact(self.repo, main, later, {"number": 3, "head": entry})

    def test_entry_without_a_merge_base_is_unreadable_and_named(self):
        unrelated = self.make([], {TEXT: "An unrelated history.\n"})
        with self.assertRaisesRegex(ValueError, "#4: could not read a merge base"):
            queue.merge_bases(self.repo, unrelated, self.base, 4)

    def test_later_train_rewriting_readme_prose_is_caught(self):
        readme = "Prose by hand.\n<!-- scope:I -->\nRow.\n<!-- /scope:I -->\n"
        old_base = self.base
        self.base = self.make([old_base], {"README.md": readme})
        self.snapshot["main"]["sha"] = self.base
        self.nodes().clear()
        one = self.train(1, {"README.md": readme.replace("Prose by hand.", "Prose, reviewed.")})
        member = self.git("rev-parse", f"{one}^2").strip()
        two = self.train(2, {"README.md": readme.replace("Prose by hand.", "Prose, reviewed.")
                             .replace("Row.", "Row, regenerated.")}, start=member)
        first = self.merge(self.base, one, 1)
        group = self.merge(first, two, 2)
        self.verdict(self.cli(head=group), 0, "queue: PASS")
        three = self.train(2, {"README.md": readme.replace("Row.", "Row, regenerated.")},
                           start=member)
        self.verdict(self.cli(head=self.merge(first, three, 2)), 1, "README.md")

    def test_preflight_reads_the_current_writer_with_a_newer_harness(self):
        old_base = self.base
        self.base = self.make([old_base], {
            "scripts/safe_push.py": harness_source('Newer harness.')})
        self.snapshot["main"]["sha"] = self.base
        blob = self.git("rev-parse", f"{self.base}:scripts/safe_push.py").strip()
        for number, head in ((1, self.one), (2, self.two)):
            block = queue.safe_push.preflight_block(head, old_base, {
                "full": True, "harness_sha": self.base, "time": "20 October 2026",
                "harness": f"origin/main's `scripts/safe_push.py` (blob `{blob[:12]}`)",
                "steps": [("4", name, "ok", 1.0)
                          for name, _ in (*queue.safe_push.CHECKS, *queue.safe_push.NEGATIVE)],
            })
            self.set_body(queue.PREFLIGHT.sub(block, self.body(number)), number)
        first = self.merge(self.base, self.one, 1)
        self.verdict(self.cli(head=self.merge(first, self.two, 2)), 0, "queue: PASS")

    def test_preflight_hidden_verdict_or_table_does_not_count(self):
        original = self.body()
        for body in (
            original.replace("Verdict: PASS.", "<!-- Verdict: PASS. -->"),
            original.replace("| Step | Outcome | Seconds |",
                             "```\n| Step | Outcome | Seconds |")
                    .replace("<!-- safe_push:preflight end -->",
                             "```\n<!-- safe_push:preflight end -->"),
        ):
            with self.subTest(body=body):
                self.set_body(body)
                self.verdict(self.cli(), 1, "pre-flight:")

    def test_train_body_evidence_and_declaration_refuse(self):
        original = self.body()
        member = queue.parents(self.repo, self.one)[1]
        review = f"{REVIEW} {member[:12]}: pass, no findings."
        for body, message in (
            (original.replace("## Members", "## No members"), "Members"),
            (original.replace(review, "TODO"), "not written"),
            (original.replace(review, "Independent reader: pass, no findings."),
             "names no reviewed commit"),
            (original.replace(review, f"{REVIEW} {self.base[:12]}: pass, no findings."),
             "names no commit of the member's own history"),
            (original.replace(review, "Not needed (1234567)"),
             "names no commit of the member's own history"),
            (original.replace("## What is new", "## Omitted"), "What is new"),
        ):
            with self.subTest(message=message):
                self.set_body(body)
                self.verdict(self.cli(), 1, message)

    def test_changed_check_must_be_declared(self):
        one = self.train(1, {CHECK: "print('new check')\n"})
        first = self.merge(self.base, one, 1)
        self.verdict(self.cli(head=self.merge(first, self.two, 2)), 1,
                     "What is new: undeclared check", CHECK)

    def test_member_protected_path_needs_security_evidence(self):
        one = self.train(1, {CHECK: "print('new check')\n"}, new=f"- check: {CHECK}")
        member = queue.parents(self.repo, one)[1]
        body = self.body().replace(f"| {REVIEW} {member[:12]}: pass, no findings. | passed",
                                   "| Not required: no protected paths. | passed")
        self.set_body(body)
        first = self.merge(self.base, one, 1)
        self.verdict(self.cli(head=self.merge(first, self.two, 2)), 1,
                     "/security-review says Not required for protected paths")

    def test_head_from_another_repository_refuses(self):
        self.snapshot["pull_requests"]["1"]["head"]["repo"]["full_name"] = "fork/repository"
        self.verdict(self.cli(), 1, "its head is not in owner/repository")

    def test_no_bot_may_write_queue_or_edit_an_ordinary_entry(self):
        # GraphQL spells a bot's login without "[bot]" (the revert App's is
        # "revert-fixture" there), so the actor's type is read, not its login.
        for change in (
                lambda: self.snapshot["pull_requests"]["1"].update(
                    user={"login": BOT, "type": "Bot"}),
                lambda: self.nodes()[0].update(
                    enqueuer={"__typename": "Bot", "login": BOT.removesuffix("[bot]")}),
                lambda: self.nodes()[0]["pullRequest"].update(
                    editor={"__typename": "Bot", "login": BOT.removesuffix("[bot]")})):
            with self.subTest(change=change):
                saved = json.loads(json.dumps(self.snapshot))
                change()
                self.verdict(self.cli(), 1, "a bot wrote, queued or edited")
                self.snapshot = saved

    def test_a_person_s_edit_is_allowed(self):
        self.nodes()[0]["pullRequest"]["editor"] = {"__typename": "User", "login": "someone"}
        self.verdict(self.cli(), 0, "queue: PASS")

    def test_unreadable_enqueuer_refuses(self):
        self.nodes()[0]["enqueuer"] = None
        self.verdict(self.cli(), 2)

    def test_train_skipped(self):
        self.verdict(self.cli(head=self.merge(self.base, self.two, 2)), 1,
                     "skipped train or trains out of queue order")

    def test_trains_out_of_queue_order(self):
        first = self.merge(self.base, self.two, 2)
        self.verdict(self.cli(head=self.merge(first, self.one, 1)), 1,
                     "skipped train or trains out of queue order")

    def test_squashed_entry(self):
        head = self.make([self.base], tree=self.git("rev-parse", f"{self.head}^{{tree}}").strip(),
                         subject="Merge pull request #2 from owner/train-2")
        self.verdict(self.cli(head=head), 1, "must have exactly two parents")

    def test_merge_adds_extra_content(self):
        changes = {**self.trees[self.head], "notes/extra.txt": "Unreviewed.\n"}
        head = self.merge(self.first, self.two, 2, changes=changes)
        self.verdict(self.cli(head=head), 1, "has conflicts or extra content")

    def test_subject_and_queue_must_agree(self):
        head = self.merge(self.first, self.two, 2,
                          subject="Merge pull request #1 from owner/incorrect")
        self.verdict(self.cli(head=head), 1,
                     "merge subject and queue head identify different pull requests")

    def test_queue_head_must_equal_second_parent(self):
        self.snapshot["pull_requests"]["2"]["head"]["sha"] = self.one
        self.verdict(self.cli(), 1, "head differs from the second parent")

    def test_queue_subject_falls_back_only_to_unique_queued_head(self):
        head = self.merge(self.first, self.two, 2, subject="Queue group second entry")
        self.verdict(self.cli(head=head), 0, "queue: PASS")
        self.nodes().pop()
        self.verdict(self.cli(head=head), 1, "cannot identify the merge's pull request")

    def test_already_merged_prefix_is_allowed_only_when_main_holds_it(self):
        pr = self.snapshot["pull_requests"]["1"]
        pr.update(state="closed", merged=True, merge_commit_sha=self.first)
        self.snapshot["main"]["sha"] = self.first
        self.nodes().pop(0)
        self.nodes()[0]["position"] = 1
        self.verdict(self.cli(), 0, "queue: PASS")
        self.snapshot["main"]["sha"] = self.base
        self.verdict(self.cli(), 1, "merged prefix is not held by main")

    def test_closed_unmerged_entry_refuses(self):
        self.snapshot["pull_requests"]["1"]["state"] = "closed"
        self.verdict(self.cli(), 1, "only a merged prefix")

    def test_tree_only_checks_headings_without_rendering(self):
        self.checkout(self.head)
        page = self.repo / PAGE
        original = page.read_text(encoding="utf-8")
        page.write_text(original + "\n## 20 October 2026\n", encoding="utf-8")
        (self.repo / "scripts/render.py").write_text("raise SystemExit(9)\n", encoding="utf-8")
        self.verdict(self.cli(tree=True, prepare=False), 1, PAGE, "repeated dated heading")
        page.write_text(original, encoding="utf-8")
        self.verdict(self.cli(tree=True, prepare=False), 0, "queue: PASS")
        self.verdict(self.cli("--render", tree=True, prepare=False), 1, "render.py failed")

    def test_tree_reads_dated_headings_as_they_render(self):
        self.checkout(self.head)
        page = self.repo / PAGE
        original = page.read_text(encoding="utf-8")
        cyrillic = "## 20 \u041ectober 2026"
        for added, message in (
                (" ## 20 October 2026", "repeated dated heading"),
                ("   ## 20 October 2026", "repeated dated heading"),
                ("## 20 October 2026\u200b", "repeated dated heading"),
                ("## 20 october 2026", "repeated dated heading"),
                ("20 October 2026\n---------------", "repeated dated heading"),
                ("20 October 2026\n===", "repeated dated heading"),
                ("## **20 October 2026**", "repeated dated heading"),
                ("## 20 Oct 2026", "repeated dated heading"),
                ("## October 20, 2026", "repeated dated heading"),
                ("## 2026-10-20", "repeated dated heading"),
                ("## 20\u00a0October\u00a02026", "repeated dated heading"),
                ("## \uff12\uff10 October 2026", "repeated dated heading"),
                (cyrillic, "letters outside ASCII")):
            with self.subTest(added=added):
                page.write_text(original + "\n" + added + "\n", encoding="utf-8")
                self.verdict(self.cli(tree=True, prepare=False), 1, PAGE, message)
        for added in ("## 21 October 2026", "    ## 20 October 2026",
                      "## 20 October 2026: a later note", "### 20 October 2026"):
            with self.subTest(added=added):
                page.write_text(original + "\n" + added + "\n", encoding="utf-8")
                self.verdict(self.cli(tree=True, prepare=False), 0, "queue: PASS")
        page.write_text(original, encoding="utf-8")

    def test_tree_reads_headings_through_html_links_and_containers(self):
        # Character references, inline HTML, link syntax, block quotes and list items
        # are read through; an HTML heading tag is refused rather than read.
        self.checkout(self.head)
        page = self.repo / PAGE
        original = page.read_text(encoding="utf-8")
        for added, message in (
                ("## 20&nbsp;October 2026", "repeated dated heading"),
                ("## 20 Octo&#98;er 2026", "repeated dated heading"),
                ("## 20 October&#x20;2026", "repeated dated heading"),
                ("## [20 October 2026](#x)", "repeated dated heading"),
                ("## [20 October 2026][x]", "repeated dated heading"),
                ("## [20](#a) [October](#b) [2026](#c)", "repeated dated heading"),
                ("## 20 Octo<!-- -->ber 2026", "repeated dated heading"),
                ("## 20 October 2026<span></span>", "repeated dated heading"),
                ("## <em>20 October</em> 2026", "repeated dated heading"),
                ("## 20 October 2026 ##", "repeated dated heading"),
                ("## 20 October 2026 ####   ", "repeated dated heading"),
                ("> ## 20 October 2026", "repeated dated heading"),
                (">## 20 October 2026", "repeated dated heading"),
                ("- ## 20 October 2026", "repeated dated heading"),
                ("1. ## 20 October 2026", "repeated dated heading"),
                ("> - > ## 20 October 2026", "repeated dated heading"),
                ("> 20 October 2026\n> ---", "repeated dated heading"),
                ("<h2>20 October 2026</h2>", "an HTML heading tag"),
                ("<H1 class=\"date\">Any heading</H1>", "an HTML heading tag"),
                ("Some text <h2\nid=x>A heading</h2>", "an HTML heading tag")):
            with self.subTest(added=added):
                page.write_text(original + "\n" + added + "\n", encoding="utf-8")
                self.verdict(self.cli(tree=True, prepare=False), 1, PAGE, message)
        for added in ("## 20 October 2026 [a later note](#x)", "## 20 October 2026 &amp; 21",
                      "> ### 20 October 2026", "<h3>20 October 2026</h3>",
                      "## 20 October 2026 <b>and after</b>", "- 20 October 2026"):
            with self.subTest(added=added):
                page.write_text(original + "\n" + added + "\n", encoding="utf-8")
                self.verdict(self.cli(tree=True, prepare=False), 0, "queue: PASS")
        page.write_text(original, encoding="utf-8")

    def test_long_heading_lines_are_read_in_linear_time(self):
        # A 200,000-character line, in the shapes that once backtracked ("## a", spaces
        # and a last word: about 0.45 s at 8,000 characters, and hours at 200,000) and in
        # those the reading of HTML, links and containers could, is read in under a second.
        size = 200_000
        for line in ("## a" + " " * size + "b", "## a" + " " * size,
                     "## " + "#" * size + " x", "## " + "<" * size,
                     "## " + "<!--" * (size // 4), "## " + "<a" * (size // 2),
                     "## " + "](" * (size // 2), "## " + "][" * (size // 2),
                     "## " + "&#" * (size // 2), "> " * (size // 2) + "## 20 October 2026",
                     "- " * (size // 2), "## 1 " + "a " * (size // 2),
                     "## 20 October 2026" + " " * size + "#"):
            with self.subTest(line=line[:12]):
                self.assertGreaterEqual(len(line), size)
                started = time.perf_counter()
                for _, heading in queue.headings("Paragraph.\n\n" + line + "\n=\n"):
                    queue.heading_date(heading)
                self.assertLess(time.perf_counter() - started, 1.0)

    def test_repeated_dated_heading_refuses(self):
        page = self.trees[self.base][PAGE] + "\n## 20 October 2026\n\nRepeated date.\n"
        one = self.train(1, {PAGE: page})
        first = self.merge(self.base, one, 1)
        head = self.merge(first, self.two, 2)
        self.verdict(self.cli(head=head), 1, PAGE, "repeated dated heading")
        self.verdict(self.cli(head=head, tree=True), 1, "repeated dated heading")

    def test_render_freshness_refuses_modified_and_untracked_generated_files(self):
        for script in (
            "from pathlib import Path\nPath('facts.json').write_text('{\"new\": true}\\n')\n",
            "from pathlib import Path\nPath('book').mkdir(exist_ok=True)\n"
            "Path('book/new.md').write_text('New page.\\n')\n",
        ):
            with self.subTest(script=script):
                one = self.train(1, {"scripts/render.py": script},
                                 new="- check: scripts/render.py")
                first = self.merge(self.base, one, 1)
                group = self.merge(first, self.two, 2)
                # The judge runs no code of the group, so it does not render: the check
                # job does, on the same group; --tree --render is the same reading.
                self.verdict(self.cli(head=group), 0, "queue: PASS")
                self.checkout(group)
                self.verdict(self.cli("--render", tree=True, prepare=False), 1,
                             "render freshness: generated files changed")

    def revert_group(self, extra=False, merges=1):
        old_base, original = self.base, self.trees[self.base]
        self.base = self.first if merges == 1 else self.head
        self.snapshot["main"]["sha"] = self.base
        reverted = [self.first] if merges == 1 else [self.head, self.first]
        changes = {TEXT: original[TEXT]}
        if merges == 2:
            changes[SECOND] = original[SECOND]
        if extra:
            changes["notes/unrelated.txt"] = "An extra change.\n"
        head = self.make([self.base], changes)
        self.nodes().clear()
        self.pr(3, head, f"revert/{self.base[:12]}",
                "Failed run: 71\n" + "\n".join(f"Reverts: {sha}" for sha in reverted) + "\n",
                ["auto-revert"], {"login": BOT, "type": "Bot"})
        self.failed_run(old_base, self.base)
        return self.merge(self.base, head, 3), old_base

    def failed_run(self, before, after):
        self.snapshot["runs"] = {"71": {
            "id": 71, "path": ".github/workflows/post-merge.yml", "event": "push",
            "head_branch": "main", "conclusion": "failure", "head_sha": after,
        }}
        self.snapshot["pushes"] = [[{
            "ref": "refs/heads/main", "activity_type": "push", "before": before, "after": after,
        }]]
        self.snapshot["queue_merges"] = [[]]
        self.snapshot["main_red"] = [[{
            "number": 9, "state": "open", "labels": [{"name": "main-red"}],
            "body": "Run: https://github.com/owner/repository/actions/runs/71\n",
        }]]

    def test_exact_auto_revert_passes(self):
        head, _ = self.revert_group()
        self.verdict(self.cli(head=head), 0, "queue: PASS")

    def test_auto_revert_needs_an_open_main_red_issue_naming_its_run(self):
        head, _ = self.revert_group()
        for issues in ([[]], [[{"number": 9, "state": "open", "labels": [{"name": "main-red"}],
                                 "body": "Run: https://github.com/o/r/actions/runs/710\n"}]]):
            with self.subTest(issues=issues):
                self.snapshot["main_red"] = issues
                self.verdict(self.cli(head=head), 1, "no open main-red issue names")

    def test_auto_revert_branch_must_name_the_failed_push(self):
        head, _ = self.revert_group()
        self.snapshot["pull_requests"]["3"]["head"]["ref"] = "revert/000000000000"
        self.verdict(self.cli(head=head), 1, "the branch must be revert/")

    def test_auto_revert_queued_by_the_bot_passes(self):
        # As GitHub gives it: the revert App's bot queued it, named by GraphQL without "[bot]".
        head, _ = self.revert_group()
        self.nodes()[0]["enqueuer"] = {"__typename": "Bot", "login": BOT.removesuffix("[bot]")}
        self.verdict(self.cli(head=head), 0, "queue: PASS")

    def test_auto_revert_with_extra_change_refuses(self):
        head, _ = self.revert_group(extra=True)
        self.verdict(self.cli(head=head), 1, "not the exact revert tree (extra change)")

    def test_auto_revert_requires_trusted_bot_label_and_branch(self):
        head, _ = self.revert_group()
        pr = self.snapshot["pull_requests"]["3"]
        original = copy.deepcopy(pr)
        for change in ({"user": {"login": "other[bot]", "type": "Bot"}},
                       {"user": {"login": BOT, "type": "User"}},
                       {"head": {**pr["head"], "ref": "tooling/untrusted"}},
                       {"labels": []}):
            with self.subTest(change=change):
                self.snapshot["pull_requests"]["3"] = {**original, **change}
                self.verdict(self.cli(head=head), 1, "configured App bot must agree")
        self.snapshot["pull_requests"]["3"] = original
        os.environ.pop("STOICHEIA_REVERT_BOT")
        self.verdict(self.cli(head=head), 1, "configured App bot must agree")

    def test_auto_revert_multiple_merges_must_be_newest_first(self):
        head, _ = self.revert_group(merges=2)
        self.verdict(self.cli(head=head), 0, "queue: PASS")
        self.set_body("\n".join(reversed(self.body(3).splitlines())) + "\n", 3)
        self.verdict(self.cli(head=head), 1, "named merges must be newest first")

    def test_auto_revert_cannot_name_a_nonmerge_or_off_main_commit(self):
        head, old_base = self.revert_group()
        for sha, message in ((old_base, "must be a merge before its base"),
                             (self.two, "must be a distinct merge on main")):
            with self.subTest(sha=sha):
                self.set_body(f"Failed run: 71\nReverts: {sha}\n", 3)
                self.verdict(self.cli(head=head), 1, message)

    def test_auto_revert_requires_one_visible_failed_run(self):
        head, _ = self.revert_group()
        original = self.body(3)
        for replacement in ("", "Failed run: 71\nFailed run: 71", "Failed run: invalid",
                            "<!-- Failed run: 71 -->", "```\nFailed run: 71\n```"):
            with self.subTest(replacement=replacement):
                self.set_body(original.replace("Failed run: 71", replacement), 3)
                self.verdict(self.cli(head=head), 1, "exactly one Failed run line")

    def test_auto_revert_requires_a_failed_main_post_merge_push(self):
        head, _ = self.revert_group()
        run = self.snapshot["runs"]["71"]
        for key, value in (("path", ".github/workflows/ci.yml"), ("event", "pull_request"),
                           ("head_branch", "train/one"), ("conclusion", "success")):
            with self.subTest(key=key):
                original = run[key]
                run[key] = value
                self.verdict(self.cli(head=head), 1, "failed post-merge push on main")
                run[key] = original

    def test_auto_revert_reads_later_activity_pages_and_queue_merges(self):
        head, _ = self.revert_group()
        activity = self.snapshot["pushes"][0][0]
        self.snapshot["pushes"] = [[], [activity]]
        self.verdict(self.cli(head=head), 0, "queue: PASS")
        self.snapshot["pushes"] = [[]]
        self.snapshot["queue_merges"] = [[], [{**activity, "activity_type": "merge_queue_merge"}]]
        self.verdict(self.cli(head=head), 0, "queue: PASS")

    def test_auto_revert_missing_ambiguous_or_malformed_activity_refuses(self):
        head, _ = self.revert_group()
        original = self.snapshot["pushes"]
        activity = original[0][0]
        for pages, code, message in (
            ([[]], 1, "push is missing or ambiguous"),
            ([[activity, {**activity, "before": self.two}]], 1, "push is missing or ambiguous"),
            ([{}], 2, "could not read a main activity page"),
            ([[{**activity, "before": "invalid"}]], 2, "could not read main push activity"),
            ([[{**activity, "ref": "refs/heads/other"}]], 2, "could not read main push activity"),
        ):
            with self.subTest(pages=pages):
                self.snapshot["pushes"] = pages
                self.verdict(self.cli(head=head), code, message)

    def test_auto_revert_missing_run_or_activity_never_uses_network(self):
        head, _ = self.revert_group()
        original = copy.deepcopy(self.snapshot)
        for kind in ("runs", "pushes", "queue_merges"):
            with self.subTest(kind=kind):
                self.snapshot = {key: value for key, value in original.items() if key != kind}
                self.verdict(self.cli(head=head), 2, f"fixture lacks {kind}")

    def test_auto_revert_with_two_merge_bases_with_main_refuses(self):
        self.revert_group()
        self.fixture.write_text(json.dumps(self.snapshot), encoding="utf-8")
        pr = dict(queue.pull_request(self.snapshot["pull_requests"]["3"], 3), main=self.base)
        api = queue.GitHub("owner/repository", self.fixture)
        with patch.object(queue, "merge_bases", return_value=[self.base, self.one]), \
                self.assertRaisesRegex(queue.Refused, "#3 has more than one merge base"):
            queue.exact_revert(self.repo, pr, api)

    def test_auto_revert_cannot_omit_a_failed_push_merge(self):
        head, _ = self.revert_group(merges=2)
        self.set_body(self.body(3).replace(f"Reverts: {self.first}\n", ""), 3)
        self.verdict(self.cli(head=head), 1, "do not equal the failed push's merges")

    def test_auto_revert_cannot_reverse_an_unrelated_historical_merge(self):
        head, _ = self.revert_group()
        # The run failed only on the next push; the exact earlier reversal is unrelated.
        self.snapshot["main"]["sha"] = self.head
        self.failed_run(self.first, self.head)
        self.verdict(self.cli(head=head), 1, "do not equal the failed push's merges")

    def test_auto_revert_requires_the_failed_push_on_main(self):
        head, _ = self.revert_group()
        self.failed_run(self.base, self.two)
        self.verdict(self.cli(head=head), 1, "range is not on main's first-parent chain")

    def test_activity_boundary_requests_all_pages_for_both_types(self):
        with patch.dict(os.environ, {"GH_TOKEN": "fixture-token"}), \
                patch.object(queue.subprocess, "run", return_value=subprocess.CompletedProcess(
                    [], 0, "[[], []]", "")) as call:
            api = queue.GitHub("owner/repository", None)
            for kind, activity in (("pushes", "push"), ("queue_merges", "merge_queue_merge")):
                self.assertEqual(api.read(kind), [[], []])
                args = call.call_args.args[0]
                self.assertIn("--paginate", args)
                self.assertIn("--slurp", args)
                self.assertIn(f"activity_type={activity}", args[-1])
                self.assertIn("ref=refs/heads/main", args[-1])
            api.read("runs", 71)
            self.assertEqual(call.call_args.args[0][-1], "repos/owner/repository/actions/runs/71")

    def test_unreadable_github_never_passes(self):
        self.fixture.write_text("{unreadable", encoding="utf-8")
        self.verdict(self.cli(snapshot=False), 2, "could not read")
        original = copy.deepcopy(self.snapshot)
        for kind in ("main", "queue", "pull_requests"):
            with self.subTest(missing=kind):
                self.snapshot = {k: v for k, v in original.items() if k != kind}
                self.verdict(self.cli(), 2, "could not read")
        self.snapshot = original
        self.snapshot["pull_requests"]["1"]["labels"] = None
        self.verdict(self.cli(), 2, "could not read pull request #1")

    def test_truncated_duplicate_and_misnumbered_queue_are_unreadable(self):
        original = copy.deepcopy(self.snapshot)
        entries = self.snapshot["queue"]["data"]["repository"]["mergeQueue"]["entries"]
        entries["pageInfo"]["hasNextPage"] = True
        self.verdict(self.cli(), 2, "complete queue in position order")
        self.snapshot = copy.deepcopy(original)
        self.nodes()[0]["position"] = 2
        self.verdict(self.cli(), 2, "complete queue in position order")
        self.snapshot = original
        self.nodes()[1]["pullRequest"] = dict(self.nodes()[0]["pullRequest"])
        self.verdict(self.cli(), 2, "complete queue in position order")

    def test_github_failure_never_prints_token(self):
        with patch.dict(os.environ, {"GH_TOKEN": "private-fixture-token"}), \
                patch.object(queue.subprocess, "run", return_value=subprocess.CompletedProcess(
                    [], 1, "private-fixture-token", "private-fixture-token")) as call:
            with self.assertRaisesRegex(ValueError, "GitHub: could not read queue"):
                queue.GitHub("owner/repository", None).read("queue")
            self.assertEqual(call.call_args.args[0][:3], ["gh", "api", "graphql"])

    def test_fixture_failure_cannot_fall_back_to_network(self):
        self.fixture.write_text("{}", encoding="utf-8")
        with patch.object(queue.subprocess, "run", side_effect=AssertionError("network used")):
            with self.assertRaisesRegex(ValueError, "fixture lacks queue"):
                queue.GitHub("owner/repository", self.fixture).read("queue")

    def test_gaps_runs_changed_check_and_test_once(self):
        one = self.train(1, {CHECK: "raise SystemExit('checks are not tests')\n",
                             TEST: "print('sample test ran')\n"},
                         new=f"- check: {CHECK}\n- check: {TEST}")
        first = self.merge(self.base, one, 1)
        output = self.verdict(self.cli("--gaps", head=self.merge(first, self.two, 2)), 0,
                              f"gaps: python3 -I {TEST}", "sample test ran")
        self.assertEqual(output.count(f"gaps: python3 -I {TEST}"), 1)
        self.assertNotIn(f"gaps: python3 -I {CHECK}", output)

    def test_gaps_runs_a_scripts_test_and_safe_push_special_case(self):
        one = self.train(1, {
            "scripts/another.py": "print('check')\n",
            "scripts/test_another.py": "print('another test ran')\n",
            "scripts/safe_push.py": harness_source('A new fixture harness.'),
        }, new="- check: scripts/another.py\n- check: scripts/test_another.py\n"
               "- check: scripts/safe_push.py")
        first = self.merge(self.base, one, 1)
        self.verdict(self.cli("--gaps", head=self.merge(first, self.two, 2)), 0,
                     "gaps: python3 -I scripts/test_another.py",
                     "gaps: python3 scripts/test_safe_push.py",
                     "another test ran", "safe push test ran")

    def test_gaps_runs_a_changed_script_test_without_its_production_script(self):
        for path, command in (("scripts/test_another.py", "python3 -I"),
                              ("scripts/test_safe_push.py", "python3")):
            with self.subTest(path=path):
                one = self.train(1, {path: "raise SystemExit(7)\n"}, new=f"- check: {path}")
                first = self.merge(self.base, one, 1)
                self.verdict(self.cli("--gaps", head=self.merge(first, self.two, 2)), 1,
                             f"gaps: {command} {path} failed (exit 7)")

    def test_gaps_does_not_require_a_deleted_test(self):
        one = self.train(1, {TEST: None}, new=f"- check: {TEST}")
        first = self.merge(self.base, one, 1)
        output = self.verdict(self.cli("--gaps", head=self.merge(first, self.two, 2)), 0,
                              "queue: PASS")
        self.assertNotIn(f"gaps: python3 -I {TEST}", output)

    def test_exact_auto_revert_selects_nothing_for_deleted_check_and_tests(self):
        old_base = self.base
        changes = {
            "scripts/introduced.py": "print('new check')\n",
            "scripts/test_introduced.py": "raise SystemExit(7)\n",
            "tests/test_introduced.py": "raise SystemExit(7)\n",
        }
        one = self.train(1, changes, new="\n".join(f"- check: {p}" for p in changes))
        self.base = self.merge(old_base, one, 1)
        self.snapshot["main"]["sha"] = self.base
        head = self.make([self.base], {path: None for path in changes})
        self.nodes().clear()
        self.pr(3, head, f"revert/{self.base[:12]}",
                f"Failed run: 71\nReverts: {self.base}\n", ["auto-revert"],
                {"login": BOT, "type": "Bot"})
        self.failed_run(old_base, self.base)
        output = self.verdict(self.cli("--gaps", head=self.merge(self.base, head, 3)), 0,
                              "queue: PASS")
        self.assertNotIn("gaps: python3", output)

    def test_deleted_script_selects_no_surviving_counterpart_test(self):
        one = self.train(1, {CHECK: None}, new=f"- check: {CHECK}")
        self.checkout(one)
        self.assertEqual(queue.gap_commands(self.repo, {CHECK}, {CHECK}), [])

    def queue_job(self, head, base):
        """Execute the workflow's extraction and invocation with local fixture objects."""
        workflow = (SCRIPTS.parent / ".github/workflows/ci.yml").read_text(encoding="utf-8")
        step = workflow.split(
            "      - name: Check the group with main's copy of check_queue.py\n", 1)[1]
        script = textwrap.dedent(step.split("        run: |\n", 1)[1].split("\n\n", 1)[0])
        self.checkout(head)
        runner = self.root / "runner"
        runner.mkdir()
        env = dict(os.environ, GROUP_HEAD=head, GROUP_BASE=base,
                   GITHUB_EVENT_NAME="merge_group", RUNNER_TEMP=str(runner),
                   REPOSITORY="owner/repository")
        return subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script], cwd=self.repo,
                              env=env, capture_output=True, text=True)

    def test_queue_job_executes_the_base_judge_with_all_its_scripts(self):
        script = (
            "import sys\nfrom pathlib import Path\n"
            "sys.path.insert(0, str(Path(__file__).resolve().parent))\n"
            "import safe_push, check_train\nfrom helpers.sample import VALUE\n"
            "assert safe_push.VALUE == check_train.VALUE == VALUE == 'base'\n"
            "print('base judge ran')\n"
        )
        base = self.make([self.base], {
            "scripts/check_queue.py": script, "scripts/safe_push.py": "VALUE = 'base'\n",
            "scripts/check_train.py": "VALUE = 'base'\n",
            "scripts/helpers/sample.py": "VALUE = 'base'\n",
        })
        head = self.make([base], {
            path: "raise SystemExit('group judge ran')\n" for path in (
                "scripts/check_queue.py", "scripts/safe_push.py", "scripts/check_train.py",
                "scripts/helpers/sample.py")
        })
        output = self.verdict(self.queue_job(head, base), 0, "base judge ran")
        self.assertEqual(output.count("base judge ran"), 1)
        self.assertNotIn("group judge ran", output)

    def test_queue_job_refuses_when_only_the_group_has_a_judge(self):
        head = self.make([self.base], {"scripts/check_queue.py": "print('group judge ran')\n"})
        output = self.verdict(self.queue_job(head, self.base), 2, "base has no queue judge")
        self.assertNotIn("group judge ran", output)

    def test_real_judge_imports_its_own_dependencies_with_a_hostile_checkout(self):
        judge = self.root / "judge"
        shutil.copytree(SCRIPTS, judge, ignore=shutil.ignore_patterns("__pycache__"))
        self.checkout(self.head)
        for name in ("check_queue.py", "check_train.py", "safe_push.py", "heath.py"):
            (self.repo / "scripts" / name).write_text("raise SystemExit('hostile script')\n",
                                                     encoding="utf-8")
        result = subprocess.run([sys.executable, "-I", str(judge / "check_queue.py"),
                                 "--tree", str(self.repo)], cwd=self.repo,
                                capture_output=True, text=True)
        self.verdict(result, 0, "queue: PASS")

    def test_gaps_failing_test_refuses(self):
        one = self.train(1, {TEST: "raise SystemExit(7)\n"}, new=f"- check: {TEST}")
        first = self.merge(self.base, one, 1)
        self.verdict(self.cli("--gaps", head=self.merge(first, self.two, 2)), 1,
                     f"gaps: python3 -I {TEST} failed (exit 7)")

    def test_gaps_includes_overdeclared_test(self):
        self.set_body(self.body().replace("None.", f"- check: {TEST}"))
        self.verdict(self.cli("--gaps"), 0, f"gaps: python3 -I {TEST}", "old sample test")

    def test_gaps_missing_declared_test_refuses(self):
        self.set_body(self.body().replace("None.", "- check: tests/test_absent.py"))
        self.verdict(self.cli("--gaps"), 1, "declared test is missing")

    def test_gaps_reports_acceptance_without_judging_it_again(self):
        one = self.train(1, {"Elements/BookI/Prop01.lean": "-- Changed fixture.\n"},
                         new="- propositions: I.1")
        first = self.merge(self.base, one, 1)
        group = self.merge(first, self.two, 2)
        self.verdict(self.cli("--gaps", head=group), 2, "ACCEPTANCE_VERDICTS is required")
        from check_acceptance import VERDICTS_FORMAT
        report = self.root / "verdicts.json"
        report.write_text(json.dumps({
            "format": VERDICTS_FORMAT, "checker": "fixture",
            "verdicts": {"I.1": {"P1": "pass", "P2": "fail"}},
        }), encoding="utf-8")
        os.environ["ACCEPTANCE_VERDICTS"] = str(report)
        self.verdict(self.cli("--gaps", head=group), 0, "I.1 P1: pass", "I.1 P2: fail",
                     "acceptance report only")

    def test_checkout_must_be_the_group_head(self):
        self.checkout(self.base)
        self.verdict(self.cli(prepare=False), 1, "checkout is not the supplied group head")

    def test_unexpected_source_edits_refuse(self):
        self.checkout(self.head)
        (self.repo / TEXT).write_text("A working copy change.\n", encoding="utf-8")
        self.verdict(self.cli(prepare=False), 1, "checkout has source changes")

    def test_deleted_tracked_file_is_unreadable_in_tree_mode(self):
        # Rule (d) reads the decisions page alone; conflict markers are S23's.
        self.checkout(self.head)
        (self.repo / PAGE).unlink()
        self.verdict(self.cli(tree=True, prepare=False), 2, "cannot read the decisions page")

    def test_tree_mode_rejects_group_arguments(self):
        self.verdict(self.cli("--gaps", tree=True), 2, "--tree accepts only --render")


if __name__ == "__main__":
    unittest.main()
