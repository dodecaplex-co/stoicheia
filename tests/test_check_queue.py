#!/usr/bin/env python3
"""Exercise queue refusals in throwaway git repositories, without network or Lean.

    python3 -m pip install -r scripts/requirements-test_safe_push.txt
    python3 -I tests/test_check_queue.py

The workflow cases read .github/workflows/ci.yml with PyYAML, pinned in
scripts/requirements-test_safe_push.txt; install it in a virtual environment, since a
system Python may refuse the install and python3 -I does not see a user install.
Fixtures write objects with hash-object, mktree and commit-tree. Their own index
and checkout use read-tree; the source repository's index and history never move.
Every CLI invocation supplies --github-json, so missing fixture data cannot cause
a GitHub request.
"""

from __future__ import annotations

import copy
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

import yaml

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
# Main's own classifier, which a fixture's main is given when a light pre-flight is judged.
CLASSIFIER = (SCRIPTS / "risk.py").read_text(encoding="utf-8")


def harness_source(comment, extra=(), low=queue.safe_push.LOW_CLASSES):
    """A fixture harness: a comment, CHECKS and NEGATIVE lists naming the real checks (and
    any extra ones), and LOW_CLASSES, the classes for which its pre-flight leaves the full
    checks to CI (none, as before #329, when `low` is None), as check_queue reads them by
    ast."""
    checks = [name for name, _ in queue.safe_push.CHECKS] + list(extra)
    negative = [name for name, _ in queue.safe_push.NEGATIVE]
    return (f"# {comment}\n"
            + "CHECKS = [\n" + "".join(f"    ({n!r}, None),\n" for n in checks) + "]\n"
            + "NEGATIVE = [\n" + "".join(f"    ({n!r}, None),\n" for n in negative) + "]\n"
            + (f"LOW_CLASSES = {tuple(low)!r}\n" if low is not None else ""))


def fixture_environment() -> dict:
    """The environment of every fixture: no inherited Git, GitHub or acceptance settings,
    and a fixed identity and time. No variable named with a token either: --gaps runs no
    test beside one."""
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(("GIT_", "GH_", "GITHUB_", "STOICHEIA_REVERT_"))
           and key != "ACCEPTANCE_VERDICTS" and "TOKEN" not in key.upper()}
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
    return env


class QueueTests(unittest.TestCase):
    """Build two real trains and GitHub-style group merges for each test."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.enterContext(patch.dict(os.environ, fixture_environment(), clear=True))
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
            # No open main-red issue: main is green.
            "main_red": [[]],
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

    def light_block(self, head, cls, base=None):
        """A pre-flight against `base`, main by default, by its harness, that left the full
        checks to CI for the class `cls`, by safe_push's own writer, with the step 4 its
        short path writes."""
        base = base or self.base
        blob = self.git("rev-parse", f"{base}:scripts/safe_push.py").strip()
        return queue.safe_push.preflight_block(head, base, {
            "short": True, "class": cls, "class_why": "a fixture's class",
            "harness_sha": base, "time": "23 October 2026",
            "harness": f"origin/main's `scripts/safe_push.py` (blob `{blob[:12]}`)",
            "steps": [("2", "secrets", "ok", 1.0), ("3", "statements", "ok", 1.0),
                      ("4", "class", "ok", 0.5), ("4", "full local checks", "skip", None)],
        })

    def light_group(self, changes, cls, classifier=CLASSIFIER, labels=None, new="None."):
        """A group of one train, on a new main whose scripts/risk.py is `classifier` (None:
        main has none), whose pre-flight left the full checks to CI for the class `cls`."""
        self.base = self.make([self.base], {"scripts/risk.py": classifier})
        self.snapshot["main"]["sha"] = self.base
        self.nodes().clear()
        one = self.train(1, changes, new=new)
        self.set_body(queue.PREFLIGHT.sub(self.light_block(one, cls), self.body()))
        if labels is not None:
            self.snapshot["pull_requests"]["1"]["labels"] = [{"name": n} for n in labels]
        return self.merge(self.base, one, 1)

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
            "title": f"Fixture pull request #{number}",
            "head": {"sha": head, "ref": ref, "repo": {"full_name": "owner/repository"}},
            "base": {"ref": "main", "repo": {"full_name": "owner/repository"}},
            "body": body,
            "labels": [{"name": label} for label in (labels or ["tooling"])],
            "state": "open", "merged": False, "merge_commit_sha": None,
            "user": author or {"login": "fixture", "type": "User"},
        }
        nodes = self.nodes()
        for node in nodes:
            if node["pullRequest"]["number"] == number:
                node["pullRequest"].update(headRefOid=head, body=body)
                break
        else:
            nodes.append({"position": len(nodes) + 1,
                          "enqueuer": {"__typename": "User", "login": "fixture"},
                          "pullRequest": {"number": number, "headRefOid": head,
                                          "body": body, "editor": None,
                                          "timelineItems": {"nodes": []}}})

    def nodes(self):
        return self.snapshot["queue"]["data"]["repository"]["mergeQueue"]["entries"]["nodes"]

    def body(self, number=1):
        return self.snapshot["pull_requests"][str(number)]["body"]

    def set_body(self, body, number=1):
        """Edit a pull request's body, as both of GitHub's answers then give it: its REST
        answer and, while it is queued, the queue's GraphQL answer."""
        self.snapshot["pull_requests"][str(number)]["body"] = body
        for node in self.nodes():
            if node["pullRequest"]["number"] == number:
                node["pullRequest"]["body"] = body

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

    def test_safe_push_counts_current_exactly_the_blocks_the_judge_accepts(self):
        # The b7aac65f-like case, a head built on newer main than an old main commit,
        # with a member merged on its own first, so that the head's merge base with main
        # lies off main's chain. safe_push's queue mode compares against the newest commit
        # of main's chain that the head contains, not that merge base: the base of every
        # block the judge accepts. For each block, safe_push's block_current and the
        # judge's pre-flight agree, whatever base the merge compares against.
        old_base = self.base
        newer = self.make([old_base], {
            "scripts/safe_push.py": harness_source("A newer main harness.")})
        member = self.make([newer], {TEXT: "A member merged before its train.\n"})
        main = self.merge(newer, member, 5)
        head = self.merge(newer, self.make([member], {SECOND: "The train's own line.\n"}))
        ctx = queue.safe_push.Context(self.repo, head, main, 1, "", None, {},
                                      branch="docs/agreement", queue=True, harness_sha=main)
        self.assertEqual(self.git("merge-base", "--all", head, main).split(), [member])
        compared_base = queue.safe_push.queue_base(ctx, head)
        self.assertEqual(compared_base, newer)
        cases = {(newer, newer): True, (newer, main): True, (old_base, old_base): False,
                 (old_base, newer): False, (newer, old_base): False, (member, member): False,
                 (member, main): False, (main, main): False}
        for (base, harness), accepted in cases.items():
            block = self.block(head, base=base, harness_commit=harness)
            try:
                queue.preflight(self.repo, main, {"head": head, "body": block,
                                                  "ref": "docs/agreement"})
                judged = True
            except queue.Refused:
                judged = False
            self.assertEqual(judged, accepted, (base, harness))
            if accepted:
                self.assertEqual(base, compared_base, (base, harness))
            for compared in (compared_base, member, base):
                with self.subTest(base=base, harness=harness, compared=compared):
                    current = queue.safe_push.block_current(
                        ctx._replace(base=compared), queue.safe_push.BLOCK.search(block),
                        {"harness_sha": main})
                    self.assertEqual(current, accepted)

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
        two = self.train(2, {"README.md": readme.replace("Row.", "Row, regenerated.")})
        first = self.merge(self.base, one, 1)
        group = self.merge(first, two, 2)
        self.verdict(self.cli(head=group), 0, "queue: PASS")
        rewritten = readme.replace("Prose by hand.", "Prose, rewritten.")
        three = self.train(2, {"README.md": rewritten})
        self.verdict(self.cli(head=self.merge(first, three, 2,
                                              changes={"README.md": rewritten})),
                     1, "batching", "conflicts or extra content")

    def test_valid_later_train_restoring_readme_prose_is_caught(self):
        # Rule (a)'s check of README's hand-written part, by trains each valid on its own:
        # train 2 merges train 1's member, with its own row, and a reviewed member on it
        # that puts back the prose train 1 changed. Every merge is automatic, so only
        # the revert and reapplication of README's hand-written part refuses it.
        readme = "Prose by hand.\n<!-- scope:I -->\nRow.\n<!-- /scope:I -->\n"
        self.base = self.make([self.base], {"README.md": readme})
        self.snapshot["main"]["sha"] = self.base
        self.nodes().clear()
        one = self.train(1, {"README.md": readme.replace("Prose by hand.", "Prose, reviewed.")})
        member = queue.parents(self.repo, one)[1]
        restore = self.make([member], {"README.md": readme.replace("Row.", "Row, regenerated.")})
        head = self.merge(self.merge(self.base, member), restore)
        rows = "".join(f"| content/{name} | {sha} | {REVIEW} {sha[:12]}: pass. | "
                       f"{REVIEW} {sha[:12]}: pass. | passed at {sha} |\n"
                       for name, sha in (("1b", member), ("2", restore)))
        self.pr(2, head, "train/area-2", (
            "## Members\n\n| Branch | Head | /code-review | /security-review | "
            "/no-mistakes |\n|---|---|---|---|---|\n" + rows
            + "\n## What is new\n\nNone.\n\n" + self.block(head)))
        group = self.merge(self.merge(self.base, one, 1), head, 2)
        self.verdict(self.cli(head=group), 1,
                     "not overwriting: #1 changed lines were overwritten: README.md")

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

    def test_light_preflight_of_r0_to_r2_passes(self):
        # Since #329 a pre-flight of R0 to R2 leaves the full checks to CI (#334): the judge
        # accepts it while main's classifier, run now, still classes the train so.
        for cls, path in (("R0", "docs/notes.md"), ("R1", "docs/briefs/sample.md"),
                          ("R2", "Staging/Sample.lean")):
            with self.subTest(cls=cls):
                group = self.light_group({path: "A low change.\n"}, cls)
                self.verdict(self.cli(head=group), 0, "queue: PASS")

    def test_light_preflight_of_r3_or_above_refuses(self):
        for path, new in (("docs/WORKFLOW.md", "None."), (CHECK, f"- check: {CHECK}")):
            with self.subTest(path=path):
                group = self.light_group({path: "A change to the checks.\n"}, "R3", new=new)
                self.verdict(self.cli(head=group), 1, "pre-flight: left the full checks to "
                             "CI for the class R3, which only a change of R0 to R2 may")

    def test_light_preflight_claiming_a_class_its_paths_lack_refuses(self):
        # The block says R1, but main's classifier gives the paths a higher class.
        for path, cls, new in (
                ("docs/WORKFLOW.md", "R3", "None."), (CHECK, "R3", f"- check: {CHECK}"),
                ("Elements/Foundations/Sample.lean", "R4",
                 "- foundations: Elements/Foundations/Sample.lean"),
                # The train's own copy of the classifier, which would class it R0, judges
                # nothing.
                ("scripts/risk.py", "R5", "- check: scripts/risk.py")):
            with self.subTest(path=path):
                group = self.light_group({path: "print('R0 Docs')\n"}, "R1", new=new)
                self.verdict(self.cli(head=group), 1, "pre-flight: left the full checks to "
                             f"CI, but the class by main's scripts/risk.py is {cls} (")

    def test_light_preflight_of_a_release_refuses(self):
        group = self.light_group({"docs/notes.md": "A release's note.\n"}, "R0",
                                 labels=["docs", "release"])
        self.verdict(self.cli(head=group), 1, "scripts/risk.py is R5 (the pull request is "
                     "labelled release)")

    def test_light_preflight_without_main_s_classifier_refuses(self):
        # No classifier at main, or one that fails, classes every change R5: fail closed.
        for classifier, why in ((None, "has no scripts/risk.py to class it"),
                                ("raise SystemExit(3)\n", "could not class it (exit 3)"),
                                ("print('no class')\n", "printed no class")):
            with self.subTest(why=why):
                group = self.light_group({"docs/notes.md": "A note.\n"}, "R0",
                                         classifier=classifier)
                self.verdict(self.cli(head=group), 1, "scripts/risk.py is R5 (", why)

    def test_light_preflight_of_a_check_input_refuses_whatever_main_s_class(self):
        # Should main's classifier ever class a check input low, the judge refuses still,
        # as safe_push's short path then runs the full checks (beyond_low).
        group = self.light_group({CHECK: "print('a lowered check')\n"}, "R0",
                                 classifier="print('R0 Docs')\n", new=f"- check: {CHECK}")
        self.verdict(self.cli(head=group), 1, "pre-flight: left the full checks to CI, but "
                     f"the change touches {CHECK}, which no change of R0 to R2 may")

    def test_light_preflight_must_be_as_safe_push_writes_it(self):
        group = self.light_group({"docs/notes.md": "A note.\n"}, "R1")
        self.verdict(self.cli(head=group), 0, "queue: PASS")
        original = self.body()
        skipped = "| 4. full local checks | skip |  |"
        step = "its step 4 is not the class, passed, and the full local checks, skipped"
        disagree = "the record's class R1 and its Risk class line disagree"
        end = "<!-- safe_push:preflight end -->"
        for body, message in (
            (original.replace(skipped + "\n", ""), step),
            (original.replace("| 4. class | ok |", "| 4. class | skip |"), step),
            (original.replace(skipped, skipped + "\n| 4. lake build | ok | 1.0 |"), step),
            (original.replace("| 2. secrets | ok |", "| 2. secrets | FAIL |"),
             "contains a FAIL row"),
            (original.replace("Verdict: PASS.", "Verdict: FAIL."), "one passing verdict"),
            (original.replace("Risk class R1:", "Risk class R2:"), disagree),
            (original.replace("Risk class R1: a fixture's class.\n", ""), disagree),
            (original.replace(end, "Risk class R1: said twice.\n" + end), disagree),
            (original.replace(end, "Risk Class R5: said again, in other capitals.\n" + end),
             disagree),
            (original.replace(end, "Noted: the full checks skipped.\n" + end),
             "full checks skipped"),
        ):
            with self.subTest(message=message, body=body[-200:]):
                self.set_body(body)
                self.verdict(self.cli(head=group), 1, message)

    def test_light_preflight_of_a_harness_that_writes_none_refuses(self):
        # A light block is held to the harness it names, as a full one is to its checks:
        # that harness must leave the full checks to CI for the block's class, by its
        # LOW_CLASSES, so a block typed by hand naming a harness from before #329 refuses.
        for source, message in (
                (harness_source("A harness from before #329.", low=None),
                 "the recorded harness has no LOW_CLASSES, so never does"),
                (harness_source("A harness whose short path is R0's alone.", low=("R0",)),
                 "for the class R1, which the recorded harness never does (its LOW_CLASSES "
                 "are R0)"),
                (harness_source("A harness that names them twice.")
                 + "LOW_CLASSES = ('R0', 'R1', 'R2', 'R3')\n",
                 "the recorded harness's LOW_CLASSES could not be read")):
            with self.subTest(message=message):
                self.base = self.make([self.base], {"scripts/safe_push.py": source})
                group = self.light_group({"docs/notes.md": "A note.\n"}, "R1")
                self.verdict(self.cli(head=group), 1, message)

    def dated(self, when, parents, changes):
        """A commit made at the time `when`: which of several merge bases `git diff A...B`
        takes turns on their commit dates."""
        with patch.dict(os.environ, GIT_AUTHOR_DATE=when, GIT_COMMITTER_DATE=when):
            return self.make(parents, changes)

    def test_light_preflight_classes_the_change_from_its_base_not_the_group_s(self):
        # Main runs c0, c1 (an R4 change), then c2, where a branch P, forked at c0 and
        # committed later, lands. The train merged P before it landed, sits on c1, and sets
        # c1's change back. The group base's three-dot diff takes P, the newer of the two
        # merge bases, and sees a note alone; the block's own diff, from c1, sees the R4.
        foundations = "Elements/Foundations/Sample.lean"
        c0 = self.make([self.base], {"scripts/risk.py": CLASSIFIER, foundations: "old\n"})
        p = self.dated("2026-10-21T12:00:00+00:00", [c0], {"docs/p.md": "P's change.\n"})
        c1 = self.dated("2026-10-20T12:00:00+00:00", [c0], {foundations: "new\n"})
        c2 = self.merge(c1, p, 9)
        head = self.make([self.merge(c1, p)], {foundations: "old\n",
                                               "docs/notes.md": "A note.\n"})
        self.assertEqual(queue.safe_push.risk_class(self.repo, c2, head, set()).cls, "R0")
        self.base = c2
        self.snapshot["main"]["sha"] = c2
        self.nodes().clear()
        self.pr(1, head, "content/sample", self.light_block(head, "R0", base=c1))
        self.verdict(self.cli(head=self.merge(c2, head, 1)), 1, "pre-flight: left the full "
                     "checks to CI, but the class by main's scripts/risk.py is R4 (",
                     "), of the change")

    def test_light_preflight_classes_what_the_merge_brings_into_the_group(self):
        # The block's base, c1, is no merge base of the head with main: the head holds Q,
        # an R4 change that landed on c1 as c2, and P, which landed on c2 as c3, and sets
        # Q's change back. The change from the group base and the change from the block's
        # base are both R0; what the entry's merge brings into the group is R4.
        foundations = "Elements/Foundations/Sample.lean"
        c0 = self.make([self.base], {"scripts/risk.py": CLASSIFIER, foundations: "old\n"})
        p = self.dated("2026-10-22T12:00:00+00:00", [c0], {"docs/p.md": "P's change.\n"})
        c1 = self.dated("2026-10-20T12:00:00+00:00", [c0], {"docs/c1.md": "c1.\n"})
        q = self.dated("2026-10-20T13:00:00+00:00", [c1], {foundations: "new\n"})
        c3 = self.merge(self.merge(c1, q, 8), p, 9)
        held = self.merge(self.merge(c1, p), q)
        head = self.make([held], {foundations: "old\n", "docs/notes.md": "A note.\n"})
        for start in (c3, c1):
            self.assertEqual(queue.safe_push.risk_class(self.repo, start, head, set()).cls,
                             "R0")
        self.base = c3
        self.snapshot["main"]["sha"] = c3
        self.nodes().clear()
        self.pr(1, head, "content/sample", self.light_block(head, "R0", base=c1))
        self.verdict(self.cli(head=self.merge(c3, head, 1)), 1, "pre-flight: left the full "
                     "checks to CI, but the class by main's scripts/risk.py is R4 (",
                     "), of what its merge brings into the group")

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

    def rename(self, typename):
        """The entry's last title rename, by an actor of this type, as its timeline gives
        it."""
        self.nodes()[0]["pullRequest"]["timelineItems"]["nodes"] = [
            {"actor": {"__typename": typename, "login": "renamer"}}]

    def test_no_bot_may_rename_an_ordinary_entry(self):
        # The title goes into main's merge commit, so a bot's rename is the bot's words.
        self.rename("Bot")
        self.verdict(self.cli(), 1, "#1: a bot last renamed a pull request")
        self.rename("User")
        self.verdict(self.cli(), 0, "queue: PASS")

    def test_unreadable_rename_refuses(self):
        timeline = self.nodes()[0]["pullRequest"]["timelineItems"]
        for nodes in (None, [{"actor": None}], [{}], [{"actor": {"login": "renamer"}}],
                      [{"actor": {"__typename": "User", "login": "a"}}] * 2):
            with self.subTest(nodes=nodes):
                timeline["nodes"] = nodes
                self.verdict(self.cli(), 2, "who queued, edited and renamed each entry")
        del self.nodes()[0]["pullRequest"]["timelineItems"]
        self.verdict(self.cli(), 2, "who queued, edited and renamed each entry")

    def test_the_queue_read_asks_for_each_entry_s_last_rename(self):
        with patch.dict(os.environ, {"GH_TOKEN": "fixture-token"}), \
                patch.object(queue.subprocess, "run", return_value=subprocess.CompletedProcess(
                    [], 0, "{}", "")) as call:
            queue.GitHub("owner/repository", None).read("queue")
        query = next(arg for arg in call.call_args.args[0] if arg.startswith("query="))
        self.assertIn("timelineItems(itemTypes:[RENAMED_TITLE_EVENT],last:1)", query)
        self.assertIn("...on RenamedTitleEvent{actor{__typename login}}", query)

    def test_the_queue_read_asks_for_each_entry_s_body(self):
        # A field of the pull request itself, in the same answer as its head and editor.
        with patch.dict(os.environ, {"GH_TOKEN": "fixture-token"}), \
                patch.object(queue.subprocess, "run", return_value=subprocess.CompletedProcess(
                    [], 0, "{}", "")) as call:
            queue.GitHub("owner/repository", None).read("queue")
        query = next(arg for arg in call.call_args.args[0] if arg.startswith("query="))
        self.assertRegex(query, r"pullRequest\{[^{}]*\bheadRefOid\b[^{}]*\bbody\b")

    def test_a_body_edited_after_the_queue_read_is_unreadable(self):
        # The queue's GraphQL answer names each entry's last editor, a person here. A bot's
        # edit after it, which the later REST read sees, would be judged as that person's:
        # here it adds the line that lets the entries land as a red main's fix; or, main
        # green, it adds only a line break. The body judged must be the one the queue read
        # gave, character for character, or none.
        bodies = {number: self.body(number) for number in (1, 2)}
        for node in self.nodes():
            node["pullRequest"]["editor"] = {"__typename": "User", "login": "someone"}
        for red, edit in ((self.RED, "Fixes main-red: #9\n\n{}"), ([[]], "{}\n")):
            with self.subTest(edit=edit):
                self.snapshot["main_red"] = red
                for number, body in bodies.items():
                    self.set_body(body, number)
                    self.snapshot["pull_requests"][str(number)]["body"] = edit.format(body)
                self.verdict(self.cli(), 2, "#1's body differs between the queue's answer "
                             "and its pull request's")
        # The same edit, given by both reads, is judged as ever: a person's passes.
        self.snapshot["main_red"] = self.RED
        for number, body in bodies.items():
            self.set_body("Fixes main-red: #9\n\n" + body, number)
        self.verdict(self.cli(), 0, "queue: PASS")

    def test_any_queued_entry_s_body_edited_after_the_queue_read_is_unreadable(self):
        # The second entry's body alone, edited after the queue read: every open entry's
        # body is compared, not only the first's.
        self.snapshot["pull_requests"]["2"]["body"] = self.body(2) + "\n"
        self.verdict(self.cli(), 2, "#2's body differs between the queue's answer and its "
                     "pull request's")

    def test_an_unreadable_queued_body_is_unreadable(self):
        node = self.nodes()[0]["pullRequest"]
        for body in (None, 3, ["a body"]):
            with self.subTest(body=body):
                node["body"] = body
                self.verdict(self.cli(), 2, "could not read each queued entry's body")
        del node["body"]
        self.verdict(self.cli(), 2, "could not read each queued entry's body")

    RED = [[{"number": 9, "state": "open", "labels": [{"name": "main-red"}],
             "body": "Main's integration checks failed.\n"}]]

    def test_red_main_holds_every_entry_but_its_declared_fix(self):
        # A train queued before main went red, or queued without --merge, waits as --merge
        # does: only a pull request that declares it fixes every open main-red issue lands.
        self.snapshot["main_red"] = self.RED
        self.verdict(self.cli(), 1, "#1: main is red (open main-red issues #9)")
        for number in (1, 2):
            self.set_body("Fixes main-red: #9\n\n" + self.body(number), number)
        self.verdict(self.cli(), 0, "queue: PASS")
        for line, message in (("Fixes main-red: #9, #10", "naming every open main-red issue"),
                              ("Fixes main-red: 9", "unreadable main-red fix")):
            with self.subTest(line=line):
                self.set_body(self.body().replace("Fixes main-red: #9", line))
                self.verdict(self.cli(), 1, "#1: ", message)
                self.set_body(self.body().replace(line, "Fixes main-red: #9"))

    def test_red_main_judges_no_merged_entry(self):
        # An entry already merged is on main; the pause is for those still queued.
        pr = self.snapshot["pull_requests"]["1"]
        pr.update(state="closed", merged=True, merge_commit_sha=self.first)
        self.snapshot["main"]["sha"] = self.first
        self.nodes().pop(0)
        self.nodes()[0]["position"] = 1
        self.snapshot["main_red"] = self.RED
        self.verdict(self.cli(), 1, "#2: main is red")
        self.set_body("Fixes main-red: #9\n\n" + self.body(2), 2)
        self.verdict(self.cli(), 0, "queue: PASS")

    def test_unreadable_main_red_issues_refuse_an_ordinary_entry(self):
        for pages in ([[{"state": "open", "labels": [{"name": "main-red"}], "body": ""}]],
                      [{}], None):
            with self.subTest(pages=pages):
                self.snapshot["main_red"] = pages
                self.verdict(self.cli(), 2, "could not read the open main-red issues")
        del self.snapshot["main_red"]
        self.verdict(self.cli(), 2, "fixture lacks main_red")

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
                # Judging a group runs none of the group's scripts, so the judge does not
                # render: the check job does, on the same group; --tree --render is the
                # same reading.
                self.verdict(self.cli(head=group), 0, "queue: PASS")
                self.checkout(group)
                self.verdict(self.cli("--render", tree=True, prepare=False), 1,
                             "render freshness: generated files changed")

    def revert_group(self, extra=False, merges=1):
        old_base, original = self.base, self.trees[self.base]
        self.base = self.first if merges == 1 else self.head
        self.snapshot["main"]["sha"] = self.base
        reverted = [self.first] if merges == 1 else [self.head, self.first]
        # One commit for each merge, its revert, newest first, as auto_revert makes them.
        head = self.base
        if merges == 2:
            head = self.make([head], {SECOND: original[SECOND]})
        changes = {TEXT: original[TEXT]}
        if extra:
            changes["notes/unrelated.txt"] = "An extra change.\n"
        head = self.make([head], changes)
        self.nodes().clear()
        self.pr(3, head, f"revert/{self.base[:12]}",
                "Failed run: 71\n" + "\n".join(f"Reverts: {sha}" for sha in reverted) + "\n",
                ["auto-revert"], {"login": BOT, "type": "Bot"})
        self.failed_run(old_base, self.base)
        return self.merge(self.base, head, 3), old_base

    def failed_run(self, before, after):
        """Run 71, a failed post-merge run of the push before..after, as GitHub records it:
        the run, the push, an open main-red issue naming the run, and each pull request
        that a merge of the push's first-parent chain names, merged as that merge."""
        for line in self.git("log", "--first-parent", "--format=%H %s",
                             f"{before}..{after}").splitlines():
            sha, subject = line.split(" ", 1)
            match = queue.SUBJECT.fullmatch(subject)
            if match and match.group(1) in self.snapshot["pull_requests"]:
                self.snapshot["pull_requests"][match.group(1)].update(
                    state="closed", merged=True, merge_commit_sha=sha)
        self.snapshot["runs"] = {"71": {
            "id": 71, "path": ".github/workflows/post-merge.yml", "event": "push",
            "head_branch": "main", "status": "completed", "conclusion": "failure",
            "head_sha": after,
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
        run = "https://github.com/owner/repository/actions/runs/71"
        for body in ("Run: https://github.com/o/r/actions/runs/710\n",
                     # Another repository's run of the same number names nothing.
                     "Run: https://github.com/other/repository/actions/runs/71\n",
                     # Nor does this repository's address off the issue's own Run: line.
                     f"Failed jobs:\n{run}\n", f"Runs: {run}\n", f"Run: {run}0\n",
                     f"Run: {run}\nRun: {run}\n", f"> Run: {run}\n"):
            with self.subTest(body=body):
                self.snapshot["main_red"] = [[{"number": 9, "state": "open",
                                               "labels": [{"name": "main-red"}],
                                               "body": body}]]
                self.verdict(self.cli(head=head), 1, "no open main-red issue names")
        self.snapshot["main_red"] = [[]]
        self.verdict(self.cli(head=head), 1, "no open main-red issue names")
        for body in (f"Run: {run}/attempts/2\n", f"Before: x\nRun: {run}\r\n\nOutcome.\n"):
            with self.subTest(body=body):
                self.snapshot["main_red"] = [[{"number": 9, "state": "open",
                                               "labels": [{"name": "main-red"}],
                                               "body": body}]]
                self.verdict(self.cli(head=head), 0, "queue: PASS")

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

    def queued_revert(self, after, before, head, reverts):
        """Queue `head` as the bot's revert of the merges `reverts`, of the failed push
        before..after, alone; the group on main's tip."""
        self.nodes().clear()
        self.pr(3, head, f"revert/{after[:12]}",
                "Failed run: 71\n" + "".join(f"Reverts: {sha}\n" for sha in reverts),
                ["auto-revert"], {"login": BOT, "type": "Bot"})
        self.failed_run(before, after)
        return self.merge(self.base, head, 3)

    def test_auto_revert_built_on_a_later_main_refuses(self):
        # The failed push is the first train's merge; main has moved on to the second's.
        # A revert of the first built there would keep the decisions record as at that
        # later main, not as at the failed push.
        old_base, original = self.base, self.trees[self.base]
        self.base = self.head
        self.snapshot["main"]["sha"] = self.head
        head = self.make([self.head], {TEXT: original[TEXT]})
        group = self.queued_revert(self.first, old_base, head, [self.first])
        self.verdict(self.cli(head=group), 1,
                     "the revert's base must be the failed push's tip")

    def test_auto_revert_holds_only_its_reverts_and_one_keep_commit(self):
        # The exact tree is not enough: the branch's commits are the reverts, one for each
        # merge, then at most the one commit that keeps the decisions record.
        _, old_base = self.revert_group(merges=2)
        original = self.trees[old_base]
        base, snapshot = self.base, copy.deepcopy(self.snapshot)
        exact = self.snapshot["pull_requests"]["3"]["head"]["sha"]
        injected = "notes/injected.txt"
        through = self.make([self.make([self.head], {SECOND: original[SECOND],
                                                     injected: "Injected.\n"})],
                            {injected: None})
        side = self.make([self.head], {})
        cases = {
            "an injected file, taken out again": self.make([through], {TEXT: original[TEXT]}),
            "both reverts in one commit": self.make([self.head], {
                TEXT: original[TEXT], SECOND: original[SECOND]}),
            "a commit of no change after them": self.make([exact], {}),
            "a merge on the branch": self.make([exact, side],
                                               tree=self.git("rev-parse",
                                                             f"{exact}^{{tree}}").strip()),
            "the reverts in the other order": self.make([self.make([self.head], {
                TEXT: original[TEXT]})], {SECOND: original[SECOND]}),
        }
        for case, head in cases.items():
            with self.subTest(case=case):
                self.base, self.snapshot = base, copy.deepcopy(snapshot)
                group = self.queued_revert(self.head, old_base, head, [self.head, self.first])
                self.verdict(self.cli(head=group), 1, "auto-revert: the branch must hold")

    def test_auto_revert_of_a_push_holding_a_one_parent_commit_refuses(self):
        # auto_revert reverts none of such a push; nor does the queue admit a revert of
        # its merges alone.
        old_base, original = self.base, self.trees[self.base]
        direct = self.make([self.base], {SECOND: "A direct commit to main.\n"})
        one = self.train(1, {TEXT: "The first train's reviewed line.\n"}, start=direct)
        self.base = self.merge(direct, one, 1)
        self.snapshot["main"]["sha"] = self.base
        head = self.make([self.base], {TEXT: original[TEXT]})
        group = self.queued_revert(self.base, old_base, head, [self.base])
        self.verdict(self.cli(head=group), 1,
                     "the failed push holds a commit that is not a two-parent merge")

    def refused_before_any_revert(self, group, message, code=1):
        """The queue refuses the revert group `group`, with exit `code`, naming `message`;
        and exact_revert does so before it computes any revert (revert_checkout)."""
        self.verdict(self.cli(head=group), code, message)
        pr = dict(queue.pull_request(self.snapshot["pull_requests"]["3"], 3), main=self.base)
        api = queue.GitHub("owner/repository", self.fixture)
        with patch.object(queue, "revert_checkout",
                          side_effect=AssertionError("a revert was computed")), \
                self.assertRaisesRegex(queue.Refused if code == 1 else ValueError, message):
            queue.exact_revert(self.repo, pr, api)

    def test_auto_revert_of_a_merge_that_names_no_pull_request_refuses(self):
        # auto_revert reverts only a push of pull request merges, each named by its
        # subject exactly as it reads it; nor does the queue admit the revert of another
        # two-parent merge.
        old_base, original = self.base, self.trees[self.base]
        snapshot = copy.deepcopy(self.snapshot)
        for subject in ("Merge reviewed member", "Merge branch 'train/area-1'",
                        "Merge pull request #1", "Merge pull request #01 from owner/train-1"):
            with self.subTest(subject=subject):
                self.snapshot = copy.deepcopy(snapshot)
                self.base = self.merge(old_base, self.one, subject=subject)
                self.snapshot["main"]["sha"] = self.base
                head = self.make([self.base], {TEXT: original[TEXT]})
                group = self.queued_revert(self.base, old_base, head, [self.base])
                self.refused_before_any_revert(group, "names no pull request in its subject")

    def test_auto_revert_reads_a_merge_s_subject_as_auto_revert_reads_it(self):
        # Git's %s keeps a subject's leading space and drops a trailing one: auto_revert,
        # which takes off only the line end, finds no pull request in the first and #1
        # in the second, and so does the queue.
        import auto_revert
        old_base, original = self.base, self.trees[self.base]
        snapshot = copy.deepcopy(self.snapshot)
        for subject, number in ((" Merge pull request #1 from owner/train-1", None),
                                ("\tMerge pull request #1 from owner/train-1", None),
                                ("Merge pull request #1 from owner/train-1 ", 1),
                                ("Merge pull request #1 from owner/train-1\t", 1)):
            with self.subTest(subject=subject):
                self.snapshot = copy.deepcopy(snapshot)
                self.base = self.merge(old_base, self.one, subject=subject)
                self.snapshot["main"]["sha"] = self.base
                head = self.make([self.base], {TEXT: original[TEXT]})
                group = self.queued_revert(self.base, old_base, head, [self.base])
                if number is None:
                    with self.assertRaisesRegex(auto_revert.Refusal,
                                                "does not identify a pull request"):
                        auto_revert.trains(self.repo, old_base, self.base)
                    self.refused_before_any_revert(group, "names no pull request in its "
                                                   "subject")
                else:
                    self.assertEqual([train.number for train in auto_revert.trains(
                        self.repo, old_base, self.base)], [number])
                    self.verdict(self.cli(head=group), 0, "queue: PASS")

    def test_auto_revert_of_a_push_repeating_a_pull_request_refuses(self):
        # Both merges of the push name #1: auto_revert reverts neither.
        old_base, original = self.base, self.trees[self.base]
        self.base = self.merge(self.first, self.two, 1)
        self.snapshot["main"]["sha"] = self.base
        head = self.make([self.make([self.base], {SECOND: original[SECOND]})],
                         {TEXT: original[TEXT]})
        group = self.queued_revert(self.base, old_base, head, [self.base, self.first])
        self.refused_before_any_revert(group, "the failed push repeats pull request #1")

    def pull_request_refuses(self, *cases, code=1):
        """Each (change, message) case, a change to #1 as GitHub's REST answer gives it,
        the pull request of the failed push's one merge, refuses the exact revert of that
        merge before any revert is computed; #1 as it was passes. The group is returned."""
        group, _ = self.revert_group()
        original = copy.deepcopy(self.snapshot["pull_requests"]["1"])
        for change, message in cases:
            with self.subTest(change=change):
                self.snapshot["pull_requests"]["1"] = {**original, **change}
                self.refused_before_any_revert(group, message, code)
        self.snapshot["pull_requests"]["1"] = original
        self.verdict(self.cli(head=group), 0, "queue: PASS")
        return group

    def test_auto_revert_of_a_merge_its_pull_request_does_not_record_refuses(self):
        # #1 names another merge commit, or is not merged at all.
        message = "#1 does not confirm the failed push's merge"
        self.pull_request_refuses(({"merge_commit_sha": self.head}, message),
                                  ({"state": "open", "merged": False}, message))

    def test_auto_revert_of_a_merge_from_another_head_refuses(self):
        self.pull_request_refuses(
            ({"head": {"sha": self.two, "ref": "train/area-1",
                       "repo": {"full_name": "owner/repository"}}},
             "#1 does not confirm the failed push's merge"))

    def test_auto_revert_of_a_merge_into_another_branch_refuses(self):
        self.pull_request_refuses(
            ({"base": {"ref": "develop", "repo": {"full_name": "owner/repository"}}},
             "#1 was not merged into main of owner/repository"))

    def test_auto_revert_of_a_merge_into_another_repository_refuses(self):
        self.pull_request_refuses(
            ({"base": {"ref": "main", "repo": {"full_name": "fork/repository"}}},
             "#1 was not merged into main of owner/repository"))

    def test_auto_revert_of_a_merge_into_another_repository_of_the_owner_refuses(self):
        # The whole name of the base repository is compared, not its owner alone.
        self.pull_request_refuses(
            ({"base": {"ref": "main", "repo": {"full_name": "owner/other"}}},
             "#1 was not merged into main of owner/repository"))

    def test_auto_revert_of_a_pull_request_with_a_blank_title_refuses(self):
        self.pull_request_refuses(({"title": ""}, "#1 has a blank title"),
                                  ({"title": " \t\n"}, "#1 has a blank title"))

    def test_auto_revert_of_a_pull_request_without_a_kind_label_refuses(self):
        message = "#1 has no kind label, one of tooling, text, lean, docs"
        self.pull_request_refuses(
            ({"labels": []}, message),
            ({"labels": [{"name": "auto-revert"}, {"name": "security-review"}]}, message))

    def test_auto_revert_of_a_merge_whose_pull_request_is_unreadable(self):
        message = "could not read pull request #1"
        group = self.pull_request_refuses(
            *(({key: value}, message) for key, value in (
                ("number", 2), ("merged", "true"), ("merge_commit_sha", "invalid"),
                ("head", {"ref": "train/area-1"}), ("base", None),
                ("base", {"ref": "main", "repo": None}), ("base", {"ref": 7}),
                ("title", None), ("labels", None), ("labels", ["tooling"]),
                ("labels", [{"name": ""}]))), code=2)
        for key in ("title", "base", "labels"):
            with self.subTest(missing=key):
                original = self.snapshot["pull_requests"]["1"].pop(key)
                self.refused_before_any_revert(group, message, code=2)
                self.snapshot["pull_requests"]["1"][key] = original
        del self.snapshot["pull_requests"]["1"]
        self.refused_before_any_revert(group, "fixture lacks pull_requests", code=2)

    def test_auto_revert_reads_merge_attributes_from_before(self):
        # As the revert job reads them: from the main whose own run passed, never from the
        # tree being reverted.
        _, old_base = self.revert_group(merges=2)
        self.fixture.write_text(json.dumps(self.snapshot), encoding="utf-8")
        pr = dict(queue.pull_request(self.snapshot["pull_requests"]["3"], 3), main=self.base)
        api = queue.GitHub("owner/repository", self.fixture)
        calls, run = [], queue.safe_push.run

        def recording(args, *rest, **kwargs):
            calls.append(list(args))
            return run(args, *rest, **kwargs)

        with patch.object(queue.safe_push, "run", side_effect=recording):
            queue.exact_revert(self.repo, pr, api)
        reverts = [call for call in calls if "revert" in call]
        self.assertEqual(len(reverts), 2, calls)
        for call in reverts:
            self.assertEqual(call[call.index("revert") - 1], f"--attr-source={old_base}")

    def waited_push(self, *states):
        """failed_push on run 71 as GitHub reports it at each read in turn, the last state
        repeating, with a clock that only sleeping moves on: the push it finds, how many
        times it read the run, and each sleep."""
        self.failed_run(self.base, self.first)
        reads, slept, now = [], [], [0.0]
        snapshot = self.snapshot

        class Reads:
            def read(self, kind, number=None):
                if kind != "runs":
                    return copy.deepcopy(snapshot[kind])
                reads.append(number)
                state = states[min(len(reads), len(states)) - 1]
                return dict(snapshot["runs"][str(number)], **state)

        def sleep(seconds):
            slept.append(seconds)
            now[0] += seconds

        try:
            return queue.failed_push(Reads(), 71, sleep=sleep, clock=lambda: now[0]), \
                len(reads), slept
        except (queue.Refused, ValueError) as error:
            return error, len(reads), slept

    RUNNING = {"status": "in_progress", "conclusion": None}

    def test_auto_revert_waits_for_its_run_to_complete_as_a_failure(self):
        # The revert job is one of the failed run's own jobs, so the run can still be in
        # progress when the revert is judged: it is read every 15 seconds until it ends.
        found, reads, slept = self.waited_push(
            self.RUNNING, {"status": "queued", "conclusion": None},
            {"status": "completed", "conclusion": "failure"})
        self.assertEqual(found, (self.base, self.first))
        self.assertEqual((reads, slept), (3, [15, 15]))

    def test_auto_revert_whose_run_completes_as_a_success_refuses(self):
        found, reads, slept = self.waited_push(
            self.RUNNING, {"status": "completed", "conclusion": "success"})
        self.assertIsInstance(found, queue.Refused)
        self.assertIn("run must be a failed post-merge push on main", str(found))
        self.assertEqual((reads, slept), (2, [15]))

    def test_auto_revert_whose_run_never_completes_refuses_after_ten_minutes(self):
        found, reads, slept = self.waited_push(self.RUNNING)
        self.assertIsInstance(found, queue.Refused)
        self.assertIn("the failed run had not completed after 10 minutes", str(found))
        self.assertEqual((reads, slept), (41, [15] * 40))

    def test_auto_revert_run_without_a_readable_status_is_unreadable(self):
        for state in ({"status": None}, {"status": 3}):
            with self.subTest(state=state):
                found, reads, slept = self.waited_push(state)
                self.assertIsInstance(found, ValueError)
                self.assertIn("could not read the failed run", str(found))
                self.assertEqual((reads, slept), (1, []))
        del self.snapshot["runs"]["71"]["status"]
        self.fixture.write_text(json.dumps(self.snapshot), encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "could not read the failed run"):
            queue.failed_push(queue.GitHub("owner/repository", self.fixture), 71)

    ENTRY = "docs/decisions/2026-10-21-a-train.md"
    DECISION = "- **A train's decision.** Kept as history.\n"

    def entries_revert_group(self, revert=None, train=None, page=None):
        """Main with decision entries, each a file of its own (and, if given, `page` as
        its decisions page); a train adding one, with a reviewed line; that train's merge
        pushed and failed; and the bot's revert of it, which restores the reviewed line
        and keeps the folder and the page, unless `revert` says otherwise."""
        changes = {"docs/decisions/README.md": "One file a decision.\n"}
        if page is not None:
            changes[PAGE] = page
        self.base = self.make([self.base], changes)
        original = self.trees[self.base]
        trained = {TEXT: "The first train's reviewed line.\n", self.ENTRY: self.DECISION,
                   **(train or {})}
        one = self.train(1, trained)
        old_base, self.base = self.base, self.merge(self.base, one, 1)
        self.snapshot["main"]["sha"] = self.base
        # The revert, as git makes it, then the commit that keeps the record as at the
        # failed push (with any change `revert` asks for).
        reverted = self.make([self.base], {path: original.get(path) for path in trained})
        kept = {path: text for path, text in self.trees[self.base].items()
                if path == PAGE or path.startswith(queue.ENTRIES + "/")}
        head = self.make([reverted], {**kept, **(revert or {})})
        self.nodes().clear()
        self.pr(3, head, f"revert/{self.base[:12]}",
                f"Failed run: 71\nReverts: {self.base}\n", ["auto-revert"],
                {"login": BOT, "type": "Bot"})
        self.failed_run(old_base, self.base)
        return self.merge(self.base, head, 3)

    def test_auto_revert_keeps_decision_entries(self):
        # The record is history: the revert keeps docs/decisions/ and the decisions page
        # as at the failed push; the rest is reverted.
        head = self.entries_revert_group()
        self.verdict(self.cli(head=head), 0, "queue: PASS")

    def test_auto_revert_keeps_an_edited_decision_entry(self):
        # A train that edits an entry already on main: the revert keeps the edit, and the
        # plain git revert, which undoes it, refuses.
        edited = {"docs/decisions/README.md": "One file a decision, kept.\n"}
        base, snapshot = self.base, copy.deepcopy(self.snapshot)
        head = self.entries_revert_group(train=edited)
        self.verdict(self.cli(head=head), 0, "queue: PASS")
        self.base, self.snapshot = base, snapshot
        head = self.entries_revert_group(
            train=edited, revert={"docs/decisions/README.md": "One file a decision.\n"})
        self.verdict(self.cli(head=head), 1, "not the exact revert tree (extra change)")

    def test_auto_revert_that_takes_a_decision_entry_away_refuses(self):
        # The plain git revert, which deletes the entry.
        head = self.entries_revert_group(revert={self.ENTRY: None})
        self.verdict(self.cli(head=head), 1, "not the exact revert tree (extra change)")

    def test_auto_revert_may_change_nothing_else_under_decision_entries(self):
        base, snapshot = self.base, copy.deepcopy(self.snapshot)
        for change in ({self.ENTRY: "- **A train's decision.** Edited by the revert.\n"},
                       {"docs/decisions/2026-10-21-another.md": "- **Another.**\n"},
                       {"docs/decisions/README.md": None}):
            with self.subTest(change=change):
                self.base, self.snapshot = base, copy.deepcopy(snapshot)
                head = self.entries_revert_group(revert=change)
                self.verdict(self.cli(head=head), 1,
                             "not the exact revert tree (extra change)")

    ADDED = "\nA page decision the train added.\n"

    def test_auto_revert_keeps_the_decisions_page_with_the_entries(self):
        # The page is the record too, only ever added to: the revert keeps both it and the
        # train's entry as at the failed push.
        original = self.trees[self.base][PAGE]
        head = self.entries_revert_group(train={PAGE: original + self.ADDED})
        self.assertEqual(self.trees[head][PAGE], original + self.ADDED)
        self.verdict(self.cli(head=head), 0, "queue: PASS")

    def test_auto_revert_that_reverts_the_page_s_added_lines_refuses(self):
        # The plain git revert, which takes the train's lines off the page again.
        original = self.trees[self.base][PAGE]
        head = self.entries_revert_group(train={PAGE: original + self.ADDED},
                                         revert={PAGE: original})
        self.verdict(self.cli(head=head), 1, "not the exact revert tree (extra change)")

    def test_auto_revert_may_change_nothing_else_on_the_decisions_page(self):
        original = self.trees[self.base][PAGE]
        kept = original + self.ADDED
        base, snapshot = self.base, copy.deepcopy(self.snapshot)
        for page in (kept + "\nA line the revert added.\n",
                     kept.replace("A previous decision.", "A previous decision, edited."),
                     kept.replace("A previous decision.\n", ""),
                     original + "\nA page decision the train added, edited.\n",
                     None):
            with self.subTest(page=page):
                self.base, self.snapshot = base, copy.deepcopy(snapshot)
                head = self.entries_revert_group(train={PAGE: kept}, revert={PAGE: page})
                self.verdict(self.cli(head=head), 1,
                             "not the exact revert tree (extra change)")

    def test_auto_revert_keeps_the_whole_page_whatever_comments_it_holds(self):
        # The whole page is kept, so comments of the shape an earlier design gave a region
        # of it, paired or not, change nothing: the kept page passes, and a revert of the
        # lines between them refuses.
        begin, end = "<!-- decisions:entries begin -->", "<!-- decisions:entries end -->"
        original = self.trees[self.base][PAGE]
        base, snapshot = self.base, copy.deepcopy(self.snapshot)
        for before, after in ((f"{begin}\n{end}\n", f"{begin}\n{self.ADDED}{end}\n"),
                              (f"{end}\n", f"{self.ADDED}{end}\n")):
            for revert, code, message in (
                    ({}, 0, "queue: PASS"),
                    ({PAGE: original + before}, 1, "not the exact revert tree")):
                with self.subTest(before=before, code=code):
                    self.base, self.snapshot = base, copy.deepcopy(snapshot)
                    head = self.entries_revert_group(page=original + before,
                                                     train={PAGE: original + after},
                                                     revert=revert)
                    self.verdict(self.cli(head=head), code, message)

    def test_auto_revert_without_decision_entries_adds_none(self):
        # Without the folder, nothing changes: a revert that adds one is an extra change.
        head, _ = self.revert_group()
        self.verdict(self.cli(head=head), 0, "queue: PASS")
        revert_head = self.snapshot["pull_requests"]["3"]["head"]["sha"]
        added = self.make([revert_head], {self.ENTRY: self.DECISION})
        self.snapshot["pull_requests"]["3"]["head"]["sha"] = added
        self.nodes()[0]["pullRequest"]["headRefOid"] = added
        self.verdict(self.cli(head=self.merge(self.base, added, 3)), 1,
                     "not the exact revert tree (extra change)")

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

    # The tests of each file under .github/, written here as the contract that
    # check_queue's map must keep (GITHUB_TESTS, which says what reads each).
    AUTO_REVERT = ["python3", "-I", "tests/test_auto_revert.py"]
    QUEUE_TESTS = ["python3", "-I", "tests/test_check_queue.py"]
    RELEASE_GATE = ["python3", "-I", "tests/test_release_gate.py"]
    SAFE_PUSH = ["python3", "scripts/test_safe_push.py"]
    GITHUB_TESTS = {
        ".github/pull_request_template.md": [RELEASE_GATE, SAFE_PUSH],
        ".github/workflows/ci.yml": [AUTO_REVERT, QUEUE_TESTS, SAFE_PUSH],
        ".github/workflows/post-merge.yml": [AUTO_REVERT, QUEUE_TESTS, SAFE_PUSH],
        ".github/workflows/release-gate.yml": [SAFE_PUSH],
        ".github/workflows/safe-push-tests.yml": [SAFE_PUSH],
    }

    def github_group(self, changes, new):
        """A group whose first train makes `changes`, on a main that holds the files of
        .github/ and the tests they ask for, each test printing that it ran."""
        tests = ("tests/test_auto_revert.py", "tests/test_check_queue.py",
                 "tests/test_release_gate.py")
        self.base = self.make([self.base], {
            **{path: "name: fixture\n" for path in self.GITHUB_TESTS},
            **{path: f"print('{path} ran')\n" for path in tests}})
        self.snapshot["main"]["sha"] = self.base
        two = self.train(2, {SECOND: "The second train's reviewed line.\n"})
        one = self.train(1, changes, new=new)
        return self.merge(self.merge(self.base, one, 1), two, 2)

    def test_gaps_runs_the_tests_of_each_changed_or_deleted_github_file(self):
        # A train that replaces an enforced command with `true` changes only a workflow:
        # its tests must still run, and a deleted workflow's too.
        for number, (path, commands) in enumerate(self.GITHUB_TESTS.items()):
            for deleted in (False, True):
                with self.subTest(path=path, deleted=deleted):
                    change = None if deleted else "name: fixture\njobs: {check: {run: true}}\n"
                    group = self.github_group({path: change}, f"- check: {path}")
                    plan = self.root / f"github-plan-{number}-{deleted}.json"
                    self.verdict(self.cli("--gaps", "--plan", str(plan), head=group), 0,
                                 "queue: PASS")
                    self.assertEqual(json.loads(plan.read_text(encoding="utf-8")),
                                     {"head": group, "commands": commands})
                    output = self.verdict(self.run_plan(plan, group), 0, "queue: PASS")
                    for command in commands:
                        self.assertEqual(output.count(f"gaps: {' '.join(command)}\n"), 1)

    def test_gaps_refuses_a_github_file_it_maps_no_tests_to(self):
        # A new workflow, or any other file under .github/, has no tests until main's
        # check_queue.py names them: the group is refused, naming the file, not passed.
        for number, path in enumerate((".github/workflows/new.yml", ".github/workflows/ci.yaml",
                                       ".github/CODEOWNERS", ".github/actions/run/action.yml",
                                       ".github/workflows/ci.yml.orig")):
            with self.subTest(path=path):
                group = self.github_group({path: "name: new\n"}, f"- check: {path}")
                plan = self.root / f"unmapped-plan-{number}.json"
                self.verdict(self.cli("--gaps", "--plan", str(plan), head=group), 1,
                             f"queue: REFUSED: gaps: no tests are mapped to {path}")
                self.assertFalse(plan.exists())

    def test_gaps_refuses_a_changed_workflow_whose_mapped_test_is_deleted(self):
        # A group that changes ci.yml and deletes a test mapped to it would run fewer of
        # its tests, or none: each mapped test it deletes, alone or with the others,
        # refuses the group, naming it, until main's copy maps others.
        ci = ".github/workflows/ci.yml"
        mapped = ["scripts/test_safe_push.py", "tests/test_auto_revert.py",
                  "tests/test_check_queue.py"]
        for number, deleted in enumerate([mapped, *([test] for test in mapped)]):
            with self.subTest(deleted=deleted):
                changes = {ci: "name: fixture\njobs: {check: {run: true}}\n",
                           **{test: None for test in deleted}}
                group = self.github_group(changes, "\n".join(f"- check: {p}" for p in changes))
                plan = self.root / f"deleted-test-plan-{number}.json"
                self.verdict(self.cli("--gaps", "--plan", str(plan), head=group), 1,
                             "queue: REFUSED: gaps: declared test is missing or not a regular "
                             f"file: {deleted[0]}, which GITHUB_TESTS names for {ci}")
                self.assertFalse(plan.exists())

    def test_gap_commands_keeps_the_tests_of_a_deleted_github_file(self):
        group = self.github_group({TEXT: "A change elsewhere.\n"}, "None.")
        self.checkout(group)
        ci = ".github/workflows/ci.yml"
        # A deleted workflow asks for its tests, and a deletion excuses none of them.
        self.assertEqual(queue.gap_commands(self.repo, {ci}, {ci}), self.GITHUB_TESTS[ci])
        self.assertEqual(queue.gap_commands(self.repo, {ci}, {ci, "tests/test_auto_revert.py"}),
                         self.GITHUB_TESTS[ci])
        # A file it maps no tests to refuses, deleted or not, and so does .github itself.
        for path in (".github/old.yml", ".github"):
            with self.subTest(path=path):
                for deleted in (set(), {path}):
                    with self.assertRaisesRegex(queue.Refused,
                                                "no tests are mapped to " + re.escape(path)):
                        queue.gap_commands(self.repo, {path}, deleted)
        # A mapped test that is missing refuses, naming it and the file it is mapped to,
        # whether the group deleted it or not.
        (self.repo / "tests/test_auto_revert.py").unlink()
        for deleted in (set(), {"tests/test_auto_revert.py"}, {ci, "tests/test_auto_revert.py"}):
            with self.subTest(deleted=sorted(deleted)):
                with self.assertRaisesRegex(queue.Refused, re.escape(
                        "missing or not a regular file: tests/test_auto_revert.py, which "
                        f"GITHUB_TESTS names for {ci}")):
                    queue.gap_commands(self.repo, {ci}, deleted)

    def test_gaps_refuses_a_deleted_mapped_test_whatever_else_the_group_changes(self):
        # A group that deletes a test GITHUB_TESTS names, and changes nothing under
        # .github/, leaves that file's next change with fewer of its tests to run: the
        # deletion refuses, naming the test and the files it reads, until main's copy of
        # the map names others.
        for number, (test, first) in enumerate((
                ("tests/test_release_gate.py", ".github/pull_request_template.md"),
                ("scripts/test_safe_push.py", ".github/pull_request_template.md"),
                ("tests/test_auto_revert.py", ".github/workflows/ci.yml"),
                ("tests/test_check_queue.py", ".github/workflows/ci.yml"))):
            with self.subTest(test=test):
                message = (f"declared test is missing or not a regular file: {test}, which "
                           f"GITHUB_TESTS names for {first}")
                group = self.github_group({test: None}, f"- check: {test}")
                plan = self.root / f"deleted-mapped-plan-{number}.json"
                self.verdict(self.cli("--gaps", "--plan", str(plan), head=group), 1,
                             f"queue: REFUSED: gaps: {message}")
                self.assertFalse(plan.exists())
                # Asked for whether the group's changes name it or not.
                for checks in ({test}, set(), {TEXT}):
                    with self.assertRaisesRegex(queue.Refused, re.escape(message)):
                        queue.gap_commands(self.repo, checks, {test})

    def queue_job(self, head, base):
        """Execute the workflow's extraction and invocation with local fixture objects."""
        with (SCRIPTS.parent / ".github/workflows/ci.yml").open(encoding="utf-8") as source:
            workflow = yaml.safe_load(source)
        job = workflow["jobs"]["queue-integrity"]
        steps = [step for step in job["steps"] if step.get("name") ==
                 "Check the group with main's copy of check_queue.py"]
        self.assertEqual(len(steps), 1)
        script = steps[0].get("run")
        self.assertIsInstance(script, str)
        self.checkout(head)
        runner = self.root / "runner"
        runner.mkdir()
        env = dict(os.environ, GROUP_HEAD=head, GROUP_BASE=base,
                   GITHUB_EVENT_NAME="merge_group", RUNNER_TEMP=str(runner),
                   REPOSITORY="owner/repository")
        return subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script], cwd=self.repo,
                              env=env, capture_output=True, text=True)

    def test_queue_job_installs_test_dependency_only_for_offline_tests(self):
        with (SCRIPTS.parent / ".github/workflows/ci.yml").open(encoding="utf-8") as source:
            workflow = yaml.safe_load(source)
        steps = workflow["jobs"]["queue-integrity"]["steps"]
        install = [step for step in steps if step.get("name") ==
                   "Install the queue tests' pinned YAML parser"]
        offline = [step for step in steps if step.get("name") ==
                   "Check the queue and train checks, and automatic reverts, case by case"]
        judge = [step for step in steps if step.get("name") ==
                 "Check the group with main's copy of check_queue.py"]
        self.assertEqual(len(install), 1)
        self.assertEqual(len(offline), 1)
        self.assertEqual(len(judge), 1)
        self.assertEqual(install[0].get("if"), "github.event_name != 'merge_group'")
        self.assertEqual(offline[0].get("if"), "github.event_name != 'merge_group'")
        self.assertEqual(judge[0].get("if"), "github.event_name == 'merge_group'")

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

    def run_plan(self, plan, head, *extra):
        return subprocess.run([sys.executable, "-I", str(SCRIPTS / "check_queue.py"),
                               "--run-plan", str(plan), "--head", head, *extra],
                              cwd=self.repo, capture_output=True, text=True)

    def planned_group(self, test="print('sample test ran')\n"):
        """A group whose first train changes the sample test, and the plan --gaps --plan
        writes for it, running nothing."""
        one = self.train(1, {TEST: test}, new=f"- check: {TEST}")
        group = self.merge(self.merge(self.base, one, 1), self.two, 2)
        plan = self.root / "gaps-plan.json"
        output = self.verdict(self.cli("--gaps", "--plan", str(plan), head=group), 0,
                              f"gaps: chosen: python3 -I {TEST}", "queue: PASS")
        self.assertNotIn("sample test ran", output)
        self.assertNotIn(f"gaps: python3 -I {TEST}", output)
        return group, plan

    def test_gaps_plan_chooses_the_tests_and_run_plan_runs_them(self):
        group, plan = self.planned_group()
        self.assertEqual(json.loads(plan.read_text(encoding="utf-8")),
                         {"head": group, "commands": [["python3", "-I", TEST]]})
        self.verdict(self.run_plan(plan, group), 0, f"gaps: python3 -I {TEST}",
                     "sample test ran", "queue: PASS")
        # A plan is written to a new file only.
        self.verdict(self.cli("--gaps", "--plan", str(plan), head=group), 2, "File exists")

    def test_run_plan_reports_a_failing_test(self):
        group, plan = self.planned_group("raise SystemExit(7)\n")
        self.verdict(self.run_plan(plan, group), 1,
                     f"gaps: python3 -I {TEST} failed (exit 7)")

    def test_no_test_runs_beside_a_token(self):
        # A test is the group's own code: it could read a token in its environment or, on
        # Linux, in its parent's. Both ways of running the tests refuse while one is set.
        group, plan = self.planned_group()
        for name in ("GH_TOKEN", "GITHUB_TOKEN", "ACTIONS_ID_TOKEN_REQUEST_TOKEN", "a_token"):
            with self.subTest(name=name), patch.dict(os.environ, {name: "fixture-secret"}):
                for result in (self.run_plan(plan, group), self.cli("--gaps", head=group)):
                    output = self.verdict(result, 2, "holds a token", name)
                    self.assertNotIn("sample test ran", output)
                    self.assertNotIn("fixture-secret", output)

    def test_run_plan_runs_only_what_gaps_chooses(self):
        self.checkout(self.head)
        (self.repo / "tests/test_link.py").symlink_to("test_check_sample.py")
        command = ["python3", "-I", TEST]
        cases = (
            ({"head": self.base, "commands": [command]}, "not one for this head"),
            ({"head": self.head, "commands": [command], "more": 1}, "not one for this head"),
            ({"head": self.head, "commands": "python3"}, "not one for this head"),
            ([command], "not one for this head"),
            ({"head": self.head, "commands": [["bash", "-c", "echo ran"]]}, "does not choose"),
            ({"head": self.head, "commands": [["python3", TEST]]}, "does not choose"),
            ({"head": self.head, "commands": [["python3", "-I", TEXT]]}, "does not choose"),
            ({"head": self.head, "commands": [["python3", "-I", "scripts/test_safe_push.py"]]},
             "does not choose"),
            ({"head": self.head, "commands": [["python3", "-I", "tests/a/test_b.py"]]},
             "does not choose"),
            ({"head": self.head, "commands": [command, command]}, "repeats or misnames"),
            ({"head": self.head, "commands": [["python3", "-I", "tests/test_absent.py"]]},
             "repeats or misnames"),
            ({"head": self.head, "commands": [["python3", "-I", "tests/test_link.py"]]},
             "repeats or misnames"),
        )
        for number, (plan, message) in enumerate(cases):
            with self.subTest(plan=plan):
                path = self.root / f"plan-{number}.json"
                path.write_text(json.dumps(plan), encoding="utf-8")
                output = self.verdict(self.run_plan(path, self.head), 2, message)
                self.assertNotIn("sample test", output)
        path = self.root / "unreadable.json"
        path.write_text("{unreadable", encoding="utf-8")
        self.verdict(self.run_plan(path, self.head), 2, "could not read")
        self.verdict(self.run_plan(path, self.head, "--base", self.base), 2,
                     "--run-plan needs --head and accepts nothing else")
        self.verdict(self.cli("--plan", str(path)), 2, "--plan belongs to --gaps")

    EXPRESSIONS = {"github.token": "fixture-workflow-secret", "github.run_id": "1",
                   "github.repository": "owner/repository", "vars.STOICHEIA_REVERT_BOT": BOT}

    def gaps_step(self, steps, name, head, base, runner):
        """Run one of the queue-gaps job's steps as the runner would, the expressions of
        its env given fixture values; an expression this does not know fails the test."""
        matching = [step for step in steps if step.get("name") == name]
        self.assertEqual(len(matching), 1, name)
        values = dict(self.EXPRESSIONS, **{
            "github.event.merge_group.head_sha": head, "runner.temp": str(runner),
            "github.event.merge_group.base_sha": base})

        def value(match):
            self.assertIn(match.group(1), values)
            return values[match.group(1)]

        env = dict(os.environ, RUNNER_TEMP=str(runner), GITHUB_EVENT_NAME="merge_group")
        for key, text in (matching[0].get("env") or {}).items():
            env[key] = re.sub(r"\$\{\{\s*(.*?)\s*\}\}", value, str(text))
        return subprocess.run(["bash", "-e", "-o", "pipefail", "-c", matching[0]["run"]],
                              cwd=self.repo, env=env, capture_output=True, text=True)

    def test_gaps_job_runs_the_tests_in_a_step_that_holds_no_token(self):
        # The tests are the group's own code, and on Linux a process can read its parent's
        # environment: the step that holds the token chooses the tests and runs none, and
        # no later step declares a token. The base's judge records how it is called.
        with (SCRIPTS.parent / ".github/workflows/ci.yml").open(encoding="utf-8") as source:
            steps = yaml.safe_load(source)["jobs"]["queue-gaps"]["steps"]
        choose = [step.get("name") for step in steps].index("Choose the tests of what is new")
        self.assertIn("--plan", steps[choose]["run"])
        self.assertNotIn("--run-plan", steps[choose]["run"])
        for step in steps[choose + 1:]:
            for key, text in (step.get("env") or {}).items():
                self.assertNotIn("TOKEN", key.upper(), step)
                self.assertNotRegex(str(text), r"(?i)token|secrets\.", step)
        judge = ("import json, os, sys\n"
                 "log = os.path.join(os.environ['RUNNER_TEMP'], 'judge-calls.jsonl')\n"
                 "tokens = sorted(key for key in os.environ if 'TOKEN' in key.upper())\n"
                 "with open(log, 'a', encoding='utf-8') as calls:\n"
                 "    calls.write(json.dumps([sys.argv[1:], tokens]) + '\\n')\n")
        base = self.make([self.base], {"scripts/check_queue.py": judge})
        head = self.make([base], {"scripts/check_queue.py": "raise SystemExit('group ran')\n"})
        self.checkout(head)
        runner = self.root / "runner"
        runner.mkdir()
        for name in ("Choose the tests of what is new", "Run the tests of what is new"):
            result = self.gaps_step(steps, name, head, base, runner)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        calls = [json.loads(line) for line in
                 (runner / "judge-calls.jsonl").read_text(encoding="utf-8").splitlines()]
        plan = str(runner / "gaps-plan.json")
        self.assertEqual(calls, [
            [["--gaps", "--head", head, "--base", base, "--repo", "owner/repository",
              "--plan", plan], ["GH_TOKEN"]],
            [["--run-plan", plan, "--head", head], []]])

    @staticmethod
    def workflow(name):
        with (SCRIPTS.parent / ".github/workflows" / name).open(encoding="utf-8") as source:
            return yaml.safe_load(source)

    def test_python_modules_run_isolated_outside_the_checkout(self):
        # python3 -m puts the working directory first on the import path, so a pip/ folder
        # in a group's checkout would run in pip's place.
        modules = []
        for name in ("ci.yml", "post-merge.yml"):
            for job, value in self.workflow(name)["jobs"].items():
                for step in value.get("steps", []):
                    for line in str(step.get("run", "")).splitlines():
                        if re.search(r"\bpython3?(?:\s+-\S+)*\s+-m\b", line):
                            modules.append((name, job, step.get("working-directory"), line))
        # The check job installs the parser the lane-condition check reads the workflows
        # with (checks/24-lane-condition.toml, #346).
        self.assertEqual(sorted(job for _, job, _, _ in modules),
                         ["check", "queue-gaps", "queue-integrity"])
        for name, job, directory, line in modules:
            with self.subTest(job=job):
                self.assertEqual(directory, "${{ runner.temp }}")
                self.assertRegex(line, r"^python3 -I -m pip install -r \"\$[A-Z_]+/\S+\.txt\"$")

    def test_queue_timeouts_are_pinned(self):
        # To be measured again on the queue's trial (WORKFLOW, "Turning it on").
        jobs = self.workflow("ci.yml")["jobs"]
        self.assertEqual(jobs["acceptance"]["timeout-minutes"], 60)
        self.assertEqual(jobs["queue-gaps"]["timeout-minutes"], 75)
        self.assertEqual(jobs["queue-integrity"]["timeout-minutes"], 20)
        # The status check timeout: acceptance, then queue-gaps, which waits for it, and
        # 15 minutes for runners.
        self.assertEqual(jobs["queue-gaps"]["needs"], "acceptance")
        status = jobs["acceptance"]["timeout-minutes"] + jobs["queue-gaps"]["timeout-minutes"]
        self.assertEqual(status + 15, 150)
        guide = " ".join((SCRIPTS.parent / "docs/WORKFLOW.md").read_text(
            encoding="utf-8").split())
        self.assertIn("set the queue's status check timeout to 150 minutes", guide)
        # --merge follows an entry through one rebuild behind a group that fails.
        self.assertEqual(queue.safe_push.QUEUE_TIMEOUT, 2 * 150 * 60)

    def test_risk_job_classes_a_merge_group_r5(self):
        # The judge accepts a light pre-flight only because a merge group's own run is R5,
        # by the risk job's last case, so every check runs on the group before it merges.
        steps = self.workflow("ci.yml")["jobs"]["risk"]["steps"]
        classify = [step for step in steps if step.get("id") == "classify"]
        self.assertEqual(len(classify), 1)
        self.assertEqual(classify[0]["env"]["EVENT"], "${{ github.event_name }}")
        output = self.root / "github-output"
        env = dict(os.environ, EVENT="merge_group", BASE_REF="", HEAD_SHA="", RELEASE="false",
                   REF=f"refs/heads/gh-readonly-queue/main/pr-1-{self.head}",
                   GITHUB_OUTPUT=str(output), RUNNER_TEMP=str(self.root))
        result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", classify[0]["run"]],
                                cwd=self.repo, env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("a merge_group event of", result.stdout)
        self.assertEqual(output.read_text(encoding="utf-8").splitlines(),
                         ["class=R5", "formal_model=true"])

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

    def test_entry_attributes_cannot_hide_a_repeated_heading_from_the_judge(self):
        # A train gives the decisions page working-tree-encoding=UTF-7, with which Git
        # writes "## 20 October 2026" to the group's checkout as "+ACMAIw- 20 October
        # 2026": the judge reads the page's blob, as GitHub shows it, never the checkout.
        page = self.trees[self.base][PAGE] + "\n## 20 October 2026\n\nRepeated date.\n"
        one = self.train(1, {PAGE: page,
                             ".gitattributes": f"{PAGE} working-tree-encoding=UTF-7\n"})
        group = self.merge(self.merge(self.base, one, 1), self.two, 2)
        self.checkout(group)
        self.assertNotIn(b"\n## 20 October 2026\n\nRepeated", (self.repo / PAGE).read_bytes())
        self.verdict(self.cli(head=group, prepare=False), 1, PAGE, "repeated dated heading")

    def test_a_group_page_that_is_no_regular_file_is_unreadable(self):
        blob = self.git("hash-object", "-w", "--stdin", data="## 20 October 2026\n").strip()
        index = self.root / "page-index"
        for mode in ("100755", "120000"):
            with self.subTest(mode=mode), patch.dict(os.environ, GIT_INDEX_FILE=str(index)):
                self.git("read-tree", self.head)
                self.git("update-index", "--cacheinfo", f"{mode},{blob},{PAGE}")
                head = self.make([self.head], tree=self.git("write-tree").strip())
                with self.assertRaisesRegex(ValueError, "page at the group head is not a "
                                                        "regular file"):
                    queue.page_blob(self.repo, head)
        self.assertEqual(queue.page_blob(self.repo, self.head), self.trees[self.head][PAGE])


class TreeTests(unittest.TestCase):
    """Rule (d)'s line reading, each case run by --tree on a repository whose index holds
    only the decisions page, which is all that --tree reads."""

    ORIGINAL = "## 20 October 2026\n\nA previous decision.\n"
    PLAIN = "which is not plain"
    REPEATED = "repeated dated heading"
    YEAR = "a year in no date this check reads"

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name) / "repo"
        self.page = self.repo / PAGE
        self.page.parent.mkdir(parents=True)
        self.enterContext(patch.dict(os.environ, fixture_environment(), clear=True))
        self.page.write_text(self.ORIGINAL, encoding="utf-8")
        for args in (("init", "--quiet", "--initial-branch=main"), ("add", "--", PAGE)):
            subprocess.run(["git", *args], cwd=self.repo, check=True, capture_output=True)

    def tree(self, added: str, original: str | None = None):
        """Run --tree on the page with `added` as its last lines."""
        text = (self.ORIGINAL if original is None else original) + "\n" + added + "\n"
        self.page.write_bytes(text.encode("utf-8"))
        return self.check()

    def check(self):
        """Run --tree on the repository as it stands."""
        return subprocess.run([sys.executable, "-I", str(SCRIPTS / "check_queue.py"),
                               "--tree", str(self.repo)], cwd=self.repo,
                              capture_output=True, text=True)

    def refused(self, cases, original: str | None = None):
        """Each (added, message) case is refused, naming the page and the message."""
        for added, message in cases:
            with self.subTest(added=added):
                result = self.tree(added, original)
                output = result.stdout + result.stderr
                self.assertEqual(result.returncode, 1, output)
                self.assertIn(f"queue: REFUSED: {PAGE}:", output)
                self.assertIn(message, output)

    def passes(self, cases, original: str | None = None):
        for added in cases:
            with self.subTest(added=added):
                result = self.tree(added, original)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("queue: PASS", result.stdout)

    def test_the_page_as_written_passes(self):
        self.passes(["## 21 October 2026", "### 20 October 2026", "#20 October 2026",
                     "A paragraph of 20 October 2026, in prose.", "- 20 October 2026",
                     "> 20 October 2026", "> quoted prose\n> 20 October 2026",
                     "> ### 20 October 2026", "<h3>20 October 2026</h3>",
                     "Prose that quotes the tag as &lt;h2&gt;, with <b>HTML</b> and a "
                     "[link](#x).",
                     "21 October 2026\n===\n\nNotes\n---", "## 21 October 2026 ##",
                     "# Notes #", "##"])

    def test_a_dated_heading_repeats_wherever_its_date_stands(self):
        self.refused((added, self.REPEATED) for added in (
            " ## 20 October 2026", "   ## 20 October 2026", "    ## 20 October 2026",
            "# 20 October 2026", "## 20 october 2026", "## 20 Oct 2026", "## 20 OCT 2026",
            "## 20th October 2026", "## October 20, 2026",
            "## 2026-10-20", "## 20 October 2026: a later note",
            "## A note of 20 October 2026", "## 20 October 2026 ##",
            "## 20 October 2026 ####   ", "# 20 October 2026 #",
            "20 October 2026\n---------------", "20 October 2026\n===",
            "20 October 2026\n-", "20 October 2026\n- ", "20 October\n2026\n===",
            "Prose.\r## 20 October 2026", "Prose.\r\n## 20 October 2026"))
        self.refused([("## 20 October 2026", self.REPEATED)],
                     original="\N{BYTE ORDER MARK}" + self.ORIGINAL)

    def test_heading_text_must_be_plain(self):
        # What a renderer would read through (character references, inline HTML, link
        # syntax, emphasis, escapes and characters outside ASCII) refuses instead.
        self.refused((added, self.PLAIN) for added in (
            "## 20&nbsp;October 2026", "## 20 Octo&#98;er 2026", "## 20 October&#x20;2026",
            "## [20 October 2026](#x)", "## [20 October 2026](https://example.test/a(b))",
            r"## [20 October 2026](https://example.test/a\(b\))",
            "## [20 October 2026][x]", "## [20](#a) [October](#b) [2026](#c)",
            "## 20 Octo<!-- -->ber 2026", "## 20 October 2026<span></span>",
            "## <em>20 October</em> 2026", "## **20 October 2026**", "## 20 `October` 2026",
            "## 20 October\\_2026", "## 20_October 2026",
            "## 20 October 2026\N{ZERO WIDTH SPACE}",
            "## 20\N{NO-BREAK SPACE}October\N{NO-BREAK SPACE}2026",
            "## \N{FULLWIDTH DIGIT TWO}\N{FULLWIDTH DIGIT ZERO} October 2026",
            "## 20 \N{CYRILLIC CAPITAL LETTER O}ctober 2026",
            "## 20 October 2026 [a later note](#x)",
            "## 20 October 2026 &amp; 21", "## 20 October 2026 <b>and after</b>",
            "## 20 October 2026#", "### 20 October 2026\n---", "20\tOctober 2026\n==="))

    def test_containers_hide_no_heading(self):
        self.refused((added, self.REPEATED) for added in (
            "> ## 20 October 2026", ">## 20 October 2026", "- ## 20 October 2026",
            "+ ## 20 October 2026", "1. ## 20 October 2026", "1) ## 20 October 2026",
            "> - > ## 20 October 2026", "> - ## 20 October 2026", "* > 2. ## 20 October 2026",
            "> 20 October 2026\n> ---", "- 20 October 2026\n---",
            "- 20 October 2026\n  ---", "> - 20 October 2026\n---",
            "1.  Item\n\n    ## 20 October 2026",
            # GFM's footnote definitions and task items hold blocks too (the fourth review).
            "[^n]: ## 20 October 2026", "[^n]:## 20 October 2026",
            "   [^n]: ## 20 October 2026", "> [^n]: ## 20 October 2026",
            "- [ ] ## 20 October 2026", "- [x] ## 20 October 2026",
            "- [X] ## 20 October 2026", "* [ ] ## 20 October 2026",
            # A list number that cannot open a list inside a paragraph is its text.
            "Notes\n20. October 2026\n===", "Notes\n20) October 2026\n==="))

    def test_code_and_html_hide_no_heading(self):
        # The cases a reading of blocks once passed, the third review's five among them.
        self.refused((added, self.REPEATED) for added in (
            "```markdown\n## 20 October 2026\n```", "~~~\n20 October 2026\n---\n~~~",
            "    ## 20 October 2026\n\n    20 October 2026\n    ---",
            "<!--\n## 20 October 2026\n-->", "<div>\n## 20 October 2026\n</div>\n",
            "<x title=\">\">\n## 20 October 2026\n\n", "<x title='<'>\n## 20 October 2026\n\n",
            "<pre>\n## 20 October 2026\n</pre>", "```\n## hidden\n```\n## 20 October 2026",
            "<div>\n## hidden\n</div>\n\n## 20 October 2026",
            "<pre>\n## hidden\n</pre>\n## 20 October 2026",
            "> ```\n> ## hidden\n## 20 October 2026",
            "- ```\n  ## hidden\n## 20 October 2026",
            "- ```\n## 20 October 2026", "Some prose.\n<span>\n## 20 October 2026",
            "- <div>\n## 20 October 2026", "20 October\n    2026\n===",
            "- Item\n\n  ```\n## 20 October 2026"))

    def test_an_underline_reads_back_to_the_blank_line(self):
        # A line of spaces and tabs is blank; a line of no-break spaces, or one holding
        # only a list marker or a > (indented four columns or more, it is a paragraph's
        # text), is not. A later underline's text holds an earlier one's.
        self.refused((added, self.REPEATED) for added in (
            "20 October\n*\n2026\n---", "20 October\n\N{NO-BREAK SPACE}\n2026\n===",
            "20 October\n1.\n2026\n---", "20 October\n    ===\n2026\n---",
            "21 October 2026\n===\nNotes\n---", "20 October\n>\n2026\n===",
            "20 October 2026\n    >\n===", "20 October 2026\n\t>\n===",
            "- 20 October 2026\n      >\n  ===", "> 20 October 2026\n>     >\n> ===",
            "21 October 2026\n===\n>\nNotes\n---"))
        self.refused([("21 October 2026\n===\nNotes\n---", self.PLAIN)])
        self.passes(["21 October 2026\n===\n \t\nNotes\n---"])
        # The blank line ends the stretch: no date is read across it, though the heading
        # "2026" below it holds a year in no date.
        result = self.tree("20 October\n\n2026\n===")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(self.YEAR, result.stdout)
        self.assertNotIn(self.REPEATED, result.stdout)

    def test_a_year_must_stand_in_a_date_the_check_reads(self):
        # A date written in a way the check does not read refuses, never passes (the
        # fourth review): every year from 1900 to 2199 must be a read date's year, in its
        # own line, and a year in a list number or footnote marker never is.
        self.refused((added, self.YEAR) for added in (
            "## 20/10/2026", "## 20.10.2026", "## 20-10-2026", "## 10/20/2026",
            "## The 20th of October 2026", "## 2026 October 20", "## October 2026",
            "## 2026", "## 31 February 2026", "## 2026-02-31", "## FY2026",
            "## 21 October 2026 (also 20/10/2026)", "# 20October2026",
            "20 October\n2026\n===", "Notes\n2026. October 20\n===", "1. October 2026\n   =",
            "Notes 20 October\n[^2026]:\n==="))
        self.passes(["## 21 October 2026", "## October 21, 2026", "## 2026-10-21",
                     "## 21st October 2026", "## 21 October 2026 to 22 October 2026",
                     "## Book I, 1066 and after", "## 2200 propositions", "### 2026",
                     "A paragraph of 2026, in prose.", "1. 21 October 2026\n   ---"])

    def test_a_page_a_checkout_may_rewrite_is_unreadable(self):
        # --tree reads the checkout, where Git writes the page through its attributes:
        # with working-tree-encoding=UTF-7, "## 20 October 2026" stands there as
        # "+ACMAIw- 20 October 2026" (the fourth review), which no line reading takes for
        # a heading. So any attribute that can change how a checkout writes the page,
        # from .gitattributes or from the repository's own attributes file, is unreadable.
        written = ("+ACMAIw- 20 October 2026\n\nA previous decision.\n\n"
                   "+ACMAIw- 20 October 2026\n")
        cases = (("working-tree-encoding=UTF-7", "working-tree-encoding=UTF-7"),
                 ("filter=hidden", "filter=hidden"), ("ident", "ident=set"),
                 ("text", "text=set"), ("-text", "text=unset"), ("eol=crlf", "eol=crlf"),
                 ("crlf", "crlf=set"))
        for where in (".gitattributes", ".git/info/attributes"):
            for value, reported in cases:
                with self.subTest(where=where, value=value):
                    attributes = self.repo / where
                    attributes.write_text(f"{PAGE} {value}\n", encoding="utf-8")
                    self.page.write_text(written, encoding="utf-8")
                    result = self.check()
                    attributes.unlink()
                    self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                    self.assertIn(f"the decisions page has {reported}, with which",
                                  result.stderr)
                    self.assertIn("take the attribute off the page", result.stderr)
        self.page.write_text(self.ORIGINAL, encoding="utf-8")
        self.assertEqual(self.check().returncode, 0)

    def test_html_heading_tags_refuse_anywhere(self):
        self.refused((added, "an HTML heading tag") for added in (
            "<h2>20 October 2026</h2>", "<H1 class=\"date\">Any heading</H1>",
            "Some text <h2\nid=x>A heading</h2>", "```html\n<h2>20 October 2026</h2>\n```",
            "<!-- <h1>hidden heading</h1> -->"))

    def test_long_lines_and_pages_are_read_in_linear_time(self):
        # 200,000 characters, in the shapes that once backtracked ("## a", spaces and a
        # last word: about 0.45 s at 8,000 characters, and hours at 200,000; "<a" and
        # spaces, quadratic in a tag reader), in long runs of markers, digits and
        # underlines, and as pages of many lines, are read in under a second.
        size = 200_000
        lines = ("## a" + " " * size + "b", "## a" + " " * size, "## " + "#" * size + " x",
                 "## " + "<" * size, "## " + "<!--" * (size // 4), "## " + "<a" * (size // 2),
                 "<a" + " " * size, "## " + "](" * (size // 2), "## " + "][" * (size // 2),
                 "## " + "&#" * (size // 2),
                 "> " * (size // 2) + "## 20 October 2026", "- " * (size // 2),
                 "1. " * (size // 3 + 1), "1" * size + "x", "=" * size + "x",
                 "-" * size + " -", "## 1 " + "a " * (size // 2),
                 "## 1 January " + "2026 1 January " * (size // 15),
                 "## [20 October 2026](a" + "(" * size, "<x title=\"" + ">" * size + "\">",
                 "## 20 October 2026" + " " * size + "#", "<h2" * (size // 3 + 1),
                 "[^" + "a" * size, "[^" + "]" * size, "[^a]:" * (size // 5),
                 "[ ] " * (size // 4), "1. " * (size // 3) + "2026", "Notes 2026 " * (size // 11))
        pages = ("a\n=\n" * (size // 4), "a\n" * (size // 2) + "=",
                 "x\n" + "-\n" * (size // 2), "1 January 2026\n=\n" * (size // 16 + 1),
                 "## 20 October 2026\n" * (size // 19 + 1),
                 "a\n" + "\N{NO-BREAK SPACE}\n" * (size // 2) + "=", ">\n" * (size // 2),
                 "1. a\n" * (size // 5) + "=", "[^a]: 2026\n" * (size // 11 + 1) + "=")
        for page in (*("Paragraph.\n\n" + line + "\n=\n" for line in lines), *pages):
            with self.subTest(page=page[:24]):
                self.assertGreaterEqual(len(page), size)
                started = time.perf_counter()
                queue.heading_problems(page)
                self.assertLess(time.perf_counter() - started, 1.0)


if __name__ == "__main__":
    unittest.main()
