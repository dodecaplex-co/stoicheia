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
import subprocess
import sys
import tempfile
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
            "scripts/safe_push.py": "# The fixture's trusted base harness.\n",
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

    def block(self, head, base=None, harness=None):
        base = base or self.base
        blob = self.git("rev-parse", f"{base}:scripts/safe_push.py").strip()
        return queue.safe_push.preflight_block(head, base, {
            "full": True, "time": "20 October 2026",
            "harness": harness or f"origin/main's `scripts/safe_push.py` (blob `{blob[:12]}`)",
            "steps": [("4", "full checks", "ok", 1)],
        })

    def train(self, number, changes, start=None, new="None."):
        start = start or self.base
        member = self.make([start], changes)
        head = self.merge(start, member)
        body = (
            "## Members\n\n"
            "| Branch | Head | /code-review | /security-review | /no-mistakes |\n"
            "|---|---|---|---|---|\n"
            f"| content/{number} | {member} | Independent reader: pass, no findings. | "
            f"Independent reader: pass, no findings. | passed at {member} |\n\n"
            f"## What is new\n\n{new}\n\n" + self.block(head)
        )
        self.pr(number, head, f"train/area-{number}", body)
        return head

    def pr(self, number, head, ref, body, labels=None, author=None):
        self.snapshot["pull_requests"][str(number)] = {
            "number": number, "head": {"sha": head, "ref": ref}, "body": body,
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
                          "pullRequest": {"number": number, "headRefOid": head}})

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
        self.set_body(queue.safe_push.BLOCK.sub("", self.body()))
        self.verdict(self.cli(), 1, "pre-flight: missing or malformed block")

    def test_preflight_names_another_harness_blob(self):
        old = self.git("rev-parse", f"{self.base}:scripts/safe_push.py").strip()
        wrong = self.git("rev-parse", f"{self.base}:{TEXT}").strip()
        self.set_body(self.body().replace(old[:12], wrong[:12]))
        self.verdict(self.cli(), 1, "harness blob is not the recorded base's safe_push.py")

    def test_preflight_hidden_duplicated_or_malformed_refuses(self):
        original = self.body()
        block = queue.safe_push.BLOCK.search(original).group()
        for replacement in ("```\n" + block + "\n```", "<!-- hidden\n" + block + "\n-->",
                            block + "\n" + block, block.replace("sha=", "sha=BAD")):
            with self.subTest(replacement=replacement[:30]):
                self.set_body(original.replace(block, replacement))
                self.verdict(self.cli(), 1, "pre-flight:")

    def test_preflight_skipped_full_checks_refuses(self):
        self.set_body(self.body().replace("by origin/main's", "full checks skipped; by origin/main's"))
        self.verdict(self.cli(), 1, "full checks skipped")

    def test_preflight_uses_its_recorded_base_harness(self):
        old_base = self.base
        self.base = self.make([old_base], {
            "scripts/safe_push.py": "# A newer main harness.\n",
        })
        self.snapshot["main"]["sha"] = self.base
        first = self.merge(self.base, self.one, 1)
        self.verdict(self.cli(head=self.merge(first, self.two, 2)), 0, "queue: PASS")

    def test_train_body_evidence_and_declaration_refuse(self):
        original = self.body()
        for body, message in (
            (original.replace("## Members", "## No members"), "Members"),
            (original.replace("Independent reader: pass, no findings.", "TODO"), "not written"),
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
        body = self.body().replace("| Independent reader: pass, no findings. | passed",
                                   "| Not required: no protected paths. | passed")
        self.set_body(body)
        first = self.merge(self.base, one, 1)
        self.verdict(self.cli(head=self.merge(first, self.two, 2)), 1,
                     "/security-review says Not required for protected paths")

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

    def test_conflict_markers_refuse_in_tracked_text(self):
        for marker in ("<<<<<<< branch\n", "=======\n", ">>>>>>> other\n", "||||||| base\n"):
            with self.subTest(marker=marker):
                one = self.train(1, {TEXT: marker})
                first = self.merge(self.base, one, 1)
                group = self.merge(first, self.two, 2)
                self.verdict(self.cli(head=group), 1, TEXT, "conflict marker")

    def test_tree_only_scans_without_rendering(self):
        self.checkout(self.head)
        lean = self.repo / "Elements/BookI/Prop01.lean"
        lean.write_text("-- fixture\n<<<<<<< branch\n", encoding="utf-8")
        (self.repo / "scripts/render.py").write_text("raise SystemExit(9)\n", encoding="utf-8")
        self.verdict(self.cli(tree=True, prepare=False), 1, str(lean.relative_to(self.repo)),
                     "conflict marker")
        lean.write_text("-- fixture\n", encoding="utf-8")
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
                self.verdict(self.cli(head=self.merge(first, self.two, 2)), 1,
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
        self.pr(3, head, "revert/failed-group",
                "\n".join(f"Reverts: {sha}" for sha in reverted) + "\n",
                ["auto-revert"], {"login": BOT, "type": "Bot"})
        return self.merge(self.base, head, 3), old_base

    def test_exact_auto_revert_passes(self):
        head, _ = self.revert_group()
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
                self.set_body(f"Reverts: {sha}\n", 3)
                self.verdict(self.cli(head=head), 1, message)

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
            "scripts/safe_push.py": "# A new fixture harness.\n",
        }, new="- check: scripts/another.py\n- check: scripts/test_another.py\n"
               "- check: scripts/safe_push.py")
        first = self.merge(self.base, one, 1)
        self.verdict(self.cli("--gaps", head=self.merge(first, self.two, 2)), 0,
                     "gaps: python3 -I scripts/test_another.py",
                     "gaps: python3 scripts/test_safe_push.py",
                     "another test ran", "safe push test ran")

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
        self.checkout(self.head)
        (self.repo / TEXT).unlink()
        self.verdict(self.cli(tree=True, prepare=False), 2, "cannot read a tracked file")

    def test_tree_mode_rejects_group_arguments(self):
        self.verdict(self.cli("--gaps", tree=True), 2, "--tree accepts only --render")


if __name__ == "__main__":
    unittest.main()
