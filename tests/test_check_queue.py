#!/usr/bin/env python3
"""Exercise queue refusals in throwaway git repositories, without network or Lean.

    python3 -m pip install -r scripts/requirements-test_safe_push.txt
    python3 -I tests/test_check_queue.py

The workflow cases read .github/workflows/ (ci.yml, post-merge.yml and the queue's
judge, queue-judge.yml, whose jobs they run step by step) with PyYAML, pinned in
scripts/requirements-test_safe_push.txt; install it in a virtual environment, since a
system Python may refuse the install and python3 -I does not see a user install.
Fixtures write objects with hash-object, mktree and commit-tree. Their own index
and checkout use read-tree; the source repository's index and history never move.
Every CLI invocation supplies --github-json, so missing fixture data cannot cause
a GitHub request; a workflow's steps, which call gh, find a stand-in for it first on
their PATH (FAKE_GH), which answers from the fixture's snapshot.
"""

from __future__ import annotations

import base64
import contextlib
import copy
import io
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
import warnings
import zipfile
from pathlib import Path
from unittest.mock import patch

import yaml

sys.dont_write_bytecode = True
SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
import check_queue as queue
from check_acceptance import VERDICTS_FORMAT

PAGE = queue.safe_push.DECISIONS
TEXT = "notes/first.txt"
SECOND = "notes/second.txt"
CHECK = "scripts/check_sample.py"
TEST = "tests/test_check_sample.py"
BOT = "revert-fixture[bot]"
REVIEW = "Independent reader at"
# Main's own classifier, which a fixture's main is given when a light pre-flight is judged.
CLASSIFIER = (SCRIPTS / "risk.py").read_text(encoding="utf-8")
# The queue's judge, which the organization ruleset requires from main.
JUDGE = ".github/workflows/queue-judge.yml"
JUDGE_JOBS = ("queue-integrity", "queue-gaps")
# The group's CI run, its acceptance job and that job's artifact, as GitHub gives them
# (acceptance_answers): the job ran from STARTED to COMPLETED, and made the artifact at
# CREATED.
RUN, JOB, ARTIFACT = 7001, 9001, 5001
STARTED, CREATED, COMPLETED = ("2026-10-27T21:00:00Z", "2026-10-27T21:49:00Z",
                               "2026-10-27T21:50:00Z")
VERDICTS = json.dumps({"format": VERDICTS_FORMAT, "checker": "fixture",
                       "verdicts": {}}).encode("utf-8")


def artifact_zip(members, method=zipfile.ZIP_STORED) -> bytes:
    """A zip of (name, bytes) members, each a regular file unless its ZipInfo says else, and
    each compressed by `method` (stored, by default) unless its ZipInfo says else."""
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w") as archive:
        for name, data in members:
            info = name if isinstance(name, zipfile.ZipInfo) else zipfile.ZipInfo(name)
            if not isinstance(name, zipfile.ZipInfo):
                info.external_attr = 0o100644 << 16
                info.compress_type = method
            archive.writestr(info, data)
    return buffer.getvalue()


def sized_zip(size: int) -> bytes:
    """A zip of exactly `size` bytes: the four files the acceptance job keeps, stored, each
    of a quarter of what the zip's headers leave."""
    names = queue.ACCEPTANCE_FILES
    each, rest = divmod(size - len(artifact_zip([(name, b"") for name in names])), len(names))
    return artifact_zip([(name, b"x" * (each + (rest if number == 0 else 0)))
                         for number, name in enumerate(names)])


def declaring(data: bytes, name: str, size: int) -> bytes:
    """The zip `data` with its central directory declaring `size` bytes for `name`'s file,
    whatever the file holds: the size zipfile reads it by."""
    data, at = bytearray(data), 0
    while (at := data.find(b"PK\x01\x02", at)) != -1:
        length = int.from_bytes(data[at + 28:at + 30], "little")
        if data[at + 46:at + 46 + length] == name.encode("utf-8"):
            data[at + 24:at + 28] = size.to_bytes(4, "little")
        at += 4
    return bytes(data)


# The acceptance job's artifact in the ratchet, as its "Keep the reports" step keeps it.
KEPT_REPORTS = artifact_zip([("report.md", b"# Acceptance\n"), ("verdicts.json", VERDICTS),
                             ("main-report.md", b"# Main\n"), ("main.json", VERDICTS)])


def acceptance_answers(head: str) -> dict:
    """GitHub's answers, as a fixture keys them (check_queue.GitHub), for a group whose CI
    run's acceptance job passed: the run, listed for the head and read by its id; its
    jobs, acceptance and another; its acceptance artifact; and that artifact's zip."""
    run = {"id": RUN, "run_attempt": 1, "status": "in_progress", "head_sha": head,
           "event": "merge_group", "path": ".github/workflows/ci.yml",
           "head_repository": {"full_name": "owner/repository"}}
    job = {"id": JOB, "run_id": RUN, "run_attempt": 1, "name": "acceptance",
           "status": "completed", "conclusion": "success", "started_at": STARTED,
           "completed_at": COMPLETED}
    artifact = {"id": ARTIFACT, "name": "acceptance", "expired": False, "created_at": CREATED,
                "workflow_run": {"id": RUN, "head_sha": head}}
    return {"ci_runs": {"total_count": 1, "workflow_runs": [run]},
            "runs": {str(RUN): run},
            "jobs": {str(RUN): {"total_count": 2, "jobs": [dict(job, id=JOB - 1, name="check"),
                                                           job]}},
            "artifacts": {str(RUN): {"total_count": 1, "artifacts": [artifact]}},
            "artifact_zips": {str(ARTIFACT): base64.b64encode(KEPT_REPORTS).decode("ascii")}}


# A stand-in for gh, first on the PATH of a workflow's steps: `gh api` answered from a
# fixture's snapshot, by the keys check_queue.GitHub's fixtures use, each call logged.
FAKE_GH = r'''
import base64, json, re, sys
snapshot_path, log_path, args = sys.argv[1], sys.argv[2], sys.argv[3:]
with open(log_path, "a", encoding="utf-8") as log:
    log.write(json.dumps(args) + "\n")
with open(snapshot_path, encoding="utf-8") as source:
    snapshot = json.load(source)
ROUTES = (("commits/main", "main"), ("pulls/([0-9]+)", "pull_requests"),
          ("actions/runs/([0-9]+)", "runs"),
          (r"issues\?state=open&labels=main-red&per_page=100", "main_red"),
          (r"actions/workflows/ci\.yml/runs\?event=merge_group&head_sha=[0-9a-f]{40}"
           "&per_page=100", "ci_runs"),
          (r"actions/runs/([0-9]+)/jobs\?filter=latest&per_page=100", "jobs"),
          (r"actions/runs/([0-9]+)/artifacts\?name=acceptance&per_page=100", "artifacts"),
          ("actions/artifacts/([0-9]+)/zip", "artifact_zips"),
          ("collaborators/([A-Za-z0-9-]+)/permission", "permissions"))
if args[:2] == ["api", "graphql"]:
    kind, value = "queue", snapshot["queue"]
else:
    endpoint = args[-1].removeprefix("repos/owner/repository/")
    if args[:3] != ["api", "--method", "GET"] or endpoint == args[-1]:
        sys.exit("fake gh: a call it does not read")
    for pattern, kind in ROUTES:
        if match := re.fullmatch(pattern, endpoint):
            value = snapshot[kind]
            value = value[match.group(1)] if match.groups() else value
            break
    else:
        sys.exit("fake gh: an endpoint it does not read")
if kind == "artifact_zips":
    sys.stdout.buffer.write(base64.b64decode(value))
else:
    print(json.dumps(value))
'''
# A stand-in for python3, first on the same PATH: this test's Python, but pip's install
# of a requirements file is checked, never run, so that no step reaches the network.
FAKE_PYTHON = '''#!/bin/sh
if [ "$#" = 6 ] && [ "$1" = -I ] && [ "$2" = -m ] && [ "$3" = pip ] && [ "$4" = install ] \\
    && [ "$5" = -r ]; then
  test -f "$6" && echo "fixture pip: would install $6" && exit 0
  echo "fixture pip: no requirements file $6" >&2
  exit 1
fi
for argument in "$@"; do
  if [ "$argument" = pip ]; then echo "fixture pip: a form it does not read" >&2; exit 1; fi
done
exec {python} "$@"
'''


def permission_answer(login: str, base: str, role: str | None = None) -> dict:
    """GitHub's REST answer for an account's permission on the repository
    (collaborators/{login}/permission), as a fixture keys it by login: its legacy base
    role, `base`, and the name of its role, `role`, that base role unless given."""
    return {"permission": base, "role_name": role or base,
            "user": {"login": login, "type": "User"}}


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
            # Each account's permission on the repository, keyed by login: the fixture's
            # author, the owner's account, and someone, a person who edits a body in the
            # cases below, are writers.
            "permissions": {"fixture": permission_answer("fixture", "admin"),
                            "someone": permission_answer("someone", "write")},
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

    def test_a_harness_check_named_by_a_string_of_its_own_is_read(self):
        # Main's safe_push.py names a check by EMPTY_CHECK, bound once, by a plain
        # assignment of its top level, to a string (harness_value): read as a harness, it
        # gives its names, that one among them. A name bound twice, conditionally, to a
        # non-string, augmented, imported or not at all still refuses.
        real = self.make([self.base], {"scripts/safe_push.py": (
            SCRIPTS / "safe_push.py").read_text(encoding="utf-8")})
        names = queue.harness_check_names(self.repo, real)
        self.assertEqual(names, {f"4. {name}" for name, _ in (*queue.safe_push.CHECKS,
                                                              *queue.safe_push.NEGATIVE)})
        self.assertIn("4. git status --porcelain is empty", names)
        lists = 'CHECKS = [("lake build", None), (EMPTY, None)]\nNEGATIVE = [("negative", None)]\n'
        for label, binding in (
                ("twice", 'EMPTY = "git status"\nEMPTY = "another"\n'),
                ("twice, by one assignment", 'EMPTY = EMPTY = "git status"\n'),
                ("conditionally", 'NOTE = "a note"\nif FLAG:\n    EMPTY = "git status"\n'),
                ("to a non-string", "EMPTY = 4\n"),
                ("augmented", 'EMPTY = "git status"\nEMPTY += " again"\n'),
                ("imported", 'EMPTY = "git status"\nfrom checks import EMPTY\n'),
                ("unbound", "")):
            with self.subTest(label):
                harness = self.make([self.base], {"scripts/safe_push.py": binding + lists})
                with self.assertRaisesRegex(queue.Refused, "harness's checks could not be read"):
                    queue.harness_check_names(self.repo, harness)

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

    def test_valid_later_train_deleting_readme_markers_is_caught(self):
        # #578: README.md's markers are written by hand, so its hand-written part is read
        # with each region's body emptied and its markers kept (heath.outside). Train 1
        # adds Book II's region inline in a line of prose; a reviewed member of train 2, on
        # train 1's member, deletes it, markers and all, and keeps the prose. Every merge is
        # automatic, and with the regions taken out whole, markers and all, as before #578,
        # the hand-written part read as train 1 left it.
        readme = "Prose by hand.\n<!-- scope:I -->\nRow.\n<!-- /scope:I -->\n"
        added = readme + "Book II: <!-- scope:II -->Row two.<!-- /scope:II --> Read it.\n"
        self.base = self.make([self.base], {"README.md": readme})
        self.snapshot["main"]["sha"] = self.base
        self.nodes().clear()
        one = self.train(1, {"README.md": added})
        member = queue.parents(self.repo, one)[1]
        deleted = self.make([member], {"README.md": readme + "Book II:  Read it.\n"})
        head = self.merge(self.merge(self.base, member), deleted)
        rows = "".join(f"| content/{name} | {sha} | {REVIEW} {sha[:12]}: pass. | "
                       f"{REVIEW} {sha[:12]}: pass. | passed at {sha} |\n"
                       for name, sha in (("1b", member), ("2", deleted)))
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
        # someone is a writer (setUp); a person without write access refuses (below).
        self.nodes()[0]["pullRequest"]["editor"] = {"__typename": "User", "login": "someone"}
        self.verdict(self.cli(), 0, "queue: PASS")

    # Rule (b)'s second requirement rests on write access (#617): an ordinary queued entry
    # passes only when its author, and its body's last editor when it has one, have write,
    # maintain or admin access, which GitHub's REST answer gives as admin or write.
    WRITER = "write, maintain or admin access to owner/repository"

    def edited_by(self, login, *answer, typename="User"):
        """The first entry's body, last edited by `login`, of GitHub's type `typename`, whose
        permission GitHub gives as `answer` (permission_answer's base and role) if given."""
        self.nodes()[0]["pullRequest"]["editor"] = {"__typename": typename, "login": login}
        if answer:
            self.snapshot["permissions"][login] = permission_answer(login, *answer)

    def test_a_body_last_edited_by_a_member_without_write_access_refuses(self):
        # An organization member who may open a pull request between the repository's
        # branches, and whose base permission or team role is read or triage, edits the
        # body after a writer has queued it.
        for answer in (("read", "read"), ("read", "triage")):
            with self.subTest(answer=answer):
                self.edited_by("member", *answer)
                self.verdict(self.cli(), 1, f"#1: its body's last editor has no {self.WRITER}")

    def test_a_body_last_edited_by_an_outside_account_refuses(self):
        # Neither a member nor a collaborator: a reader of a public repository, or none.
        for base in ("read", "none"):
            with self.subTest(base=base):
                self.edited_by("outsider", base)
                self.verdict(self.cli(), 1, f"#1: its body's last editor has no {self.WRITER}")

    def test_an_author_without_write_access_refuses(self):
        # The body never edited since it was opened: its author's own words.
        self.assertIsNone(self.nodes()[0]["pullRequest"]["editor"])
        self.snapshot["pull_requests"]["1"]["user"] = {"login": "contributor", "type": "User"}
        for base in ("read", "none"):
            with self.subTest(base=base):
                self.snapshot["permissions"]["contributor"] = permission_answer(
                    "contributor", base)
                self.verdict(self.cli(), 1, f"#1: its author has no {self.WRITER}")

    def test_writers_pass(self):
        # The owner's account, admin, wrote the pull request and last edited its body; then
        # a maintainer, or a custom role built on write, whose permission GitHub gives as
        # write, last edited it.
        self.assertEqual(self.snapshot["permissions"]["fixture"]["permission"], "admin")
        self.edited_by("fixture")
        self.verdict(self.cli(), 0, "queue: PASS")
        for role in ("maintain", "write", "queue-writer"):
            with self.subTest(role=role):
                self.edited_by("maintainer", "write", role)
                self.verdict(self.cli(), 0, "queue: PASS")

    def test_a_failed_permission_read_is_unreadable(self):
        # The answer missing, or not one GitHub gives (maintain is given as write), is
        # unreadable, never a pass: for the author's read and for the editor's alike.
        self.edited_by("someone")
        for login, whose in (("fixture", "#1's author"), ("someone", "#1's body's last editor")):
            original = self.snapshot["permissions"][login]
            user = original["user"]
            for answer in (None, [], {}, {"permission": "admin"}, {"user": user},
                           {"user": None, "permission": "admin"},
                           {"user": {}, "permission": "admin"},
                           {"user": {"login": 7}, "permission": "admin"},
                           *({"user": user, "permission": value}
                             for value in (None, 3, ["admin"], "maintain", "Admin", ""))):
                with self.subTest(whose=whose, answer=answer):
                    self.snapshot["permissions"][login] = answer
                    self.verdict(self.cli(), 2, f"could not read the permission of {whose}")
            with self.subTest(whose=whose, answer="absent"):
                del self.snapshot["permissions"][login]
                self.verdict(self.cli(), 2, f"could not read the permission of {whose}")
            self.snapshot["permissions"][login] = original

    def test_the_permission_read_asks_github_for_the_account_alone(self):
        # REST collaborators/{login}/permission, through the one boundary. A failed gh, or
        # an answer that is not JSON, is unreadable, showing nothing of gh's; and a login
        # not of GitHub's shape is never put into an endpoint.
        with patch.dict(os.environ, {"GH_TOKEN": "private-fixture-token"}):
            api = queue.GitHub("owner/repository", None)
            answer = json.dumps(permission_answer("someone", "write"))
            with patch.object(queue.subprocess, "run", return_value=subprocess.CompletedProcess(
                    [], 0, answer, "")) as call:
                self.assertTrue(queue.write_access(api, "someone", {}, "a reader"))
            self.assertEqual(call.call_args.args[0], [
                "gh", "api", "--method", "GET",
                "repos/owner/repository/collaborators/someone/permission"])
            for status, out in ((1, answer), (1, "private-fixture-token"),
                                (0, "{private-fixture-token")):
                with self.subTest(status=status, out=out), \
                        patch.object(queue.subprocess, "run", return_value=subprocess.
                                     CompletedProcess([], status, out, "private-fixture-token")):
                    with self.assertRaises(ValueError) as caught:
                        queue.write_access(api, "someone", {}, "a reader")
                    self.assertEqual(str(caught.exception),
                                     "GitHub: could not read the permission of a reader")
            with patch.object(queue.subprocess, "run", side_effect=AssertionError("asked")):
                for login in ("some/../one", "someone?per_page=1", "-someone", None):
                    with self.subTest(login=login), \
                            self.assertRaisesRegex(ValueError, "GitHub: unknown read"):
                        api.read("permissions", login=login)

    def test_an_answer_for_another_account_is_unreadable(self):
        # GitHub's logins ignore case, so Kelvin's answer is kelvin's; another login's, a
        # lookalike's among them, is not, for the editor's read or the author's.
        self.edited_by("kelvin", "admin")
        answered = self.snapshot["permissions"]["kelvin"]["user"]
        for login in ("other", "kelvin-x", "\N{KELVIN SIGN}elvin"):
            with self.subTest(login=login):
                answered["login"] = login
                self.verdict(self.cli(), 2,
                             "could not read the permission of #1's body's last editor")
        answered["login"] = "Kelvin"
        self.verdict(self.cli(), 0, "queue: PASS")
        self.snapshot["permissions"]["fixture"]["user"]["login"] = "other"
        self.verdict(self.cli(), 2, "could not read the permission of #1's author")

    def test_a_login_not_of_github_s_shape_is_unreadable(self):
        # Never put into an endpoint, though an admin's answer is planted for each.
        for login in ("some one", "-someone", "someone-", "some--one", "x" * 40,
                      "../someone", "someone?per_page=1", "some_one", "someone\n"):
            with self.subTest(login=login):
                self.edited_by(login, "admin")
                self.verdict(self.cli(), 2,
                             "could not read the permission of #1's body's last editor")
        self.nodes()[0]["pullRequest"]["editor"] = None
        self.snapshot["pull_requests"]["1"]["user"] = {"login": "fixture/x", "type": "User"}
        self.snapshot["permissions"]["fixture/x"] = permission_answer("fixture/x", "admin")
        self.verdict(self.cli(), 2, "could not read the permission of #1's author")

    def test_a_body_last_edited_by_an_actor_that_is_not_a_user_is_unreadable(self):
        # A bot's edit refuses (above); any other actor GraphQL may name has no permission
        # to read, though a writer's answer stands under its login.
        for typename in ("Mannequin", "Organization", "EnterpriseUserAccount"):
            with self.subTest(typename=typename):
                self.edited_by("someone", typename=typename)
                self.verdict(self.cli(), 2, "#1's body's last editor is not a user")

    def test_each_account_s_permission_is_read_once_a_run(self):
        # Both entries' author and the first's last editor are one account, its login in
        # two cases, as GitHub's logins ignore case: one read, which the second spelling,
        # with no answer of its own, never needs.
        self.edited_by("FIXTURE")
        self.checkout(self.head)
        self.fixture.write_text(json.dumps(self.snapshot), encoding="utf-8")
        read, asked = queue.GitHub.read, []

        def counted(api, kind, *args, **kwargs):
            if kind == "permissions":
                asked.append(kwargs["login"])
            return read(api, kind, *args, **kwargs)

        with patch.object(queue.GitHub, "read", counted), contextlib.chdir(self.repo), \
                contextlib.redirect_stdout(io.StringIO()) as out:
            code = queue.main(["--head", self.head, "--base", self.base,
                               "--repo", "owner/repository", "--github-json", str(self.fixture)])
        self.assertEqual((code, out.getvalue()), (0, "queue: PASS\n"))
        self.assertEqual(asked, ["fixture"])

    def test_a_merged_entry_s_accounts_are_not_read(self):
        # Already on main, judged by its own group: only the queued entries are read.
        pr = self.snapshot["pull_requests"]["1"]
        pr.update(state="closed", merged=True, merge_commit_sha=self.first,
                  user={"login": "former", "type": "User"})
        self.snapshot["main"]["sha"] = self.first
        self.nodes().pop(0)
        self.nodes()[0]["position"] = 1
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
        JUDGE: [QUEUE_TESTS, SAFE_PUSH],
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

    @staticmethod
    def workflow(name):
        with (SCRIPTS.parent / ".github/workflows" / name).open(encoding="utf-8") as source:
            return yaml.safe_load(source)

    # The ifs the step runner reads, each as it is on the event the runner simulates.
    CONDITIONS = {"": lambda event: True,
                  "github.event_name == 'merge_group'": lambda event: event == "merge_group",
                  "github.event_name != 'merge_group'": lambda event: event != "merge_group",
                  "github.event_name == 'pull_request'": lambda event: event == "pull_request"}

    def fixture_tools(self, real_python=False):
        """The folder put first on the PATH of a workflow's steps: gh, FAKE_GH over this
        test's fixture file, logging each call to gh-calls.jsonl beside it; and python3,
        either this test's interpreter or FAKE_PYTHON, which checks pip's install and runs
        nothing else of pip."""
        tools = self.root / ("real-python-tools" if real_python else "tools")
        if not tools.is_dir():
            tools.mkdir()
            (tools / "fake_gh.py").write_text(FAKE_GH, encoding="utf-8")
            python = shlex.quote(sys.executable)
            python_command = f"#!/bin/sh\nexec {python} \"$@\"\n" if real_python \
                else FAKE_PYTHON.format(python=python)
            for name, text in (
                    ("gh", f"#!/bin/sh\nexec {python} -I {shlex.quote(str(tools / 'fake_gh.py'))} "
                           f"{shlex.quote(str(self.fixture))} "
                           f"{shlex.quote(str(self.root / 'gh-calls.jsonl'))} \"$@\"\n"),
                    ("python3", python_command)):
                (tools / name).write_text(text, encoding="utf-8")
                (tools / name).chmod(0o755)
        return tools

    def run_job(self, job, event="merge_group", head=None, base=None, workflow=None,
                steps=None, runner=None, real_python=False):
        """Run the steps of the queue judge's `job` in order, from main's copy of
        queue-judge.yml or a planted `workflow`, as GitHub's runner would on `event`, in
        the checkout as the test left it. The job may have no if of its own, since a
        skipped required job counts as passed. Each step's if is read against the event
        (CONDITIONS; any other fails the test): a step whose if is false is skipped, as
        GitHub skips it, but on a merge group every step must run, so that no plant passes
        by running a step GitHub would skip. Each expression of a step's environment or
        working directory is given its value on the event, and any other fails the test.
        The checkout and Python's setup are the fixture's own; gh and pip are FAKE_GH and
        FAKE_PYTHON (fixture_tools), and the snapshot is written for gh first. With
        `steps`, only the steps so named run, the test having set up what those before
        them leave. As on GitHub, the first step that fails ends the job. The result's
        args are the labels of the steps that ran, its status the failing step's or 0,
        and its output theirs. A `head` or `base` of "" is an event that gives none."""
        head = self.head if head is None else head
        base = self.base if base is None else base
        spec = (workflow or self.workflow("queue-judge.yml"))["jobs"][job]
        self.assertNotIn("if", spec, f"{job}: a skipped required job counts as passed")
        runner = runner or self.root / f"runner-{job}"
        runner.mkdir(exist_ok=True)
        group = event == "merge_group"
        values = {"github.event_name": event, "github.token": "fixture-workflow-secret",
                  "github.repository": "owner/repository", "vars.STOICHEIA_REVERT_BOT": BOT,
                  "runner.temp": str(runner),
                  "github.event.merge_group.head_sha": head if group else "",
                  "github.event.merge_group.base_sha": base if group else ""}

        def evaluated(text):
            def value(match):
                self.assertIn(match.group(1), values, f"{job}: an expression the runner "
                              "does not know")
                return values[match.group(1)]
            return re.sub(r"\$\{\{\s*(.*?)\s*\}\}", value, str(text))

        self.fixture.write_text(json.dumps(self.snapshot), encoding="utf-8")
        common = dict(os.environ, RUNNER_TEMP=str(runner), GITHUB_EVENT_NAME=event,
                      GITHUB_WORKSPACE=str(self.repo),
                      PATH=f"{self.fixture_tools(real_python)}{os.pathsep}{os.environ['PATH']}")
        if real_python:
            # The requirements are empty and there is no index, so nothing is installed: let
            # pip run outside a virtual environment, as a hosted runner's Python does.
            common.update(PIP_NO_INDEX="1", PIP_DISABLE_PIP_VERSION_CHECK="1",
                          PIP_BREAK_SYSTEM_PACKAGES="1")
        ran, out, err, status = [], [], [], 0
        for number, step in enumerate(spec["steps"], 1):
            label = step.get("name") or step.get("uses") or f"step {number}"
            condition = str(step.get("if", "")).strip()
            if condition.startswith("${{") and condition.endswith("}}"):
                condition = condition[3:-2].strip()
            self.assertIn(condition, self.CONDITIONS, f"{label}: an if the runner does not read")
            if not self.CONDITIONS[condition](event):
                self.assertFalse(group, f"{label}: skipped on a merge group, where every step "
                                 "runs")
                continue
            if steps is not None and label not in steps:
                continue
            ran.append(label)
            if "uses" in step:
                self.assertIn(step["uses"], ("actions/checkout@v5", "actions/setup-python@v5"),
                              label)
                continue
            env = dict(common, **{key: evaluated(text)
                                  for key, text in (step.get("env") or {}).items()})
            where = evaluated(step.get("working-directory", self.repo))
            result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", step["run"]],
                                    cwd=where, env=env, capture_output=True, text=True)
            out.append(result.stdout)
            err.append(result.stderr)
            if result.returncode:
                status = result.returncode
                break
        return subprocess.CompletedProcess(ran, status, "".join(out), "".join(err))

    def queue_job(self, head, base):
        """Run the queue judge's queue-integrity job on a merge group of `head` and `base`,
        checked out."""
        self.checkout(head)
        return self.run_job("queue-integrity", head=head, base=base)

    def test_queue_job_installs_test_dependency_only_for_offline_tests(self):
        # The offline cases are CI's queue-tests: it installs their parser and runs them on
        # every event, a merge group's among them, with no if. The judge's queue-integrity
        # installs nothing, so the Python that runs the judge holds nothing a group names,
        # and its judge runs on a merge group alone.
        tests = self.workflow("ci.yml")["jobs"]["queue-tests"]
        install = [step for step in tests["steps"] if step.get("name") ==
                   "Install the queue tests' pinned YAML parser"]
        offline = [step for step in tests["steps"] if step.get("name") ==
                   "Check the queue and train checks, and automatic reverts, case by case"]
        self.assertEqual(len(install), 1)
        self.assertEqual(len(offline), 1)
        for spec in (tests, *tests["steps"]):
            self.assertNotIn("if", spec)
        steps = self.workflow("queue-judge.yml")["jobs"]["queue-integrity"]["steps"]
        judge = [step for step in steps if step.get("name") ==
                 "Check the group with main's copy of check_queue.py"]
        self.assertEqual(len(judge), 1)
        self.assertEqual(judge[0].get("if"), "github.event_name == 'merge_group'")
        self.assertEqual([step for step in steps if "pip" in str(step.get("run", ""))], [])

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

    # A base judge that records how each step calls it, and the tokens it holds then;
    # for --acceptance-run it writes the verdicts, as main's does.
    RECORDING_JUDGE = (
        "import json, os, sys\n"
        "log = os.path.join(os.environ['RUNNER_TEMP'], 'judge-calls.jsonl')\n"
        "tokens = sorted(key for key in os.environ if 'TOKEN' in key.upper())\n"
        "with open(log, 'a', encoding='utf-8') as calls:\n"
        "    calls.write(json.dumps([sys.argv[1:], tokens]) + '\\n')\n"
        "if '--acceptance-run' in sys.argv:\n"
        "    out = sys.argv[sys.argv.index('--out') + 1]\n"
        "    os.makedirs(out)\n"
        "    with open(os.path.join(out, 'verdicts.json'), 'w', encoding='utf-8') as file:\n"
        "        file.write('{}')\n")

    def recording_group(self):
        """A base whose judge is RECORDING_JUDGE, with main's pin of the tests' parser, and
        a head whose judge would refuse were it run."""
        base = self.make([self.base], {
            "scripts/check_queue.py": self.RECORDING_JUDGE,
            "scripts/requirements-test_safe_push.txt": "pyyaml==0\n"})
        head = self.make([base], {"scripts/check_queue.py": "raise SystemExit('group ran')\n"})
        return base, head

    def recorded(self, runner):
        return [json.loads(line) for line in
                (runner / "judge-calls.jsonl").read_text(encoding="utf-8").splitlines()]

    def test_gaps_job_runs_the_tests_in_a_step_that_holds_no_token(self):
        # The tests are the group's own code, and on Linux a process can read its parent's
        # environment: the steps that hold the token read acceptance's verdicts and choose
        # the tests, and run none, and no later step declares a token. The base's judge
        # records how each step of the whole job, run on a merge group, calls it.
        steps = self.workflow("queue-judge.yml")["jobs"]["queue-gaps"]["steps"]
        choose = [step.get("name") for step in steps].index("Choose the tests of what is new")
        self.assertIn("--plan", steps[choose]["run"])
        self.assertNotIn("--run-plan", steps[choose]["run"])
        for step in steps[choose + 1:]:
            for key, text in (step.get("env") or {}).items():
                self.assertNotIn("TOKEN", key.upper(), step)
                self.assertNotRegex(str(text), r"(?i)token|secrets\.", step)
        base, head = self.recording_group()
        self.checkout(head)
        result = self.run_job("queue-gaps", head=head, base=base)
        self.verdict(result, 0, "fixture pip: would install")
        self.assertEqual(len(result.args), len(steps))
        runner = self.root / "runner-queue-gaps"
        plan = str(runner / "gaps-plan.json")
        self.assertEqual(self.recorded(runner), [
            [["--acceptance-run", "--head", head, "--repo", "owner/repository",
              "--ci-workflow", "ci.yml", "--out", str(runner / "acceptance")], ["GH_TOKEN"]],
            [["--gaps", "--head", head, "--base", base, "--repo", "owner/repository",
              "--plan", plan], ["GH_TOKEN"]],
            [["--run-plan", plan, "--head", head], []]])

    def test_python_modules_run_isolated_outside_the_checkout(self):
        requirement = "scripts/requirements-test_safe_push.txt"
        head = self.make([self.base], {requirement: ""})
        self.checkout(head)
        hostile = self.repo / "pip"
        hostile.mkdir()
        (hostile / "__init__.py").write_text("", encoding="utf-8")
        marker = self.repo / "hostile-pip-ran"
        (hostile / "__main__.py").write_text(
            "from pathlib import Path\n"
            f"Path({str(marker)!r}).write_text('hostile pip ran', encoding='utf-8')\n"
            "print('hostile pip ran')\n", encoding="utf-8")
        cases = (
            ("check", "Install the pinned YAML parser the lane-condition check reads the "
             "workflows with", self.workflow("ci.yml")),
            ("queue-tests", "Install the queue tests' pinned YAML parser", self.workflow("ci.yml")),
            ("queue-gaps", "Install the tests' pinned YAML parser, main's pin",
             self.workflow("queue-judge.yml")))
        for job, step, workflow in cases:
            with self.subTest(job=job):
                runner = self.root / f"isolated-{job}"
                if job == "queue-gaps":
                    (runner / "judge").mkdir(parents=True)
                    (runner / "judge" / Path(requirement).name).write_text("", encoding="utf-8")
                result = self.run_job(job, head=head, workflow=workflow, steps={step},
                                      runner=runner, real_python=True)
                self.verdict(result, 0)
                self.assertFalse(marker.exists())

        workflow = copy.deepcopy(self.workflow("ci.yml"))
        step = next(step for step in workflow["jobs"]["queue-tests"]["steps"]
                    if step.get("name") == "Install the queue tests' pinned YAML parser")
        step.pop("working-directory")
        step["run"] = step["run"].replace("python3 -I -m", "python3 -m")
        result = self.run_job("queue-tests", head=head, workflow=workflow,
                              steps={step["name"]}, runner=self.root / "unsafe-module",
                              real_python=True)
        self.verdict(result, 0, "hostile pip ran")
        self.assertEqual(marker.read_text(encoding="utf-8"), "hostile pip ran")

    def test_every_python_module_line_of_the_workflows_runs_isolated(self):
        # python3 -m puts the working directory first on the import path, so a pip/ folder
        # in a group's checkout would run in pip's place. The census of every such line in
        # the workflows (the test above runs three of them against a hostile module).
        modules = []
        for name in ("ci.yml", "post-merge.yml", "queue-judge.yml"):
            for job, value in self.workflow(name)["jobs"].items():
                for step in value.get("steps", []):
                    for line in str(step.get("run", "")).splitlines():
                        if re.search(r"\bpython3?(?:\s+-\S+)*\s+-m\b", line):
                            modules.append((name, job, step.get("working-directory"), line))
        # The check job installs the parser the lane-condition check reads the workflows
        # with (checks/24-lane-condition.toml, #346).
        self.assertEqual(sorted(job for _, job, _, _ in modules),
                         ["check", "queue-gaps", "queue-tests"])
        for name, job, directory, line in modules:
            with self.subTest(job=job):
                self.assertEqual(directory, "${{ runner.temp }}")
                self.assertRegex(line, r"^python3 -I -m pip install -r \"\$[A-Z_]+/\S+\.txt\"$")

    def test_queue_timeouts_are_pinned(self):
        # The design's section 4. queue-gaps starts with the group and waits for
        # acceptance (--acceptance-run), so it has no cutoff of its own earlier than the
        # queue's status check timeout, 150 minutes from the group's start: the waiter's
        # deadline and the job's limit are that timeout too, and the job starts after the
        # group does. Acceptance's limit and a budget of 75 minutes for the gap tests leave
        # 15 for runners and the handover after acceptance ends, which is serial (a poll of
        # a minute, then the reads and the download, each allowed 60 seconds): a group that
        # ends near the timeout may be ejected at it (AcceptanceRunTests, the deadline
        # passed during the handover). The two are budgets, which no job holds:
        # queue-gaps' own limit is the 150. The poll is a minute for the token's limit of
        # about 1,000 requests an hour; the revert's wait keeps RUN_POLL. To be measured
        # again on the queue's trial (WORKFLOW, "Turning it on").
        ci, judge = self.workflow("ci.yml")["jobs"], self.workflow("queue-judge.yml")["jobs"]
        status, gap_tests_budget, runners_and_handover_budget = 150, 75, 15
        self.assertEqual(ci["acceptance"]["timeout-minutes"], 60)
        self.assertEqual(ci["acceptance"]["timeout-minutes"] + gap_tests_budget
                         + runners_and_handover_budget, status)
        self.assertEqual(queue.ACCEPTANCE_WAIT, status * 60)
        self.assertEqual(judge["queue-gaps"]["timeout-minutes"], status)
        self.assertNotIn("needs", judge["queue-gaps"])
        self.assertEqual(queue.ACCEPTANCE_POLL, 60)
        self.assertEqual(queue.RUN_POLL, 15)
        self.assertEqual(judge["queue-integrity"]["timeout-minutes"], 20)
        guide = " ".join((SCRIPTS.parent / "docs/WORKFLOW.md").read_text(
            encoding="utf-8").split())
        self.assertIn(f"set the queue's status check timeout to {status} minutes", guide)
        # --merge follows an entry through one rebuild behind a group that fails.
        self.assertEqual(queue.safe_push.QUEUE_TIMEOUT, 2 * 150 * 60)

    # The planted cases of the queue judge's design (MQ3-reqwf, 27 October 2026, section
    # 7), each naming the guard it holds; undone, its test turns red. Most run main's file
    # step by step (run_job); the body-edit plants run this tree's check_queue.py by its
    # command line, and one of them main's file too. Those of main's own file (a job made
    # conditional, a merge-group step skipped, the judge step removed, cancel-in-progress
    # added, merge_group dropped from `on:`) and CI's queue-tests dropped are the
    # contracts': in scripts/test_safe_push.py,
    # Units.test_the_queue_judge_workflow_refuses_its_plants. That GitHub runs main's copy,
    # binds the rule to the file and ignores a job of the same name elsewhere is for the
    # live trial alone.

    def real_main(self):
        """Main with scripts/ as this repository holds it but for its tests and its harness,
        which stays the fixture's: the trains built now name this commit as their
        pre-flight's base and harness, whose CHECKS harness_check_names reads by ast. tests/
        holds a stand-in for each test GITHUB_TESTS names, printing that it ran. The queue
        is emptied for the trains to come."""
        scripts = {f"scripts/{path.relative_to(SCRIPTS).as_posix()}":
                   path.read_text(encoding="utf-8")
                   for path in sorted(SCRIPTS.rglob("*"))
                   if path.is_file() and "__pycache__" not in path.parts
                   and not path.name.startswith("test_") and path != SCRIPTS / "safe_push.py"}
        stand_ins = {path: f"print('{path} ran')\n" for path in (
            "tests/test_check_queue.py", "tests/test_auto_revert.py",
            "tests/test_release_gate.py")}
        self.base = self.make([self.base], {**scripts, **stand_ins})
        self.snapshot["main"]["sha"] = self.base
        self.nodes().clear()

    def real_harness(self):
        """Main's next commit, which puts in this repository's harness, scripts/safe_push.py,
        for the judge to import beside it; the group is built on it."""
        self.base = self.make([self.base], {
            "scripts/safe_push.py": (SCRIPTS / "safe_push.py").read_text(encoding="utf-8")})
        self.snapshot["main"]["sha"] = self.base

    def sound_group(self, changes, new="None.", real_preflight=False):
        """A group of main as it is (real_main, real_harness), the first train making
        `changes`, the second a change elsewhere, whose CI run's acceptance job passed;
        checked out. Its trains are pre-flighted by the fixture's harness or, with
        `real_preflight`, by this repository's, which main then holds before they are
        built."""
        self.real_main()
        if real_preflight:
            self.real_harness()
        one = self.train(1, changes, new=new)
        two = self.train(2, {SECOND: "The second train's reviewed line.\n"})
        if not real_preflight:
            self.real_harness()
        group = self.merge(self.merge(self.base, one, 1), two, 2)
        self.snapshot.update(acceptance_answers(group))
        self.checkout(group)
        return group

    def labels(self, job):
        return [step.get("name") or step.get("uses")
                for step in self.workflow("queue-judge.yml")["jobs"][job]["steps"]]

    def test_on_a_pull_request_each_judge_job_passes_at_once(self):
        # Neither job has an if of its own, since a skipped required job counts as passed:
        # on a pull request each runs its first step alone, which says there is nothing to
        # judge, and passes; on any other event but a merge group that step fails.
        for job in JUDGE_JOBS:
            with self.subTest(job=job):
                result = self.run_job(job, event="pull_request")
                self.verdict(result, 0, "A pull request: nothing to judge here")
                self.assertEqual(result.args, self.labels(job)[:1])
                result = self.run_job(job, event="push", runner=self.root / f"push-{job}")
                self.verdict(result, 1, "A push event: the queue's judge runs on pull "
                             "requests and merge groups only")

    def test_the_step_runner_runs_every_step_on_a_group_as_github_would(self):
        # The runner's own plants: a merge-group step made to run on pull requests alone,
        # a step whose if the runner does not read, and a job given an if of its own each
        # fail the run, so that no plant passes by running a step GitHub would skip.
        for change, refusal in (
                (lambda job: job["steps"][3].update({"if": "github.event_name == 'pull_request'"}),
                 "skipped on a merge group, where every step runs"),
                (lambda job: job["steps"][3].update({"if": "always()"}),
                 "an if the runner does not read"),
                (lambda job: job.update({"if": "github.event_name == 'merge_group'"}),
                 "a skipped required job counts as passed")):
            with self.subTest(refusal=refusal):
                planted = self.workflow("queue-judge.yml")
                change(planted["jobs"]["queue-integrity"])
                with self.assertRaisesRegex(AssertionError, re.escape(refusal)):
                    self.run_job("queue-integrity", workflow=planted)

    def test_plant_a_group_whose_own_judge_passes_everything_is_judged_by_main_s(self):
        # A group whose second train overwrites the first's reviewed line, rule (a), and
        # whose own scripts/check_queue.py passes everything, called by its own copy of
        # queue-judge.yml, which takes scripts/ from the checkout. Main's queue-integrity,
        # run as the runner would on the group, refuses it. Guard: the judge step's
        # `git archive "$GROUP_BASE:scripts"`, main's scripts from the group's base; taken
        # from the checkout instead, the plant passes.
        self.real_main()
        one = self.train(1, {TEXT: "The first train's reviewed line.\n"})
        own = (SCRIPTS.parent / JUDGE).read_text(encoding="utf-8").replace(
            '"$GROUP_BASE:scripts"', "HEAD:scripts")
        two = self.train(2, {TEXT: "A later train overwrote the reviewed line.\n",
                             "scripts/check_queue.py": "print('queue: PASS')\n", JUDGE: own},
                         start=one)
        self.real_harness()
        group = self.merge(self.merge(self.base, one, 1), two, 2)
        self.checkout(group)
        self.verdict(self.run_job("queue-integrity", head=group), 1,
                     f"queue: REFUSED: not overwriting: #1 changed lines were overwritten: {TEXT}")

    # A group's own check_queue.py that chooses no tests, writes the verdicts it is asked
    # for, and passes everything.
    CHOOSES_NOTHING = (
        "import json, os, sys\n"
        "print('group judge ran')\n"
        "args = sys.argv[1:]\n"
        "if '--acceptance-run' in args:\n"
        "    out = args[args.index('--out') + 1]\n"
        "    os.makedirs(out, exist_ok=True)\n"
        "    with open(os.path.join(out, 'verdicts.json'), 'w', encoding='utf-8') as file:\n"
        "        file.write('{}')\n"
        "if '--plan' in args:\n"
        "    with open(args[args.index('--plan') + 1], 'w', encoding='utf-8') as plan:\n"
        "        json.dump({'head': args[args.index('--head') + 1], 'commands': []}, plan)\n"
        "print('queue: PASS')\n")

    def test_plant_a_group_whose_own_gap_choice_chooses_nothing_is_judged_by_main_s(self):
        # A valid group whose train changes a check, weakens the check's test to succeed,
        # and changes its own check_queue.py to choose no tests. Main's queue-gaps, run as
        # the runner would, chooses the check's test by main's --gaps and runs it. That it
        # passes proves nothing of the weakened test: its adequacy is the protected path's
        # security review's (WORKFLOW, section 10). Guards: the first judging step's
        # `git archive "$GROUP_BASE:scripts"`, main's scripts for it and the steps after
        # it; and gap_commands, which chooses the test. Undo either: the test is not run.
        changes = {CHECK: "print('changed check')\n", TEST: "print('weakened sample test ran')\n",
                   "scripts/check_queue.py": self.CHOOSES_NOTHING}
        group = self.sound_group(changes, "\n".join(f"- check: {path}" for path in changes))
        output = self.verdict(self.run_job("queue-gaps", head=group), 0,
                              f"gaps: chosen: python3 -I {TEST}", f"gaps: python3 -I {TEST}\n",
                              "weakened sample test ran", "queue: PASS")
        self.assertNotIn("group judge ran", output)

    def test_plant_a_group_that_adds_a_workflow_with_the_judge_s_job_is_refused_by_main_s(self):
        # A group whose train adds a workflow of its own with a job queue-integrity, which
        # passes on every merge group, as if it were the judge. Main's queue-gaps, run as
        # the runner would, refuses the group by main's --gaps. Guard: gap_commands'
        # refusal of a path under .github/ to which GITHUB_TESTS maps no tests; undone, the
        # group is not refused by it. That GitHub's rule binds the judge's own file, so that
        # a job of the same name elsewhere satisfies nothing, is the live trial's to show.
        impostor = ".github/workflows/impostor.yml"
        group = self.sound_group({impostor: (
            "name: Queue judge\non:\n  merge_group:\njobs:\n  queue-integrity:\n"
            "    runs-on: ubuntu-latest\n    steps:\n      - run: echo 'queue: PASS'\n")},
            f"- check: {impostor}")
        self.verdict(self.run_job("queue-gaps", head=group), 1,
                     f"queue: REFUSED: gaps: no tests are mapped to {impostor}")

    def test_plant_a_body_edited_after_its_pre_flight_is_refused_by_main_s_judge(self):
        # The body edited after the pre-flight, the head unchanged: the judge refuses each
        # edit by its own predicate of preflight, whose refusal is named here, so that
        # undoing any one of them turns its case red. Each runs this tree's check_queue.py
        # by its command line; the block hidden runs main's file too, its queue-integrity
        # step as the runner runs it, last.
        original = self.body()
        blob = self.git("rev-parse", f"{self.base}:scripts/safe_push.py").strip()
        other = self.git("rev-parse", f"{self.base}:{TEXT}").strip()
        block = queue.PREFLIGHT.search(original).group()
        name = queue.safe_push.CHECKS[0][0]
        for label, body, refusal in (
                # Guard: the harness blob's --disambiguate match with the recorded harness
                # commit's safe_push.py.
                ("the harness blob changed", original.replace(blob[:12], other[:12]),
                 "harness blob is not the recorded harness commit's safe_push.py"),
                # Guard: preflight_steps' passing line for each check of the harness.
                ("a check line removed", original.replace(f"| 4. {name} | ok | 1.0 |\n", ""),
                 "steps must run the full checks"),
                # Guard: the visible witness, the sentinel that must stand where the block did.
                ("the block hidden", original.replace(block, f"<!--\n{block}\n-->"),
                 "block is hidden by code or HTML")):
            with self.subTest(label):
                self.set_body(body)
                self.verdict(self.cli(), 1, f"queue: REFUSED: pre-flight: {refusal}")
        # A light pre-flight claimed for an R3 diff, a change to a check. Guard:
        # light_preflight's class of the change by main's scripts/risk.py.
        group = self.light_group({CHECK: "print('changed check')\n"}, "R1",
                                 new=f"- check: {CHECK}")
        self.verdict(self.cli(head=group), 1, "queue: REFUSED: pre-flight: left the full checks "
                     "to CI, but the class by main's scripts/risk.py is R3 (")
        group = self.sound_group({TEXT: "The first train's reviewed line.\n"})
        block = queue.PREFLIGHT.search(self.body()).group()
        self.set_body(self.body().replace(block, f"<!--\n{block}\n-->"))
        self.verdict(self.run_job("queue-integrity", head=group), 1,
                     "queue: REFUSED: pre-flight: block is hidden by code or HTML")

    def test_plant_a_body_edited_between_github_s_two_readings_is_unreadable(self):
        # The body edited between the queue's answer and the pull request's, which the
        # verdict reads. Guard: chain's comparison of the two bodies; undone, the later
        # body, a passing one, is judged alone and passes.
        self.snapshot["pull_requests"]["1"]["body"] = self.body() + "\nA later edit.\n"
        self.verdict(self.cli(), 2, "#1's body differs between the queue's answer and its "
                     "pull request's")

    def test_a_consistent_forgery_passes(self):
        # Rule (b)'s second requirement, the authenticity of the pre-flight's evidence, is
        # held by write access to the pull request until #574, not by the judge (WORKFLOW,
        # section 10; the owner's decision of 28 October 2026): the judge checks the block
        # for consistency with the repository, not that a pre-flight ran. Each block here
        # is typed, as anyone who can edit the body could type it, for a head no pre-flight
        # ever ran on, with its head, base, harness and blob right and every check "ok",
        # and main's judge passes it. No guard of the judge holds this: the test says so,
        # so that what the judge does not check stays in sight, and it is to refuse once
        # the judge verifies evidence CI signs (#574).
        blob = self.git("rev-parse", f"{self.base}:scripts/safe_push.py").strip()
        rows = "".join(f"| 4. {name} | ok | 1.0 |\n"
                       for name, _ in (*queue.safe_push.CHECKS, *queue.safe_push.NEGATIVE))
        for number, head in ((1, self.one), (2, self.two)):
            typed = (f"<!-- safe_push:preflight begin sha={head} base={self.base} "
                     f"harness={self.base} -->\n"
                     f"Pre-flight of `{head[:12]}` against origin/main `{self.base[:12]}`, by "
                     f"origin/main's `scripts/safe_push.py` (blob `{blob[:12]}`).\n\n"
                     "Verdict: PASS.\n\n| Step | Outcome | Seconds |\n|---|---|---|\n"
                     f"{rows}<!-- safe_push:preflight end -->")
            self.set_body(queue.PREFLIGHT.sub(lambda _: typed, self.body(number)), number)
        self.verdict(self.cli(), 0, "queue: PASS")

    def test_plant_a_checkout_that_is_not_the_group_s_head_fails_each_judging_step(self):
        # Whichever copy of the file runs, each step that runs main's judge first compares
        # the checkout with the group's head, and fails before the judge runs. Guard: each
        # step's `test "$(git rev-parse HEAD)" = "$GROUP_HEAD"`; undone, the base's judge
        # runs on another tree, and records the call. The two steps after the extraction
        # find the base's scripts as it leaves them.
        base, head = self.recording_group()
        self.checkout(base)
        for number, (job, step, extracted) in enumerate((
                ("queue-integrity", "Check the group with main's copy of check_queue.py", False),
                ("queue-gaps", "Read acceptance's verdicts from the group's CI run with main's "
                               "copy of check_queue.py", False),
                ("queue-gaps", "Choose the tests of what is new", True),
                ("queue-gaps", "Run the tests of what is new", True))):
            with self.subTest(step=step):
                runner = self.root / f"wrong-checkout-{number}"
                if extracted:
                    (runner / "judge").mkdir(parents=True)
                    archive = subprocess.run(["git", "archive", "--format=tar", f"{base}:scripts"],
                                             cwd=self.repo, capture_output=True, check=True)
                    subprocess.run(["tar", "-xf", "-", "-C", str(runner / "judge")],
                                   input=archive.stdout, check=True)
                result = self.run_job(job, head=head, base=base, steps={step}, runner=runner)
                self.assertEqual(result.args, [step])
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertFalse((runner / "judge-calls.jsonl").exists())

    def test_plant_an_event_without_a_head_or_base_fails_each_first_judging_step(self):
        # A merge group's event gives both shas. Were one empty, each step that first reads
        # them fails at its first lines, before Git reads a revision made of it: with no
        # base, the check of ":scripts/check_queue.py" reads the group's own file, in the
        # index, and passes, and only the archive after it fails. Guard: each step's
        # `test -n "$GROUP_HEAD"` and `test -n "$GROUP_BASE"`; undone, the base's case
        # reaches Git. The head's case is held by the comparison of the checkout too, so
        # only the contracts' digest tells its guard undone.
        base, head = self.recording_group()
        self.checkout(head)
        for number, (job, step) in enumerate((
                ("queue-integrity", "Check the group with main's copy of check_queue.py"),
                ("queue-gaps", "Read acceptance's verdicts from the group's CI run with main's "
                               "copy of check_queue.py"))):
            for given in ({"head": head, "base": ""}, {"head": "", "base": base}):
                with self.subTest(step=step, empty=[k for k, v in given.items() if not v]):
                    runner = self.root / f"no-sha-{number}-{bool(given['head'])}"
                    result = self.run_job(job, steps={step}, runner=runner, **given)
                    self.assertEqual(result.args, [step])
                    self.assertEqual((result.returncode, result.stdout, result.stderr),
                                     (1, "", ""))
                    self.assertFalse((runner / "judge-calls.jsonl").exists())

    def test_control_a_sound_group_passes_every_step_of_both_jobs(self):
        # The controls: a sound group, judged by main's copy of each job, runs every step
        # on a merge group, and each exits 0.
        group = self.sound_group({TEXT: "The first train's reviewed line.\n"})
        for job in JUDGE_JOBS:
            with self.subTest(job=job):
                result = self.run_job(job, head=group)
                self.verdict(result, 0, "queue: PASS")
                self.assertEqual(result.args, self.labels(job))

    def test_control_a_sound_group_pre_flighted_by_main_s_own_harness_passes(self):
        # The same control, its trains pre-flighted by this repository's
        # scripts/safe_push.py, which names a check by EMPTY_CHECK, a name bound to a
        # string: main's judge reads that harness's checks (harness_check_names, through
        # harness_value) and passes the group. Undo that reading and this control turns red.
        group = self.sound_group({TEXT: "The first train's reviewed line.\n"},
                                 real_preflight=True)
        self.assertEqual(self.git("show", f"{self.base}:scripts/safe_push.py"),
                         (SCRIPTS / "safe_push.py").read_text(encoding="utf-8"))
        self.assertIn(f"harness={self.base}", self.body())
        for job in JUDGE_JOBS:
            with self.subTest(job=job):
                result = self.run_job(job, head=group)
                self.verdict(result, 0, "queue: PASS")
                self.assertEqual(result.args, self.labels(job))

    def test_control_a_sound_group_that_changes_the_judge_is_judged_by_main_s_copy(self):
        # A sound group whose train changes queue-judge.yml itself, its own copy one that
        # could judge nothing: main's copy judges it, every step exits 0, and main's
        # GITHUB_TESTS chooses the tests that read the file.
        group = self.sound_group({JUDGE: "name: A copy that judges nothing\non: push\njobs: {}\n"},
                                 f"- check: {JUDGE}")
        for job in JUDGE_JOBS:
            with self.subTest(job=job):
                result = self.run_job(job, head=group)
                self.verdict(result, 0, "queue: PASS")
                self.assertEqual(result.args, self.labels(job))
        self.assertIn("tests/test_check_queue.py ran", result.stdout)
        self.assertIn("safe push test ran", result.stdout)

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

    def test_working_edits_to_readme_prose_refuse_and_to_a_body_do_not(self):
        # #578: README.md is generated only between its markers, so a working-tree edit of
        # its prose is a source change; one inside a scope body is render's, which the
        # render freshness check catches.
        readme = "Prose by hand.\n<!-- scope:I -->\nRow.\n<!-- /scope:I -->\n"
        self.base = self.make([self.base], {"README.md": readme})
        self.snapshot["main"]["sha"] = self.base
        self.nodes().clear()
        group = self.merge(self.base, self.train(1, {TEXT: "A reviewed line.\n"}), 1)
        for old, new, code, message in (
                ("Prose by hand.", "Prose, edited.", 1, "the part of README.md written by hand"),
                ("Row.", "Row, regenerated.", 0, "queue: PASS")):
            with self.subTest(new=new):
                self.checkout(group)
                (self.repo / "README.md").write_text(readme.replace(old, new), encoding="utf-8")
                self.verdict(self.cli(head=group, prepare=False), code, message)

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


class AcceptanceRunTests(unittest.TestCase):
    """--acceptance-run, the design's section 4: each case through acceptance_run, GitHub
    answering each read in turn and a clock that sleeping moves on, and a slow read where
    a test says so, or through the command line with a fixture, whose zip is in base64.
    Each test names the predicate of the four steps it holds."""

    HEAD = "0123456789abcdef" * 2 + "01234567"

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.enterContext(patch.dict(os.environ, fixture_environment(), clear=True))
        answers = acceptance_answers(self.HEAD)
        self.sound = {"ci_runs": answers["ci_runs"], "runs": answers["runs"][str(RUN)],
                      "jobs": answers["jobs"][str(RUN)],
                      "artifacts": answers["artifacts"][str(RUN)],
                      "artifact_zips": KEPT_REPORTS}

    def waited(self, took=None, **changes):
        """acceptance_run on HEAD, GitHub answering each kind at each of its reads in turn,
        the last answer repeating: the sound answers, but for `changes`, each a list. Each
        read of a kind `took` names takes that many seconds of the clock. The verdicts or
        the error, the kinds read in order, and each sleep."""
        answers = {kind: [answer] for kind, answer in self.sound.items()}
        answers.update(changes)
        reads, slept, now = [], [], [0.0]
        test = self

        class Reads:
            repo = "owner/repository"

            def read(self, kind, number=None, workflow=None, head=None):
                reads.append(kind)
                if kind == "ci_runs":
                    test.assertEqual((number, workflow, head), (None, "ci.yml", test.HEAD))
                else:
                    test.assertEqual(number, ARTIFACT if kind == "artifact_zips" else RUN)
                given = answers[kind]
                now[0] += (took or {}).get(kind, 0)
                return copy.deepcopy(given[min(reads.count(kind), len(given)) - 1])

        def sleep(seconds):
            slept.append(seconds)
            now[0] += seconds

        try:
            with contextlib.redirect_stdout(io.StringIO()):
                found = queue.acceptance_run(Reads(), self.HEAD, "ci.yml", sleep=sleep,
                                             clock=lambda: now[0])
        except (queue.Refused, ValueError) as error:
            found = error
        return found, reads, slept

    def run_answer(self, **change):
        return dict(self.sound["ci_runs"]["workflow_runs"][0], **change)

    def job(self, **change):
        return dict(self.sound["jobs"]["jobs"][1], **change)

    def artifact(self, **change):
        return dict(self.sound["artifacts"]["artifacts"][0], **change)

    @staticmethod
    def listing(key, *items):
        return {"total_count": len(items), key: list(items)}

    def other_job(self):
        return self.sound["jobs"]["jobs"][0]

    def refused(self, found, message):
        self.assertIsInstance(found, queue.Refused, found)
        self.assertIn(message, str(found))

    def unreadable(self, found, message):
        self.assertIsInstance(found, ValueError, found)
        self.assertIn(message, str(found))

    RUNNING = {"status": "in_progress", "conclusion": None}
    SOUND_READS = ["ci_runs", "jobs", "artifacts", "artifact_zips", "runs", "jobs", "artifacts"]

    def test_a_passed_acceptance_gives_its_verdicts(self):
        # The control: one run, its acceptance job passed, the one artifact it made, read
        # and read again; in the ratchet, and with the full gate, which keeps no main's.
        found, reads, slept = self.waited()
        self.assertEqual((found, reads, slept), (VERDICTS, self.SOUND_READS, []))
        full = artifact_zip([("report.md", b"# Acceptance\n"), ("verdicts.json", VERDICTS)])
        self.assertEqual(self.waited(artifact_zips=[full])[0], VERDICTS)

    def test_a_run_not_yet_begun_is_waited_for(self):
        # Step 1's wait: read again every ACCEPTANCE_POLL seconds until the run is listed.
        found, reads, slept = self.waited(ci_runs=[self.listing("workflow_runs")] * 2
                                          + [self.sound["ci_runs"]])
        self.assertEqual((found, reads.count("ci_runs"), slept), (VERDICTS, 3, [60, 60]))

    def test_no_run_by_the_deadline_refuses(self):
        # Step 1's deadline, ACCEPTANCE_WAIT, the queue's status check timeout.
        found, reads, slept = self.waited(ci_runs=[self.listing("workflow_runs")])
        self.refused(found, "no run of ci.yml for the group's head had begun after 150 minutes")
        self.assertEqual((reads, slept), (["ci_runs"] * 151, [60] * 150))

    def test_a_job_and_an_artifact_not_yet_there_are_waited_for(self):
        # Step 2's and step 3's waits: no acceptance job listed while the run goes on, then
        # one in progress, then passed; no artifact listed, then one.
        found, reads, slept = self.waited(
            jobs=[self.listing("jobs", self.other_job()),
                  self.listing("jobs", self.other_job(), self.job(**self.RUNNING)),
                  self.sound["jobs"]],
            artifacts=[self.listing("artifacts"), self.sound["artifacts"]])
        self.assertEqual(found, VERDICTS)
        self.assertEqual(reads, ["ci_runs", "jobs", "runs", "jobs", "jobs", "artifacts",
                                 "artifacts", "artifact_zips", "runs", "jobs", "artifacts"])
        self.assertEqual(slept, [60, 60, 60])

    def test_a_deadline_passed_during_the_handover_refuses(self):
        # The design's section 4, "Time", with the injected clock: acceptance ends two
        # polls before the deadline, and the reads after it are slow, 55 seconds each of
        # the reader's 60 (the artifacts, the zip, the run, the artifacts again; the jobs
        # at once), so that the deadline passes during the handover: that refuses, failing
        # closed, and names the deadline. With five polls to spare, the same handover
        # passes. While the job is listed and running, each poll reads the jobs alone.
        slow = {"artifacts": 55, "artifact_zips": 55, "runs": 55}
        for spare, passes in ((2, False), (5, True)):
            polls = queue.ACCEPTANCE_WAIT // 60 - spare
            with self.subTest(spare=spare):
                found, reads, slept = self.waited(took=slow, jobs=[
                    self.listing("jobs", self.job(**self.RUNNING))] * polls + [self.sound["jobs"]])
                self.assertEqual(reads, ["ci_runs", *["jobs"] * (polls + 1),
                                         *self.SOUND_READS[2:]])
                self.assertEqual(slept, [60] * polls)
                if passes:
                    self.assertEqual(found, VERDICTS)
                else:
                    self.refused(found, "the deadline, 150 minutes, passed during the handover")

    def test_two_runs_refuse(self):
        # Step 1's "exactly one" run.
        found, _, _ = self.waited(ci_runs=[self.listing(
            "workflow_runs", self.run_answer(), self.run_answer(id=RUN + 1))])
        self.refused(found, "GitHub lists 2 runs of ci.yml for the group's head")

    def test_a_run_of_another_head_event_workflow_or_repository_refuses(self):
        # Step 1's run: of the head, on the merge group event, of ci.yml, from this
        # repository (ci_run's comparison).
        for key, value, name in (("head_sha", "f" * 40, "head"), ("event", "push", "event"),
                                 ("head_repository", {"full_name": "fork/repository"},
                                  "head repository")):
            with self.subTest(key=key):
                found, _, _ = self.waited(ci_runs=[self.listing(
                    "workflow_runs", self.run_answer(**{key: value}))])
                self.refused(found, f"the CI run {RUN} has another {name} than")

    def test_the_ci_workflow_path_may_carry_a_ref_suffix_on_both_reads(self):
        paths = (".github/workflows/ci.yml", ".github/workflows/ci.yml@refs/heads/main")
        for initial in paths:
            for reread in paths:
                with self.subTest(initial=initial, reread=reread):
                    found, _, _ = self.waited(
                        ci_runs=[self.listing("workflow_runs", self.run_answer(path=initial))],
                        runs=[self.run_answer(path=reread)])
                    self.assertEqual(found, VERDICTS)

    def test_another_workflow_refuses_with_or_without_a_ref_suffix_on_both_reads(self):
        paths = (".github/workflows/other.yml",
                 ".github/workflows/other.yml@refs/heads/main")
        for source in ("ci_runs", "runs"):
            for path in paths:
                with self.subTest(source=source, path=path):
                    changes = {source: [self.run_answer(path=path)]}
                    if source == "ci_runs":
                        changes[source] = [self.listing("workflow_runs", changes[source][0])]
                    found, _, _ = self.waited(**changes)
                    self.refused(found, f"the CI run {RUN} has another workflow file than")

    def test_a_run_begun_again_while_waiting_refuses(self):
        # The attempt held from step 1: an acceptance job of a later attempt
        # (acceptance_job), or the run read again at one (same_run), refuses.
        found, _, _ = self.waited(jobs=[
            self.listing("jobs", self.job(**self.RUNNING)),
            self.listing("jobs", self.job(id=JOB + 1, run_attempt=2, **self.RUNNING))])
        self.refused(found, "was run again after it was first read at attempt 1: its "
                     "acceptance job is of attempt 2")
        found, _, _ = self.waited(jobs=[self.listing("jobs", self.other_job())],
                                  runs=[self.run_answer(run_attempt=2)])
        self.refused(found, "was run again after it was first read at attempt 1: it is at "
                     "attempt 2")

    def test_a_partial_re_run_cannot_carry_over_an_earlier_acceptance_job(self):
        later = self.run_answer(run_attempt=2)
        found, reads, _ = self.waited(ci_runs=[self.listing("workflow_runs", later)])
        self.refused(found, f"the CI run {RUN} lists an acceptance job of attempt 1, not its "
                     "current attempt 2")
        self.assertEqual(reads, ["ci_runs", "jobs"])

    def test_an_acceptance_job_from_the_current_attempt_counts(self):
        later = self.run_answer(run_attempt=2)
        current_jobs = self.listing("jobs", self.other_job(), self.job(run_attempt=2))
        found, reads, _ = self.waited(ci_runs=[self.listing("workflow_runs", later)],
                                      runs=[later], jobs=[current_jobs])
        self.assertEqual(found, VERDICTS)
        self.assertEqual(reads, self.SOUND_READS)

    def test_a_ci_run_without_acceptance_refuses(self):
        # The plant of a group whose ci.yml drops acceptance: once the run has completed
        # with no job of that name, step 2 refuses, as the `needs` did.
        found, _, _ = self.waited(jobs=[self.listing("jobs", self.other_job())],
                                  runs=[self.run_answer(status="completed")])
        self.refused(found, f"the CI run {RUN} completed with no job named acceptance")

    def test_a_skipped_cancelled_or_failed_job_refuses(self):
        # Step 2's conclusion: success alone.
        for conclusion in ("skipped", "cancelled", "failure", "timed_out"):
            with self.subTest(conclusion=conclusion):
                found, _, _ = self.waited(jobs=[self.listing(
                    "jobs", self.job(conclusion=conclusion))])
                self.refused(found, f"ended {conclusion}, not success")

    def test_two_acceptance_jobs_or_another_run_s_refuse(self):
        # Step 2's one job of this run.
        found, _, _ = self.waited(jobs=[self.listing("jobs", self.job(), self.job(id=JOB + 1))])
        self.refused(found, f"the CI run {RUN} has 2 jobs named acceptance, not one")
        found, _, _ = self.waited(jobs=[self.listing("jobs", self.job(run_id=RUN + 1))])
        self.refused(found, "lists an acceptance job of another run")

    def test_a_missing_artifact_refuses_at_the_deadline(self):
        # Step 3's wait, against the one deadline.
        found, _, slept = self.waited(artifacts=[self.listing("artifacts")])
        self.refused(found, "the acceptance job's artifact had not been listed after 150 minutes")
        self.assertEqual(slept, [60] * 150)

    def test_an_earlier_artifact_and_one_from_the_selected_job_pass(self):
        earlier = self.artifact(id=ARTIFACT - 1, created_at="2026-10-27T20:59:59Z",
                                expired=True)
        found, _, _ = self.waited(artifacts=[self.listing(
            "artifacts", earlier, self.artifact())])
        self.assertEqual(found, VERDICTS)

    def test_two_artifacts_from_the_selected_job_refuse(self):
        found, _, _ = self.waited(artifacts=[self.listing(
            "artifacts", self.artifact(), self.artifact(id=ARTIFACT + 1))])
        self.refused(found, f"the CI run {RUN} lists 2 artifacts made during its acceptance "
                     "job, not one")

    def test_an_expired_artifact_refuses(self):
        # Step 3's unexpired artifact.
        found, _, _ = self.waited(artifacts=[self.listing("artifacts",
                                                          self.artifact(expired=True))])
        self.refused(found, "acceptance artifact has expired")

    def test_another_run_s_or_head_s_artifact_refuses(self):
        # Step 3's artifact of that run and head.
        for origin in ({"id": RUN + 1, "head_sha": self.HEAD}, {"id": RUN, "head_sha": "f" * 40}):
            with self.subTest(origin=origin):
                found, _, _ = self.waited(artifacts=[self.listing(
                    "artifacts", self.artifact(workflow_run=origin))])
                self.refused(found, "is another run's, or another head's")

    def test_an_artifact_outside_the_job_s_execution_is_never_selected(self):
        for created in ("2026-10-27T20:59:59Z", "2026-10-27T21:50:01Z"):
            with self.subTest(created=created):
                found, reads, _ = self.waited(artifacts=[self.listing(
                    "artifacts", self.artifact(created_at=created))])
                self.refused(found, "the acceptance job's artifact had not been listed after "
                             "150 minutes")
                self.assertNotIn("artifact_zips", reads)
        for created in (STARTED, COMPLETED):
            with self.subTest(created=created):
                found, _, _ = self.waited(artifacts=[self.listing(
                    "artifacts", self.artifact(created_at=created))])
                self.assertEqual(found, VERDICTS)

    def test_a_zip_holding_more_than_the_acceptance_job_keeps_refuses(self):
        # Step 3's zip (acceptance_verdicts): the files the acceptance job keeps, each
        # once, named alone and regular, and verdicts.json among them.
        link = zipfile.ZipInfo("verdicts.json")
        link.external_attr = 0o120777 << 16
        folder = zipfile.ZipInfo("reports/")
        folder.external_attr = 0o040755 << 16
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")  # zipfile warns of a name written twice
            cases = (
                ([("verdicts.json", VERDICTS), ("notes.txt", b"")],
                 "holds a file the acceptance job does not keep: notes.txt"),
                ([("reports/verdicts.json", VERDICTS)], "holds a path"),
                ([("../verdicts.json", VERDICTS)], "holds a path"),
                ([("verdicts.json", VERDICTS), (folder, b"")], "holds a path"),
                ([(link, b"/etc/passwd")], "holds a link, or another file that is not regular"),
                ([("verdicts.json", VERDICTS), ("verdicts.json", b"{}")], "holds a name twice"),
                ([("report.md", b"")], "holds no verdicts.json"))
            zips = [(artifact_zip(members), message) for members, message in cases]
        # A name stored with a NUL, which zipfile itself would read as verdicts.json.
        cut = artifact_zip([("report.md", b""), ("verdicts.jsonX", VERDICTS)])
        zips.append((cut.replace(b"verdicts.jsonX", b"verdicts.json\0"),
                     "holds a file the acceptance job does not keep: verdicts.json\\x00"))
        for data, message in zips:
            with self.subTest(message=message):
                self.refused(self.waited(artifact_zips=[data])[0],
                             f"acceptance: the artifact {message}")
        for data in (b"not a zip", KEPT_REPORTS[:-30]):
            with self.subTest(data=data[:12]):
                self.unreadable(self.waited(artifact_zips=[data])[0],
                                "could not read the acceptance artifact's zip")

    def test_a_zip_past_its_limit_refuses(self):
        # Step 3's zip, of a group's own CI: at most ACCEPTANCE_ZIP_MAX bytes, which a zip
        # of exactly that size passes and one of a byte more does not, before it is read
        # as a zip (acceptance_verdicts; the download holds the same limit as it comes).
        limit = queue.ACCEPTANCE_ZIP_MAX
        at, over = sized_zip(limit), sized_zip(limit + 1)
        self.assertEqual((len(at), len(over)), (limit, limit + 1))
        found = self.waited(artifact_zips=[at])[0]
        self.assertEqual(found, zipfile.ZipFile(io.BytesIO(at)).read("verdicts.json"))
        self.refused(self.waited(artifact_zips=[over])[0],
                     f"acceptance: the artifact's zip is larger than {limit} bytes")

    def test_a_verdicts_json_past_its_limit_refuses(self):
        # Step 3's verdicts: at most ACCEPTANCE_VERDICTS_MAX bytes, stored or deflated,
        # which a file of exactly that size passes; one byte more refuses by the size its
        # header declares, before anything is decompressed.
        limit = queue.ACCEPTANCE_VERDICTS_MAX
        for method in (zipfile.ZIP_STORED, zipfile.ZIP_DEFLATED):
            with self.subTest(method=method):
                verdicts = b" " * limit
                self.assertEqual(self.waited(artifact_zips=[artifact_zip(
                    [("verdicts.json", verdicts)], method)])[0], verdicts)
                self.refused(self.waited(artifact_zips=[artifact_zip(
                    [("verdicts.json", verdicts + b" ")], method)])[0],
                    f"the artifact holds verdicts.json, which declares {limit + 1} bytes, "
                    f"more than {limit}")

    def test_a_compressed_payload_that_expands_past_the_limit_refuses(self):
        # A zip of some 16,000 bytes whose verdicts.json, or another file it keeps, would
        # expand to 16 MiB: refused by the size each file's header declares, before
        # anything is decompressed. A file compressed by another method than deflate,
        # which zipfile would decompress a whole read at once, refuses however small.
        expands = b"\0" * (16 << 20)
        for members in ([("verdicts.json", expands)],
                        [("verdicts.json", VERDICTS), ("report.md", expands)]):
            name = members[-1][0]
            with self.subTest(name=name):
                bomb = artifact_zip(members, zipfile.ZIP_DEFLATED)
                self.assertLess(len(bomb), 20000)
                self.refused(self.waited(artifact_zips=[bomb])[0],
                             f"the artifact holds {name}, which declares {16 << 20} bytes")
        for method in (zipfile.ZIP_BZIP2, zipfile.ZIP_LZMA):
            with self.subTest(method=method):
                self.refused(self.waited(artifact_zips=[artifact_zip(
                    [("verdicts.json", VERDICTS)], method)])[0],
                    "the artifact holds verdicts.json compressed by another method than deflate")

    def test_a_header_that_understates_its_file_refuses(self):
        # zipfile reads a file no further than its header declares. Read through the
        # bounded stream instead, a verdicts.json whose header declares 1,000 bytes refuses
        # once it gives one byte past ACCEPTANCE_VERDICTS_MAX, stored or deflated, however
        # much more it holds within the zip's own limit; and if it holds fewer than that
        # but more than 1,000, it refuses for holding other than its header declares.
        limit = queue.ACCEPTANCE_VERDICTS_MAX
        for method in (zipfile.ZIP_STORED, zipfile.ZIP_DEFLATED):
            for size in (limit + 1, 3 * limit):
                with self.subTest(method=method, size=size):
                    data = declaring(artifact_zip([("verdicts.json", b"\0" * size)], method),
                                     "verdicts.json", 1000)
                    self.assertEqual(zipfile.ZipFile(io.BytesIO(data)).getinfo(
                        "verdicts.json").file_size, 1000)
                    self.refused(self.waited(artifact_zips=[data])[0],
                                 f"the artifact's verdicts.json is larger than {limit} bytes")
            with self.subTest(method=method, size=5000):
                data = declaring(artifact_zip([("verdicts.json", b"\0" * 5000)], method),
                                 "verdicts.json", 1000)
                self.refused(self.waited(artifact_zips=[data])[0],
                             "verdicts.json holds 5000 bytes, not the 1000 its header declares")

    def test_the_download_is_bounded_as_it_comes(self):
        # Step 3's download, by gh api, a stand-in for it first on the PATH: gh's bytes as
        # given, by the artifact's id, up to ACCEPTANCE_ZIP_MAX. At one byte more the
        # reading stops and refuses, and gh, which holds on after it for 30 seconds, is
        # stopped by its handle at once rather than waited for. A gh that exits other
        # than 0 is unreadable.
        tools = self.root / "tools"
        tools.mkdir()
        (tools / "fake_gh.py").write_text(
            "import json, os, sys, time\n"
            "with open(os.environ['FAKE_ZIP_LOG'], 'w', encoding='utf-8') as log:\n"
            "    json.dump(sys.argv[1:], log)\n"
            "sys.stdout.buffer.write(b'x' * int(os.environ['FAKE_ZIP_BYTES']))\n"
            "sys.stdout.buffer.flush()\n"
            "time.sleep(int(os.environ['FAKE_ZIP_HOLD']))\n"
            "sys.exit(int(os.environ['FAKE_ZIP_EXIT']))\n", encoding="utf-8")
        (tools / "gh").write_text(f"#!/bin/sh\nexec {shlex.quote(sys.executable)} -I "
                                  f"{shlex.quote(str(tools / 'fake_gh.py'))} \"$@\"\n",
                                  encoding="utf-8")
        (tools / "gh").chmod(0o755)
        log, limit = self.root / "gh-call.json", queue.ACCEPTANCE_ZIP_MAX
        api = queue.GitHub("owner/repository", None)
        for size, hold, code in ((limit, 0, 0), (limit + 1, 30, 0), (10, 0, 1)):
            with self.subTest(size=size, code=code), patch.dict(os.environ, {
                    "GH_TOKEN": "fixture-token", "FAKE_ZIP_LOG": str(log),
                    "FAKE_ZIP_BYTES": str(size), "FAKE_ZIP_HOLD": str(hold),
                    "FAKE_ZIP_EXIT": str(code),
                    "PATH": f"{tools}{os.pathsep}{os.environ['PATH']}"}):
                start = time.monotonic()
                if size == limit:
                    self.assertEqual(api.read("artifact_zips", ARTIFACT), b"x" * limit)
                elif code:
                    with self.assertRaisesRegex(ValueError, "could not read artifact_zips"):
                        api.read("artifact_zips", ARTIFACT)
                else:
                    with self.assertRaisesRegex(queue.Refused, re.escape(
                            f"acceptance: the artifact's zip is larger than {limit} bytes")):
                        api.read("artifact_zips", ARTIFACT)
                    self.assertLess(time.monotonic() - start, 15)
                self.assertEqual(json.loads(log.read_text(encoding="utf-8")),
                                 ["api", "--method", "GET",
                                  f"repos/owner/repository/actions/artifacts/{ARTIFACT}/zip"])

    def test_a_change_at_the_second_reading_refuses(self):
        # Step 4: after the download, the same run at its attempt, the same job, still its
        # latest execution and passed, and the complete artifact list unchanged, with the
        # selected artifact still unexpired and in its window.
        jobs, artifacts = self.sound["jobs"], self.sound["artifacts"]
        earlier = self.artifact(id=ARTIFACT - 1, created_at="2026-10-27T20:59:59Z")
        with_earlier = self.listing("artifacts", earlier, self.artifact())
        for label, changes, message in (
                ("another job", {"jobs": [jobs, self.listing("jobs", self.job(id=JOB + 1))]},
                 "acceptance job or its artifact changed while the artifact was read"),
                ("a re-run begun", {"jobs": [jobs, self.listing(
                    "jobs", self.job(id=JOB + 1, run_attempt=2, **self.RUNNING))]},
                 "was run again after it was first read at attempt 1"),
                ("the job no longer passed", {"jobs": [jobs, self.listing(
                    "jobs", self.job(**self.RUNNING))]}, "changed while the artifact was read"),
                ("another artifact", {"artifacts": [artifacts, self.listing(
                    "artifacts", self.artifact(id=ARTIFACT + 1))]},
                 "changed while the artifact was read"),
                ("an earlier artifact appeared", {"artifacts": [artifacts, with_earlier]},
                 "changed while the artifact was read"),
                ("an earlier artifact disappeared", {"artifacts": [with_earlier, artifacts]},
                 "changed while the artifact was read"),
                ("the artifact gone", {"artifacts": [artifacts, self.listing("artifacts")]},
                 "changed while the artifact was read"),
                ("the artifact expired", {"artifacts": [artifacts, self.listing(
                    "artifacts", self.artifact(expired=True))]}, "has expired"),
                ("the run at another attempt", {"runs": [self.run_answer(run_attempt=2)]},
                 "it is at attempt 2")):
            with self.subTest(label):
                found, reads, _ = self.waited(**changes)
                self.refused(found, message)
                self.assertEqual(reads[:4], self.SOUND_READS[:4])

    def test_a_list_not_read_whole_is_unreadable(self):
        # Every list read whole (listed): total_count the items given, in one page of 100.
        for kind, key, item in (("ci_runs", "workflow_runs", self.run_answer()),
                                ("jobs", "jobs", self.job()),
                                ("artifacts", "artifacts", self.artifact())):
            for label, answer in (("more than given", {"total_count": 2, key: [item]}),
                                  ("more than a page", self.listing(key, *[item] * 101)),
                                  ("no count", {key: [item]}), ("no list", {"total_count": 0}),
                                  ("not an object", self.listing(key, [item]))):
                with self.subTest(kind=kind, label=label):
                    self.unreadable(self.waited(**{kind: [answer]})[0],
                                    "whole, in one page of 100")

    def test_malformed_answers_are_unreadable(self):
        # Missing or malformed data is unreadable, never a pass.
        run, job, artifact = self.run_answer(), self.job(), self.artifact()
        runs = [self.listing("workflow_runs", {k: v for k, v in run.items() if k != "id"}),
                self.listing("workflow_runs", dict(run, run_attempt="1")),
                self.listing("workflow_runs", dict(run, head_sha="x")),
                self.listing("workflow_runs", dict(run, head_repository=None))]
        jobs = [self.listing("jobs", dict(job, id="9001")),
                self.listing("jobs", dict(job, started_at="yesterday")),
                self.listing("jobs", dict(job, completed_at="2026-10-27T20:00:00Z")),
                self.listing("jobs", dict(job, status=None)),
                self.listing("jobs", {k: v for k, v in job.items() if k != "name"})]
        artifacts = [self.listing("artifacts", dict(artifact, expired="false")),
                     self.listing("artifacts", {k: v for k, v in artifact.items()
                                                if k != "created_at"}),
                     self.listing("artifacts", dict(artifact, workflow_run=None)),
                     self.listing("artifacts", dict(
                         artifact, id=ARTIFACT - 1, created_at="2026-10-27T20:59:59Z",
                         expired="false"), artifact)]
        for kind, answers, message in (("ci_runs", runs, "could not read the group's CI run"),
                                       ("jobs", jobs,
                                        "could not read the CI run's acceptance job"),
                                       ("artifacts", artifacts,
                                        "could not read the CI run's acceptance artifact")):
            for number, answer in enumerate(answers):
                with self.subTest(kind=kind, case=number):
                    self.unreadable(self.waited(**{kind: [answer]})[0], message)
        self.unreadable(self.waited(artifact_zips=["UEsF"])[0],
                        "could not read the acceptance artifact")

    def command(self, *extra, fixture=None):
        return subprocess.run([sys.executable, "-I", str(SCRIPTS / "check_queue.py"), *extra]
                              + (["--github-json", str(fixture)] if fixture else []),
                              cwd=self.root, capture_output=True, text=True)

    def fixture(self, answers=None):
        path = self.root / "github.json"
        path.write_text(json.dumps(answers or acceptance_answers(self.HEAD)), encoding="utf-8")
        return path

    def asked(self, out):
        return ("--acceptance-run", "--head", self.HEAD, "--repo", "owner/repository",
                "--ci-workflow", "ci.yml", "--out", str(out))

    def test_the_command_writes_the_verdicts_alone(self):
        # The verdicts, from main's copy, alone, to a new file of a folder it makes.
        out = self.root / "acceptance"
        result = self.command(*self.asked(out), fixture=self.fixture())
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("queue: PASS", result.stdout)
        self.assertEqual(os.listdir(out), ["verdicts.json"])
        self.assertEqual((out / "verdicts.json").read_bytes(), VERDICTS)
        result = self.command(*self.asked(out), fixture=self.fixture())
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("File exists", result.stderr)

    def test_the_command_writes_nothing_when_it_refuses(self):
        answers = acceptance_answers(self.HEAD)
        answers["artifacts"][str(RUN)]["artifacts"][0]["expired"] = True
        out = self.root / "acceptance"
        result = self.command(*self.asked(out), fixture=self.fixture(answers))
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("queue: REFUSED: acceptance: the CI run 7001's acceptance artifact has "
                      "expired", result.stdout)
        self.assertFalse(out.exists())

    def test_the_command_takes_its_arguments_alone(self):
        # As the other modes do: every argument the mode needs, and nothing else.
        out = str(self.root / "acceptance")
        asked = self.asked(out)
        drop = lambda name: [a for i, a in enumerate(asked)
                             if a != name and (i == 0 or asked[i - 1] != name)]
        for args, message in (
                (drop("--out"), "--acceptance-run needs --head, --repo, --ci-workflow and --out"),
                (drop("--ci-workflow"), "--acceptance-run needs"),
                (drop("--head"), "--acceptance-run needs"),
                (drop("--repo"), "--acceptance-run needs"),
                ([*asked, "--base", self.HEAD], "--acceptance-run needs"),
                ([*asked, "--gaps"], "--acceptance-run needs"),
                ([*asked, "--plan", out], "--acceptance-run needs"),
                ([*asked, "--render"], "--acceptance-run needs"),
                ([*asked, "--tree", out], "--tree accepts only --render"),
                ([*asked, "--run-plan", out], "--run-plan needs --head and accepts nothing else"),
                ([*asked, "stray"], "unrecognized arguments: stray"),
                (asked[1:], "--ci-workflow and --out belong to --acceptance-run"),
                (["--head", self.HEAD, "--base", self.HEAD, "--repo", "owner/repository",
                  "--out", out], "--ci-workflow and --out belong to --acceptance-run"),
                ([*drop("--ci-workflow"), "--ci-workflow", "../ci.yml"],
                 "--ci-workflow must name a workflow file of .github/workflows/, alone"),
                ([*drop("--ci-workflow"), "--ci-workflow", "ci.yml/runs"], "must name a workflow"),
                ([*drop("--repo"), "--repo", "owner"], "--repo must be owner/name"),
                ([*drop("--head"), "--head", "HEAD"], "could not read head")):
            with self.subTest(args=args):
                result = self.command(*args, fixture=self.fixture())
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertIn(message, result.stderr)
                self.assertFalse((self.root / "acceptance").exists())

    def test_the_reader_reads_each_list_whole_and_the_zip_as_bytes(self):
        # Through gh api, as the reader reads the rest: each list one page of 100, the
        # zip by the artifact's id, its bytes as given, by the bounded download (whose
        # reading of gh test_the_download_is_bounded_as_it_comes holds).
        api = queue.GitHub("owner/repository", None)
        root = "repos/owner/repository/actions/"
        with patch.dict(os.environ, {"GH_TOKEN": "fixture-token"}), \
                patch.object(queue.subprocess, "run", return_value=subprocess.CompletedProcess(
                    [], 0, "{}", "")) as call:
            for args, endpoint in (
                    (("ci_runs", None, "ci.yml", self.HEAD),
                     f"workflows/ci.yml/runs?event=merge_group&head_sha={self.HEAD}&per_page=100"),
                    (("jobs", RUN), f"runs/{RUN}/jobs?filter=latest&per_page=100"),
                    (("artifacts", RUN), f"runs/{RUN}/artifacts?name=acceptance&per_page=100"),
                    (("runs", RUN), f"runs/{RUN}")):
                with self.subTest(kind=args[0]):
                    self.assertEqual(api.read(*args), {})
                    self.assertEqual(call.call_args.args[0],
                                     ["gh", "api", "--method", "GET", root + endpoint])
                    self.assertIs(call.call_args.kwargs["text"], True)
            with patch.object(queue, "download", return_value=KEPT_REPORTS) as fetch:
                self.assertEqual(api.read("artifact_zips", ARTIFACT), KEPT_REPORTS)
            self.assertEqual(fetch.call_args.args[0],
                             ["gh", "api", "--method", "GET", root + f"artifacts/{ARTIFACT}/zip"])
            for workflow, head in (("../ci.yml", self.HEAD), ("ci.yml", "HEAD")):
                with self.subTest(workflow=workflow, head=head):
                    with self.assertRaisesRegex(ValueError, "unknown read"):
                        api.read("ci_runs", workflow=workflow, head=head)


class RulesetTests(unittest.TestCase):
    """docs/rulesets/queue-judge.json, the organization ruleset the owner imports, bound to
    the queue judge's workflow and to the lists of required checks (the design's sections
    5, 6 and 8). This is configuration, not enforcement: the owner's check of the
    installed rule and the coordinator's trial show that."""

    RULESET = SCRIPTS.parent / "docs/rulesets/queue-judge.json"
    @classmethod
    def problems(cls, ruleset, workflows, required) -> list[str]:
        """Where the configuration departs from the one reviewed: an active branch ruleset
        on main of this repository alone, with no bypass actor, whose one rule, "Require
        workflows to pass before merging", enforced on creation too, names the queue
        judge's workflow in this repository at main's ref, by those three alone (no sha);
        that workflow holds the judge's two jobs, no other workflow has a job of either id
        or name, and safe_push's required checks do not name the judge's."""
        found = []
        if set(ruleset) != {"name", "target", "enforcement", "bypass_actors", "conditions",
                            "rules"}:
            found.append("settings other than the reviewed ones")
        if ruleset.get("target") != "branch":
            found.append("a target other than branches")
        if ruleset.get("enforcement") != "active":
            found.append("a ruleset not enforced")
        if ruleset.get("bypass_actors") != []:
            found.append("a bypass actor")
        if ruleset.get("conditions") != {
                "repository_name": {"include": ["stoicheia"], "exclude": [], "protected": True},
                "ref_name": {"include": ["refs/heads/main"], "exclude": []}}:
            found.append("conditions other than main of this repository alone")
        rules = ruleset.get("rules")
        if not isinstance(rules, list) or [rule.get("type") for rule in rules] != ["workflows"] \
                or set(rules[0]) != {"type", "parameters"}:
            found.append("rules other than one rule requiring workflows")
        else:
            parameters = rules[0]["parameters"]
            if set(parameters) != {"do_not_enforce_on_create", "workflows"} \
                    or parameters["do_not_enforce_on_create"] is not False:
                found.append("parameters other than the reviewed ones")
            named = parameters.get("workflows")
            if not isinstance(named, list) or len(named) != 1:
                found.append("not one workflow")
            else:
                if set(named[0]) != {"path", "repository_id", "ref"}:
                    found.append("a workflow named by more than its path, repository and ref")
                if named[0].get("path") != JUDGE:
                    found.append("another path than the judge's")
                if named[0].get("ref") != "refs/heads/main":
                    found.append("another ref than main's")
                if type(named[0].get("repository_id")) is not int \
                        or named[0]["repository_id"] != 1421047853:
                    found.append("another repository than this one")
        if set(JUDGE_JOBS) - set((workflows.get(Path(JUDGE).name) or {}).get("jobs") or {}):
            found.append("a judge's workflow without the judge's jobs")
        for name, workflow in workflows.items():
            for job_id, job in (workflow.get("jobs") or {}).items():
                if name != Path(JUDGE).name and {job_id, job.get("name")} & set(JUDGE_JOBS):
                    found.append(f"{name}: a job named as the judge's")
        if set(required) & set(JUDGE_JOBS):
            found.append("safe_push's required checks name the judge's")
        return found

    def configuration(self):
        return {"ruleset": json.loads(self.RULESET.read_text(encoding="utf-8")),
                "workflows": {path.name: yaml.safe_load(path.read_text(encoding="utf-8"))
                              for path in sorted((SCRIPTS.parent / ".github/workflows")
                                                 .glob("*.y*ml"))},
                "required": queue.safe_push.REQUIRED_CHECKS}

    def test_the_ruleset_is_the_one_reviewed(self):
        self.assertEqual(self.problems(**self.configuration()), [])

    def test_the_binding_refuses_each_plant(self):
        # Section 7's plants of the reviewed ruleset file, and of what it binds, each
        # refused by its own predicate of `problems`, named by its refusal.
        def workflow(state):
            return state["ruleset"]["rules"][0]["parameters"]["workflows"][0]

        plants = (
            ("a required_status_checks rule", "rules other than one rule requiring workflows",
             lambda s: s["ruleset"]["rules"].append({"type": "required_status_checks",
                                                     "parameters": {}})),
            ("a bypass actor", "a bypass actor", lambda s: s["ruleset"]["bypass_actors"].append(
                {"actor_id": 5, "actor_type": "RepositoryRole", "bypass_mode": "always"})),
            ("a sha beside the ref", "a workflow named by more than its path, repository and ref",
             lambda s: workflow(s).update(sha="0" * 40)),
            ("another target", "a target other than branches",
             lambda s: s["ruleset"].update(target="tag")),
            ("another branch", "conditions other than main of this repository alone",
             lambda s: s["ruleset"]["conditions"]["ref_name"].update(include=["~ALL"])),
            ("another repository", "conditions other than main of this repository alone",
             lambda s: s["ruleset"]["conditions"]["repository_name"].update(include=["~ALL"])),
            ("another path", "another path than the judge's",
             lambda s: workflow(s).update(path=".github/workflows/ci.yml")),
            ("another ref", "another ref than main's",
             lambda s: workflow(s).update(ref="refs/heads/other")),
            ("another repository's workflow", "another repository than this one",
             lambda s: workflow(s).update(repository_id=1)),
            ("a second workflow", "not one workflow",
             lambda s: s["ruleset"]["rules"][0]["parameters"]["workflows"].append(workflow(s))),
            ("not enforced on creation", "parameters other than the reviewed ones",
             lambda s: s["ruleset"]["rules"][0]["parameters"].update(
                 do_not_enforce_on_create=True)),
            ("evaluated only", "a ruleset not enforced",
             lambda s: s["ruleset"].update(enforcement="evaluate")),
            ("another setting", "settings other than the reviewed ones",
             lambda s: s["ruleset"].update(source_type="Repository")),
            ("another workflow's job of the judge's id", "ci.yml: a job named as the judge's",
             lambda s: s["workflows"]["ci.yml"]["jobs"].update({"queue-integrity": {}})),
            ("another workflow's job of the judge's name", "ci.yml: a job named as the judge's",
             lambda s: s["workflows"]["ci.yml"]["jobs"]["check"].update(name="queue-gaps")),
            ("the judge's workflow without a job", "a judge's workflow without the judge's jobs",
             lambda s: s["workflows"][Path(JUDGE).name]["jobs"].pop("queue-gaps")),
            ("safe_push requiring the judge by name",
             "safe_push's required checks name the judge's",
             lambda s: s.update(required=(*s["required"], "queue-integrity"))))
        for label, refusal, plant in plants:
            with self.subTest(label):
                state = self.configuration()
                plant(state)
                self.assertIn(refusal, "\n".join(self.problems(**state)))


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
