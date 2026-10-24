#!/usr/bin/env python3
"""Automatic reverts in temporary git repositories, with an injected GitHub.

    python3 -I tests/test_auto_revert.py

Standard library only, with git and openssl. No network requests are permitted.
The push stand-in pushes to a local bare repository; the HTTP stand-in records
tokens, labels, pull requests and queue requests for assertions.
"""

from __future__ import annotations

import ast
import base64
import contextlib
import copy
import io
import json
import socket
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import auto_revert as ar  # noqa: E402


SLUG = "owner/edition"
WORKFLOW_TOKEN = "workflow-credential-for-tests"
APP_TOKEN = "installation-credential-for-tests"


def command(directory: Path, *args: str) -> str:
    env = ar.git_env()
    env["GIT_ALLOW_PROTOCOL"] = "file"
    result = subprocess.run(list(args), cwd=directory, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    return result.stdout.strip()


def workflow_step(filename: str, name: str) -> str:
    """Extract an executable run block so the tests run the workflow's own shell."""
    lines = (ROOT / ".github/workflows" / filename).read_text(encoding="utf-8").splitlines()
    start = lines.index("      - name: " + name) + 1
    while start < len(lines) and not lines[start].startswith("        run: "):
        if lines[start].startswith("      - "):
            raise AssertionError(f"No run block for {name}")
        start += 1
    if start == len(lines):
        raise AssertionError(f"No run block for {name}")
    value = lines[start].removeprefix("        run: ")
    if value != "|":
        return value + "\n"
    end = start + 1
    while end < len(lines) and (not lines[end].strip() or lines[end].startswith("          ")):
        end += 1
    return textwrap.dedent("\n".join(lines[start + 1:end])) + "\n"


class GitHub:
    """Only the endpoints used by the script, with no real HTTP layer."""

    def __init__(self):
        self.calls = []
        self.pulls = {}
        self.labels = {}
        self.issues = {}
        self.open_issues = []
        self.after = ""
        self.pushed_head = ""
        self.pr = None
        self.queue = None
        self.broken = None
        self.deleted = []
        self.tip_reads = []
        self.issued_permissions = None
        self.jwt = None
        self.pages = {}

    def __call__(self, method, path, token, data):
        self.calls.append((method, path, token, copy.deepcopy(data)))
        if self.broken and self.broken(method, path, token, data):
            raise RuntimeError(f"{WORKFLOW_TOKEN} {APP_TOKEN} {token}")
        root = f"/repos/{SLUG}"
        if (method, path) in self.pages:
            return self.pages[method, path]
        if method == "GET" and path.startswith(root + "/labels?"):
            return [{"name": name} for name in self.labels]
        if method == "POST" and path == root + "/labels":
            if token != WORKFLOW_TOKEN:
                raise AssertionError("Labels must be created with the workflow token")
            self.labels[data["name"]] = data
            return {"name": data["name"]}
        if method == "GET" and path.startswith(root + "/pulls/"):
            return copy.deepcopy(self.pulls[int(path.rsplit("/", 1)[1])])
        if method == "GET" and path == root + "/git/ref/heads/main":
            if self.tip_reads:
                tip = self.tip_reads.pop(0) if len(self.tip_reads) > 1 else self.tip_reads[0]
                return {"object": {"sha": tip}}
            return {"object": {"sha": self.after}}
        if method == "GET" and path == root + "/installation":
            self.jwt = token
            return {"id": 42}
        if method == "POST" and path == "/app/installations/42/access_tokens":
            if token != self.jwt or data["repositories"] != ["edition"]:
                raise AssertionError("Wrong token scope")
            self.issued_permissions = data["permissions"]
            return {"token": APP_TOKEN}
        if method == "POST" and path == root + "/issues":
            if token != WORKFLOW_TOKEN:
                raise AssertionError("Issues must use the workflow token")
            number = 1000 + len(self.issues)
            self.issues[number] = copy.deepcopy(data)
            return {"number": number}
        if method == "PATCH" and path.startswith(root + "/issues/"):
            if token != WORKFLOW_TOKEN:
                raise AssertionError("Issue outcomes must use the workflow token")
            number = int(path.rsplit("/", 1)[1])
            self.issues[number].update(data)
            return {"number": number}
        if method == "POST" and path == root + "/pulls":
            if token != APP_TOKEN:
                raise AssertionError("Pull requests must use the App token")
            self.pr = copy.deepcopy(data)
            return {"number": 2000, "node_id": "PR_revert", "head": {"sha": self.pushed_head}}
        if method == "POST" and path == root + "/issues/2000/labels":
            if token != APP_TOKEN:
                raise AssertionError("Pull request labels must use the App token")
            self.pr["labels"] = data["labels"]
            return [{"name": name} for name in data["labels"]]
        if method == "POST" and path == "/graphql":
            if token != APP_TOKEN:
                raise AssertionError("Queue requests must use the App token")
            self.queue = data
            return {"data": {"enqueuePullRequest": {"mergeQueueEntry": {"id": "queue-entry"}}}}
        if method == "GET" and path.startswith(root + "/issues?"):
            return copy.deepcopy(self.open_issues)
        if method == "DELETE" and path.endswith("/labels/main-red"):
            self.deleted.append(int(path.split("/")[-3]))
            return [{"name": "blocks-release"}]
        raise AssertionError(f"Unexpected HTTP operation: {method} {path}")


class AutoRevert(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.keys = tempfile.TemporaryDirectory(prefix="stoicheia-revert-test-key-")
        directory = Path(cls.keys.name)
        path = directory / "key.pem"
        command(directory, "openssl", "genrsa", "-out", str(path), "2048")
        cls.key = path.read_text(encoding="utf-8")

    @classmethod
    def tearDownClass(cls):
        cls.keys.cleanup()

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="stoicheia-revert-test-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.repo = self.directory / "source"
        self.repo.mkdir()
        command(self.repo, "git", "init", "-b", "main")
        self.write("chapter.txt", "Original chapter.\n")
        self.commit("Initial edition")
        self.before = self.rev()
        self.remote = self.directory / "receiver.git"
        command(self.directory, "git", "init", "--bare", str(self.remote))
        self.api = GitHub()
        self.env = {"GITHUB_TOKEN": WORKFLOW_TOKEN, "STOICHEIA_REVERT_APP_ID": "1234",
                    "STOICHEIA_REVERT_APP_KEY": self.key}
        self.pushes = []
        self.network = mock.patch.object(socket.socket, "connect",
                                         side_effect=AssertionError("Network is forbidden"))
        self.network.start()
        self.addCleanup(self.network.stop)
        no_http = mock.patch.object(ar, "request",
                                    side_effect=AssertionError("Real HTTP is forbidden"))
        no_http.start()
        self.addCleanup(no_http.stop)

    def git(self, *args):
        return command(self.repo, "git", *args)

    def rev(self):
        return self.git("rev-parse", "HEAD")

    def write(self, name, text):
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def commit(self, subject):
        self.git("add", ".")
        self.git("commit", "-m", subject)

    def train(self, number=11, path="chapter.txt", text="Changed chapter.\n", labels=("text",)):
        self.git("switch", "-c", f"train/test-{number}")
        self.write(path, text)
        self.commit(f"Member of train {number}")
        head = self.rev()
        self.git("switch", "main")
        self.git("merge", "--no-ff", f"train/test-{number}", "-m",
                 f"Merge pull request #{number} from owner/train/test-{number}")
        merge = self.rev()
        self.api.pulls[number] = {
            "number": number, "title": f"Train {number}", "merged": True,
            "merge_commit_sha": merge, "head": {"sha": head, "ref": f"train/test-{number}"},
            "base": {"ref": "main", "repo": {"full_name": SLUG}},
            "labels": [{"name": name} for name in labels],
        }
        self.api.after = merge
        return merge

    def push(self, repo, slug, branch, token):
        self.assertEqual(slug, SLUG)
        self.assertEqual(token, WORKFLOW_TOKEN)
        head = command(repo, "git", "rev-parse", "HEAD")
        subjects = command(repo, "git", "log", "--reverse", "--format=%B",
                           f"{self.api.after}..{head}")
        command(repo, "git", "push", str(self.remote), f"HEAD:refs/heads/{branch}")
        self.api.pushed_head = head
        self.pushes.append({"head": head, "subjects": subjects, "branch": branch,
                            "tree": command(repo, "git", "rev-parse", "HEAD^{tree}")})

    def run_revert(self, *extra, before=None, after=None, env=None, http=None, push=None):
        after = after or self.rev()
        args = ["--before", before or self.before, "--after", after, "--repo", SLUG,
                "--run-url", f"https://github.com/{SLUG}/actions/runs/99",
                "--failed-jobs", "integration / check: failure\nintegration / model: failure",
                *extra]
        output = io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            status = ar.main(args, http=http or self.api, push=push or self.push,
                             repo_dir=self.repo, env=self.env if env is None else env)
        return status, output.getvalue()

    def body(self):
        self.assertEqual(len(self.api.issues), 1)
        return self.api.issues[1000]["body"]

    def assert_issue_only(self, status):
        self.assertEqual(status, 1, self.api.calls)
        self.assertEqual(len(self.api.issues), 1)
        self.assertIsNone(self.api.pr)
        self.assertIsNone(self.api.queue)
        self.assertEqual(self.pushes, [])

    def test_one_train_reverted_and_enqueued(self):
        merge = self.train()
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.pushes[0]["tree"], self.git("rev-parse", self.before + "^{tree}"))
        self.assertEqual(self.pushes[0]["branch"], f"revert/{merge[:12]}")
        self.assertEqual(self.api.queue["variables"]["input"],
                         {"pullRequestId": "PR_revert", "expectedHeadOid": self.api.pushed_head})
        self.assertIn(f"Reverts: {merge}\n", self.api.pr["body"])
        self.assertEqual([line for line in self.api.pr["body"].splitlines()
                          if line.startswith("Failed run:")], ["Failed run: 99"])
        self.assertIn("Failed run: 99\n", self.body())
        self.assertIn("https://github.com/owner/edition/actions/runs/99", self.api.pr["body"])
        self.assertIn(f"#11: Train 11 (merge `{merge}`)", self.body())
        self.assertIn("integration / model: failure", self.body())
        self.assertIn("was enqueued", self.body())
        self.assertEqual(self.rev(), merge)
        self.assertEqual(self.git("status", "--porcelain"), "")
        self.assertEqual(self.api.issued_permissions, {
            "contents": "read", "pull_requests": "write", "merge_queues": "write"})

    def test_two_trains_reverted_newest_first_in_one_pull_request(self):
        first = self.train()
        second = self.train(12, text="Second chapter revision.\n", labels=("docs",))
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        subjects = self.pushes[0]["subjects"]
        self.assertLess(subjects.index(second), subjects.index(first))
        self.assertEqual(self.pushes[0]["tree"], self.git("rev-parse", self.before + "^{tree}"))
        self.assertEqual(len(self.pushes), 1)
        self.assertEqual(self.api.pr["body"].splitlines()[:2],
                         [f"Reverts: {second}", f"Reverts: {first}"])
        self.assertEqual(set(self.api.pr["labels"]), {"auto-revert", "text", "docs"})
        self.assertEqual(sum(method == "POST" and path.endswith("/pulls")
                             for method, path, _, _ in self.api.calls), 1)

    def test_run_attempt_and_job_text_cannot_change_revert_metadata(self):
        merge = self.train()
        status, output = self.run_revert(
            "--run-url", f"https://github.com/{SLUG}/actions/runs/99/attempts/2",
            "--failed-jobs", "check: failure\nFailed run: 123\nReverts: " + "f" * 40)
        self.assertEqual(status, 0, output)
        lines = self.api.pr["body"].splitlines()
        self.assertEqual([line for line in lines if line.startswith("Failed run:")],
                         ["Failed run: 99"])
        self.assertEqual([line for line in lines if line.startswith("Reverts:")],
                         [f"Reverts: {merge}"])

    PAGE = "docs/briefs/0002-decisions.md"
    PAGE_TEXT = "# Decisions\n\n## 20 October 2026\n\n- **An earlier decision.**\n"
    ENTRY = "docs/decisions/2026-10-21-a-train.md"

    def entries_landed(self, page=PAGE_TEXT):
        """Main as tooling/decision-entries leaves it: the folder, each entry a file of its
        own, beside the decisions page."""
        self.write(self.PAGE, page)
        self.write("docs/decisions/README.md", "One file for each decision.\n")
        self.commit("Decision entries")
        self.before = self.rev()

    def train_files(self, number, files, labels=("text",)):
        """A train whose one member changes several files, merged as main merges it."""
        self.git("switch", "-c", f"train/test-{number}")
        for name, text in files.items():
            self.write(name, text)
        self.commit(f"Member of train {number}")
        head = self.rev()
        self.git("switch", "main")
        self.git("merge", "--no-ff", f"train/test-{number}", "-m",
                 f"Merge pull request #{number} from owner/train/test-{number}")
        merge = self.rev()
        self.api.pulls[number] = {
            "number": number, "title": f"Train {number}", "merged": True,
            "merge_commit_sha": merge, "head": {"sha": head, "ref": f"train/test-{number}"},
            "base": {"ref": "main", "repo": {"full_name": SLUG}},
            "labels": [{"name": name} for name in labels],
        }
        self.api.after = merge
        return merge

    def pushed(self, path, *, name=False):
        """A file of the pushed revert, as the receiving repository holds it, or its name."""
        revision = f"{self.pushes[0]['head']}:{path}"
        return command(self.remote, "git", *(("rev-parse", revision) if name
                                              else ("show", revision)))

    def changed(self, start):
        """The files the pushed revert changes against `start`."""
        return command(self.remote, "git", "diff", "--no-renames", "--name-only", start,
                       self.pushes[0]["head"]).splitlines()

    KEEP = f"Keep docs/decisions/ and {PAGE} as at"

    def test_decision_entries_and_the_page_are_kept(self):
        # The record is history, only ever added to: the revert keeps the folder and the
        # page as at the failed push; all else is reverted.
        self.entries_landed()
        entry = "- **A train's decision.** Kept as history.\n"
        page = self.PAGE_TEXT + "- **A page line.**\n"
        merge = self.train_files(11, {"chapter.txt": "Changed chapter.\n", self.ENTRY: entry,
                                      self.PAGE: page})
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.pushed("chapter.txt"), "Original chapter.")
        self.assertEqual(self.pushed(self.ENTRY), entry.strip())
        self.assertEqual(self.pushed(self.PAGE), page.strip())
        for path in ("docs/decisions", self.PAGE):
            self.assertEqual(self.pushed(path, name=True),
                             self.git("rev-parse", f"{merge}:{path}"))
        self.assertEqual(self.changed(merge), ["chapter.txt"])
        self.assertIn(f"{self.KEEP} {merge[:12]}", self.pushes[0]["subjects"])
        self.assertIn("was enqueued", self.body())

    def test_without_entries_the_page_is_still_kept(self):
        # No folder: the page alone is kept, and no folder is made.
        page = "# Decisions\n\n- **An earlier decision.**\n"
        self.write(self.PAGE, page)
        self.commit("The decisions page")
        self.before = self.rev()
        merge = self.train_files(11, {"chapter.txt": "Changed chapter.\n",
                                      self.PAGE: page + "- **A page line.**\n"})
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.changed(merge), ["chapter.txt"])
        self.assertEqual(self.changed(self.before), [self.PAGE])
        self.assertIn(self.KEEP, self.pushes[0]["subjects"])

    def keeps_the_page_whole(self, before, after):
        """The whole page is kept: comments of the shape an earlier design gave a region of
        it change nothing."""
        self.entries_landed(self.PAGE_TEXT + before)
        merge = self.train_files(11, {"chapter.txt": "Changed chapter.\n",
                                      self.PAGE: self.PAGE_TEXT + after})
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.pushed(self.PAGE, name=True),
                         self.git("rev-parse", f"{merge}:{self.PAGE}"))
        self.assertEqual(self.changed(merge), ["chapter.txt"])
        self.assertIn(self.KEEP, self.pushes[0]["subjects"])

    BEGIN, END = "<!-- decisions:entries begin -->", "<!-- decisions:entries end -->"

    def test_paired_region_comments_in_the_page_change_nothing(self):
        self.keeps_the_page_whole(f"{self.BEGIN}\n{self.END}\n",
                                  f"{self.BEGIN}\n- **A train's line.**\n{self.END}\n")

    def test_a_lone_region_comment_in_the_page_changes_nothing(self):
        self.keeps_the_page_whole(f"{self.END}\n", f"- **A train's line.**\n{self.END}\n")

    def test_a_push_that_leaves_the_entries_alone_reverts_exactly(self):
        self.entries_landed()
        self.train_files(11, {"chapter.txt": "Changed chapter.\n"})
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.pushes[0]["tree"], self.git("rev-parse", self.before + "^{tree}"))
        self.assertNotIn("Keep docs/decisions/", self.pushes[0]["subjects"])

    def test_without_entries_nothing_changes(self):
        self.train()
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.pushes[0]["tree"], self.git("rev-parse", self.before + "^{tree}"))
        self.assertNotIn("Keep docs/decisions/", self.pushes[0]["subjects"])

    def test_push_refuses_every_branch_outside_the_revert_format(self):
        branches = ["main", "train/test", "refs/heads/revert/123456789abc",
                    "revert/", "revert/123456789ab", "revert/123456789abcd",
                    "revert/123456789abg", "revert/123456789ABC", "revert/123456789abc/extra",
                    "revert/123456789abc\n", "revert/123456789abc:main"]
        for branch in branches:
            with self.subTest(branch=branch), mock.patch.object(ar, "git") as git:
                with self.assertRaisesRegex(ar.Refusal, "revert/<12 lower-case hex digits>"):
                    ar.push_branch(self.repo, SLUG, branch, APP_TOKEN)
                git.assert_not_called()

    def test_without_app_secrets_issue_only_says_why(self):
        self.train()
        status, output = self.run_revert(env={"GITHUB_TOKEN": WORKFLOW_TOKEN})
        self.assert_issue_only(status)
        self.assertIn("not both set", self.body())
        self.assertIn("no automatic revert", self.body())
        self.assertNotIn("was enqueued", output)
        self.assertIsNone(self.api.jwt)

    def test_one_missing_app_secret_also_refuses(self):
        self.train()
        env = self.env.copy()
        del env["STOICHEIA_REVERT_APP_KEY"]
        status, _ = self.run_revert(env=env)
        self.assert_issue_only(status)

    def test_non_merge_anywhere_in_chain_means_issue_only(self):
        self.write("chapter.txt", "Direct main commit.\n")
        self.commit("Not a train")
        self.train(text="Train after a direct commit.\n")
        status, _ = self.run_revert()
        self.assert_issue_only(status)
        self.assertIn("non-merge", self.body())

    def test_before_on_second_parent_is_not_a_first_parent_base(self):
        self.train()
        status, _ = self.run_revert(before=self.api.pulls[11]["head"]["sha"])
        self.assert_issue_only(status)
        self.assertIn("first-parent", self.body())

    def test_missing_before_commit_means_issue_only(self):
        self.train()
        status, _ = self.run_revert(before="f" * 40)
        self.assert_issue_only(status)
        self.assertIn("git rev-parse failed", self.body())

    def test_revert_conflict_opens_issue_without_push_or_pull_request(self):
        self.train()
        original = ar.git
        injected = False

        def conflicting(repo, *args, **kwargs):
            nonlocal injected
            if "revert" in args and not injected:
                injected = True
                (repo / "chapter.txt").write_text("A conflicting local revision.\n",
                                                  encoding="utf-8")
                original(repo, "add", "chapter.txt")
                original(repo, "commit", "-m", "A concurrent local change")
            return original(repo, *args, **kwargs)

        with mock.patch.object(ar, "git", side_effect=conflicting):
            status, _ = self.run_revert()
        self.assertTrue(injected)
        self.assert_issue_only(status)
        self.assertIn("did not apply cleanly", self.body())
        self.assertIn("no pull request opened", self.body())
        self.assertIsNone(self.api.jwt)

    def test_labels_include_kinds_and_protected_path(self):
        self.train(path="scripts/check.py", text="print('check')\n",
                   labels=("tooling", "docs", "unrelated"))
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(set(self.api.pr["labels"]),
                         {"auto-revert", "tooling", "docs", "security-review"})
        self.assertEqual(self.api.issues[1000]["labels"], ["blocks-release", "main-red"])
        self.assertEqual(set(self.api.labels),
                         {"blocks-release", "main-red", "auto-revert", "tooling", "docs",
                          "security-review"})

    def test_a_workflow_revert_is_left_to_the_coordinator(self):
        # The job's token cannot push a workflow change and the App writes no contents.
        self.train(path=".github/workflows/example.yml", text="name: Example\n",
                   labels=("tooling",))
        status, output = self.run_revert()
        self.assertEqual(status, 1, output)
        self.assertEqual(self.pushes, [])
        self.assertIsNone(self.api.issued_permissions)
        self.assertIn("revert it by hand", self.body())

    LINKED = "scripts/audit/tool.py"

    def test_a_revert_that_would_break_a_kept_link_is_left_to_the_coordinator(self):
        # The kept page links to a file the train added, which the revert deletes: the
        # revert's own check_links.py step would fail, so nothing is pushed.
        self.entries_landed()
        page = self.PAGE_TEXT + f"- **A tool.** See [the tool](../../{self.LINKED}).\n"
        entry = f"- **An entry.** [The tool](../../{self.LINKED}#L1).\n"
        self.train_files(11, {self.LINKED: "print('tool')\n", self.PAGE: page,
                              self.ENTRY: entry}, labels=("tooling",))
        status, output = self.run_revert()
        self.assert_issue_only(status)
        self.assertIsNone(self.api.issued_permissions)
        body = self.body()
        self.assertIn(f"- {self.PAGE}:6: ../../{self.LINKED}\n", body)
        self.assertIn(f"- {self.ENTRY}:1: ../../{self.LINKED}#L1\n", body)
        self.assertIn("Revert it by hand, mending each link", body)
        self.assertIn("No branch pushed and no pull request opened.", body)

    def test_a_kept_link_to_a_heading_or_lines_the_revert_takes_away_is_named(self):
        self.write("docs/guide.md", "# Guide\n\nThe guide.\n")
        self.write("notes.txt", "One.\n")
        self.entries_landed()
        page = (self.PAGE_TEXT + "- [A part](../guide.md#a-new-part).\n"
                "- [Line three](../../notes.txt#L3).\n")
        self.train_files(11, {"docs/guide.md": "# Guide\n\nThe guide.\n\n## A new part\n",
                              "notes.txt": "One.\nTwo.\nThree.\n", self.PAGE: page})
        status, _ = self.run_revert()
        self.assert_issue_only(status)
        self.assertIn(f"- {self.PAGE}:6: ../guide.md#a-new-part\n", self.body())
        self.assertIn(f"- {self.PAGE}:7: ../../notes.txt#L3\n", self.body())

    def test_kept_links_that_still_resolve_or_were_already_broken_are_pushed(self):
        # A link the revert leaves resolving, one broken before it, a web address, and a
        # link in code (which check_links.py does not read) stop nothing.
        self.write("docs/guide.md", "# Guide\n\n## A part\n")
        self.entries_landed()
        page = (self.PAGE_TEXT + "- [Chapter](../../chapter.txt), [part](../guide.md#a-part),"
                " [folder](../decisions/), [root](/), [gone](../../never-there.md),"
                " [web](https://example.invalid/x).\n"
                f"- `[code](../../{self.LINKED})`\n\n```\n[fenced](../../{self.LINKED})\n```\n")
        self.train_files(11, {"chapter.txt": "Changed chapter.\n", self.LINKED: "print(1)\n",
                              "docs/guide.md": "# Guide\n\n## A part\n\nMore.\n",
                              self.PAGE: page}, labels=("tooling",))
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.pushed(self.PAGE), page.strip())
        self.assertIn("was enqueued", self.body())

    def test_the_link_reading_is_check_links_own(self):
        # The trusted script imports no repository code, so it holds a copy of
        # check_links.py's reading: the two must read every link and anchor alike.
        import check_links
        for name in ("SCHEME", "LINE_ANCHOR", "FENCE", "ATX", "SETEXT", "COMMENT",
                     "LINK_TEXT", "REF_DEF", "HTML_URL", "HTML_ANCHOR"):
            with self.subTest(pattern=name):
                self.assertEqual(getattr(ar, name).pattern, getattr(check_links, name).pattern)
                self.assertEqual(getattr(ar, name).flags, getattr(check_links, name).flags)
        for path in ("docs/briefs/0002-decisions.md", "docs/WORKFLOW.md", "README.md",
                     "docs/STYLE.md", "CONTRIBUTING.md"):
            with self.subTest(path=path):
                text = ar.markdown((ROOT / path).read_bytes())
                self.assertEqual(list(ar.links(text)), list(check_links.links(ROOT / path)))
                self.assertEqual(ar.anchors(text), check_links.anchors(ROOT / path))
        for target in ("../x.md", "https://example.invalid", "//host/x", "mailto:a", "",
                       " #top", "C:/x"):
            self.assertEqual(ar.relative(target), check_links.relative(target), target)

    def test_reverts_read_merge_attributes_from_before(self):
        # Never from the tree being reverted, which the failed push wrote.
        self.train()
        self.train(12, text="Second chapter revision.\n")
        calls, original = [], ar.git

        def recording(repo, *args, **kwargs):
            calls.append(args)
            return original(repo, *args, **kwargs)

        with mock.patch.object(ar, "git", side_effect=recording):
            status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        reverts = [args for args in calls if "revert" in args]
        self.assertEqual(len(reverts), 2)
        for args in reverts:
            self.assertEqual(args[:2], (f"--attr-source={self.before}", "revert"))

    def test_an_enqueued_revert_whose_issue_is_not_updated_says_both(self):
        self.train()
        self.api.broken = lambda method, path, token, data: method == "PATCH"
        status, output = self.run_revert()
        self.assertEqual(status, 3, output)
        self.assertIsNotNone(self.api.queue)
        self.assertIn("Revert pull request #2000 was enqueued", output)
        self.assertIn("Issue #1000 was not updated with this outcome", output)
        for secret in (WORKFLOW_TOKEN, APP_TOKEN):
            self.assertNotIn(secret, output)

    def test_an_unrecorded_outcome_without_an_enqueue_is_exit_2(self):
        self.train()
        self.api.broken = lambda method, path, token, data: method == "PATCH" or (
            path == "/graphql")
        status, output = self.run_revert()
        self.assertEqual(status, 2, output)
        self.assertIn("enqueueing is not confirmed", output)
        self.assertIn("Issue #1000 was not updated with this outcome", output)

    def test_tokens_and_private_key_are_never_printed(self):
        self.train()
        self.api.broken = lambda method, path, token, data: path == "/graphql"
        status, output = self.run_revert()
        self.assertEqual(status, 1, output)
        for secret in (WORKFLOW_TOKEN, APP_TOKEN, self.key, self.api.jwt):
            self.assertNotIn(secret, output)
            self.assertNotIn(secret, self.body())
        self.assertIn("enqueueing is not confirmed", self.body())

    def test_app_jwt_is_signed_with_rs256(self):
        self.train()
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        header, claims, signature = self.api.jwt.split(".")

        def decoded(value):
            return base64.urlsafe_b64decode(value + "=" * (-len(value) % 4))

        self.assertEqual(json.loads(decoded(header)), {"alg": "RS256", "typ": "JWT"})
        data = json.loads(decoded(claims))
        self.assertEqual(data["iss"], "1234")
        self.assertEqual(data["exp"] - data["iat"], 600)
        public = self.directory / "public.pem"
        command(self.directory, "openssl", "rsa", "-in", str(Path(self.keys.name) / "key.pem"),
                "-pubout", "-out", str(public))
        signed = self.directory / "signature"
        signed.write_bytes(decoded(signature))
        payload = self.directory / "payload"
        payload.write_bytes(f"{header}.{claims}".encode())
        self.assertIn("Verified OK", command(self.directory, "openssl", "dgst", "-sha256",
                                             "-verify", str(public), "-signature", str(signed),
                                             str(payload)))

    def test_http_failure_leaves_an_issue_and_no_revert(self):
        self.train()
        self.api.broken = lambda method, path, token, data: "/pulls/" in path
        status, _ = self.run_revert()
        self.assert_issue_only(status)
        self.assertIn("GitHub could not complete", self.body())

    def test_unreadable_pull_request_metadata_refuses(self):
        self.train()
        self.api.pulls[11]["head"] = None
        status, _ = self.run_revert()
        self.assert_issue_only(status)
        self.assertIn("metadata could not be read", self.body())

    def test_missing_kind_label_refuses(self):
        self.train(labels=("unrelated",))
        status, _ = self.run_revert()
        self.assert_issue_only(status)
        self.assertIn("no kind label", self.body())

    def test_issue_creation_failure_prevents_app_activity(self):
        self.train()
        self.api.broken = lambda method, path, token, data: (method == "POST"
                                                             and path.endswith("/issues"))
        status, output = self.run_revert()
        self.assertEqual(status, 2, output)
        self.assertEqual(self.pushes, [])
        self.assertIsNone(self.api.jwt)

    def test_main_moving_refuses_to_push(self):
        self.train()
        self.api.after = self.before
        status, _ = self.run_revert()
        self.assert_issue_only(status)
        self.assertIn("Main has moved", self.body())

    def test_graphql_errors_never_count_as_enqueued(self):
        self.train()

        def http(method, path, token, data):
            if path == "/graphql":
                return {"errors": [{"message": APP_TOKEN}]}
            return self.api(method, path, token, data)

        status, output = self.run_revert(http=http)
        self.assertEqual(status, 1, output)
        self.assertIn("GraphQL error", self.body())
        self.assertNotIn(APP_TOKEN, output)

    def test_missing_queue_entry_never_counts_as_enqueued(self):
        self.train()

        def http(method, path, token, data):
            if path == "/graphql":
                return {"data": {"enqueuePullRequest": None}}
            return self.api(method, path, token, data)

        status, _ = self.run_revert(http=http)
        self.assertEqual(status, 1)
        self.assertIn("did not confirm the queue entry", self.body())

    def test_pr_head_must_equal_pushed_head_before_enqueue(self):
        self.train()

        def http(method, path, token, data):
            response = self.api(method, path, token, data)
            if method == "POST" and path.endswith("/pulls"):
                response["head"]["sha"] = self.before
            return response

        status, _ = self.run_revert(http=http)
        self.assertEqual(status, 1)
        self.assertIsNone(self.api.queue)
        self.assertIn("did not confirm", self.body())

    def test_dry_run_lists_actions_without_http_push_or_changes(self):
        merge = self.train()
        status, output = self.run_revert("--dry-run")
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.calls, [])
        self.assertEqual(self.pushes, [])
        self.assertEqual(self.rev(), merge)
        self.assertEqual(self.git("status", "--porcelain"), "")
        for text in ("git revert", "openssl", "expectedHeadOid", "security-review",
                     "blocks-release", "main-red", "revert/" + merge[:12]):
            self.assertIn(text, output)
        self.assertNotIn(self.key, output)

    def test_push_authentication_is_not_in_arguments_or_config_files(self):
        calls = []

        def capture(repo, *args, env):
            calls.append((args, env))
            raise ar.Refusal("git push failed.")

        with mock.patch.object(ar, "git", side_effect=capture), self.assertRaises(ar.Refusal):
            ar.push_branch(self.repo, SLUG, "revert/123456789abc", APP_TOKEN)
        args, env = calls[0]
        self.assertNotIn(APP_TOKEN, " ".join(args))
        self.assertEqual(args[-1], "HEAD:refs/heads/revert/123456789abc")
        self.assertEqual(env["GIT_CONFIG_KEY_0"], "http.https://github.com/.extraheader")
        self.assertNotIn(APP_TOKEN, self.git("config", "--local", "--list"))

    def test_protected_paths_match_safe_push_without_importing_it(self):
        # The duplicated protected-path policy is an explicit contract: the trusted
        # script cannot import the failed revision's safe_push.py to classify it.
        tree = ast.parse((ROOT / "scripts/safe_push.py").read_text(encoding="utf-8"))
        values = {}
        for node in tree.body:
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name) and target.id in {
                            "PROTECTED", "PROTECTED_JUDGED", "KIND_LABELS", "DECISIONS"}:
                        values[target.id] = ast.literal_eval(node.value)
        self.assertEqual(ar.PROTECTED, values["PROTECTED"] + values["PROTECTED_JUDGED"])
        self.assertEqual(ar.KINDS, set(values["KIND_LABELS"]))
        # So is the decisions page, which a revert keeps.
        self.assertEqual(ar.DECISIONS, values["DECISIONS"])
        for prefix in values["PROTECTED"] + values["PROTECTED_JUDGED"]:
            self.assertTrue(ar.protected(prefix + "example.py" if prefix.endswith("/")
                                         else prefix))
            self.assertFalse(ar.protected("unprotected/" + prefix))
        self.assertFalse(ar.protected("scripts-lookalike/example.py"))
        self.assertFalse(ar.protected("lean-toolchain.notes"))

    def run_clear(self, *extra):
        output = io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            status = ar.main(["--clear", "--repo", SLUG, *extra],
                             http=self.api, env={"GITHUB_TOKEN": WORKFLOW_TOKEN},
                             repo_dir=self.repo)
        return status, output.getvalue()

    @staticmethod
    def open_issue(number, **extra):
        return {"number": number, "state": "open",
                "labels": [{"name": "main-red"}, {"name": "blocks-release"}], **extra}

    @classmethod
    def failure_issue(cls, number, after):
        return cls.open_issue(number, body=f"Main failed.\n\nAfter: {after}\n")

    def test_clear_removes_only_main_red_from_open_issues(self):
        self.api.open_issues = [self.open_issue(4), self.open_issue(5),
                                self.open_issue(6, pull_request={})]
        status, output = self.run_clear()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.deleted, [4, 5])
        self.assertTrue(all(token == WORKFLOW_TOKEN for _, _, token, _ in self.api.calls))
        self.assertTrue(all(method in {"GET", "DELETE"} for method, _, _, _ in self.api.calls))
        self.assertIn("blocks-release and the issue remain", output)

    def test_clear_reads_every_page_before_removing_any_label(self):
        root = f"/repos/{SLUG}/issues?state=open&labels=main-red&per_page=100&page="
        self.api.pages["GET", root + "1"] = [self.open_issue(n) for n in range(1, 101)]
        self.api.pages["GET", root + "2"] = [self.open_issue(101)]
        status, output = self.run_clear()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.deleted, list(range(1, 102)))
        self.assertEqual([call[0] for call in self.api.calls[:3]], ["GET", "GET", "DELETE"])

    def test_clear_empty_list_succeeds(self):
        status, output = self.run_clear()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.deleted, [])

    def test_clear_unreadable_page_removes_nothing(self):
        self.api.open_issues = [self.open_issue(4), {"number": 5}]
        status, output = self.run_clear()
        self.assertEqual(status, 2, output)
        self.assertEqual(self.api.deleted, [])

    @staticmethod
    def run_of(number, sha, **extra):
        return {"id": number, "head_sha": sha, "head_branch": "main", "event": "push",
                "path": ".github/workflows/post-merge.yml", **extra}

    def unreadable_runs(self, later):
        """GitHub's answers that name no post-merge run for later; None is a refusal."""
        return {
            "refused": None,
            "not an object": [],
            "no list": {"workflow_runs": None},
            "an unreadable run": {"workflow_runs": [self.run_of(9, later), "run"]},
            "no run yet": {"total_count": 0, "workflow_runs": []},
            "only another commit's": {"workflow_runs": [self.run_of(11, "c" * 40)]},
            "an unreadable id": {"workflow_runs": [self.run_of(9, later),
                                                   self.run_of(True, later)]},
            "a zero id": {"workflow_runs": [self.run_of(0, later)]},
        }

    def test_clear_old_success_does_not_clear_new_main(self):
        # Main has moved on: its tip, read afresh, is another commit, so the run that
        # passed is not failed, no label changes, and the later push's run is named.
        later = "b" * 40
        runs = (f"/repos/{SLUG}/actions/workflows/post-merge.yml/runs?head_sha={later}"
                "&event=push&branch=main&per_page=100")
        self.api.after = later
        self.api.pages["GET", runs] = {"total_count": 4, "workflow_runs": [
            self.run_of(7, later), self.run_of(9, later), self.run_of(11, "c" * 40),
            self.run_of(12, later, head_branch="other")]}
        self.api.open_issues = [self.open_issue(4)]
        status, output = self.run_clear("--after", "a" * 40)
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.deleted, [])
        self.assertIn(f"Main has moved on from {'a' * 40} to {later}: the later push's "
                      f"post-merge run 9, https://github.com/{SLUG}/actions/runs/9, decides, "
                      "and no label was changed.", output)
        self.assertEqual([(method, path) for method, path, _, _ in self.api.calls],
                         [("GET", f"/repos/{SLUG}/git/ref/heads/main"), ("GET", runs)])

    def test_clear_when_main_has_moved_names_its_commit_if_no_run_can_be_read(self):
        later = "b" * 40
        runs = (f"/repos/{SLUG}/actions/workflows/post-merge.yml/runs?head_sha={later}"
                "&event=push&branch=main&per_page=100")
        for name, answer in self.unreadable_runs(later).items():
            with self.subTest(name):
                self.api = GitHub()
                self.api.after = later
                self.api.open_issues = [self.open_issue(4)]
                if answer is None:
                    self.api.broken = lambda method, path, token, data: path == runs
                else:
                    self.api.pages["GET", runs] = answer
                status, output = self.run_clear("--after", "a" * 40)
                self.assertEqual(status, 0, output)
                self.assertEqual(self.api.deleted, [])
                self.assertIn(f"Main has moved on from {'a' * 40} to {later}: no post-merge "
                              f"run for {later} could be read yet; the later push's run "
                              "decides, and no label was changed.", output)
                self.assertNotIn(WORKFLOW_TOKEN, output)

    def test_clear_failing_at_main_s_own_tip_fails_and_removes_nothing(self):
        # The opposite of a moved main: main's tip is the run's commit, so a clear that
        # fails fails, removes no label and never reads as main having moved on.
        root = f"/repos/{SLUG}"
        after = self.rev()
        failures = {
            "an unreadable issue": ([self.open_issue(4), {"number": 5}], None),
            "a refused issue list": (
                [self.open_issue(4)],
                lambda method, path, token, data: path.startswith(root + "/issues?")),
            "a refused removal": (
                [self.failure_issue(4, after), self.failure_issue(5, after)],
                lambda method, path, token, data: method == "DELETE"),
        }
        for name, (issues, broken) in failures.items():
            with self.subTest(name):
                self.api = GitHub()
                self.api.after = after
                self.api.open_issues = issues
                self.api.broken = broken
                status, output = self.run_clear("--after", after)
                self.assertEqual(status, 2, output)
                self.assertEqual(self.api.deleted, [])
                self.assertNotIn("moved on", output)
                self.assertFalse(any("/actions/" in path for _, path, _, _ in self.api.calls))
                # A refused removal is the last: no other issue's label is tried.
                self.assertIn(
                    [path for method, path, _, _ in self.api.calls if method == "DELETE"],
                    ([], [f"{root}/issues/4/labels/main-red"]))

    def test_clear_after_removes_ancestor_issue_but_keeps_newer_and_unreadable_issues(self):
        after = self.rev()
        self.git("switch", "-c", "newer-failure")
        self.write("chapter.txt", "A newer failed revision.\n")
        self.commit("Newer failed revision")
        newer = self.rev()
        self.git("switch", "main")
        self.api.after = after
        self.api.open_issues = [self.failure_issue(4, after), self.failure_issue(5, newer),
                                self.open_issue(6)]
        status, output = self.run_clear("--after", after)
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.deleted, [4])
        self.assertIn("Issue #5 keeps main-red", output)
        self.assertIn("Issue #6 keeps main-red", output)

    def test_clear_rechecks_main_before_removing_a_label(self):
        after = self.rev()
        self.git("switch", "-c", "later-main")
        self.write("chapter.txt", "Later main.\n")
        self.commit("Later main")
        later = self.rev()
        self.git("switch", "main")
        self.api.tip_reads = [after, later]
        self.api.open_issues = [self.failure_issue(4, after)]
        status, output = self.run_clear("--after", after)
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.deleted, [])
        self.assertIn(f"Main has moved on from {after} to {later}", output)

    def test_clear_with_main_s_tip_unreadable_removes_nothing(self):
        self.api.open_issues = [self.open_issue(4)]
        for tip in ("", "b" * 39, None):
            with self.subTest(tip=tip):
                self.api.after = tip
                status, output = self.run_clear("--after", "a" * 40)
                self.assertEqual(status, 2, output)
                self.assertIn("Main's tip could not be read", output)
                self.assertEqual(self.api.deleted, [])

    def run_clear_step(self, tip, *, after=None, issues=None, runs=None, refused=(),
                       tip_reads=None):
        """The clear job's step, run as the workflow runs it, with a stand-in for gh: the
        step's output, its exit and the labels it removed. runs is GitHub's answer for
        the post-merge runs at tip, None a refusal; refused names the other operations
        refused, "issues" or "delete"."""
        script = workflow_step("post-merge.yml",
                               "Clear main-red after successful integration of the current main")
        directory = self.directory / "clear-bin"
        directory.mkdir(exist_ok=True)
        state = self.directory / "clear-state.json"
        state.write_text(json.dumps({"tip": tip, "tips": tip_reads or [tip],
                                     "issues": issues or [[]], "runs": runs,
                                     "refused": list(refused), "deleted": []}),
                         encoding="utf-8")
        gh = directory / "gh"
        gh.write_text(f"#!{sys.executable}\n" + textwrap.dedent('''\
            import json
            import os
            import sys
            from pathlib import Path

            args = sys.argv[1:]
            root = "repos/" + os.environ["REPOSITORY"]
            path = Path(os.environ["CLEAR_STATE"])
            state = json.loads(path.read_text())
            if args == ["api", root + "/git/ref/heads/main", "--jq", ".object.sha"]:
                tip = state["tips"].pop(0) if len(state["tips"]) > 1 else state["tips"][0]
                state["tip"] = tip
                path.write_text(json.dumps(state))
                if tip is None:
                    sys.exit(1)
                print(tip)
            elif args == ["api", root + "/actions/workflows/post-merge.yml/runs?head_sha="
                          + str(state["tip"]) + "&event=push&branch=main&per_page=100"]:
                if state["runs"] is None:
                    sys.exit(1)
                print(json.dumps(state["runs"]))
            elif args == ["api", "--paginate", "--slurp",
                          root + "/issues?state=open&labels=main-red&per_page=100"]:
                if "issues" in state["refused"]:
                    sys.exit(1)
                print(json.dumps(state["issues"]))
            elif args[:3] == ["api", "--method", "DELETE"]:
                if "delete" in state["refused"]:
                    sys.exit(1)
                state["deleted"].append(args[3])
                path.write_text(json.dumps(state))
                print(json.dumps([{"name": "blocks-release"}]))
            else:
                raise AssertionError("Unexpected gh operation: " + repr(args))
            '''), encoding="utf-8")
        gh.chmod(0o755)
        env = ar.git_env()
        env.update(PATH=str(directory) + ":" + env["PATH"], REPOSITORY=SLUG,
                   AFTER=after or "a" * 40,
                   RUNS_URL=f"https://github.com/{SLUG}/actions/runs",
                   RUNNER_TEMP=str(self.directory), CLEAR_STATE=str(state))
        result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script],
                                cwd=self.repo, env=env, text=True, capture_output=True,
                                check=False)
        deleted = json.loads(state.read_text(encoding="utf-8"))["deleted"]
        return result.stdout + result.stderr, result.returncode, deleted

    def test_workflow_clear_changes_nothing_and_passes_when_main_has_moved(self):
        later = "b" * 40
        issues = [[self.open_issue(4)]]
        runs = {"total_count": 4, "workflow_runs": [
            self.run_of(7, later), self.run_of(9, later), self.run_of(11, "c" * 40),
            self.run_of(12, later, head_branch="other")]}
        output, code, deleted = self.run_clear_step(later, issues=issues, runs=runs)
        self.assertEqual(code, 0, output)
        self.assertEqual(deleted, [])
        self.assertIn(f"Main has moved on from {'a' * 40} to {later}: the later push's "
                      f"post-merge run 9, https://github.com/{SLUG}/actions/runs/9, decides, "
                      "and no label was changed.", output)
        after = self.rev()
        output, code, deleted = self.run_clear_step(
            after, after=after, issues=[[self.failure_issue(4, after)]], runs=runs)
        self.assertEqual(code, 0, output)
        self.assertEqual(deleted, [f"repos/{SLUG}/issues/4/labels/main-red"])
        self.assertNotIn("moved on", output)

    def test_workflow_clear_when_main_has_moved_names_its_commit_if_no_run_can_be_read(self):
        later = "b" * 40
        for name, runs in self.unreadable_runs(later).items():
            with self.subTest(name):
                output, code, deleted = self.run_clear_step(
                    later, issues=[[self.open_issue(4)]], runs=runs)
                self.assertEqual(code, 0, output)
                self.assertEqual(deleted, [])
                self.assertIn(f"Main has moved on from {'a' * 40} to {later}: no post-merge "
                              f"run for {later} could be read yet; the later push's run "
                              "decides, and no label was changed.", output)

    def test_workflow_clear_fails_at_main_s_own_tip_and_removes_nothing(self):
        # The opposite of a moved main: main's tip is the run's commit, so a clear that
        # fails fails the job, removes no label and never reads as main having moved on.
        after = self.rev()
        failures = {
            "an unreadable issue": ([[self.open_issue(4), {"number": 5}]], ()),
            "a refused issue list": ([[self.open_issue(4)]], ("issues",)),
            "a refused removal": (
                [[self.failure_issue(4, after), self.failure_issue(5, after)]], ("delete",)),
        }
        for name, (issues, refused) in failures.items():
            with self.subTest(name):
                output, code, deleted = self.run_clear_step(
                    after, after=after, issues=issues, refused=refused,
                    runs={"workflow_runs": [self.run_of(9, after)]})
                self.assertNotEqual(code, 0, output)
                self.assertEqual(deleted, [])
                self.assertNotIn("moved on", output)

    def test_workflow_clear_removes_ancestor_issue_but_keeps_newer_and_unreadable_issues(self):
        after = self.rev()
        self.git("switch", "-c", "newer-workflow-failure")
        self.write("chapter.txt", "A newer workflow failure.\n")
        self.commit("Newer workflow failure")
        newer = self.rev()
        self.git("switch", "main")
        issues = [[self.failure_issue(4, after), self.failure_issue(5, newer),
                   self.open_issue(6)]]
        output, code, deleted = self.run_clear_step(
            after, after=after, issues=issues, runs={"workflow_runs": []})
        self.assertEqual(code, 0, output)
        self.assertEqual(deleted, [f"repos/{SLUG}/issues/4/labels/main-red"])
        self.assertIn("Issue #5 keeps main-red", output)
        self.assertIn("Issue #6 keeps main-red", output)

    def test_workflow_clear_rechecks_main_before_removing_a_label(self):
        after = self.rev()
        self.git("switch", "-c", "later-workflow-main")
        self.write("chapter.txt", "Later workflow main.\n")
        self.commit("Later workflow main")
        later = self.rev()
        self.git("switch", "main")
        runs = {"workflow_runs": [self.run_of(9, later)]}
        output, code, deleted = self.run_clear_step(
            after, after=after, issues=[[self.failure_issue(4, after)]], runs=runs,
            tip_reads=[after, later])
        self.assertEqual(code, 0, output)
        self.assertEqual(deleted, [])
        self.assertIn(f"Main has moved on from {after} to {later}", output)

    def test_workflow_clear_fails_when_main_s_tip_is_unreadable(self):
        for tip in (None, "", "not a commit"):
            with self.subTest(tip=tip):
                output, code, deleted = self.run_clear_step(tip, issues=[[self.open_issue(4)]])
                self.assertNotEqual(code, 0, output)
                self.assertEqual(deleted, [])

    def test_clear_dry_run_never_contacts_github(self):
        status, output = self.run_clear("--dry-run")
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.calls, [])
        self.assertIn("DELETE main-red", output)

    def test_clear_unconfirmed_deletion_fails(self):
        self.api.open_issues = [self.open_issue(4)]
        self.api.pages["DELETE", f"/repos/{SLUG}/issues/4/labels/main-red"] = None
        status, output = self.run_clear()
        self.assertEqual(status, 2, output)
        self.assertIn("did not confirm clearing", output)

    def run_acceptance_event(self, name, data):
        script = workflow_step("ci.yml", "Identify main for this event")
        event = self.directory / "event.json"
        event.write_text(json.dumps(data), encoding="utf-8")
        output = self.directory / "github-env"
        output.write_text("", encoding="utf-8")
        env = ar.git_env()
        env.update(GITHUB_EVENT_NAME=name, GITHUB_EVENT_PATH=str(event), GITHUB_ENV=str(output))
        result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script],
                                cwd=self.repo, env=env, text=True, capture_output=True,
                                check=False)
        return result, output.read_text(encoding="utf-8")

    def test_acceptance_push_compares_with_before_not_last_merge_parent(self):
        first = self.train()
        after = self.train(12, text="Second revision.\n")
        result, output = self.run_acceptance_event(
            "push", {"before": self.before, "after": after, "ref": "refs/heads/main",
                     "deleted": False})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, f"MAIN_SHA={self.before}\n")
        self.assertNotIn(first, output)

    def test_acceptance_group_compares_with_group_base(self):
        self.train()
        after = self.train(12, text="Second revision.\n")
        result, output = self.run_acceptance_event(
            "merge_group", {"merge_group": {"head_sha": after, "base_sha": self.before,
                                            "base_ref": "refs/heads/main"}})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, f"MAIN_SHA={self.before}\n")

    def test_acceptance_pull_request_uses_checkout_first_parent(self):
        main = self.train()
        self.train(12, text="Second revision.\n")
        result, output = self.run_acceptance_event(
            "pull_request", {"pull_request": {"head": {"sha": self.api.pulls[12]["head"]["sha"]},
                                            "base": {"sha": self.before}}})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, f"MAIN_SHA={main}\n")

    def test_acceptance_unknown_missing_and_mismatched_events_fail_closed(self):
        after = self.train()
        cases = [
            ("workflow_call", {}),
            ("push", {"after": after, "ref": "refs/heads/main", "deleted": False}),
            ("push", {"before": "0" * 40, "after": after, "ref": "refs/heads/main",
                      "deleted": False}),
            ("push", {"before": self.before, "after": self.before, "ref": "refs/heads/main",
                      "deleted": False}),
            ("merge_group", {"merge_group": {"head_sha": after, "base_sha": self.before,
                                            "base_ref": "refs/heads/other"}}),
        ]
        for name, data in cases:
            with self.subTest(name=name, data=data):
                result, output = self.run_acceptance_event(name, data)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(output, "")

    def test_queue_does_not_pass_when_acceptance_failed_or_was_skipped(self):
        script = workflow_step("ci.yml", "Require a completed acceptance check")
        for status in ("success", "failure", "cancelled", "skipped", "", "unknown"):
            with self.subTest(status=status):
                env = ar.git_env()
                env["ACCEPTANCE_RESULT"] = status
                result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script],
                                        cwd=self.repo, env=env, capture_output=True, check=False)
                self.assertEqual(result.returncode == 0, status == "success",
                                 result.stderr.decode())

    @staticmethod
    def successful_run(before, **changes):
        return {"id": 98, "head_sha": before, "head_branch": "main", "event": "push",
                "path": ".github/workflows/post-merge.yml", "status": "completed",
                "conclusion": "success", **changes}

    def workflow_env(self, before, pages, *, unreadable=False):
        directory = self.directory / "bin"
        directory.mkdir(exist_ok=True)
        fixture = self.directory / "workflow-api.json"
        fixture.write_text(json.dumps({"pages": pages, "unreadable": unreadable}),
                           encoding="utf-8")
        gh = directory / "gh"
        gh.write_text(f"#!{sys.executable}\n" + textwrap.dedent('''\
            import json
            import os
            import sys
            from pathlib import Path

            args = sys.argv[1:]
            root = "repos/" + os.environ["REPOSITORY"]
            with open(os.environ["API_CALLS"], "a", encoding="utf-8") as calls:
                calls.write(json.dumps(args) + "\\n")
            query = root + "/actions/workflows/post-merge.yml/runs?head_sha=" + (
                os.environ["BEFORE"] + "&event=push&branch=main&per_page=100")
            if args == ["api", "--paginate", "--slurp", query]:
                fixture = json.loads(Path(os.environ["API_FIXTURE"]).read_text())
                if fixture["unreadable"]:
                    sys.exit(1)
                print(json.dumps(fixture["pages"]))
            elif args == ["api", "--paginate", root + "/labels?per_page=100", "--jq", ".[].name"]:
                print("blocks-release\\nmain-red")
            elif args == ["api", root + "/pulls/11", "--jq", ".title"]:
                print("Train 11")
            elif args[:4] == ["api", "--method", "POST", root + "/issues"]:
                payload = Path(args[args.index("--input") + 1]).read_text()
                Path(os.environ["ISSUE_PAYLOAD"]).write_text(payload)
                print("Opened issue #1000")
            else:
                raise AssertionError("Unexpected gh operation: " + repr(args))
            '''), encoding="utf-8")
        gh.chmod(0o755)
        output = self.directory / "github-output"
        output.write_text("", encoding="utf-8")
        (self.directory / "api-calls").write_text("", encoding="utf-8")
        jobs = self.directory / "failed-jobs"
        jobs.write_text("integration / check: failure\n", encoding="utf-8")
        env = ar.git_env()
        env.update(PATH=str(directory) + ":" + env["PATH"], BEFORE=before, AFTER=self.rev(),
                   RUNNER_TEMP=str(self.directory), GITHUB_OUTPUT=str(output), REPOSITORY=SLUG,
                   RUN_ID="99", RUN_URL=f"https://github.com/{SLUG}/actions/runs/99",
                   API_FIXTURE=str(fixture), API_CALLS=str(self.directory / "api-calls"),
                   ISSUE_PAYLOAD=str(self.directory / "issue.json"), FAILED_JOBS=str(jobs))
        return env

    def run_trusted_extraction(self, before, pages=None, *, unreadable=False):
        script = workflow_step("post-merge.yml", "Take the revert script from the previous main")
        if pages is None:
            pages = [{"total_count": 1, "workflow_runs": [self.successful_run(before)]}]
        env = self.workflow_env(before, pages, unreadable=unreadable)
        result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script],
                                cwd=self.repo, env=env, text=True, capture_output=True,
                                check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.trusted_outputs = dict(
            line.split("=", 1) for line in
            Path(env["GITHUB_OUTPUT"]).read_text(encoding="utf-8").splitlines())
        self.workflow_environment = env
        return self.trusted_outputs["script"]

    def assert_fallback_issue(self, reason):
        script = workflow_step(
            "post-merge.yml",
            "Open the issue when the trusted script or failed jobs are unavailable")
        env = self.workflow_environment.copy()
        env["TRUST_FAILURE"] = self.trusted_outputs["reason"]
        result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script],
                                cwd=self.repo, env=env, text=True, capture_output=True,
                                check=False)
        self.assertEqual(result.returncode, 1, result.stderr)
        payload = json.loads(Path(env["ISSUE_PAYLOAD"]).read_text(encoding="utf-8"))
        self.assertIn(reason, payload["body"])
        self.assertIn("Failed run: 99\n", payload["body"])
        self.assertIn("Issue only; no automatic revert or pull request was attempted.",
                      payload["body"])
        self.assertEqual(payload["labels"], ["blocks-release", "main-red"])
        calls = [json.loads(line) for line in Path(env["API_CALLS"]).read_text().splitlines()]
        self.assertEqual(sum(call[:3] == ["api", "--method", "POST"] for call in calls), 1)

    def test_workflow_executes_previous_main_script_despite_after_replacement(self):
        self.write("scripts/auto_revert.py", "print('Previous main script')\n")
        self.commit("Install trusted script")
        before = self.rev()
        self.train(path="scripts/auto_revert.py",
                   text="raise RuntimeError('Failed revision ran')\n")
        extracted = self.run_trusted_extraction(before)
        self.assertEqual(command(self.directory, sys.executable, "-I", extracted),
                         "Previous main script")
        self.assertEqual(self.trusted_outputs["reason"], "")

    def test_workflow_does_not_use_after_script_when_before_has_none(self):
        self.train(path="scripts/auto_revert.py",
                   text="raise RuntimeError('Failed revision ran')\n")
        self.assertEqual(self.run_trusted_extraction(self.before), "")
        self.assert_fallback_issue("no readable revert script")

    def test_workflow_refuses_before_without_a_successful_post_merge_run(self):
        self.write("scripts/auto_revert.py", "raise RuntimeError('Untrusted previous main ran')\n")
        self.commit("Install untrusted script")
        before = self.rev()
        good = self.successful_run(before)
        cases = [
            ([{"total_count": 0, "workflow_runs": []}], False, "No post-merge run"),
            ([{"total_count": 1, "workflow_runs": [dict(good, conclusion="failure")]}],
             False, "did not conclude success"),
            ([{"total_count": 1,
               "workflow_runs": [dict(good, status="in_progress", conclusion=None)]}],
             False, "did not conclude success"),
            ([{"total_count": 1, "workflow_runs": [good]}], True, "could not be read"),
            ([{"workflow_runs": [good]}], False, "could not be read"),
            ([], False, "could not be read"),
            ([{"total_count": 1, "workflow_runs": None}], False, "could not be read"),
            ([{"total_count": 2, "workflow_runs": [good]}], False, "could not be read"),
            ([{"total_count": 2, "workflow_runs": [good, good]}], False, "could not be read"),
            ([{"total_count": 1, "workflow_runs": [good]},
              {"total_count": 0, "workflow_runs": []}], False, "could not be read"),
            ([{"total_count": 1, "workflow_runs": [{key: value for key, value in good.items()
                                                   if key != "conclusion"}]}],
             False, "could not be read"),
        ]
        for pages, unreadable, reason in cases:
            with self.subTest(pages=pages, unreadable=unreadable):
                self.assertEqual(
                    self.run_trusted_extraction(before, pages, unreadable=unreadable), "")
                self.assert_fallback_issue(reason)

    def test_workflow_refuses_a_run_for_another_commit_branch_event_or_workflow(self):
        self.write("scripts/auto_revert.py", "print('Must not be trusted')\n")
        self.commit("Install script")
        before = self.rev()
        changes = [{"head_sha": "f" * 40}, {"head_branch": "topic"}, {"event": "pull_request"},
                   {"path": ".github/workflows/ci.yml"}, {"id": "98"}, {"id": 0},
                   {"id": 1.5}, {"id": True}, {"status": None}, {"conclusion": []}]
        for change in changes:
            with self.subTest(change=change):
                pages = [{"total_count": 1,
                          "workflow_runs": [self.successful_run(before, **change)]}]
                self.assertEqual(self.run_trusted_extraction(before, pages), "")
                self.assert_fallback_issue("could not be read")

    def test_workflow_uses_latest_run_across_all_pages(self):
        self.write("scripts/auto_revert.py", "print('Previous main script')\n")
        self.commit("Install script")
        before = self.rev()
        good = self.successful_run(before)
        for conclusion in ("failure", "success"):
            with self.subTest(conclusion=conclusion):
                pages = [{"total_count": 2, "workflow_runs": [good]},
                         {"total_count": 2,
                          "workflow_runs": [dict(good, id=99, conclusion=conclusion)]}]
                extracted = self.run_trusted_extraction(before, pages)
                if conclusion == "failure":
                    self.assertEqual(extracted, "")
                    self.assert_fallback_issue("did not conclude success")
                else:
                    self.assertEqual(command(self.directory, sys.executable, "-I", extracted),
                                     "Previous main script")

    def test_workflow_refuses_an_invalid_previous_commit(self):
        for before in ("0" * 40, "invalid", "a" * 39):
            with self.subTest(before=before):
                self.assertEqual(self.run_trusted_extraction(before), "")
                self.assert_fallback_issue("previous main commit is invalid")


if __name__ == "__main__":
    unittest.main()
