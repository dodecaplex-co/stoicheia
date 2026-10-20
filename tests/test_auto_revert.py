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
        no_http = mock.patch.object(ar, "request", side_effect=AssertionError("Real HTTP is forbidden"))
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
        self.assertEqual(token, APP_TOKEN)
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
        self.assertIn("https://github.com/owner/edition/actions/runs/99", self.api.pr["body"])
        self.assertIn(f"#11: Train 11 (merge `{merge}`)", self.body())
        self.assertIn("integration / model: failure", self.body())
        self.assertIn("was enqueued", self.body())
        self.assertEqual(self.rev(), merge)
        self.assertEqual(self.git("status", "--porcelain"), "")
        self.assertEqual(self.api.issued_permissions, {"contents": "write", "pull_requests": "write"})

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
            if args[0] == "revert" and not injected:
                injected = True
                (repo / "chapter.txt").write_text("A conflicting local revision.\n", encoding="utf-8")
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
                         {"blocks-release", "main-red", "auto-revert", "tooling", "docs", "security-review"})

    def test_workflow_revert_requests_workflow_permission(self):
        self.train(path=".github/workflows/example.yml", text="name: Example\n", labels=("tooling",))
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.issued_permissions["workflows"], "write")

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
                                             "-verify", str(public), "-signature", str(signed), str(payload)))

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
        self.api.broken = lambda method, path, token, data: method == "POST" and path.endswith("/issues")
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
                    if isinstance(target, ast.Name) and target.id in {"PROTECTED", "PROTECTED_JUDGED", "KIND_LABELS"}:
                        values[target.id] = ast.literal_eval(node.value)
        self.assertEqual(ar.PROTECTED, values["PROTECTED"] + values["PROTECTED_JUDGED"])
        self.assertEqual(ar.KINDS, set(values["KIND_LABELS"]))
        for prefix in values["PROTECTED"] + values["PROTECTED_JUDGED"]:
            self.assertTrue(ar.protected(prefix + "example.py" if prefix.endswith("/") else prefix))
            self.assertFalse(ar.protected("unprotected/" + prefix))
        self.assertFalse(ar.protected("scripts-lookalike/example.py"))
        self.assertFalse(ar.protected("lean-toolchain.notes"))

    def run_clear(self, *extra):
        output = io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            status = ar.main(["--clear", "--repo", SLUG, *extra],
                             http=self.api, env={"GITHUB_TOKEN": WORKFLOW_TOKEN})
        return status, output.getvalue()

    @staticmethod
    def open_issue(number, **extra):
        return {"number": number, "state": "open",
                "labels": [{"name": "main-red"}, {"name": "blocks-release"}], **extra}

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

    def test_clear_old_success_does_not_clear_new_main(self):
        self.api.after = "b" * 40
        self.api.open_issues = [self.open_issue(4)]
        status, output = self.run_clear("--after", "a" * 40)
        self.assertEqual(status, 2, output)
        self.assertEqual(self.api.deleted, [])

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
                                cwd=self.repo, env=env, text=True, capture_output=True, check=False)
        return result, output.read_text(encoding="utf-8")

    def test_acceptance_push_compares_with_before_not_last_merge_parent(self):
        first = self.train()
        after = self.train(12, text="Second revision.\n")
        result, output = self.run_acceptance_event(
            "push", {"before": self.before, "after": after, "ref": "refs/heads/main", "deleted": False})
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
            ("push", {"before": "0" * 40, "after": after, "ref": "refs/heads/main", "deleted": False}),
            ("push", {"before": self.before, "after": self.before, "ref": "refs/heads/main", "deleted": False}),
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
                self.assertEqual(result.returncode == 0, status == "success", result.stderr.decode())

    def run_trusted_extraction(self, before):
        script = workflow_step("post-merge.yml", "Take the revert script from the previous main")
        output = self.directory / "github-output"
        env = ar.git_env()
        env.update(BEFORE=before, RUNNER_TEMP=str(self.directory), GITHUB_OUTPUT=str(output))
        result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script],
                                cwd=self.repo, env=env, text=True, capture_output=True, check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        return output.read_text(encoding="utf-8").strip().removeprefix("script=")

    def test_workflow_executes_previous_main_script_despite_after_replacement(self):
        self.write("scripts/auto_revert.py", "print('Previous main script')\n")
        self.commit("Install trusted script")
        before = self.rev()
        self.train(path="scripts/auto_revert.py", text="raise RuntimeError('Failed revision ran')\n")
        extracted = self.run_trusted_extraction(before)
        self.assertEqual(command(self.directory, sys.executable, "-I", extracted), "Previous main script")

    def test_workflow_does_not_use_after_script_when_before_has_none(self):
        self.train(path="scripts/auto_revert.py", text="raise RuntimeError('Failed revision ran')\n")
        self.assertEqual(self.run_trusted_extraction(self.before), "")


if __name__ == "__main__":
    unittest.main()
