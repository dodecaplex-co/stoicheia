#!/usr/bin/env python3
"""Tests for scripts/safe_push.py, on a throwaway clone with a bare origin.

    python3 scripts/test_safe_push.py        # five minutes or so; no Lean, no network
    STOICHEIA_SLOW_TESTS=1 python3 scripts/test_safe_push.py FullChecks   # Lean, minutes

The clone is made with `git clone --local` of this repository into a temporary
directory: a bare `origin.git` and a working clone of it. Origin's main is this
checkout's HEAD with this checkout's copies of the harness (scripts/safe_push.py, its
hook, its allow-list, its tests) and of the pull request template committed on top, so
that origin/main's harness, which safe_push runs, is the one under test. GitHub is
played by a stand-in for gh (STOICHEIA_TEST_GH): pull requests kept in a JSON file, their
checks set by each test, merged into the bare origin with a merge commit. Each test plants
one commit and runs safe_push.py against that origin:

- each guard refuses its bad commit: a secret, a statement changed without a decision,
  the axiom lock changed without one, a commit that is not a fast-forward, a change to
  heath/ with no leaf named, a whole directory deleted, and a protected path changed
  without a decisions entry naming it;
- a good commit passes, by a dry run and then the pre-flight, from a dirty working tree:
  pushed to its branch, never to main, and its pull request opened with the template's
  body and the pre-flight's summary; then updated, keeping the coordinator's words;
- --merge refuses a draft, an unticked or missing required box, red or missing CI, and a
  protected change without its label; reruns the pre-flight for a head it has not seen;
  and merges with a merge commit, deleting the branch;
- the pre-push hook refuses every push to main and scans a push to any other branch;
- the review's findings: the harness and the check scripts are origin/main's, an
  allow-list entry the push adds does not count, the heath/ leaves are origin/main's, an
  interruption after the push is "pushed; CI not followed", scratchpad paths and
  machine-made identities are refused, .gitattributes cannot hide a file, and a broad
  allow-list entry is refused;
- the second review's notes: an interruption (Ctrl-C, or SIGTERM to the process alone)
  after the push of a run handed over to origin/main's harness is still exit 3; the
  launcher (`git safe-push`) runs origin/main's copy even when the checkout's never hands
  over, and STOICHEIA_HARNESS is checked; UTF-16 text after 8 KB of prose or binary junk
  is found; an allow-list entry excuses its own value alone, in a binary file too, and
  never a commit message; --merge runs the scan and the guards again whatever the record
  says, and shows its notes; a fork's pull request of the same name is left alone; the
  title, the branch name and an open pull request's body are scanned before the push;
  lakefile.lean and .gitignore are protected; a recased source comment names no leaf; a
  hand edit to PROGRAM.md is not a generated change; an allowed tag is still scanned;
  and an installed hook that differs from origin/main's is noted;
- and the edge cases, each refused: (1) a credential split over two lines; (2) one
  base64-encoded; (3) a key file added under a name later renamed, a secret taken out
  again within the push, and files renamed to .pem, .key and .env names; (4) symlinks
  into private directories or out of the repository; (5) a statement changed on a
  re-wrapped line, a decision naming another proposition, an old brief line edited in
  place, and a statement's text after a binder's `:=`; (6) the axiom lock changed with a
  decision silent on it, a mention outside the decisions page, or an old line edited;
  (7) stale or hand-edited generated pages; (8) a commit behind origin/main or with an
  unrelated history, and origin/main moving during the checks or at the push; (9) the
  hook given HEAD:main, main, refs/heads/main, --mirror, a forced refspec and tags;
  (10) a dry run, which never pushes, calls no gh, and leaves no worktree or temporary
  file, on success, on a refusal or when interrupted.

The long checks of step 4 (the build and the rest) are skipped by the internal flag
`--_test-skip-checks`, used here and nowhere else; safe_push honours it only against a
local origin, and with it calls only the gh stand-in. The checks the guards run
themselves (check_fidelity.py and render.py on the commit as committed) still run. The
opt-in FullChecks test runs step 4 for real, once, on a good commit, as a dry run of the
pre-flight. Python 3.11 or later; standard library and git.
"""

from __future__ import annotations

import base64
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
SAFE_PUSH = HERE / "safe_push.py"
INSTALL_HOOKS = HERE / "install_hooks.sh"
SOURCE = HERE.parent
sys.path.insert(0, str(HERE))
import safe_push  # noqa: E402

TMP: Path
ORIGIN: Path
WORK: Path
LOG: Path
BASE: str
GH: Path
GH_STATE: Path
BRANCH = "test-pr"
DECISIONS = "docs/briefs/0002-decisions.md"
# The files of the harness under test, committed on top of HEAD as origin's main.
HARNESS_FILES = ("scripts/safe_push.py", "scripts/heath.py", "scripts/test_safe_push.py",
                 "scripts/hooks/pre-push", "scripts/hooks/safe-push", "scripts/install_hooks.sh",
                 "scripts/safe_push_allow.toml", ".github/pull_request_template.md")


def git(cwd, *args, env=None, check=True) -> str:
    r = subprocess.run(["git", *args], cwd=cwd, env=env, capture_output=True, text=True)
    if check and r.returncode != 0:
        raise AssertionError(f"git {' '.join(args)} failed in {cwd}:\n{r.stdout}{r.stderr}")
    return r.stdout


def clean_env() -> dict:
    env = dict(os.environ, STOICHEIA_PUSH_LOG=str(LOG), STOICHEIA_TEST_GH=str(GH),
               STOICHEIA_FAKE_GH_STATE=str(GH_STATE), STOICHEIA_FAKE_GH_ORIGIN=str(ORIGIN),
               STOICHEIA_PYTHON=sys.executable)
    for name in ("STOICHEIA_SAFE_PUSH", "STOICHEIA_HARNESS", "STOICHEIA_TAG_PUSH",
                 "STOICHEIA_FAKE_GH_KILL"):
        env.pop(name, None)
    return env


# Planted secrets are built when the tests run, so that this file passes the scan itself.
TOKEN = base64.b64encode(hashlib.sha256(b"a planted token").digest()).decode()
PRIVATE_DIR = "/" + "Users" + "/someone/" + "Down" + "loads/notes.txt"
KEY_HEADER = "-----BEGIN " + "RSA PRIVATE" + " KEY-----"
GH_TOKEN = "gh" + "p_" + hashlib.sha256(b"a planted GitHub token").hexdigest()[:36]
HEXKEY = hashlib.sha256(b"a planted hex key").hexdigest()
TILDE_DOWNLOADS = "~/" + "Down" + "loads"
PRIVATE_SCANS = "../../" + "secret" + "s2026/scans"
FOLDED_HOME = "-" + "Users" + "-someone"
SCRATCHPAD = "/private" + "/tmp/" + "claude" + "-501/" + FOLDED_HOME + "/0123/scratchpad/x.txt"

PASSING = [{"name": n, "bucket": "pass", "state": "SUCCESS", "workflow": "CI"}
           for n in ("check", "model", "negative")]

# A stand-in for gh: pull requests in a JSON file; checks as each test sets them; a merge
# made in the bare origin with a merge commit, as GitHub makes it.
FAKE_GH = r'''#!@PYTHON@
import json, os, subprocess, sys, time

STATE = os.environ["STOICHEIA_FAKE_GH_STATE"]
ORIGIN = os.environ["STOICHEIA_FAKE_GH_ORIGIN"]


def load():
    with open(STATE) as f:
        return json.load(f)


def save(s):
    with open(STATE, "w") as f:
        json.dump(s, f, indent=1)


def head_of(branch):
    r = subprocess.run(["git", "rev-parse", "--verify", "--quiet", "refs/heads/" + branch],
                       cwd=ORIGIN, capture_output=True, text=True)
    return r.stdout.strip()


def opt(args, name):
    return args[args.index(name) + 1] if name in args else None


def opts(args, name):
    return [args[i + 1] for i, a in enumerate(args) if a == name]


def fields(pr, wanted):
    # A fork's pull request has a head of its own, never origin's branch of that name.
    fork = pr.get("isCrossRepository", False)
    head = pr.get("forkHead", "") if fork else \
        (head_of(pr["headRefName"]) or pr.get("mergedHead", ""))
    full = dict(pr, headRefOid=head, labels=[{"name": n} for n in pr["labels"]],
                isCrossRepository=fork,
                headRepositoryOwner=pr.get("headRepositoryOwner", {"login": "test"}))
    return {k: full.get(k) for k in wanted.split(",")}


def kill_on_watch():
    """STOICHEIA_FAKE_GH_KILL=<pid file>:<signal>: while following CI, signal the
    process the pid file names, as a Ctrl-C or a supervisor's timeout would, and go on
    watching until killed."""
    spec = os.environ.get("STOICHEIA_FAKE_GH_KILL")
    if not spec:
        return
    pidfile, signum = spec.rsplit(":", 1)
    for _ in range(100):
        if os.path.exists(pidfile) and open(pidfile).read().strip():
            break
        time.sleep(0.1)
    os.kill(int(open(pidfile).read()), int(signum))
    time.sleep(60)


def main(argv):
    s = load()
    s["calls"].append(argv)
    save(s)
    args = list(argv)
    if "-R" in args:
        i = args.index("-R")
        del args[i:i + 2]
    cmd = args[:2]
    if cmd == ["auth", "status"]:
        return 0
    if cmd == ["label", "list"]:
        print(json.dumps([{"name": n} for n in s["labels"]]))
        return 0
    if cmd == ["label", "create"]:
        s["labels"].append(args[2])
        save(s)
        return 0
    if cmd == ["pr", "list"]:
        found = [p for p in s["prs"] if p["headRefName"] == opt(args, "--head")
                 and p["state"] == "OPEN"]
        print(json.dumps([fields(p, opt(args, "--json")) for p in found]))
        return 0
    if cmd == ["pr", "create"]:
        n = len(s["prs"]) + 1
        labels = opts(args, "--label")
        if any(n_ not in s["labels"] for n_ in labels):
            print("could not add label: not found", file=sys.stderr)
            return 1
        with open(opt(args, "--body-file")) as f:
            body = f.read()
        s["prs"].append({"number": n, "title": opt(args, "--title"), "body": body,
                         "headRefName": opt(args, "--head"), "baseRefName": opt(args, "--base"),
                         "isDraft": "--draft" in args, "labels": labels, "state": "OPEN",
                         "url": "https://github.invalid/test/stoicheia/pull/%d" % n})
        save(s)
        print(s["prs"][-1]["url"])
        return 0
    n = int(args[2]) if len(args) > 2 and args[2].isdigit() else None
    pr = next((p for p in s["prs"] if p["number"] == n), None)
    if pr is None:
        print("fake gh: no such pull request: %s" % argv, file=sys.stderr)
        return 1
    if cmd == ["pr", "view"]:
        print(json.dumps(fields(pr, opt(args, "--json"))))
        return 0
    if cmd == ["pr", "edit"]:
        if opt(args, "--body-file"):
            with open(opt(args, "--body-file")) as f:
                pr["body"] = f.read()
        if opt(args, "--title"):
            pr["title"] = opt(args, "--title")
        for label in opts(args, "--add-label"):
            if label not in pr["labels"]:
                pr["labels"].append(label)
        save(s)
        return 0
    if cmd == ["pr", "ready"]:
        pr["isDraft"] = "--undo" in args
        save(s)
        return 0
    if cmd == ["pr", "checks"]:
        sha = head_of(pr["headRefName"])
        checks = s["checks"].get(sha, s["checks"]["*"])
        if "--watch" in args:
            kill_on_watch()
            return 0 if all(c["bucket"] == "pass" for c in checks) else 1
        print(json.dumps(checks))
        return 0
    if cmd == ["pr", "merge"]:
        if "--merge" not in args or "--squash" in args or "--rebase" in args:
            return 1
        sha = head_of(pr["headRefName"])
        if opt(args, "--match-head-commit") != sha:
            print("head moved", file=sys.stderr)
            return 1
        main = subprocess.run(["git", "rev-parse", "refs/heads/main"], cwd=ORIGIN,
                              capture_output=True, text=True, check=True).stdout.strip()
        env = dict(os.environ, GIT_AUTHOR_NAME="GitHub", GIT_AUTHOR_EMAIL="noreply@github.com",
                   GIT_COMMITTER_NAME="GitHub", GIT_COMMITTER_EMAIL="noreply@github.com")
        merge = subprocess.run(["git", "commit-tree", sha + "^{tree}", "-p", main, "-p", sha,
                                "-m", "Merge pull request #%d" % n], cwd=ORIGIN, env=env,
                               capture_output=True, text=True, check=True).stdout.strip()
        subprocess.run(["git", "update-ref", "refs/heads/main", merge, main], cwd=ORIGIN,
                       check=True)
        if "--delete-branch" in args:
            subprocess.run(["git", "update-ref", "-d", "refs/heads/" + pr["headRefName"]],
                           cwd=ORIGIN, check=True)
        pr["state"], pr["mergedHead"] = "MERGED", sha
        save(s)
        return 0
    print("fake gh: not understood: %s" % argv, file=sys.stderr)
    return 2


sys.exit(main(sys.argv[1:]))
'''


def reset_gh() -> None:
    GH_STATE.write_text(json.dumps({"prs": [], "labels": [], "checks": {"*": PASSING},
                                    "calls": []}))


def setUpModule():
    global TMP, ORIGIN, WORK, LOG, BASE, GH, GH_STATE
    TMP = Path(tempfile.mkdtemp(prefix="stoicheia-safe-push-test-"))
    ORIGIN, WORK, LOG = TMP / "origin.git", TMP / "work", TMP / "cache" / "pushes.log"
    GH, GH_STATE = TMP / "fake-gh", TMP / "fake-gh.json"
    GH.write_text(FAKE_GH.replace("@PYTHON@", sys.executable))
    GH.chmod(0o755)
    reset_gh()
    common = git(SOURCE, "rev-parse", "--path-format=absolute", "--git-common-dir").strip()
    head = git(SOURCE, "rev-parse", "HEAD").strip()
    git(TMP, "clone", "--quiet", "--bare", "--local", common, str(ORIGIN))
    git(ORIGIN, "update-ref", "refs/heads/main", head)
    git(ORIGIN, "symbolic-ref", "HEAD", "refs/heads/main")
    git(TMP, "clone", "--quiet", "--local", str(ORIGIN), str(WORK))
    git(WORK, "config", "user.name", "safe_push test")
    git(WORK, "config", "user.email", "safe-push-test@example.invalid")
    git(WORK, "config", "commit.gpgsign", "false")
    git(WORK, "checkout", "--quiet", "--detach", head)
    for rel in HARNESS_FILES:
        if (SOURCE / rel).exists():
            (WORK / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(SOURCE / rel, WORK / rel)
            git(WORK, "add", "--", rel)
    if git(WORK, "status", "--porcelain").strip():
        git(WORK, "commit", "-q", "-m", "The harness under test")
        git(WORK, "push", "--quiet", "--no-verify", "origin", "HEAD:refs/heads/main")
    BASE = git(WORK, "rev-parse", "HEAD").strip()
    git(WORK, "fetch", "--quiet", "origin")
    r = subprocess.run(["sh", str(INSTALL_HOOKS)], cwd=WORK, capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr


def tearDownModule():
    shutil.rmtree(TMP, ignore_errors=True)


class Clone(unittest.TestCase):
    """Each test starts from origin/main at BASE, a clean clone, no branch on origin but
    main, and no pull request."""

    def setUp(self):
        git(ORIGIN, "update-ref", "refs/heads/main", BASE)
        for ref in git(ORIGIN, "for-each-ref", "--format=%(refname)", "refs/heads/").split():
            if ref != "refs/heads/main":
                git(ORIGIN, "update-ref", "-d", ref)
        git(WORK, "fetch", "--quiet", "--prune", "origin")
        git(WORK, "checkout", "--quiet", "--force", "--detach", BASE)
        git(WORK, "clean", "-fdq")
        reset_gh()

    def text(self, path: str) -> str:
        return (WORK / path).read_text()

    def replaced(self, path: str, old: str, new: str) -> str:
        text = self.text(path)
        self.assertEqual(text.count(old), 1, f"{path}: expected one {old!r}")
        return text.replace(old, new)

    def commit(self, message: str, write: dict | None = None, remove=(), env=None) -> str:
        for path, text in (write or {}).items():
            (WORK / path).parent.mkdir(parents=True, exist_ok=True)
            if isinstance(text, bytes):
                (WORK / path).write_bytes(text)
            else:
                (WORK / path).write_text(text)
            git(WORK, "add", "--", path)
        for path in remove:
            git(WORK, "rm", "-r", "-q", "--", path)
        git(WORK, "commit", "-q", "-m", message, env=env)
        return git(WORK, "rev-parse", "HEAD").strip()

    def new_base(self, message: str, write: dict) -> str:
        """A commit on origin's main, as a merged pull request would leave it."""
        sha = self.commit(message, write)
        git(WORK, "push", "--quiet", "--no-verify", "origin", f"{sha}:refs/heads/main")
        git(WORK, "fetch", "--quiet", "origin")
        return sha

    def safe_push(self, *args, env=None, script=SAFE_PUSH) -> subprocess.CompletedProcess:
        """safe_push.py under the internal test flag; the pre-flight for BRANCH unless the
        arguments name --branch, --merge or --scan-push."""
        if not {"--branch", "--merge", "--scan-push"} & set(args):
            args = ("--branch", BRANCH, *args)
        return subprocess.run([sys.executable, str(script), "--_test-skip-checks", *args],
                              cwd=WORK, env=env or clean_env(), capture_output=True, text=True)

    def origin_main(self) -> str:
        return git(ORIGIN, "rev-parse", "refs/heads/main").strip()

    def origin_branch(self, name: str = BRANCH) -> str | None:
        r = subprocess.run(["git", "rev-parse", "--verify", "--quiet", f"refs/heads/{name}"],
                           cwd=ORIGIN, capture_output=True, text=True)
        return r.stdout.strip() or None

    def guard(self, out: str, name: str) -> str | None:
        """The outcome a step's line reports: "ok", "FAIL", "note", or None if absent."""
        m = re.search(r"^\s+(ok|FAIL|note)\s+%s:" % re.escape(name), out, re.M)
        return m.group(1) if m else None

    def assertRefused(self, r, *wanted):
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        self.assertIn("REFUSED", out)
        for w in wanted:
            self.assertIn(w, out)
        self.assertEqual(self.origin_main(), BASE, "a refused push moved origin/main")
        self.assertIsNone(self.origin_branch(), "a refused push pushed the branch")
        return out

    def decision(self, line: str) -> dict:
        return {DECISIONS: self.text(DECISIONS) + f"\n- **A decision for the test.** {line}\n"}

    def gh_state(self) -> dict:
        return json.loads(GH_STATE.read_text())

    def set_gh(self, change) -> None:
        state = self.gh_state()
        change(state)
        GH_STATE.write_text(json.dumps(state))


class Accepts(Clone):
    def test_good_commit_dry_run_then_push_from_a_dirty_tree(self):
        first, rest = self.text("heath/I/01.md").split("\n", 1)
        heath = first + "\n<!-- Checked against the page image, scan leaf n261. -->\n" + rest
        sha = self.commit("A good commit", {
            "docs/reading.md": self.text("docs/reading.md") + "\nA line for the test.\n",
            "heath/I/01.md": heath,
        })
        # Nothing is read from the working tree: a change there, and an untracked file
        # holding a secret, are neither checked nor pushed.
        (WORK / "README.md").write_text(self.text("README.md") + "\nUncommitted.\n")
        (WORK / "notes.txt").write_text(f"api_token = '{TOKEN}'\n")
        tags = git(ORIGIN, "tag", "--list")

        r = self.safe_push("--dry-run")
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, out)
        self.assertIn("dry run", out)
        self.assertEqual(self.origin_main(), BASE)
        self.assertIsNone(self.origin_branch())
        for name in ("commit", "fast-forward", "harness", "secrets", "statements", "axiom lock",
                     "protected paths", "heath/", "directories", "review records"):
            self.assertEqual(self.guard(out, name), "ok", f"{name}:\n{out}")
        self.assertIn("leaf n261", out)

        r = self.safe_push()                       # HEAD, by default, to the branch
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, out)
        self.assertEqual(self.origin_main(), BASE, "the pre-flight pushed to main")
        self.assertEqual(self.origin_branch(), sha)
        for name in ("git push", "tags", "pull request", "CI"):
            self.assertEqual(self.guard(out, name), "ok", f"{name}:\n{out}")
        self.assertEqual(git(ORIGIN, "tag", "--list"), tags, "a tag was made")
        self.assertNotIn("Uncommitted", git(ORIGIN, "show", f"{sha}:README.md"))
        self.assertEqual(len(git(WORK, "worktree", "list").splitlines()), 1,
                         "a temporary worktree was left behind")
        log = LOG.read_text()
        self.assertIn(f"dry run {sha[:12]}", log)
        self.assertIn(f"push {sha[:12]}", log)
        # The pull request: onto main, from the branch, with the template's body.
        (pr,) = self.gh_state()["prs"]
        self.assertEqual((pr["headRefName"], pr["baseRefName"], pr["title"]),
                         (BRANCH, "main", "A good commit"))
        body = pr["body"]
        self.assertIn(f"<!-- safe_push:preflight begin sha={sha} base={BASE} -->", body)
        self.assertIn("## Checklist", body)
        self.assertIn("- [ ] **Required:**", body)
        self.assertIn(f"`{sha[:7]}` A good commit", body)
        self.assertIn("| 3. statements | ok |", body)
        self.assertNotIn("<!-- safe_push: commits -->", body)
        self.assertNotIn(str(Path.home()), body, "a private path in the public body")

    def test_nothing_to_push(self):
        r = self.safe_push()
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("Nothing to push", r.stdout)


class Preconditions(Clone):
    def test_unknown_commit(self):
        self.assertRefused(self.safe_push("--commit", "0123456789abcdef0123456789abcdef01234567"),
                           "is not a commit")

    def test_not_a_fast_forward(self):
        side = self.commit("Someone else's commit", {
            "docs/reading.md": self.text("docs/reading.md") + "\nTheirs.\n"})
        git(WORK, "push", "--quiet", "origin", f"{side}:refs/heads/side")   # not main
        git(ORIGIN, "update-ref", "refs/heads/main", side)
        git(WORK, "checkout", "--quiet", "--detach", BASE)
        mine = self.commit("Mine", {"docs/reading.md": self.text("docs/reading.md") + "\nMine.\n"})
        r = self.safe_push("--commit", mine)
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        self.assertIn("not a fast-forward", out)
        self.assertEqual(self.guard(out, "fast-forward"), "FAIL", out)
        self.assertEqual(self.origin_main(), side)

    def test_internal_flag_needs_a_local_origin(self):
        url = git(WORK, "remote", "get-url", "origin").strip()
        git(WORK, "remote", "set-url", "origin", "https://github.com/example/none.git")
        try:
            self.assertRefused(self.safe_push(), "only against a local origin")
        finally:
            git(WORK, "remote", "set-url", "origin", url)


class Secrets(Clone):
    def test_secrets_refused(self):
        self.commit("Plant secrets", {
            "docs/notes.md": f"Some notes.\napi_token = \"{TOKEN}\"\nsee {PRIVATE_DIR}\n",
            "deploy/.env": "PLAIN=1\n",
            "deploy/server.pem": "not really a certificate\n",
            "deploy/id": f"{KEY_HEADER}\nMIIEow\n",
        })
        out = self.assertRefused(self.safe_push(), "secret scan")
        self.assertEqual(self.guard(out, "secrets"), "FAIL", out)
        for rule in ("key, token or secret", "private path", ".env file", "key file",
                     "private key"):
            self.assertIn(rule, out)
        self.assertNotIn(TOKEN, out, "the report repeats the secret")

    def test_secret_in_a_commit_message_refused(self):
        self.commit(f"Notes from {PRIVATE_DIR}", {
            "docs/reading.md": self.text("docs/reading.md") + "\nA line.\n"})
        self.assertRefused(self.safe_push(), "message", "private path")

    # The value is pinned by its SHA-256: written here, it would be flagged in turn.
    ALLOW = ('[[allow]]\npath = "docs/notes.md"\nmatch = "api_token"\n'
             'rule = "key, token or secret"\n'
             f'sha256 = "{hashlib.sha256(TOKEN.encode()).hexdigest()}"\n'
             'reason = "A fixture for the test, not a real token."\n')

    def test_allow_list_with_a_reason(self):
        # origin/main's allow-list counts: the entry lands in a pull request of its own.
        self.new_base("Allow a fixture", {"scripts/safe_push_allow.toml": self.ALLOW})
        self.commit("A flagged line, allowed", {"docs/notes.md": f"api_token = \"{TOKEN}\"\n"})
        r = self.safe_push("--dry-run")
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, out)
        self.assertEqual(self.guard(out, "secrets"), "ok", out)
        self.assertIn("A fixture for the test", out)

    def test_allow_list_without_a_reason_refused(self):
        allow = self.ALLOW.replace('reason = "A fixture for the test, not a real token."\n', "")
        main = self.new_base("Allow a fixture, with no reason",
                             {"scripts/safe_push_allow.toml": allow})
        self.commit("A flagged line", {"docs/notes.md": f"api_token = \"{TOKEN}\"\n"})
        r = self.safe_push()
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        self.assertIn("has no reason", out)
        self.assertEqual(self.origin_main(), main)
        self.assertIsNone(self.origin_branch())


SIGNATURE_OLD = "theorem Prop1 (A B : Point) (hAB : A ≠ B) (P : Point) :"
SIGNATURE_NEW = "theorem Prop1 (A B : Point) (hAB : A ≠ B) (Q : Point) :"


class Statements(Clone):
    def test_lean_statement_changed_without_a_decision_refused(self):
        self.commit("Change I.1's statement", {"Elements/BookI/Prop01.lean": self.replaced(
            "Elements/BookI/Prop01.lean", SIGNATURE_OLD, SIGNATURE_NEW)})
        out = self.assertRefused(self.safe_push(), "I.1: the Lean statement changed")
        self.assertEqual(self.guard(out, "statements"), "FAIL", out)

    def test_facts_statement_changed_without_a_decision_refused(self):
        facts = json.loads(self.text("facts.json"))
        old = next(p["statement"] for p in facts["propositions"] if p["ref"] == "III.1 Por.")
        new = old.replace("Elements.Collinear D C G", "Elements.Collinear D G C")
        self.assertNotEqual(old, new)
        text = self.replaced("facts.json", json.dumps(old, ensure_ascii=False),
                             json.dumps(new, ensure_ascii=False))
        self.commit("Change III.1 Por.'s statement", {"facts.json": text})
        out = self.assertRefused(self.safe_push(), "III.1 Por.: facts.json's statement changed")
        self.assertEqual(self.guard(out, "statements"), "FAIL", out)

    def test_statement_changed_with_a_decision_passes_the_guard(self):
        changes = {"Elements/BookI/Prop01.lean": self.replaced(
            "Elements/BookI/Prop01.lean", SIGNATURE_OLD, SIGNATURE_NEW)}
        changes.update(self.decision("I.1 names its side point Q."))
        self.commit("Change I.1's statement, with a decision", changes)
        out = self.assertRefused(self.safe_push())
        self.assertEqual(self.guard(out, "statements"), "ok", out)
        self.assertIn("named in the docs/briefs/ lines added", out)
        # The Lean file changed, so I.1's review record is stale, and that is refused too.
        self.assertEqual(self.guard(out, "review records"), "FAIL", out)
        self.assertIn("I.1", out)


class Lock(Clone):
    LOCK = "Certificate/axioms.lock"

    def weakened(self) -> dict:
        line = '"Postulate1" = "∀ (A B : Elements.Point), Ne A B → Exists'
        return {self.LOCK: self.replaced(self.LOCK, line, line.replace("Ne A B → ", ""))}

    def test_lock_changed_without_a_decision_refused(self):
        self.commit("Weaken Postulate 1 in the lock", self.weakened())
        out = self.assertRefused(self.safe_push(), "axioms.lock changed")
        self.assertEqual(self.guard(out, "axiom lock"), "FAIL", out)

    def test_lock_changed_with_a_decision_passes_the_guard(self):
        changes = self.weakened()
        changes.update(self.decision("The axiom lock gains a weaker Postulate 1."))
        self.commit("Weaken Postulate 1 in the lock, with a decision", changes)
        out = self.assertRefused(self.safe_push())
        self.assertEqual(self.guard(out, "axiom lock"), "ok", out)


class Heath(Clone):
    WORD = ("equilateral triangle.*", "equilateral triangle*.")   # I.1's enunciation

    def test_heath_changed_without_a_leaf_refused(self):
        self.commit("Edit a Heath word", {"heath/I/01.md": self.replaced("heath/I/01.md",
                                                                         *self.WORD)})
        out = self.assertRefused(self.safe_push(), "heath/I/01.md")
        self.assertEqual(self.guard(out, "heath/"), "FAIL", out)

    def test_heath_changed_naming_another_pages_leaf_refused(self):
        text = self.replaced("heath/I/01.md", *self.WORD)
        text = text.replace("# Proposition 1", "<!-- Checked, scan leaf n999. -->\n# Proposition 1")
        self.commit("Edit a Heath word, naming a leaf of another page", {"heath/I/01.md": text})
        out = self.assertRefused(self.safe_push(), "not one of its own pages' leaves")
        self.assertEqual(self.guard(out, "heath/"), "FAIL", out)

    def test_heath_changed_naming_its_leaf_passes_the_guard(self):
        text = self.replaced("heath/I/01.md", *self.WORD)
        text = text.replace("# Proposition 1", "<!-- Checked, scan leaf n261. -->\n# Proposition 1")
        self.commit("Edit a Heath word, naming its leaf", {"heath/I/01.md": text})
        out = self.safe_push("--dry-run")
        self.assertEqual(self.guard(out.stdout, "heath/"), "ok", out.stdout)

    def test_heath_file_deleted_refused(self):
        self.commit("Delete a Heath file", remove=["heath/I/48.md"])
        self.assertRefused(self.safe_push(), "heath/I/48.md: deleted")

    def test_source_comment_widened_by_the_change_refused(self):
        # Finding 3: the leaves allowed are origin/main's; a change that adds n999 to the
        # file's own source comment, and then names n999, is refused.
        text = self.replaced("heath/I/01.md", *self.WORD)
        text = text.replace("scan leaves n261–n262;", "scan leaves n261–n262, n999;")
        text = text.replace("# Proposition 1", "<!-- Checked, scan leaf n999. -->\n# Proposition 1")
        self.commit("Edit a Heath word, widening the source comment", {"heath/I/01.md": text})
        out = self.assertRefused(self.safe_push(), "not one of its own pages' leaves",
                                 "origin/main's copy")
        self.assertEqual(self.guard(out, "heath/"), "FAIL", out)

    def test_source_comment_recased_does_not_name_a_leaf(self):
        # Review note 10: the source comment is the file's first, known by its place; with
        # "Source:" written "source:", it still lists the leaves and checks none.
        text = self.replaced("heath/I/01.md", *self.WORD).replace("<!-- Source:", "<!-- source:")
        self.commit("Edit a Heath word, and recase the source comment", {"heath/I/01.md": text})
        out = self.assertRefused(self.safe_push(), "no comment in the change naming the scan leaf")
        self.assertEqual(self.guard(out, "heath/"), "FAIL", out)


class Directories(Clone):
    def test_directory_deleted_without_a_decision_refused(self):
        self.commit("Delete a directory", remove=["mishnah/intro"])
        out = self.assertRefused(self.safe_push(), "mishnah/intro/")
        self.assertEqual(self.guard(out, "directories"), "FAIL", out)

    def test_directory_deleted_with_a_decision_passes_the_guard(self):
        self.commit("Delete a directory, with a decision",
                    self.decision("The introductions in `mishnah/intro/` move."),
                    remove=["mishnah/intro"])
        r = self.safe_push("--dry-run")
        self.assertEqual(self.guard(r.stdout, "directories"), "ok", r.stdout)


class Hook(Clone):
    def push(self, refspec, **env) -> subprocess.CompletedProcess:
        e = clean_env()
        e.update(env)
        return subprocess.run(["git", "push", "origin", refspec], cwd=WORK, env=e,
                              capture_output=True, text=True)

    def test_hook_refuses_pushes_to_main_that_safe_push_did_not_check(self):
        # Every push to main is refused now, the commit checked or not: main changes only
        # by a pull request's merge commit.
        sha = self.commit("A commit", {"docs/reading.md": self.text("docs/reading.md") + "\nX.\n"})
        r = self.push(f"{sha}:refs/heads/main")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("git safe-push --branch", r.stderr)
        r = self.push(f"{sha}:refs/heads/main", STOICHEIA_SAFE_PUSH=sha)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("refusing a push to main", r.stderr)
        r = self.push(":refs/heads/main", STOICHEIA_SAFE_PUSH=sha)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("refusing to delete main", r.stderr)
        self.assertEqual(self.origin_main(), BASE)
        r = self.push(f"{sha}:refs/heads/a-branch")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("the secret scan of the push to refs/heads/a-branch", r.stdout + r.stderr)

    def test_hook_scans_a_push_to_any_branch(self):
        # Finding 2: the same secret scan on every branch, not just main.
        bad = self.commit("Plant a token", {"docs/notes.md": f"api_token = \"{TOKEN}\"\n"})
        for ref in ("refs/heads/feature", "refs/heads/someone/else"):
            with self.subTest(ref=ref):
                r = self.push(f"{bad}:{ref}")
                self.assertNotEqual(r.returncode, 0, r.stderr)
                self.assertIn(f"pre-push: refusing the push to {ref}", r.stderr)
                self.assertIsNone(self.origin_branch(ref.removeprefix("refs/heads/")))
        self.assertNotIn(TOKEN, r.stdout + r.stderr, "the hook repeats the secret")

    def test_hook_scans_with_origin_mains_copy(self):
        # A branch that empties its own copy of the scan is still scanned by origin/main's.
        lame = self.replaced("scripts/safe_push.py", "def scan_push_main(",
                             "def scan_push_main(*a):\n    return 0\n\n\ndef _unused(")
        bad = self.commit("Disable the scan, and plant a token", {
            "scripts/safe_push.py": lame, "docs/notes.md": f"api_token = \"{TOKEN}\"\n"})
        r = self.push(f"{bad}:refs/heads/feature")
        self.assertNotEqual(r.returncode, 0, r.stderr)
        self.assertIn("pre-push: refusing the push to refs/heads/feature", r.stderr)


# --------------------------------------------------------------------------------------
# The edge cases: each planted commit is refused (or, for the dry run, behaves as stated).


def hooks_dir() -> Path:
    out = git(WORK, "rev-parse", "--git-path", "hooks").strip()
    return Path(out) if os.path.isabs(out) else WORK / out


class Edge(Clone):
    def flagged(self, out: str, path: str) -> bool:
        """Does the secret scan's report name a finding in `path`: "path: rule",
        "path:3: rule", "path:2-3: rule", each perhaps with "(in commit <sha>)"?"""
        where = r"^\s+%s(:\d+(-\d+)?)?( \(in commit [0-9a-f]+\))?: " % re.escape(path)
        return re.search(where, out, re.M) is not None

    def assertFlagged(self, out: str, *paths: str):
        self.assertEqual(self.guard(out, "secrets"), "FAIL", out)
        for path in paths:
            self.assertTrue(self.flagged(out, path), f"{path} not flagged:\n{out}")

    def swap_hook(self, script: str) -> None:
        """Put `script` in place of the installed pre-push hook until the test ends."""
        hook = hooks_dir() / "pre-push"
        saved = hook.read_text()
        hook.write_text(script)
        hook.chmod(0o755)
        self.addCleanup(lambda: (hook.write_text(saved), hook.chmod(0o755)))

    def side_commit(self) -> str:
        """Someone else's commit on top of BASE, in origin (on a side branch), not on main."""
        side = self.commit("Someone else's commit", {
            "docs/reading.md": self.text("docs/reading.md") + "\nTheirs.\n"})
        git(WORK, "push", "--quiet", "origin", f"{side}:refs/heads/side")
        self.addCleanup(lambda: git(ORIGIN, "update-ref", "-d", "refs/heads/side", check=False))
        git(WORK, "checkout", "--quiet", "--detach", BASE)
        return side

    def good_commit(self, line: str = "A line for the test.") -> str:
        return self.commit("A good commit", {
            "docs/reading.md": self.text("docs/reading.md") + f"\n{line}\n"})


class SplitSecrets(Edge):
    """(1) A credential-like value split over two added lines."""

    def test_value_split_over_two_lines_refused(self):
        half = len(TOKEN) // 2
        self.commit("A token split over lines", {
            # the key word on one line, its value on the next
            "docs/notes.md": f"Some notes.\napi_token =\n    \"{TOKEN}\"\n",
            # a string continued in parentheses
            "scripts/settings.py": f'API_TOKEN = (\n    "{TOKEN[:half]}"\n    "{TOKEN[half:]}"\n)\n',
            # a value broken at the wrap, neither part long enough alone
            "docs/wrapped.txt": f"token: {HEXKEY[:18]}\n       {HEXKEY[18:]}\n",
            # a shell string continued with a backslash
            "docs/continued.sh": f'export GITHUB_TOKEN="{HEXKEY[:12]}\\\n{HEXKEY[12:]}"\n',
        })
        out = self.assertRefused(self.safe_push(), "secret scan")
        self.assertFlagged(out, "docs/notes.md", "scripts/settings.py", "docs/wrapped.txt",
                           "docs/continued.sh")
        self.assertNotIn(TOKEN, out, "the report repeats the secret")
        self.assertNotIn(TOKEN[half:], out, "the report repeats half of the secret")


class EncodedSecrets(Edge):
    """(2) A credential-like value base64-encoded in a text file."""

    def test_base64_encoded_credentials_refused(self):
        def b64(s: str) -> str:
            return base64.b64encode(s.encode()).decode()
        assignment = f'api_token = "{TOKEN}"'
        # base64 lines of 76 columns hold 57 bytes: the token starts on the first line, with
        # too little of it there for the token rule, and ends on the second.
        prefix = "A note, padded so that the wrap cuts the token: "
        self.assertTrue(23 < len(prefix) < 57 < len(prefix) + len(GH_TOKEN))
        wrapped = base64.encodebytes((prefix + GH_TOKEN + " and more after it.\n").encode())
        self.commit("Encoded credentials", {
            "docs/blob.txt": f"config: {b64(assignment)}\n",
            "docs/key.txt": b64(f"{KEY_HEADER}\nMIIEowIBAAKCAQEA\n") + "\n",
            "docs/value.txt": f"value = {b64(GH_TOKEN)}\n",
            "docs/wrapped.txt": wrapped.decode(),          # 76 columns, cut mid-token
        })
        out = self.assertRefused(self.safe_push(), "secret scan")
        self.assertFlagged(out, "docs/blob.txt", "docs/key.txt", "docs/value.txt",
                           "docs/wrapped.txt")
        self.assertIn("base64", out)
        self.assertNotIn(b64(assignment), out, "the report repeats the encoded secret")


class RenamedSecrets(Edge):
    """(3) A credential file under a renamed path; a file renamed to a key file's name."""

    def test_credential_file_added_then_renamed_refused(self):
        self.commit("Add a key file", {"deploy/server.key": "not really a key\n"})
        git(WORK, "mv", "deploy/server.key", "deploy/server.txt")
        git(WORK, "commit", "-q", "-m", "Rename it to something plain")
        out = self.assertRefused(self.safe_push(), "secret scan")
        self.assertFlagged(out, "deploy/server.key")
        self.assertIn("key file", out)

    def test_existing_files_renamed_to_key_names_refused(self):
        renames = {"docs/examples.md": "docs/examples.pem", "docs/reading.md": "docs/reading.key",
                   "docs/references.bib": "docs/.env"}
        for old, new in renames.items():
            git(WORK, "mv", old, new)
        git(WORK, "commit", "-q", "-m", "Rename three files")
        out = self.assertRefused(self.safe_push(), "secret scan")
        self.assertFlagged(out, *renames.values())

    def test_secret_added_and_removed_within_the_push_refused(self):
        # The push carries every commit, so a secret in the history is published even
        # when a later commit of the same push takes it out again.
        self.commit("Plant a token", {"docs/notes.md": f"api_token = \"{TOKEN}\"\n",
                                      "deploy/.env": "PLAIN=1\n"})
        self.commit("Take it out again", remove=["docs/notes.md", "deploy/.env"])
        out = self.assertRefused(self.safe_push(), "secret scan")
        self.assertFlagged(out, "docs/notes.md", "deploy/.env")
        self.assertIn("in commit", out)


class Symlinks(Edge):
    """(4) A symlink added that points into a private directory, or out of the repository."""

    def link(self, links: dict) -> None:
        for path, target in links.items():
            os.symlink(target, WORK / path)
            git(WORK, "add", "--", path)

    def test_symlink_into_a_private_directory_refused(self):
        links = {"docs/inbox": TILDE_DOWNLOADS, "docs/scans": PRIVATE_SCANS,
                 "docs/notes": PRIVATE_DIR, "docs/elsewhere": "../../../elsewhere/notes.txt",
                 "docs/etc": "/etc/hosts"}
        self.link(links)
        git(WORK, "commit", "-q", "-m", "Links out of the repository")
        out = self.assertRefused(self.safe_push(), "secret scan")
        self.assertFlagged(out, *links)

    def test_symlink_within_the_repository_passes_the_scan(self):
        self.link({"docs/readme": "../README.md"})
        git(WORK, "commit", "-q", "-m", "A link within the repository")
        r = self.safe_push("--dry-run")
        self.assertEqual(self.guard(r.stdout, "secrets"), "ok", r.stdout + r.stderr)


SIGNATURE_WRAPPED = "theorem Prop1 (A B : Point)\n    (hAB : A ≠ B)\n    (P : Point) :"


class DisguisedStatements(Edge):
    """(5) A statement change made to look like whitespace; a decision naming another
    proposition."""

    LEAN = "Elements/BookI/Prop01.lean"

    def changed(self, new: str) -> dict:
        return {self.LEAN: self.replaced(self.LEAN, SIGNATURE_OLD, new)}

    def assertStatementRefused(self, ref="I.1"):
        out = self.assertRefused(self.safe_push(), f"{ref}: the Lean statement changed")
        self.assertEqual(self.guard(out, "statements"), "FAIL", out)
        return out

    def test_rewrap_alone_passes_the_statement_guard(self):
        self.commit("Re-wrap I.1's statement", self.changed(SIGNATURE_WRAPPED))
        r = self.safe_push("--dry-run")
        self.assertEqual(self.guard(r.stdout, "statements"), "ok", r.stdout)

    def test_hypothesis_changed_on_a_rewrapped_line_refused(self):
        self.commit("Re-wrap I.1's statement", self.changed(
            SIGNATURE_WRAPPED.replace("A ≠ B", "B ≠ A")))
        self.assertStatementRefused()

    def test_binder_changed_on_a_rewrapped_line_refused(self):
        self.commit("Re-wrap I.1's statement", self.changed(
            SIGNATURE_WRAPPED.replace("(P : Point)", "{P : Point}")))
        self.assertStatementRefused()

    def test_decision_naming_a_different_proposition_refused(self):
        changes = self.changed(SIGNATURE_NEW)
        changes.update(self.decision(
            "I.10, II.1 and III.1 keep their statements; `BookI.Prop10` and\n  I. 11 change."))
        self.commit("Change I.1's statement, with a decision about others", changes)
        self.assertStatementRefused()

    def test_old_brief_line_edited_does_not_approve_a_change(self):
        # A line of a brief that already named I.1, edited in place, is not a decision
        # about I.1's new statement.
        changes = self.changed(SIGNATURE_NEW)
        brief = "docs/briefs/0003-book-II.md"
        changes[brief] = self.replaced(brief, "System E's rules, as I.1 does);",
                                       "System E's rules, just as I.1 does);")
        self.commit("Change I.1's statement, touching an old line naming it", changes)
        self.assertStatementRefused()

    def test_change_after_an_inner_assignment_compared(self):
        # The statement runs to its own `:=`, not to the first one in a binder or comment.
        src = ("/-- A test statement. -/\n"
               "theorem Prop7 (A B : Point) (h : A ≠ B := by decide) -- a := b\n"
               "    (P : Point) :\n    A = B := by\n  sorry\n")
        statement = safe_push.source_statement(src, 7, None)
        for old, new in (("A = B := by", "B = A := by"), ("(P : Point)", "{P : Point}")):
            other = safe_push.source_statement(src.replace(old, new), 7, None)
            self.assertNotEqual(statement, other, f"{old} -> {new} not seen")
        self.assertTrue(statement.endswith("A = B"), statement)


class LockDecisions(Edge):
    """(6) An axioms.lock change with a decisions entry that does not mention the lock."""

    LOCK = "Certificate/axioms.lock"
    DECISIONS = DECISIONS

    def weakened(self) -> dict:
        line = '"Postulate1" = "∀ (A B : Elements.Point), Ne A B → Exists'
        return {self.LOCK: self.replaced(self.LOCK, line, line.replace("Ne A B → ", ""))}

    def assertLockRefused(self):
        out = self.assertRefused(self.safe_push(), "axioms.lock changed")
        self.assertEqual(self.guard(out, "axiom lock"), "FAIL", out)

    def test_decision_not_mentioning_the_lock_refused(self):
        changes = self.weakened()
        changes.update(self.decision("Postulate 1 no longer asks for two distinct points."))
        self.commit("Weaken Postulate 1, with a decision silent on the lock", changes)
        self.assertLockRefused()

    def test_lock_mentioned_outside_the_decisions_page_refused(self):
        changes = self.weakened()
        brief = "docs/briefs/book-I.md"
        changes[brief] = self.text(brief) + "\nThe axiom lock changes (axioms.lock).\n"
        self.commit("Weaken Postulate 1 in axioms.lock (the axiom lock)", changes)
        self.assertLockRefused()

    def test_old_decisions_line_mentioning_the_lock_edited_refused(self):
        changes = self.weakened()
        changes[self.DECISIONS] = self.replaced(
            self.DECISIONS, "(../../Certificate/axioms.lock) holds the",
            "(../../Certificate/axioms.lock) keeps the")
        self.commit("Weaken Postulate 1, touching an old line on the lock", changes)
        self.assertLockRefused()


class GeneratedPages(Edge):
    """(7) A commit whose generated pages are stale: render.py would change them."""

    READING = "reading/I/01.md"

    def test_stale_generated_pages_refused(self):
        self.commit("Further reading, pages not regenerated", {
            self.READING: self.text(self.READING) + "- A line of further reading for the test.\n"})
        out = self.assertRefused(self.safe_push(), "book/I/01.md")
        self.assertEqual(self.guard(out, "generated pages"), "FAIL", out)

    def test_generated_page_edited_by_hand_refused(self):
        page = "book/I/01.md"
        self.commit("Edit a generated page by hand", {page: self.text(page) + "\nBy hand.\n"})
        out = self.assertRefused(self.safe_push(), page)
        self.assertEqual(self.guard(out, "generated pages"), "FAIL", out)

    def test_regenerated_pages_pass(self):
        (WORK / self.READING).write_text(self.text(self.READING)
                                         + "- A line of further reading for the test.\n")
        r = subprocess.run([sys.executable, "scripts/render.py"], cwd=WORK,
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        git(WORK, "add", "-u")
        git(WORK, "commit", "-q", "-m", "Further reading, pages regenerated")
        r = self.safe_push("--dry-run")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(self.guard(r.stdout, "generated pages"), "ok", r.stdout)


# Runs safe_push in a subprocess with `guards` or `watch_checks` wrapped, so that
# something happens at a chosen moment: origin's main moves, or an interruption.
DRIVER = r"""
import subprocess, sys
sys.path.insert(0, sys.argv[1])
import safe_push
action, origin, target = sys.argv[2], sys.argv[3], sys.argv[4]
real_guards, real_watch = safe_push.guards, safe_push.watch_checks
def guards(*args, **kwargs):
    result = real_guards(*args, **kwargs)
    if action == "move":
        subprocess.run(["git", "update-ref", "refs/heads/main", target], cwd=origin, check=True)
    elif action == "interrupt":
        raise KeyboardInterrupt("a test interruption")
    return result
def watch_checks(*args, **kwargs):
    if action == "watch-interrupt":
        raise KeyboardInterrupt("a test interruption")
    if action == "watch-fail":
        raise RuntimeError("gh went away")
    return real_watch(*args, **kwargs)
safe_push.guards = guards
safe_push.watch_checks = watch_checks
sys.exit(safe_push.main(sys.argv[5:]))
"""


class Ancestry(Edge):
    """(8) A commit that is not a descendant of origin/main; origin/main moving between
    the check and the push."""

    def drive(self, action: str, target: str, *args, env=None) -> subprocess.CompletedProcess:
        if not {"--branch", "--merge"} & set(args):
            args = ("--branch", BRANCH, *args)
        return subprocess.run([sys.executable, "-c", DRIVER, str(HERE), action, str(ORIGIN),
                               target, "--_test-skip-checks", *args], cwd=WORK,
                              env=env or clean_env(), capture_output=True, text=True)

    def test_commit_behind_origin_main_refused(self):
        newer = self.good_commit()
        git(WORK, "push", "--quiet", "origin", f"{newer}:refs/heads/side")
        self.addCleanup(lambda: git(ORIGIN, "update-ref", "-d", "refs/heads/side", check=False))
        git(ORIGIN, "update-ref", "refs/heads/main", newer)
        r = self.safe_push("--commit", BASE)      # an ancestor of origin/main: a rewind
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        self.assertIn("not a fast-forward", out)
        self.assertEqual(self.origin_main(), newer)

    def test_unrelated_history_refused(self):
        def cleanup():
            git(WORK, "checkout", "--quiet", "--force", "--detach", BASE)
            git(WORK, "branch", "-q", "-D", "unrelated", check=False)
        git(WORK, "checkout", "--quiet", "--orphan", "unrelated")
        self.addCleanup(cleanup)
        git(WORK, "rm", "-r", "-q", "--cached", ".")
        (WORK / "only.txt").write_text("A history of its own.\n")
        git(WORK, "add", "only.txt")
        git(WORK, "commit", "-q", "-m", "An unrelated root")
        orphan = git(WORK, "rev-parse", "HEAD").strip()
        r = self.safe_push("--commit", orphan)
        out = self.assertRefused(r, "not a fast-forward")
        self.assertEqual(self.guard(out, "fast-forward"), "FAIL", out)

    def test_origin_main_moves_during_the_checks_refused(self):
        side = self.side_commit()
        mine = self.good_commit()
        r = self.drive("move", side)
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        self.assertIn("moved", out)
        self.assertEqual(self.origin_main(), side, "the push went ahead over the new main")
        self.assertNotEqual(self.origin_main(), mine)
        self.assertIsNone(self.origin_branch(), "the branch was pushed over the new main")

    def test_origin_main_moves_at_the_push_refused(self):
        # Between safe_push's last look at origin and the push of the branch: the hook
        # runs inside `git push`, after git has read origin's refs. The branch goes up,
        # but the merge is refused: the head no longer holds main, so the tree checked is
        # not the tree a merge would make.
        side = self.side_commit()
        mine = self.good_commit()
        real = TMP / "real-pre-push"
        shutil.copy(HERE / "hooks" / "pre-push", real)
        self.swap_hook(f'#!/bin/sh\ngit -C "{ORIGIN}" update-ref refs/heads/main {side}\n'
                       f'exec sh "{real}" "$@"\n')
        r = self.safe_push()
        self.assertEqual(self.origin_branch(), mine, r.stdout + r.stderr)
        self.assertEqual(self.origin_main(), side)
        self.set_gh(lambda s: s["prs"][0].update(body=s["prs"][0]["body"].replace("- [ ]", "- [x]")))
        r = self.safe_push("--merge", "1")
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        self.assertIn("is not an ancestor", out)
        self.assertEqual(self.origin_main(), side, "the merge went ahead over the new main")


class HookRefspecs(Edge):
    """(9) The pre-push hook: every spelling of a push to main, a forced one, and a tag."""

    def push(self, *args, **env) -> subprocess.CompletedProcess:
        e = clean_env()
        e.update(env)
        return subprocess.run(["git", "push", *args], cwd=WORK, env=e, capture_output=True,
                              text=True)

    def tag(self, name: str, *args) -> None:
        git(WORK, "tag", *args, name)
        self.addCleanup(lambda: git(WORK, "tag", "-d", name, check=False))
        self.addCleanup(lambda: git(ORIGIN, "update-ref", "-d", f"refs/tags/{name}",
                                    check=False))

    def test_every_spelling_of_a_push_to_main_refused(self):
        sha = self.good_commit()
        git(WORK, "branch", "-f", "main", sha)
        self.addCleanup(lambda: git(WORK, "branch", "-f", "main", BASE))
        for args in (["origin", "HEAD:main"], ["origin", "refs/heads/main"], ["origin", "main"],
                     ["origin", f"{sha}:refs/heads/main"], ["origin", "+HEAD:main"],
                     ["--force", "origin", "HEAD:main"], ["--mirror", "origin"]):
            with self.subTest(args=args):
                r = self.push(*args)
                self.assertNotEqual(r.returncode, 0, r.stderr)
                self.assertIn("pre-push: refusing", r.stderr)
                self.assertEqual(self.origin_main(), BASE)

    def test_forced_push_refused_even_of_the_commit_checked(self):
        side = self.side_commit()
        git(ORIGIN, "update-ref", "refs/heads/main", side)
        mine = self.good_commit()                 # not a descendant of origin's main
        git(WORK, "fetch", "--quiet", "origin")
        r = self.push("origin", f"+{mine}:refs/heads/main", STOICHEIA_SAFE_PUSH=mine)
        self.assertNotEqual(r.returncode, 0, r.stderr)
        self.assertIn("refusing a push to main", r.stderr)
        self.assertEqual(self.origin_main(), side)

    def test_tag_push_refused(self):
        sha = self.good_commit()
        self.addCleanup(lambda: git(ORIGIN, "update-ref", "-d", "refs/heads/stoicheia-test-tagged",
                                    check=False))
        self.tag("stoicheia-test-light")
        self.tag("stoicheia-test-annotated", "-a", "-m", "An annotated tag for the test")
        for args, env in ((["origin", "stoicheia-test-light"], {}),
                          (["origin", "refs/tags/stoicheia-test-light"], {}),
                          (["--tags", "origin"], {}),
                          (["--follow-tags", "origin", "HEAD:refs/heads/stoicheia-test-tagged"],
                           {}),
                          (["origin", "stoicheia-test-light"], {"STOICHEIA_SAFE_PUSH": sha})):
            with self.subTest(args=args, env=env):
                r = self.push(*args, **env)
                self.assertNotEqual(r.returncode, 0, r.stderr)
                self.assertIn("pre-push: refusing to push or delete the tag", r.stderr)
                self.assertEqual(git(ORIGIN, "tag", "--list", "stoicheia-test-*"), "")
                self.assertEqual(git(ORIGIN, "branch", "--list", "stoicheia-test-*"), "")
        # Deleting a tag on origin is refused too.
        r = self.push("origin", f"{sha}:refs/heads/stoicheia-test-tagged")   # a branch passes
        self.assertEqual(r.returncode, 0, r.stderr)
        git(ORIGIN, "update-ref", "refs/tags/stoicheia-test-light", sha)
        r = self.push("origin", ":refs/tags/stoicheia-test-light")
        self.assertNotEqual(r.returncode, 0, r.stderr)
        self.assertIn("stoicheia-test-light", git(ORIGIN, "tag", "--list"))
        # With the owner's OK, a tag is pushed by name.
        git(ORIGIN, "update-ref", "-d", "refs/tags/stoicheia-test-light")
        r = self.push("origin", "stoicheia-test-light", STOICHEIA_TAG_PUSH="stoicheia-test-light")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("the secret scan of the push to refs/tags/stoicheia-test-light",
                      r.stdout + r.stderr)

    def test_allowed_tag_still_scanned(self):
        # Review note 12: the owner's OK for a tag does not publish an unscanned commit, nor
        # an annotated tag's message holding a private path.
        self.commit("Plant a token", {"docs/notes.md": f"api_token = \"{TOKEN}\"\n"})
        self.tag("stoicheia-test-secret")
        r = self.push("origin", "refs/tags/stoicheia-test-secret",
                      STOICHEIA_TAG_PUSH="stoicheia-test-secret")
        self.assertNotEqual(r.returncode, 0, r.stderr)
        self.assertIn("pre-push: refusing the push to refs/tags/stoicheia-test-secret", r.stderr)
        self.assertNotIn(TOKEN, r.stdout + r.stderr)
        git(WORK, "checkout", "--quiet", "--force", "--detach", BASE)
        self.good_commit()
        self.tag("stoicheia-test-message", "-a", "-m", f"Notes in {PRIVATE_DIR}")
        r = self.push("origin", "refs/tags/stoicheia-test-message",
                      STOICHEIA_TAG_PUSH="stoicheia-test-message")
        self.assertNotEqual(r.returncode, 0, r.stderr)
        self.assertIn("its message holds what the secret scan refuses", r.stderr)
        self.assertEqual(git(ORIGIN, "tag", "--list", "stoicheia-test-*"), "")


class DryRun(Edge):
    """(10) --dry-run never pushes, calls no gh, and leaves no worktree, on success or
    failure."""

    LOCK = LockDecisions.LOCK
    weakened = LockDecisions.weakened

    def run_dry(self, *args, driver=None) -> tuple[subprocess.CompletedProcess, Path]:
        tmp = Path(tempfile.mkdtemp(prefix="dry-run-tmp-", dir=TMP))
        calls = TMP / "pre-push-calls"
        calls.unlink(missing_ok=True)
        real = TMP / "real-pre-push"
        shutil.copy(HERE / "hooks" / "pre-push", real)
        self.swap_hook(f'#!/bin/sh\necho called >> "{calls}"\nexec sh "{real}" "$@"\n')
        env = clean_env()
        env["TMPDIR"] = str(tmp)
        refs = git(ORIGIN, "for-each-ref")
        if driver:
            r = subprocess.run([sys.executable, "-c", DRIVER, str(HERE), driver, str(ORIGIN),
                                BASE, "--_test-skip-checks", "--dry-run", *args], cwd=WORK,
                               env=env, capture_output=True, text=True)
        else:
            r = self.safe_push("--dry-run", *args, env=env)
        out = r.stdout + r.stderr
        self.assertEqual(git(ORIGIN, "for-each-ref"), refs, f"origin's refs changed:\n{out}")
        self.assertFalse(calls.exists(), f"git push was run:\n{out}")
        self.assertEqual(self.gh_state()["calls"], [], f"gh was called:\n{out}")
        self.assertEqual(len(git(WORK, "worktree", "list").splitlines()), 1,
                         f"a temporary worktree was left behind:\n{out}")
        admin = Path(git(WORK, "rev-parse", "--git-common-dir").strip())
        admin = admin if admin.is_absolute() else WORK / admin
        self.assertEqual(list((admin / "worktrees").glob("*")) if (admin / "worktrees").exists()
                         else [], [], "worktree metadata was left behind")
        self.assertEqual(list(tmp.iterdir()), [], "temporary files were left behind")
        return r, tmp

    def test_dry_run_on_success(self):
        self.good_commit()
        r, _ = self.run_dry()
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("would push", r.stdout)

    def test_dry_run_refused_in_the_guards(self):
        self.commit("Weaken Postulate 1 in the lock", self.weakened())
        r, _ = self.run_dry()
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("REFUSED", r.stdout)

    def test_dry_run_refused_in_the_secret_scan(self):
        self.commit("Plant a token", {"docs/notes.md": f"api_token = \"{TOKEN}\"\n"})
        r, _ = self.run_dry()
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)

    def test_dry_run_interrupted(self):
        self.good_commit()
        r, _ = self.run_dry(driver="interrupt")
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("Interrupted", r.stdout)


# --------------------------------------------------------------------------------------
# A: the pre-flight's pull request, and --merge


def ticked(body: str) -> str:
    return body.replace("- [ ] **Required", "- [x] **Required")


class PullRequests(Edge):
    def test_branch_main_refused(self):
        sha = self.good_commit()
        for name in ("main", "refs/heads/main", "Main", "HEAD"):
            with self.subTest(name=name):
                self.assertRefused(self.safe_push("--branch", name), f"--branch {name}")
        self.assertEqual(self.origin_main(), BASE)
        self.assertEqual(git(ORIGIN, "for-each-ref", "--format=%(refname)", "refs/heads/"),
                         "refs/heads/main\n")
        self.assertNotEqual(sha, BASE)

    def test_direct_push_to_main_refused(self):
        self.good_commit()
        for args in ([], ["--commit", "HEAD"]):
            with self.subTest(args=args):
                r = subprocess.run([sys.executable, str(SAFE_PUSH), "--_test-skip-checks", *args],
                                   cwd=WORK, env=clean_env(), capture_output=True, text=True)
                self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
                self.assertIn("no longer pushes to main", r.stdout)
                self.assertIn("--branch <name>", r.stdout)
        self.assertEqual(self.origin_main(), BASE)
        self.assertEqual(self.gh_state()["calls"], [])

    def test_usage_errors(self):
        for args in (["--merge", "1", "--branch", "x"], ["--title", "T"],
                     ["--branch", "x", "--label", "nonsense"], ["--branch", "x", "--body-file",
                                                                 str(TMP / "none.md")]):
            with self.subTest(args=args):
                r = subprocess.run([sys.executable, str(SAFE_PUSH), *args], cwd=WORK,
                                   env=clean_env(), capture_output=True, text=True)
                self.assertEqual(r.returncode, 2, r.stdout + r.stderr)

    def test_update_keeps_the_coordinators_words(self):
        first = self.good_commit()
        r = self.safe_push("--draft", "--label", "docs")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        (pr,) = self.gh_state()["prs"]
        self.assertTrue(pr["isDraft"])
        self.assertEqual(pr["labels"], ["docs"])
        self.assertIn(f"sha={first}", pr["body"])
        # The coordinator writes the reviews in; a fix lands on the branch, and the
        # pre-flight runs again: the summary is replaced, and nothing else.
        words = "| /code-review | abc1234 | One material finding, resolved in the fix. |"
        self.set_gh(lambda s: s["prs"][0].update(
            body=s["prs"][0]["body"].replace("| /code-review | | |", words)))
        second = self.good_commit("A second line, the fix.")
        r = self.safe_push()
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, out)
        self.assertIn("#1 updated", out)
        (pr,) = self.gh_state()["prs"]
        self.assertIn(words, pr["body"])
        self.assertIn(f"sha={second}", pr["body"])
        self.assertNotIn(f"sha={first}", pr["body"])
        self.assertEqual(pr["body"].count("safe_push:preflight begin"), 1)
        self.assertEqual(self.origin_branch(), second)

    def test_body_file(self):
        self.good_commit()
        body = TMP / "body.md"
        body.write_text("A body of my own.\n\n<!-- safe_push: commits -->\n\n"
                        "<!-- safe_push: preflight -->\n")
        r = self.safe_push("--title", "My title", "--body-file", str(body))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        (pr,) = self.gh_state()["prs"]
        self.assertEqual(pr["title"], "My title")
        self.assertTrue(pr["body"].startswith("A body of my own."))
        self.assertIn("Commits (", pr["body"])
        self.assertIn("safe_push:preflight begin", pr["body"])

    def test_branch_with_commits_this_one_lacks_refused(self):
        theirs = self.good_commit("Their line.")
        git(WORK, "push", "--quiet", "origin", f"{theirs}:refs/heads/{BRANCH}")
        git(WORK, "checkout", "--quiet", "--detach", BASE)
        self.good_commit("My line.")
        r = self.safe_push()
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        self.assertIn("has commits", out)
        self.assertEqual(self.origin_branch(), theirs, "the branch was forced")

    def test_a_forks_pull_request_of_the_same_name_is_left_alone(self):
        # Review note 7: `gh pr list --head` matches a fork's branch of the same name; the
        # pre-flight opens a pull request of its own, and never edits the stranger's.
        sha = self.good_commit()
        stranger = {"number": 1, "title": "A stranger's", "body": "A stranger's body.\n",
                    "headRefName": BRANCH, "baseRefName": "main", "isDraft": False,
                    "labels": [], "state": "OPEN", "isCrossRepository": True,
                    "headRepositoryOwner": {"login": "stranger"}, "forkHead": "f" * 40,
                    "url": "https://github.invalid/test/stoicheia/pull/1"}
        self.set_gh(lambda s: s["prs"].append(stranger))
        r = self.safe_push()
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, out)
        self.assertIn("#2 opened", out)
        theirs, ours = self.gh_state()["prs"]
        self.assertEqual((theirs["body"], theirs["labels"]), (stranger["body"], []))
        self.assertIn(f"sha={sha}", ours["body"])
        edits = [c for c in self.gh_state()["calls"] if c[:2] == ["pr", "edit"]]
        self.assertEqual(edits, [], "the stranger's pull request was edited")

    def test_public_names_scanned_before_the_push(self):
        # Review note 9: the title is posted, and the branch name pushed as a ref.
        self.good_commit()
        self.assertRefused(self.safe_push("--title", f"Notes from {PRIVATE_DIR}"),
                           "a public name", "the title")
        name = "secret" + "s2026-notes"
        out = self.assertRefused(self.safe_push("--branch", name), "the branch name")
        self.assertIsNone(self.origin_branch(name), out)
        self.assertEqual(self.gh_state()["calls"], [])

    def test_open_pull_requests_body_scanned_before_the_push(self):
        first = self.good_commit()
        self.assertEqual(self.safe_push().returncode, 0)
        self.set_gh(lambda s: s["prs"][0].update(body=s["prs"][0]["body"]
                                                 + f"\nSee {PRIVATE_DIR}.\n"))
        self.good_commit("A second line, the fix.")
        r = self.safe_push()
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        self.assertIn("the pull request's body holds what the secret scan refuses", out)
        self.assertEqual(self.origin_branch(), first, "the fix was pushed before the body "
                         "was checked")

    def test_hand_edit_to_program_md_is_not_a_generated_change(self):
        # Review note 11: README.md and PROGRAM.md are generated only between markers.
        path = "docs/PROGRAM.md"
        self.commit("A lesson, by hand", {path: self.replaced(
            path, "## 6. Cost and time", "- **A lesson for the test.**\n\n## 6. Cost and time")})
        r = self.safe_push("--dry-run")
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, out)
        body = Path(re.search(r"the body it would post: (\S+)", out).group(1)).read_text()
        generated = body[body.index("## Generated files"):body.index("## Needs the owner's OK")]
        self.assertIn("None.", generated)
        self.assertNotIn("PROGRAM.md", generated)

    def test_ci_failing_after_the_push(self):
        sha = self.good_commit()
        failing = [dict(c, bucket="fail", state="FAILURE") if c["name"] == "negative" else c
                   for c in PASSING]
        self.set_gh(lambda s: s["checks"].update({sha: failing}))
        r = self.safe_push()
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 3, out)
        self.assertIn("CI did not pass", out)
        self.assertIn("failing: negative", out)
        self.assertEqual(self.origin_main(), BASE)


class Merge(Edge):
    def opened(self, *args, **write) -> str:
        sha = self.good_commit() if not write else self.commit("A change", write)
        r = self.safe_push(*args)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        return sha

    def merge(self, *args) -> subprocess.CompletedProcess:
        return self.safe_push("--merge", "1", *args)

    def test_merge_waits_for_the_gates(self):
        sha = self.opened("--draft")
        failing = [dict(c, bucket="pending", state="IN_PROGRESS") for c in PASSING]
        self.set_gh(lambda s: s["checks"].update({sha: failing}))
        r = self.merge()
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        for gate in ("draft", "checklist", "CI"):
            self.assertEqual(self.guard(out, gate), "FAIL", f"{gate}:\n{out}")
        self.assertIn("unticked: Required:", out)
        self.assertIn("still running", out)
        self.assertEqual(self.origin_main(), BASE)
        self.assertEqual(self.origin_branch(), sha)

    def test_merge_with_a_merge_commit(self):
        sha = self.opened()
        self.set_gh(lambda s: s["prs"][0].update(body=ticked(s["prs"][0]["body"])))
        r = self.merge("--dry-run")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("would merge", r.stdout)
        self.assertEqual(self.origin_main(), BASE)
        r = self.merge()
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, out)
        main = self.origin_main()
        self.assertEqual(git(ORIGIN, "rev-list", "--parents", "-n", "1", main).split()[1:],
                         [BASE, sha], "not a merge commit of main and the head")
        self.assertIsNone(self.origin_branch(), "the branch was not deleted")
        merges = [c for c in self.gh_state()["calls"] if c[:2] == ["pr", "merge"]]
        self.assertEqual(len(merges), 1)
        self.assertIn("--merge", merges[0])
        self.assertIn(sha, merges[0])               # --match-head-commit
        self.assertFalse({"--squash", "--rebase", "--admin", "--auto"} & set(merges[0]))
        self.assertEqual(self.guard(out, "main"), "ok", out)

    def test_missing_required_box_refused(self):
        self.opened()
        drop = "- [ ] **Required:** Nothing public goes out without the owner's OK.\n"

        def edit(s):
            body = s["prs"][0]["body"]
            assert drop in body
            s["prs"][0]["body"] = ticked(body.replace(drop, ""))
        self.set_gh(edit)
        out = self.merge().stdout
        self.assertIn("missing from the body: Required: Nothing public", out)
        self.assertEqual(self.origin_main(), BASE)

    def test_new_head_gets_its_preflight_at_the_merge(self):
        self.opened()
        self.set_gh(lambda s: s["prs"][0].update(body=ticked(s["prs"][0]["body"])))
        # A commit pushed to the branch by hand: the pre-flight has not seen it.
        newer = self.good_commit("A line pushed by hand.")
        git(WORK, "push", "--quiet", "origin", f"{newer}:refs/heads/{BRANCH}")
        r = self.merge()
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, out)
        self.assertIn(f"none of {newer[:12]}", out)
        self.assertEqual(git(ORIGIN, "rev-parse", "refs/heads/main^2").strip(), newer)
        self.assertIn(f"sha={newer}", self.gh_state()["prs"][0]["body"])

    def test_merge_runs_the_scan_and_the_guards_again(self):
        # Review note 6: the pre-flight's record stands in for the full checks alone.
        self.opened()
        self.set_gh(lambda s: s["prs"][0].update(body=ticked(s["prs"][0]["body"])))
        out = self.merge("--dry-run").stdout
        self.assertIn("the full checks are not repeated", out)
        for name in ("secrets", "statements", "protected paths", "heath/", "review records"):
            self.assertEqual(self.guard(out, name), "ok", f"{name}:\n{out}")

    def test_forged_record_does_not_skip_the_scan_or_the_guards(self):
        # A record in the local store, as code the pre-flight ran could write it, for a
        # head pushed by hand that plants a token and edits Heath with no leaf named.
        self.opened()
        self.set_gh(lambda s: s["prs"][0].update(body=ticked(s["prs"][0]["body"])))
        bad = self.commit("A head pushed by hand", {
            "docs/notes.md": f"api_token = \"{TOKEN}\"\n",
            "heath/I/01.md": self.replaced("heath/I/01.md", *Heath.WORD)})
        git(WORK, "push", "--quiet", "--no-verify", "origin", f"{bad}:refs/heads/{BRANCH}")
        harness = safe_push.blob_id(SAFE_PUSH.read_bytes())
        record = {"sha": bad, "base": BASE, "branch": BRANCH, "full": True,
                  "time": "forged", "harness": "origin/main's", "harness_blob": harness,
                  "steps": [["2", "secrets", "ok", 0.1], ["4", "lake build", "ok", 1.0]],
                  "notes": [], "protected": [], "statements": []}
        path = LOG.parent / "preflight" / f"{bad}-{BASE}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(record))
        r = self.merge()
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        self.assertEqual(self.guard(out, "secrets"), "FAIL", out)
        self.assertEqual(self.origin_main(), BASE)
        # A record of another harness stands in for nothing: the full checks run again.
        git(WORK, "checkout", "--quiet", "--force", "--detach", BASE)
        record.update(harness_blob="0" * 40, sha=self.good_commit("Another line."))
        git(WORK, "push", "--quiet", "--no-verify", "origin",
            f"+{record['sha']}:refs/heads/{BRANCH}")
        (LOG.parent / "preflight" / f"{record['sha']}-{BASE}.json").write_text(json.dumps(record))
        r = self.merge("--dry-run")
        self.assertIn("is not of the full checks by origin/main's harness", r.stdout)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_bad_new_head_refused_at_the_merge(self):
        self.opened()
        self.set_gh(lambda s: s["prs"][0].update(body=ticked(s["prs"][0]["body"])))
        bad = self.commit("Edit a Heath word by hand", {"heath/I/01.md": self.replaced(
            "heath/I/01.md", *Heath.WORD)})
        git(WORK, "push", "--quiet", "origin", f"{bad}:refs/heads/{BRANCH}")
        r = self.merge()
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        self.assertEqual(self.guard(out, "heath/"), "FAIL", out)
        self.assertEqual(self.origin_main(), BASE)

    def test_protected_change_needs_its_label(self):
        path = "scripts/check_style.py"
        change = {path: self.text(path) + "\n# A comment for the test.\n"}
        change.update(self.decision(f"A comment in `{path}`, for the test."))
        self.opened(**change)
        (pr,) = self.gh_state()["prs"]
        self.assertIn("security-review", pr["labels"])
        self.assertIn(f"`{path}`", pr["body"])
        # Without the label, or with the security review's box unticked, no merge.
        self.set_gh(lambda s: s["prs"][0].update(labels=[], body=ticked(s["prs"][0]["body"])))
        out = self.merge().stdout
        self.assertIn("lacks the label security-review", out)
        self.set_gh(lambda s: s["prs"][0].update(
            labels=["security-review"],
            body=s["prs"][0]["body"].replace("- [x] **Required if protected:**",
                                             "- [ ] **Required if protected:**")))
        out = self.merge().stdout
        self.assertIn("unticked: Required if protected:", out)
        self.assertEqual(self.origin_main(), BASE)
        self.set_gh(lambda s: s["prs"][0].update(body=s["prs"][0]["body"].replace(
            "- [ ] **Required if protected:**", "- [x] **Required if protected:**")))
        r = self.merge()
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)


# --------------------------------------------------------------------------------------
# B: the review's findings, each with a planted commit


class ProtectedPaths(Edge):
    """(1) The guards and the check scripts are origin/main's; a protected path changes
    only with a decisions entry naming it, and the label."""

    def test_protected_change_without_a_decision_refused(self):
        for path in ("scripts/check_style.py", ".github/workflows/ci.yml",
                     "tests/model/MODEL.md", "review/terms.toml", ".gitattributes",
                     ".gitignore", "lakefile.lean"):
            with self.subTest(path=path):
                git(WORK, "checkout", "--quiet", "--force", "--detach", BASE)
                old = self.text(path) if (WORK / path).exists() else ""
                self.commit(f"Touch {path}", {path: old + "\n# for the test\n"})
                out = self.assertRefused(self.safe_push(), "protected paths", path)
                self.assertEqual(self.guard(out, "protected paths"), "FAIL", out)

    def test_decision_naming_another_file_does_not_count(self):
        changes = {"scripts/check_style.py": self.text("scripts/check_style.py") + "\n# x\n"}
        changes.update(self.decision("A comment in `scripts/check_links.py`."))
        self.commit("Touch check_style.py, naming check_links.py", changes)
        self.assertRefused(self.safe_push(), "naming them: scripts/check_style.py")

    def test_weakened_check_judged_by_origin_mains_copy(self):
        # The commit makes check_fidelity.py pass whatever it finds, and changes a Lean
        # file under a review record: origin/main's copy finds the record stale, and says
        # so; the commit's own copy passes. With the decisions entry the pre-flight goes
        # on, and the finding goes to the security review, in the body. (The pages are
        # regenerated: PROGRAM.md's status table counts the stale record.)
        path = "scripts/check_fidelity.py"
        lean = "Elements/BookI/Prop01.lean"
        changes = {path: self.replaced(path, 'if __name__ == "__main__":\n',
                                       'if __name__ == "__main__":\n    sys.exit(0)\n'),
                   lean: self.text(lean) + "\n-- A comment for the test.\n"}
        changes.update(self.decision(f"`{path}` is changed for the test."))
        for rel, text in changes.items():
            (WORK / rel).write_text(text)
        r = subprocess.run([sys.executable, "scripts/render.py"], cwd=WORK,
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        git(WORK, "add", "-u")
        sha = self.commit("Weaken check_fidelity.py")
        r = self.safe_push()
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, out)
        self.assertEqual(self.guard(out, "review records (origin/main's checks)"), "note", out)
        self.assertEqual(self.guard(out, "review records (the commit's checks)"), "ok", out)
        self.assertEqual(self.origin_branch(), sha)
        (pr,) = self.gh_state()["prs"]
        self.assertIn("security-review", pr["labels"])
        self.assertIn("review records (origin/main's checks): check_fidelity.py fails", pr["body"])
        self.assertEqual(len(git(WORK, "worktree", "list").splitlines()), 1)
        # Review note 11: --merge shows the notes beside the checklist, for the reviews.
        self.set_gh(lambda s: s["prs"][0].update(body=ticked(s["prs"][0]["body"])))
        r = self.safe_push("--merge", "1", "--dry-run")
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, out)
        self.assertEqual(self.guard(out, "pre-flight notes"), "note", out)
        notes = out[out.index("pre-flight notes"):]
        self.assertIn("review records (origin/main's checks): check_fidelity.py fails", notes)

    def test_harness_runs_from_origin_main(self):
        # The commit empties its own copy of the secret scan and plants a token; run from
        # the commit's checkout, its copy hands over to origin/main's, which refuses it.
        lame = self.replaced("scripts/safe_push.py", "def secret_scan(",
                             "def secret_scan(*a, **k):\n    return None\n\n\ndef _unused(")
        self.commit("Empty the scan, and plant a token", {
            "scripts/safe_push.py": lame, "docs/notes.md": f"api_token = \"{TOKEN}\"\n"})
        out = self.assertRefused(self.safe_push(script=WORK / "scripts" / "safe_push.py"),
                                 "running origin/main's in its place", "secret scan")
        self.assertEqual(self.guard(out, "harness"), "ok", out)

    def test_allow_list_entry_added_by_the_push_does_not_count(self):
        self.commit("A flagged line, with its own allow-list entry", {
            "docs/notes.md": f"api_token = \"{TOKEN}\"\n",
            "scripts/safe_push_allow.toml": Secrets.ALLOW})
        out = self.assertRefused(self.safe_push(), "secret scan")
        self.assertFlagged(out, "docs/notes.md")

    def test_protected_paths_listed(self):
        for path in ("scripts/safe_push.py", "scripts/hooks/pre-push", ".github/workflows/ci.yml",
                     ".github/pull_request_template.md", "Certificate/axioms.lock",
                     "Certificate/Facts.lean", "tests/certificate_expectations.json",
                     "review/SCHEMA.md", "review/terms.toml", ".gitattributes",
                     ".gitignore", "lakefile.toml", "lakefile.lean", "lean-toolchain",
                     "lake-manifest.json", "scripts/hooks/safe-push"):
            self.assertTrue(safe_push.is_protected(path), path)
        # The guides and the template name the same paths.
        workflow = (SOURCE / "docs" / "WORKFLOW.md").read_text()
        template = (SOURCE / ".github" / "pull_request_template.md").read_text()
        for name in ("lakefile.lean", ".gitignore"):
            self.assertIn(f"`{name}`", workflow, name)
            self.assertIn(name, template, name)
        for path in ("docs/WORKFLOW.md", "review/I/01.toml", "Elements/BookI/Prop01.lean",
                     "heath/I/01.md", "scriptsx/a.py", "book/I/01.md"):
            self.assertFalse(safe_push.is_protected(path), path)


class InterruptedAfterThePush(Edge):
    """(4) An interruption or a failure to follow CI after the push is "pushed; CI not
    followed", exit 3; never "interrupted", exit 1."""

    def drive(self, action: str) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, "-c", DRIVER, str(HERE), action, str(ORIGIN),
                               BASE, "--_test-skip-checks", "--branch", BRANCH], cwd=WORK,
                              env=clean_env(), capture_output=True, text=True)

    def test_interrupt_while_following_ci(self):
        sha = self.good_commit()
        r = self.drive("watch-interrupt")
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 3, out)
        self.assertIn("pushed; CI not followed", out)
        self.assertNotIn("Interrupted:", out)
        self.assertEqual(self.origin_branch(), sha)
        self.assertIn("pushed; CI not followed", LOG.read_text().splitlines()[-1])

    def test_failure_while_following_ci(self):
        self.good_commit()
        r = self.drive("watch-fail")
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 3, out)
        self.assertIn("pushed; CI not followed (RuntimeError: gh went away)", out)


class HandOver(Edge):
    """Review notes 2, 3 and 6: origin/main's harness replaces a copy that differs, so an
    interruption after its push is still exit 3; the launcher runs origin/main's copy
    whatever the checkout holds; STOICHEIA_HARNESS is checked; the installed hook and
    launcher are compared with origin/main's."""

    def differing_copy(self, change=None) -> Path:
        """A copy of the harness outside the clone that differs from origin/main's."""
        where = Path(tempfile.mkdtemp(prefix="differing-", dir=TMP))
        text = SAFE_PUSH.read_text()
        text = change(text) if change else text + "\n# A copy that differs.\n"
        (where / "safe_push.py").write_text(text)
        shutil.copy(HERE / "heath.py", where / "heath.py")
        return where / "safe_push.py"

    def interrupted(self, signum: int) -> None:
        sha = self.good_commit()
        pidfile = TMP / f"safe-push-{signum}.pid"
        pidfile.unlink(missing_ok=True)
        env = clean_env()
        env["STOICHEIA_FAKE_GH_KILL"] = f"{pidfile}:{signum}"
        proc = subprocess.Popen(
            [sys.executable, str(self.differing_copy()), "--_test-skip-checks", "--branch",
             BRANCH], cwd=WORK, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, preexec_fn=lambda: signal.signal(signal.SIGINT, signal.SIG_DFL))
        pidfile.write_text(str(proc.pid))
        out, _ = proc.communicate(timeout=300)
        self.assertIn("running origin/main's in its place", out)
        self.assertEqual(proc.returncode, 3, out)
        self.assertIn("Pushed; CI not followed: interrupted", out)
        self.assertIn("pushed; CI not followed", LOG.read_text().splitlines()[-1])
        self.assertEqual(self.origin_branch(), sha)
        self.assertEqual(len(git(WORK, "worktree", "list").splitlines()), 1)

    def test_ctrl_c_after_the_push_of_a_handed_over_run(self):
        self.interrupted(signal.SIGINT)

    def test_sigterm_after_the_push_of_a_handed_over_run(self):
        # A supervisor's timeout signals the process it started, and nothing else.
        self.interrupted(signal.SIGTERM)

    def test_launcher_runs_origin_mains_copy(self):
        # The checkout's copy never hands over, and does not scan; a token is planted. The
        # launcher runs origin/main's copy, which refuses it.
        lame = self.replaced("scripts/safe_push.py", "def harness(repo, base: str, rep: Report)"
                             " -> None:\n", "def harness(repo, base, rep):\n    return None\n\n\n"
                             "def _unused(repo, base: str, rep: Report) -> None:\n")
        lame = lame.replace("def secret_scan(", "def secret_scan(*a, **k):\n    return None\n\n\n"
                            "def _unused_scan(", 1)
        self.commit("A harness that judges itself, and a token", {
            "scripts/safe_push.py": lame, "docs/notes.md": f"api_token = \"{TOKEN}\"\n"})
        r = subprocess.run(["git", "safe-push", "--_test-skip-checks", "--branch", BRANCH],
                           cwd=WORK / "docs", env=clean_env(), capture_output=True, text=True)
        out = self.assertRefused(r, "secret scan")
        self.assertEqual(self.guard(out, "harness"), "ok", out)
        self.assertNotIn("running origin/main's in its place", out)

    def test_install_hooks_installs_the_launcher(self):
        common = Path(git(WORK, "rev-parse", "--path-format=absolute",
                          "--git-common-dir").strip())
        launcher = common / "stoicheia" / "safe-push"
        self.assertEqual(launcher.read_bytes(), (HERE / "hooks" / "safe-push").read_bytes())
        self.assertIn("stoicheia/safe-push", git(WORK, "config", "--get", "alias.safe-push"))

    def test_harness_variable_checked(self):
        self.good_commit()
        env = clean_env()
        env["STOICHEIA_HARNESS"] = "origin/main"
        r = subprocess.run([sys.executable, str(self.differing_copy()), "--_test-skip-checks",
                            "--branch", BRANCH], cwd=WORK, env=env, capture_output=True,
                           text=True)
        self.assertRefused(r, "STOICHEIA_HARNESS says this is origin/main's harness")

    def test_installed_hook_that_differs_is_noted(self):
        hook = hooks_dir() / "pre-push"
        self.swap_hook(hook.read_text() + "\n# STOICHEIA_SAFE_PUSH, and something else\n")
        self.good_commit()
        out = self.safe_push("--dry-run").stdout
        self.assertEqual(self.guard(out, "pre-push hook"), "note", out)
        self.assertIn("differs from origin/main's scripts/hooks/pre-push", out)


class PrivatePaths(Edge):
    """(5) Scratchpad paths, in a file or a message; private paths and machine-made
    identities in a commit's author or committer."""

    def test_scratchpad_paths_refused(self):
        self.commit("Notes with a scratchpad path", {
            "docs/notes.md": f"Read {SCRATCHPAD} first.\n",
            "docs/project.md": f"The project directory is {FOLDED_HOME}-dev-stoicheia.\n"})
        out = self.assertRefused(self.safe_push(), "secret scan")
        self.assertFlagged(out, "docs/notes.md", "docs/project.md")

    def test_private_identities_refused(self):
        env = dict(os.environ, GIT_AUTHOR_NAME="someone", GIT_AUTHOR_EMAIL="someone@laptop.local",
                   GIT_COMMITTER_NAME="/" + "Users" + "/someone",
                   GIT_COMMITTER_EMAIL="someone@example.invalid")
        sha = self.commit("A commit by a made-up identity", {
            "docs/reading.md": self.text("docs/reading.md") + "\nA line.\n"}, env=env)
        out = self.assertRefused(self.safe_push(), "secret scan")
        self.assertFlagged(out, f"commit {sha[:12]} author", f"commit {sha[:12]} committer")
        self.assertIn("machine-made identity", out)
        self.assertIn("private path in an identity", out)


class HiddenFiles(Edge):
    """(6) A file marked binary or -diff by .gitattributes, or made binary by a NUL, or
    written in UTF-16, is still scanned."""

    def test_gitattributes_cannot_hide_a_file(self):
        self.commit("Hide two files from the diff", {
            ".gitattributes": "docs/hidden.md binary\ndocs/nodiff.md -diff\n",
            "docs/hidden.md": f"api_token = \"{TOKEN}\"\n",
            "docs/nodiff.md": f"see {SCRATCHPAD}\n"})
        # Installed in the clone as well, as a checkout would have it.
        out = self.assertRefused(self.safe_push(), "secret scan")
        self.assertFlagged(out, "docs/hidden.md", "docs/nodiff.md")

    def test_nul_and_utf16_cannot_hide_a_file(self):
        self.commit("Two files that read as binary", {
            "docs/nul.md": b"\0" + f"api_token = \"{TOKEN}\"\n".encode(),
            "docs/wide.md": f"api_token = \"{TOKEN}\"\n".encode("utf-16")})
        out = self.assertRefused(self.safe_push(), "secret scan")
        self.assertFlagged(out, "docs/nul.md", "docs/wide.md")

    def test_utf16_after_8_kb_of_prose_or_binary_junk_refused(self):
        # Review note 4: a NUL anywhere makes a file binary, and UTF-16 text is read
        # wherever it stands, not only at the start.
        prose = ("An ordinary line of prose, of the kind a guide is made of.\n" * 160).encode()
        self.assertGreater(len(prose), 8000)
        wide = f"token = {GH_TOKEN}\n".encode("utf-16-le")
        junk = bytes(range(256)) * 4
        self.commit("Two files with UTF-16 text late in them", {
            "docs/early.md": prose, "docs/late.md": prose + wide,
            "docs/junk.bin": junk + f"api_token = \"{TOKEN}\"\n".encode("utf-16-be")})
        out = self.assertRefused(self.safe_push(), "secret scan")
        self.assertFlagged(out, "docs/late.md", "docs/junk.bin")
        self.assertFalse(self.flagged(out, "docs/early.md"), out)
        self.assertNotIn(GH_TOKEN, out)


class AllowList(Edge):
    """(7) An allow-list entry is narrow: one file, one rule, a long enough match, a reason."""

    def test_broad_entries_refused(self):
        narrow = Secrets.ALLOW
        for broad, problem in ((narrow.replace('"docs/notes.md"', '"docs/*"'), "a glob in path"),
                               (narrow.replace('rule = "key, token or secret"\n', ""),
                                "names no rule"),
                               (narrow.replace('match = "api_token"', 'match = "api"'),
                                "match of at least 8"),
                               (narrow.replace('"docs/notes.md"', '"commit 0123456789ab message"'),
                                "cannot be allowed"),
                               (narrow.replace('"docs/notes.md"', '"the pull request\'s body"'),
                                "cannot be allowed")):
            with self.subTest(problem=problem):
                git(WORK, "checkout", "--quiet", "--force", "--detach", BASE)
                git(ORIGIN, "update-ref", "refs/heads/main", BASE)
                main = self.new_base("A broad entry", {"scripts/safe_push_allow.toml": broad})
                self.commit("A flagged line", {"docs/notes.md": f"api_token = \"{TOKEN}\"\n"})
                r = self.safe_push("--dry-run")
                out = r.stdout + r.stderr
                self.assertEqual(r.returncode, 1, out)
                self.assertIn("broad or incomplete entry", out)
                self.assertIn(problem, out)
                self.assertEqual(self.origin_main(), main)

    def test_an_entry_excuses_its_own_value_alone(self):
        # Review note 5: an entry pins the value it excuses; another token on a line like
        # it, added later, is still refused.
        self.new_base("Allow a fixture", {"scripts/safe_push_allow.toml": Secrets.ALLOW})
        other = base64.b64encode(hashlib.sha256(b"another planted token").digest()).decode()
        self.commit("The allowed line, and another like it", {
            "docs/notes.md": f"api_token = \"{TOKEN}\"\napi_token = \"{other}\"\n"})
        r = self.safe_push("--dry-run")
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        fail = out[out.index("FAIL  secrets:"):out.index("REFUSED")]
        self.assertIn("docs/notes.md:2: key, token or secret", fail)
        self.assertNotIn("docs/notes.md:1:", fail)
        self.assertIn("A fixture for the test", out)       # line 1, allowed

    def test_a_binary_files_entry_is_as_narrow(self):
        # In a binary file a finding's text is a window around the hit, not the whole
        # file: eight bytes from elsewhere in it excuse nothing, and the report prints
        # no more than the window.
        far = b"FARAWAY-WORDS-" * 20
        blob = far + b"\0" + b"x" * 100 + b"\0\x01\x02" + GH_TOKEN.encode() + b"\0\x03" \
            + b"PADDING!" * 20
        allow = ('[[allow]]\npath = "docs/blob.bin"\nmatch = "FARAWAY-WORDS-"\n'
                 'rule = "GitHub token"\n'
                 f'sha256 = "{hashlib.sha256(b"something else").hexdigest()}"\n'
                 'reason = "A fixture for the test."\n')
        self.new_base("Allow a fixture in a binary file", {"scripts/safe_push_allow.toml": allow})
        self.commit("A binary file holding a token", {"docs/blob.bin": blob})
        r = self.safe_push("--dry-run")
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        self.assertTrue(self.flagged(out, "docs/blob.bin"), out)
        self.assertNotIn("FARAWAY", out)
        self.assertNotIn(GH_TOKEN, out)

    def test_the_committed_allow_list_is_narrow(self):
        text = (SOURCE / "scripts" / "safe_push_allow.toml").read_text()
        import tomllib
        for entry in tomllib.loads(text).get("allow", []):
            self.assertFalse(set("*?[") & set(entry["path"]), entry)
            self.assertIn(entry["rule"].removeprefix("base64-encoded "), safe_push.KNOWN_RULES)
            self.assertGreaterEqual(len(entry["match"]), 8, entry)
            self.assertTrue(entry["reason"].strip(), entry)


@unittest.skipUnless(os.environ.get("STOICHEIA_SLOW_TESTS") == "1",
                     "the full checks need Lean and take minutes: STOICHEIA_SLOW_TESTS=1")
class FullChecks(Edge):
    """Step 4 for real: the whole sequence once, on a good commit, without the internal
    flag, as a dry run of the pre-flight (the real gh is never called by the tests)."""

    def step(self, out: str, name: str) -> str | None:
        """A step's outcome, whether or not its line carries a detail after a colon."""
        m = re.search(r"^\s+(ok|FAIL|skip)\s+%s(:|\s+\(|$)" % re.escape(name), out, re.M)
        return m.group(1) if m else None

    def test_full_sequence_on_a_good_commit(self):
        self.good_commit()
        r = subprocess.run([sys.executable, str(SAFE_PUSH), "--branch", BRANCH, "--dry-run"],
                           cwd=WORK, env=clean_env(), capture_output=True, text=True)
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, out)
        for name, _ in safe_push.CHECKS + safe_push.NEGATIVE:
            self.assertEqual(self.step(out, name), "ok", f"{name}:\n{out}")
        self.assertEqual(self.step(out, "git push"), "skip", out)
        self.assertEqual(self.origin_main(), BASE)
        self.assertEqual(len(git(WORK, "worktree", "list").splitlines()), 1,
                         "a temporary worktree was left behind")


class Units(unittest.TestCase):
    """The scanner and the helpers, without git."""

    def flagged(self, line: str) -> list[str]:
        return [f.rule for f in safe_push.scan_text("x", 1, line)]

    def test_secrets_flagged(self):
        hexkey = hashlib.sha256(b"x").hexdigest()
        for line in (f"api_token = \"{TOKEN}\"", f'"client_secret": "{TOKEN}"',
                     f"export GITHUB_TOKEN={hexkey}", KEY_HEADER,
                     "gh" + "p_" + "a1B2" * 9, "sk" + "-" + "proj" + "Ab3dE" * 5,
                     "xo" + "xb-" + "1234-5678-abcdef", "AK" + "IA" + "ABCDEFGH23456789",
                     "Authori" + "zation: Bearer abcdefgh12345678", f"see {PRIVATE_DIR}",
                     "C:" + "\\" + "Users" + "\\someone", "secret" + "s2026/thing",
                     f"cd {SCRATCHPAD}", f"projects/{FOLDED_HOME}/memory",
                     "/tmp/" + "claude" + "-1000/x"):
            self.assertTrue(self.flagged(line), line)

    def test_ordinary_lines_pass(self):
        for line in ('lean = "sha256:061379c1f0411141"', "    key = prop_key(ref)",
                     "the key step is I.5, which Heath does not bracket",
                     "token: docs/reports/crew/voice-02.md",
                     "Authori" + "zation: Bearer ${{ secrets.GITHUB_TOKEN }}",
                     "obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B (ne_of_between_ends hADB)",
                     "the secret of the construction lies in Postulate 3",
                     "the non-Users-facing part", "a /tmp/build directory"):
            self.assertEqual(self.flagged(line), [], line)
        lean = (SOURCE / "Elements" / "BookIII" / "Prop16.lean").read_text()
        self.assertEqual([f for i, l in enumerate(lean.splitlines())
                          for f in safe_push.scan_text("Prop16.lean", i, l)], [])

    def test_across_lines_encoded_and_linked(self):
        def across(*lines):
            return [f.rule for f in safe_push.scan_block("x", list(enumerate(lines, 1)))]
        self.assertTrue(across("api_token =", f'    "{TOKEN}"'))
        self.assertTrue(across(f'key = "{HEXKEY[:16]}"', f'      "{HEXKEY[16:]}"'))
        self.assertEqual(across(f"api_token = \"{TOKEN}\"", "the next line"),
                         ["key, token or secret"], "flagged once, not again across lines")
        encoded = base64.b64encode(GH_TOKEN.encode()).decode()
        self.assertEqual([f.rule for f in safe_push.scan_text("x", 1, f"v: {encoded}")],
                         ["base64-encoded GitHub token"])
        for target, out in (("../README.md", False), ("sub/file", False), ("/etc/hosts", True),
                            (TILDE_DOWNLOADS, True), ("../../up", True), ("C:\\x", True)):
            self.assertEqual(bool(safe_push.scan_link("docs/link", target)), out, target)

    def test_ordinary_files_pass_read_across_lines(self):
        # Whole files of the repository, every line as if added: nothing is flagged,
        # this harness, its tests, its hook and the template included; and the images,
        # read as binaries.
        for path in ("Elements/BookIII/Prop16.lean", "docs/WORKFLOW.md", "facts.json",
                     "docs/briefs/0002-decisions.md", "review/III/16.toml",
                     "scripts/safe_push.py", "scripts/test_safe_push.py",
                     "scripts/hooks/pre-push", "figures/I/01-idea.svg", "AGENTS.md",
                     "docs/FORMALIZATION.md", "docs/PROGRAM.md",
                     ".github/pull_request_template.md"):
            numbered = list(enumerate((SOURCE / path).read_text().splitlines(), 1))
            self.assertEqual([f.shown() for f in safe_push.scan_block(path, numbered)], [],
                             path)
        for path in sorted((SOURCE / "assets").glob("*.png")):
            self.assertEqual([f.shown() for f in safe_push.scan_binary(path.name,
                                                                        path.read_bytes())],
                             [], path)

    def test_allow_list_pins_the_value(self):
        (f,) = safe_push.scan_text("docs/x.md", 3, f"example_token: {HEXKEY}")
        other = hashlib.sha256(b"another").hexdigest()
        (g,) = safe_push.scan_text("docs/x.md", 4, f"example_token: {other}")

        def entry(match, digest=None):
            return [safe_push.Allow("docs/x.md", match, "key, token or secret", "A fixture.",
                                    digest)]
        self.assertIsNone(safe_push.allowed(f, entry("example_token:")))
        self.assertTrue(safe_push.allowed(f, entry(f"example_token: {HEXKEY}")))
        self.assertIsNone(safe_push.allowed(g, entry(f"example_token: {HEXKEY}")))
        pinned = entry("example_token:", hashlib.sha256(HEXKEY.encode()).hexdigest())
        self.assertTrue(safe_push.allowed(f, pinned))
        self.assertIsNone(safe_push.allowed(g, pinned))
        # A commit message is never allowed, whatever the entry says.
        message = f._replace(path="commit 0123456789ab message")
        self.assertIsNone(safe_push.allowed(message, [safe_push.Allow(
            message.path, f"example_token: {HEXKEY}", "key, token or secret", "x", None)]))

    def test_binary_findings_carry_a_window(self):
        data = b"A" * 500 + b"\0" + GH_TOKEN.encode() + b"\0" + b"B" * 500
        found = [f for f in safe_push.scan_binary("x.bin", data) if f.rule == "GitHub token"]
        self.assertTrue(found)
        for f in found:
            self.assertLessEqual(len(f.text), len(GH_TOKEN) + 2 * safe_push.WINDOW)
            self.assertEqual(safe_push.flagged_value(f), GH_TOKEN)
            self.assertNotIn(GH_TOKEN, f.shown())

    def test_secret_files(self):
        for path in (".env", "deploy/.env.local", "keys/server.key", "a/b.pem", "id_ed25519"):
            self.assertTrue(safe_push.scan_path(path), path)
        for path in ("docs/env.md", "scripts/check_style.py", "Certificate/axioms.lock"):
            self.assertEqual(safe_push.scan_path(path), [], path)

    def test_names_ref(self):
        names = safe_push.names_ref
        self.assertTrue(names("III.16 keeps its statement", "III.16"))
        self.assertTrue(names("Heath's III. 16", "III.16"))
        self.assertTrue(names("`BookIII.Prop16` changes", "III.16 Por."))
        self.assertFalse(names("III.16 changes", "III.1"))
        self.assertFalse(names("III.1 changes", "I.1"))
        self.assertFalse(names("BookIII.Prop10 changes", "III.1"))

    def test_source_statement(self):
        src = (SOURCE / "Elements" / "BookIII" / "Prop01.lean").read_text()
        main = safe_push.source_statement(src, 1, None)
        porism = safe_push.source_statement(src, 1, "porism")
        self.assertTrue(main.startswith("{A B : Point} {ABC : Circle}"), main)
        self.assertTrue(porism.startswith("{A B C D G : Point}"), porism)
        self.assertNotIn(":=", main + porism)

    def test_revert_advice_and_slug(self):
        ctx = safe_push.Context(Path("."), "a" * 40, "b" * 40, 3, "", None, {})
        advice = safe_push.revert_advice(ctx)
        self.assertIn(f"git revert --no-edit -m 1 {'a' * 40}", advice)
        self.assertIn("git safe-push --branch", advice)
        self.assertEqual(safe_push.github_slug("https://github.com/jackChallis/stoicheia.git"),
                         "jackChallis/stoicheia")
        self.assertEqual(safe_push.github_slug("git@github.com:jackChallis/stoicheia.git"),
                         "jackChallis/stoicheia")
        self.assertFalse(safe_push.is_local("https://github.com/jackChallis/stoicheia.git"))

    def test_identities(self):
        flagged = safe_push.scan_identity
        self.assertTrue(flagged("a", "Some One <someone@Some-MacBook.local>"))
        self.assertTrue(flagged("a", "someone <someone@(none)>"))
        self.assertTrue(flagged("a", "/" + "Users" + "/someone <a@example.org>"))
        self.assertEqual(flagged("a", "Jack Challis <jack@example.org>"), [])
        self.assertEqual(flagged("a", "GitHub <noreply@github.com>"), [])

    def test_checklist(self):
        template = ("- [ ] **Required:** One.\n- [ ] **Required if protected:** Two.\n"
                    "- [ ] Optional.\n")
        problems = safe_push.checklist_problems
        self.assertEqual(problems(template.replace("[ ] **Required:**", "[x] **Required:**"),
                                  template, False), [])
        self.assertEqual(problems(template, template, False), ["unticked: Required: One."])
        self.assertEqual(len(problems(template, template, True)), 2)
        self.assertEqual(problems("- [x] **Required:** One.\n", template, True),
                         ["missing from the body: Required if protected: Two."])
        self.assertTrue(problems("No checklist at all.", None, False))

    def test_judge_checks(self):
        judge = safe_push.judge_checks
        self.assertEqual(judge(PASSING)[0], "success")
        self.assertEqual(judge(PASSING[:2])[0], "missing")
        self.assertEqual(judge(PASSING + [{"name": "check", "bucket": "fail"}])[0], "failure")
        self.assertEqual(judge(PASSING + [{"name": "other", "bucket": "pending"}])[0], "pending")


if __name__ == "__main__":
    unittest.main(verbosity=2)
