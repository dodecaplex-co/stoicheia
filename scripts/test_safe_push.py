#!/usr/bin/env python3
"""Tests for scripts/safe_push.py, on a throwaway clone with a bare origin.

    python3 scripts/test_safe_push.py        # two minutes or so; no Lean, no network
    STOICHEIA_SLOW_TESTS=1 python3 scripts/test_safe_push.py FullChecks   # Lean, minutes

The clone is made with `git clone --local` of this repository into a temporary
directory: a bare `origin.git`, whose main is set to this checkout's HEAD, and a working
clone of it. Each test plants one commit and runs safe_push.py against that origin:

- each guard refuses its bad commit: a secret, a statement changed without a decision,
  the axiom lock changed without one, a commit that is not a fast-forward, a change to
  heath/ with no leaf named, and a whole directory deleted;
- a good commit passes, by a dry run and then a push, from a dirty working tree;
- the pre-push hook refuses any push to main that safe_push did not check;
- and the edge cases, each refused: (1) a credential split over two lines; (2) one
  base64-encoded; (3) a key file added under a name later renamed, a secret taken out
  again within the push, and files renamed to .pem, .key and .env names; (4) symlinks
  into private directories or out of the repository; (5) a statement changed on a
  re-wrapped line, a decision naming another proposition, an old brief line edited in
  place, and a statement's text after a binder's `:=`; (6) the axiom lock changed with a
  decision silent on it, a mention outside the decisions page, or an old line edited;
  (7) stale or hand-edited generated pages; (8) a commit behind origin/main or with an
  unrelated history, and origin/main moving during the checks or at the push; (9) the
  hook given HEAD:main, main, refs/heads/main, --mirror, a forced refspec (even of the
  commit checked) and tags; (10) a dry run, which never pushes and leaves no worktree or
  temporary file, on success, on a refusal or when interrupted.

The long checks of step 4 (the build and the rest) are skipped by the internal flag
`--_test-skip-checks`, used here and nowhere else; safe_push honours it only against a
local origin. The checks the guards run themselves (check_fidelity.py and render.py on
the commit as committed) still run. The opt-in FullChecks test runs step 4 for real,
once, on a good commit, and pushes it to the throwaway origin. Python 3.11 or later;
standard library and git.
"""

from __future__ import annotations

import base64
import hashlib
import json
import os
import re
import shutil
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


def git(cwd, *args, env=None, check=True) -> str:
    r = subprocess.run(["git", *args], cwd=cwd, env=env, capture_output=True, text=True)
    if check and r.returncode != 0:
        raise AssertionError(f"git {' '.join(args)} failed in {cwd}:\n{r.stdout}{r.stderr}")
    return r.stdout


def clean_env() -> dict:
    env = dict(os.environ, STOICHEIA_PUSH_LOG=str(LOG))
    env.pop("STOICHEIA_SAFE_PUSH", None)
    return env


# Planted secrets are built when the tests run, so that this file passes the scan itself.
TOKEN = base64.b64encode(hashlib.sha256(b"a planted token").digest()).decode()
PRIVATE_DIR = "/" + "Users" + "/someone/" + "Down" + "loads/notes.txt"
KEY_HEADER = "-----BEGIN " + "RSA PRIVATE" + " KEY-----"
GH_TOKEN = "gh" + "p_" + hashlib.sha256(b"a planted GitHub token").hexdigest()[:36]
HEXKEY = hashlib.sha256(b"a planted hex key").hexdigest()
TILDE_DOWNLOADS = "~/" + "Down" + "loads"
PRIVATE_SCANS = "../../" + "secret" + "s2026/scans"


def setUpModule():
    global TMP, ORIGIN, WORK, LOG, BASE
    TMP = Path(tempfile.mkdtemp(prefix="stoicheia-safe-push-test-"))
    ORIGIN, WORK, LOG = TMP / "origin.git", TMP / "work", TMP / "cache" / "pushes.log"
    common = git(SOURCE, "rev-parse", "--path-format=absolute", "--git-common-dir").strip()
    BASE = git(SOURCE, "rev-parse", "HEAD").strip()
    git(TMP, "clone", "--quiet", "--bare", "--local", common, str(ORIGIN))
    git(ORIGIN, "update-ref", "refs/heads/main", BASE)
    git(ORIGIN, "symbolic-ref", "HEAD", "refs/heads/main")
    git(TMP, "clone", "--quiet", "--local", str(ORIGIN), str(WORK))
    git(WORK, "config", "user.name", "safe_push test")
    git(WORK, "config", "user.email", "safe-push-test@example.invalid")
    git(WORK, "config", "commit.gpgsign", "false")
    r = subprocess.run(["sh", str(INSTALL_HOOKS)], cwd=WORK, capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr


def tearDownModule():
    shutil.rmtree(TMP, ignore_errors=True)


class Clone(unittest.TestCase):
    """Each test starts from origin/main at BASE and a clean clone."""

    def setUp(self):
        git(ORIGIN, "update-ref", "refs/heads/main", BASE)
        git(WORK, "checkout", "--quiet", "--force", "--detach", BASE)
        git(WORK, "clean", "-fdq")

    def text(self, path: str) -> str:
        return (WORK / path).read_text()

    def replaced(self, path: str, old: str, new: str) -> str:
        text = self.text(path)
        self.assertEqual(text.count(old), 1, f"{path}: expected one {old!r}")
        return text.replace(old, new)

    def commit(self, message: str, write: dict | None = None, remove=()) -> str:
        for path, text in (write or {}).items():
            (WORK / path).parent.mkdir(parents=True, exist_ok=True)
            (WORK / path).write_text(text)
            git(WORK, "add", "--", path)
        for path in remove:
            git(WORK, "rm", "-r", "-q", "--", path)
        git(WORK, "commit", "-q", "-m", message)
        return git(WORK, "rev-parse", "HEAD").strip()

    def safe_push(self, *args, env=None) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, str(SAFE_PUSH), "--_test-skip-checks", *args],
                              cwd=WORK, env=env or clean_env(), capture_output=True, text=True)

    def origin_main(self) -> str:
        return git(ORIGIN, "rev-parse", "refs/heads/main").strip()

    def guard(self, out: str, name: str) -> str | None:
        """The outcome a step's line reports: "ok", "FAIL", or None if absent."""
        m = re.search(r"^\s+(ok|FAIL)\s+%s:" % re.escape(name), out, re.M)
        return m.group(1) if m else None

    def assertRefused(self, r, *wanted):
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        self.assertIn("REFUSED", out)
        for w in wanted:
            self.assertIn(w, out)
        self.assertEqual(self.origin_main(), BASE, "a refused push moved origin/main")
        return out

    def decision(self, line: str) -> dict:
        path = "docs/briefs/0002-decisions.md"
        return {path: self.text(path) + f"\n- **A decision for the test.** {line}\n"}


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
        for name in ("commit", "fast-forward", "secrets", "statements", "axiom lock", "heath/",
                     "directories", "review records"):
            self.assertEqual(self.guard(out, name), "ok", f"{name}:\n{out}")
        self.assertIn("leaf n261", out)

        r = self.safe_push()                       # HEAD, by default
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, out)
        self.assertEqual(self.origin_main(), sha)
        self.assertEqual(self.guard(out, "git push"), "ok", out)
        self.assertEqual(self.guard(out, "tags"), "ok", out)
        self.assertEqual(git(ORIGIN, "tag", "--list"), tags, "a tag was made")
        self.assertNotIn("Uncommitted", git(ORIGIN, "show", f"{sha}:README.md"))
        self.assertEqual(len(git(WORK, "worktree", "list").splitlines()), 1,
                         "a temporary worktree was left behind")
        log = LOG.read_text()
        self.assertIn(f"dry run {sha[:12]}", log)
        self.assertIn(f"push {sha[:12]}", log)

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

    def test_allow_list_with_a_reason(self):
        allow = ('[[allow]]\npath = "docs/notes.md"\nmatch = "api_token"\n'
                 'reason = "A fixture for the test, not a real token."\n')
        self.commit("A flagged line, allowed", {
            "docs/notes.md": f"api_token = \"{TOKEN}\"\n",
            "scripts/safe_push_allow.toml": allow})
        r = self.safe_push("--dry-run")
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, out)
        self.assertEqual(self.guard(out, "secrets"), "ok", out)
        self.assertIn("A fixture for the test", out)

    def test_allow_list_without_a_reason_refused(self):
        allow = '[[allow]]\npath = "docs/notes.md"\nmatch = "api_token"\n'
        self.commit("A flagged line, allowed without a reason", {
            "docs/notes.md": f"api_token = \"{TOKEN}\"\n",
            "scripts/safe_push_allow.toml": allow})
        self.assertRefused(self.safe_push(), "has no reason")


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
        sha = self.commit("A commit", {"docs/reading.md": self.text("docs/reading.md") + "\nX.\n"})
        r = self.push(f"{sha}:refs/heads/main")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("safe_push.py", r.stderr)
        r = self.push(f"{sha}:refs/heads/main", STOICHEIA_SAFE_PUSH=BASE)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("safe_push.py checked", r.stderr)
        r = self.push(":refs/heads/main", STOICHEIA_SAFE_PUSH=sha)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("refusing to delete main", r.stderr)
        self.assertEqual(self.origin_main(), BASE)
        r = self.push(f"{sha}:refs/heads/a-branch")
        self.assertEqual(r.returncode, 0, r.stderr)
        r = self.push(f"{sha}:refs/heads/main", STOICHEIA_SAFE_PUSH=sha)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(self.origin_main(), sha)


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
        self.addCleanup(lambda: git(ORIGIN, "update-ref", "-d", "refs/heads/side"))
        git(WORK, "checkout", "--quiet", "--detach", BASE)
        return side

    def good_commit(self) -> str:
        return self.commit("A good commit", {
            "docs/reading.md": self.text("docs/reading.md") + "\nA line for the test.\n"})


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
    DECISIONS = "docs/briefs/0002-decisions.md"

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


# Runs safe_push in a subprocess with `guards` (or the step named) wrapped, so that
# something happens at a chosen moment: origin's main moves, or an interruption.
DRIVER = r"""
import subprocess, sys
sys.path.insert(0, sys.argv[1])
import safe_push
action, origin, target = sys.argv[2], sys.argv[3], sys.argv[4]
real = safe_push.guards
def guards(*args, **kwargs):
    real(*args, **kwargs)
    if action == "move":
        subprocess.run(["git", "update-ref", "refs/heads/main", target], cwd=origin, check=True)
    elif action == "interrupt":
        raise KeyboardInterrupt("a test interruption")
safe_push.guards = guards
sys.exit(safe_push.main(sys.argv[5:]))
"""


class Ancestry(Edge):
    """(8) A commit that is not a descendant of origin/main; origin/main moving between
    the check and the push."""

    def drive(self, action: str, target: str, *args, env=None) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, "-c", DRIVER, str(HERE), action, str(ORIGIN),
                               target, "--_test-skip-checks", *args], cwd=WORK,
                              env=env or clean_env(), capture_output=True, text=True)

    def test_commit_behind_origin_main_refused(self):
        newer = self.good_commit()
        git(WORK, "push", "--quiet", "origin", f"{newer}:refs/heads/side")
        self.addCleanup(lambda: git(ORIGIN, "update-ref", "-d", "refs/heads/side"))
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

    def test_origin_main_moves_at_the_push_refused(self):
        # Between safe_push's last look at origin and the push itself: the hook runs
        # inside `git push`, after git has read origin's refs.
        side = self.side_commit()
        mine = self.good_commit()
        real = TMP / "real-pre-push"
        shutil.copy(HERE / "hooks" / "pre-push", real)
        self.swap_hook(f'#!/bin/sh\ngit -C "{ORIGIN}" update-ref refs/heads/main {side}\n'
                       f'exec sh "{real}" "$@"\n')
        r = self.safe_push()
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        self.assertIn("git push failed", out)
        self.assertEqual(self.origin_main(), side, "the push went ahead over the new main")
        self.assertNotEqual(self.origin_main(), mine)


class HookRefspecs(Edge):
    """(9) The pre-push hook, without STOICHEIA_SAFE_PUSH: every spelling of a push to
    main, a forced one, and a tag."""

    def push(self, *args, **env) -> subprocess.CompletedProcess:
        e = clean_env()
        e.pop("STOICHEIA_TAG_PUSH", None)
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
        self.assertIn("not a fast-forward", r.stderr)
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


class DryRun(Edge):
    """(10) --dry-run never pushes, and leaves no worktree, on success or failure."""

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


@unittest.skipUnless(os.environ.get("STOICHEIA_SLOW_TESTS") == "1",
                     "the full checks need Lean and take minutes: STOICHEIA_SLOW_TESTS=1")
class FullChecks(Edge):
    """Step 4 for real: the whole sequence once, on a good commit, without the internal
    flag, then the push to the throwaway origin."""

    def step(self, out: str, name: str) -> str | None:
        """A step's outcome, whether or not its line carries a detail after a colon."""
        m = re.search(r"^\s+(ok|FAIL|skip)\s+%s(:|\s+\(|$)" % re.escape(name), out, re.M)
        return m.group(1) if m else None

    def test_full_sequence_on_a_good_commit(self):
        sha = self.good_commit()
        r = subprocess.run([sys.executable, str(SAFE_PUSH)], cwd=WORK, env=clean_env(),
                           capture_output=True, text=True)
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, out)
        for name, _ in safe_push.CHECKS + safe_push.NEGATIVE:
            self.assertEqual(self.step(out, name), "ok", f"{name}:\n{out}")
        self.assertEqual(self.step(out, "git push"), "ok", out)
        self.assertEqual(self.origin_main(), sha)
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
                     "C:" + "\\" + "Users" + "\\someone", "secret" + "s2026/thing"):
            self.assertTrue(self.flagged(line), line)

    def test_ordinary_lines_pass(self):
        for line in ('lean = "sha256:061379c1f0411141"', "    key = prop_key(ref)",
                     "the key step is I.5, which Heath does not bracket",
                     "token: docs/reports/crew/voice-02.md",
                     "Authori" + "zation: Bearer ${{ secrets.GITHUB_TOKEN }}",
                     "obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B (ne_of_between_ends hADB)",
                     "the secret of the construction lies in Postulate 3"):
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
        # this harness and its tests included.
        for path in ("Elements/BookIII/Prop16.lean", "docs/WORKFLOW.md", "facts.json",
                     "docs/briefs/0002-decisions.md", "review/III/16.toml",
                     "scripts/safe_push.py", "scripts/test_safe_push.py",
                     "scripts/hooks/pre-push", "figures/I/01-idea.svg"):
            numbered = list(enumerate((SOURCE / path).read_text().splitlines(), 1))
            self.assertEqual([f.shown() for f in safe_push.scan_block(path, numbered)], [],
                             path)

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
        self.assertIn(f"git revert --no-edit {'a' * 40}", advice)
        self.assertIn("python3 scripts/safe_push.py", advice)
        self.assertEqual(safe_push.github_slug("https://github.com/jackChallis/stoicheia.git"),
                         "jackChallis/stoicheia")
        self.assertEqual(safe_push.github_slug("git@github.com:jackChallis/stoicheia.git"),
                         "jackChallis/stoicheia")
        self.assertFalse(safe_push.is_local("https://github.com/jackChallis/stoicheia.git"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
