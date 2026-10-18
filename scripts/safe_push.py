#!/usr/bin/env python3
"""The pre-flight of a pull request, and its merge: the way work reaches main.

    git safe-push --branch <name> --label <kind> [--label L]... [--title T]
                  [--body-file F] [--ready] [--commit <sha>] [--dry-run]
    git safe-push --merge <pr-number> [--dry-run]
    git safe-push --dry-run [--commit <sha>]                      # the checks alone

`git safe-push` is the launcher scripts/install_hooks.sh installs outside the tracked
tree (scripts/hooks/safe-push): it runs origin/main's copy of this file, whatever the
checkout holds. `python3 scripts/safe_push.py ...` runs the checkout's copy, which hands
over to origin/main's when it differs; that holds only while the copy run is one that
hands over, so the launcher is the way in.

Nothing is pushed to main: main changes only by a pull request's merge commit
(docs/WORKFLOW.md, "Landing work: pull requests"). Run with none of --branch, --merge
and --dry-run, the script refuses, and says to use --branch.

The pre-flight (--branch) checks one commit (HEAD unless --commit names another) from end
to end, reading nothing from the working tree, and only then pushes it to
refs/heads/<name> and opens the pull request, or updates the open one. The steps run in
order, and the first that fails stops it with a message saying why:

1. Preconditions. The commit exists; `git fetch origin`; origin/main is an ancestor of
   the commit, so that the merge commit will hold exactly the tree checked; the branch,
   if origin has it, is an ancestor too, for nothing is ever forced; the branch is not
   main; the branch name and the title hold nothing the scan refuses. The harness is
   origin/main's: when this copy of safe_push.py or heath.py differs from origin/main's,
   origin/main's replaces this process (os.execve), so that a branch cannot weaken the
   guards that judge it, and an interruption reaches the copy that pushed.
2. A secret scan of every line the push adds, of every file it adds or changes, of its
   commit messages, and of each commit's author and committer, and then of each commit's
   own change, since the push publishes the history: a secret added and taken out again,
   or a key file added and then renamed, is found in the commit that brings it. It looks
   for private keys, API-key-like tokens, Authorization headers with values, `.env` and
   key files, the owner's private paths (an agent's scratchpad among them) and
   machine-made identities: in each line, across consecutive lines, inside base64 that
   decodes to text, and in symlinks, which may not point out of the repository. Whether
   a file is text or binary is read from its bytes (a NUL anywhere makes it binary, and
   a binary file is read whole: its printable runs and its UTF-16 runs, wherever they
   stand), and the diff is read as text, so a .gitattributes line cannot take a file out
   of the scan. A false positive goes in origin/main's `scripts/safe_push_allow.toml`:
   one file, one rule, a part of the line, and the flagged value itself, pinned by its
   SHA-256, to an entry, with its reason. A commit's message or identity cannot be
   allowed, and an entry added by the push itself does not count.
3. Invariant guards against origin/main, in a fresh temporary worktree of the commit:
   - every statement (facts.json's `statement`, and the Lean source of `theorem PropN`,
     its porism and its companions, up to its own `:=`, whitespace aside) is unchanged,
     unless the push adds a new line to `docs/briefs/` naming it;
   - `Certificate/axioms.lock` is unchanged, unless 0002-decisions.md gains a new line
     mentioning the lock;
   - a protected path (PROTECTED, below, as docs/WORKFLOW.md lists them) changes only
     with a new line in 0002-decisions.md naming each file changed, and the pull request
     then carries the label `security-review`;
   - every changed file under `heath/` carries, in the change, a comment naming a scan
     leaf of its own pages, as origin/main's copy of the file lists them;
   - no review record is stale, and the generated pages are current (check_fidelity.py
     and render.py, on the commit as committed);
   - no whole directory under Elements/, heath/, review/, figures/ or mishnah/ is
     deleted unless 0002-decisions.md gains a new line naming it.
4. The full check sequence of docs/WORKFLOW.md, section 8, in that worktree, and
   `negative_tests.py` in a second one, each step timed. The checks run with
   origin/main's copies of the check scripts and their expected values (CHECK_INPUTS,
   below); when the commit changes any of those, they run again with the commit's own
   copies, which must pass. A check that fails with origin/main's copies is noted for the
   security review, and refuses the commit when it also changes what the checks judge
   (anything but the checks, the protected paths, the decisions page and the generated
   pages): a check change lands in a pull request of its own, before the code it checks.
   Step 3's two checks run the same way.
5. The pull request settled first: our open one for the branch (a fork's of the same
   name is never touched), or a new one; its body, --body-file or generated from
   .github/pull_request_template.md (the commits, the statements, the review records
   touched, the protected paths, and the pre-flight's summary between its markers; on an
   update without --body-file, only that summary is replaced), scanned. Then
   `git push origin <sha>:refs/heads/<name>`, never forced; then `gh pr create --base
   main --head <name>`, a draft unless --ready, or `gh pr edit` of the open one; it needs
   a label for its kind (tooling, text, lean or docs), given or already on it; then its
   CI, followed to its conclusion (`gh pr checks --watch`).
6. A summary, printed and appended to `~/.cache/stoicheia/pushes.log`, outside the
   repository (`STOICHEIA_PUSH_LOG` names another file); each step's output is kept
   beside it in `logs/`, and the pre-flight's record in `preflight/`, for --merge.

--merge <n> merges a pull request only when its head passes the secret scan and the
guards against the current origin/main, run again then (a record of the pre-flight is a
local file, so it stands in for the full checks alone, and only when origin/main's
harness made it; else they run again too), CI on that head is green (`gh pr checks`:
check, model and negative pass, nothing fails or waits), no required box of its
checklist is unticked (the template's own required boxes included, so deleting one does
not help), the coordinator has written its "What and why", its reviews (each with its
commit and its findings) and its "Needs the owner's OK", it carries a label for its kind
and `security-review` when a protected path changes, and it is not a draft; the
pre-flight's notes are shown beside the checklist. Then `gh pr merge <n>
--merge --delete-branch --match-head-commit <head>`: a merge commit, never a squash or a
rebase, since review records stamp the branch's commits. Afterwards main is checked to
hold the tree checked.

`--dry-run` does everything but the push, the pull request and the merge. The temporary
worktrees are removed at the end, on a failure too. The pre-push hook,
`scripts/hooks/pre-push` (installed by `scripts/install_hooks.sh`), runs origin/main's
secret scan (`--scan-push`) on a push to any branch, refuses every push to main, and
refuses a tag unless STOICHEIA_TAG_PUSH names it, which the owner's OK alone sets, and
scans the tag then.

Exit status: 0 when done (a pull request opened or updated with CI green, a merge, a dry
run passed, or nothing to do); 1 when refused before any push or merge; 2 for a usage
error; 3 when pushed but CI failed or was not followed, or merged but main is not the
tree checked. Standard library, git and gh; Python 3.11 or later.
"""

from __future__ import annotations

import argparse
import base64
import binascii
import contextlib
import datetime
import hashlib
import json
import math
import os
import posixpath
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import NamedTuple

sys.path.insert(0, str(Path(__file__).resolve().parent))
import heath  # noqa: E402  (the contracts: parse_ref, prop_key, theorem_span)

# origin/main's harness runs in place of a branch's copy when this marker is in it.
HARNESS_PROTOCOL = 2

PY = sys.executable
DECISIONS = "docs/briefs/0002-decisions.md"
BRIEFS = "docs/briefs/"
LOCK = "Certificate/axioms.lock"
ALLOWLIST = "scripts/safe_push_allow.toml"
TEMPLATE = ".github/pull_request_template.md"
GUARDED_DIRS = ("Elements", "heath", "review", "figures", "mishnah")
# A change to any of these needs a decisions entry naming the file, and the label below.
# docs/WORKFLOW.md's "Protected paths" names each of them (test_safe_push checks it).
# lakefile.lean is here although the repository has none: Lake reads it in preference to
# lakefile.toml, and runs it. .gitignore is here because an added rule hides untracked
# files from `git status`, and so from the check that the generated pages are current.
PROTECTED = ("scripts/", ".github/", "Certificate/", "tests/", "review/SCHEMA.md",
             "review/terms.toml", ".gitattributes", ".gitignore", "lakefile.toml",
             "lakefile.lean", "lean-toolchain", "lake-manifest.json")
# The checks and what they expect: origin/main's copies judge the commit (step 4).
CHECK_INPUTS = ("scripts/", "tests/", "Certificate/", "review/SCHEMA.md", "review/terms.toml")
SECURITY_LABEL = "security-review"
LABELS = {
    **{f"stage-{n}": f"Brief 0005, stage {n}" for n in range(2, 7)},
    "tooling": "Scripts, CI and the harness",
    "text": "Heath's text, commentary and the reader's pages",
    "lean": "Proofs and statements",
    "docs": "Guides, briefs and reports",
    SECURITY_LABEL: "Changes a protected path: needs /security-review before merge",
}
KIND_LABELS = ("tooling", "text", "lean", "docs")      # every pull request carries one
REQUIRED_CHECKS = ("check", "model", "negative")
GENERATED = ("facts.json", "book/", "CERTIFICATE.md", "GRAPH.md", "README.md", "docs/PROGRAM.md")
# Of these, two are generated only between their markers (render.py's SCOPE_MARKERS and
# STATUS_MARKERS); the rest of each is written by hand.
GENERATED_REGIONS = {
    "README.md": re.compile(r"<!-- scope:([IVX]+) -->.*?<!-- /scope:\1 -->", re.S),
    "docs/PROGRAM.md": re.compile(r"<!-- status -->\n.*?<!-- /status -->", re.S),
}
CI_APPEAR_TIMEOUT = 300   # seconds to wait for the checks to appear after the push
CI_POLL = 10              # seconds between looks for them
CI_WATCH_INTERVAL = "30"  # seconds between `gh pr checks --watch` refreshes
HEAD_TIMEOUT = 60         # seconds to wait for GitHub to see the branch's new head
TAIL = 40                 # lines of a failed step's output to print

# The full local check sequence, exactly as docs/WORKFLOW.md, section 8, and CI's `check`
# job run it, then the `model` job. Change it with them.
CHECKS = [
    ("lake build", ["lake", "build"]),
    ("lake build Audit", ["lake", "build", "Audit"]),
    ("lake env lean Certificate/Facts.lean", ["lake", "env", "lean", "Certificate/Facts.lean"]),
    ("python3 scripts/heath.py", [PY, "scripts/heath.py"]),
    ("python3 scripts/check_fidelity.py", [PY, "scripts/check_fidelity.py"]),
    ("python3 scripts/check_style.py", [PY, "scripts/check_style.py"]),
    ("python3 scripts/render.py", [PY, "scripts/render.py"]),
    ("git status --porcelain is empty", None),
    ("python3 scripts/check_links.py", [PY, "scripts/check_links.py"]),
    ("python3 -I tests/model/run.py --fast", [PY, "-I", "tests/model/run.py", "--fast"]),
]
# CI's `negative` job, in a second disposable worktree: negative_tests.py plants breaks
# in the tree it runs in.
NEGATIVE = [
    ("negative: lake build", ["lake", "build"]),
    ("negative: lake env lean Certificate/Facts.lean",
     ["lake", "env", "lean", "Certificate/Facts.lean"]),
    ("negative: python3 scripts/negative_tests.py", [PY, "scripts/negative_tests.py"]),
]

ARGV: list[str] = []      # this run's arguments, for origin/main's harness to run with
HARNESS = "this copy of `scripts/safe_push.py`"   # which harness ran, for the record
HARNESS_BLOB: str | None = None     # its blob, when it is origin/main's


class Refusal(Exception):
    """A step failed: nothing is pushed or merged (or, after it, nothing more is done)."""


class NothingToPush(Exception):
    """origin/main is already the commit."""


# --------------------------------------------------------------------------------------
# Running commands


def run(cmd, cwd, *, env=None, input=None, binary=False) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, env=env, input=input, capture_output=True,
                          text=not binary)


def git(repo, *args, check=True, binary=False) -> str | bytes:
    """git's stdout, run in `repo` with paths printed as they are."""
    r = run(["git", "-c", "core.quotePath=false", *args], repo, binary=binary)
    if check and r.returncode != 0:
        err = r.stderr.decode(errors="replace") if binary else r.stderr
        raise Refusal(f"`git {' '.join(args)}` failed: {err.strip()}")
    return r.stdout


def git_ok(repo, *args) -> bool:
    return run(["git", *args], repo).returncode == 0


def show_bytes(repo, rev: str, path: str) -> bytes | None:
    r = run(["git", "show", f"{rev}:{path}"], repo, binary=True)
    return r.stdout if r.returncode == 0 else None


def show(repo, rev: str, path: str) -> str | None:
    """A file's text at a revision, or None if it is not there."""
    data = show_bytes(repo, rev, path)
    return data.decode("utf-8", errors="replace") if data is not None else None


def rev_parse(repo, rev: str) -> str | None:
    r = run(["git", "rev-parse", "--verify", "--quiet", rev], repo)
    return r.stdout.strip() if r.returncode == 0 else None


def tool_env() -> dict:
    """The environment for the checks: elan's lake on the PATH, as CI and AGENTS.md set it."""
    env = dict(os.environ)
    elan = str(Path.home() / ".elan" / "bin")
    env["PATH"] = elan + os.pathsep + env.get("PATH", "")
    return env


def blob_id(data: bytes) -> str:
    """git's id of a blob holding `data`."""
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def plural(n: int, word: str) -> str:
    return f"{n} {word}" + ("" if n == 1 else "s")


def tail(text: str, n: int = TAIL) -> str:
    lines = text.rstrip().splitlines()
    shown = lines[-n:]
    more = f"    … {len(lines) - n} lines before these\n" if len(lines) > n else ""
    return more + "\n".join("    " + line for line in shown)


# --------------------------------------------------------------------------------------
# The report: every step's outcome and time, printed as it happens and summed up at the end


class Step(NamedTuple):
    stage: str
    name: str
    outcome: str      # "ok", "FAIL", "skip", "note"
    seconds: float | None
    detail: str


class Report:
    def __init__(self):
        self.steps: list[Step] = []
        self.started = time.time()

    def add(self, stage, name, outcome, detail="", seconds=None):
        self.steps.append(Step(stage, name, outcome, seconds, detail))
        took = f"  ({seconds:.1f} s)" if seconds is not None else ""
        label = {"ok": "ok  ", "FAIL": "FAIL", "skip": "skip", "note": "note"}[outcome]
        first, *rest = (detail or "").splitlines() or [""]
        print(f"  {label}  {name}: {first}{took}" if first else f"  {label}  {name}{took}",
              flush=True)
        for line in rest:
            print(f"        {line}", flush=True)

    def heading(self, text):
        print(f"\n{text}", flush=True)

    def failed(self) -> list[Step]:
        return [s for s in self.steps if s.outcome == "FAIL"]


# --------------------------------------------------------------------------------------
# The diff, read once and parsed exactly


class Added(NamedTuple):
    path: str
    line: int       # line number in the new file
    text: str


def _unquote(path: str) -> str:
    """A path as git prints it in a header: quoted, with C escapes, when unusual."""
    if path.startswith('"') and path.endswith('"'):
        raw = path[1:-1].encode("latin-1", errors="backslashreplace")
        return raw.decode("unicode_escape").encode("latin-1").decode("utf-8", errors="replace")
    return path


HUNK = re.compile(r"^@@ -\d+(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


class Hunk(NamedTuple):
    path: str | None        # the new file's path; None when the hunk deletes the file
    removed: list[str]
    added: list[Added]


def diff_hunks(repo, old: str, new: str, *pathspec: str) -> list[Hunk]:
    """Every hunk of the diff from `old` to `new` (commits or trees), with the lines it
    removes and the lines it adds, each added line with its file and line number. Every
    file is read as text (`--text`), whatever .gitattributes says of it, and with no
    external diff or text conversion. Parsed by the hunk counts, so an added line that
    itself begins "+++" is not taken for a header."""
    out = git(repo, "diff", "--no-color", "--text", "--no-ext-diff", "--no-textconv",
              "--no-renames", "--unified=0", "--src-prefix=a/", "--dst-prefix=b/", old, new,
              "--", *pathspec, binary=True).decode("utf-8", errors="replace")
    hunks: list[Hunk] = []
    path = None
    old_left = new_left = 0
    line_no = 0
    for line in out.split("\n"):
        if old_left > 0 or new_left > 0:
            if line.startswith("+"):
                if path is not None:
                    hunks[-1].added.append(Added(path, line_no, line[1:]))
                line_no += 1
                new_left -= 1
            elif line.startswith("-"):
                hunks[-1].removed.append(line[1:])
                old_left -= 1
            elif line.startswith("\\"):
                pass        # "\ No newline at end of file"
            else:
                old_left = new_left = 0
            continue
        if line.startswith("diff --git "):
            path = None
        elif line.startswith("+++ "):
            target = _unquote(line[4:].rstrip("\t"))
            path = None if target == "/dev/null" else target[2:]
        elif line.startswith("@@"):
            m = HUNK.match(line)
            if m:
                old_left = int(m.group(1)) if m.group(1) is not None else 1
                line_no = int(m.group(2))
                new_left = int(m.group(3)) if m.group(3) is not None else 1
                hunks.append(Hunk(path, [], []))
    return hunks


def added_lines(repo, old: str, new: str, *pathspec: str) -> list[Added]:
    """Every line the diff from `old` to `new` adds, with its file and line number."""
    return [a for h in diff_hunks(repo, old, new, *pathspec) for a in h.added]


def changed_files(repo, old: str, new: str, *pathspec: str) -> list[tuple[str, str]]:
    """(status, path) for each file the diff changes, renames shown as delete and add."""
    out = git(repo, "diff", "--name-status", "-z", "--no-renames", old, new, "--", *pathspec)
    parts = out.split("\0")
    return [(parts[i][0], parts[i + 1]) for i in range(0, len(parts) - 1, 2)]


class Change(NamedTuple):
    status: str     # A, M, D, T
    path: str
    mode: str       # the new mode: 100644, 100755, 120000 (a symlink), 160000 (a gitlink)
    blob: str       # the new blob


def raw_changes(repo, old: str, new: str) -> list[Change]:
    out = git(repo, "diff", "--raw", "-z", "--no-renames", "--no-abbrev", old, new)
    parts = out.split("\0")
    changes = []
    for meta, path in zip(parts[0::2], parts[1::2]):
        fields = meta.lstrip(":").split()
        if len(fields) >= 5:
            changes.append(Change(fields[4][0], path, fields[1], fields[3]))
    return changes


def read_blobs(repo, ids) -> dict[str, bytes]:
    """The bytes of each blob, read straight from the object store (`git cat-file`), so
    that no attribute, filter or conversion stands between the scan and the content."""
    ids = list(dict.fromkeys(ids))
    if not ids:
        return {}
    r = run(["git", "cat-file", "--batch"], repo, input=("\n".join(ids) + "\n").encode(),
            binary=True)
    out, pos, blobs = r.stdout, 0, {}
    for oid in ids:
        nl = out.find(b"\n", pos)
        if nl < 0:
            break
        header = out[pos:nl].decode(errors="replace").split()
        if len(header) < 3:          # "<oid> missing"
            pos = nl + 1
            continue
        size = int(header[2])
        blobs[oid] = out[nl + 1:nl + 1 + size]
        pos = nl + 1 + size + 1
    return blobs


def is_binary(data: bytes) -> bool:
    """A NUL byte anywhere. (git looks only at the first 8000 bytes, so a file of prose
    with UTF-16 text after it would read as text, and its tail, a NUL between every
    character, would match no rule. A binary file is read whole, so nothing is lost.)"""
    return b"\0" in data


def empty_tree(repo) -> str:
    return git(repo, "hash-object", "-t", "tree", os.devnull).strip()


def gains(hunks: list[Hunk], count) -> bool:
    """Does the diff add a new mention? True when some hunk's added lines hold more
    mentions (as `count` counts them in the lines joined, so that a name broken across a
    wrapped line is still found) than its removed lines: a line edited in place that
    still names the same thing adds none."""
    for h in hunks:
        added = " ".join(a.text.strip() for a in h.added)
        removed = " ".join(line.strip() for line in h.removed)
        if count(added) > count(removed):
            return True
    return False


def under(path: str, prefixes) -> bool:
    """Is `path` one of `prefixes`, or under one that ends in a slash?"""
    return any(path == p or (p.endswith("/") and path.startswith(p)) for p in prefixes)


def is_protected(path: str) -> bool:
    return under(path, PROTECTED)


# --------------------------------------------------------------------------------------
# Step 2: the secret scan

# Each pattern is written so that its own source text does not match it, so this file
# passes its own scan.
PRIVATE_KEY = re.compile(r"BEGIN (?:[A-Z0-9]+ )*PRIVATE KEY")
TOKEN_RULES = [
    ("private key", PRIVATE_KEY),
    ("GitHub token", re.compile(r"(?<![A-Za-z0-9_])(?:gh[pousr]_[A-Za-z0-9]{30,}"
                                r"|github_pat_[A-Za-z0-9_]{30,})")),
    ("sk- API key", re.compile(r"(?<![A-Za-z0-9_-])sk-[A-Za-z0-9_-]{20,}")),
    ("Slack token", re.compile(r"(?<![A-Za-z0-9_])xox[abposr]-[A-Za-z0-9-]{10,}")),
    ("AWS access key", re.compile(r"(?<![A-Z0-9])(?:AKIA|ASIA)[0-9A-Z]{16}(?![0-9A-Z])")),
    ("Authorization header", re.compile(
        r"(?i)\bauthorization\b[\"']?\s*[:=]\s*[\"']?\s*"
        r"(?:(?:bearer|basic|token|digest)\s+)?[A-Za-z0-9+/=._~-]{8,}")),
    ("bearer token", re.compile(r"(?i)\bbearer\s+[A-Za-z0-9+/=._~-]{20,}")),
]
WEAK_RULES = ("Authorization header", "bearer token")   # not looked for in binary files
# A long base64 or hex run after a word naming a key, token, secret or password, perhaps
# with an opening bracket between (a value continued in parentheses). The name is
# bounded, and must start a word, so a long run of letters (an image's base64 in an SVG)
# costs linear time, not quadratic.
KEYWORD = re.compile(
    r"(?i)(?<![\w-])[\w-]{0,40}(?:key|token|secret|passw(?:or)?d|bearer)[\w-]{0,40}[\"']?"
    r"\s*(?:=>|:=|[:=]|\s)\s*(?:[(\[{]\s*)?[\"'`]?([A-Za-z0-9+/_=.~-]{20,})")
# A run that may be base64 (standard or URL-safe): decoded, and scanned again, when it
# decodes to text.
B64_RUN = re.compile(r"[A-Za-z0-9+/_-]{24,}={0,2}")
B64_DEPTH = 2           # base64 within base64, and no deeper
# Where two lines join: a string closed at the end of one and reopened at the start of
# the next (with `+`, `.`, `&` or `||` between, or a backslash), so that "abc" "def"
# reads as abcdef.
QUOTE_END = re.compile(r"""(["'`])\s*(?:\+|\.|&|\|\|)?\s*\\?$""")
QUOTE_START = re.compile(r"""^(?:\+|\.|&|\|\|)?\s*(["'`])""")
# The owner's private paths, in pieces for the reason above.
PRIVATE_PATHS = [
    re.compile("(?i)secret" + "s20"),
    re.compile("/" + "Downloads" + "/"),
    re.compile("/" + "Users" + "/"),
    re.compile(r"(?i)\b[A-Z]:\\" + "Users" + r"\\"),
    # A home directory folded into one name, as an agent's project and scratchpad
    # directories fold it: a dash, the word, a dash and a name.
    re.compile("(?<![A-Za-z0-9])-" + "Users" + "-[A-Za-z0-9]"),
    # An agent's scratchpad, under the temporary directory.
    re.compile("(?:/private)?/tmp/" + "claude" + "-"),
]
# A private path is flagged whole, from the space, quote or bracket before it to the one
# after, so that an allow-list entry pins that path and no other on its line.
PATH_EDGE = frozenset(" \t\r\n\"'`<>()[]{},;|")


def path_span(text: str, a: int, b: int) -> tuple[int, int]:
    while a > 0 and text[a - 1] not in PATH_EDGE:
        a -= 1
    while b < len(text) and text[b] not in PATH_EDGE:
        b += 1
    return a, b


# An identity git made up from the machine's name, when none was configured.
MACHINE_IDENTITY = re.compile(r"(?i)@[^\s<>@]+\.(?:local|localdomain|lan)>?$|\(none\)")
SECRET_FILES = [
    (re.compile(r"(^|/)\.env(\.[^/]*)?$"), ".env file"),
    (re.compile(r"\.(key|pem|p12|pfx)$", re.I), "key file"),
    (re.compile(r"(^|/)id_(rsa|dsa|ecdsa|ed25519)$"), "SSH private key file"),
]
# Printable runs in a binary file, line breaks included, read as lines of text; and runs
# of UTF-16 text, little- and big-endian, wherever they stand in it.
PRINTABLE_RUN = re.compile(rb"[\x20-\x7e\t\r\n]{8,}")
UTF16_RUNS = ((re.compile(rb"(?:[\x20-\x7e\t\r\n]\x00){8,}"), "utf-16-le"),
              (re.compile(rb"(?:\x00[\x20-\x7e\t\r\n]){8,}"), "utf-16-be"))
WINDOW = 40             # bytes kept on each side of a hit in a binary file, for the report
KNOWN_RULES = ({rule for rule, _ in TOKEN_RULES} | {rule for _, rule in SECRET_FILES}
               | {"key, token or secret", "private path", "private path in a file name",
                  "private path in an identity", "machine-made identity",
                  "symlink out of the repository"})


def entropy(s: str) -> float:
    counts = {c: s.count(c) for c in set(s)}
    return -sum(k / len(s) * math.log2(k / len(s)) for k in counts.values())


def looks_secret(value: str) -> bool:
    """A value after a key word: a long hex run, or a long random-looking base64 run.
    Lean names, prose and paths are not."""
    value = value.strip("=.")
    if re.fullmatch(r"[0-9a-fA-F]{32,}", value):
        return True
    segments = re.split(r"[/.]", value)
    if len(segments) > 1 and all(re.fullmatch(r"[A-Za-z_-]*\d{0,2}[A-Za-z_-]*", s)
                                 for s in segments):
        return False    # a path or a dotted name
    digits = sum(c.isdigit() for c in value)
    letters = sum(c.isalpha() for c in value)
    return len(value) >= 20 and digits >= 2 and letters >= 4 and entropy(value) >= 3.5


class Finding(NamedTuple):
    rule: str
    path: str
    line: int | None
    text: str           # the whole line (or lines), for the allow-list to match
    span: tuple[int, int]
    end: int | None = None          # the last line, for a finding across lines
    commit: str | None = None       # the commit that brings it, if the push takes it out

    def shown(self) -> str:
        """The line with the secret masked, so the report does not repeat it."""
        a, b = self.span
        secret = self.text[a:b]
        masked = secret[:4] + f"…({len(secret)} chars)" if b - a > 8 else secret
        line = (self.text[:a] + masked + self.text[b:]).strip()
        if len(line) > 140:
            line = line[:140] + "…"
        where = f"{self.path}:{self.line}" if self.line else self.path
        if self.end and self.end != self.line:
            where += f"-{self.end}"
        if self.commit:
            where += f" (in commit {self.commit[:12]})"
        return f"{where}: {self.rule}: {line}"


def readable(raw: bytes) -> bool:
    """Bytes that read as text: printable ASCII and line breaks, nearly all of them."""
    text = sum(32 <= b < 127 or b in (9, 10, 13) for b in raw)
    return len(raw) >= 12 and text >= 0.9 * len(raw)


def b64_text(run: str) -> str | None:
    """A base64 run decoded, if it decodes to readable text; else None. The first 48
    bytes are decoded first, so that an image's base64 costs little."""
    body = run.rstrip("=")
    if len(body) % 4 == 1:
        return None
    if "-" in body or "_" in body:
        if "+" in body or "/" in body:
            return None
        body = body.replace("-", "+").replace("_", "/")
    padded = body + "=" * (-len(body) % 4)
    try:
        if not readable(base64.b64decode(padded[:64], validate=True)):
            return None
        raw = base64.b64decode(padded, validate=True)
    except (binascii.Error, ValueError):
        return None
    return raw.decode("utf-8", errors="replace") if readable(raw) else None


def hits(text: str, *, strong_only=False, depth=0) -> list[tuple[str, tuple, tuple]]:
    """(rule, the span of the match, the span to mask) for each possible secret in text,
    base64 decoded and looked through too (not in binary files: `strong_only`)."""
    found = []
    for rule, pattern in TOKEN_RULES:
        if strong_only and rule in WEAK_RULES:
            continue
        for m in pattern.finditer(text):
            found.append((rule, m.span(), m.span()))
    if not strong_only:
        for m in KEYWORD.finditer(text):
            if looks_secret(m.group(1)):
                found.append(("key, token or secret", m.span(), m.span(1)))
    for pattern in PRIVATE_PATHS:
        for m in pattern.finditer(text):
            span = path_span(text, *m.span())
            found.append(("private path", span, span))
    if not strong_only and depth < B64_DEPTH:
        for m in B64_RUN.finditer(text):
            plain = b64_text(m.group(0))
            if plain is None:
                continue
            for rule in dict.fromkeys(r for r, _, _ in hits(plain, depth=depth + 1)):
                rule = rule.removeprefix("base64-encoded ")
                found.append((f"base64-encoded {rule}", m.span(), m.span()))
    return found


def scan_text(path: str, line_no: int | None, text: str, *, strong_only=False) -> list[Finding]:
    # One finding per place: a token can match two rules.
    found, seen = [], set()
    for rule, _, mask in hits(text, strong_only=strong_only):
        if mask not in seen:
            seen.add(mask)
            found.append(Finding(rule, path, line_no, text, mask))
    return found


def joined_views(texts: list[str]) -> list[tuple[str, list[int], list[int]]]:
    """A run of lines read as one, two ways: with a space between lines (a key word at the
    end of one line, its value on the next), and closed up (a value broken across lines,
    or a string continued with quotes, `+` or a backslash). Each view comes with the
    offset and length of each line's piece of it."""
    spaced = [t.strip() for t in texts]
    tight = list(spaced)
    for i in range(len(tight) - 1):
        a, b = tight[i], tight[i + 1]
        ma, mb = QUOTE_END.search(a), QUOTE_START.match(b)
        if ma and mb and ma.group(1) == mb.group(1):
            tight[i], tight[i + 1] = a[:ma.start()], b[mb.end():]
        elif a.endswith("\\"):
            tight[i] = a[:-1].rstrip()
    views = []
    for pieces, sep in ((spaced, " "), (tight, "")):
        starts, pos = [], 0
        for p in pieces:
            starts.append(pos)
            pos += len(p) + len(sep)
        views.append((sep.join(pieces), starts, [len(p) for p in pieces]))
    return views


def runs(numbered: list[tuple[int, str]]) -> list[list[tuple[int, str]]]:
    """Numbered lines cut into runs of consecutive line numbers."""
    out: list[list[tuple[int, str]]] = []
    for no, text in numbered:
        if out and no == out[-1][-1][0] + 1:
            out[-1].append((no, text))
        else:
            out.append([(no, text)])
    return out


def pieces_in(starts: list[int], lengths: list[int], a: int, b: int) -> list[int]:
    """The pieces of a joined view (by index) that the span a..b touches."""
    return [i for i, (s, n) in enumerate(zip(starts, lengths)) if s < b and s + n > a]


def scan_block(path: str, numbered: list[tuple[int, str]]) -> list[Finding]:
    """The lines a diff adds to one file (or a commit message's lines), each alone and
    then each run of consecutive lines read as one, for a secret split across lines.
    A finding across lines is kept unless what it masks lies in one line that is
    already flagged alone for the same text; and once, in the widest run of lines it is
    seen in."""
    found = []
    alone: set[tuple[int, str]] = set()
    for no, text in numbered:
        for f in scan_text(path, no, text):
            found.append(f)
            alone.add((no, text[f.span[0]:f.span[1]]))
    for run in runs(numbered):
        if len(run) < 2:
            continue
        across: dict[tuple, Finding] = {}
        for joined, starts, lengths in joined_views([t for _, t in run]):
            for rule, (a, b), (ma, mb) in hits(joined):
                lines = pieces_in(starts, lengths, a, b)
                if len(lines) < 2:
                    continue
                first, last = lines[0], lines[-1]
                masked = pieces_in(starts, lengths, ma, mb)
                if len(masked) == 1 and (run[masked[0]][0], joined[ma:mb]) in alone:
                    continue
                lo, hi = starts[first], starts[last] + lengths[last]
                mask = (max(ma, lo) - lo, min(mb, hi) - lo)
                key = (run[first][0], run[last][0], mask)
                across.setdefault(key, Finding(rule, path, run[first][0], joined[lo:hi], mask,
                                               end=run[last][0]))
        wide = list(across.values())
        found += [f for f in wide if not any((g.line, g.end) != (f.line, f.end)
                                             and g.line <= f.line and g.end >= f.end
                                             for g in wide)]
    return found


def utf16_text(data: bytes) -> str | None:
    """A blob that is UTF-16 text (a byte-order mark, or a NUL beside nearly every ASCII
    byte), decoded; else None."""
    if data[:2] in (b"\xff\xfe", b"\xfe\xff"):
        return data.decode("utf-16", errors="replace")
    head = data[:512]
    if len(head) >= 16:
        for nul_at, codec in ((1, "utf-16-le"), (0, "utf-16-be")):
            if head[nul_at::2].count(0) >= 0.9 * len(head[nul_at::2]):
                return data.decode(codec, errors="replace")
    return None


def printable(text: str) -> str:
    """Text with every character outside printable ASCII shown as a dot, one for one, so
    that spans into it still hold."""
    return re.sub(r"[^\x20-\x7e]", ".", text)


def scan_binary(path: str, data: bytes) -> list[Finding]:
    """A binary file, read whole: the strong rules over its bytes, each hit with a window
    of WINDOW bytes on each side as its text (never the whole file, which an allow-list
    match would otherwise find anywhere, and which the report would print); its
    printable runs, line breaks included, read as lines with every rule, so that a NUL
    planted in a text file does not hide it, nor a value split over two lines; its runs
    of UTF-16 text, wherever they stand, read the same way; and, if the whole of it is
    UTF-16 text, its lines."""
    raw = data.decode("latin-1")
    found = []
    for f in scan_text(path, None, raw, strong_only=True):
        a, b = f.span
        lo, hi = max(0, a - WINDOW), min(len(raw), b + WINDOW)
        found.append(f._replace(text=printable(raw[lo:hi]), span=(a - lo, b - lo)))
    seen = {(f.rule, f.text[f.span[0]:f.span[1]]) for f in found}

    def add(more: list[Finding]) -> None:
        for f in more:
            key = (f.rule, f.text[f.span[0]:f.span[1]])
            if key not in seen:
                seen.add(key)
                found.append(f)

    def lines_of(text: str, first: int) -> list[tuple[int, str]]:
        return list(enumerate(text.splitlines(), first))

    line, pos = 1, 0        # the line each run starts on, counted as the runs go
    for m in PRINTABLE_RUN.finditer(data):
        line, pos = line + data.count(b"\n", pos, m.start()), m.start()
        add(scan_block(path, lines_of(m.group(0).decode("ascii"), line)))
    for pattern, codec in UTF16_RUNS:
        for m in pattern.finditer(data):
            add(scan_block(path, lines_of(m.group(0).decode(codec, errors="replace"), 1)))
    text = utf16_text(data)
    if text is not None:
        add(scan_block(path, lines_of(text, 1)))
    return found


def scan_path(path: str) -> list[Finding]:
    found = [Finding(rule, path, None, path, (0, 0)) for pattern, rule in SECRET_FILES
             if pattern.search(path)]
    for pattern in PRIVATE_PATHS:
        for m in pattern.finditer(path):
            found.append(Finding("private path in a file name", path, None, path,
                                 path_span(path, *m.span())))
    return found


def scan_link(path: str, target: str) -> list[Finding]:
    """A symlink that points out of the repository: to an absolute path, to a home
    directory, or up past the top. (Its target is an added line too, so the text rules,
    the private paths among them, see it as well.)"""
    t = target.strip()
    up = posixpath.normpath(posixpath.join(posixpath.dirname(path), t.replace("\\", "/")))
    if t.startswith(("/", "\\", "~")) or re.match(r"^[A-Za-z]:", t) or up == ".." \
            or up.startswith("../"):
        text = f"{path} -> {t}"
        return [Finding("symlink out of the repository", path, None, text, (0, 0))]
    return []


def scan_identity(where: str, ident: str) -> list[Finding]:
    """A commit's author or committer: no private path, and not an identity git made up
    from the machine's name."""
    found = [Finding("private path in an identity", where, None, ident, m.span())
             for pattern in PRIVATE_PATHS for m in pattern.finditer(ident)]
    m = MACHINE_IDENTITY.search(ident)
    if m:
        found.append(Finding("machine-made identity", where, None, ident, m.span()))
    return found


class Allow(NamedTuple):
    path: str
    match: str
    rule: str
    reason: str
    sha256: str | None      # the SHA-256 of the flagged value, when match does not hold it


# Places the scan reads that no entry may allow: a flagged commit message or identity is
# rewritten, and the pull request's body, title and branch name are the coordinator's to
# change.
UNALLOWABLE = re.compile(r"^commit |^the pull request's body$|^the title$|^the branch name$")
SHA256 = re.compile(r"[0-9a-f]{64}")


def load_allowlist(repo, rev) -> list[Allow]:
    """The allow-list as `rev` (origin/main) has it. Each entry is narrow: one file named
    exactly (no glob, and never a commit's message or identity, nor the pull request's
    body), one rule, a part of the flagged line at least eight characters long, the
    flagged value pinned (held in that part, or named by its SHA-256), and a reason. A
    broad entry is refused, not read."""
    text = show(repo, rev, ALLOWLIST) if rev else None
    if text is None:
        return []
    import tomllib
    try:
        data = tomllib.loads(text)
    except tomllib.TOMLDecodeError as e:
        raise Refusal(f"origin/main's {ALLOWLIST} is not valid TOML: {e}")
    entries, problems = [], []
    for i, entry in enumerate(data.get("allow", []), 1):
        if not isinstance(entry, dict):
            problems.append(f"entry {i} is not a table")
            continue
        path, match = entry.get("path"), entry.get("match")
        reason, rule, digest = entry.get("reason"), entry.get("rule"), entry.get("sha256")
        bad = []
        if not isinstance(path, str) or not path:
            bad.append("has no path")
        elif any(c in path for c in "*?["):
            bad.append("names more than one file (a glob in path)")
        elif UNALLOWABLE.search(path):
            bad.append(f"names {path!r}, which cannot be allowed (reword or rewrite it)")
        if not isinstance(match, str) or len(match) < 8:
            bad.append("has no match of at least 8 characters")
        if not isinstance(rule, str) or rule.removeprefix("base64-encoded ") not in KNOWN_RULES:
            bad.append("names no rule of the scan")
        if digest is not None and not (isinstance(digest, str) and SHA256.fullmatch(digest)):
            bad.append("has a sha256 that is not 64 lowercase hex digits")
        if not isinstance(reason, str) or not reason.strip():
            bad.append("has no reason")
        if bad:
            problems.append(f"entry {i} " + ", ".join(bad))
        else:
            entries.append(Allow(path, match, rule, reason.strip(), digest))
    if problems:
        raise Refusal(f"origin/main's {ALLOWLIST} has a broad or incomplete entry: "
                      + "; ".join(problems))
    return entries


def flagged_value(f: Finding) -> str:
    """What a finding flags: the matched text, or, for a rule on the whole file name or
    link (an empty span), its whole text."""
    a, b = f.span
    return f.text[a:b] if b > a else f.text


def value_sha256(f: Finding) -> str:
    return hashlib.sha256(flagged_value(f).encode("utf-8", errors="surrogatepass")).hexdigest()


def allowed(f: Finding, allow: list[Allow]) -> Allow | None:
    """The entry that excuses the finding: the same file and rule, a match found in the
    flagged line, and the flagged value itself pinned, held in the match or named by its
    SHA-256; so another value on a similar line is still refused. (A value written into
    the allow-list would be flagged there in turn, in the allow-list's own pull request,
    where its new entry does not count yet: hence the SHA-256.)"""
    if UNALLOWABLE.search(f.path):
        return None
    for a in allow:
        if a.path == f.path and a.rule == f.rule and a.match in f.text and (
                flagged_value(f) in a.match or a.sha256 == value_sha256(f)):
            return a
    return None


class Introduced(NamedTuple):
    """What a diff brings in: the files it adds or changes, the lines it adds to text
    files, the binary files ({path: bytes}), and the symlinks ({path: blob})."""
    files: set[str]
    lines: list[Added]
    binaries: dict[str, bytes]
    links: dict[str, str]


def introduced(repo, old: str, new: str) -> Introduced:
    """Text or binary is read from each blob's bytes, never from .gitattributes."""
    changes = [c for c in raw_changes(repo, old, new) if c.status != "D"]
    regular = {c.path: c.blob for c in changes if c.mode not in ("120000", "160000")}
    blobs = read_blobs(repo, regular.values())
    binaries = {p: blobs.get(b, b"") for p, b in regular.items() if is_binary(blobs.get(b, b""))}
    lines = [a for a in added_lines(repo, old, new) if a.path not in binaries]
    links = {c.path: c.blob for c in changes if c.mode == "120000"}
    return Introduced({c.path for c in changes}, lines, binaries, links)


def commit_introduced(repo, commit: str, parents: list[str]) -> Introduced:
    """What one commit brings in that none of its parents has. For a merge, that is what
    it adds against every parent (its own resolution): each side's commits are scanned
    on their own, or are on origin already."""
    each = [introduced(repo, p, commit) for p in parents or [empty_tree(repo)]]
    if len(each) == 1:
        return each[0]
    keys = set.intersection(*({(a.path, a.text) for a in e.lines} for e in each))
    return Introduced(set.intersection(*(e.files for e in each)),
                      [a for a in each[0].lines if (a.path, a.text) in keys],
                      {p: d for p, d in each[0].binaries.items()
                       if all(p in e.binaries for e in each)},
                      {p: b for p, b in each[0].links.items()
                       if all(e.links.get(p) == b for e in each)})


def scan_introduced(repo, d: Introduced) -> list[Finding]:
    found = []
    for path in sorted(d.files):
        found += scan_path(path)
    by_file: dict[str, list[tuple[int, str]]] = {}
    for a in d.lines:
        by_file.setdefault(a.path, []).append((a.line, a.text))
    for path, numbered in by_file.items():
        found += scan_block(path, numbered)
    for path, data in sorted(d.binaries.items()):
        found += scan_binary(path, data)
    for path, blob in sorted(d.links.items()):
        target = git(repo, "cat-file", "blob", blob, binary=True)
        found += scan_link(path, target.decode("utf-8", errors="replace"))
    return found


def secret_scan(repo, base: str | None, sha: str, rep: Report, allow_rev: str | None) -> None:
    """The net change of the push, then each commit's own change, its message and its
    identities: a secret added and taken out again, or a key file added and then
    renamed, is still in the history the push publishes. `base` None: no common history,
    so every commit is read."""
    rep.heading("2. Secret scan")
    t = time.time()
    allow = load_allowlist(repo, allow_rev)
    commits = [line.split() for line in
               git(repo, "rev-list", "--reverse", "--parents",
                   f"{base}..{sha}" if base else sha).splitlines()]
    diffs = [(None, introduced(repo, base or empty_tree(repo), sha))]
    if [c[1:] for c in commits] != [[base]]:    # one commit on origin/main: the same diff
        diffs += [(c, commit_introduced(repo, c, parents)) for c, *parents in commits]
    findings: list[Finding] = []
    for commit, d in diffs:
        findings += [f._replace(commit=commit) for f in scan_introduced(repo, d)]
    for c, *_ in commits:
        message = git(repo, "log", "-1", "--format=%B", c)
        findings += scan_block(f"commit {c[:12]} message",
                               list(enumerate(message.splitlines(), 1)))
        idents = git(repo, "log", "-1", "--format=%an <%ae>%x00%cn <%ce>", c).rstrip("\n")
        author, committer = (idents.split("\0") + ["", ""])[:2]
        findings += scan_identity(f"commit {c[:12]} author", author)
        findings += scan_identity(f"commit {c[:12]} committer", committer)
    # Each finding once: where the push leaves it if it does, else in its commit.
    unique: dict[tuple, Finding] = {}
    for f in findings:
        unique.setdefault((f.rule, f.path, f.text, f.span), f)
    findings = list(unique.values())
    refused = [f for f in findings if not allowed(f, allow)]
    passed = [(f, allowed(f, allow)) for f in findings if allowed(f, allow)]
    seconds = time.time() - t
    net = diffs[0][1]
    scanned = (f"{plural(len(net.lines), 'added line')} in {plural(len(net.files), 'file')} "
               f"({len(net.binaries)} binary), and each of {plural(len(commits), 'commit')} "
               "on its own, with its message and identities")
    for f, a in passed:
        rep.add("2", "allow-listed", "note", f"{f.shown()}\nreason: {a.reason}")
    if refused:
        detail = "\n".join(f.shown() for f in refused)
        rep.add("2", "secrets", "FAIL", f"{len(refused)} found in {scanned}:\n{detail}", seconds)
        raise Refusal(f"the secret scan found {len(refused)} possible secret(s) or private "
                      f"path(s). Remove them (and rewrite the commits that hold them), or, for "
                      f"a false positive, add a narrow entry with its reason to {ALLOWLIST} "
                      "in a pull request of its own, before this one, pinning the value by "
                      "its SHA-256 (printf %s '<the value>' | shasum -a 256).")
    rep.add("2", "secrets", "ok", f"nothing found in {scanned}", seconds)


# --------------------------------------------------------------------------------------
# Step 3: the invariant guards


OPEN, CLOSE = "([{⟨⦃⦗", ")]}⟩⦄⦘"


def statement_end(text: str) -> int:
    """Where a declaration's statement ends: at its own `:=`, the first one outside
    brackets, comments and strings, so that a binder's default value (`(h : p := by
    simp)`) or a comment holding `:=` does not end it early. The end of `text` if none."""
    depth, i, n = 0, 0, len(text)
    while i < n:
        if text.startswith("--", i):
            nl = text.find("\n", i)
            i = n if nl < 0 else nl
            continue
        if text.startswith("/-", i):
            level, i = 1, i + 2
            while i < n and level:
                if text.startswith("/-", i):
                    level, i = level + 1, i + 2
                elif text.startswith("-/", i):
                    level, i = level - 1, i + 2
                else:
                    i += 1
            continue
        c = text[i]
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
        elif c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(":=", i):
            return i
        i += 1
    return n


def source_statement(src: str, n: int, name: str | None) -> str | None:
    """The statement of `theorem PropN` (or `PropN.<name>`) as written in the Lean: its
    binders and type, up to its own `:=`, whitespace made single (so a re-wrapped
    statement is the same statement, and a changed binder on a re-wrapped line is not).
    The docstring is left out: it is Heath's enunciation, which check_fidelity compares
    with heath/."""
    if name is None:
        span = heath.theorem_span(src, n)
        if span is None:
            return None
        text = src[span.body:span.end]
    else:
        m = re.search(r"(?m)^theorem Prop%d\.%s\s" % (n, re.escape(name)), src)
        if not m:
            return None
        text = src[m.end():]
    return " ".join(text[:statement_end(text)].split())


def facts_statements(text: str | None) -> dict[str, str | None]:
    if not text:
        return {}
    try:
        facts = json.loads(text)
    except json.JSONDecodeError:
        return {}
    return {p["ref"]: p.get("statement") for p in facts.get("propositions", []) if "ref" in p}


LEAN_FILE = re.compile(r"^Elements/Book([IVX]+)/Prop(\d+)\.lean$")


def lean_files(repo, rev) -> dict[tuple[str, int], str]:
    out = git(repo, "ls-tree", "-r", "--name-only", rev, "--", "Elements")
    found = {}
    for path in out.splitlines():
        m = LEAN_FILE.match(path)
        if m:
            found[(m.group(1), int(m.group(2)))] = path
    return found


def ref_count(text: str, ref: str) -> int:
    """How often `text` names the proposition of `ref`: "III.16", "III. 16" or
    `BookIII.Prop16`. A porism or companion is named by its proposition. "III.1" is
    not named by "III.16", nor "I.1" by "III.1" or "I.10"."""
    r = heath.parse_ref(ref)
    plain = r"(?<![\w.])%s\.\s?%d(?!\d)" % (r.book, r.n)
    lean = r"(?<!\w)Book%s\.Prop%d(?!\d)" % (r.book, r.n)
    return len(re.findall(plain, text)) + len(re.findall(lean, text))


def names_ref(text: str, ref: str) -> bool:
    return ref_count(text, ref) > 0


def guard_statements(repo, base, sha, wt: Path, rep: Report) -> list[str]:
    """The statements changed with a brief or decision naming them, for the body."""
    t = time.time()
    old_facts = facts_statements(show(repo, base, "facts.json"))
    new_facts = facts_statements((wt / "facts.json").read_text()
                                 if (wt / "facts.json").exists() else None)
    old_files, new_files = lean_files(repo, base), lean_files(repo, sha)
    refs = set(old_facts) | set(new_facts)
    sources = {}
    for files, rev in ((old_files, base), (new_files, sha)):
        for (book, n), path in files.items():
            src = show(repo, rev, path) or ""
            sources[(rev, path)] = src
            refs.add(f"{book}.{n}")
            if re.search(r"(?m)^theorem Prop%d\.porism\s" % n, src):
                refs.add(f"{book}.{n} Por.")
    briefs = diff_hunks(repo, base, sha, BRIEFS)
    changed, approved, new = [], [], []
    for ref in sorted(refs, key=lambda r: (heath.prop_key(r), r)):
        r = heath.parse_ref(ref)
        path = f"Elements/Book{r.book}/Prop{r.n:02d}.lean"
        old_src = sources.get((base, path))
        new_src = sources.get((sha, path))
        old_sig = source_statement(old_src, r.n, r.name) if old_src else None
        new_sig = source_statement(new_src, r.n, r.name) if new_src else None
        why = []
        if old_sig is not None and new_sig is None:
            why.append("its theorem is gone from the Lean")
        elif old_sig is not None and old_sig != new_sig:
            why.append("the Lean statement changed")
        if old_facts.get(ref) and new_facts.get(ref) and old_facts[ref] != new_facts[ref]:
            why.append("facts.json's statement changed")
        if ref in old_facts and ref not in new_facts:
            why.append("its facts.json entry is gone")
        if not why:
            if old_sig is None and ref not in old_facts:
                new.append(ref)
            continue
        if gains(briefs, lambda text: ref_count(text, ref)):
            approved.append(f"{ref} ({'; '.join(why)}), named in the docs/briefs/ lines added")
        else:
            changed.append(f"{ref}: {'; '.join(why)}, and no new line in docs/briefs/ "
                           f"(a brief's revision or a decisions entry) names {r.parent}; "
                           "an old line edited in place does not count")
    seconds = time.time() - t
    count = len(refs) - len(new)
    notes = []
    if approved:
        notes.append("changed with a brief or decision naming them: " + ", ".join(approved))
    if new:
        notes.append(f"new statements (not changes): {', '.join(new)}")
    if changed:
        rep.add("3", "statements", "FAIL", "\n".join(changed + notes), seconds)
    else:
        rep.add("3", "statements", "ok",
                "\n".join([f"{count} statements compared in facts.json and the Lean"] + notes),
                seconds)
    return approved


LOCK_MENTION = re.compile(r"(?i)\baxioms\.lock\b|\baxiom lock\b")


def guard_lock(repo, base, sha, rep: Report) -> None:
    if git_ok(repo, "diff", "--quiet", f"{base}..{sha}", "--", LOCK):
        rep.add("3", "axiom lock", "ok", f"{LOCK} unchanged")
        return
    if gains(diff_hunks(repo, base, sha, DECISIONS), lambda t: len(LOCK_MENTION.findall(t))):
        rep.add("3", "axiom lock", "ok", f"{LOCK} changed, and {DECISIONS} gains a line "
                "mentioning the lock")
    else:
        rep.add("3", "axiom lock", "FAIL", f"{LOCK} changed, and no new line in {DECISIONS} "
                "mentions the lock (\"axioms.lock\" or \"axiom lock\"; an old line edited in "
                "place does not count)")


def guard_protected(repo, base, sha, rep: Report) -> list[str]:
    """A protected path changes only with a new line in the decisions page naming the
    file; the pull request then carries the label security-review. The files, for the
    body and the merge."""
    files = protected_files(repo, base, sha)
    if not files:
        rep.add("3", "protected paths", "ok", "none changed")
        return []
    decisions = diff_hunks(repo, base, sha, DECISIONS)

    def named(path):
        pattern = re.compile(r"(?<![\w-])%s(?![\w/-])" % re.escape(path))
        return gains(decisions, lambda text: len(pattern.findall(text)))

    unnamed = [p for p in files if not named(p)]
    if unnamed:
        rep.add("3", "protected paths", "FAIL",
                f"changed with no new line in {DECISIONS} naming them: {', '.join(unnamed)} "
                f"(a protected change is named file by file in a decisions entry, and its "
                f"pull request carries the label {SECURITY_LABEL})")
    else:
        rep.add("3", "protected paths", "ok",
                f"changed, each named in {DECISIONS}: {', '.join(files)}; the pull request "
                f"carries the label {SECURITY_LABEL}, and needs /security-review")
    return files


COMMENT = re.compile(r"<!--.*?-->", re.S)
LEAF_RANGE = re.compile(r"\bn(\d+)\s*[–-]\s*n(\d+)\b")
LEAF = re.compile(r"\bn(\d+)\b")
LEAF_WORD = re.compile(r"(?i)\bleaf\b|\bleaves\b")
SOURCE_COMMENT = re.compile(r"(?i)<!--\s*source\s*:")


def own_leaves(text: str) -> set[int]:
    """The scan leaves a heath file's source comment (its first comment) names."""
    m = COMMENT.search(text)
    if not m:
        return set()
    source = m.group(0)
    leaves = set()
    for a, b in LEAF_RANGE.findall(source):
        leaves |= set(range(int(a), int(b) + 1))
    leaves |= {int(x) for x in LEAF.findall(source)}
    return leaves


def guard_heath(repo, base, sha, wt: Path, rep: Report) -> None:
    files = changed_files(repo, base, sha, "heath")
    if not files:
        rep.add("3", "heath/", "ok", "unchanged")
        return
    added: dict[str, set[int]] = {}
    for a in added_lines(repo, base, sha, "heath"):
        added.setdefault(a.path, set()).add(a.line)
    bad, good = [], []
    for status, path in files:
        if status == "D":
            bad.append(f"{path}: deleted (a change to heath/ is made against the page image "
                       "and carries a comment naming the leaf checked)")
            continue
        text = (wt / path).read_text(errors="replace")
        # The leaves are origin/main's: a change cannot widen its own source comment.
        old = show(repo, base, path)
        leaves = own_leaves(old if old is not None else text)
        lines = added.get(path, set())
        named = set()
        source = COMMENT.search(text)
        for m in COMMENT.finditer(text):
            # The source comment, the file's first, lists the leaves; it does not check
            # one. It is known by its place, so that "Source:" rewritten as "source:"
            # does not make it count; and any comment that reads as one is skipped too.
            if m.start() == source.start() or SOURCE_COMMENT.match(m.group(0)):
                continue
            first = text.count("\n", 0, m.start()) + 1
            last = first + m.group(0).count("\n")
            if lines & set(range(first, last + 1)) and LEAF_WORD.search(m.group(0)):
                named |= {int(x) for x in LEAF.findall(m.group(0))}
        checked = named & leaves if leaves else named
        if checked:
            good.append(f"{path} (leaf {', '.join(f'n{x}' for x in sorted(checked))})")
        elif named:
            bad.append(f"{path}: the comment added names leaf "
                       f"{', '.join(f'n{x}' for x in sorted(named))}, not one of its own "
                       f"pages' leaves ({', '.join(f'n{x}' for x in sorted(leaves))}, as "
                       "origin/main's copy of its source comment lists them)")
        else:
            bad.append(f"{path}: changed, with no comment in the change naming the scan leaf "
                       "checked (docs/STYLE.md, section 5)")
    if bad:
        rep.add("3", "heath/", "FAIL", "\n".join(bad + [f"checked: {g}" for g in good]))
    else:
        rep.add("3", "heath/", "ok", "each change names a leaf checked: " + ", ".join(good))


def guard_directories(repo, base, sha, rep: Report) -> None:
    def dirs(rev):
        out = git(repo, "ls-tree", "-r", "-d", "--name-only", rev, "--", *GUARDED_DIRS)
        return set(out.splitlines())

    gone = sorted(dirs(base) - dirs(sha))
    top = [d for d in gone if not any(d.startswith(p + "/") for p in gone)]
    if not top:
        rep.add("3", "directories", "ok", f"none deleted under {', '.join(GUARDED_DIRS)}")
        return
    decisions = diff_hunks(repo, base, sha, DECISIONS)

    def named(d):
        pattern = re.compile(r"(?<![\w/.-])%s/?(?![\w./-])" % re.escape(d))
        return gains(decisions, lambda text: len(pattern.findall(text)))

    unnamed = [d for d in top if not named(d)]
    if unnamed:
        rep.add("3", "directories", "FAIL", f"deleted with no new line in {DECISIONS} "
                f"naming them: {', '.join(d + '/' for d in unnamed)}")
    else:
        rep.add("3", "directories", "ok", f"deleted, each named in {DECISIONS}: "
                f"{', '.join(d + '/' for d in top)}")


def status_lines(wt: Path, excludes: list[str]) -> subprocess.CompletedProcess:
    return run(["git", "status", "--porcelain", "--", ".", *excludes], wt)


def guard_fidelity(wt: Path, rep: Report, logs: Path, label="", fail="FAIL") -> None:
    t = time.time()
    r = run([PY, "scripts/check_fidelity.py"], wt, env=tool_env())
    out = (r.stdout or "") + (r.stderr or "")
    (logs / f"03-check_fidelity{slug_of(label)}.log").write_text(out)
    seconds = time.time() - t
    if r.returncode == 0:
        rep.add("3", "review records" + label, "ok", "check_fidelity.py passes on the commit "
                "as committed: no record stale", seconds)
    else:
        rep.add("3", "review records" + label, fail,
                "check_fidelity.py fails on the commit as committed:\n" + tail(out, 25), seconds)


def guard_generated(wt: Path, rep: Report, logs: Path, label="", fail="FAIL",
                    excludes=()) -> None:
    """The generated pages are current: render.py, run on the commit as committed (its
    facts.json as committed), changes nothing. It needs no Lean, so it runs here, before
    the full checks, which run it again after the build."""
    t = time.time()
    r = run([PY, "scripts/render.py"], wt, env=tool_env())
    out = (r.stdout or "") + (r.stderr or "")
    status = status_lines(wt, list(excludes))
    (logs / f"03-render{slug_of(label)}.log").write_text(
        f"{out}\n$ git status --porcelain\n{status.stdout}")
    seconds = time.time() - t
    name = "generated pages" + label
    if r.returncode != 0:
        rep.add("3", name, fail, "render.py fails on the commit as committed:\n" + tail(out, 25),
                seconds)
    elif status.returncode != 0 or status.stdout.strip():
        rep.add("3", name, fail, "stale: render.py, on the commit as committed, changes "
                "them; regenerate with python3 scripts/render.py and commit the result with "
                "its sources (docs/WORKFLOW.md, section 8):\n"
                + tail(status.stdout + status.stderr, 25), seconds)
    else:
        rep.add("3", name, "ok", "render.py changes nothing on the commit as committed", seconds)


def guard_foundations(repo, base, sha, rep: Report) -> None:
    """Not a guard: the foundations are the coordinator's, so their changes are listed."""
    files = changed_files(repo, base, sha, "Elements/Foundations")
    if files:
        rep.add("3", "foundations", "note", "changed (the coordinator's files): "
                + ", ".join(p for _, p in files))


def slug_of(label: str) -> str:
    """A pass's label, for a log file's name: " (the commit's checks)" -> "-the-commit-s-checks"."""
    s = re.sub(r"[^A-Za-z0-9]+", "-", label).strip("-")
    return f"-{s}" if s else ""


@contextlib.contextmanager
def base_copies(repo, base, wt: Path, changes: list[tuple[str, str]]):
    """origin/main's copies of the check inputs the commit changes, put in place in the
    worktree (and the files the commit adds to them taken out); the worktree is reset
    to the commit afterwards. Yields the pathspecs that keep them out of `git status`."""
    for status, path in changes:
        target = wt / path
        if target.is_symlink() or target.is_file():
            target.unlink()
        if status == "A":
            continue
        entry = git(repo, "ls-tree", "-z", base, "--", path).split("\0")[0]
        if not entry:
            continue
        mode, _, oid = entry.split("\t", 1)[0].split()
        data = git(repo, "cat-file", "blob", oid, binary=True)
        target.parent.mkdir(parents=True, exist_ok=True)
        if mode == "120000":
            os.symlink(data.decode(errors="replace"), target)
        else:
            target.write_bytes(data)
            os.chmod(target, 0o755 if mode == "100755" else 0o644)
    try:
        yield [f":(exclude,literal){p}" for _, p in changes]
    finally:
        run(["git", "reset", "-q", "--hard", "HEAD"], wt)
        run(["git", "clean", "-fdq"], wt)


BASE_PASS = " (origin/main's checks)"


def passes(repo, base, wt: Path, changes: list[tuple[str, str]]):
    """(label, the outcome of a failure, status excludes) for each pass of the checks:
    with origin/main's copies of the check inputs; and, when the commit changes any,
    with the commit's own, which must pass, while a failure with origin/main's is noted
    for the security review (and refuses the commit, if it changes what the checks
    judge as well: keep_apart)."""
    if not changes:
        yield "", "FAIL", []
        return
    with base_copies(repo, base, wt, changes) as excludes:
        yield BASE_PASS, "note", excludes
    yield " (the commit's checks)", "FAIL", []


def hand_written_changed(repo, base, sha, path: str) -> bool:
    """For README.md and PROGRAM.md: does the change touch the text outside their
    markers, which is written by hand? (The other generated files are all render.py's.)"""
    pattern = GENERATED_REGIONS.get(path)
    if pattern is None:
        return False
    old, new = show(repo, base, path) or "", show(repo, sha, path) or ""
    return pattern.sub("", old) != pattern.sub("", new)


def judged_files(repo, base, sha) -> list[str]:
    """The files the commit changes that the checks judge: all but the check inputs and
    the other protected paths, the decisions page, and what render.py writes."""
    return sorted(p for _, p in changed_files(repo, base, sha)
                  if not under(p, CHECK_INPUTS + PROTECTED) and p != DECISIONS
                  and not (under(p, GENERATED) and not hand_written_changed(repo, base, sha, p)))


def keep_apart(repo, base, sha, rep: Report, stage: str) -> bool:
    """A check change is a pull request of its own, landed before the code it checks
    (docs/WORKFLOW.md, "Landing work: pull requests"). So when a check fails with
    origin/main's copies, the commit may change nothing the checks judge: a check
    weakened in the same pull request as the code it would catch is refused, not only
    noted. True when it refuses."""
    failed = [s.name.removesuffix(BASE_PASS) for s in rep.steps
              if s.stage == stage and s.outcome == "note" and s.name.endswith(BASE_PASS)]
    judged = judged_files(repo, base, sha) if failed else []
    if not judged:
        return False
    shown = ", ".join(judged[:8]) + (f" and {len(judged) - 8} more" if len(judged) > 8 else "")
    rep.add(stage, "check change kept apart", "FAIL",
            f"origin/main's checks fail on the commit ({', '.join(failed)}), and it changes "
            f"what they judge as well as the checks: {shown}. Land the check change first, in "
            "a pull request of its own (the checks, their expected values, the decisions "
            "entry and the regenerated pages), and the rest after it (docs/WORKFLOW.md, "
            "\"Landing work: pull requests\")")
    return True


class Guarded(NamedTuple):
    statements: list[str]       # changed with a brief or decision naming them
    protected: list[str]        # protected paths changed
    check_inputs: list[tuple[str, str]]   # check inputs changed: (status, path)


def guards(ctx, wt: Path, rep: Report, logs: Path) -> Guarded:
    repo, base, sha = ctx.repo, ctx.base, ctx.sha
    rep.heading(f"3. Invariant guards against origin/main, in {wt}")
    statements = guard_statements(repo, base, sha, wt, rep)
    guard_lock(repo, base, sha, rep)
    protected = guard_protected(repo, base, sha, rep)
    guard_heath(repo, base, sha, wt, rep)
    guard_directories(repo, base, sha, rep)
    inputs = [(s, p) for s, p in changed_files(repo, base, sha) if under(p, CHECK_INPUTS)]
    for label, fail, excludes in passes(repo, base, wt, inputs):
        guard_fidelity(wt, rep, logs, label, fail)
        guard_generated(wt, rep, logs, label, fail, excludes)
    keep_apart(repo, base, sha, rep, "3")
    guard_foundations(repo, base, sha, rep)
    failed = [s.name for s in rep.failed() if s.stage == "3"]
    if failed:
        raise Refusal(f"the invariant guards refused: {', '.join(failed)}")
    return Guarded(statements, protected, inputs)


# --------------------------------------------------------------------------------------
# Step 4: the full local checks, in disposable worktrees


@contextlib.contextmanager
def worktree(repo, sha, parent: Path, name: str):
    """A fresh detached worktree of the commit, removed afterwards, on a failure too."""
    path = parent / name
    git(repo, "worktree", "add", "--detach", "--quiet", str(path), sha)
    try:
        yield path
    finally:
        r = run(["git", "worktree", "remove", "--force", str(path)], repo)
        if r.returncode != 0:
            shutil.rmtree(path, ignore_errors=True)
            run(["git", "worktree", "prune"], repo)


def run_step(stage, name, cmd, cwd: Path, rep: Report, logs: Path, index: int,
             fail="FAIL", excludes=()) -> None:
    t = time.time()
    log = logs / f"{index:02d}{slug_of(name)}.log"
    if cmd is None:     # the generated pages are current
        r = status_lines(cwd, list(excludes))
        out, ok = r.stdout + r.stderr, r.returncode == 0 and not r.stdout.strip()
    else:
        r = run(cmd, cwd, env=tool_env())
        out, ok = (r.stdout or "") + (r.stderr or ""), r.returncode == 0
    log.write_text(out)
    seconds = time.time() - t
    if ok:
        rep.add(stage, name, "ok", "", seconds)
        return
    rep.add(stage, name, fail, f"full output in {log}\n{tail(out)}", seconds)
    if fail == "FAIL":
        raise Refusal(f"`{name}` failed on the commit")


def copy_build(src: Path, dst: Path) -> None:
    """Give the second worktree the first one's build of the same commit (a clone of the
    files on APFS); lake rebuilds whatever it finds out of date."""
    if not (src / ".lake").exists():
        return
    flags = ["-Rc"] if sys.platform == "darwin" else ["-R"]
    if run(["cp", *flags, str(src / ".lake"), str(dst / ".lake")], dst).returncode != 0:
        shutil.rmtree(dst / ".lake", ignore_errors=True)


def full_checks(ctx, wt: Path, parent: Path, inputs, rep: Report, logs: Path) -> None:
    for label, fail, excludes in passes(ctx.repo, ctx.base, wt, inputs):
        for i, (name, cmd) in enumerate(CHECKS, 1):
            run_step("4", name + label, cmd, wt, rep, logs, 10 + i, fail, excludes)
        if label == BASE_PASS and keep_apart(ctx.repo, ctx.base, ctx.sha, rep, "4"):
            raise Refusal("a check changed together with what it checks")
    with worktree(ctx.repo, ctx.sha, parent, "negative") as neg:
        copy_build(wt, neg)
        for label, fail, excludes in passes(ctx.repo, ctx.base, neg, inputs):
            for i, (name, cmd) in enumerate(NEGATIVE, 1):
                run_step("4", name + label, cmd, neg, rep, logs, 30 + i, fail, excludes)
            if label == BASE_PASS and keep_apart(ctx.repo, ctx.base, ctx.sha, rep, "4"):
                raise Refusal("a check changed together with what it checks")


class Preflight(NamedTuple):
    statements: list[str]
    protected: list[str]


def check_commit(ctx, rep: Report, logs: Path, test_mode: bool,
                 checked: dict | None = None) -> Preflight:
    """Steps 2 to 4 on the commit: the secret scan, the guards and the full checks.
    `checked`, a record of the full checks of this commit against this origin/main by
    origin/main's harness, stands in for step 4 alone (--merge); steps 2 and 3 always
    run."""
    secret_scan(ctx.repo, ctx.base, ctx.sha, rep, allow_rev=ctx.base)
    with tempfile.TemporaryDirectory(prefix="stoicheia-push-") as tmp:
        parent = Path(tmp)
        with worktree(ctx.repo, ctx.sha, parent, "check") as wt:
            g = guards(ctx, wt, rep, logs)
            rep.heading("4. The full local checks (docs/WORKFLOW.md, section 8)")
            if checked is not None:
                rep.add("4", "full local checks", "skip", f"run on {ctx.sha[:12]} against "
                        f"origin/main {ctx.base[:12]} by {checked.get('harness')}, "
                        f"{checked.get('time')}")
            elif test_mode:
                rep.add("4", "full local checks", "skip", "internal test flag, local origin")
            else:
                full_checks(ctx, wt, parent, g.check_inputs, rep, logs)
    return Preflight(g.statements, g.protected)


# --------------------------------------------------------------------------------------
# Step 1: preconditions, and the harness


class Context(NamedTuple):
    repo: Path
    sha: str
    base: str
    commits: int
    origin: str
    github: str | None       # "owner/repo" when origin is on GitHub
    tags: dict[str, str]     # origin's tags before the push
    branch: str | None = None
    gh: tuple = ("gh",)
    remote_branch: str | None = None    # the branch on origin before the push


def is_local(url: str) -> bool:
    if url.startswith("file://"):
        return True
    if re.match(r"^[A-Za-z][A-Za-z0-9+.-]*://", url) or re.match(r"^[^/]+@[^/:]+:", url):
        return False
    return Path(url).exists()


def github_slug(url: str) -> str | None:
    m = re.search(r"github\.com[:/]([^/]+)/([^/]+?)(?:\.git)?/?$", url)
    return f"{m.group(1)}/{m.group(2)}" if m else None


def remote_refs(repo, *args) -> dict[str, str]:
    out = git(repo, "ls-remote", "origin", *args)
    refs = {}
    for line in out.splitlines():
        sha, _, ref = line.partition("\t")
        refs[ref] = sha
    return refs


HOOK, LAUNCHER = "scripts/hooks/pre-push", "scripts/hooks/safe-push"


def installed_paths(repo) -> dict[str, Path]:
    """Where install_hooks.sh puts the pre-push hook and the launcher, outside the
    tracked tree, shared by every worktree of the clone."""
    out = git(repo, "rev-parse", "--git-path", "hooks", check=False).strip()
    hooks = Path(out) if os.path.isabs(out) else Path(repo) / out
    common = git(repo, "rev-parse", "--path-format=absolute", "--git-common-dir",
                 check=False).strip()
    return {HOOK: hooks / "pre-push", LAUNCHER: Path(common) / "stoicheia" / "safe-push"}


def check_installed(repo, base: str, rep: Report) -> None:
    """A note when the hook or the launcher is missing, or differs from origin/main's
    copy: code the pre-flight ran (a commit's checks, Lean at elaboration) could have
    rewritten either, and the marker alone would not show it."""
    for source, path in installed_paths(repo).items():
        name = "pre-push hook" if source == HOOK else "launcher (git safe-push)"
        try:
            data = path.read_bytes()
        except OSError:
            data = None
        theirs = show_bytes(repo, base, source)
        if data is None:
            rep.add("1", name, "note", "not installed here (sh scripts/install_hooks.sh)")
        elif theirs is not None and data != theirs:
            rep.add("1", name, "note", f"the installed copy differs from origin/main's "
                    f"{source}: install it again, from a checkout of origin/main "
                    "(sh scripts/install_hooks.sh --force)")


def harness_copy(theirs: bytes, theirs_heath: bytes) -> Path:
    """origin/main's safe_push.py and heath.py, written to a directory named by their
    blobs, beside the log (~/.cache/stoicheia/harness/<blob>-<blob>/): it needs no
    cleaning up, since the same harness always lands in the same place, and each file is
    written afresh, through a rename, so that nothing left there earlier is run."""
    path = log_path().parent / "harness" / f"{blob_id(theirs)}-{blob_id(theirs_heath)}"
    path.mkdir(parents=True, exist_ok=True)
    for name, data in (("safe_push.py", theirs), ("heath.py", theirs_heath)):
        fd, tmp = tempfile.mkstemp(prefix=f".{name}.", dir=path)
        with os.fdopen(fd, "wb") as f:
            f.write(data)
        os.replace(tmp, path / name)
    return path


def harness(repo, base: str, rep: Report) -> None:
    """origin/main's safe_push.py and heath.py judge the commit. When this copy differs
    from them, origin/main's replaces this process (os.execve), with the same arguments:
    its signals, its summary and its exit status are the run's own, so an interruption
    after its push is still "pushed; CI not followed". A copy of origin/main's that
    predates the marker is not run: this copy runs, once, while the harness that runs
    from origin/main lands. STOICHEIA_HARNESS, which the hand-over sets, is believed only
    when this file's bytes are origin/main's."""
    global HARNESS, HARNESS_BLOB
    here = Path(__file__).resolve().parent
    own, own_heath = (here / "safe_push.py").read_bytes(), (here / "heath.py").read_bytes()
    theirs = show_bytes(repo, base, "scripts/safe_push.py")
    theirs_heath = show_bytes(repo, base, "scripts/heath.py")
    same = (theirs, theirs_heath) == (own, own_heath)
    if os.environ.get("STOICHEIA_HARNESS"):
        if not same:
            raise Refusal("STOICHEIA_HARNESS says this is origin/main's harness, but this "
                          "copy of scripts/safe_push.py or heath.py is not origin/main's "
                          f"(blob {blob_id(own)[:12]}): origin/main moved since the hand-over, "
                          "or the variable was set by hand. Run safe_push again, with the "
                          "variable unset.")
        HARNESS = f"origin/main's `scripts/safe_push.py` (blob `{blob_id(own)[:12]}`)"
        HARNESS_BLOB = blob_id(own)
        rep.add("1", "harness", "ok", f"origin/main's scripts/safe_push.py (blob "
                f"{blob_id(own)[:12]}), run in place of a copy that differs from it")
        return
    if theirs is None or theirs_heath is None or b"HARNESS_PROTOCOL" not in theirs:
        HARNESS = (f"this copy of `scripts/safe_push.py` (blob `{blob_id(own)[:12]}`), since "
                   "origin/main's predates running from origin/main")
        rep.add("1", "harness", "note", "origin/main's scripts/safe_push.py does not yet run "
                "from origin/main: this copy runs, while the change that makes it do so lands")
        return
    if same:
        HARNESS = f"origin/main's `scripts/safe_push.py` (blob `{blob_id(own)[:12]}`)"
        HARNESS_BLOB = blob_id(own)
        rep.add("1", "harness", "ok", f"origin/main's scripts/safe_push.py "
                f"(blob {blob_id(own)[:12]})")
        return
    print("  this copy of safe_push.py or heath.py differs from origin/main's: running "
          "origin/main's in its place", flush=True)
    path = harness_copy(theirs, theirs_heath) / "safe_push.py"
    env = dict(os.environ, STOICHEIA_HARNESS="origin/main")
    sys.stdout.flush()
    sys.stderr.flush()
    os.execve(PY, [PY, str(path), *ARGV], env)


def gh_command(test_mode: bool) -> tuple:
    """gh, or, under the internal test flag, the stand-in the tests name; never the real
    gh under that flag."""
    if not test_mode:
        return ("gh",)
    stand_in = os.environ.get("STOICHEIA_TEST_GH")
    if not stand_in:
        raise Refusal("the internal test flag needs STOICHEIA_TEST_GH, a stand-in for gh")
    return (stand_in,)


def gh_ready(gh: tuple, repo, test_mode: bool) -> None:
    if not test_mode and shutil.which("gh") is None:
        raise Refusal("gh is not installed: the pull request needs it")
    r = run([*gh, "auth", "status", "--hostname", "github.com"], repo)
    if r.returncode != 0:
        raise Refusal("gh is not logged in to github.com (`gh auth login`)")


def fetch_base(repo, origin: str, test_mode: bool, rep: Report) -> str:
    if test_mode and not is_local(origin):
        raise Refusal("the internal test flag works only against a local origin")
    t = time.time()
    r = run(["git", "fetch", "origin"], repo)
    if r.returncode != 0:
        raise Refusal(f"`git fetch origin` failed: {r.stderr.strip()}")
    rep.add("1", "fetch", "ok", f"git fetch origin ({origin})", time.time() - t)
    base = rev_parse(repo, "refs/remotes/origin/main^{commit}")
    if base is None:
        raise Refusal("origin has no main branch")
    return base


def check_branch_name(repo, branch: str) -> None:
    name = branch.removeprefix("refs/heads/")
    if name.lower() in ("main", "head") or branch.startswith("refs/") and \
            not branch.startswith("refs/heads/"):
        raise Refusal(f"refusing --branch {branch}: main changes only by a pull request's "
                      "merge commit; name a branch of its own")
    if name.startswith("refs/") or name.startswith("-") or \
            not git_ok(repo, "check-ref-format", "--branch", name):
        raise Refusal(f"refusing --branch {branch}: not a branch name git accepts")


def preconditions(repo: Path, commit: str, branch: str | None, dry_run: bool,
                  test_mode: bool, rep: Report, title: str | None = None) -> Context:
    rep.heading("1. Preconditions")
    if branch:
        check_branch_name(repo, branch)
        branch = branch.removeprefix("refs/heads/")
    r = run(["git", "rev-parse", "--verify", "--quiet", f"{commit}^{{commit}}"], repo)
    if r.returncode != 0:
        raise Refusal(f"{commit!r} is not a commit in {repo}")
    sha = r.stdout.strip()
    subject = git(repo, "log", "-1", "--format=%s", sha).strip()
    rep.add("1", "commit", "ok", f"{sha[:12]} \"{subject}\" (read from git, not from the "
            "working tree)")
    origin = git(repo, "remote", "get-url", "origin", check=False).strip()
    if not origin:
        raise Refusal("this repository has no remote called origin")
    base = fetch_base(repo, origin, test_mode, rep)
    harness(repo, base, rep)
    if branch or title:
        check_public_names(branch, title)
        rep.add("1", "public names", "ok", "nothing the scan refuses in "
                + " or ".join(n for n, v in (("the branch name", branch), ("the title", title))
                              if v))
    if base == sha:
        rep.add("1", "fast-forward", "ok", f"origin/main is already {sha[:12]}")
        raise NothingToPush(sha)
    if not git_ok(repo, "merge-base", "--is-ancestor", base, sha):
        rep.add("1", "fast-forward", "FAIL", f"origin/main {base[:12]} is not an ancestor of "
                f"{sha[:12]}")
        raise Refusal(f"not a fast-forward: origin/main ({base[:12]}) is not an ancestor of "
                      f"{sha[:12]}. Merge origin/main into the branch first (a merge commit), "
                      "so that the merge holds exactly the tree checked; nothing is forced.")
    commits = int(git(repo, "rev-list", "--count", f"{base}..{sha}").strip())
    rep.add("1", "fast-forward", "ok", f"origin/main {base[:12]} is an ancestor: "
            f"{plural(commits, 'commit')} to propose")
    remote_branch = None
    if branch:
        remote_branch = remote_refs(repo, f"refs/heads/{branch}").get(f"refs/heads/{branch}")
        if remote_branch is None:
            rep.add("1", "branch", "ok", f"{branch}: new on origin")
        elif remote_branch == sha:
            rep.add("1", "branch", "ok", f"{branch}: already at {sha[:12]} on origin")
        elif rev_parse(repo, f"{remote_branch}^{{commit}}") is None or \
                not git_ok(repo, "merge-base", "--is-ancestor", remote_branch, sha):
            rep.add("1", "branch", "FAIL", f"origin's {branch} ({remote_branch[:12]}) is not "
                    f"an ancestor of {sha[:12]}")
            raise Refusal(f"origin's {branch} has commits {sha[:12]} lacks: merge them in (a "
                          "merge commit; review records stamp the branch's commits), or use "
                          "another branch name. Nothing is forced.")
        else:
            rep.add("1", "branch", "ok", f"{branch}: a fast-forward from {remote_branch[:12]}")
    rep.add("1", "tags and releases", "ok", "none is made: tags, releases and their notes "
            "stay manual, with the owner's OK")
    slug = "test/stoicheia" if test_mode else github_slug(origin)
    if not test_mode and shutil.which("lake", path=tool_env()["PATH"]) is None:
        raise Refusal("lake is not on the PATH, nor in ~/.elan/bin: the full checks need it")
    tags: dict[str, str] = {}
    gh: tuple = ("gh",)
    if branch and not dry_run:
        if not slug:
            raise Refusal(f"origin ({origin}) is not on GitHub: no pull request can be opened")
        gh = gh_command(test_mode)
        gh_ready(gh, repo, test_mode)
        tags = remote_refs(repo, "--tags")
    check_installed(repo, base, rep)
    return Context(repo, sha, base, commits, origin, slug, tags, branch, gh, remote_branch)


# --------------------------------------------------------------------------------------
# Step 5: the push of the branch, the pull request, and its CI


def push_branch(ctx: Context, rep: Report) -> None:
    rep.heading("5. Push")
    now = remote_refs(ctx.repo, "refs/heads/main").get("refs/heads/main")
    if now != ctx.base:
        raise Refusal(f"origin/main moved from {ctx.base[:12]} to {str(now)[:12]} during the "
                      "checks: run safe_push again, against the new main")
    ref = f"refs/heads/{ctx.branch}"
    remote = remote_refs(ctx.repo, ref).get(ref)
    if remote == ctx.sha:
        rep.add("5", "git push", "ok", f"origin's {ctx.branch} is already {ctx.sha[:12]}")
        return
    if remote != ctx.remote_branch:
        raise Refusal(f"origin's {ctx.branch} moved during the checks: run safe_push again")
    t = time.time()
    r = run(["git", "push", "--no-follow-tags", "--porcelain", "origin", f"{ctx.sha}:{ref}"],
            ctx.repo)
    if r.returncode != 0:
        rep.add("5", "git push", "FAIL", (r.stdout + r.stderr).strip(), time.time() - t)
        raise Refusal("git push failed; nothing was forced")
    after = remote_refs(ctx.repo, ref).get(ref)
    if after != ctx.sha:
        rep.add("5", "git push", "FAIL", f"origin's {ctx.branch} is {after}, not {ctx.sha}")
        raise Refusal(f"the push did not leave origin's {ctx.branch} at the commit")
    rep.add("5", "git push", "ok", f"origin's {ctx.branch} "
            f"{(ctx.remote_branch or 'new')[:12]} -> {ctx.sha[:12]}, never forced",
            time.time() - t)
    tags = remote_refs(ctx.repo, "--tags")
    if tags != ctx.tags:
        new = sorted(set(tags) - set(ctx.tags))
        rep.add("5", "tags", "FAIL", f"origin's tags changed during the push: {new}")
    else:
        rep.add("5", "tags", "ok", "origin's tags unchanged")


def gh_run(ctx: Context, *args) -> subprocess.CompletedProcess:
    return run([*ctx.gh, *args, "-R", ctx.github], ctx.repo)


def gh_json(ctx: Context, *args):
    r = gh_run(ctx, *args)
    if r.returncode != 0 and not r.stdout.strip():
        raise Refusal(f"`gh {' '.join(args)}` failed: {(r.stderr or r.stdout).strip()}")
    try:
        return json.loads(r.stdout or "null")
    except json.JSONDecodeError:
        raise Refusal(f"`gh {' '.join(args)}` did not print JSON: {r.stdout.strip()[:200]}")


def ensure_labels(ctx: Context, labels) -> None:
    present = {item.get("name") for item in
               gh_json(ctx, "label", "list", "--json", "name", "--limit", "500") or []}
    for name in sorted(set(labels) - present):
        r = gh_run(ctx, "label", "create", name, "--description", LABELS.get(name, ""),
                   "--color", "b60205" if name == SECURITY_LABEL else "c5def5")
        if r.returncode != 0:
            raise Refusal(f"could not create the label {name}: {r.stderr.strip()}")


# The pre-flight's summary sits between these markers in the body, and is replaced there.
BLOCK = re.compile(r"<!-- safe_push:preflight begin(?: sha=(\w+) base=(\w+))? -->.*?"
                   r"<!-- safe_push:preflight end -->", re.S)
PLACEHOLDER = re.compile(r"<!-- safe_push: (\w+) -->")
STAMP_FIELD = re.compile(r'(?m)^(fingerprint|commit|lean)\s*=\s*"([^"]*)"')


def sanitized(text: str) -> str:
    """A line for the public body: the home directory written as ~."""
    return text.replace(str(Path.home()), "~")


def preflight_block(sha: str, base: str, record: dict) -> str:
    lines = [f"<!-- safe_push:preflight begin sha={sha} base={base} -->",
             f"Pre-flight of `{sha[:12]}` against origin/main `{base[:12]}`, "
             f"{record.get('time', '')}, by {record.get('harness', 'safe_push.py')}"
             + ("; the full checks skipped (the internal test flag)"
                if not record.get("full") else "") + ".",
             "",
             "| Step | Outcome | Seconds |",
             "|---|---|---|"]
    for stage, name, outcome, seconds in record.get("steps", []):
        took = f"{seconds:.1f}" if seconds is not None else ""
        lines.append(f"| {stage}. {name} | {outcome} | {took} |")
    notes = record.get("notes", [])
    if notes:
        lines += ["", "Noted by the pre-flight:"]
        lines += [f"- {sanitized(name)}: {sanitized(first)}" for name, first in notes]
    if record.get("protected"):
        lines += ["", f"Protected paths changed: {', '.join(f'`{p}`' for p in record['protected'])}"
                  f"; label `{SECURITY_LABEL}`; /security-review required."]
    lines.append("<!-- safe_push:preflight end -->")
    return "\n".join(lines)


def put_block(body: str, block: str) -> str:
    """The body with the pre-flight's summary in place: between its markers, at the
    template's placeholder, or appended."""
    if BLOCK.search(body):
        return BLOCK.sub(lambda m: block, body, count=1)
    if "<!-- safe_push: preflight -->" in body:
        return body.replace("<!-- safe_push: preflight -->", block, 1)
    return body.rstrip() + "\n\n## Checks run on the exact commit\n\n" + block + "\n"


def generated_changed(repo, base, sha, path: str) -> bool:
    """Does the change touch what render.py writes in `path`? For README.md and
    PROGRAM.md, only the text between their markers; a hand edit elsewhere in them is
    not a generated change."""
    pattern = GENERATED_REGIONS.get(path)
    if pattern is None:
        return True
    old, new = show(repo, base, path) or "", show(repo, sha, path) or ""
    return [m.group(0) for m in pattern.finditer(old)] != \
        [m.group(0) for m in pattern.finditer(new)]


def describe(ctx: Context, pre: Preflight) -> dict[str, str]:
    """The parts of the body the pre-flight knows: commits, statements, records,
    generated files, protected paths."""
    repo, base, sha = ctx.repo, ctx.base, ctx.sha
    log = git(repo, "log", "--reverse", "--format=- `%h` %s", f"{base}..{sha}").strip()
    records = []
    for status, path in changed_files(repo, base, sha, "review"):
        if not re.fullmatch(r"review/[IVX]+/\d+\.toml", path):
            continue
        old = dict(STAMP_FIELD.findall(show(repo, base, path) or ""))
        new = dict(STAMP_FIELD.findall(show(repo, sha, path) or ""))
        if status == "D":
            records.append(f"- `{path}`: deleted")
        elif old != new and new.get("commit"):
            records.append(f"- `{path}`: re-stamped at `{new['commit'][:12]}`")
        else:
            records.append(f"- `{path}`: touched, not re-stamped")
    generated = [p for _, p in changed_files(repo, base, sha) if under(p, GENERATED)
                 and generated_changed(repo, base, sha, p)]
    gen_dirs = sorted({p.split("/")[0] + "/" if p.startswith("book/") else p for p in generated})
    return {
        "commits": f"<!-- safe_push:commits begin -->\nCommits (`{base[:12]}..{sha[:12]}`):"
                   f"\n\n{log}\n<!-- safe_push:commits end -->",
        "statements": "\n".join(f"- {s}" for s in pre.statements) or "None.",
        "records": "\n".join(records) or "None.",
        "generated": ("Changed: " + ", ".join(f"`{p}`" for p in gen_dirs)) if gen_dirs
                     else "None.",
        "protected": (", ".join(f"`{p}`" for p in pre.protected)
                      + f": the label `{SECURITY_LABEL}`, and /security-review before merge."
                      if pre.protected else "None."),
    }


def fallback_template() -> str:
    return ("## What and why\n\n<!-- safe_push: commits -->\n\n"
            "## Checks run on the exact commit\n\n<!-- safe_push: preflight -->\n")


def fill_body(ctx: Context, pre: Preflight, record: dict, text: str) -> str:
    """A body with the template's `safe_push` placeholders filled, and the pre-flight's
    summary in place."""
    parts = describe(ctx, pre)
    body = PLACEHOLDER.sub(lambda m: parts.get(m.group(1), m.group(0))
                           if m.group(1) != "preflight" else m.group(0), text)
    return put_block(body, preflight_block(ctx.sha, ctx.base, record))


def generated_body(ctx: Context, pre: Preflight, record: dict) -> str:
    """The body from origin/main's template (the commit's, while origin/main has none)."""
    template = show(ctx.repo, ctx.base, TEMPLATE) or show(ctx.repo, ctx.sha, TEMPLATE) \
        or fallback_template()
    return fill_body(ctx, pre, record, template)


def check_body(body: str) -> None:
    """The body is public: it is scanned before it is posted."""
    found = scan_block("the pull request's body", list(enumerate(body.splitlines(), 1)))
    if found:
        raise Refusal("the pull request's body holds what the secret scan refuses: "
                      + "; ".join(f.shown() for f in found))


def check_public_names(branch: str | None, title: str | None) -> None:
    """The branch name is pushed as a public ref, and the title is posted: each is
    scanned, with no allow-list, before anything is pushed."""
    found = []
    if title:
        found += scan_text("the title", None, title)
    if branch:
        found += scan_text("the branch name", None, branch)
    if found:
        raise Refusal("a public name holds what the secret scan refuses: "
                      + "; ".join(f.shown() for f in found))


class PR(NamedTuple):
    number: int
    url: str
    created: bool


class PRPlan(NamedTuple):
    """The pull request as it will be: the open one of ours to update, if any, and its
    body, labels and title, all known and checked before the push."""
    existing: dict | None
    body: str
    labels: set
    title: str


def own_prs(ctx: Context, prs: list[dict]) -> list[dict]:
    """The pull requests whose head is a branch of origin itself. `gh pr list --head`
    matches on the branch's name alone, so it finds a fork's pull request of the same
    name too; and on a public repository anyone can open one in advance."""
    owner = (ctx.github or "").split("/")[0].lower()
    mine = []
    for p in prs:
        if p.get("isCrossRepository") is not False:
            continue
        login = str((p.get("headRepositoryOwner") or {}).get("login") or owner).lower()
        if login == owner and p.get("headRefName", ctx.branch) == ctx.branch:
            mine.append(p)
    return mine


def plan_pr(ctx: Context, pre: Preflight, record: dict, args) -> PRPlan:
    """Everything the pull request will carry, settled before the push: our open pull
    request for the branch (never a fork's of the same name), and the body, scanned. A
    new pull request's body, or --body-file, is known in full; an open one's is fetched."""
    labels = set(args.label) | ({SECURITY_LABEL} if pre.protected else set())
    listed = gh_json(ctx, "pr", "list", "--head", ctx.branch, "--base", "main", "--state",
                     "open", "--json", "number,url,isDraft,labels,isCrossRepository,"
                     "headRepositoryOwner,headRefName") or []
    mine = own_prs(ctx, listed)
    existing = mine[0] if mine else None
    have = labels | {item.get("name") for item in (existing or {}).get("labels") or []}
    if not have & set(KIND_LABELS):
        raise Refusal("the pull request needs a label for its kind, one of "
                      f"{', '.join(KIND_LABELS)}: --label <kind> (docs/WORKFLOW.md, "
                      "\"Landing work: pull requests\")")
    if args.body_file:
        body = fill_body(ctx, pre, record, Path(args.body_file).read_text())
    elif existing:
        view = gh_json(ctx, "pr", "view", str(existing["number"]), "--json", "body")
        body = put_block(view.get("body") or "", preflight_block(ctx.sha, ctx.base, record))
    else:
        body = generated_body(ctx, pre, record)
    check_body(body)
    title = args.title or git(ctx.repo, "log", "-1", "--format=%s", ctx.sha).strip()
    return PRPlan(existing, body, labels, title)


def open_pr(ctx: Context, plan: PRPlan, args, rep: Report, logs: Path) -> PR:
    rep.heading("6. Pull request")
    t = time.time()
    labels, existing = plan.labels, plan.existing
    ensure_labels(ctx, labels)
    body_path = logs / "pr-body.md"
    body_path.write_text(plan.body)
    if existing:
        pr = PR(int(existing["number"]), existing.get("url", ""), False)
        edit = ["pr", "edit", str(pr.number), "--body-file", str(body_path)]
        if args.title:
            edit += ["--title", args.title]
        for label in sorted(labels):
            edit += ["--add-label", label]
        r = gh_run(ctx, *edit)
        if r.returncode != 0:
            raise Refusal(f"`gh pr edit` failed: {r.stderr.strip()}")
        if args.ready and existing.get("isDraft"):
            r = gh_run(ctx, "pr", "ready", str(pr.number))
            if r.returncode != 0:
                raise Refusal(f"`gh pr ready` failed: {r.stderr.strip()}")
    else:
        create = ["pr", "create", "--base", "main", "--head", ctx.branch, "--title",
                  plan.title, "--body-file", str(body_path)]
        if not args.ready:
            create.append("--draft")
        for label in sorted(labels):
            create += ["--label", label]
        r = gh_run(ctx, *create)
        if r.returncode != 0:
            raise Refusal(f"`gh pr create` failed: {r.stderr.strip()}")
        url = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else ""
        m = re.search(r"/pull/(\d+)", url)
        if not m:
            raise Refusal(f"`gh pr create` printed no pull request URL: {r.stdout.strip()}")
        pr = PR(int(m.group(1)), url, True)
    # GitHub may take a moment to see the branch's new head.
    deadline = time.time() + HEAD_TIMEOUT
    while True:
        view = gh_json(ctx, "pr", "view", str(pr.number), "--json",
                       "headRefOid,baseRefName,isCrossRepository,url")
        if view.get("headRefOid") == ctx.sha or time.time() > deadline:
            break
        time.sleep(3)
    if view.get("headRefOid") != ctx.sha or view.get("baseRefName") != "main" \
            or view.get("isCrossRepository"):
        rep.add("6", "pull request", "FAIL", f"#{pr.number}'s head is "
                f"{str(view.get('headRefOid'))[:12]}, base {view.get('baseRefName')}, not "
                f"{ctx.sha[:12]} onto main", time.time() - t)
        raise Refusal(f"pull request #{pr.number} does not propose the commit checked")
    pr = pr._replace(url=view.get("url") or pr.url)
    rep.add("6", "pull request", "ok", f"#{pr.number} {'opened' if pr.created else 'updated'}"
            f"{' as a draft' if pr.created and not args.ready else ''}: {pr.url}"
            + (f"; labels {', '.join(sorted(labels))}" if labels else ""), time.time() - t)
    return pr


def judge_checks(checks: list[dict]) -> tuple[str, str]:
    """("success", …) when check, model and negative pass and nothing fails or waits."""
    buckets: dict[str, list[str]] = {}
    for c in checks:
        buckets.setdefault(str(c.get("name")), []).append(str(c.get("bucket")))
    failing = sorted(n for n, b in buckets.items() if {"fail", "cancel"} & set(b))
    pending = sorted(n for n, b in buckets.items() if "pending" in b)
    missing = [n for n in REQUIRED_CHECKS if "pass" not in buckets.get(n, [])]
    shown = ", ".join(f"{n} {'/'.join(sorted(set(b)))}" for n, b in sorted(buckets.items()))
    if failing:
        return "failure", f"failing: {', '.join(failing)} ({shown})"
    if pending:
        return "pending", f"still running: {', '.join(pending)} ({shown})"
    if missing:
        return "missing", f"no passing run of {', '.join(missing)} ({shown or 'no checks'})"
    return "success", shown


def pr_checks(ctx: Context, number: int) -> list[dict]:
    r = gh_run(ctx, "pr", "checks", str(number), "--json", "name,bucket,state,workflow")
    try:
        return json.loads(r.stdout or "[]") or []
    except json.JSONDecodeError:
        return []


def watch_checks(ctx: Context, pr: PR, rep: Report) -> str:
    """Wait for the pull request's checks on the commit and follow them; return the
    verdict."""
    rep.heading("CI")
    t = time.time()
    checks: list[dict] = []
    while time.time() - t < CI_APPEAR_TIMEOUT:
        checks = pr_checks(ctx, pr.number)
        if checks:
            break
        time.sleep(CI_POLL)
    if not checks:
        rep.add("6", "CI", "FAIL", f"no checks appeared for #{pr.number} in "
                f"{CI_APPEAR_TIMEOUT} s: `gh pr checks {pr.number}`")
        return "unknown"
    print(f"  following the checks of #{pr.number}: {pr.url}", flush=True)
    subprocess.run([*ctx.gh, "pr", "checks", str(pr.number), "--watch", "--interval",
                    CI_WATCH_INTERVAL, "-R", ctx.github], cwd=ctx.repo)
    verdict, detail = judge_checks(pr_checks(ctx, pr.number))
    rep.add("6", "CI", "ok" if verdict == "success" else "FAIL", f"{verdict}: {detail}",
            time.time() - t)
    return verdict


# --------------------------------------------------------------------------------------
# The pre-flight's record, for --merge


def log_path() -> Path:
    env = os.environ.get("STOICHEIA_PUSH_LOG")
    return Path(env) if env else Path.home() / ".cache" / "stoicheia" / "pushes.log"


def record_path(sha: str, base: str) -> Path:
    return log_path().parent / "preflight" / f"{sha}-{base}.json"


def make_record(ctx: Context, pre: Preflight, rep: Report, full: bool,
                checked: dict | None = None) -> dict:
    """The pre-flight's record. `checked`, the earlier record whose full checks stood in
    for step 4 (--merge), gives its step 4 and its notes."""
    steps = [[s.stage, s.name, s.outcome, s.seconds] for s in rep.steps
             if s.outcome in ("ok", "FAIL", "skip") and s.stage in ("2", "3", "4")]
    notes = [[s.name, (s.detail.splitlines() or [""])[0]] for s in rep.steps
             if s.outcome == "note"]
    if checked is not None:
        steps = [s for s in steps if s[0] != "4"] + \
            [list(s) for s in checked.get("steps", []) if s and s[0] == "4"]
        notes += [list(n) for n in checked.get("notes", []) if list(n) not in notes]
    return {
        "sha": ctx.sha, "base": ctx.base, "branch": ctx.branch,
        "full": full or bool(checked and checked.get("full")),
        "time": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
        "harness": HARNESS, "harness_blob": HARNESS_BLOB,
        "steps": steps, "notes": notes,
        "protected": pre.protected, "statements": pre.statements,
    }


def checks_record(record: dict | None, test_mode: bool) -> dict | None:
    """The record, if its full checks may stand in for step 4 at the merge: they were run
    (or skipped by the internal test flag, under it) by origin/main's harness, the one
    running now. The record is a local file anything run as the user could write, so it
    never stands in for the secret scan or the guards, and CI runs the same checks."""
    if record is None or HARNESS_BLOB is None:
        return None
    if record.get("harness_blob") != HARNESS_BLOB or not (record.get("full") or test_mode):
        return None
    return record


def save_record(record: dict) -> None:
    path = record_path(record["sha"], record["base"])
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(record, indent=1) + "\n")


def load_record(sha: str, base: str) -> dict | None:
    try:
        record = json.loads(record_path(sha, base).read_text())
    except (OSError, json.JSONDecodeError):
        return None
    return record if record.get("sha") == sha and record.get("base") == base else None


# --------------------------------------------------------------------------------------
# --merge: the gates, then a merge commit


BOX = re.compile(r"(?m)^\s*[-*]\s+\[([ xX])\]\s+\*\*(Required(?: if protected)?):\*\*\s*(.*?)\s*$")


def boxes(body: str) -> list[tuple[bool, str, str]]:
    """(ticked, kind, text) for each required box of a checklist."""
    return [(m.group(1) != " ", m.group(2), " ".join(m.group(3).split()))
            for m in BOX.finditer(body or "")]


def checklist_problems(body: str, template: str | None, protected: bool) -> list[str]:
    def needed(kind):
        return kind == "Required" or protected

    have = boxes(body)
    wanted = [(k, x) for _, k, x in boxes(template or "") if needed(k)]
    if not have and not wanted:
        return ["the body has no checklist of required boxes: use "
                f"{TEMPLATE}"]
    problems = [f"unticked: {k}: {x}" for ticked, k, x in have if needed(k) and not ticked]
    present = {(k, x) for _, k, x in have}
    problems += [f"missing from the body: {k}: {x}" for k, x in wanted if (k, x) not in present]
    return problems


SECTION = re.compile(r"(?m)^## +(.+?) *$")
# The sections the coordinator writes, which --merge needs written when the template has them.
WRITTEN = ("What and why", "Reviews", "Needs the owner's OK")
OWN_PART = re.compile(r"<!-- safe_push:(\w+) begin\b.*?<!-- safe_push:\1 end -->", re.S)


def sections(body: str) -> dict[str, str]:
    parts = SECTION.split(body or "")
    return {parts[i].strip(): parts[i + 1] for i in range(1, len(parts) - 1, 2)}


def own_words(text: str) -> str:
    """A section's words, without its comments and without what safe_push wrote."""
    return COMMENT.sub("", OWN_PART.sub("", text)).strip()


def review_rows(text: str) -> dict[str, list[str]]:
    """{review: its cells after the first} for each row of a Reviews table."""
    rows = {}
    for line in text.splitlines():
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if line.strip().startswith("|") and cells[0].startswith("/"):
            rows[cells[0]] = cells[1:]
    return rows


def section_problems(body: str, template: str | None, protected: bool) -> list[str]:
    """What the coordinator has still to write: "What and why", each review's commit and
    findings (the security review's only when a protected path changes), and "Needs the
    owner's OK"."""
    wanted, have = sections(template or ""), sections(body)
    problems = []
    for name in (n for n in WRITTEN if n in wanted):
        if name not in have:
            problems.append(f"missing from the body: the section \"{name}\"")
        elif name == "Reviews":
            rows = review_rows(have[name])
            for review in review_rows(wanted[name]):
                cells = rows.get(review, [])
                if (review != "/security-review" or protected) and not (
                        len(cells) >= 2 and all(cells[:2])):
                    problems.append(f"not written: the review {review}, its commit and its "
                                    "findings")
        elif not own_words(have[name]):
            problems.append(f"not written: the section \"{name}\"")
    return problems


def protected_files(repo, base, sha) -> list[str]:
    return sorted({p for _, p in changed_files(repo, base, sha) if is_protected(p)})


def merge_preconditions(repo: Path, number: int, test_mode: bool, rep: Report):
    rep.heading("1. Preconditions")
    origin = git(repo, "remote", "get-url", "origin", check=False).strip()
    if not origin:
        raise Refusal("this repository has no remote called origin")
    base = fetch_base(repo, origin, test_mode, rep)
    harness(repo, base, rep)
    slug = "test/stoicheia" if test_mode else github_slug(origin)
    if not slug:
        raise Refusal(f"origin ({origin}) is not on GitHub: there is no pull request to merge")
    gh = gh_command(test_mode)
    gh_ready(gh, repo, test_mode)
    ctx = Context(repo, "", base, 0, origin, slug, {}, None, gh)
    view = gh_json(ctx, "pr", "view", str(number), "--json",
                   "number,state,isDraft,headRefName,headRefOid,baseRefName,body,labels,url,"
                   "isCrossRepository,title")
    if not view or view.get("state") != "OPEN":
        raise Refusal(f"pull request #{number} is not open ({(view or {}).get('state')})")
    if view.get("baseRefName") != "main" or view.get("isCrossRepository"):
        raise Refusal(f"pull request #{number} does not propose a branch of origin onto main")
    head, branch = view.get("headRefOid", ""), view.get("headRefName", "")
    if branch.lower() == "main":
        raise Refusal(f"pull request #{number}'s head is main")
    if rev_parse(repo, f"{head}^{{commit}}") is None:
        run(["git", "fetch", "origin", f"refs/heads/{branch}"], repo)
    if rev_parse(repo, f"{head}^{{commit}}") is None:
        raise Refusal(f"the head {head[:12]} of #{number} is not here after `git fetch origin`")
    if not git_ok(repo, "merge-base", "--is-ancestor", base, head):
        raise Refusal(f"origin/main ({base[:12]}) is not an ancestor of #{number}'s head "
                      f"({head[:12]}): merge origin/main into {branch} (a merge commit), run "
                      f"the pre-flight again (--branch {branch}), then --merge")
    commits = int(git(repo, "rev-list", "--count", f"{base}..{head}").strip())
    rep.add("1", "pull request", "ok", f"#{number} \"{view.get('title')}\": {branch} at "
            f"{head[:12]}, {plural(commits, 'commit')} onto origin/main {base[:12]}")
    check_installed(repo, base, rep)
    return ctx._replace(sha=head, commits=commits, branch=branch), view


def gates(ctx: Context, number: int, rep: Report, record: dict | None = None) -> dict:
    """Not a draft; every required box ticked; the coordinator's sections written; a
    label for its kind, and security-review when a protected path changes; CI green on
    the head. Each is reported; any failure refuses the merge. The record's notes are
    shown beside the checklist: a check that failed with origin/main's copies, on a
    commit that changes nothing the checks judge (keep_apart refuses the rest), is for
    the security review to weigh."""
    rep.heading("2. The gates")
    view = gh_json(ctx, "pr", "view", str(number), "--json",
                   "isDraft,headRefOid,body,labels,state")
    if view.get("headRefOid") != ctx.sha or view.get("state") != "OPEN":
        raise Refusal(f"#{number} changed meanwhile (head {str(view.get('headRefOid'))[:12]}, "
                      f"{view.get('state')}): run --merge again")
    protected = protected_files(ctx.repo, ctx.base, ctx.sha)
    if view.get("isDraft"):
        rep.add("G", "draft", "FAIL", f"#{number} is a draft: when it is ready, "
                f"`gh pr ready {number}`")
    else:
        rep.add("G", "draft", "ok", "ready for review")
    body, template = view.get("body") or "", show(ctx.repo, ctx.base, TEMPLATE)
    problems = checklist_problems(body, template, bool(protected))
    if problems:
        rep.add("G", "checklist", "FAIL", "\n".join(problems))
    else:
        rep.add("G", "checklist", "ok", "every required box ticked")
    unwritten = section_problems(body, template, bool(protected))
    if unwritten:
        rep.add("G", "sections", "FAIL", "\n".join(unwritten))
    else:
        rep.add("G", "sections", "ok", "what and why, the reviews and the owner's OK written")
    notes = [n for n in (record or {}).get("notes", []) if len(n) == 2 and n[0] != "pre-flight"]
    if notes:
        rep.add("G", "pre-flight notes", "note", f"{plural(len(notes), 'note')} of the "
                "pre-flight, for the reviews:\n" + "\n".join(f"{n}: {d}" for n, d in notes))
    labels = {item.get("name") for item in view.get("labels") or []}
    if protected and SECURITY_LABEL not in labels:
        rep.add("G", "label", "FAIL", f"protected paths change ({', '.join(protected)}), and "
                f"#{number} lacks the label {SECURITY_LABEL}")
    elif protected:
        rep.add("G", "label", "ok", f"{SECURITY_LABEL}, for {', '.join(protected)}")
    kinds = sorted(labels & set(KIND_LABELS))
    rep.add("G", "kind label", "ok" if kinds else "FAIL", ", ".join(kinds) if kinds else
            f"#{number} has no label for its kind: one of {', '.join(KIND_LABELS)}")
    verdict, detail = judge_checks(pr_checks(ctx, number))
    rep.add("G", "CI", "ok" if verdict == "success" else "FAIL",
            f"{verdict} on {ctx.sha[:12]}: {detail}")
    failed = [s.name for s in rep.failed() if s.stage == "G"]
    if failed:
        raise Refusal(f"the merge gates refused: {', '.join(failed)}")
    return view


def revert_advice(ctx: Context) -> str:
    """How to undo a merge commit `ctx.sha`, through a pull request of its own."""
    branch = f"revert-{ctx.sha[:12]}"
    return "\n".join([
        "Nothing has been reverted. To undo the merge, in a pull request of its own:",
        f"    git switch -c {branch} origin/main",
        f"    git revert --no-edit -m 1 {ctx.sha}",
        f"    git safe-push --branch {branch}"])


def merge(ctx: Context, number: int, rep: Report) -> None:
    rep.heading("4. Merge")
    now = remote_refs(ctx.repo, "refs/heads/main").get("refs/heads/main")
    if now != ctx.base:
        raise Refusal(f"origin/main moved from {ctx.base[:12]} to {str(now)[:12]}: run "
                      "--merge again")
    t = time.time()
    r = gh_run(ctx, "pr", "merge", str(number), "--merge", "--delete-branch",
               "--match-head-commit", ctx.sha)
    if r.returncode != 0:
        rep.add("4", "gh pr merge", "FAIL", (r.stdout + r.stderr).strip(), time.time() - t)
        raise Refusal("`gh pr merge` refused; nothing was merged")
    rep.add("4", "gh pr merge", "ok", f"#{number} merged with a merge commit", time.time() - t)


def verify_merge(ctx: Context, rep: Report) -> str:
    """main is a merge commit of the base checked and the head checked, with the head's
    tree; the branch is gone. Returns the merge commit."""
    run(["git", "fetch", "origin"], ctx.repo)
    main = rev_parse(ctx.repo, "refs/remotes/origin/main^{commit}") or ""
    parents = git(ctx.repo, "rev-list", "--parents", "-n", "1", main).split()[1:] if main else []
    same_tree = main and rev_parse(ctx.repo, f"{main}^{{tree}}") == \
        rev_parse(ctx.repo, f"{ctx.sha}^{{tree}}")
    if parents == [ctx.base, ctx.sha] and same_tree:
        rep.add("5", "main", "ok", f"origin/main {main[:12]}: a merge commit of {ctx.base[:12]} "
                f"and {ctx.sha[:12]}, with the tree checked")
    else:
        rep.add("5", "main", "FAIL", f"origin/main {main[:12]} has parents "
                f"{', '.join(p[:12] for p in parents)}, and "
                f"{'the' if same_tree else 'not the'} tree checked")
    gone = not remote_refs(ctx.repo, f"refs/heads/{ctx.branch}")
    rep.add("5", "branch", "ok" if gone else "note",
            f"{ctx.branch} deleted on origin" if gone else f"{ctx.branch} is still on origin")
    return main


# --------------------------------------------------------------------------------------
# Step 6: the summary and the log outside the repository


def summary(rep: Report, mode: str, sha: str, base: str, result: str, ci: str) -> None:
    total = time.time() - rep.started
    print(f"\nSummary: {mode} of {sha[:12] or '?'} against origin/main {base[:12] or '?'}: "
          f"{result}" + (f"; CI {ci}" if ci else "") + f" ({total:.0f} s)")
    timed = [s for s in rep.steps if s.outcome in ("ok", "FAIL", "skip")]
    width = max((len(s.name) for s in timed), default=10)
    for s in timed:
        took = f"{s.seconds:8.1f} s" if s.seconds is not None else " " * 10
        print(f"  {s.stage}  {s.outcome:4}  {s.name:<{width}}  {took}")
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    steps = "; ".join(f"{s.name}={s.outcome}" + (f" {s.seconds:.1f}s" if s.seconds else "")
                      for s in timed)
    line = (f"{stamp} {mode} {sha[:12] or '?'} against {base[:12] or '?'}: {result}"
            + (f"; CI {ci}" if ci else "") + f"; {total:.0f}s; {steps}\n")
    path = log_path()
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a") as f:
            f.write(line)
        print(f"Logged to {path}")
    except OSError as e:
        print(f"Could not write the log {path}: {e}")


# --------------------------------------------------------------------------------------
# The three ways in: the pre-flight, the merge, and the hook's scan


def _terminate(signum, frame):
    raise KeyboardInterrupt(f"signal {signum}")


def logs_dir(sha: str) -> Path:
    stamp = datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
    path = log_path().parent / "logs" / f"{stamp}-{sha[:12]}"
    path.mkdir(parents=True, exist_ok=True)
    return path


def preflight_main(repo: Path, args) -> int:
    mode = "dry run" if args.dry_run else "push"
    print(f"safe_push: {mode} of {args.commit} from {repo}"
          + (f", for the branch {args.branch}" if args.branch else ""), flush=True)
    rep = Report()
    sha = base = ""
    result, ci, code = "refused", "", 1
    pushed, pr = False, None
    try:
        ctx = preconditions(repo, args.commit, args.branch, args.dry_run, args.test_mode, rep,
                            title=args.title)
        sha, base = ctx.sha, ctx.base
        logs = logs_dir(sha)
        pre = check_commit(ctx, rep, logs, args.test_mode)
        record = make_record(ctx, pre, rep, full=not args.test_mode)
        save_record(record)
        if args.dry_run:
            rep.heading("5. Push")
            where = f"refs/heads/{ctx.branch}, and open or update its pull request" \
                if ctx.branch else "nowhere: no --branch given"
            if ctx.branch:
                body = fill_body(ctx, pre, record, Path(args.body_file).read_text()) \
                    if args.body_file else generated_body(ctx, pre, record)
                check_body(body)
                (logs / "pr-body.md").write_text(body)
                print(f"  the body it would post: {logs / 'pr-body.md'}")
            rep.add("5", "git push", "skip", f"dry run: would push {sha[:12]} to {where}")
            result, code = "passed every check (dry run, not pushed)", 0
        else:
            # The pull request is settled, its body scanned, before anything is public.
            plan = plan_pr(ctx, pre, record, args)
            push_branch(ctx, rep)
            pushed = True
            result = f"pushed to {ctx.branch}"
            pr = open_pr(ctx, plan, args, rep, logs)
            result = f"pushed to {ctx.branch}; pull request #{pr.number} " \
                     f"{'opened' if pr.created else 'updated'}"
            ci = watch_checks(ctx, pr, rep)
            if ci == "success" and not rep.failed():
                code = 0
            else:
                code = 3
                print("\nCI did not pass for the pull request. Nothing is merged, and main is "
                      f"unchanged: fix {ctx.branch}, then run the pre-flight again.")
    except NothingToPush as e:
        sha = base = str(e)
        result, code = "nothing to push", 0
        print(f"\nNothing to push: origin/main is already {sha[:12]}.")
    except Refusal as e:
        if pushed:
            result, code = f"pushed; CI not followed ({e})", 3
            print(f"\nPushed; CI not followed: {e}")
        else:
            result = f"refused ({e})"
            print(f"\nREFUSED: {e}")
    except KeyboardInterrupt as e:
        if pushed:
            result, code = f"pushed; CI not followed (interrupted: {e or 'Ctrl-C'})", 3
            print(f"\nPushed; CI not followed: interrupted ({e or 'Ctrl-C'})."
                  + (f" Follow it with `gh pr checks {pr.number} --watch`." if pr else
                     " Run the pre-flight again to open the pull request."))
        else:
            result = f"interrupted ({e or 'Ctrl-C'})"
            print(f"\nInterrupted: {result}. The temporary worktrees are removed.")
            code = 1
    except Exception as e:      # after the push, a failure to follow CI is not a refusal
        if not pushed:
            raise
        result, code = f"pushed; CI not followed ({type(e).__name__}: {e})", 3
        print(f"\nPushed; CI not followed: {type(e).__name__}: {e}")
    summary(rep, mode, sha, base, result, ci)
    return code


def merge_main(repo: Path, number: int, dry_run: bool, test_mode: bool) -> int:
    mode = "merge dry run" if dry_run else "merge"
    print(f"safe_push: {mode} of pull request #{number} from {repo}", flush=True)
    rep = Report()
    sha = base = ""
    result, code = "refused", 1
    merged = False
    try:
        ctx, view = merge_preconditions(repo, number, test_mode, rep)
        sha, base = ctx.sha, ctx.base
        earlier = load_record(ctx.sha, ctx.base)
        checked = checks_record(earlier, test_mode)
        if checked is None:
            gates(ctx, number, rep)     # before the long checks, so a draft fails at once
        rep.heading("3. The pre-flight of the head")
        # The secret scan and the guards run on the head every time: the record is a
        # local file, and the pre-flight ran the commit's own code (its checks, and Lean
        # at elaboration), which could have written it. Only the full checks, which CI
        # runs as well, may be taken from it.
        if earlier is None:
            rep.add("3", "pre-flight", "note", f"none of {ctx.sha[:12]} against origin/main "
                    f"{ctx.base[:12]}: it runs now")
        elif checked is None:
            rep.add("3", "pre-flight", "note", f"the record of {ctx.sha[:12]} against "
                    f"origin/main {ctx.base[:12]} is not of the full checks by origin/main's "
                    "harness: they run now")
        else:
            rep.add("3", "pre-flight", "ok", f"{ctx.sha[:12]} checked against origin/main "
                    f"{ctx.base[:12]} ({checked.get('time')}): the secret scan and the guards "
                    "run again; the full checks are not repeated")
        logs = logs_dir(ctx.sha)
        pre = check_commit(ctx, rep, logs, test_mode, checked=checked)
        record = make_record(ctx, pre, rep, full=not test_mode and checked is None,
                             checked=checked)
        save_record(record)
        gates(ctx, number, rep, record)
        body = gh_json(ctx, "pr", "view", str(number), "--json", "body").get("body") or ""
        m = BLOCK.search(body)
        if not m or (m.group(1), m.group(2)) != (ctx.sha, ctx.base):
            if dry_run:
                rep.add("3", "body", "note", "its pre-flight summary is not of this head: "
                        "--merge would replace it")
            else:
                new = put_block(body, preflight_block(ctx.sha, ctx.base, record))
                check_body(new)
                path = logs_dir(ctx.sha) / "pr-body.md"
                path.write_text(new)
                r = gh_run(ctx, "pr", "edit", str(number), "--body-file", str(path))
                rep.add("3", "body", "ok" if r.returncode == 0 else "FAIL",
                        "its pre-flight summary replaced with this head's")
        if rep.failed():
            raise Refusal("the pull request's body could not be brought up to date")
        if dry_run:
            rep.heading("4. Merge")
            rep.add("4", "gh pr merge", "skip", f"dry run: would merge #{number} "
                    f"({ctx.sha[:12]}) with a merge commit, and delete {ctx.branch}")
            result, code = "passed every gate (dry run, not merged)", 0
        else:
            merge(ctx, number, rep)
            merged = True
            main_sha = verify_merge(ctx, rep)
            result = f"merged #{number} as {main_sha[:12]}"
            code = 0 if not rep.failed() else 3
            if code:
                print("\nMerged, but main is not what was checked.\n"
                      + revert_advice(ctx._replace(sha=main_sha)))
    except Refusal as e:
        result = f"refused ({e})" if not merged else f"merged, then {e}"
        code = 1 if not merged else 3
        print(f"\nREFUSED: {e}")
    except KeyboardInterrupt as e:
        result = f"interrupted ({e or 'Ctrl-C'})" + ("; merged" if merged else "")
        code = 3 if merged else 1
        print(f"\nInterrupted: {result}.")
    summary(rep, mode, sha, base, result, "")
    return code


def scan_push_main(repo: Path, local: str, remote: str, ref: str) -> int:
    """The pre-push hook's scan of a push to any branch, or of a tag the owner allowed:
    the commits it carries that the branch on origin, or else origin/main, lacks, with
    origin/main's allow-list; and an annotated tag's message."""
    print(f"pre-push: the secret scan of the push to {ref}", flush=True)
    rep = Report()
    main = rev_parse(repo, "refs/remotes/origin/main^{commit}")
    tag_message: list[Finding] = []
    if git(repo, "cat-file", "-t", local, check=False).strip() == "tag":
        # An annotated tag: its message is published with it, and its target is scanned.
        body = git(repo, "cat-file", "tag", local, check=False).split("\n\n", 1)
        tag_message = scan_block(f"tag {ref.removeprefix('refs/tags/')} message",
                                 list(enumerate((body[1] if len(body) > 1 else "")
                                                .splitlines(), 1)))
    commit = rev_parse(repo, f"{local}^{{commit}}")
    if commit is None:
        print(f"pre-push: refusing the push to {ref}: {local[:12]} is not a commit, nor a tag "
              "of one", file=sys.stderr)
        return 1
    local = commit
    if tag_message:
        print(f"pre-push: refusing the push to {ref}: its message holds what the secret scan "
              "refuses: " + "; ".join(f.shown() for f in tag_message), file=sys.stderr)
        return 1
    base = None
    if remote.strip("0") and rev_parse(repo, f"{remote}^{{commit}}"):
        base = remote if git_ok(repo, "merge-base", "--is-ancestor", remote, local) else \
            (git(repo, "merge-base", remote, local, check=False).strip() or None)
    if base is None and main:
        base = git(repo, "merge-base", main, local, check=False).strip() or None
    try:
        secret_scan(repo, base, local, rep, allow_rev=main)
    except Refusal as e:
        print(f"pre-push: refusing the push to {ref}: {e}", file=sys.stderr)
        return 1
    return 0


REFUSE_DIRECT = """REFUSED: safe_push.py no longer pushes to main: main changes only by a pull
request's merge commit (docs/WORKFLOW.md, "Landing work: pull requests"). Open one with
the pre-flight, and merge it when its gates pass:

    git safe-push --branch <name> --label <kind> [--title T] [--body-file F] [--ready]
    git safe-push --merge <pr-number>

or check the commit alone, pushing nothing: git safe-push --dry-run
(`git safe-push` runs origin/main's copy of this script: sh scripts/install_hooks.sh)"""


def main(argv=None) -> int:
    global ARGV
    ARGV = list(sys.argv[1:] if argv is None else argv)
    if sys.version_info < (3, 11):
        print(f"safe_push needs Python 3.11 or later (tomllib); this is {sys.version.split()[0]}"
              f" at {sys.executable}", file=sys.stderr)
        return 2
    parser = argparse.ArgumentParser(
        description="The pre-flight of a pull request (--branch), and its merge (--merge).")
    parser.add_argument("--branch", help="push the commit to this branch, and open or update "
                        "its pull request onto main")
    parser.add_argument("--title", help="the pull request's title (default: the commit's subject)")
    parser.add_argument("--body-file", help="the pull request's body (default: generated from "
                        f"{TEMPLATE})")
    parser.add_argument("--ready", action="store_true", help="open the pull request ready for "
                        "review, or mark the open one ready (a new one is otherwise a draft)")
    parser.add_argument("--label", action="append", default=[], choices=sorted(LABELS),
                        help="a label for the pull request (repeatable); one names its kind, "
                        f"{', '.join(KIND_LABELS)}, unless the open one has it")
    parser.add_argument("--merge", type=int, metavar="PR", help="merge this pull request, if "
                        "its gates pass")
    parser.add_argument("--commit", default="HEAD", help="the commit to check (default HEAD)")
    parser.add_argument("--dry-run", action="store_true",
                        help="everything but the push, the pull request and the merge")
    # The pre-push hook's entry point: the secret scan of one ref's push.
    parser.add_argument("--scan-push", nargs=3, metavar=("LOCAL", "REMOTE", "REF"),
                        help=argparse.SUPPRESS)
    # Used ONLY by scripts/test_safe_push.py: skips step 4, works only against a local
    # origin, never GitHub, and calls the gh stand-in STOICHEIA_TEST_GH names.
    parser.add_argument("--_test-skip-checks", dest="test_mode", action="store_true",
                        help=argparse.SUPPRESS)
    args = parser.parse_args(ARGV)
    if args.merge is not None and (args.branch or args.title or args.body_file or args.ready
                                   or args.label or args.commit != "HEAD"):
        parser.error("--merge takes only --dry-run")
    if not args.branch and (args.title or args.body_file or args.ready or args.label):
        parser.error("--title, --body-file, --ready and --label go with --branch")
    if args.body_file and not Path(args.body_file).is_file():
        parser.error(f"--body-file {args.body_file}: no such file")

    r = run(["git", "rev-parse", "--show-toplevel"], Path.cwd())
    if r.returncode != 0:
        print("safe_push: run it inside the repository", file=sys.stderr)
        return 2
    repo = Path(r.stdout.strip())
    if args.scan_push:
        return scan_push_main(repo, *args.scan_push)
    signal.signal(signal.SIGTERM, _terminate)
    signal.signal(signal.SIGHUP, _terminate)
    if args.merge is not None:
        return merge_main(repo, args.merge, args.dry_run, args.test_mode)
    if not args.branch and not args.dry_run:
        print(REFUSE_DIRECT)
        return 1
    return preflight_main(repo, args)


if __name__ == "__main__":
    sys.exit(main())
