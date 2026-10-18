#!/usr/bin/env python3
"""Push one commit to main, checked from end to end: the one way the coordinator pushes.

    python3 scripts/safe_push.py [--commit <sha>] [--dry-run]

The commit is HEAD unless `--commit` names another. Nothing is read from the working
tree, so a dirty one does not matter: everything is read from the commit itself, through
git and a fresh temporary worktree of it. The steps run in order, and the first that
fails stops the push with a message saying why:

1. Preconditions. The commit exists; `git fetch origin`; origin/main is an ancestor of
   the commit, so the push is a fast-forward (it is never forced). No tag or release is
   made: those stay manual, with the owner's OK.
2. A secret scan of every line the push adds (`git diff origin/main..<sha>`), of every
   file it adds or changes, and of its commit messages: private keys, API-key-like
   tokens, Authorization headers with values, `.env` and key files, and the owner's
   private paths. A false positive goes in `scripts/safe_push_allow.toml`, with its
   reason.
3. Invariant guards against origin/main, in a fresh temporary worktree of the commit:
   - every statement (facts.json's `statement`, and the Lean source of `theorem PropN`,
     its porism and its companions) is unchanged, unless the push adds a line to
     `docs/briefs/` (a brief's revision, or an entry in 0002-decisions.md) naming it;
   - `Certificate/axioms.lock` is unchanged, unless 0002-decisions.md gains a line
     mentioning the lock;
   - every changed file under `heath/` carries, in the change, a comment naming a scan
     leaf of its own pages (docs/STYLE.md, section 5);
   - no review record is stale (`check_fidelity.py`, on the commit as committed);
   - no whole directory under Elements/, heath/, review/, figures/ or mishnah/ is
     deleted unless 0002-decisions.md gains a line naming it.
4. The full local check sequence of docs/WORKFLOW.md, section 8, in that worktree, and
   `negative_tests.py` in a second one; each step's outcome and time is recorded.
5. `git push origin <sha>:refs/heads/main`, never forced, then a wait for the GitHub
   Actions run of that commit (`gh run list --commit`, `gh run watch --exit-status`).
   On a failure it prints the revert command, and reverts nothing itself.
6. A summary, printed and appended to `~/.cache/stoicheia/pushes.log`, outside the
   repository (`STOICHEIA_PUSH_LOG` names another file); each step's full output is
   kept beside it, in `logs/`.

`--dry-run` does everything but the push. The temporary worktrees are removed at the
end, on a failure too. The pre-push hook, `scripts/hooks/pre-push` (installed by
`scripts/install_hooks.sh`), refuses a push to main unless STOICHEIA_SAFE_PUSH names the
commit pushed, which this script sets for its own push alone.

Exit status: 0 when pushed and CI passed, when a dry run passed, or when there is nothing
to push; 1 when refused before the push; 2 for a usage error; 3 when pushed but CI failed
or could not be followed. Standard library, git and gh; Python 3.11 or later.
"""

from __future__ import annotations

import argparse
import contextlib
import datetime
import fnmatch
import json
import math
import os
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

PY = sys.executable
DECISIONS = "docs/briefs/0002-decisions.md"
BRIEFS = "docs/briefs/"
LOCK = "Certificate/axioms.lock"
ALLOWLIST = "scripts/safe_push_allow.toml"
GUARDED_DIRS = ("Elements", "heath", "review", "figures", "mishnah")
CI_APPEAR_TIMEOUT = 300   # seconds to wait for the Actions run to appear after the push
CI_WATCH_INTERVAL = "30"  # seconds between `gh run watch` refreshes
TAIL = 40                 # lines of a failed step's output to print

# The full local check sequence, exactly as docs/WORKFLOW.md, section 8, and CI's `check`
# job run it, then the `model` job. Change it with them.
CHECKS = [
    ("lake build", ["lake", "build"]),
    ("lake build Audit", ["lake", "build", "Audit"]),
    ("lake build Staging", ["lake", "build", "Staging"]),
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


class Refusal(Exception):
    """A step failed: nothing is pushed (or, after the push, nothing more is done)."""


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


def show(repo, rev: str, path: str) -> str | None:
    """A file's text at a revision, or None if it is not there."""
    r = run(["git", "show", f"{rev}:{path}"], repo, binary=True)
    return r.stdout.decode("utf-8", errors="replace") if r.returncode == 0 else None


def tool_env() -> dict:
    """The environment for the checks: elan's lake on the PATH, as CI and AGENTS.md set it."""
    env = dict(os.environ)
    elan = str(Path.home() / ".elan" / "bin")
    env["PATH"] = elan + os.pathsep + env.get("PATH", "")
    return env


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


def added_lines(repo, base: str, sha: str, *pathspec: str) -> list[Added]:
    """Every line the diff base..sha adds, with its file and line number. Parsed by the
    hunk counts, so an added line that itself begins "+++" is not taken for a header."""
    out = git(repo, "diff", "--no-color", "--no-ext-diff", "--no-textconv", "--no-renames",
              "--unified=0", "--src-prefix=a/", "--dst-prefix=b/", f"{base}..{sha}",
              "--", *pathspec, binary=True).decode("utf-8", errors="replace")
    found: list[Added] = []
    path = None
    old_left = new_left = 0
    line_no = 0
    for line in out.split("\n"):
        if old_left > 0 or new_left > 0:
            if line.startswith("+"):
                if path is not None:
                    found.append(Added(path, line_no, line[1:]))
                line_no += 1
                new_left -= 1
            elif line.startswith("-"):
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
    return found


def changed_files(repo, base: str, sha: str, *pathspec: str) -> list[tuple[str, str]]:
    """(status, path) for each file the diff changes, renames shown as delete and add."""
    out = git(repo, "diff", "--name-status", "-z", "--no-renames", f"{base}..{sha}", "--",
              *pathspec)
    parts = out.split("\0")
    return [(parts[i][0], parts[i + 1]) for i in range(0, len(parts) - 1, 2)]


def binary_files(repo, base: str, sha: str) -> set[str]:
    out = git(repo, "diff", "--numstat", "-z", "--no-renames", f"{base}..{sha}")
    return {rec.split("\t", 2)[2] for rec in out.split("\0")
            if rec.startswith("-\t-\t")}


def added_text(repo, base, sha, *pathspec) -> str:
    """The lines the push adds under `pathspec`, joined, so that a name broken across
    two lines of a wrapped paragraph is still found."""
    return " ".join(a.text.strip() for a in added_lines(repo, base, sha, *pathspec))


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
# A long base64 or hex run after a word naming a key, token, secret or password.
# The name is bounded, and must start a word, so a long run of letters (an image's
# base64 in an SVG) costs linear time, not quadratic.
KEYWORD = re.compile(
    r"(?i)(?<![\w-])[\w-]{0,40}(?:key|token|secret|passw(?:or)?d|bearer)[\w-]{0,40}[\"']?"
    r"\s*(?:=>|:=|[:=]|\s)\s*[\"'`]?([A-Za-z0-9+/_=.~-]{20,})")
# The owner's private paths, in pieces for the reason above.
PRIVATE_PATHS = [
    re.compile("(?i)secret" + "s20"),
    re.compile("/" + "Downloads" + "/"),
    re.compile("/" + "Users" + "/"),
    re.compile(r"(?i)\b[A-Z]:\\" + "Users" + r"\\"),
]
SECRET_FILES = [
    (re.compile(r"(^|/)\.env(\.[^/]*)?$"), ".env file"),
    (re.compile(r"\.(key|pem|p12|pfx)$", re.I), "key file"),
    (re.compile(r"(^|/)id_(rsa|dsa|ecdsa|ed25519)$"), "SSH private key file"),
]


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
    text: str           # the whole line, for the allow-list to match
    span: tuple[int, int]

    def shown(self) -> str:
        """The line with the secret masked, so the report does not repeat it."""
        a, b = self.span
        secret = self.text[a:b]
        masked = secret[:4] + f"…({len(secret)} chars)" if b - a > 8 else secret
        line = (self.text[:a] + masked + self.text[b:]).strip()
        if len(line) > 140:
            line = line[:140] + "…"
        where = f"{self.path}:{self.line}" if self.line else self.path
        return f"{where}: {self.rule}: {line}"


def scan_text(path: str, line_no: int | None, text: str, *, strong_only=False) -> list[Finding]:
    found = []
    for rule, pattern in TOKEN_RULES:
        if strong_only and rule in ("Authorization header", "bearer token"):
            continue
        for m in pattern.finditer(text):
            found.append(Finding(rule, path, line_no, text, m.span()))
    if not strong_only:
        for m in KEYWORD.finditer(text):
            if looks_secret(m.group(1)):
                found.append(Finding("key, token or secret", path, line_no, text, m.span(1)))
    for pattern in PRIVATE_PATHS:
        for m in pattern.finditer(text):
            found.append(Finding("private path", path, line_no, text, m.span()))
    # One finding per place: a token can match two rules.
    seen, unique = set(), []
    for f in found:
        if f.span not in seen:
            seen.add(f.span)
            unique.append(f)
    return unique


def scan_path(path: str) -> list[Finding]:
    found = [Finding(rule, path, None, path, (0, 0)) for pattern, rule in SECRET_FILES
             if pattern.search(path)]
    for pattern in PRIVATE_PATHS:
        for m in pattern.finditer(path):
            found.append(Finding("private path in a file name", path, None, path, m.span()))
    return found


class Allow(NamedTuple):
    path: str
    match: str
    rule: str | None
    reason: str


def load_allowlist(repo, sha) -> list[Allow]:
    """The allow-list as the commit has it: each entry a file glob, a part of the flagged
    line (or of the file name), an optional rule, and a reason, which is required."""
    text = show(repo, sha, ALLOWLIST)
    if text is None:
        return []
    import tomllib
    try:
        data = tomllib.loads(text)
    except tomllib.TOMLDecodeError as e:
        raise Refusal(f"{ALLOWLIST} is not valid TOML: {e}")
    entries, problems = [], []
    for i, entry in enumerate(data.get("allow", []), 1):
        if not isinstance(entry, dict):
            problems.append(f"entry {i} is not a table")
            continue
        path, match = entry.get("path"), entry.get("match")
        reason, rule = entry.get("reason"), entry.get("rule")
        if not isinstance(path, str) or not path:
            problems.append(f"entry {i} has no path")
        if not isinstance(match, str) or not match:
            problems.append(f"entry {i} has no match")
        if not isinstance(reason, str) or not reason.strip():
            problems.append(f"entry {i} has no reason")
        if isinstance(path, str) and path and isinstance(match, str) and match \
                and isinstance(reason, str) and reason.strip():
            entries.append(Allow(path, match, rule, reason.strip()))
    if problems:
        raise Refusal(f"{ALLOWLIST}: " + "; ".join(problems))
    return entries


def allowed(f: Finding, allow: list[Allow]) -> Allow | None:
    for a in allow:
        if fnmatch.fnmatchcase(f.path, a.path) and a.match in f.text and a.rule in (None, f.rule):
            return a
    return None


def secret_scan(repo, base, sha, rep: Report):
    rep.heading("2. Secret scan")
    t = time.time()
    allow = load_allowlist(repo, sha)
    findings: list[Finding] = []
    files = changed_files(repo, base, sha)
    for status, path in files:
        if status != "D":
            findings += scan_path(path)
    lines = added_lines(repo, base, sha)
    for a in lines:
        findings += scan_text(a.path, a.line, a.text)
    binaries = binary_files(repo, base, sha)
    present = {p for s, p in files if s != "D"}
    for path in sorted(binaries & present):
        blob = git(repo, "cat-file", "blob", f"{sha}:{path}", binary=True)
        findings += scan_text(path, None, blob.decode("latin-1"), strong_only=True)
    commits = git(repo, "rev-list", f"{base}..{sha}").split()
    for c in commits:
        message = git(repo, "log", "-1", "--format=%B", c)
        for i, line in enumerate(message.splitlines(), 1):
            findings += scan_text(f"commit {c[:12]} message", i, line)
    refused = [f for f in findings if not allowed(f, allow)]
    passed = [(f, allowed(f, allow)) for f in findings if allowed(f, allow)]
    seconds = time.time() - t
    scanned = (f"{plural(len(lines), 'added line')} in {plural(len(present), 'file')} "
               f"({len(binaries & present)} binary), {plural(len(commits), 'commit message')}")
    for f, a in passed:
        rep.add("2", "allow-listed", "note", f"{f.shown()}\nreason: {a.reason}")
    if refused:
        detail = "\n".join(f.shown() for f in refused)
        rep.add("2", "secrets", "FAIL", f"{len(refused)} found in {scanned}:\n{detail}", seconds)
        raise Refusal(f"the secret scan found {len(refused)} possible secret(s) or private "
                      f"path(s). Remove them (and rewrite the commits that hold them), or, for "
                      f"a false positive, add an entry with its reason to {ALLOWLIST}.")
    rep.add("2", "secrets", "ok", f"nothing found in {scanned}", seconds)


# --------------------------------------------------------------------------------------
# Step 3: the invariant guards


def source_statement(src: str, n: int, name: str | None) -> str | None:
    """The statement of `theorem PropN` (or `PropN.<name>`) as written in the Lean: its
    binders and type, up to `:=`, whitespace made single. The docstring is left out: it
    is Heath's enunciation, which check_fidelity compares with heath/."""
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
    cut = text.find(":=")
    return " ".join((text[:cut] if cut >= 0 else text).split())


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


def names_ref(text: str, ref: str) -> bool:
    """Does `text` name the proposition of `ref`: "III.16", "III. 16" or
    `BookIII.Prop16`? A porism or companion is named by its proposition. "III.1" is
    not named by "III.16", nor "I.1" by "III.1"."""
    r = heath.parse_ref(ref)
    plain = r"(?<![\w.])%s\.\s?%d(?!\d)" % (r.book, r.n)
    lean = r"Book%s\.Prop%d(?!\d)" % (r.book, r.n)
    return re.search(plain, text) is not None or re.search(lean, text) is not None


def guard_statements(repo, base, sha, wt: Path, rep: Report) -> None:
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
    briefs = added_text(repo, base, sha, BRIEFS)
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
        if names_ref(briefs, ref):
            approved.append(f"{ref} ({'; '.join(why)}), named in the docs/briefs/ lines added")
        else:
            changed.append(f"{ref}: {'; '.join(why)}, and no line added to docs/briefs/ "
                           f"(a brief's revision or a decisions entry) names {r.parent}")
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


LOCK_MENTION = re.compile(r"(?i)axioms\.lock|axiom lock")


def guard_lock(repo, base, sha, rep: Report) -> None:
    if git_ok(repo, "diff", "--quiet", f"{base}..{sha}", "--", LOCK):
        rep.add("3", "axiom lock", "ok", f"{LOCK} unchanged")
        return
    if LOCK_MENTION.search(added_text(repo, base, sha, DECISIONS)):
        rep.add("3", "axiom lock", "ok", f"{LOCK} changed, and {DECISIONS} gains a line "
                "mentioning the lock")
    else:
        rep.add("3", "axiom lock", "FAIL", f"{LOCK} changed, and no line added to "
                f"{DECISIONS} mentions the lock (\"axioms.lock\" or \"axiom lock\")")


COMMENT = re.compile(r"<!--.*?-->", re.S)
LEAF_RANGE = re.compile(r"\bn(\d+)\s*[–-]\s*n(\d+)\b")
LEAF = re.compile(r"\bn(\d+)\b")
LEAF_WORD = re.compile(r"(?i)\bleaf\b|\bleaves\b")


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
        leaves = own_leaves(text)
        lines = added.get(path, set())
        named = set()
        for m in COMMENT.finditer(text):
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
                       f"pages' leaves ({', '.join(f'n{x}' for x in sorted(leaves))})")
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
    decisions = added_text(repo, base, sha, DECISIONS)
    unnamed = [d for d in top
               if not re.search(r"(?<![\w/.-])%s/?(?![\w./-])" % re.escape(d), decisions)]
    if unnamed:
        rep.add("3", "directories", "FAIL", f"deleted with no line added to {DECISIONS} "
                f"naming them: {', '.join(d + '/' for d in unnamed)}")
    else:
        rep.add("3", "directories", "ok", f"deleted, each named in {DECISIONS}: "
                f"{', '.join(d + '/' for d in top)}")


def guard_fidelity(wt: Path, rep: Report, logs: Path) -> None:
    t = time.time()
    r = run([PY, "scripts/check_fidelity.py"], wt, env=tool_env())
    out = (r.stdout or "") + (r.stderr or "")
    (logs / "03-check_fidelity.log").write_text(out)
    seconds = time.time() - t
    if r.returncode == 0:
        rep.add("3", "review records", "ok", "check_fidelity.py passes on the commit as "
                "committed: no record stale", seconds)
    else:
        rep.add("3", "review records", "FAIL",
                "check_fidelity.py fails on the commit as committed:\n" + tail(out, 25), seconds)


def guard_foundations(repo, base, sha, rep: Report) -> None:
    """Not a guard: the foundations are the coordinator's, so their changes are listed."""
    files = changed_files(repo, base, sha, "Elements/Foundations")
    if files:
        rep.add("3", "foundations", "note", "changed (the coordinator's files): "
                + ", ".join(p for _, p in files))


def guards(repo, base, sha, wt: Path, rep: Report, logs: Path) -> None:
    rep.heading(f"3. Invariant guards against origin/main, in {wt}")
    guard_statements(repo, base, sha, wt, rep)
    guard_lock(repo, base, sha, rep)
    guard_heath(repo, base, sha, wt, rep)
    guard_directories(repo, base, sha, rep)
    guard_fidelity(wt, rep, logs)
    guard_foundations(repo, base, sha, rep)
    failed = [s.name for s in rep.failed() if s.stage == "3"]
    if failed:
        raise Refusal(f"the invariant guards refused: {', '.join(failed)}")


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


def run_step(stage, name, cmd, cwd: Path, rep: Report, logs: Path, index: int) -> None:
    t = time.time()
    log = logs / f"{index:02d}-{re.sub(r'[^A-Za-z0-9]+', '-', name).strip('-')}.log"
    if cmd is None:     # the generated pages are current
        r = run(["git", "status", "--porcelain"], cwd)
        out, ok = r.stdout + r.stderr, r.returncode == 0 and not r.stdout.strip()
    else:
        r = run(cmd, cwd, env=tool_env())
        out, ok = (r.stdout or "") + (r.stderr or ""), r.returncode == 0
    log.write_text(out)
    seconds = time.time() - t
    if ok:
        rep.add(stage, name, "ok", "", seconds)
        return
    rep.add(stage, name, "FAIL", f"full output in {log}\n{tail(out)}", seconds)
    raise Refusal(f"`{name}` failed on the commit")


def copy_build(src: Path, dst: Path) -> None:
    """Give the second worktree the first one's build of the same commit (a clone of the
    files on APFS); lake rebuilds whatever it finds out of date."""
    if not (src / ".lake").exists():
        return
    flags = ["-Rc"] if sys.platform == "darwin" else ["-R"]
    if run(["cp", *flags, str(src / ".lake"), str(dst / ".lake")], dst).returncode != 0:
        shutil.rmtree(dst / ".lake", ignore_errors=True)


# --------------------------------------------------------------------------------------
# Step 1: preconditions


class Context(NamedTuple):
    repo: Path
    sha: str
    base: str
    commits: int
    origin: str
    github: str | None       # "owner/repo" when origin is on GitHub
    tags: dict[str, str]     # origin's tags before the push


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


def hook_installed(repo) -> bool:
    out = git(repo, "rev-parse", "--git-path", "hooks", check=False).strip()
    hook = Path(out) if os.path.isabs(out) else Path(repo) / out
    hook = hook / "pre-push"
    try:
        return "STOICHEIA_SAFE_PUSH" in hook.read_text()
    except OSError:
        return False


def preconditions(repo: Path, commit: str, dry_run: bool, test_mode: bool,
                  rep: Report) -> Context:
    rep.heading("1. Preconditions")
    if sys.version_info < (3, 11):
        raise Refusal("safe_push needs Python 3.11 or later (tomllib)")
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
    if test_mode and not is_local(origin):
        raise Refusal("the internal test flag works only against a local origin")
    t = time.time()
    r = run(["git", "fetch", "origin"], repo)
    if r.returncode != 0:
        raise Refusal(f"`git fetch origin` failed: {r.stderr.strip()}")
    rep.add("1", "fetch", "ok", f"git fetch origin ({origin})", time.time() - t)
    r = run(["git", "rev-parse", "--verify", "--quiet", "refs/remotes/origin/main^{commit}"],
            repo)
    if r.returncode != 0:
        raise Refusal("origin has no main branch")
    base = r.stdout.strip()
    if base == sha:
        rep.add("1", "fast-forward", "ok", f"origin/main is already {sha[:12]}")
        raise NothingToPush(sha)
    if not git_ok(repo, "merge-base", "--is-ancestor", base, sha):
        rep.add("1", "fast-forward", "FAIL", f"origin/main {base[:12]} is not an ancestor of "
                f"{sha[:12]}")
        raise Refusal(f"not a fast-forward: origin/main ({base[:12]}) is not an ancestor of "
                      f"{sha[:12]}. Merge or rebase onto origin/main first; safe_push never "
                      "forces a push.")
    commits = int(git(repo, "rev-list", "--count", f"{base}..{sha}").strip())
    rep.add("1", "fast-forward", "ok", f"origin/main {base[:12]} is an ancestor: "
            f"{commits} commit{'s' if commits != 1 else ''} to push")
    rep.add("1", "tags and releases", "ok", "none is made: tags, releases and their notes "
            "stay manual, with the owner's OK")
    slug = github_slug(origin)
    if not test_mode and shutil.which("lake", path=tool_env()["PATH"]) is None:
        raise Refusal("lake is not on the PATH, nor in ~/.elan/bin: the full checks need it")
    tags: dict[str, str] = {}
    if not dry_run:
        tags = remote_refs(repo, "--tags")
        if slug:
            if shutil.which("gh") is None:
                raise Refusal("gh is not installed: the push must be followed to its CI run")
            r = run(["gh", "auth", "status", "--hostname", "github.com"], repo)
            if r.returncode != 0:
                raise Refusal("gh is not logged in to github.com (`gh auth login`): the push "
                              "must be followed to its CI run")
    if not hook_installed(repo):
        rep.add("1", "pre-push hook", "note", "not installed here (sh scripts/install_hooks.sh); "
                "safe_push does not need it")
    return Context(repo, sha, base, commits, origin, slug, tags)


# --------------------------------------------------------------------------------------
# Step 5: the push, and its CI run


def push(ctx: Context, rep: Report) -> None:
    rep.heading("5. Push")
    now = remote_refs(ctx.repo, "refs/heads/main").get("refs/heads/main")
    if now != ctx.base:
        raise Refusal(f"origin/main moved from {ctx.base[:12]} to {str(now)[:12]} during the "
                      "checks: run safe_push again, against the new main")
    t = time.time()
    env = dict(os.environ, STOICHEIA_SAFE_PUSH=ctx.sha)
    r = run(["git", "push", "--no-follow-tags", "--porcelain", "origin",
             f"{ctx.sha}:refs/heads/main"], ctx.repo, env=env)
    if r.returncode != 0:
        rep.add("5", "git push", "FAIL", (r.stdout + r.stderr).strip(), time.time() - t)
        raise Refusal("git push failed; nothing was forced")
    after = remote_refs(ctx.repo, "refs/heads/main").get("refs/heads/main")
    if after != ctx.sha:
        rep.add("5", "git push", "FAIL", f"origin/main is {after}, not {ctx.sha}")
        raise Refusal("the push did not leave origin/main at the commit")
    rep.add("5", "git push", "ok", f"origin/main {ctx.base[:12]} -> {ctx.sha[:12]}, "
            "a fast-forward", time.time() - t)
    tags = remote_refs(ctx.repo, "--tags")
    if tags != ctx.tags:
        new = sorted(set(tags) - set(ctx.tags))
        rep.add("5", "tags", "FAIL", f"origin's tags changed during the push: {new}")
    else:
        rep.add("5", "tags", "ok", "origin's tags unchanged")


def revert_advice(ctx: Context) -> str:
    lines = ["Nothing has been reverted. To undo the push, from a clean checkout of "
             f"{ctx.sha[:12]}:",
             f"    git revert --no-edit {ctx.sha}",
             "    python3 scripts/safe_push.py"]
    if ctx.commits > 1:
        lines += [f"The push carried {ctx.commits} commits; that revert undoes the last "
                  "alone. To undo all of them in one commit:",
                  f"    git restore --source={ctx.base} --staged --worktree -- :/",
                  f"    git commit -m \"Revert to {ctx.base[:12]}: CI failed on {ctx.sha[:12]}\"",
                  "    python3 scripts/safe_push.py"]
    return "\n".join(lines)


def watch_ci(ctx: Context, rep: Report) -> str:
    """Wait for the Actions run of the commit and follow it; return its conclusion."""
    rep.heading("CI")
    if not ctx.github:
        rep.add("5", "CI", "skip", f"origin ({ctx.origin}) is not on GitHub: no Actions run "
                "to follow")
        return "none"
    t = time.time()
    runs = []
    while time.time() - t < CI_APPEAR_TIMEOUT:
        r = run(["gh", "run", "list", "--commit", ctx.sha, "--event", "push", "--json",
                 "databaseId,workflowName,status,conclusion,url", "-R", ctx.github], ctx.repo)
        if r.returncode == 0:
            runs = json.loads(r.stdout or "[]")
            if runs:
                break
        time.sleep(10)
    if not runs:
        rep.add("5", "CI", "FAIL", f"no Actions run appeared for {ctx.sha[:12]} in "
                f"{CI_APPEAR_TIMEOUT} s: `gh run list --commit {ctx.sha}`")
        return "unknown"
    conclusions = []
    for item in runs:
        run_id = str(item["databaseId"])
        print(f"  following {item.get('workflowName')} run {run_id}: {item.get('url')}",
              flush=True)
        subprocess.run(["gh", "run", "watch", run_id, "--exit-status", "--compact",
                        "--interval", CI_WATCH_INTERVAL, "-R", ctx.github], cwd=ctx.repo)
        r = run(["gh", "run", "view", run_id, "--json", "conclusion,url,jobs", "-R",
                 ctx.github], ctx.repo)
        view = json.loads(r.stdout or "{}") if r.returncode == 0 else {}
        conclusion = view.get("conclusion") or "unknown"
        jobs = ", ".join(f"{j.get('name')} {j.get('conclusion')}" for j in view.get("jobs", []))
        conclusions.append(conclusion)
        rep.add("5", f"CI {item.get('workflowName')}",
                "ok" if conclusion == "success" else "FAIL",
                f"{conclusion}: {jobs} ({view.get('url', item.get('url'))})")
    return "success" if all(c == "success" for c in conclusions) else ",".join(conclusions)


# --------------------------------------------------------------------------------------
# Step 6: the summary and the log outside the repository


def log_path() -> Path:
    env = os.environ.get("STOICHEIA_PUSH_LOG")
    return Path(env) if env else Path.home() / ".cache" / "stoicheia" / "pushes.log"


def summary(rep: Report, mode: str, sha: str, base: str, result: str, ci: str) -> None:
    total = time.time() - rep.started
    print(f"\nSummary: {mode} of {sha[:12] or '?'} onto origin/main {base[:12] or '?'}: "
          f"{result}" + (f"; CI {ci}" if ci else "") + f" ({total:.0f} s)")
    timed = [s for s in rep.steps if s.outcome in ("ok", "FAIL", "skip")]
    width = max((len(s.name) for s in timed), default=10)
    for s in timed:
        took = f"{s.seconds:8.1f} s" if s.seconds is not None else " " * 10
        print(f"  {s.stage}  {s.outcome:4}  {s.name:<{width}}  {took}")
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    steps = "; ".join(f"{s.name}={s.outcome}" + (f" {s.seconds:.1f}s" if s.seconds else "")
                      for s in timed)
    line = (f"{stamp} {mode} {sha[:12] or '?'} onto {base[:12] or '?'}: {result}"
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


def _terminate(signum, frame):
    raise KeyboardInterrupt(f"signal {signum}")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="Push a commit to main after checking it from end to end.")
    parser.add_argument("--commit", default="HEAD", help="the commit to push (default HEAD)")
    parser.add_argument("--dry-run", action="store_true", help="everything but the push")
    # Used ONLY by scripts/test_safe_push.py: skips step 4, and works only against a
    # local origin, never GitHub.
    parser.add_argument("--_test-skip-checks", dest="test_mode", action="store_true",
                        help=argparse.SUPPRESS)
    args = parser.parse_args(argv)

    r = run(["git", "rev-parse", "--show-toplevel"], Path.cwd())
    if r.returncode != 0:
        print("safe_push: run it inside the repository", file=sys.stderr)
        return 2
    repo = Path(r.stdout.strip())
    mode = "dry run" if args.dry_run else "push"
    print(f"safe_push: {mode} of {args.commit} from {repo}", flush=True)
    signal.signal(signal.SIGTERM, _terminate)
    signal.signal(signal.SIGHUP, _terminate)

    rep = Report()
    sha = base = ""
    result, ci, code = "refused", "", 1
    stamp = datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
    try:
        ctx = preconditions(repo, args.commit, args.dry_run, args.test_mode, rep)
        sha, base = ctx.sha, ctx.base
        logs = log_path().parent / "logs" / f"{stamp}-{sha[:12]}"
        logs.mkdir(parents=True, exist_ok=True)
        secret_scan(repo, base, sha, rep)
        with tempfile.TemporaryDirectory(prefix="stoicheia-push-") as tmp:
            parent = Path(tmp)
            with worktree(repo, sha, parent, "check") as wt:
                guards(repo, base, sha, wt, rep, logs)
                rep.heading("4. The full local checks (docs/WORKFLOW.md, section 8)")
                if args.test_mode:
                    rep.add("4", "full local checks", "skip", "internal test flag, local origin")
                else:
                    for i, (name, cmd) in enumerate(CHECKS, 1):
                        run_step("4", name, cmd, wt, rep, logs, 10 + i)
                    with worktree(repo, sha, parent, "negative") as neg:
                        copy_build(wt, neg)
                        for i, (name, cmd) in enumerate(NEGATIVE, 1):
                            run_step("4", name, cmd, neg, rep, logs, 30 + i)
        if args.dry_run:
            rep.heading("5. Push")
            rep.add("5", "git push", "skip", f"dry run: would push {sha[:12]} to origin/main")
            result, code = "passed every check (dry run, not pushed)", 0
        else:
            push(ctx, rep)
            result = "pushed"
            ci = watch_ci(ctx, rep)
            if ci in ("success", "none") and not rep.failed():
                code = 0
            else:
                code = 3
                print("\nCI did not pass for the push.\n" + revert_advice(ctx))
    except NothingToPush as e:
        sha = base = str(e)
        result, code = "nothing to push", 0
        print(f"\nNothing to push: origin/main is already {sha[:12]}.")
    except Refusal as e:
        result = f"refused ({e})" if result == "refused" else f"{result}, then {e}"
        print(f"\nREFUSED: {e}")
        if result.startswith("pushed"):
            code = 3
    except KeyboardInterrupt as e:
        result = f"interrupted ({e or 'Ctrl-C'})"
        print(f"\nInterrupted: {result}. The temporary worktrees are removed.")
        code = 1
    finally:
        summary(rep, mode, sha, base, result, ci)
    return code


if __name__ == "__main__":
    sys.exit(main())
