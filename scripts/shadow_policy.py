#!/usr/bin/env python3
"""The shadow run of main's checking policy in CI (#574, train 1): its driver.

    python3 -I scripts/shadow_policy.py judge --base B --tested T --out DIR
                [--repository OWNER/NAME] [--event NAME] [--pr-head H]
    python3 -I scripts/shadow_policy.py plant NAME --base B --out DIR
                [--repository OWNER/NAME]
    python3 -I scripts/shadow_policy.py self-test

`judge` runs main's own pre-flight, unchanged, on the commit T against the base B, and
writes what it found to DIR/verdict.json. Main's pre-flight is `scripts/safe_push.py
--dry-run` as B holds it: B's scripts/ is taken out of Git (`git archive`) into
DIR/harness and run from there, in DIR/repo, a clone whose origin, DIR/origin.git, holds B
as its main and nothing else, with T checked out detached. So main's policy applies as the
local pre-flight applies it: the secret scan, the guards of step 3, both passes of
check_fidelity.py and render.py, keep_apart at steps 3 and 4, step 4's full checks under
B's registry and then T's own, and the negative tests in both passes. What needs a branch
is not run, as the dry run is given none: the kind label, the public names, a train/
branch's check and its body; the class is found without labels. Nothing of the policy is
written again here, so nothing here can drift from it. The pre-flight's log, its step logs
and its record (STOICHEIA_PUSH_LOG names DIR/state/pushes.log) stay beside the verdict, and
its printed report in DIR/preflight.log.

The verdict is read from the report safe_push.py prints, in the format of its Report.add
(each step's line as it happens, under its step's heading) and summary() (after
"Summary:", a table of every ok, FAIL and skip). It fails closed: an exit other than 0 or
1, no summary line or two, a summary of another commit or base, a table row that the
stream does not hold in the same place and under the same step, a pass with a failing
step, a refusal with none (the harness or the environment refused, not the policy), or a
pass whose record is missing or disagrees with the report, is verdict "error", and exit 3;
why is in DIR/why.txt. A change to that format on main therefore turns every verdict into
"error", never into "passed"; and the self-test reads report texts printed by the
checkout's own Report and summary(), so that such a change shows on main's next push.

`plant` builds one of the planted cases (PLANTS) on B, in a throwaway worktree, judges it
into DIR/judge, and compares the verdict with the case's expectation (DIR/plant.json).
Each mirrors a case scripts/test_safe_push.py holds for the local harness, so the shadow is
held to the local harness's known behaviour. `self-test` reads report texts in the real
format, and planted misreadings of them, with no Lean and no network.

verdict.json, schema "stoicheia-shadow-policy/1", canonical (keys sorted, no spaces,
ASCII): the repository, event, base, tested and its tree, pr_head and its tree when known
(T a merge whose parents are B and pr_head, and no other); `policy`, the blobs of B's
safe_push.py, heath.py, check_train.py, registry.py and risk.py, the tree of B's checks/,
and the driver's own blob and whose copy it is (`from`: "base", "tested" or
"neither"); `runtime`; the pre-flight's `exit`, the `verdict` (passed, refused or error),
`result` (the summary's words), `class`, `kept_apart` (the step of a "check change kept
apart" FAIL, or null), `base_pass_notes` and `pinned_values`, every `steps` row and every
`notes` line, and `record`, the pre-flight's own record when it passed.

Trust. The verdict is only as good as the run that made it. It counts only while the
workflow GitHub runs (.github/workflows/shadow-policy.yml) still calls main's driver, and
the copy of the workflow GitHub runs is the pushed commit's; nothing here is signed or
protected (the plan's next train protects the verdict, and a later one signs it); and the
pre-flight runs T's own code, its checks and its Lean, as the same user in the same job, so
a hostile T could change what this driver reads or writes after it, and what the
workflow's later steps run. So a verdict is evidence that main's policy, run in CI, agrees
with the local pre-flight on honest work, not a defence against a hostile commit. Standard
library and Git only; Python 3.11 or later.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import importlib.util
import io
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path
from typing import NamedTuple

SCHEMA = "stoicheia-shadow-policy/1"
FULL_SHA = re.compile(r"[0-9a-f]{40}")
DRIVER = "scripts/shadow_policy.py"
WORKFLOW = ".github/workflows/shadow-policy.yml"
# The policy's files at the base, whose blobs the verdict names; and its registry of checks.
POLICY_FILES = ("scripts/safe_push.py", "scripts/heath.py", "scripts/check_train.py",
                "scripts/registry.py", "scripts/risk.py")
REGISTRY = "checks"

# What the report says, in safe_push.py's words: BASE_PASS, keep_apart's FAIL and its note,
# and the result of a dry run that passed (preflight_main).
BASE_PASS = " (origin/main's checks)"
KEPT_APART = "check change kept apart"
PINNED = "pinned values"
MODE = "dry run"
PASSED = "passed every check (dry run, not pushed)"
# Report.add's labels, and the lines it prints: "  <label>  <name>: <first line>" with
# "  (<seconds> s)" after it when timed; the detail's other lines indented by eight spaces.
# Report.heading's line, "<step>. <words>", after an empty line.
LABELS = {"ok  ": "ok", "FAIL": "FAIL", "skip": "skip", "note": "note"}
HEADING = re.compile(r"(\d+)\. \S.*")
STEP_LINE = re.compile(r"  (ok  |FAIL|skip|note)  (.*)")
TOOK = re.compile(r"  \(\d+\.\d s\)$")
# summary(): "Summary: <mode> of <sha12> against origin/main <base12>: <result> (<n> s)",
# the result perhaps of several lines (a refusal's message); then a row for each ok, FAIL
# and skip, "  <stage>  <outcome:4>  <name, padded to the longest>  <seconds:8.1f> s" (ten
# spaces when untimed); then the line saying where the log went.
SUMMARY = re.compile(r"Summary: (.+?) of ([0-9a-f]{12}|\?) against origin/main "
                     r"([0-9a-f]{12}|\?): (.*) \(\d+ s\)", re.S)
SUMMARY_END = re.compile(r" \(\d+ s\)$")
ROW = re.compile(r"  (\d+)  (ok  |FAIL|skip)  (.*)")
ROW_REST = re.compile(r"(.*?)  (?: {10}| *\d+\.\d s)")
LOGGED = ("Logged to ", "Could not write the log ")

# The variables the launcher (scripts/hooks/safe-push) unsets before it runs main's
# safe_push.py, and GIT_REPLACE_REF_BASE, which it unsets too: none ties a command run here
# to another repository. STOICHEIA_HARNESS is safe_push's own hand-over marker.
UNSET = frozenset({"GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_COMMON_DIR", "GIT_CONFIG",
                   "GIT_CONFIG_COUNT", "GIT_CONFIG_PARAMETERS", "GIT_DIR", "GIT_GRAFT_FILE",
                   "GIT_IMPLICIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_INTERNAL_SUPER_PREFIX",
                   "GIT_OBJECT_DIRECTORY", "GIT_PREFIX", "GIT_SHALLOW_FILE", "GIT_WORK_TREE",
                   "GIT_REPLACE_REF_BASE", "STOICHEIA_HARNESS"})
# Git here reads no replacement objects and runs no hook: a clone of the repository may
# have safe_push's pre-push hook installed, which a push to a scratch origin must not run.
GIT = ("git", "-c", "core.hooksPath=/dev/null", "-c", "core.useReplaceRefs=false")


class Failed(Exception):
    """The run could not be made or read: the verdict is "error"."""


class Misread(Failed):
    """The report is not one safe_push.py prints, or not a verdict of the policy."""


class PlantError(Failed):
    """A planted case could not be built: its anchor is gone, or its render.py failed."""


def clean_env(**extra: str) -> dict:
    env = {name: value for name, value in os.environ.items() if name not in UNSET}
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    env.update(extra)
    return env


def git(cwd: Path, *args: str, env: dict | None = None, check: bool = True) -> str:
    r = subprocess.run([*GIT, *args], cwd=cwd, env=env or clean_env(), capture_output=True,
                       text=True)
    if check and r.returncode != 0:
        raise Failed(f"`git {' '.join(args)}` failed in {cwd}: {r.stderr.strip()}")
    return r.stdout


def rev(cwd: Path, name: str) -> str | None:
    r = subprocess.run([*GIT, "rev-parse", "--verify", "--quiet", name], cwd=cwd,
                       env=clean_env(), capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None


def blob_id(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def canonical(value) -> bytes:
    """As safe_push.py's canonical(): keys sorted, no spaces, ASCII."""
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
                      allow_nan=False).encode("ascii")


def source_repo() -> Path:
    r = subprocess.run([*GIT, "rev-parse", "--show-toplevel"], env=clean_env(),
                       capture_output=True, text=True)
    if r.returncode != 0 or not r.stdout.strip():
        raise SystemExit(usage("run it inside the repository"))
    return Path(r.stdout.strip())


def usage(why: str) -> int:
    print(f"shadow_policy.py: {why}", file=sys.stderr)
    return 2


def commit_named(repo: Path, value: str, what: str) -> str | None:
    """None when `value` is a full SHA of a commit the repository holds; else why not."""
    if not FULL_SHA.fullmatch(value or ""):
        return f"{what} must be a full 40-hex commit SHA, not {value!r}"
    if rev(repo, f"{value}^{{commit}}") != value:
        return f"{what} {value} is not a commit this repository holds"
    return None


def fresh_dir(value: str) -> Path | str:
    """DIR, absolute and newly made; or why it cannot be."""
    out = Path(value).absolute()
    if os.path.lexists(out):
        return f"{out} exists: --out names a folder the run makes"
    try:
        out.mkdir()
    except OSError as e:
        return f"cannot make {out}: {e}"
    return out


# --------------------------------------------------------------------------------------
# Reading the report


class Reading(NamedTuple):
    verdict: str                 # "passed" or "refused"
    result: str                  # the summary's words
    cls: str | None              # the risk class step 4's "class" row gives
    kept_apart: str | None       # the step of a "check change kept apart" FAIL
    steps: list[dict]            # each ok, FAIL and skip: stage, outcome, name
    notes: list[dict]            # each note: stage, name, first line


def note_parts(rest: str) -> tuple[str, str]:
    """A note's name and its first line. A base pass's note is named up to BASE_PASS, since
    a check's name may hold ": " (negative: lake build); any other, up to the first ": "."""
    rest = TOOK.sub("", rest)
    at = rest.find(BASE_PASS)
    if at < 0:
        name, _, first = rest.partition(": ")
        return name, first
    name, after = rest[:at + len(BASE_PASS)], rest[at + len(BASE_PASS):]
    if after and not after.startswith(": "):
        raise Misread(f"an unreadable note: {rest!r}")
    return name, after[2:]


def read_report(text: str, code: int | None, base: str, tested: str) -> Reading:
    """The verdict in safe_push.py's printed report of a dry run of `tested` against
    `base`, which exited `code`; a Misread whenever it cannot be read as one."""
    if code not in (0, 1):
        raise Misread(f"safe_push.py exited {code}, neither 0 (passed) nor 1 (refused)")
    lines = text.split("\n")
    starts = [i for i, line in enumerate(lines) if line.startswith("Summary: ")]
    if len(starts) != 1:
        raise Misread("no summary line" if not starts else f"{len(starts)} summary lines")
    start = starts[0]
    end = next((j for j in range(start, len(lines)) if SUMMARY_END.search(lines[j])), None)
    m = SUMMARY.fullmatch("\n".join(lines[start:end + 1])) if end is not None else None
    if not m:
        raise Misread("the summary line is not one safe_push.py's summary() prints")
    mode, sha, against, result = m.groups()
    if (mode, sha, against) != (MODE, tested[:12], base[:12]):
        raise Misread(f"the summary is of a {mode} of {sha} against {against}, not a "
                      f"{MODE} of {tested[:12]} against {base[:12]}")
    rows, at = [], end + 1
    while at < len(lines) and not lines[at].startswith(LOGGED):
        row = ROW.fullmatch(lines[at])
        parts = ROW_REST.fullmatch(row.group(3)) if row else None
        if not parts:
            raise Misread(f"an unreadable row of the summary: {lines[at]!r}")
        rows.append((row.group(1), LABELS[row.group(2)], parts.group(1).rstrip(" "),
                     len(row.group(3))))
        at += 1
    if at == len(lines):
        raise Misread("the summary has no line saying where its log went")
    if any(line.strip() for line in lines[at + 1:]):
        raise Misread("the report goes on after its summary")
    if len({width for *_, width in rows}) > 1:
        raise Misread("the summary's rows are not of one width")
    # The stream: each step's line under its step's heading. Every row of the summary is a
    # line here, in the same order and under the same step; notes are in the stream alone.
    stage, events = None, []
    for line in lines[:start]:
        if HEADING.fullmatch(line):
            stage = line.split(".", 1)[0]
        elif m := STEP_LINE.fullmatch(line):
            events.append((stage, LABELS[m.group(1)], m.group(2)))
    stepped = [e for e in events if e[1] != "note"]
    if len(stepped) != len(rows):
        raise Misread(f"the summary has {len(rows)} rows, but the report streamed "
                      f"{len(stepped)} lines of ok, FAIL and skip")
    steps, cls = [], None
    for (stage, outcome, name, _), (under, said, rest) in zip(rows, stepped):
        if (under, said) != (stage, outcome) or not re.fullmatch(
                re.escape(name) + r"(?:: .*|  \(\d+\.\d s\))?", rest):
            raise Misread(f"the summary's row {stage} {outcome} {name!r} is not the "
                          f"streamed line {said} {rest!r}, under step {under}")
        steps.append({"stage": stage, "outcome": outcome, "name": name})
        if (stage, outcome, name) == ("4", "ok", "class"):
            found = re.match(r"class: (R[0-5]),", rest)
            if not found:
                raise Misread(f"step 4's class line names no class: {rest!r}")
            cls = found.group(1)
    notes = []
    for under, said, rest in events:
        if said == "note":
            if under is None:
                raise Misread(f"a note before any step's heading: {rest!r}")
            name, first = note_parts(rest)
            notes.append({"stage": under, "name": name, "first": first})
    failed = [s for s in steps if s["outcome"] == "FAIL"]
    if code == 0:
        if result != PASSED:
            raise Misread(f"exit 0, but the summary says {result!r}")
        if failed:
            raise Misread(f"exit 0, but {failed[0]['name']!r} failed")
        verdict = "passed"
    else:
        if not (result.startswith("refused (") and result.endswith(")")):
            raise Misread(f"exit 1, but the summary says {result!r}")
        if not failed:
            raise Misread(f"a refusal with no step failing, so not the policy's verdict but "
                          f"the harness's or the environment's: {result}")
        verdict = "refused"
    kept = next((s["stage"] for s in failed if s["name"] == KEPT_APART), None)
    return Reading(verdict, result, cls, kept, steps, notes)


def check_record(record, reading: Reading, base: str, tested: str) -> None:
    """A pass leaves the pre-flight's record (make_record), whose steps of 2 to 4 and whose
    notes must be the report's."""
    if not isinstance(record, dict) or (record.get("sha"), record.get("base")) != (tested, base):
        raise Misread("the pre-flight passed, but left no record of this commit and base")
    ours = [[s["stage"], s["name"], s["outcome"]] for s in reading.steps
            if s["stage"] in ("2", "3", "4")]
    theirs = [s[:3] if isinstance(s, list) else s for s in record.get("steps") or []]
    if theirs != ours:
        raise Misread("the pre-flight's record holds other steps than its report")
    if (record.get("notes") or []) != [[n["name"], n["first"]] for n in reading.notes]:
        raise Misread("the pre-flight's record holds other notes than its report")


# --------------------------------------------------------------------------------------
# Judging a commit


def policy_blobs(source: Path, base: str, tested: str) -> dict:
    found: dict = {path: rev(source, f"{base}:{path}") for path in POLICY_FILES}
    found[f"{REGISTRY}/"] = rev(source, f"{base}:{REGISTRY}")
    blob = blob_id(Path(__file__).read_bytes())
    whose = ("base" if blob == rev(source, f"{base}:{DRIVER}") else
             "tested" if blob == rev(source, f"{tested}:{DRIVER}") else "neither")
    found["driver"] = {"blob": blob, "from": whose}
    return found


def runtime(repo: Path, lean_ran: bool) -> dict:
    """What ran it. Lean's version is asked only once Lean has run, since elan would
    otherwise fetch the toolchain to answer; lean-toolchain names it either way."""
    path = str(Path.home() / ".elan" / "bin") + os.pathsep + os.environ.get("PATH", "")

    def first_line(cmd: list[str], cwd: Path | None = None) -> str | None:
        try:
            r = subprocess.run(cmd, cwd=cwd, env=clean_env(PATH=path), capture_output=True,
                               text=True, timeout=120)
        except (OSError, subprocess.TimeoutExpired):
            return None
        said = r.stdout.strip().splitlines()
        return said[0] if r.returncode == 0 and said else None

    toolchain = repo / "lean-toolchain"
    image = {"os": os.environ.get("ImageOS"), "version": os.environ.get("ImageVersion")}
    return {
        "python": platform.python_version(),
        "git": first_line(["git", "--version"]),
        "elan": first_line(["elan", "--version"]),
        "lean": {"toolchain": toolchain.read_text().strip() if toolchain.is_file() else None,
                 "version": first_line(["lean", "--version"], repo) if lean_ran else None},
        "os": f"{platform.system()} {platform.release()}",
        "runner_image": image if any(image.values()) else None,
    }


def pinned_origin(source: Path, base: str, tested: str, out: Path) -> Path:
    """DIR/origin.git, whose main is the base and which holds nothing else; DIR/repo, its
    clone, with the tested commit pushed in under a ref of its own and checked out."""
    origin, repo = out / "origin.git", out / "repo"
    git(out, "init", "--bare", "--quiet", str(origin))
    git(origin, "symbolic-ref", "HEAD", "refs/heads/main")
    git(source, "push", "--quiet", "--no-verify", str(origin), f"{base}:refs/heads/main")
    git(out, "clone", "--quiet", str(origin), str(repo))
    git(source, "push", "--quiet", "--no-verify", str(repo), f"{tested}:refs/shadow/tested")
    git(repo, "-c", "advice.detachedHead=false", "checkout", "--quiet", "--detach", tested)
    if (rev(repo, "HEAD"), rev(repo, "refs/remotes/origin/main")) != (tested, base):
        raise Failed(f"{repo} is not the tested commit with origin's main the base")
    return repo


def harness_of(source: Path, base: str, out: Path) -> Path:
    """The base's scripts/, taken out of Git into DIR/harness, as queue-integrity takes the
    queue judge's; held to the base's blobs, since an export attribute could change what
    `git archive` writes."""
    harness = out / "harness"
    harness.mkdir()
    tar = subprocess.run([*GIT, "archive", "--format=tar", base, "scripts"], cwd=source,
                         env=clean_env(), capture_output=True)
    if tar.returncode != 0:
        raise Failed(f"`git archive {base} scripts` failed: {tar.stderr.decode(errors='replace')}")
    untar = subprocess.run(["tar", "-xf", "-", "-C", str(harness)], input=tar.stdout,
                           capture_output=True)
    if untar.returncode != 0:
        raise Failed(f"the base's scripts/ could not be unpacked: "
                     f"{untar.stderr.decode(errors='replace')}")
    for path in POLICY_FILES:
        copy, blob = harness / path, rev(source, f"{base}:{path}")
        if (blob_id(copy.read_bytes()) if copy.is_file() else None) != blob:
            raise Failed(f"the harness's {path} is not the base's")
    return harness / "scripts" / "safe_push.py"


def run_preflight(script: Path, repo: Path, tested: str, out: Path) -> tuple[int, str]:
    """safe_push.py --dry-run, as the launcher runs it, its output streamed to the console
    and to DIR/preflight.log as it comes, and kept to be read."""
    cmd = [sys.executable, str(script), "--dry-run", "--commit", tested]
    env = clean_env(STOICHEIA_PUSH_LOG=str(out / "state" / "pushes.log"))
    print(f"shadow_policy.py: main's pre-flight: {' '.join(cmd)} (in {repo})", flush=True)
    chunks = []
    with open(out / "preflight.log", "wb") as log:
        proc = subprocess.Popen(cmd, cwd=repo, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        for raw in proc.stdout:
            sys.stdout.buffer.write(raw)
            sys.stdout.flush()
            log.write(raw)
            chunks.append(raw)
        code = proc.wait()
    return code, b"".join(chunks).decode("utf-8", errors="replace")


def judge(source: Path, base: str, tested: str, out: Path, repository: str, event: str,
          pr_head: str | None) -> dict:
    """Judge `tested` against `base` by the base's pre-flight, into `out`, which exists
    and is empty; the verdict, also written to out/verdict.json."""
    verdict: dict = {
        "schema": SCHEMA, "repository": repository, "event": event, "base": base,
        "tested": tested, "tested_tree": rev(source, f"{tested}^{{tree}}"),
        "pr_head": pr_head,
        "pr_head_tree": rev(source, f"{pr_head}^{{tree}}") if pr_head else None,
        "policy": policy_blobs(source, base, tested), "exit": None,
        "verdict": "error", "result": None, "class": None, "kept_apart": None,
        "base_pass_notes": [], "pinned_values": False, "steps": [], "notes": [],
        "record": None,
    }
    why = None
    repo = out / "repo"
    try:
        repo = pinned_origin(source, base, tested, out)
        script = harness_of(source, base, out)
        code, text = run_preflight(script, repo, tested, out)
        verdict["exit"] = code
        reading = read_report(text, code, base, tested)
        if reading.verdict == "passed":
            path = out / "state" / "preflight" / f"{tested}-{base}.json"
            try:
                record = json.loads(path.read_text())
            except (OSError, UnicodeError, json.JSONDecodeError):
                record = None
            check_record(record, reading, base, tested)
            verdict["record"] = record
        verdict.update({
            "verdict": reading.verdict, "result": reading.result, "class": reading.cls,
            "kept_apart": reading.kept_apart, "steps": reading.steps, "notes": reading.notes,
            "base_pass_notes": [n for n in reading.notes if n["name"].endswith(BASE_PASS)],
            "pinned_values": any(n["name"] == PINNED for n in reading.notes),
        })
    except Failed as e:
        why = str(e)
    except Exception as e:      # whatever went wrong, the verdict is written, and is "error"
        why = f"{type(e).__name__}: {e}"
    lean_ran = any(s["stage"] == "4" and s["name"] not in ("class", "check list",
                                                         "full local checks")
                   for s in verdict["steps"])
    verdict["runtime"] = runtime(repo, lean_ran)
    (out / "verdict.json").write_bytes(canonical(verdict))
    if why is not None:
        (out / "why.txt").write_text(why + "\n")
        print(f"\nshadow_policy.py: verdict error: {why}", flush=True)
    else:
        print(f"\nshadow_policy.py: verdict {verdict['verdict']}"
              + (f", kept apart at step {verdict['kept_apart']}" if verdict["kept_apart"]
                 else ""), flush=True)
    print(f"shadow_policy.py: {out / 'verdict.json'}", flush=True)
    return verdict


# --------------------------------------------------------------------------------------
# The planted cases


# The registry entry of check_links.py, whose name step 4 reports (read from it at the
# base, never written here a second time); and the decisions page that test_safe_push's
# decision() adds its line to, as safe_push.py names it (DECISIONS), read from the base.
LINKS_ENTRY = "checks/18-check-links.toml"
LINKS = "{links}"
MAIN_GUARD = 'if __name__ == "__main__":\n'
MISSING = "no-such-page.md"
IDENTITY = ("Shadow plant", "shadow-plant@invalid")

# Each plant: what it changes, its kind, the case of scripts/test_safe_push.py it mirrors,
# and what main's pre-flight must find. An expectation: the verdict; the step at which a
# check change is kept apart, or null; the notes that must appear, by step and name; the
# rows that must appear and those that must not, by step, outcome and name; and whether no
# step may fail. LINKS in a name stands for the name of the base's LINKS_ENTRY.
PLANTS = {
    "control": {
        "change": "a line appended to docs/WORKFLOW.md, outside its generated region",
        "kind": "a clean change of R3, so that step 4 runs in full",
        "mirrors": "good_commit, on a guide of R3 in place of docs/reading.md (R0)",
        "expect": {"verdict": "passed", "kept_apart": None, "notes": [],
                   "steps": [["4", "ok", "check list"]],
                   "absent": [["4", "skip", "full local checks"]], "no_fail": True},
    },
    "weakened-fidelity": {
        "change": "check_fidelity.py exits 0; a comment in Elements/BookI/Prop01.lean, so "
                  "that a review record goes stale",
        "kind": "a weakened script, kept apart at step 3",
        "mirrors": "test_weakened_check_with_the_code_it_would_catch_refused",
        "expect": {"verdict": "refused", "kept_apart": "3",
                   "notes": [["3", "review records" + BASE_PASS]],
                   "steps": [["3", "FAIL", KEPT_APART]], "absent": [], "no_fail": False},
    },
    "loosened-renderer": {
        "change": 'render.py accepts the stage "anything", and docs/program.toml uses it',
        "kind": "a forbidden combination of check and content, kept apart at step 3",
        "mirrors": "test_renderer_validation_loosened_with_content_is_kept_apart",
        "expect": {"verdict": "refused", "kept_apart": "3",
                   "notes": [["3", "render.py" + BASE_PASS]],
                   "steps": [["3", "FAIL", KEPT_APART]], "absent": [], "no_fail": False},
    },
    "dropped-check": {
        "change": f"{LINKS_ENTRY} removed; a broken link added to docs/reading.md",
        "kind": "a dropped check, kept apart at step 4",
        "mirrors": "test_a_registry_entry_removed_with_judged_content_is_kept_apart",
        "expect": {"verdict": "refused", "kept_apart": "4",
                   "notes": [["4", LINKS + BASE_PASS]],
                   "steps": [["4", "ok", "check list"], ["4", "FAIL", KEPT_APART]],
                   "absent": [], "no_fail": False},
    },
    "weakened-links": {
        "change": "check_links.py exits 0; a broken link added to docs/reading.md",
        "kind": "a weakened script, kept apart at step 4",
        "mirrors": "test_kept_apart_counts_verdicts_not_freshness",
        "expect": {"verdict": "refused", "kept_apart": "4",
                   "notes": [["4", LINKS + BASE_PASS]],
                   "steps": [["4", "ok", "check list"], ["4", "FAIL", KEPT_APART]],
                   "absent": [], "no_fail": False},
    },
    "renderer-freshness": {
        "change": "render.py's wording changed; a line added to docs/reading.md",
        "kind": "the legitimate exception for stale pages (FRESHNESS)",
        "mirrors": "test_renderer_change_with_content_is_not_kept_apart",
        "expect": {"verdict": "passed", "kept_apart": None,
                   "notes": [["3", "generated pages" + BASE_PASS]],
                   "steps": [["3", "ok", "generated pages (the commit's checks)"],
                             ["4", "ok", "check list"]],
                   "absent": [["4", "skip", "full local checks"]], "no_fail": True},
    },
}


def read(tree: Path, path: str) -> str:
    return (tree / path).read_bytes().decode("utf-8")


def write(tree: Path, path: str, text: str) -> None:
    (tree / path).write_bytes(text.encode("utf-8"))


def replaced(tree: Path, path: str, old: str, new: str) -> None:
    """`old`, which must stand exactly once in `path`, made `new`, as test_safe_push's
    replaced() makes it: a plant whose anchor is gone fails, never plants nothing."""
    text = read(tree, path) if (tree / path).is_file() else ""
    if text.count(old) != 1:
        raise PlantError(f"{path}: expected one {old!r}, found {text.count(old)}")
    write(tree, path, text.replace(old, new))


def appended(tree: Path, path: str, text: str) -> None:
    if not (tree / path).is_file():
        raise PlantError(f"{path} is not a file at the base")
    write(tree, path, read(tree, path) + text)


def broken_link(tree: Path) -> None:
    if (tree / "docs" / MISSING).exists():
        raise PlantError(f"docs/{MISSING} exists, so a link to it is not broken")
    appended(tree, "docs/reading.md",
             f"\nA link for the test: [a page that is not there]({MISSING}).\n")


def plant_control(tree: Path) -> None:
    text = read(tree, "docs/WORKFLOW.md")
    if text.rfind("<!-- /checks -->") < text.rfind("<!-- checks -->"):
        raise PlantError("docs/WORKFLOW.md ends inside its generated region")
    appended(tree, "docs/WORKFLOW.md", "\nA line for the test.\n")


def plant_weakened_fidelity(tree: Path) -> None:
    replaced(tree, "scripts/check_fidelity.py", MAIN_GUARD, MAIN_GUARD + "    sys.exit(0)\n")
    appended(tree, "Elements/BookI/Prop01.lean", "\n-- A comment for the test.\n")


def plant_loosened_renderer(tree: Path) -> None:
    replaced(tree, "scripts/render.py", 'PROGRAM_STAGES = ("brief",',
             'PROGRAM_STAGES = ("anything", "brief",')
    text = read(tree, "docs/program.toml")
    stage = re.search(r'(?m)^stage = "[^"\n]*"$', text)
    if not stage:
        raise PlantError("docs/program.toml: no stage line")
    write(tree, "docs/program.toml",
          text[:stage.start()] + 'stage = "anything"' + text[stage.end():])


def plant_dropped_check(tree: Path) -> None:
    if not (tree / LINKS_ENTRY).is_file():
        raise PlantError(f"{LINKS_ENTRY} is not a file at the base")
    (tree / LINKS_ENTRY).unlink()
    broken_link(tree)


def plant_weakened_links(tree: Path) -> None:
    replaced(tree, "scripts/check_links.py", MAIN_GUARD, MAIN_GUARD + "    sys.exit(0)\n")
    broken_link(tree)


def plant_renderer_freshness(tree: Path) -> None:
    replaced(tree, "scripts/render.py", '"This page keeps three things apart."',
             '"This page keeps three things apart, for the test."')
    appended(tree, "docs/reading.md", "\nA line for the test.\n")


CHANGES = {
    "control": plant_control,
    "weakened-fidelity": plant_weakened_fidelity,
    "loosened-renderer": plant_loosened_renderer,
    "dropped-check": plant_dropped_check,
    "weakened-links": plant_weakened_links,
    "renderer-freshness": plant_renderer_freshness,
}

# Which of the paths given are protected, and where decisions go, by the base's own
# safe_push.py (is_protected, DECISIONS), loaded from the plant's scripts/, which no plant
# changes.
PROTECTION = """
import json, sys
sys.path.insert(0, sys.argv[1])
import safe_push
print(json.dumps({"decisions": safe_push.DECISIONS,
                  "protected": [p for p in sys.argv[2:] if safe_push.is_protected(p)]}))
"""


def regenerated(tree: Path, base: str) -> tuple[list[str], str]:
    """The plant with the pages its own render.py regenerates, all staged, as
    test_safe_push's regenerated_commit() makes one; the protected paths it changes, and
    the decisions page."""
    r = subprocess.run([sys.executable, "scripts/render.py"], cwd=tree,
                       env=clean_env(PYTHONDONTWRITEBYTECODE="1"), capture_output=True,
                       text=True)
    if r.returncode != 0:
        raise PlantError(f"the plant's render.py failed:\n{(r.stdout + r.stderr)[-3000:]}")
    git(tree, "add", "-A")
    changed = [p for p in git(tree, "diff", "--cached", "--name-only", "--no-renames", "-z",
                              base).split("\0") if p]
    if {"scripts/safe_push.py", "scripts/heath.py"} & set(changed):
        raise PlantError("a plant may not change the harness it is judged by")
    asked = subprocess.run([sys.executable, "-I", "-c", PROTECTION, str(tree / "scripts"),
                            *changed], cwd=tree, env=clean_env(PYTHONDONTWRITEBYTECODE="1"),
                           capture_output=True, text=True)
    try:
        answer = json.loads(asked.stdout)
        return list(answer["protected"]), str(answer["decisions"])
    except (ValueError, KeyError, TypeError):
        raise PlantError(f"the base's safe_push.py could not name the protected paths: "
                         f"{asked.stderr.strip()[-2000:]}") from None


def decision(paths: list[str]) -> str:
    """test_safe_push's decision() line, naming each protected path the plant changes."""
    named = [f"`{p}`" for p in paths]
    listed = named[0] if len(named) == 1 else ", ".join(named[:-1]) + " and " + named[-1]
    verb = "is" if len(named) == 1 else "are"
    return f"\n- **A decision for the test.** {listed} {verb} changed for the test.\n"


def build_plant(source: Path, name: str, base: str, tree: Path) -> str:
    """The planted commit on the base, made in a detached worktree of the repository that
    is removed afterwards, and committed under a fixed identity, dated as the base is, so
    that one plant on one base is always one commit."""
    git(source, "worktree", "add", "--detach", "--quiet", str(tree), base)
    try:
        CHANGES[name](tree)
        protected, decisions = regenerated(tree, base)
        if protected:
            appended(tree, decisions, decision(protected))
            again, _ = regenerated(tree, base)
            if set(again) - set(protected):
                raise PlantError(f"regenerating changed protected paths no decision names: "
                                 f"{sorted(set(again) - set(protected))}")
        changed = git(tree, "diff", "--cached", "--name-status", "--no-renames", base)
        print(f"shadow_policy.py: the plant {name} changes:\n{changed.rstrip()}", flush=True)
        date = git(source, "log", "-1", "--format=%cI", base).strip()
        env = clean_env(GIT_AUTHOR_NAME=IDENTITY[0], GIT_AUTHOR_EMAIL=IDENTITY[1],
                        GIT_COMMITTER_NAME=IDENTITY[0], GIT_COMMITTER_EMAIL=IDENTITY[1],
                        GIT_AUTHOR_DATE=date, GIT_COMMITTER_DATE=date)
        git(tree, "-c", "commit.gpgsign=false", "commit", "--quiet", "--no-verify", "-m",
            f"Shadow plant {name}: {PLANTS[name]['change']}", env=env)
        sha = rev(tree, "HEAD")
        if not sha or rev(tree, "HEAD^") != base:
            raise PlantError("the planted commit is not a child of the base")
        return sha
    finally:
        git(source, "worktree", "remove", "--force", str(tree), check=False)
        if tree.exists():
            shutil.rmtree(tree, ignore_errors=True)
            git(source, "worktree", "prune", check=False)


def links_name(source: Path, base: str) -> str:
    text = git(source, "show", f"{base}:{LINKS_ENTRY}", check=False)
    try:
        name = tomllib.loads(text).get("name")
    except tomllib.TOMLDecodeError:
        name = None
    if not isinstance(name, str) or not name:
        raise PlantError(f"the base's {LINKS_ENTRY} names no check")
    return name


def resolved(expect: dict, links: str) -> dict:
    def name(text):
        return text.replace(LINKS, links) if isinstance(text, str) else text
    return {key: [[name(x) for x in item] for item in value] if isinstance(value, list)
            else value for key, value in expect.items()}


def compare(expect: dict, got: dict) -> list[str]:
    """How the verdict `got` departs from the resolved expectation `expect`."""
    misses = []
    if got.get("verdict") != expect["verdict"]:
        misses.append(f"verdict {got.get('verdict')}, not {expect['verdict']}")
    if got.get("kept_apart") != expect["kept_apart"]:
        misses.append(f"kept apart at {got.get('kept_apart')}, not {expect['kept_apart']}")
    notes = {(n["stage"], n["name"]) for n in got.get("notes", [])}
    steps = {(s["stage"], s["outcome"], s["name"]) for s in got.get("steps", [])}
    misses += [f"no note {name!r} at step {stage}" for stage, name in expect["notes"]
               if (stage, name) not in notes]
    misses += [f"no row {stage} {outcome} {name!r}" for stage, outcome, name in expect["steps"]
               if (stage, outcome, name) not in steps]
    misses += [f"the row {stage} {outcome} {name!r}" for stage, outcome, name in expect["absent"]
               if (stage, outcome, name) in steps]
    if expect["no_fail"]:
        misses += [f"{s['name']!r} failed at step {s['stage']}" for s in got.get("steps", [])
                   if s["outcome"] == "FAIL"]
    return misses


def expectation_problems(name: str, plant: dict) -> list[str]:
    """Why the plant's entry is not well formed; none when it is."""
    problems = []
    if set(plant) != {"change", "kind", "mirrors", "expect"} or \
            not all(isinstance(plant[k], str) and plant[k] for k in ("change", "kind", "mirrors")):
        return [f"{name}: not an entry of change, kind, mirrors and expect"]
    e = plant["expect"]
    if set(e) != {"verdict", "kept_apart", "notes", "steps", "absent", "no_fail"}:
        return [f"{name}: an expectation of other fields"]
    stage = re.compile(r"\d")

    def named(text) -> bool:
        return isinstance(text, str) and bool(text) and "{" not in text.replace(LINKS, "")

    if e["verdict"] not in ("passed", "refused"):
        problems.append(f"{name}: verdict {e['verdict']!r}")
    if e["kept_apart"] not in (None, "3", "4"):
        problems.append(f"{name}: kept apart at {e['kept_apart']!r}")
    if e["verdict"] == "passed" and (e["kept_apart"] is not None or e["no_fail"] is not True):
        problems.append(f"{name}: a pass with a check kept apart, or a step failing")
    if e["verdict"] == "refused" and (e["kept_apart"] is None or e["no_fail"] is not False
                                      or [e["kept_apart"], "FAIL", KEPT_APART] not in e["steps"]):
        problems.append(f"{name}: a refusal not kept apart by its own row")
    for note in e["notes"]:
        if not (isinstance(note, list) and len(note) == 2 and isinstance(note[0], str)
                and stage.fullmatch(note[0]) and named(note[1])):
            problems.append(f"{name}: a note {note!r}")
    for row in e["steps"] + e["absent"]:
        if not (isinstance(row, list) and len(row) == 3 and isinstance(row[0], str)
                and stage.fullmatch(row[0]) and row[1] in ("ok", "FAIL", "skip")
                and named(row[2])):
            problems.append(f"{name}: a row {row!r}")
    if not isinstance(e["no_fail"], bool):
        problems.append(f"{name}: no_fail {e['no_fail']!r}")
    return problems


# --------------------------------------------------------------------------------------
# The self-test


TESTED, BASE = "3f" * 20, "c0" * 20


class Printed:
    """A report printed as safe_push.py's Report.add, Report.heading and summary() print
    one, to the line: the format the reader is held to, here. The self-test reads the
    checkout's own Report and summary() beside it, when there is one."""

    def __init__(self):
        self.lines: list[str] = []
        # As safe_push's Step: stage, name, outcome, seconds, detail.
        self.steps: list[tuple] = []

    def heading(self, text):
        self.lines += ["", text]

    def add(self, stage, name, outcome, detail="", seconds=None):
        self.steps.append((stage, name, outcome, seconds, detail))
        took = f"  ({seconds:.1f} s)" if seconds is not None else ""
        label = {"ok": "ok  ", "FAIL": "FAIL", "skip": "skip", "note": "note"}[outcome]
        first, *rest = (detail or "").splitlines() or [""]
        self.lines.append(f"  {label}  {name}: {first}{took}" if first
                          else f"  {label}  {name}{took}")
        self.lines += [f"        {line}" for line in rest]

    def say(self, text):
        self.lines += text.split("\n")

    def summary(self, result):
        self.lines += ["", f"Summary: {MODE} of {TESTED[:12]} against origin/main "
                           f"{BASE[:12]}: {result} (1234 s)"]
        timed = [s for s in self.steps if s[2] in ("ok", "FAIL", "skip")]
        width = max((len(s[1]) for s in timed), default=10)
        for stage, name, outcome, seconds, _ in timed:
            took = f"{seconds:8.1f} s" if seconds is not None else " " * 10
            self.lines.append(f"  {stage}  {outcome:4}  {name:<{width}}  {took}")
        self.lines.append("Logged to /home/runner/work/_temp/shadow/state/pushes.log")

    def text(self):
        return "\n".join(self.lines) + "\n"


def opening(rep, say):
    say(f"safe_push: {MODE} of {TESTED} from /home/runner/work/_temp/shadow/repo")
    rep.heading("1. Preconditions")
    rep.add("1", "commit", "ok", f'{TESTED[:12]} "A commit" (read from git, not from the '
            "working tree)")
    rep.add("1", "fetch", "ok", "git fetch origin (/home/runner/work/_temp/shadow/origin.git)",
            0.4)
    rep.add("1", "harness", "ok", "origin/main's scripts/safe_push.py (blob 0123456789ab)")
    rep.add("1", "fast-forward", "ok", f"origin/main {BASE[:12]} is an ancestor: 1 commit to "
            "propose")
    rep.add("1", "tags and releases", "ok", "none is made: tags, releases and their notes "
            "stay manual, with the owner's OK")
    rep.add("1", "pre-push hook", "note", "not installed here (sh scripts/install_hooks.sh)")
    rep.heading("2. Secret scan")
    rep.add("2", "secret scan", "ok", "nothing found in the 3 files and 1 commit the push "
            "brings", 1.2)
    rep.heading("3. Invariant guards against origin/main")
    rep.add("3", "paths", "ok", "every path of 1 tree keeps origin/main's standard", 0.3)
    say("  in a fresh worktree of the commit, /tmp/stoicheia-push-x/check")


def full_checks(rep, cls="R3"):
    rep.heading("4. The full local checks (docs/WORKFLOW.md, section 8)")
    rep.add("4", "class", "ok", f"{cls}, Checks, by origin/main's scripts/risk.py (blob "
            "0123456789ab): docs/WORKFLOW.md", 0.2)
    rep.add("4", "check list", "ok", "27 checks: the 26 of origin/main's registry, checks/ "
            "(tree 0123456789ab), as its scripts/registry.py (blob 0123456789ab) reads them, "
            "then the model job's", 0.1)


def dry_push(rep):
    rep.heading("5. Push")
    rep.add("5", "git push", "skip", f"dry run: would push {TESTED[:12]} to nowhere: no "
            "--branch given")


def case_pass(rep, say):
    opening(rep, say)
    rep.add("3", "protected paths", "ok", "none changed")
    rep.add("3", "review records", "ok", "check_fidelity.py passes on the commit as "
            "committed: no record stale", 2.5)
    rep.add("3", "generated pages", "ok", "render.py changes nothing on the commit as "
            "committed", 6.1)
    full_checks(rep)
    rep.add("4", "lake build", "ok", "", 812.4)
    rep.add("4", "git status --porcelain is empty", "ok", "", 0.1)
    rep.add("4", "negative: python3 scripts/negative_tests.py", "ok", "", 301.0)
    dry_push(rep)
    return 0, PASSED


def case_kept_apart_3(rep, say):
    opening(rep, say)
    rep.add("3", "protected paths", "ok", "changed, each named in docs/briefs/0002-decisions.md: "
            "scripts/check_fidelity.py; the pull request carries the label security-review")
    rep.add("3", "review records" + BASE_PASS, "note", "check_fidelity.py fails on the commit "
            "as committed:\n    review/I/01.toml: stale, its Lean changed", 2.4)
    rep.add("3", "generated pages" + BASE_PASS, "ok", "render.py changes nothing on the "
            "commit as committed", 5.9)
    rep.add("3", "review records (the commit's checks)", "ok", "check_fidelity.py passes on "
            "the commit as committed: no record stale", 0.3)
    rep.add("3", "generated pages (the commit's checks)", "ok", "render.py changes nothing on "
            "the commit as committed", 5.8)
    rep.add("3", KEPT_APART, "FAIL", "origin/main's checks fail on the commit (review "
            "records), and it changes what they judge as well as the checks: "
            "Elements/BookI/Prop01.lean. Land the check change first")
    say("\nREFUSED: the invariant guards refused: check change kept apart")
    return 1, "refused (the invariant guards refused: check change kept apart)"


def case_kept_apart_4(rep, say):
    opening(rep, say)
    rep.add("3", "generated pages" + BASE_PASS, "note", "stale: render.py, on the commit as "
            "committed, changes them:\n     M docs/WORKFLOW.md", 5.0)
    rep.add("3", "generated pages (the commit's checks)", "ok", "render.py changes nothing on "
            "the commit as committed", 5.1)
    full_checks(rep)
    rep.add("4", "lake build" + BASE_PASS, "ok", "", 790.2)
    rep.add("4", "python3 scripts/check_links.py" + BASE_PASS, "note", "full output in "
            "/x/logs/28.log\n    docs/reading.md:120: no-such-page.md: no such file", 1.1)
    rep.add("4", KEPT_APART, "FAIL", "origin/main's checks fail on the commit (python3 "
            "scripts/check_links.py), and it changes what they judge as well as the checks: "
            "docs/reading.md. Land the check change first")
    say("\nREFUSED: a check changed together with what it checks")
    return 1, "refused (a check changed together with what it checks)"


def case_pinned_pass(rep, say):
    opening(rep, say)
    rep.add("3", "review records" + BASE_PASS, "ok", "check_fidelity.py passes on the commit "
            "as committed: no record stale", 2.0)
    full_checks(rep, "R4")
    rep.add("4", "lake build" + BASE_PASS, "ok", "", 700.0)
    rep.add("4", "negative: lake build" + BASE_PASS, "note", "full output in /x/logs/31.log\n"
            "    error: the lock has 40 words, facts.json 41", 4.0)
    rep.add("4", PINNED, "note", "origin/main's checks fail on the commit (negative: lake "
            "build), and the only check inputs it changes are values pinned to the edition "
            "(Certificate/axioms.lock), which move with the content they pin: for the "
            "security review, which reads each law's code")
    rep.add("4", "lake build (the commit's checks)", "ok", "", 650.0)
    rep.add("4", "negative: lake build (the commit's checks)", "ok", "", 3.9)
    dry_push(rep)
    return 0, PASSED


def case_refused_unstepped(rep, say):
    opening(rep, say)
    say("\nREFUSED: lake is not on the PATH, nor in ~/.elan/bin: the full checks need it")
    return 1, "refused (lake is not on the PATH, nor in ~/.elan/bin: the full checks need it)"


# Each case: what reading it must give (None: a Misread, verdict "error").
CASES = {
    "a pass": (case_pass, {"verdict": "passed", "kept_apart": None, "class": "R3",
                           "base_pass_notes": [], "pinned_values": False}),
    "kept apart at step 3": (case_kept_apart_3, {
        "verdict": "refused", "kept_apart": "3", "class": None,
        "base_pass_notes": ["review records" + BASE_PASS], "pinned_values": False}),
    "kept apart at step 4": (case_kept_apart_4, {
        "verdict": "refused", "kept_apart": "4", "class": "R3",
        "base_pass_notes": ["generated pages" + BASE_PASS,
                            "python3 scripts/check_links.py" + BASE_PASS],
        "pinned_values": False}),
    "a pass with origin/main's checks failing and pinned values": (case_pinned_pass, {
        "verdict": "passed", "kept_apart": None, "class": "R4",
        "base_pass_notes": ["negative: lake build" + BASE_PASS], "pinned_values": True}),
    "a refusal with no step failing": (case_refused_unstepped, None),
}


def record_of(steps: list[tuple]) -> dict:
    """The record make_record() writes for these steps."""
    return {"sha": TESTED, "base": BASE,
            "steps": [[st, name, out, sec] for st, name, out, sec, _ in steps
                      if out in ("ok", "FAIL", "skip") and st in ("2", "3", "4")],
            "notes": [[name, (detail.splitlines() or [""])[0]] for _, name, out, _, detail
                      in steps if out == "note"]}


def outcome(text: str, code: int, record: dict | None = None) -> dict | None:
    """The reading's fields the cases name, or None for a Misread."""
    try:
        r = read_report(text, code, BASE, TESTED)
        if r.verdict == "passed" and record is not None:
            check_record(record, r, BASE, TESTED)
    except Misread:
        return None
    return {"verdict": r.verdict, "kept_apart": r.kept_apart, "class": r.cls,
            "base_pass_notes": [n["name"] for n in r.notes if n["name"].endswith(BASE_PASS)],
            "pinned_values": any(n["name"] == PINNED for n in r.notes)}


def checkout_safe_push():
    """The checkout's scripts/safe_push.py, beside this driver, as a module; None when
    there is none (the driver run from elsewhere)."""
    path = Path(__file__).resolve().parent / "safe_push.py"
    if not path.is_file():
        return None
    spec = importlib.util.spec_from_file_location("checkout_safe_push", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def real_text(module, scenario, logs: Path) -> tuple[int, str, list[tuple]]:
    """A case printed by the checkout's own Report and summary()."""
    out = io.StringIO()
    saved = os.environ.get("STOICHEIA_PUSH_LOG")
    os.environ["STOICHEIA_PUSH_LOG"] = str(logs / "pushes.log")
    try:
        with contextlib.redirect_stdout(out):
            rep = module.Report()
            code, result = scenario(rep, print)
            module.summary(rep, MODE, TESTED, BASE, result, "")
    finally:
        if saved is None:
            os.environ.pop("STOICHEIA_PUSH_LOG", None)
        else:
            os.environ["STOICHEIA_PUSH_LOG"] = saved
    return code, out.getvalue(), [tuple(s) for s in rep.steps]


def matrix_plants(text: str) -> list[str] | None:
    """The plants of the workflow's matrix, a flow list on one line, `plant: [a, b]`."""
    found = re.findall(r"(?m)^\s*plant:\s*\[([^\]\n]*)\]\s*$", text)
    return [p.strip() for p in found[0].split(",") if p.strip()] if len(found) == 1 else None


def self_test() -> int:
    failures: list[str] = []
    count = 0

    def check(label: str, got, want) -> None:
        nonlocal count
        count += 1
        if got != want:
            failures.append(f"{label}: got {got!r}, want {want!r}")

    # Each case, printed here in the format of Report and summary(); its steps and notes
    # read back as printed; its record checked, for a pass.
    printed = {}
    for label, (scenario, want) in CASES.items():
        rep = Printed()
        code, result = scenario(rep, rep.say)
        rep.summary(result)
        printed[label] = (code, rep.text(), rep.steps)
        check(label, outcome(rep.text(), code, record_of(rep.steps)), want)
        if want is not None:
            r = read_report(rep.text(), code, BASE, TESTED)
            check(f"{label}, its rows", [(s["stage"], s["outcome"], s["name"]) for s in r.steps],
                  [(st, out, name) for st, name, out, _, _ in rep.steps if out != "note"])
            check(f"{label}, its notes", [(n["stage"], n["name"], n["first"]) for n in r.notes],
                  [(st, name, (d.splitlines() or [""])[0]) for st, name, out, _, d in rep.steps
                   if out == "note"])
    # The planted misreadings, each "error".
    code, text, steps = printed["a pass"]
    cut = text[:text.index("\nSummary: ")] + "\n"
    summary_at = text.index("\nSummary: ")
    stream, table = text[:summary_at], text[summary_at:]
    misreadings = {
        "no summary line": (cut, 0),
        "an exit of 2": (text, 2),
        "a summary row missing from the stream": (
            stream.replace("\n  ok    lake build  (812.4 s)", "", 1) + table, 0),
        "an exit of 1 on a pass": (text, 1),
        "a summary of another commit": (text.replace(f"of {TESTED[:12]} against",
                                                     f"of {BASE[:12]} against"), 0),
        "two summaries": (text + table.lstrip("\n"), 0),
        "a pass with a step failing": (
            stream.replace("  ok    lake build  (812.4 s)", "  FAIL  lake build  (812.4 s)")
            + table.replace("  4  ok    lake build ", "  4  FAIL  lake build "), 0),
        "a row under another step": (stream.replace("\n2. Secret scan", "\n3. Secret scan")
                                     + table, 0),
    }
    for label, (planted, planted_code) in misreadings.items():
        check(f"misreading: {label}", outcome(planted, planted_code, record_of(steps)), None)
    short = record_of(steps)
    short["steps"] = short["steps"][:-1]
    check("misreading: a record that disagrees with the report", outcome(text, 0, short), None)
    check("misreading: a pass with no record", outcome(text, 0, {}), None)
    # The same cases printed by the checkout's own Report and summary(): a change to their
    # format shows here before it turns a push's verdict into "error".
    module = checkout_safe_push()
    if module is None:
        # The self-test runs from a checkout, where safe_push.py stands beside the driver:
        # without it, the check that its format is still the one read here would be lost.
        check("the checkout's safe_push.py, beside the driver", "missing", "present")
    else:
        with tempfile.TemporaryDirectory(prefix="shadow-self-test-") as logs:
            for label, (scenario, want) in CASES.items():
                try:
                    code, text, steps = real_text(module, scenario, Path(logs))
                except Exception as e:      # an interface changed: the format is not read
                    failures.append(f"{label}, by the checkout's safe_push.py: "
                                    f"{type(e).__name__}: {e}")
                    continue
                check(f"{label}, by the checkout's safe_push.py",
                      outcome(text, code, record_of(steps)), want)
    # The plants: those of the workflow's matrix, each with a change and a well-formed
    # expectation; and compared, as the plant command compares them, with the cases.
    workflow = Path(__file__).resolve().parents[1] / WORKFLOW
    try:
        listed = matrix_plants(workflow.read_text())
    except OSError as e:
        listed = f"unreadable: {e}"
    check("the workflow's plant matrix", listed, list(PLANTS))
    check("the plants' changes", list(CHANGES), list(PLANTS))
    for name, plant in PLANTS.items():
        check(f"the plant {name}'s expectation", expectation_problems(name, plant), [])
    links = "python3 scripts/check_links.py"
    readings = {}
    for label in CASES:
        code, text, _ = printed[label]
        with contextlib.suppress(Misread):
            r = read_report(text, code, BASE, TESTED)
            readings[label] = {"verdict": r.verdict, "kept_apart": r.kept_apart,
                               "steps": r.steps, "notes": r.notes}
    for name, label, matches in (
            ("control", "a pass", True),
            ("weakened-fidelity", "kept apart at step 3", True),
            ("dropped-check", "kept apart at step 4", True),
            ("weakened-links", "kept apart at step 4", True),
            ("control", "kept apart at step 3", False),
            ("weakened-fidelity", "kept apart at step 4", False),
            ("renderer-freshness", "a pass", False)):
        got = compare(resolved(PLANTS[name]["expect"], links), readings[label])
        check(f"the plant {name} against {label}", not got, matches)
    # A plant whose anchor is gone, or stands twice, fails loudly.
    with tempfile.TemporaryDirectory(prefix="shadow-self-test-") as tmp:
        (Path(tmp) / "x.py").write_text("a\na\n")
        for old in ("b", "a"):
            try:
                replaced(Path(tmp), "x.py", old, "c")
                failed = False
            except PlantError:
                failed = True
            check(f"replaced() with {old!r} standing {'twice' if old == 'a' else 'nowhere'}",
                  failed, True)
    for failure in failures:
        print(f"  FAIL  {failure}")
    print(f"shadow_policy.py self-test: {count - len(failures)} of {count} checks passed"
          + ("" if not failures else f"; {len(failures)} failed"))
    return 1 if failures else 0


# --------------------------------------------------------------------------------------
# The commands


def judge_main(args) -> int:
    source = source_repo()
    for value, what in ((args.base, "--base"), (args.tested, "--tested"),
                        (args.pr_head, "--pr-head")):
        if value is not None and (why := commit_named(source, value, what)) is not None:
            return usage(why)
    if args.pr_head is not None and (
            rev(source, f"{args.tested}^1") != args.base
            or rev(source, f"{args.tested}^2") != args.pr_head
            or rev(source, f"{args.tested}^3") is not None):
        return usage(f"--pr-head {args.pr_head}: --tested is not a merge of it into --base")
    if args.base == args.tested:
        return usage("--base and --tested are one commit: there is nothing to judge")
    if subprocess.run([*GIT, "merge-base", "--is-ancestor", args.base, args.tested],
                      cwd=source, env=clean_env()).returncode != 0:
        return usage(f"--base {args.base} is not an ancestor of --tested {args.tested}")
    out = fresh_dir(args.out)
    if isinstance(out, str):
        return usage(out)
    verdict = judge(source, args.base, args.tested, out, args.repository, args.event,
                    args.pr_head)
    return 3 if verdict["verdict"] == "error" else 0


def plant_main(args) -> int:
    source = source_repo()
    if args.name not in PLANTS:
        return usage(f"no plant {args.name!r}: the plants are {', '.join(PLANTS)}")
    if (why := commit_named(source, args.base, "--base")) is not None:
        return usage(why)
    out = fresh_dir(args.out)
    if isinstance(out, str):
        return usage(out)
    expect, got, misses, code = PLANTS[args.name]["expect"], None, [], 3
    try:
        expect = resolved(expect, links_name(source, args.base))
        sha = build_plant(source, args.name, args.base, out / "plant")
        (out / "judge").mkdir()
        verdict = judge(source, args.base, sha, out / "judge", args.repository,
                        os.environ.get("GITHUB_EVENT_NAME", ""), None)
        got = {key: verdict[key] for key in ("tested", "verdict", "kept_apart", "class",
                                             "result", "base_pass_notes", "pinned_values")}
        got["failed"] = [s for s in verdict["steps"] if s["outcome"] == "FAIL"]
        if verdict["verdict"] == "error":
            misses = ["the judge erred: see judge/why.txt"]
        else:
            misses = compare(expect, verdict)
            code = 1 if misses else 0
    except Exception as e:      # a plant that cannot be built or judged is an error
        misses = [f"the plant could not be built or judged: {type(e).__name__}: {e}"]
    (out / "plant.json").write_bytes(canonical({"name": args.name, "expected": expect,
                                                "got": got, "ok": code == 0,
                                                "mismatches": misses}))
    print(f"shadow_policy.py: the plant {args.name} "
          + ("gave its expected verdict" if code == 0 else
             "did not give its expected verdict:\n  " + "\n  ".join(misses)), flush=True)
    return code


def main(argv=None) -> int:
    if sys.version_info < (3, 11):
        return usage(f"needs Python 3.11 or later; this is {sys.version.split()[0]}")
    parser = argparse.ArgumentParser(description="The shadow run of main's checking policy.")
    commands = parser.add_subparsers(dest="command", required=True)
    repository = os.environ.get("GITHUB_REPOSITORY", "")
    j = commands.add_parser("judge", help="judge a commit by the base's own pre-flight")
    j.add_argument("--base", required=True)
    j.add_argument("--tested", required=True)
    j.add_argument("--out", required=True)
    j.add_argument("--repository", default=repository)
    j.add_argument("--event", default=os.environ.get("GITHUB_EVENT_NAME", ""))
    j.add_argument("--pr-head")
    p = commands.add_parser("plant", help="build a planted case on the base, and judge it")
    p.add_argument("name", metavar="NAME", help=", ".join(PLANTS))
    p.add_argument("--base", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--repository", default=repository)
    commands.add_parser("self-test", help="the offline cases, in seconds")
    args = parser.parse_args(argv)
    if args.command == "judge":
        return judge_main(args)
    if args.command == "plant":
        return plant_main(args)
    return self_test()


if __name__ == "__main__":
    sys.exit(main())
