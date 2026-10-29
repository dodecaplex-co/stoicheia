#!/usr/bin/env python3
"""The cases of step 4's two passes at once (#609), in scripts/safe_push.py.

    python3 -I tests/test_concurrent_passes.py        # no Lean, no network

full_checks is put to stand-in checks, small Python commands, in a Git repository of the
test's own, whose commit changes a check input: tests/which.txt, which tells a stand-in the
pass it runs in. Run with one pass at a time and with two at once, the steps, the lines
printed (times, and the one line of the work between the rows, aside), the log files and
their bytes, the rows keep_apart judges on, and the exception are the same, the test's
temporary paths masked, the worktree a pass runs in among them, which differs by design:
when both passes pass; when origin/main's fails, noted; when the commit's fails, in the
checks and, separately, in the negative tests; when both fail; when keep_apart refuses
after origin/main's checks, the commit's rows and logs discarded and no negative test run;
when either pass's run() raises; and when a pass leaves its tree changed, the clean-tree
check refusing, or the at_commit that one after another begins the next pass with: after
step 3, after origin/main's checks, after its negative tests. The one difference, which is
stricter, is pinned: a tree the commit's checks leave changed, and that none of them
refuses, is refused before its negative tests at two passes and not at one. One pass
stays for a commit that changes no check input and for origin/main's pass taken from the
cache. At two the passes are shown to overlap, and at one never to. SIGINT and SIGTERM sent
while both passes run raise KeyboardInterrupt only once both passes' checks have ended,
no further step started, the handlers put back and the second worktree removed.
STOICHEIA_PASS_WORKERS is read, taken up to two, capped against the check and negative
workers by half the cores, said on the check list line, and refused unless a whole number
from 1. The work between the rows is timed piece by piece and said in one line, not a row.
Every order a case asserts is forced by marks the checks wait for, never by how long they
sleep: a check gives up waiting only after HOLD seconds, which a right run never comes
near. It runs alone in the sequence, since it starts processes of its own and runs two
passes at once.
"""

import contextlib
import io
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import types
import unittest
from pathlib import Path
from typing import NamedTuple
from unittest import mock

REPO = Path(__file__).resolve().parent.parent
SCRIPTS = REPO / "scripts"
sys.path.insert(0, str(SCRIPTS))
import safe_push  # noqa: E402

IDENTITY = ("-c", "user.name=Concurrent passes test", "-c",
            "user.email=concurrent-passes-test@example.invalid", "-c", "commit.gpgsign=false",
            "-c", "core.hooksPath=/dev/null")
BASE_PASS, OWN_PASS = safe_push.BASE_PASS, safe_push.OWN_PASS
BETWEEN = "  between the rows of step 4: "
TIME = re.compile(r"  \(\d+\.\d s\)$")
# How long a check waits for the mark it holds for before it gives up, failing: never
# reached when the run is right, so that a busy machine only slows a case.
HOLD = 60

# A stand-in check. It reads tests/which.txt, "main" with origin/main's copies and "commit"
# with the commit's own, and does what the plan given says for that pass: it notes the
# marks it sees, marks its start, holds until the mark given exists (if one is), prints a
# line to each stream, writes in the tree as asked, marks its end, and exits with the code
# given. Each mark is a file made with O_EXCL, named by the pass and the check, so a check
# run twice in one pass fails.
STAND_IN = f"""
import json, os, subprocess, sys, time
marks, name, plan = sys.argv[1], sys.argv[2], json.loads(sys.argv[3])
which = open(os.path.join("tests", "which.txt")).read().strip()
mine = plan.get(which, {{}})
me = which + "-" + "".join(c if c.isalnum() else "-" for c in name)
def mark(what, text=""):
    fd = os.open(os.path.join(marks, me + "." + what), os.O_WRONLY | os.O_CREAT | os.O_EXCL)
    os.write(fd, text.encode())
    os.close(fd)
mark("seen", "\\n".join(sorted(os.listdir(marks))))
mark("start")
hold = mine.get("hold", "")
given_up = time.monotonic() + {HOLD}
while hold and not os.path.exists(os.path.join(marks, hold)):
    if time.monotonic() > given_up:
        sys.exit(9)
    time.sleep(0.01)
print(name, "in", which, "says this on stdout")
print(name, "in", which, "says this on stderr", file=sys.stderr)
write = mine.get("write", "")
if write == "tracked":
    open("tracked.txt", "a").write("Written by a check.\\n")
elif write == "nested":
    os.mkdir("nested")
    subprocess.run(["git", "init", "-q", "nested"], check=True)
elif write == "flag":
    subprocess.run(["git", "update-index", "--skip-worktree", "tracked.txt"], check=True)
mark("end")
sys.exit(mine.get("code", 0))
"""

# Set by setUpModule: the test's repository, origin/main, the commit, and the check inputs
# it changes.
ROOT: Path
BASE = SHA = ""
INPUTS: list[tuple[str, str]] = []
TOP: Path


def git(root: Path, *args: str) -> str:
    return subprocess.run(["git", *IDENTITY, *args], cwd=root, check=True,
                          capture_output=True, text=True).stdout


def key(which: str, name: str) -> str:
    """A stand-in's marks' name, in the pass `which`, as STAND_IN makes it."""
    return which + "-" + "".join(c if c.isalnum() else "-" for c in name)


def setUpModule():
    """origin/main, with tests/which.txt "main" and tests/only-main.sh; and the commit,
    which says "commit" there, deletes only-main.sh and adds tests/only-commit.sh: three
    check inputs changed, nothing the checks judge."""
    global ROOT, BASE, SHA, INPUTS, TOP
    TOP = Path(tempfile.mkdtemp(prefix="concurrent-passes-repo-"))
    ROOT = TOP / "repo"
    (ROOT / "tests").mkdir(parents=True)
    git(ROOT, "init", "-q")
    (ROOT / ".gitignore").write_text("__pycache__/\n*.pyc\nout/\n/.lake\n")
    (ROOT / "tracked.txt").write_text("A tracked file.\n")
    (ROOT / "tests" / "which.txt").write_text("main\n")
    script = ROOT / "tests" / "only-main.sh"
    script.write_text("#!/bin/sh\necho only in origin/main\n")
    script.chmod(0o755)
    git(ROOT, "add", "-A")
    git(ROOT, "commit", "-q", "-m", "origin/main, for the test")
    BASE = git(ROOT, "rev-parse", "HEAD").strip()
    (ROOT / "tests" / "which.txt").write_text("commit\n")
    script.unlink()
    script = ROOT / "tests" / "only-commit.sh"
    script.write_text("#!/bin/sh\necho only in the commit\n")
    script.chmod(0o755)
    git(ROOT, "add", "-A")
    git(ROOT, "commit", "-q", "-m", "The commit, for the test")
    SHA = git(ROOT, "rev-parse", "HEAD").strip()
    INPUTS = [(s, p) for s, p in safe_push.changed_files(ROOT, BASE, SHA)
              if safe_push.under(p, safe_push.CHECK_INPUTS)]
    assert sorted(p for _, p in INPUTS) == ["tests/only-commit.sh", "tests/only-main.sh",
                                            "tests/which.txt"], INPUTS


def tearDownModule():
    shutil.rmtree(TOP, ignore_errors=True)


class Outcome(NamedTuple):
    raised: tuple[str, str] | None      # the exception's type and message, masked
    steps: list[tuple[str, str, str, str]]      # stage, name, outcome, detail masked
    printed: list[str]                  # the lines printed, times and BETWEEN aside, masked
    logs: dict[str, bytes]              # each log file's name and bytes
    judged: list[list[tuple[str, str]]]     # the rows keep_apart saw, at each call
    between: list[str]                  # the BETWEEN lines (not compared)
    marks: Path                         # the stand-ins' marks (not compared)
    parent: Path                        # where the worktrees were (not compared)
    at_raise: list[str]                 # the marks made as full_checks raised (not compared)


COMPARED = ("raised", "steps", "printed", "logs", "judged")


class Stand(unittest.TestCase):
    """full_checks on the test's repository, as step 4 runs it, in a throwaway worktree of
    the commit, with the sequence given as check_list gives it, NEGATIVE the stand-ins
    given, a logs folder of its own, and keep_apart watched; no cache, no sandbox."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="concurrent-passes-"))
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)
        self.runs = 0

    def marks(self) -> Path:
        self.runs += 1
        path = self.tmp / f"marks-{self.runs}"
        path.mkdir()
        return path

    def stand_in(self, marks: Path, name: str, main=None, commit=None):
        plan = {"main": dict(main or {}), "commit": dict(commit or {})}
        return (name, [sys.executable, "-I", "-S", "-c", STAND_IN, str(marks), name,
                       json.dumps(plan)])

    def sequence(self, marks: Path, passes: int, behave=None, overlap=(True, True),
                 names=("first", "second", "third"),
                 negatives=("negative: first", "negative: second")):
        """Stand-in checks `names` and negative tests `negatives`, each behaving in each
        pass as `behave` says (a name's (main, commit) plans); at two passes, the first
        check, and the first negative test, of each pass hold until the other pass's has
        started, as `overlap` asks, so that the passes are seen to run at once."""
        behave = behave or {}

        def step(name: str, together: bool):
            main, commit = (dict(plan) for plan in behave.get(name, ({}, {})))
            if passes == 2 and together:
                main.setdefault("hold", key("commit", name) + ".start")
                commit.setdefault("hold", key("main", name) + ".start")
            return self.stand_in(marks, name, main, commit)
        return ([step(n, overlap[0] and n == names[0]) for n in names],
                [step(n, overlap[1] and n == negatives[0]) for n in negatives])

    def full(self, steps, negative, passes: int, marks: Path, keep=None, before=None,
             inputs=None, on_raise: threading.Event | None = None) -> Outcome:
        """full_checks with `passes` passes at once, keep_apart standing in as `keep` when
        given, and `before` called on the worktree first: what came of it, masked, and the
        marks made as it raised, after which `on_raise`, if given, is set."""
        parent = self.tmp / f"run-{self.runs}-{passes}-{len(os.listdir(self.tmp))}"
        logs = parent / "logs"
        logs.mkdir(parents=True)
        ctx = types.SimpleNamespace(repo=ROOT, base=BASE, sha=SHA)
        plan = safe_push.CheckList(list(steps), "", passes=passes)
        rep, out, judged, raised, at_raise = safe_push.Report(), io.StringIO(), [], None, []
        judge = keep or safe_push.keep_apart

        def watched(repo, base, sha, report, stage):
            judged.append([(s.name, s.outcome) for s in report.steps])
            return judge(repo, base, sha, report, stage)
        with mock.patch.object(safe_push, "NEGATIVE", list(negative)), \
                mock.patch.object(safe_push, "keep_apart", watched), \
                contextlib.redirect_stdout(out):
            with safe_push.worktree(ROOT, SHA, parent, "check") as wt:
                if before is not None:
                    before(wt)
                try:
                    safe_push.full_checks(ctx, wt, parent, INPUTS if inputs is None else inputs,
                                          rep, logs, plan)
                except Exception as e:
                    raised = e
                    at_raise = sorted(p.name for p in marks.iterdir())
                    if on_raise is not None:
                        on_raise.set()

        def mask(text: str) -> str:
            for path, token in ((parent / "check", "WORKTREE"), (parent / "main", "WORKTREE"),
                                (parent / "negative", "WORKTREE"), (logs, "LOGS"),
                                (parent, "PARENT")):
                for form in dict.fromkeys((str(path), os.path.realpath(path))):
                    text = text.replace(form, token)
            return text
        lines = out.getvalue().splitlines()
        return Outcome(
            (type(raised).__name__, mask(str(raised))) if raised is not None else None,
            [(s.stage, s.name, s.outcome, mask(s.detail)) for s in rep.steps],
            [mask(TIME.sub("", line)) for line in lines if not line.startswith(BETWEEN)],
            {p.name: p.read_bytes() for p in sorted(logs.iterdir())},
            judged, [line for line in lines if line.startswith(BETWEEN)], marks, parent,
            at_raise)

    @contextlib.contextmanager
    def released_once_awaited(self, marks: Path):
        """The mark `release`, for a check to hold until, made once the harness, its stop
        set (not only a signal recorded), joins the passes' threads (awaited), or else once
        it has raised: so that a harness that raises without waiting for a check still
        running raises before the check ends. Yields the event full() sets as it raises."""
        halts, joining, raised = [], threading.Event(), threading.Event()

        class Watched(safe_push.Halt):
            def __init__(self):
                super().__init__()
                halts.append(self)

        class Joined(threading.Thread):
            def join(self, timeout=None):
                if halts and threading.Event.is_set(halts[-1]):
                    joining.set()
                return super().join(timeout)

        def release():
            given_up = time.monotonic() + HOLD
            while not (joining.is_set() or raised.is_set()) and time.monotonic() < given_up:
                joining.wait(0.01)
            (marks / "release").touch()
        releaser = threading.Thread(target=release, daemon=True)
        releaser.start()
        try:
            with mock.patch.object(safe_push, "Halt", Watched), \
                    mock.patch.object(safe_push.threading, "Thread", Joined):
                yield raised
        finally:
            raised.set()
            releaser.join(HOLD)

    def both(self, build, keep=None, before=None) -> tuple[Outcome, Outcome]:
        """`build(marks, passes)`'s steps and negative tests run at one pass and at two:
        both outcomes, asserted the same."""
        outcomes = []
        for passes in (1, 2):
            marks = self.marks()
            steps, negative = build(marks, passes)
            outcomes.append(self.full(steps, negative, passes, marks, keep, before))
        one, two = outcomes
        for field in COMPARED:
            self.assertEqual(getattr(two, field), getattr(one, field), field)
        for outcome in outcomes:
            self.assertEqual(len(outcome.between), 1, outcome.between)
        return one, two

    def names(self, outcome: Outcome, label: str) -> list[str]:
        return [name for _, name, _, _ in outcome.steps if name.endswith(label)]

    def overlapped(self, two: Outcome, name: str) -> None:
        """At two passes, each pass's `name` passed, and began before the other's ended:
        each held until the other's had begun."""
        def at(which: str, what: str) -> int:
            return (two.marks / f"{key(which, name)}.{what}").stat().st_mtime_ns
        rows = {row: outcome for _, row, outcome, _ in two.steps}
        self.assertEqual((rows[name + BASE_PASS], rows[name + OWN_PASS]), ("ok", "ok"))
        self.assertLessEqual(at("commit", "start"), at("main", "end"), name)
        self.assertLessEqual(at("main", "start"), at("commit", "end"), name)


class Verdicts(Stand):
    """The same verdicts, rows, lines, logs and judgements at one pass and at two."""

    def test_a_both_passes_pass(self):
        one, two = self.both(lambda marks, passes: self.sequence(marks, passes))
        self.assertIsNone(one.raised)
        self.assertEqual([(name, outcome) for _, name, outcome, _ in one.steps],
                         [(n + BASE_PASS, "ok") for n in ("first", "second", "third")]
                         + [(n + OWN_PASS, "ok") for n in ("first", "second", "third")]
                         + [(n + BASE_PASS, "ok") for n in ("negative: first",
                                                            "negative: second")]
                         + [(n + OWN_PASS, "ok") for n in ("negative: first",
                                                           "negative: second")])
        self.assertEqual(sorted(one.logs), [
            "11-first-origin-main-s-checks.log", "11-first-the-commit-s-checks.log",
            "12-second-origin-main-s-checks.log", "12-second-the-commit-s-checks.log",
            "13-third-origin-main-s-checks.log", "13-third-the-commit-s-checks.log",
            "31-negative-first-origin-main-s-checks.log",
            "31-negative-first-the-commit-s-checks.log",
            "32-negative-second-origin-main-s-checks.log",
            "32-negative-second-the-commit-s-checks.log"])
        self.assertEqual(one.logs["12-second-the-commit-s-checks.log"],
                         b"second in commit says this on stdout\n"
                         b"second in commit says this on stderr\n")
        self.assertEqual(len(one.judged), 2)    # after each loop of origin/main's pass
        self.overlapped(two, "first")
        self.overlapped(two, "negative: first")

    def test_b_origin_mains_pass_fails_and_the_commits_passes(self):
        def build(marks, passes):
            return self.sequence(marks, passes, {"second": ({"code": 3}, {})})
        one, _ = self.both(build)
        self.assertIsNone(one.raised)
        self.assertEqual([(name, outcome) for _, name, outcome, _ in one.steps][:4],
                         [("first" + BASE_PASS, "ok"), ("second" + BASE_PASS, "note"),
                          ("third" + BASE_PASS, "ok"), ("first" + OWN_PASS, "ok")])
        self.assertIn("second" + OWN_PASS, self.names(one, OWN_PASS))
        self.assertIn("full output in LOGS/12-second-origin-main-s-checks.log\n",
                      one.steps[1][3])
        # keep_apart judged the note, and let it pass: the commit changes nothing judged.
        self.assertIn(("second" + BASE_PASS, "note"), one.judged[0])
        self.assertEqual(len(self.names(one, OWN_PASS)), 5)

    def test_c_the_commits_pass_fails(self):
        cases = (
            ("in the checks", {"second": ({}, {"code": 3})}, "second",
             ["first" + OWN_PASS, "second" + OWN_PASS]),
            ("in the negative tests", {"negative: first": ({}, {"code": 3})},
             "negative: first",
             ["first" + OWN_PASS, "second" + OWN_PASS, "third" + OWN_PASS,
              "negative: first" + OWN_PASS]),
        )
        for where, behave, failing, own in cases:
            with self.subTest(where):
                one, two = self.both(lambda marks, passes: self.sequence(marks, passes, behave))
                self.assertEqual(one.raised, ("Refusal",
                                              f"`{failing + OWN_PASS}` failed on the commit"))
                self.assertEqual(self.names(one, OWN_PASS), own)
                self.assertEqual(one.steps[-1][2], "FAIL")
                if where == "in the checks":
                    self.assertFalse([n for n in one.logs if n.startswith("3")])
                    self.assertFalse(list(two.marks.glob("*negative*")))

    def test_d_both_passes_fail(self):
        def build(marks, passes):
            return self.sequence(marks, passes, {"second": ({"code": 3}, {"code": 4})})
        one, _ = self.both(build)
        self.assertEqual(one.raised, ("Refusal", f"`second{OWN_PASS}` failed on the commit"))
        self.assertEqual([(name, outcome) for _, name, outcome, _ in one.steps],
                         [("first" + BASE_PASS, "ok"), ("second" + BASE_PASS, "note"),
                          ("third" + BASE_PASS, "ok"), ("first" + OWN_PASS, "ok"),
                          ("second" + OWN_PASS, "FAIL")])

    def test_e_keep_apart_refuses_after_origin_mains_checks(self):
        said = "planted: origin/main's checks fail, and the commit changes what they judge"

        def refusing(repo, base, sha, rep, stage):
            rep.add(stage, "check change kept apart", "FAIL", said)
            return True

        def build(marks, passes):
            # At two, origin/main's last check holds until the commit's last has ended, so
            # that the commit's whole loop has run, its logs written, when it is discarded.
            last = ({"hold": key("commit", "third") + ".end"} if passes == 2 else {}, {})
            return self.sequence(marks, passes, {"third": last})
        one, two = self.both(build, keep=refusing)
        self.assertEqual(one.raised, ("Refusal", "a check changed together with what it checks"))
        self.assertEqual([(name, outcome) for _, name, outcome, _ in one.steps],
                         [("first" + BASE_PASS, "ok"), ("second" + BASE_PASS, "ok"),
                          ("third" + BASE_PASS, "ok"), ("check change kept apart", "FAIL")])
        self.assertEqual(sorted(one.logs), ["11-first-origin-main-s-checks.log",
                                            "12-second-origin-main-s-checks.log",
                                            "13-third-origin-main-s-checks.log"])
        self.assertTrue((two.marks / f"{key('commit', 'third')}.end").exists(),
                        "the commit's loop had not run: nothing was discarded")
        for outcome in (one, two):
            self.assertFalse(list(outcome.marks.glob("*negative*")), "a negative test ran")

    def test_f_a_pass_crashes(self):
        # tests/only-commit.sh is the commit's: origin/main's copies take it out, and run()
        # raises in origin/main's pass alone. tests/only-main.sh, the other way round.
        cases = (("origin/main's", "tests/only-commit.sh", 1),
                 ("the commit's", "tests/only-main.sh", 4))
        for whose, script, rows in cases:
            with self.subTest(whose):
                def build(marks, passes):
                    steps, negative = self.sequence(marks, passes)
                    return steps[:1] + [("second", [script])] + steps[2:], negative
                one, _ = self.both(build)
                self.assertEqual(one.raised[0], "FileNotFoundError")
                self.assertIn(script, one.raised[1])
                self.assertEqual(len(one.steps), rows)
                self.assertEqual(len(one.judged), 1 if whose == "the commit's" else 0)

    def test_a_refusal_or_a_crash_waits_for_the_commits_step(self):
        # At two, the commit's first check holds until the harness, its stop set, joins the
        # passes' threads: a refusal of keep_apart, or origin/main's pass raising, comes out
        # only once that check has ended, with the rows and logs of one pass at a time.
        def refusing(repo, base, sha, rep, stage):
            rep.add(stage, "check change kept apart", "FAIL", "planted")
            return True
        cases = (("a refusal of keep_apart", refusing, None, "Refusal"),
                 ("origin/main's pass raising", None, "tests/only-commit.sh",
                  "FileNotFoundError"))
        for what, keep, script, raised in cases:
            with self.subTest(what):
                outcomes = []
                for passes in (1, 2):
                    marks = self.marks()
                    behave = {"first": ({}, {"hold": "release"})} if passes == 2 else {}
                    steps, negative = self.sequence(marks, passes, behave)
                    if script:
                        steps = steps[:1] + [("second", [script])] + steps[2:]
                    with (self.released_once_awaited(marks) if passes == 2
                          else contextlib.nullcontext()) as on_raise:
                        outcomes.append(self.full(steps, negative, passes, marks, keep,
                                                  on_raise=on_raise))
                one, two = outcomes
                for field in COMPARED:
                    self.assertEqual(getattr(two, field), getattr(one, field), field)
                self.assertEqual(one.raised[0], raised)
                self.assertFalse([name for name in one.logs if "the-commit" in name])
                self.assertIn(f"{key('commit', 'first')}.end", two.at_raise,
                              "raised before the commit's check had ended")


class Trees(Stand):
    """A pass that leaves its tree changed: the same verdict and rows at one pass and at
    two, whether a check refuses it or the at_commit one after another begins the next
    pass with; and the one difference, stricter."""

    def test_g_a_tracked_file_written(self):
        for whose, behave, raised in (
                ("the commit's, the clean-tree check refusing",
                 {"second": ({}, {"write": "tracked"})},
                 ("Refusal", f"`{safe_push.EMPTY_CHECK}{OWN_PASS}` failed on the commit")),
                ("origin/main's, put back by the reset", {"second": ({"write": "tracked"}, {})},
                 None)):
            with self.subTest(whose):
                def build(marks, passes):
                    steps, negative = self.sequence(marks, passes, behave)
                    return steps[:2] + [(safe_push.EMPTY_CHECK, None)] + steps[2:], negative
                one, _ = self.both(build)
                self.assertEqual(one.raised, raised)
                if raised is None:
                    self.assertIn((safe_push.EMPTY_CHECK + BASE_PASS, "note"),
                                  [(name, outcome) for _, name, outcome, _ in one.steps])

    def test_g_what_outlasts_the_reset_is_refused_where_it_is_one_after_another(self):
        # A repository nested in an untracked folder outlasts `git clean -fd`, and a
        # skip-worktree flag `git reset --hard`: the at_commit that begins the commit's
        # pass, one after another, refuses them, after origin/main's rows and keep_apart.
        cases = (
            ("a nested repository, origin/main's checks", {"second": ({"write": "nested"}, {})},
             "git status lists ?? nested/", 3),
            ("a flagged entry, origin/main's checks", {"second": ({"write": "flag"}, {})},
             "flagged skip-worktree or assume-unchanged: tracked.txt", 3),
            ("a nested repository, origin/main's negative tests",
             {"negative: second": ({"write": "nested"}, {})},
             "git status lists ?? nested/", 8),
        )
        for what, behave, why, rows in cases:
            with self.subTest(what):
                one, two = self.both(lambda marks, passes: self.sequence(marks, passes, behave))
                self.assertEqual(one.raised, (
                    "Refusal", f"before a pass of the checks, the files on disk in the worktree "
                               f"WORKTREE may no longer be the commit {SHA[:12]} ({why}): "
                               "something run in an earlier pass changed them"))
                self.assertEqual(len(one.steps), rows, one.steps)
                self.assertEqual(one.steps[-1][1][-len(BASE_PASS):], BASE_PASS)
                self.assertEqual(len(one.judged), 1 if rows == 3 else 2)

    def test_g_a_tree_step_3_left_changed_is_refused_before_any_row(self):
        def nested(wt: Path):
            (wt / "nested").mkdir()
            git(wt / "nested", "init", "-q")
        one, two = self.both(lambda marks, passes: self.sequence(marks, passes), before=nested)
        self.assertEqual(one.raised[0], "Refusal")
        self.assertIn("(git status lists ?? nested/)", one.raised[1])
        self.assertEqual(one.steps, [])
        self.assertFalse(list(two.marks.iterdir()), "a check ran")

    def test_the_one_difference_is_stricter(self):
        # The commit's last check leaves a nested repository, and no check after it looks.
        # One after another, its negative tests begin in a fresh worktree, and it passes;
        # at two, they begin with at_commit in its own, which refuses it.
        behave = {"third": ({}, {"write": "nested"})}
        outcomes = []
        for passes in (1, 2):
            marks = self.marks()
            steps, negative = self.sequence(marks, passes, behave, overlap=(True, False))
            outcomes.append(self.full(steps, negative, passes, marks))
        one, two = outcomes
        self.assertIsNone(one.raised)
        self.assertEqual(two.raised, (
            "Refusal", "before a pass of the checks, the files on disk in the worktree "
                       f"WORKTREE may no longer be the commit {SHA[:12]} (git status lists "
                       "?? nested/): something run in an earlier pass changed them"))
        # The same rows up to the commit's negative tests, which never begin at two.
        self.assertEqual(len(one.steps), 10)
        self.assertEqual(two.steps, one.steps[:8])


class Overlap(Stand):
    """At two passes they run at once; at one, the commit's pass never begins before
    origin/main's has ended."""

    def test_h_two_overlap_and_one_never(self):
        marks = self.marks()
        steps, negative = self.sequence(marks, 2)
        two = self.full(steps, negative, 2, marks)
        self.assertIsNone(two.raised)
        self.overlapped(two, "first")
        self.overlapped(two, "negative: first")
        marks = self.marks()
        steps, negative = self.sequence(marks, 1)
        one = self.full(steps, negative, 1, marks)
        self.assertIsNone(one.raised)
        # At one, each of the commit's checks saw every one of origin/main's in its loop
        # ended, and none of origin/main's saw one of the commit's in its loop begun.
        for loop in (("first", "second", "third"), ("negative: first", "negative: second")):
            ends = {f"{key('main', name)}.end" for name in loop}
            starts = {f"{key('commit', name)}.start" for name in loop}
            for name in loop:
                seen = set((marks / f"{key('commit', name)}.seen").read_text().split("\n"))
                self.assertLessEqual(ends, seen, name)
                seen = set((marks / f"{key('main', name)}.seen").read_text().split("\n"))
                self.assertFalse(starts & seen, name)

    def test_one_pass_stays_without_a_check_input_or_on_a_cache_hit(self):
        refused = mock.patch.object(safe_push, "at_once",
                                    side_effect=AssertionError("the passes ran at once"))
        marks = self.marks()
        steps, negative = self.sequence(marks, 1)
        with refused:
            outcome = self.full(steps, negative, 2, marks, inputs=[])
        self.assertIsNone(outcome.raised)
        self.assertEqual([name for _, name, _, _ in outcome.steps],
                         [name for name, _ in steps + negative])
        # origin/main's pass taken from the cache: replayed, then the commit's run.
        fields = {"checks": [[n, c] for n, c in steps], "negative": [[n, c] for n, c in negative]}
        recorded = [{"name": name + BASE_PASS, "outcome": "ok", "detail": "", "seconds": 0.1,
                     "log": "recorded\n"} for name, _ in steps + negative]
        hit = safe_push.MainChecks("e" * 64, fields, {"steps": recorded,
                                                      "written": "2026-10-29 00:00 UTC"})
        outcomes = []
        for passes in (1, 2):
            hit.next = 0
            marks = self.marks()
            steps, negative = self.sequence(marks, 1)
            with refused, mock.patch.object(safe_push, "CACHE", self.tmp), \
                    mock.patch.object(safe_push, "main_checks", return_value=hit):
                outcomes.append(self.full(steps, negative, passes, marks))
        for field in COMPARED:
            self.assertEqual(getattr(outcomes[1], field), getattr(outcomes[0], field), field)
        self.assertIsNone(outcomes[0].raised)
        self.assertIn("reused from the cache", outcomes[0].steps[0][3])


class Between(Stand):
    """The work between the rows: each piece named, timed and counted, in one line printed
    once however step 4 ends, never a row."""

    PIECE = re.compile(r"([a-z_ ]+?) [0-9]+\.[0-9] s(?: \(([0-9]+) times\))?")

    def pieces(self, line: str) -> dict[str, int]:
        body, _, total = line.removeprefix(BETWEEN).rpartition(": ")
        self.assertRegex(total, r"^[0-9]+\.[0-9] s in all$")
        return {m[1]: int(m[2] or 1) for m in map(self.PIECE.fullmatch, body.split(", "))}

    def test_the_line_names_each_piece(self):
        expected = {1: {"worktree add": 1, "copy_build": 1, "at_commit": 4, "base_copies": 2,
                        "reset and clean": 2, "keep_apart": 2, "worktree remove": 1},
                    2: {"worktree add": 1, "copy_build": 1, "at_commit": 7, "base_copies": 2,
                        "reset and clean": 2, "keep_apart": 2, "worktree remove": 1}}
        for passes in (1, 2):
            with self.subTest(passes=passes):
                marks = self.marks()
                steps, negative = self.sequence(marks, passes)
                outcome = self.full(steps, negative, passes, marks)
                [line] = outcome.between
                self.assertEqual(self.pieces(line), expected[passes])
                self.assertEqual(list(self.pieces(line)), list(expected[passes]))
                self.assertNotIn("between", " ".join(name for _, name, _, _ in outcome.steps))
        # On a refusal too.
        marks = self.marks()
        steps, negative = self.sequence(marks, 2, {"first": ({}, {"code": 1})})
        outcome = self.full(steps, negative, 2, marks)
        self.assertEqual(outcome.raised[0], "Refusal")
        self.assertEqual(len(outcome.between), 1)

    def test_a_piece_is_timed_on_every_way_out(self):
        between = safe_push.Between()
        self.assertEqual(between.line(), "nothing: 0.0 s in all")
        with self.assertRaises(ZeroDivisionError), between.piece("at_commit"):
            1 / 0
        with between.piece("worktree remove"):
            pass
        with between.piece("at_commit"):
            pass
        with between.piece("something else"):
            pass
        self.assertRegex(between.line(), r"^at_commit 0\.0 s \(2 times\), worktree remove "
                                         r"0\.0 s, something else 0\.0 s: 0\.0 s in all$")
        with safe_push.piece(None, "at_commit"):
            pass        # nothing timed, and nothing to time it with


class Deferred(unittest.TestCase):
    """A pass's report held: nothing printed until it is put in, then the lines of a pass
    reported directly; no heading."""

    def test_it_prints_as_the_pass_alone(self):
        rows = [("4", "a", "ok", "", 1.25), ("4", "b", "note", "said\nmore", None),
                ("4", "c", "FAIL", "why", 0.5)]
        direct, held = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(direct):
            rep = safe_push.Report()
            for row in rows:
                rep.add(*row)
        deferred = safe_push.Deferred()
        with contextlib.redirect_stdout(held):
            for row in rows:
                deferred.add(*row)
        self.assertEqual(held.getvalue(), "")
        self.assertEqual(deferred.steps, rep.steps)
        into = safe_push.Report()
        with contextlib.redirect_stdout(held):
            deferred.into(into)
        self.assertEqual(held.getvalue(), direct.getvalue())
        self.assertEqual(into.steps, rep.steps)
        with self.assertRaises(RuntimeError):
            deferred.heading("4. The full local checks")


class Stop(Stand):
    """run_sequence with `stop` set starts no further step or group, and a group already
    started runs to its end; with it unset, or none, it runs as before."""

    def test_no_step_starts_once_it_is_set(self):
        logs = self.tmp / "logs"
        logs.mkdir()
        stop = threading.Event()
        marks = self.marks()
        steps = [("first", [sys.executable, "-c", f"open({str(marks / 'first')!r}, 'w')"]),
                 ("second", [sys.executable, "-c", f"open({str(marks / 'second')!r}, 'w')"])]
        real = safe_push.run_step

        def stopping(*args, **kw):
            out = real(*args, **kw)
            stop.set()
            return out
        with mock.patch.object(safe_push, "run_step", stopping), \
                contextlib.redirect_stdout(io.StringIO()), self.assertRaises(safe_push.Stopped):
            safe_push.run_sequence(steps, self.tmp, safe_push.Report(), logs, "", "FAIL", [], 10,
                                   None, None, stop)
        self.assertEqual(sorted(p.name for p in marks.iterdir()), ["first"])
        # A group of two, at one worker and at two: set by the first, the second still runs.
        for workers in (1, 2):
            with self.subTest(workers=workers):
                stop.clear()
                marks = self.marks()
                group = [(n, [sys.executable, "-c", f"open({str(marks / n)!r}, 'w')"])
                         for n in ("one", "two", "three")]
                plan = safe_push.CheckList(group, "", concurrent=frozenset({"one", "two"}),
                                           workers=workers)
                real_run = safe_push.run

                def run(cmd, cwd, **kw):
                    r = real_run(cmd, cwd, **kw)
                    if cmd is group[0][1]:
                        stop.set()
                    return r
                root = self.tmp / f"tree-{workers}"
                root.mkdir()
                git(root, "init", "-q")
                git(root, "commit", "-q", "--allow-empty", "-m", "A tree")
                with mock.patch.object(safe_push, "run", run), \
                        contextlib.redirect_stdout(io.StringIO()), \
                        self.assertRaises(safe_push.Stopped):
                    safe_push.run_sequence(group, root, safe_push.Report(), logs, "", "FAIL",
                                           [], 20 + 10 * workers, plan, None, stop)
                self.assertEqual(sorted(p.name for p in marks.iterdir()), ["one", "two"])


class Interrupted(Stand):
    """SIGINT, then SIGTERM, sent to the harness while both passes' checks run: recorded,
    no further step started, KeyboardInterrupt raised only once both have ended, the
    handlers put back, the commit's logs of the loop discarded, and the second worktree
    removed. The checks end either the moment both signals are recorded, before the main
    thread has looked, so that the passes must read the record themselves; or only once
    the harness joins the passes' threads, so that a harness that did not wait would
    raise first."""

    def test_i_signals_wait_for_both_passes(self):
        if threading.current_thread() is not threading.main_thread():
            self.skipTest("a signal's handler runs on the main thread alone")
        signals = safe_push.GROUP_SIGNALS
        before = {signum: signal.getsignal(signum) for signum in signals}
        mine = {signum: (lambda signum, frame: None) for signum in signals}
        for signum, handler in mine.items():
            signal.signal(signum, handler)
        self.addCleanup(lambda: [signal.signal(s, h) for s, h in before.items()])
        for release_on in ("recorded", "awaited"):
            with self.subTest(release_on=release_on):
                sent, at_raise, parent, logs = self.signalled(release_on)
                self.assertEqual(sent, [True], "both passes' checks never ran together")
                self.assertIsNotNone(at_raise, "no KeyboardInterrupt")
                args, present, handlers = at_raise
                self.assertEqual(args, ())          # SIGINT's, the first
                for which in ("main", "commit"):
                    self.assertIn(f"{key(which, 'long')}.end", present,
                                  "raised before it ended")
                self.assertFalse([m for m in present if "after" in m or "negative" in m],
                                 "a step started after the signal")
                self.assertEqual(handlers, mine)
                self.assertFalse((parent / "main").exists())
                self.assertNotIn(str(parent / "main"), git(ROOT, "worktree", "list"))
                # The commit's log of the loop discarded; origin/main's kept, as one after
                # another.
                self.assertEqual(sorted(p.name for p in logs.iterdir()),
                                 ["11-long-origin-main-s-checks.log"])

    def signalled(self, release_on: str):
        """full_checks at two passes, on this, the main thread, sent SIGINT and SIGTERM once
        both passes' first checks have begun, those checks released as `release_on` says:
        whether the signals were sent; the exception's arguments, the marks made and the
        handlers, as it raised; the worktrees' folder; the logs' folder."""
        marks = self.marks()
        release = marks / "release"
        steps = [self.stand_in(marks, "long", {"hold": "release"}, {"hold": "release"}),
                 self.stand_in(marks, "after")]
        negative = [self.stand_in(marks, "negative: first")]
        recorded = threading.Event()
        real = safe_push.recorder

        def recorder(caught):
            record = real(caught)

            def marking(signum, frame):
                record(signum, frame)
                if signal.SIGTERM in caught:
                    recorded.set()
            return marking
        sent = []

        def send():
            given_up = time.monotonic() + HOLD
            started = [marks / f"{key(which, 'long')}.start" for which in ("main", "commit")]
            try:
                while not all(p.exists() for p in started):
                    if time.monotonic() > given_up:
                        return
                    time.sleep(0.01)
                os.kill(os.getpid(), signal.SIGINT)
                os.kill(os.getpid(), signal.SIGTERM)
                sent.append(True)
                if release_on == "recorded":
                    recorded.wait(HOLD)
            finally:
                if release_on == "recorded":
                    release.touch()
        parent = self.tmp / f"run-signalled-{release_on}"
        logs = parent / "logs"
        logs.mkdir(parents=True)
        ctx = types.SimpleNamespace(repo=ROOT, base=BASE, sha=SHA)
        plan = safe_push.CheckList(steps, "", passes=2)
        at_raise = None
        sender = threading.Thread(target=send, daemon=True)
        with contextlib.ExitStack() as stack:
            on_raise = (stack.enter_context(self.released_once_awaited(marks))
                        if release_on == "awaited" else None)
            stack.enter_context(mock.patch.object(safe_push, "NEGATIVE", negative))
            stack.enter_context(mock.patch.object(safe_push, "recorder", recorder))
            stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
            with safe_push.worktree(ROOT, SHA, parent, "check") as wt:
                sender.start()
                try:
                    safe_push.full_checks(ctx, wt, parent, INPUTS, safe_push.Report(), logs,
                                          plan)
                except KeyboardInterrupt as e:
                    at_raise = (e.args, sorted(p.name for p in marks.iterdir()),
                                {s: signal.getsignal(s) for s in safe_push.GROUP_SIGNALS})
                    if on_raise is not None:
                        on_raise.set()
        sender.join(HOLD)
        return sent, at_raise, parent, logs


def folder(files: dict) -> Path:
    """A root of the test's own, committed: scripts/registry.py as this checkout holds it,
    and checks/ holding `files`."""
    root = Path(tempfile.mkdtemp(prefix="concurrent-passes-registry-"))
    (root / "scripts").mkdir()
    shutil.copy2(SCRIPTS / "registry.py", root / "scripts" / "registry.py")
    (root / "checks").mkdir()
    for name, text in files.items():
        (root / "checks" / name).write_text(text)
    (root / ".gitignore").write_text("__pycache__/\n")
    git(root, "init", "-q")
    git(root, "add", "-A")
    git(root, "commit", "-q", "-m", "A registry for the test")
    return root


def registry_entry(order, command: list[str], more: str = "") -> str:
    name = " ".join(command)
    return (f"order = {order}\nname = {json.dumps(name)}\njob = \"check\"\n"
            f"command = {json.dumps(command)}\nsection8 = {json.dumps(name)}\n{more}")


class Workers(unittest.TestCase):
    """STOICHEIA_PASS_WORKERS: unset or empty one, said nothing of; a whole number from 1,
    taken up to two; two only when twice the larger of the check and negative workers is
    within half the cores; said on the check list line; anything else refused."""

    HEAD = "; the two passes, when the commit changes a check input, run"

    def passes(self, value, checks=1, negative=None, cores=16):
        env = {k: v for k, v in os.environ.items()
               if k not in (safe_push.PASS_WORKERS, safe_push.NEGATIVE_WORKERS)}
        if value is not None:
            env[safe_push.PASS_WORKERS] = value
        if negative is not None:
            env[safe_push.NEGATIVE_WORKERS] = negative
        with mock.patch.dict(os.environ, env, clear=True), \
                mock.patch.object(safe_push.os, "cpu_count", return_value=cores):
            return safe_push.pass_workers(checks)

    def within(self, said, checks, negative, cores):
        return (f"{self.HEAD} at once ({said}: twice the larger of the check workers, "
                f"{checks}, and the negative tests' workers, {negative}, is within half this "
                f"machine's {cores} cores, {max(1, cores // 2)})")

    def test_j_the_variable_is_read_taken_capped_and_said(self):
        self.assertEqual(self.passes(None), (1, ""))
        self.assertEqual(self.passes(""), (1, ""))
        self.assertEqual(self.passes("1"), (1, f"{self.HEAD} one after another "
                                               "(STOICHEIA_PASS_WORKERS=1)"))
        self.assertEqual(self.passes("2"), (2, self.within("STOICHEIA_PASS_WORKERS=2", 1, 1,
                                                           16)))
        self.assertEqual(self.passes("002")[0], 2)
        taken = "STOICHEIA_PASS_WORKERS=3, taken as 2, as there are two passes"
        self.assertEqual(self.passes("3"), (2, self.within(taken, 1, 1, 16)))
        huge = self.passes("9" * 5000)
        self.assertEqual(huge[0], 2)
        self.assertIn(f"STOICHEIA_PASS_WORKERS={'9' * 20}…, taken as 2", huge[1])
        for bad in ("0", "000", "-1", "x", " 2", "2.0", "٣"):
            with self.subTest(bad=bad), self.assertRaises(safe_push.Refusal) as raised:
                self.passes(bad)
            self.assertEqual(str(raised.exception), "STOICHEIA_PASS_WORKERS must be a whole "
                             f"number from 1, not {bad!r}")

    def test_j_the_cap(self):
        over = (f"{self.HEAD} one after another: STOICHEIA_PASS_WORKERS=2, but twice the "
                "larger of the check workers, {c}, and the negative tests' workers, {n}, is "
                "more than half this machine's {cores} cores, {cap}")
        # Twice the check workers.
        self.assertEqual(self.passes("2", checks=4, cores=16),
                         (2, self.within("STOICHEIA_PASS_WORKERS=2", 4, 1, 16)))
        self.assertEqual(self.passes("2", checks=3, cores=8),
                         (1, over.format(c=3, n=1, cores=8, cap=4)))
        # Twice the negative workers, read as negative_tests.py reads them.
        self.assertEqual(self.passes("2", negative="4", cores=16)[0], 2)
        self.assertEqual(self.passes("2", negative="5", cores=16),
                         (1, over.format(c=1, n=5, cores=16, cap=8)))
        self.assertEqual(self.passes("2", negative="05", cores=16)[0], 1)
        for counted_as_one in ("", "0", "x", "-3"):
            with self.subTest(negative=counted_as_one):
                self.assertEqual(self.passes("2", negative=counted_as_one, cores=4),
                                 (2, self.within("STOICHEIA_PASS_WORKERS=2", 1, 1, 4)))
        self.assertEqual(self.passes("2", negative="9" * 5000, cores=16)[0], 1)
        # A machine of one or two cores, or of a number unknown, never runs two at once.
        for cores in (1, 2, None):
            with self.subTest(cores=cores):
                self.assertEqual(self.passes("2", cores=cores)[0], 1)
        self.assertEqual(self.passes("2", cores=3)[0], 1)
        self.assertEqual(self.passes("2", cores=4)[0], 2)

    def listed(self, root: Path, env: dict):
        ctx = types.SimpleNamespace(repo=root, base="HEAD")
        rep, refusal, checks = safe_push.Report(), None, None
        clean = {k: v for k, v in os.environ.items()
                 if k not in (safe_push.PASS_WORKERS, safe_push.NEGATIVE_WORKERS,
                              safe_push.CHECK_WORKERS)}
        with mock.patch.dict(os.environ, dict(clean, **env), clear=True), \
                mock.patch.object(safe_push.os, "cpu_count", return_value=8), \
                contextlib.redirect_stdout(io.StringIO()):
            try:
                checks = safe_push.check_list(ctx, rep)
            except safe_push.Refusal as e:
                refusal = str(e)
        [step] = rep.steps
        return checks, refusal, step

    def test_j_the_check_list_line_carries_it(self):
        alone = folder({"10-a.toml": registry_entry(10, ["python3", "-c", "pass"])})
        along = folder({"10-a.toml": registry_entry(10, ["python3", "-c", "pass"],
                                                    "concurrent = true\n")})
        for root in (alone, along):
            self.addCleanup(shutil.rmtree, root, ignore_errors=True)
        # Read whatever the sequence declares: here, nothing concurrent.
        checks, refusal, step = self.listed(alone, {safe_push.PASS_WORKERS: "2"})
        self.assertIsNone(refusal)
        self.assertEqual(checks.passes, 2)
        self.assertTrue(step.detail.endswith(self.within("STOICHEIA_PASS_WORKERS=2", 1, 1, 8)),
                        step.detail)
        self.assertNotIn(safe_push.CHECK_WORKERS, step.detail)
        # Unset: the line as before #609.
        checks, refusal, step = self.listed(alone, {})
        self.assertEqual(checks.passes, 1)
        self.assertNotIn("passes", step.detail)
        # Beside three check workers on eight cores: capped, both said, in that order.
        checks, refusal, step = self.listed(along, {safe_push.PASS_WORKERS: "2",
                                                    safe_push.CHECK_WORKERS: "3"})
        self.assertEqual((checks.workers, checks.passes), (3, 1))
        self.assertTrue(step.detail.endswith(
            "half this machine's 8 cores)" + f"{self.HEAD} one after another: "
            "STOICHEIA_PASS_WORKERS=2, but twice the larger of the check workers, 3, and the "
            "negative tests' workers, 1, is more than half this machine's 8 cores, 4"),
            step.detail)
        for bad in ("0", "x"):
            with self.subTest(bad=bad):
                checks, refusal, step = self.listed(alone, {safe_push.PASS_WORKERS: bad})
                said = f"STOICHEIA_PASS_WORKERS must be a whole number from 1, not {bad!r}"
                self.assertEqual((step.name, step.outcome, step.detail),
                                 ("check list", "FAIL", said))
                self.assertEqual(refusal, said)

    def test_the_variable_reaches_the_cache_key(self):
        with mock.patch.dict(os.environ, {safe_push.PASS_WORKERS: "2"}):
            variables = dict(safe_push.environment(REPO)["variables"])
        self.assertEqual(variables[safe_push.PASS_WORKERS], "2")


if __name__ == "__main__":
    unittest.main()
