#!/usr/bin/env python3
"""The cases of step 4's concurrent checks (#608), in scripts/safe_push.py, and of the
registry's two fields that declare them, in scripts/registry.py.

    python3 -I tests/test_concurrent_checks.py        # no Lean, no network

The run is put to stand-in checks, small Python commands, in a Git repository of the
test's own: the same steps, outcomes, order and logs whether a sequence declares nothing,
or runs its groups one at a time or three at once; the first failure in registry order
refusing, nothing after it reported or logged, a check still running waited for, and an
exception a check's run() raised coming in its place; a check never started before the
checks its `after` names have ended; a check that runs alone between two groups as a
barrier; a check declared concurrent that writes in the tree refused, at one worker and at
three; the worktree's state taken writing nothing; every check started by run(), at one
worker exactly as before #608, on this thread with no thread started, and at more on
threads of their own, the report and logs written on this thread; never more checks at
once than the workers, the cap of STOICHEIA_CHECK_WORKERS said, and a bad value failing
the check list line; and, interrupted while two checks run, by Ctrl-C or by SIGTERM and
again while it waits, the pass going on only once both checks and their children have
ended. The registry's reader accepts `concurrent = true` and refuses every other use of
the two fields; as_json carries them; safe_push's check_sequence reads them, and holds
their rules itself; a registry without them declares nothing concurrent; and the real
registry declares what #608's audit found, so that a change to it is made on purpose. It
runs alone in the sequence, since it starts processes of its own and measures how many
run at once.
"""

import contextlib
import io
import json
import os
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
from unittest import mock

REPO = Path(__file__).resolve().parent.parent
SCRIPTS = REPO / "scripts"
sys.path.insert(0, str(SCRIPTS))
import registry  # noqa: E402
import safe_push  # noqa: E402

IDENTITY = ("-c", "user.name=Concurrent checks test", "-c",
            "user.email=concurrent-checks-test@example.invalid", "-c", "commit.gpgsign=false",
            "-c", "core.hooksPath=/dev/null")
GUARD = safe_push.TREE_GUARD

# A stand-in check: it marks its start and its end, each a file made with O_EXCL holding
# the time by its own clock, sleeps between them, prints a line to each stream, and exits
# with the code given.
STAND_IN = """
import os, sys, time
marks, name, seconds, code = sys.argv[1], sys.argv[2], float(sys.argv[3]), int(sys.argv[4])
def mark(what):
    fd = os.open(os.path.join(marks, name + "." + what), os.O_WRONLY | os.O_CREAT | os.O_EXCL)
    os.write(fd, repr(time.time()).encode())
    os.close(fd)
mark("start")
time.sleep(seconds)
print(name, "says this on stdout")
print(name, "says this on stderr", file=sys.stderr)
mark("end")
sys.exit(code)
"""

# A check that starts a child, which sleeps the seconds given, notes both pids, and waits
# for the child before it marks its own end.
PARENT = """
import os, subprocess, sys, time
marks, name, seconds = sys.argv[1], sys.argv[2], sys.argv[3]
def note(what, text):
    path = os.path.join(marks, name + "." + what)
    with open(path + ".tmp", "w") as f:
        f.write(text)
    os.replace(path + ".tmp", path)
SLEEP = "import sys, time; time.sleep(float(sys.argv[1]))"
child = subprocess.Popen([sys.executable, "-c", SLEEP, seconds])
note("child", str(child.pid))
note("check", str(os.getpid()))
child.wait()
note("end", repr(time.time()))
"""


def py(code: str) -> list[str]:
    return [sys.executable, "-c", code]


def git(root: Path, *args: str) -> str:
    return subprocess.run(["git", *IDENTITY, *args], cwd=root, check=True,
                          capture_output=True, text=True).stdout


def registry_entry(order, command: list[str], more: str = "") -> str:
    """A file of the registry, for `command`, named and shown as the command."""
    name = " ".join(command)
    return (f"order = {order}\nname = {json.dumps(name)}\njob = \"check\"\n"
            f"command = {json.dumps(command)}\nsection8 = {json.dumps(name)}\n{more}")


def registry_empty(order, more: str = "") -> str:
    return (f'order = {order}\nname = "git status --porcelain is empty"\njob = "check"\n'
            f'empty = true\nsection8 = "git status --porcelain"\n{more}')


def running(pid: int) -> bool:
    """Is the process running: there, and no zombie waiting to be reaped?"""
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    state = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], capture_output=True,
                           text=True).stdout.strip()
    return bool(state) and not state.startswith("Z")


class Stand(unittest.TestCase):
    """A Git repository of the test's own, with a tracked file and an ignored folder, out/,
    and run_sequence on it as step 4 runs a pass, with no sandbox."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="concurrent-checks-"))
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)
        self.root = self.tmp / "repo"
        self.root.mkdir()
        git(self.root, "init", "-q")
        (self.root / ".gitignore").write_text("__pycache__/\nout/\n")
        (self.root / "tracked.txt").write_text("A tracked file.\n")
        git(self.root, "add", "-A")
        git(self.root, "commit", "-q", "-m", "A repository for the test")
        self.runs = 0

    def marks(self) -> Path:
        self.runs += 1
        path = self.tmp / f"marks-{self.runs}"
        path.mkdir()
        return path

    def stand_in(self, marks: Path, name: str, seconds: float = 0.0, code: int = 0):
        return (name, py(STAND_IN) + [str(marks), name, str(seconds), str(code)])

    def run_steps(self, steps, workers=1, concurrent=(), after=None, fail="FAIL",
                  label="", cache=None, plan=True):
        """run_sequence on `steps`, declared as given (no plan when `plan` is false): its
        refusal, if any; its steps; its logs, by name; and the logs' folder."""
        logs = self.tmp / f"logs-{self.runs}-{workers}-{len(os.listdir(self.tmp))}"
        logs.mkdir()
        declared = safe_push.CheckList(list(steps), "", concurrent=frozenset(concurrent),
                                       after=dict(after or {}), workers=workers) \
            if plan else None
        rep, refusal = safe_push.Report(), None
        with contextlib.redirect_stdout(io.StringIO()):
            try:
                safe_push.run_sequence(list(steps), self.root, rep, logs, label, fail, [], 10,
                                       declared, cache)
            except safe_push.Refusal as e:
                refusal = str(e)
        return refusal, rep.steps, {p.name: p.read_bytes() for p in logs.iterdir()}, logs

    def masked(self, steps, logs: Path):
        """The steps as a reader compares them: stage, name, outcome and detail, the logs'
        folder masked; their times left out."""
        return [(s.stage, s.name, s.outcome, s.detail.replace(str(logs), "LOGS"))
                for s in steps]

    def times(self, marks: Path, name: str) -> tuple[float, float]:
        return (float((marks / f"{name}.start").read_text()),
                float((marks / f"{name}.end").read_text()))


class Parity(Stand):
    """The same steps, outcomes, order and log bytes, times masked, from a sequence that
    declares nothing (each check run alone, as before #608), and from its groups run one
    at a time and three at once."""

    def sequence(self, marks: Path, failing=()):
        def code(name):
            return 3 if name in failing else 0
        writer = py("import os, time; time.sleep(0.1); os.makedirs('out', exist_ok=True); "
                    "open('out/written.txt', 'w').write('written\\n'); print('wrote')")
        steps = [self.stand_in(marks, "reader one", 0.3, code("reader one")),
                 self.stand_in(marks, "reader two", 0.0, code("reader two")),
                 self.stand_in(marks, "reader three", 0.15, code("reader three")),
                 ("writer", writer),
                 ("reader four", py("print(open('out/written.txt').read(), end='')")),
                 self.stand_in(marks, "reader five", 0.05, code("reader five")),
                 (safe_push.EMPTY_CHECK, None),
                 self.stand_in(marks, "reader six", 0.1, code("reader six"))]
        concurrent = {name for name, _ in steps if name.startswith("reader")}
        return steps, concurrent

    def three_ways(self, fail: str, failing=(), label=""):
        seen = []
        for workers, plan in ((1, False), (1, True), (3, True)):
            git(self.root, "clean", "-fdxq")
            steps, concurrent = self.sequence(self.marks(), failing)
            refusal, done, logs, folder = self.run_steps(steps, workers, concurrent,
                                                         fail=fail, label=label, plan=plan)
            seen.append((refusal, self.masked(done, folder), logs))
        return seen

    def test_a_passing_sequence_is_the_same_at_every_count(self):
        (refusal, steps, logs), *others = self.three_ways("FAIL")
        self.assertIsNone(refusal)
        self.assertEqual([(name, outcome) for _, name, outcome, _ in steps],
                         [("reader one", "ok"), ("reader two", "ok"), ("reader three", "ok"),
                          ("writer", "ok"), ("reader four", "ok"), ("reader five", "ok"),
                          (safe_push.EMPTY_CHECK, "ok"), ("reader six", "ok")])
        self.assertEqual(sorted(logs), ["11-reader-one.log", "12-reader-two.log",
                                        "13-reader-three.log", "14-writer.log",
                                        "15-reader-four.log", "16-reader-five.log",
                                        "17-git-status-porcelain-is-empty.log",
                                        "18-reader-six.log"])
        self.assertEqual(logs["11-reader-one.log"],
                         b"reader one says this on stdout\nreader one says this on stderr\n")
        self.assertEqual(logs["15-reader-four.log"], b"written\n")
        for other in others:
            self.assertEqual(other, (refusal, steps, logs))

    def test_a_noting_pass_is_the_same_at_every_count(self):
        (refusal, steps, logs), *others = self.three_ways(
            "note", failing=("reader two", "reader five"), label=safe_push.BASE_PASS)
        self.assertIsNone(refusal)
        self.assertEqual([outcome for _, _, outcome, _ in steps],
                         ["ok", "note", "ok", "ok", "ok", "note", "ok", "ok"])
        self.assertIn("full output in LOGS/12-reader-two-origin-main-s-checks.log\n"
                      "    reader two says this on stdout", steps[1][3])
        for other in others:
            self.assertEqual(other, (refusal, steps, logs))

    def test_the_cache_collects_each_step_in_order(self):
        marks = self.marks()
        steps, concurrent = self.sequence(marks, failing=("reader three",))
        fields = {"checks": [[name, cmd] for name, cmd in steps], "negative": []}
        cache = safe_push.MainChecks("c" * 64, fields, None)
        refusal, done, _, _ = self.run_steps(steps, 3, concurrent, fail="note",
                                             label=safe_push.BASE_PASS, cache=cache)
        self.assertIsNone(refusal)
        self.assertEqual(cache.spoiled, "")
        self.assertEqual([s["name"] for s in cache.steps],
                         [name + safe_push.BASE_PASS for name, _ in steps])
        self.assertEqual([s["outcome"] for s in cache.steps], [s.outcome for s in done])

    def test_a_sequence_that_declares_nothing_takes_no_state(self):
        marks = self.marks()
        steps, _ = self.sequence(marks)
        with mock.patch.object(safe_push, "tree_state",
                               side_effect=AssertionError("a state was taken")):
            refusal, done, _, _ = self.run_steps(steps, 3, ())
            self.assertIsNone(refusal)
            # A list of steps with no plan, as the negative tests' loop gives, the same.
            git(self.root, "clean", "-fdxq")
            refusal, plain, _, _ = self.run_steps(self.sequence(self.marks())[0], plan=False)
        self.assertIsNone(refusal)
        self.assertEqual([s.name for s in done], [s.name for s in plain])
        self.assertNotIn(GUARD, [s.name for s in done])


class FirstFailure(Stand):
    """Where a failure fails the pass, the refusal names the first failing check in registry
    order, whichever ended first; nothing after it is reported or logged; and every check
    started is waited for."""

    def test_the_earlier_failure_is_the_refusal(self):
        for workers in (3, 1):
            with self.subTest(workers=workers):
                marks = self.marks()
                alone_ran = marks / "alone-ran"
                steps = [self.stand_in(marks, "first", 0.0),
                         self.stand_in(marks, "fails early", 0.6, 3),
                         self.stand_in(marks, "fails late", 0.0, 4),
                         self.stand_in(marks, "after them", 0.0),
                         ("alone after", py(f"open({str(alone_ran)!r}, 'w')"))]
                concurrent = {"first", "fails early", "fails late", "after them"}
                refusal, done, logs, folder = self.run_steps(steps, workers, concurrent)
                self.assertEqual(refusal, "`fails early` failed on the commit")
                self.assertEqual([(s.name, s.outcome) for s in done],
                                 [("first", "ok"), ("fails early", "FAIL")])
                self.assertTrue(done[1].detail.startswith(
                    f"full output in {folder / '12-fails-early.log'}\n"), done[1].detail)
                self.assertEqual(sorted(logs), ["11-first.log", "12-fails-early.log"])
                self.assertFalse(alone_ran.exists())
                started = {p.stem for p in marks.glob("*.start")}
                ended = {p.stem for p in marks.glob("*.end")}
                self.assertEqual(started, ended, "a check was left running")
                if workers == 3:
                    # The later failure ended first, and was not reported.
                    self.assertLess(self.times(marks, "fails late")[1],
                                    self.times(marks, "fails early")[1])
                else:
                    self.assertEqual(started, {"first", "fails early"})

    def test_a_check_still_running_is_waited_for(self):
        marks = self.marks()
        steps = [self.stand_in(marks, "slow pass", 1.0), self.stand_in(marks, "quick fail",
                                                                     0.0, 1)]
        refusal, done, logs, _ = self.run_steps(steps, 2, {"slow pass", "quick fail"})
        self.assertEqual(refusal, "`quick fail` failed on the commit")
        self.assertEqual([(s.name, s.outcome) for s in done],
                         [("slow pass", "ok"), ("quick fail", "FAIL")])
        # The slow check had ended before the pass returned, its log written.
        self.assertTrue((marks / "slow pass.end").exists())
        self.assertLess(self.times(marks, "quick fail")[1], self.times(marks, "slow pass")[1])
        self.assertIn("11-slow-pass.log", logs)

    def test_an_exception_comes_in_its_place(self):
        # A check whose run() raises (here, no such program) raises in registry order, as
        # run_step's run() does: the checks before it reported, none after it, and every
        # check started waited for, at one worker and at three, in either kind of pass.
        missing = str(self.tmp / "no-such-program")
        for fail in ("FAIL", "note"):
            for workers in (1, 3):
                with self.subTest(fail=fail, workers=workers):
                    marks = self.marks()
                    steps = [self.stand_in(marks, "slow", 0.6), ("missing", [missing]),
                             self.stand_in(marks, "beside", 0.0),
                             ("alone", py(f"open({str(marks / 'alone-ran')!r}, 'w')"))]
                    with self.assertRaises(FileNotFoundError) as raised:
                        self.run_steps(steps, workers, {"slow", "missing", "beside"},
                                       fail=fail)
                    self.assertIn(missing, str(raised.exception))
                    self.assertTrue((marks / "slow.end").exists())
                    started = {p.stem for p in marks.glob("*.start")}
                    self.assertEqual(started, {p.stem for p in marks.glob("*.end")})
                    self.assertEqual(started, {"slow", "beside"} if workers == 3 else {"slow"})
                    self.assertFalse((marks / "alone-ran").exists())
                    logs = sorted(p.name for p in self.tmp.glob(f"logs-{self.runs}-*/*"))
                    self.assertEqual(logs, ["11-slow.log"])


class Order(Stand):
    """`after` holds a check back until the checks it names have ended, and a check that
    runs alone is a barrier: the group after it starts once it has ended."""

    def test_after_waits_for_the_checks_it_names(self):
        marks = self.marks()
        steps = [("set up", py("pass")),
                 self.stand_in(marks, "first", 0.5), self.stand_in(marks, "beside", 0.1),
                 self.stand_in(marks, "waits", 0.0)]
        after = {"waits": ("set up", "first")}
        refusal, done, _, _ = self.run_steps(steps, 3, {"first", "beside", "waits"}, after)
        self.assertIsNone(refusal)
        self.assertEqual([s.name for s in done], ["set up", "first", "beside", "waits"])
        first, beside, waits = (self.times(marks, n) for n in ("first", "beside", "waits"))
        self.assertLess(beside[0], first[1], "the group ran one at a time")
        self.assertGreaterEqual(waits[0], first[1])

    def test_a_check_alone_is_a_barrier(self):
        before = py("import os, sys; sys.exit(os.path.exists('out/barrier.txt'))")
        writer = py("import os, time; time.sleep(0.4); os.makedirs('out', exist_ok=True); "
                    "open('out/barrier.txt', 'w').write('x')")
        after = py("import os, sys; sys.exit(not os.path.exists('out/barrier.txt'))")
        steps = [("before", before), ("writer", writer), ("after", after)]
        refusal, done, _, _ = self.run_steps(steps, 3, {"before", "after"})
        self.assertIsNone(refusal)
        self.assertEqual([(s.name, s.outcome) for s in done],
                         [("before", "ok"), ("writer", "ok"), ("after", "ok")])
        # The writer declared concurrent too, the reader after it starts before the write.
        git(self.root, "clean", "-fdxq")
        refusal, done, _, _ = self.run_steps(steps, 3, {"before", "writer", "after"},
                                             fail="note")
        self.assertEqual([(s.name, s.outcome) for s in done],
                         [("before", "ok"), ("writer", "ok"), ("after", "note")])


class Planted(Stand):
    """A check declared concurrent that writes in the tree is refused, at one worker and at
    three, the step naming the group's checks and the path; in a noting pass it is noted,
    every check runs, and the pass is kept out of the main-checks cache."""

    def planted(self, marks: Path, write: str):
        return [self.stand_in(marks, "reader", 0.1), ("planter", py(write)),
                ("later", py(f"open({str(marks / 'later-ran')!r}, 'w')"))]

    def test_a_check_that_writes_the_tree_is_refused(self):
        for write, change in (("open('planted.txt', 'w').write('x')", "?? planted.txt"),
                              ("open('tracked.txt', 'a').write('more')", "M tracked.txt")):
            for workers in (1, 3):
                with self.subTest(change, workers=workers):
                    git(self.root, "checkout", "-q", "--", ".")
                    git(self.root, "clean", "-fdxq")
                    marks = self.marks()
                    refusal, done, _, _ = self.run_steps(self.planted(marks, write), workers,
                                                         {"reader", "planter"})
                    self.assertEqual(refusal, f"`{GUARD}` failed on the commit")
                    self.assertEqual([(s.name, s.outcome) for s in done],
                                     [("reader", "ok"), ("planter", "ok"), (GUARD, "FAIL")])
                    self.assertIn("after reader, planter, each declared concurrent",
                                  done[-1].detail)
                    self.assertTrue(done[-1].detail.endswith(": " + change), done[-1].detail)
                    self.assertFalse((marks / "later-ran").exists())

    def test_a_noting_pass_notes_it_and_keeps_out_of_the_cache(self):
        marks = self.marks()
        steps = self.planted(marks, "open('planted.txt', 'w').write('x')")
        fields = {"checks": [[name, cmd] for name, cmd in steps], "negative": []}
        cache = safe_push.MainChecks("d" * 64, fields, None)
        label = safe_push.BASE_PASS
        refusal, done, _, _ = self.run_steps(steps, 3, {"reader", "planter"}, fail="note",
                                             label=label, cache=cache)
        self.assertIsNone(refusal)
        self.assertEqual([(s.name, s.outcome) for s in done],
                         [("reader" + label, "ok"), ("planter" + label, "ok"),
                          (GUARD + label, "note"), ("later" + label, "ok")])
        self.assertEqual(cache.spoiled, f"the step {GUARD} failed in origin/main's pass")
        rep = safe_push.Report()
        with contextlib.redirect_stdout(io.StringIO()):
            cache.save(rep)
        [step] = rep.steps
        self.assertEqual((step.name, step.outcome), ("main-checks cache", "note"))
        self.assertIn(f"not written: the step {GUARD} failed", step.detail)

    def test_no_guard_without_a_declaration(self):
        # A registry without the field runs as before #608: a writer is the clean-tree
        # check's to catch, and no step is added.
        marks = self.marks()
        refusal, done, _, _ = self.run_steps(
            self.planted(marks, "open('planted.txt', 'w').write('x')"), 3, ())
        self.assertIsNone(refusal)
        self.assertEqual([s.name for s in done], ["reader", "planter", "later"])


class State(Stand):
    """tree_state takes the worktree as git status sees it, each file listed hashed, and
    writes nothing: not the index, not an object."""

    def test_the_state_is_taken_writing_nothing(self):
        git_dir = self.root / ".git"

        def written():
            index = git_dir / "index"
            return (index.read_bytes(), os.stat(index).st_mtime_ns,
                    sorted(p for p in (git_dir / "objects").rglob("*") if p.is_file()))
        (self.root / "tracked.txt").write_text("Changed.\n")
        (self.root / "new.txt").write_text("New.\n")
        (self.root / "out").mkdir()
        (self.root / "out" / "ignored.txt").write_text("Ignored.\n")
        before = written()
        state = safe_push.tree_state(self.root)
        self.assertEqual(written(), before)
        self.assertEqual({path: letters for path, (letters, _) in state.items()},
                         {"tracked.txt": " M", "new.txt": "??"})
        # Changed again, git's letters the same: the state differs, and names the path.
        (self.root / "tracked.txt").write_text("Changed again.\n")
        again = safe_push.tree_state(self.root)
        self.assertEqual(safe_push.tree_changes(state, again), "M tracked.txt")
        # Put back as the index holds it, and an untracked file taken away.
        git(self.root, "checkout", "-q", "--", "tracked.txt")
        (self.root / "new.txt").unlink()
        back = safe_push.tree_state(self.root)
        self.assertEqual(back, {})
        self.assertEqual(safe_push.tree_changes(again, back),
                         "new.txt (no longer listed by git status), "
                         "tracked.txt (no longer listed by git status)")
        # A mode changed, and a link.
        os.chmod(self.root / "tracked.txt", 0o755)
        (self.root / "link").symlink_to("tracked.txt")
        moved = safe_push.tree_state(self.root)
        self.assertEqual(safe_push.tree_changes(back, moved), "?? link, M tracked.txt")

class ThroughRun(Stand):
    """Every check is started by run(), as every command the harness starts is. At one
    worker, as before #608: one after another on this thread, no thread started, run()
    given for every check what run_step gave it before, and only the guard's `git status`
    added around each group. At more, each check of a group on a thread of its own, given
    the same, its environment built on this thread, and the report and the logs written on
    this thread alone."""

    CONCURRENT = {"one", "two", "three", "four"}

    def recorded(self, workers: int, plan: bool = True):
        """Each call of run() in order: the check's name (None for another command), its
        command with the marks' folder masked, its directory, keywords and thread; the
        threads that built an environment, reported a step and wrote a file; the steps'
        names; and the refusal, if any."""
        marks = self.marks()
        steps = [self.stand_in(marks, "one", 0.2), self.stand_in(marks, "two", 0.0),
                 ("alone", py("print('alone')")), self.stand_in(marks, "three", 0.1),
                 self.stand_in(marks, "four", 0.0)]
        names = {tuple(cmd): name for name, cmd in steps}
        calls, threads = [], {}
        real_run = safe_push.run

        def run(cmd, cwd, **kw):
            calls.append((names.get(tuple(cmd)), [a.replace(str(marks), "MARKS") for a in cmd],
                          cwd, kw, threading.current_thread()))
            return real_run(cmd, cwd, **kw)

        def noted(what, real):
            def call(*args, **kw):
                threads.setdefault(what, set()).add(threading.current_thread())
                return real(*args, **kw)
            return call
        with mock.patch.object(safe_push, "run", run), \
                mock.patch.object(safe_push, "tool_env", noted("tool_env", safe_push.tool_env)), \
                mock.patch.object(safe_push, "step_done",
                                  noted("step_done", safe_push.step_done)), \
                mock.patch.object(Path, "write_text", noted("write_text", Path.write_text)):
            refusal, done, _, _ = self.run_steps(steps, workers, self.CONCURRENT, plan=plan)
        return calls, threads, [s.name for s in done], refusal

    def test_at_one_worker_every_check_runs_as_before(self):
        main = threading.main_thread()
        with mock.patch.object(safe_push.threading, "Thread",
                               side_effect=AssertionError("a thread was started")):
            # No plan: every check alone, as every check ran before #608.
            before, _, steps, refusal = self.recorded(1, plan=False)
            self.assertIsNone(refusal)
            git(self.root, "clean", "-fdxq")
            now, threads, same, refusal = self.recorded(1)
        self.assertIsNone(refusal)
        self.assertEqual(same, steps)
        checks = [call for call in now if call[0] is not None]
        self.assertEqual([call[:4] for call in checks], [call[:4] for call in before])
        self.assertEqual([call[0] for call in checks], ["one", "two", "alone", "three", "four"])
        for name, _, cwd, kw, thread in checks:
            self.assertEqual((cwd, kw), (self.root, {"env": safe_push.tool_env()}), name)
            self.assertIs(thread, main, name)
        # Beside them, only the guard's git status, before and after each of the two groups.
        others = [call[1][:2] for call in now if call[0] is None]
        self.assertEqual(others, [["git", "--no-optional-locks"]] * 4)
        self.assertEqual(threads, {"tool_env": {main}, "step_done": {main},
                                   "write_text": {main}})

    def test_at_more_each_check_runs_through_run_on_a_thread_of_its_own(self):
        main = threading.main_thread()
        one, _, steps, _ = self.recorded(1)
        git(self.root, "clean", "-fdxq")
        three, threads, same, refusal = self.recorded(3)
        self.assertIsNone(refusal)
        self.assertEqual(same, steps)
        by_name = {call[0]: call for call in three if call[0] is not None}
        self.assertEqual({name: call[1:4] for name, call in by_name.items()},
                         {call[0]: call[1:4] for call in one if call[0] is not None})
        self.assertIs(by_name["alone"][4], main)
        workers = {by_name[name][4] for name in self.CONCURRENT}
        self.assertNotIn(main, workers)
        self.assertEqual(len(workers), 4, "each check on a thread of its own")
        self.assertEqual(threads, {"tool_env": {main}, "step_done": {main},
                                   "write_text": {main}})


class Workers(Stand):
    """At most `workers` checks of a group at once; STOICHEIA_CHECK_WORKERS read, capped
    at half the cores and said, and refused, naming it, unless a whole number from 1."""

    def test_never_more_than_the_workers(self):
        marks = self.marks()
        names = [f"check {n}" for n in range(1, 6)]
        steps = [self.stand_in(marks, name, 0.6) for name in names]
        refusal, done, _, _ = self.run_steps(steps, 2, set(names))
        self.assertIsNone(refusal)
        events = sorted([(self.times(marks, n)[0], 1) for n in names]
                        + [(self.times(marks, n)[1], -1) for n in names])
        most, now = 0, 0
        for _, step in events:
            now += step
            most = max(most, now)
        self.assertEqual(most, 2)

    def workers(self, value, cores=16):
        env = {k: v for k, v in os.environ.items() if k != safe_push.CHECK_WORKERS}
        if value is not None:
            env[safe_push.CHECK_WORKERS] = value
        with mock.patch.dict(os.environ, env, clear=True), \
                mock.patch.object(safe_push.os, "cpu_count", return_value=cores):
            return safe_push.check_workers()

    def test_the_variable_is_read_capped_and_said(self):
        self.assertEqual(self.workers(None), (1, ""))
        self.assertEqual(self.workers(""), (1, ""))
        self.assertEqual(self.workers("3"), (3, "; the concurrent checks run up to 3 at once "
                                              "(STOICHEIA_CHECK_WORKERS=3, the cap 8, half "
                                              "this machine's 16 cores)"))
        self.assertEqual(self.workers("1000", cores=4),
                         (2, "; the concurrent checks run up to 2 at once "
                             "(STOICHEIA_CHECK_WORKERS=1000, capped at 2, half this "
                             "machine's 4 cores)"))
        self.assertEqual(self.workers("9" * 5000, cores=1)[0], 1)
        self.assertEqual(self.workers("002", cores=1)[0], 1)
        for bad in ("0", "-1", "x", "000", " 2", "2.0", "٣"):
            with self.subTest(bad=bad), self.assertRaises(safe_push.Refusal) as raised:
                self.workers(bad)
            self.assertEqual(str(raised.exception), "STOICHEIA_CHECK_WORKERS must be a whole "
                             f"number from 1, not {bad!r}")

    def test_the_check_list_line_says_it_or_fails(self):
        root = committed(folder({"10-a.toml": registry_entry(10, ["python3", "-c", "pass"],
                                                             "concurrent = true\n")}))
        self.addCleanup(shutil.rmtree, root, ignore_errors=True)
        ctx = types.SimpleNamespace(repo=root, base="HEAD")

        def listed(value):
            rep, refusal = safe_push.Report(), None
            env = dict(os.environ, **{safe_push.CHECK_WORKERS: value})
            with mock.patch.dict(os.environ, env), \
                    mock.patch.object(safe_push.os, "cpu_count", return_value=8), \
                    contextlib.redirect_stdout(io.StringIO()):
                try:
                    checks = safe_push.check_list(ctx, rep)
                except safe_push.Refusal as e:
                    checks, refusal = None, str(e)
            [step] = rep.steps
            return checks, refusal, step
        checks, refusal, step = listed("9")
        self.assertIsNone(refusal)
        self.assertEqual((step.name, step.outcome), ("check list", "ok"))
        self.assertTrue(step.detail.endswith("; the concurrent checks run up to 4 at once "
                                             "(STOICHEIA_CHECK_WORKERS=9, capped at 4, half "
                                             "this machine's 8 cores)"), step.detail)
        self.assertEqual(checks.workers, 4)
        for bad in ("0", "-1", "x"):
            with self.subTest(bad=bad):
                checks, refusal, step = listed(bad)
                said = f"STOICHEIA_CHECK_WORKERS must be a whole number from 1, not {bad!r}"
                self.assertEqual((step.name, step.outcome, step.detail),
                                 ("check list", "FAIL", said))
                self.assertEqual(refusal, said)

    def test_the_variable_reaches_the_checks_and_the_cache_key(self):
        with mock.patch.dict(os.environ, {safe_push.CHECK_WORKERS: "3"}):
            self.assertEqual(safe_push.tool_env()[safe_push.CHECK_WORKERS], "3")
            variables = dict(safe_push.environment(self.root)["variables"])
        self.assertEqual(variables[safe_push.CHECK_WORKERS], "3")


class Interrupted(Stand):
    """Interrupted while two checks run at two workers, each waiting for a child that sleeps,
    by Ctrl-C's KeyboardInterrupt or by _terminate's for a SIGTERM, and again while the pass
    waits: the pass raises the first, and only once both checks and both children have
    ended, no process of theirs left and no later check started. And an interrupt that
    comes just after a check's thread is started: that check runs whole, or not at all."""

    SECONDS = 3     # each child's sleep

    def test_the_pass_waits_for_the_checks_running(self):
        for first, second, said in ((signal.SIGINT, signal.SIGINT, ""),
                                    (signal.SIGTERM, signal.SIGINT, f"signal {signal.SIGTERM}")):
            with self.subTest(first=first.name):
                self.interrupted(first, second, said)

    def interrupted(self, first: int, second: int, said: str):
        marks = self.marks()
        alone_ran = marks / "alone-ran"
        steps = [(name, py(PARENT) + [str(marks), name, str(self.SECONDS)])
                 for name in ("one", "two")] + [("alone", py(f"open({str(alone_ran)!r}, 'w')"))]
        pids = [marks / f"{name}.{what}" for name in ("one", "two")
                for what in ("check", "child")]
        sent, returned = [], threading.Event()

        def interrupt():
            deadline = time.monotonic() + 20
            while time.monotonic() < deadline and not all(p.exists() for p in pids):
                time.sleep(0.05)
            for signum in (first, second):
                if returned.is_set():
                    break
                sent.append(time.time())
                os.kill(os.getpid(), signum)
                time.sleep(0.5)
        handlers = {signum: signal.getsignal(signum) for signum in (signal.SIGINT, signal.SIGTERM)}
        signal.signal(signal.SIGINT, signal.default_int_handler)
        signal.signal(signal.SIGTERM, safe_push._terminate)
        began = time.monotonic()
        sender = threading.Thread(target=interrupt, daemon=True)
        try:
            sender.start()
            with self.assertRaises(KeyboardInterrupt) as raised:
                self.run_steps(steps, 2, {"one", "two"})
            out = time.time()
            returned.set()
            while sender.is_alive():
                with contextlib.suppress(KeyboardInterrupt):
                    sender.join(1)
        finally:
            for signum, handler in handlers.items():
                signal.signal(signum, handler)
        self.assertTrue(all(p.exists() for p in pids), "the checks never started their children")
        left = [p.name for p in pids if running(int(p.read_text()))]
        for p in pids:      # only what is still running, so that no other process is hit
            if p.name in left:
                os.kill(int(p.read_text()), signal.SIGKILL)
        self.assertEqual(left, [], "left running when the pass raised")
        self.assertEqual(str(raised.exception), said, "not the first exception")
        self.assertEqual(len(sent), 2, "the pass raised before the second signal")
        self.assertLess(sent[1], out)
        for name in ("one", "two"):
            ended = marks / f"{name}.end"
            self.assertTrue(ended.exists(), f"{name} had not ended when the pass raised")
            self.assertLess(sent[0], float(ended.read_text()), "it ended before the signal")
            self.assertLess(float(ended.read_text()), out)
        self.assertFalse(alone_ran.exists())
        self.assertLess(time.monotonic() - began, 30)

    def test_a_check_whose_start_is_interrupted_runs_whole_or_not_at_all(self):
        marks = self.marks()
        steps = [self.stand_in(marks, "first", 0.5), self.stand_in(marks, "second", 0.5)]
        starts = []

        class Interrupting(threading.Thread):
            def start(self):
                super().start()
                starts.append(self)
                if len(starts) == 2:
                    raise KeyboardInterrupt
        with mock.patch.object(safe_push.threading, "Thread", Interrupting), \
                self.assertRaises(KeyboardInterrupt):
            self.run_steps(steps, 2, {"first", "second"})
        out = time.time()
        time.sleep(1.5)     # long enough for a check left running to mark its start and end
        self.assertEqual(len(starts), 2)
        self.assertLess(self.times(marks, "first")[1], out)
        started = {p.stem for p in marks.glob("*.start")}
        self.assertEqual(started, {p.stem for p in marks.glob("*.end")})
        for name in started:
            self.assertLess(self.times(marks, name)[1], out, f"{name} ran on after the pass")


def folder(files: dict) -> Path:
    """A root of the test's own: scripts/registry.py as this checkout holds it, and checks/
    holding `files`."""
    root = Path(tempfile.mkdtemp(prefix="concurrent-registry-"))
    (root / "scripts").mkdir()
    shutil.copy2(SCRIPTS / "registry.py", root / "scripts" / "registry.py")
    (root / "checks").mkdir()
    for name, text in files.items():
        (root / "checks" / name).write_text(text)
    (root / ".gitignore").write_text("__pycache__/\n")
    return root


def committed(root: Path, message: str = "A registry for the test") -> Path:
    if not (root / ".git").exists():
        git(root, "init", "-q")
    git(root, "add", "-A")
    git(root, "commit", "-q", "--allow-empty", "-m", message)
    return root


class Registry(unittest.TestCase):
    """The two fields: `concurrent = true` accepted, every other use refused naming the
    file, from the worktree and from Git alike; as_json carrying them; check_sequence
    reading them and holding their rules itself; and none declared without them."""

    FIRST = registry_entry(10, ["python3", "-c", "print(1)"])
    ALONG = "concurrent = true\n"

    def tearDown(self):
        for root in getattr(self, "roots", []):
            shutil.rmtree(root, ignore_errors=True)

    def root(self, files: dict) -> Path:
        root = folder(files)
        self.roots = getattr(self, "roots", []) + [root]
        return root

    def test_concurrent_and_after_are_read(self):
        root = committed(self.root({
            "10-a.toml": self.FIRST, "20-b.toml": registry_empty(20),
            "30-c.toml": registry_entry(30, ["python3", "-c", "pass"], self.ALONG),
            "40-d.toml": registry_entry(40, ["python3", "-c", "print(4)"], self.ALONG
                                        + 'after = ["python3 -c print(1)", "python3 -c pass"]\n')}))
        for rev in (None, "HEAD"):
            with self.subTest(rev=rev):
                entries = registry.load(root, rev)
                self.assertEqual([(e.concurrent, e.after) for e in entries],
                                 [(False, ()), (False, ()), (True, ()),
                                  (True, ("python3 -c print(1)", "python3 -c pass"))])
        listed = json.loads(registry.as_json(registry.load(root)))
        self.assertEqual([(e["concurrent"], e["after"]) for e in listed],
                         [(False, []), (False, []), (True, []),
                          (True, ["python3 -c print(1)", "python3 -c pass"])])
        checks = safe_push.check_sequence(root, "HEAD")
        self.assertEqual(checks.concurrent, frozenset({"python3 -c pass", "python3 -c print(4)"})
                         | safe_push.MODEL_JOB_CONCURRENT)
        self.assertEqual(checks.after, {"python3 -c pass": (),
                                        "python3 -c print(4)": ("python3 -c print(1)",
                                                                "python3 -c pass")})

    def test_a_registry_without_them_declares_nothing(self):
        root = committed(self.root({"10-a.toml": self.FIRST, "20-b.toml": registry_empty(20)}))
        checks = safe_push.check_sequence(root, "HEAD")
        self.assertEqual(checks.concurrent, frozenset())
        self.assertEqual(checks.after, {})
        self.assertEqual(checks.workers, 1)
        listed = json.loads(registry.as_json(registry.load(root)))
        self.assertEqual({(e["concurrent"], tuple(e["after"])) for e in listed}, {(False, ())})

    def test_the_reader_refuses_every_other_use(self):
        at = "checks/20-b.toml"
        good = registry_entry(20, ["python3", "-c", "pass"])
        cases = (
            ("concurrent false", good + "concurrent = false\n",
             f"{at}: concurrent is true, or absent"),
            ("concurrent a string", good + 'concurrent = "true"\n',
             f"{at}: concurrent is true, or absent"),
            ("concurrent a number", good + "concurrent = 1\n",
             f"{at}: concurrent is true, or absent"),
            ("concurrent with empty", registry_empty(20, self.ALONG),
             f"{at}: the check with empty judges the whole worktree"),
            ("after without concurrent", good + 'after = ["python3 -c print(1)"]\n',
             f"{at}: after is for a concurrent check"),
            ("after a string", good + self.ALONG + 'after = "python3 -c print(1)"\n',
             f"{at}: after must be a list of checks' names"),
            ("after of numbers", good + self.ALONG + "after = [1]\n",
             f"{at}: after must be a list of checks' names"),
            ("after naming one twice", good + self.ALONG
             + 'after = ["python3 -c print(1)", "python3 -c print(1)"]\n',
             f"{at}: after must be a list of checks' names, each once"),
            ("after naming a later check", good + self.ALONG + 'after = ["python3 -c later"]\n',
             f"{at}: after names 'python3 -c later', which is no earlier check's name"),
            ("after naming no check", good + self.ALONG + 'after = ["nothing"]\n',
             f"{at}: after names 'nothing', which is no earlier check's name"),
            ("after naming itself", good + self.ALONG + 'after = ["python3 -c pass"]\n',
             f"{at}: after names 'python3 -c pass', which is no earlier check's name"),
        )
        later = registry_entry(30, ["python3", "-c", "later"])
        for label, text, message in cases:
            with self.subTest(label):
                root = self.root({"10-a.toml": self.FIRST, "20-b.toml": text,
                                  "30-c.toml": later})
                with self.assertRaises(registry.RegistryError) as raised:
                    registry.load(root)
                self.assertIn(message, str(raised.exception))
                committed(root)
                with self.assertRaises(registry.RegistryError) as raised:
                    registry.load(root, "HEAD")
                self.assertIn(message, str(raised.exception))

    def test_safe_push_holds_their_rules_itself(self):
        # A reader at origin/main that prints what its own rules would refuse: check_sequence
        # refuses it, as it refuses a check named otherwise than its command.
        root = committed(self.root({"10-a.toml": self.FIRST}))
        first = {"name": "true", "command": ["true"], "empty": False}

        def printing(*entries) -> str:
            listed = [dict(e, job="check") for e in entries]
            return f"import json\nprint(json.dumps({listed!r}))\n"
        empty = {"name": safe_push.EMPTY_CHECK, "command": None, "empty": True}
        second = {"name": "false", "command": ["false"], "empty": False}
        cases = (
            ("concurrent a string", [first, dict(second, concurrent="yes")]),
            ("concurrent a number", [first, dict(second, concurrent=1)]),
            ("the empty check concurrent", [first, dict(empty, concurrent=True)]),
            ("after without concurrent", [first, dict(second, after=["true"])]),
            ("after naming a later check", [dict(first, concurrent=True, after=["false"]),
                                            second]),
            ("after not a list", [first, dict(second, concurrent=True, after="true")]),
        )
        for label, entries in cases:
            with self.subTest(label):
                (root / "scripts" / "registry.py").write_text(printing(*entries))
                committed(root, label)
                with self.assertRaises(safe_push.Refusal) as raised:
                    safe_push.check_sequence(root, "HEAD")
                self.assertIn("origin/main's registry of checks could not be read",
                              str(raised.exception))
                self.assertIn("concurrent is true or false, never for the `empty` check, and "
                              "after lists earlier checks of a concurrent one",
                              str(raised.exception))
        # And as they should be.
        (root / "scripts" / "registry.py").write_text(printing(
            dict(first, concurrent=False), dict(second, concurrent=True, after=["true"])))
        committed(root, "As they should be")
        checks = safe_push.check_sequence(root, "HEAD")
        self.assertEqual(checks.concurrent, {"false"} | safe_push.MODEL_JOB_CONCURRENT)
        self.assertEqual(checks.after, {"false": ("true",)})


class TheRegistry(unittest.TestCase):
    """The real registry's declarations, as #608's audit found them: a change to them is a
    change to this list too, made on purpose."""

    CONCURRENT = {
        "python3 -I tests/test_check_paths.py",
        "python3 scripts/check_paths.py --self-test",
        "python3 -I tests/test_certificate.py",
        "python3 scripts/sweep_citations.py --self-test",
        "python3 scripts/check_kernel.py --self-test",
        "python3 scripts/check_fidelity.py",
        "python3 -I tests/test_release_gate.py",
        "python3 -I tests/test_jev_models.py",
        "python3 scripts/audit/jev.py self-test",
        "python3 -I tests/test_screen.py",
        "python3 scripts/test_safe_push.py "
        "Units.test_every_step_after_the_lane_step_carries_its_condition",
        "python3 -I tests/test_acceptance_limits.py",
        "python3 -I tests/test_check_superposition_pins.py",
        "python3 -I scripts/check_superposition_pins.py",
        "python3 scripts/check_style.py",
        "python3 scripts/check_queue.py --tree .",
        "python3 scripts/check_links.py",
    }
    AFTER = {
        "python3 scripts/check_paths.py --self-test": ("python3 -I tests/test_check_paths.py",),
        "python3 -I scripts/check_superposition_pins.py":
            ("python3 -I tests/test_check_superposition_pins.py",),
    }
    ALONE = {
        "python3 -I tests/test_concurrent_checks.py",
        "lake build", "lake build Audit", "lake build Staging",
        "lake env lean Certificate/Facts.lean",
        "python3 scripts/sweep_citations.py",
        "python3 scripts/heath.py",
        "python3 -I tests/test_check_style.py",
        "python3 scripts/render.py",
        safe_push.EMPTY_CHECK,
    }

    def test_the_declarations_are_the_audits(self):
        entries = registry.load(REPO)
        self.assertEqual({e.name for e in entries if e.concurrent}, self.CONCURRENT)
        self.assertEqual({e.name for e in entries if not e.concurrent}, self.ALONE)
        self.assertEqual({e.name: e.after for e in entries if e.after}, self.AFTER)
        self.assertEqual(safe_push.MODEL_JOB_CONCURRENT,
                         {"python3 -I tests/model/run.py --fast"})
        # Each says why, in a comment line of its own.
        for entry in entries:
            text = (REPO / entry.path).read_text()
            word = "Concurrent" if entry.concurrent else "Alone"
            self.assertEqual(text.count("(#608)"), 1, entry.path)
            self.assertIn(f"\n# {word} (#608)", "\n" + text, entry.path)


if __name__ == "__main__":
    unittest.main()
