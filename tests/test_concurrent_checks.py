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
three, whether it writes a tracked file, an untracked one, an ignored one, one under the
build's cache, or flags an entry of the index; the worktree's state taken writing nothing;
every check started by run(), at one worker exactly as before #608, on this thread with no
thread or handler started, and at more on threads of their own, the report and logs
written on this thread; never more checks at once than the workers, the cap of
STOICHEIA_CHECK_WORKERS said, a bad value failing the check list line, and the variable not
read for a sequence that declares nothing concurrent; and, sent SIGINT, SIGTERM and SIGHUP
again and again while two checks run, the pass raising what the first would have raised,
only once both checks and their children have ended, with the handlers put back, as they
are on every way out; or with a check's end lost to an exception, the pass still going on
once both checks have ended. The registry's reader accepts
`concurrent = true` and refuses every other use of the two fields; as_json carries them;
safe_push's check_sequence reads them, and holds their rules itself; a registry without
them declares nothing concurrent; and the real registry declares what #608's audit found,
so that a change to it is made on purpose. Every order a case asserts is forced by marks
the checks wait for, never by how long they sleep, so that a busy machine slows a case but
does not fail it: a check gives up waiting only after HOLD seconds, which a right run never
comes near. It runs alone in the sequence, since it starts processes of its own and
measures how many run at once.
"""

import contextlib
import io
import json
import os
import queue
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
# How long a check waits for the mark it holds for before it gives up, failing: never
# reached when the run is right, so that a busy machine only slows a case.
HOLD = 60

# A stand-in check: it notes the marks it sees, then marks its start, sleeps the seconds
# given, holds until the mark given exists (if one is), prints a line to each stream, marks
# its end, and exits with the code given. Each mark is a file made with O_EXCL, so a check
# run twice fails.
STAND_IN = f"""
import os, sys, time
marks, name, seconds, code = sys.argv[1], sys.argv[2], float(sys.argv[3]), int(sys.argv[4])
hold = sys.argv[5] if len(sys.argv) > 5 else ""
def mark(what, text=""):
    fd = os.open(os.path.join(marks, name + "." + what), os.O_WRONLY | os.O_CREAT | os.O_EXCL)
    os.write(fd, text.encode())
    os.close(fd)
mark("seen", "\\n".join(sorted(os.listdir(marks))))
mark("start")
time.sleep(seconds)
given_up = time.monotonic() + {HOLD}
while hold and not os.path.exists(os.path.join(marks, hold)):
    if time.monotonic() > given_up:
        sys.exit(9)
    time.sleep(0.01)
print(name, "says this on stdout")
print(name, "says this on stderr", file=sys.stderr)
mark("end")
sys.exit(code)
"""

# A check that starts a child, which holds until the release mark given exists, notes both
# pids, and waits for the child before it marks its own end.
PARENT = f"""
import os, subprocess, sys
marks, name, release = sys.argv[1], sys.argv[2], sys.argv[3]
def note(what, text):
    path = os.path.join(marks, name + "." + what)
    with open(path + ".tmp", "w") as f:
        f.write(text)
    os.replace(path + ".tmp", path)
HOLDING = ("import os, sys, time\\n"
           "given_up = time.monotonic() + {HOLD}\\n"
           "while not os.path.exists(sys.argv[1]) and time.monotonic() < given_up:\\n"
           "    time.sleep(0.01)\\n")
child = subprocess.Popen([sys.executable, "-c", HOLDING, release])
note("child", str(child.pid))
note("check", str(os.getpid()))
child.wait()
note("end", "")
"""

# A pass of its own, on the main thread of a Python of its own, which alone takes a signal's
# handler: two such checks at two workers, each released by its own mark, then a check that
# runs alone. Its harness's handlers are set as main() sets them; each signal the group's
# handler records is marked as it comes, numbered. It prints what the pass raised, which
# checks had ended as it raised, the signals that handler took, and whether the handlers
# were put back.
SIGNALLED = """
import contextlib, io, json, os, signal, sys
from pathlib import Path
scripts, root, marks, logs, parent = sys.argv[1:6]
sys.path.insert(0, scripts)
import safe_push
for signum in (signal.SIGTERM, signal.SIGHUP):
    signal.signal(signum, safe_push._terminate)
before = {signum: signal.getsignal(signum) for signum in safe_push.GROUP_SIGNALS}
real, handled = safe_push.recorder, []
def recorder(caught):
    record = real(caught)
    def marking(signum, frame):
        handled.append(signum)
        open(os.path.join(marks, f"handled.{len(handled)}"), "w").close()
        record(signum, frame)
    return marking
safe_push.recorder = recorder
steps = [(name, [sys.executable, "-c", parent, marks, name,
                 os.path.join(marks, "release-" + name)]) for name in ("one", "two")]
alone = os.path.join(marks, "alone-ran")
steps.append(("alone", [sys.executable, "-c", f"open({alone!r}, 'w')"]))
plan = safe_push.CheckList(steps, "", concurrent=frozenset({"one", "two"}), workers=2)
raised = None
try:
    with contextlib.redirect_stdout(io.StringIO()):
        safe_push.run_sequence(steps, Path(root), safe_push.Report(), Path(logs), "", "FAIL",
                               [], 10, plan)
except BaseException as e:
    raised = [type(e).__name__, str(e)]
ended = sorted(n for n in ("one", "two") if os.path.exists(os.path.join(marks, n + ".end")))
restored = all(signal.getsignal(signum) is before[signum] for signum in before)
print(json.dumps({"raised": raised, "ended": ended, "handled": handled,
                  "restored": restored}))
"""
# How many passes the signals are put to, and how many signals each burst sends.
ROUNDS = 12
BURST = 20


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
    """A Git repository of the test's own, with a tracked file, and out/, the build's cache
    .lake/ and Python's bytecode ignored, the last two as the repository ignores them; and
    run_sequence on it as step 4 runs a pass, with no sandbox."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="concurrent-checks-"))
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)
        self.root = self.tmp / "repo"
        self.root.mkdir()
        git(self.root, "init", "-q")
        (self.root / ".gitignore").write_text("__pycache__/\n*.pyc\nout/\n/.lake\n")
        (self.root / "tracked.txt").write_text("A tracked file.\n")
        git(self.root, "add", "-A")
        git(self.root, "commit", "-q", "-m", "A repository for the test")
        self.runs = 0

    def marks(self) -> Path:
        self.runs += 1
        path = self.tmp / f"marks-{self.runs}"
        path.mkdir()
        return path

    def stand_in(self, marks: Path, name: str, seconds: float = 0.0, code: int = 0,
                 hold: str = ""):
        return (name, py(STAND_IN) + [str(marks), name, str(seconds), str(code)]
                + ([hold] if hold else []))

    def run_steps(self, steps, workers=1, concurrent=(), after=None, fail="FAIL",
                  label="", cache=None, plan=True):
        """run_sequence on `steps`, declared as given (no plan when `plan` is false): its
        refusal, if any; its steps; its logs, by name; and the logs' folder."""
        logs = self.tmp / f"logs-{self.runs}-{workers}-{len(os.listdir(self.tmp))}"
        logs.mkdir()
        declared = safe_push.CheckList(list(steps), "", concurrent=frozenset(concurrent),
                                       after=types.MappingProxyType(dict(after or {})),
                                       workers=workers) if plan else None
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

    def marked(self, marks: Path, what: str) -> set[str]:
        """The checks that have made the mark `what`: start or end."""
        return {p.stem for p in marks.glob(f"*.{what}")}

    def seen(self, marks: Path, name: str) -> set[str]:
        """The marks the check `name` saw before it marked its start."""
        return set((marks / f"{name}.seen").read_text().split("\n")) - {""}


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
                # At three, the earlier failure holds until the later one has ended, so the
                # later ends first; at one, the later never starts.
                hold = "fails late.end" if workers == 3 else ""
                steps = [self.stand_in(marks, "first"),
                         self.stand_in(marks, "fails early", code=3, hold=hold),
                         self.stand_in(marks, "fails late", code=4),
                         self.stand_in(marks, "after them"),
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
                started, ended = self.marked(marks, "start"), self.marked(marks, "end")
                self.assertEqual(started, ended, "a check was left running")
                if workers == 3:
                    self.assertIn("fails late", ended)      # ended first, and not reported
                else:
                    self.assertEqual(started, {"first", "fails early"})

    def test_a_check_still_running_is_waited_for(self):
        marks = self.marks()
        # The passing check holds until the failing one has ended: it is still running when
        # the failure comes.
        steps = [self.stand_in(marks, "slow pass", hold="quick fail.end"),
                 self.stand_in(marks, "quick fail", code=1)]
        refusal, done, logs, _ = self.run_steps(steps, 2, {"slow pass", "quick fail"})
        self.assertEqual(refusal, "`quick fail` failed on the commit")
        self.assertEqual([(s.name, s.outcome) for s in done],
                         [("slow pass", "ok"), ("quick fail", "FAIL")])
        # The slow check had ended before the pass returned, its log written.
        self.assertTrue((marks / "slow pass.end").exists())
        self.assertIn("11-slow-pass.log", logs)

    def test_a_published_failure_prevents_the_next_start(self):
        marks = self.marks()
        published = threading.Event()
        steps = [self.stand_in(marks, "passes"),
                 self.stand_in(marks, "fails", code=1, hold="release"),
                 self.stand_in(marks, "after")]

        class Publishing(queue.SimpleQueue):
            def put(self, item, *args, **kwargs):
                super().put(item, *args, **kwargs)
                if item[0] == "fails":
                    published.set()

            def get(self, *args, **kwargs):
                item = super().get(*args, **kwargs)
                if item[0] == "passes":
                    (marks / "release").touch()
                    published.wait(HOLD)
                return item

        with mock.patch.object(safe_push.queue, "SimpleQueue", Publishing):
            refusal, _, _, _ = self.run_steps(steps, 2, {name for name, _ in steps})
        self.assertTrue(published.is_set(), "the failure was not published")
        self.assertEqual(refusal, "`fails` failed on the commit")
        self.assertFalse((marks / "after.start").exists())

    def test_an_exception_comes_in_its_place(self):
        # A check whose run() raises (here, no such program) raises in registry order, as
        # run_step's run() does: the checks before it reported, none after it, and every
        # check started waited for, at one worker and at three, in either kind of pass.
        missing = str(self.tmp / "no-such-program")
        for fail in ("FAIL", "note"):
            for workers in (1, 3):
                with self.subTest(fail=fail, workers=workers):
                    marks = self.marks()
                    # At three, the first holds until the one beside it has started.
                    hold = "beside.start" if workers == 3 else ""
                    steps = [self.stand_in(marks, "slow", hold=hold), ("missing", [missing]),
                             self.stand_in(marks, "beside"),
                             ("alone", py(f"open({str(marks / 'alone-ran')!r}, 'w')"))]
                    with self.assertRaises(FileNotFoundError) as raised:
                        self.run_steps(steps, workers, {"slow", "missing", "beside"},
                                       fail=fail)
                    self.assertIn(missing, str(raised.exception))
                    self.assertTrue((marks / "slow.end").exists())
                    started = self.marked(marks, "start")
                    self.assertEqual(started, self.marked(marks, "end"))
                    self.assertEqual(started, {"slow", "beside"} if workers == 3 else {"slow"})
                    self.assertFalse((marks / "alone-ran").exists())
                    logs = sorted(p.name for p in self.tmp.glob(f"logs-{self.runs}-*/*"))
                    self.assertEqual(logs, ["11-slow.log"])


class Order(Stand):
    """`after` holds a check back until the checks it names have ended, and a check that
    runs alone is a barrier: the group after it starts once it has ended."""

    def test_after_waits_for_the_checks_it_names(self):
        marks = self.marks()
        # The first holds until the one beside it has started: the group runs together, or
        # the first gives up and fails.
        steps = [("set up", py("pass")),
                 self.stand_in(marks, "first", hold="beside.start"),
                 self.stand_in(marks, "beside"), self.stand_in(marks, "waits")]
        after = {"waits": ("set up", "first")}
        refusal, done, _, _ = self.run_steps(steps, 3, {"first", "beside", "waits"}, after)
        self.assertIsNone(refusal)
        self.assertEqual([s.name for s in done], ["set up", "first", "beside", "waits"])
        self.assertIn("first.end", self.seen(marks, "waits"), "waits began before first ended")

    def test_a_check_alone_is_a_barrier(self):
        before = py("import os, sys; sys.exit(os.path.exists('out/barrier.txt'))")
        writer = py("import os; os.makedirs('out', exist_ok=True); "
                    "open('out/barrier.txt', 'w').write('x')")
        after = py("import os, sys; sys.exit(not os.path.exists('out/barrier.txt'))")
        steps = [("before", before), ("writer", writer), ("after", after)]
        refusal, done, _, _ = self.run_steps(steps, 3, {"before", "after"})
        self.assertIsNone(refusal)
        # The writer, alone, writes what it likes, and the group after it takes its state
        # once the writer has ended: no step is added.
        self.assertEqual([(s.name, s.outcome) for s in done],
                         [("before", "ok"), ("writer", "ok"), ("after", "ok")])
        # Declared concurrent, the middle check is no barrier: holding until the check after
        # it has started, it ends after that check began. It writes only its marks, outside
        # the tree.
        marks = self.marks()
        steps = [self.stand_in(marks, "before"),
                 self.stand_in(marks, "middle", hold="after.start"),
                 self.stand_in(marks, "after")]
        refusal, done, _, _ = self.run_steps(steps, 3, {"before", "middle", "after"})
        self.assertIsNone(refusal)
        self.assertEqual([(s.name, s.outcome) for s in done],
                         [("before", "ok"), ("middle", "ok"), ("after", "ok")])
        self.assertNotIn("middle.end", self.seen(marks, "after"))


class Planted(Stand):
    """A check declared concurrent that writes in the tree is refused, at one worker and at
    three, the step naming the group's checks and the path; in a noting pass it is noted,
    every check runs, and the pass is kept out of the main-checks cache."""

    WRITES = (
        ("an untracked file", "open('planted.txt', 'w').write('x')", "?? planted.txt"),
        ("a tracked file", "open('tracked.txt', 'a').write('more')", "M tracked.txt"),
        ("an ignored file", "import os; os.makedirs('out', exist_ok=True); "
                            "open('out/x', 'w').write('x')", "!! out/x"),
        ("a file of the build's cache", "open('.lake/x', 'a').write('more')", "!! .lake/x"),
        ("the index", "import subprocess; subprocess.run(['git', 'update-index', "
                      "'--skip-worktree', 'tracked.txt'], check=True); "
                      "open('tracked.txt', 'a').write('more')",
         "the index changed (git ls-files --stage -v)"),
        ("the index, an entry assumed unchanged",
         "import subprocess; subprocess.run(['git', 'update-index', '--assume-unchanged', "
         "'tracked.txt'], check=True); open('tracked.txt', 'a').write('more')",
         "the index changed (git ls-files --stage -v)"),
    )

    def planted(self, marks: Path, write: str):
        return [self.stand_in(marks, "reader", 0.1), ("planter", py(write)),
                ("later", py(f"open({str(marks / 'later-ran')!r}, 'w')"))]

    def reset(self):
        """The repository as committed, and .lake/x as a build left it."""
        git(self.root, "update-index", "--no-skip-worktree", "tracked.txt")
        git(self.root, "update-index", "--no-assume-unchanged", "tracked.txt")
        git(self.root, "checkout", "-q", "--", ".")
        git(self.root, "clean", "-fdxq")
        (self.root / ".lake").mkdir()
        (self.root / ".lake" / "x").write_text("Built.\n")

    def test_a_check_that_writes_the_tree_is_refused(self):
        for what, write, change in self.WRITES:
            for workers in (1, 3):
                with self.subTest(what, workers=workers):
                    self.reset()
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
    """tree_state takes HEAD, the index's entries, and the worktree's files, ignored ones
    with them but Python's bytecode, each file hashed but under the build's cache, and
    writes nothing: not the index, not an object."""

    def test_the_state_is_taken_writing_nothing(self):
        git_dir = self.root / ".git"

        def written():
            index = git_dir / "index"
            return (index.read_bytes(), os.stat(index).st_mtime_ns,
                    sorted(p for p in (git_dir / "objects").rglob("*") if p.is_file()))

        def letters(state):
            return {path: letters for path, (letters, _) in state.paths.items()}
        (self.root / "tracked.txt").write_text("Changed.\n")
        (self.root / "new.txt").write_text("New.\n")
        for path in ("out/ignored.txt", ".lake/build/a.olean", "__pycache__/m.cpython-314.pyc",
                     "loose.pyc"):
            (self.root / path).parent.mkdir(parents=True, exist_ok=True)
            (self.root / path).write_text("Written.\n")
        before = written()
        state = safe_push.tree_state(self.root)
        self.assertEqual(written(), before)
        self.assertEqual(state.head, git(self.root, "rev-parse", "HEAD").strip())
        self.assertEqual(letters(state), {"tracked.txt": " M", "new.txt": "??",
                                          "out/ignored.txt": "!!", ".lake/build/a.olean": "!!"})
        self.assertEqual(state.paths["out/ignored.txt"][1][0], "file")      # hashed
        self.assertEqual(state.paths[".lake/build/a.olean"][1][0], "stat")  # its lstat
        # Changed again, git's letters the same: the state differs, and names the path.
        (self.root / "tracked.txt").write_text("Changed again.\n")
        again = safe_push.tree_state(self.root)
        self.assertEqual(safe_push.tree_changes(state, again), "M tracked.txt")
        # Put back as the index holds it, and untracked files taken away.
        git(self.root, "checkout", "-q", "--", "tracked.txt")
        for path in ("new.txt", "out/ignored.txt", ".lake/build/a.olean"):
            (self.root / path).unlink()
        back = safe_push.tree_state(self.root)
        self.assertEqual(back.paths, {})
        self.assertEqual(safe_push.tree_changes(again, back),
                         ".lake/build/a.olean (no longer listed by git), "
                         "new.txt (no longer listed by git), "
                         "out/ignored.txt (no longer listed by git), "
                         "tracked.txt (no longer listed by git)")
        # A mode changed, and a link.
        os.chmod(self.root / "tracked.txt", 0o755)
        (self.root / "link").symlink_to("tracked.txt")
        moved = safe_push.tree_state(self.root)
        self.assertEqual(safe_push.tree_changes(back, moved), "?? link, M tracked.txt")
        # HEAD moved by a commit, and an entry of the index flagged.
        (self.root / "link").unlink()
        os.chmod(self.root / "tracked.txt", 0o644)
        still = safe_push.tree_state(self.root)
        git(self.root, "commit", "-q", "--allow-empty", "-m", "Another")
        committed_state = safe_push.tree_state(self.root)
        self.assertEqual(safe_push.tree_changes(still, committed_state),
                         f"HEAD moved from {still.head[:12]} to {committed_state.head[:12]}")
        git(self.root, "update-index", "--skip-worktree", "tracked.txt")
        before = written()
        flagged = safe_push.tree_state(self.root)
        self.assertEqual(written(), before)
        self.assertEqual(safe_push.tree_changes(committed_state, flagged),
                         "the index changed (git ls-files --stage -v)")


class ThroughRun(Stand):
    """Every check is started by run(), as every command of step 4 is. At one worker, as
    before #608: one after another on this thread, no thread started and no signal's
    handler installed, run() given for every check what run_step gave it before, and only
    the guard's reads of git added around each group. At more, each check of a group on a
    thread of its own, given the same, its
    environment built on this thread, and the report and the logs written on this thread
    alone."""

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
                               side_effect=AssertionError("a thread was started")), \
                mock.patch.object(safe_push.signal, "signal",
                                  side_effect=AssertionError("a handler was installed")):
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
        # Beside them, only the guard's four reads of git, before and after each of the two
        # groups.
        others = [call[1] for call in now if call[0] is None]
        reads = ["rev-parse", "ls-files", "status", "ls-files"] * 4
        self.assertEqual([cmd[:2] for cmd in others], [["git", "--no-optional-locks"]] * 16)
        self.assertEqual([cmd[2 + len(safe_push.DISK_AS_IS)] for cmd in others], reads)
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
    at half the cores and said, and refused, naming it, unless a whole number from 1; and
    not read for a sequence that declares nothing concurrent."""

    def test_never_more_than_the_workers(self):
        marks = self.marks()
        names = [f"check {n}" for n in range(1, 6)]
        # Each holds until the next has started, so that two run whenever the next starts.
        steps = [self.stand_in(marks, name, hold=f"{after}.start" if after else "")
                 for name, after in zip(names, names[1:] + [""])]
        refusal, done, _, _ = self.run_steps(steps, 2, set(names))
        self.assertIsNone(refusal)
        # How many each saw running as it began, itself with them.
        most = max(1 + len({p[:-6] for p in self.seen(marks, name) if p.endswith(".start")}
                           - {p[:-4] for p in self.seen(marks, name) if p.endswith(".end")})
                   for name in names)
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

    def listed(self, root: Path, value: str):
        """check_list on the registry at `root`, with STOICHEIA_CHECK_WORKERS `value` on a
        machine of eight cores: the list, the refusal if any, and the step."""
        ctx = types.SimpleNamespace(repo=root, base="HEAD")
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

    def test_the_check_list_line_says_it_or_fails(self):
        root = committed(folder({"10-a.toml": registry_entry(10, ["python3", "-c", "pass"],
                                                             "concurrent = true\n")}))
        self.addCleanup(shutil.rmtree, root, ignore_errors=True)
        checks, refusal, step = self.listed(root, "9")
        self.assertIsNone(refusal)
        self.assertEqual((step.name, step.outcome), ("check list", "ok"))
        self.assertTrue(step.detail.endswith("; the concurrent checks run up to 4 at once "
                                             "(STOICHEIA_CHECK_WORKERS=9, capped at 4, half "
                                             "this machine's 8 cores)"), step.detail)
        self.assertEqual(checks.workers, 4)
        for bad in ("0", "-1", "x"):
            with self.subTest(bad=bad):
                checks, refusal, step = self.listed(root, bad)
                said = f"STOICHEIA_CHECK_WORKERS must be a whole number from 1, not {bad!r}"
                self.assertEqual((step.name, step.outcome, step.detail),
                                 ("check list", "FAIL", said))
                self.assertEqual(refusal, said)

    def test_with_nothing_concurrent_the_variable_is_not_read(self):
        # Every check of such a sequence runs alone, so the line is as before #608, whatever
        # the variable holds.
        root = committed(folder({"10-a.toml": registry_entry(10, ["python3", "-c", "pass"])}))
        self.addCleanup(shutil.rmtree, root, ignore_errors=True)
        lines = set()
        for value in ("", "3", "x"):
            with self.subTest(value=value):
                checks, refusal, step = self.listed(root, value)
                self.assertIsNone(refusal)
                self.assertEqual((step.name, step.outcome), ("check list", "ok"))
                self.assertNotIn(safe_push.CHECK_WORKERS, step.detail)
                self.assertEqual(checks.workers, 1)
                lines.add(step.detail)
        self.assertEqual(len(lines), 1)

    def test_the_variable_reaches_the_checks_and_the_cache_key(self):
        with mock.patch.dict(os.environ, {safe_push.CHECK_WORKERS: "3"}):
            self.assertEqual(safe_push.tool_env()[safe_push.CHECK_WORKERS], "3")
            variables = dict(safe_push.environment(self.root)["variables"])
        self.assertEqual(variables[safe_push.CHECK_WORKERS], "3")


class Interrupted(Stand):
    """Sent SIGINT, SIGTERM and SIGHUP while two checks run at two workers, each waiting for
    a child that holds until it is released: the first, then a burst of SIGINT and SIGTERM
    close together, then, once one check has ended, another, round after round, the pass
    raises what the first signal would have raised, and only once both checks and both
    children have ended, no process of theirs left and no later check started, with the
    harness's handlers put back. Those handlers are put back on every way out of a group,
    and raise what signalled raises. With a check's end lost to an exception, taken from
    the queue but not taken in, the pass still raises once the checks have ended. And an
    exception that comes just after a check's thread is started: that check runs whole, or
    not at all."""

    def test_signals_while_a_group_runs_wait_for_its_checks(self):
        # Each pass is a Python of its own, so that its group runs on a main thread, which
        # alone takes a signal's handler. All the rounds together have HOLD seconds: a pass
        # still running then is killed, and the test fails, not wedges.
        said = {signal.SIGINT: "", signal.SIGTERM: f"signal {signal.SIGTERM}",
                signal.SIGHUP: f"signal {signal.SIGHUP}"}
        given_up = time.monotonic() + HOLD
        for round_ in range(ROUNDS):
            first = safe_push.GROUP_SIGNALS[round_ % len(safe_push.GROUP_SIGNALS)]
            with self.subTest(round=round_, first=first.name):
                marks = self.marks()
                outcome = self.signalled(marks, first, given_up)
                pids = [marks / f"{name}.{what}" for name in ("one", "two")
                        for what in ("check", "child")]
                self.assertTrue(all(p.exists() for p in pids),
                                "the checks never started their children")
                left = [p.name for p in pids if running(int(p.read_text()))]
                for p in pids:      # only what still runs, so that no other process is hit
                    if p.name in left:
                        with contextlib.suppress(ProcessLookupError):
                            os.kill(int(p.read_text()), signal.SIGKILL)
                self.assertEqual(left, [], "left running when the pass raised")
                self.assertEqual(outcome["raised"], ["KeyboardInterrupt", said[first]],
                                 "not what the first signal raises")
                self.assertEqual(outcome["ended"], ["one", "two"],
                                 "the pass raised before the checks ended")
                self.assertTrue(outcome["restored"], "the handlers were not put back")
                self.assertEqual(outcome["handled"][0], first)
                self.assertGreater(len(outcome["handled"]), 1, "no signal after the first")
                self.assertFalse((marks / "alone-ran").exists())

    def signalled(self, marks: Path, first: int, given_up: float) -> dict:
        """A pass of its own (SIGNALLED) sent `first` once both checks and their children
        run; once it has recorded it, a burst; once check `one`, released, has ended,
        another; then `two` released: what it printed. Killed, failing, at `given_up`."""
        logs = self.tmp / f"logs-{self.runs}-signalled"
        logs.mkdir()
        child = subprocess.Popen([sys.executable, "-I", "-c", SIGNALLED, str(SCRIPTS),
                                  str(self.root), str(marks), str(logs), PARENT],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

        def until(*paths: Path) -> bool:
            """Whether the paths exist while the pass still runs: polled last, so that a
            signal sent after a true answer reaches it, or its unreaped end, never another
            process given its pid."""
            while child.poll() is None and time.monotonic() < given_up:
                if all(p.exists() for p in paths):
                    return True
                time.sleep(0.01)
            return False

        def burst(kinds):
            for n in range(BURST):
                os.kill(child.pid, kinds[n % len(kinds)])
        try:
            if until(*(marks / f"{name}.{what}" for name in ("one", "two")
                       for what in ("check", "child"))):
                os.kill(child.pid, first)
                if until(marks / "handled.1"):
                    burst((signal.SIGINT, signal.SIGTERM))
                    (marks / "release-one").touch()
                    if until(marks / "one.end"):
                        burst((signal.SIGTERM, signal.SIGINT))
        except ProcessLookupError:
            pass        # the pass has ended: what it printed says how
        finally:
            (marks / "release-one").touch()
            (marks / "release-two").touch()
        try:
            out, err = child.communicate(timeout=max(0.0, given_up - time.monotonic()))
        except subprocess.TimeoutExpired:
            child.kill()
            child.communicate()
            self.fail(f"a pass still ran after {HOLD} s")
        self.assertEqual(child.returncode, 0, err)
        return json.loads(out)

    def test_the_handlers_are_put_back_on_every_way_out(self):
        # Handlers of the test's own, on this, the main thread: during the group each is
        # the recorder, and after it each is the test's again, whether the group passed,
        # refused, or raised what a check's run() raised. (A signal's way out is the test
        # above's.)
        signals = safe_push.GROUP_SIGNALS
        before = {signum: signal.getsignal(signum) for signum in signals}
        mine = {signum: (lambda signum, frame: None) for signum in signals}
        for signum, handler in mine.items():
            signal.signal(signum, handler)
        self.addCleanup(lambda: [signal.signal(s, h) for s, h in before.items()])
        during, real_run = [], safe_push.run

        def run(cmd, cwd, **kw):
            during.append({signum: signal.getsignal(signum) for signum in signals})
            return real_run(cmd, cwd, **kw)
        marks = self.marks()
        missing = str(self.tmp / "no-such-program")
        ways = (("passed", [self.stand_in(marks, "a"), self.stand_in(marks, "b")], None),
                ("refused", [self.stand_in(marks, "c", code=1), self.stand_in(marks, "d")],
                 safe_push.Refusal),
                ("raised", [("missing", [missing]), self.stand_in(marks, "e")],
                 FileNotFoundError))
        for way, steps, raised in ways:
            with self.subTest(way):
                during.clear()
                logs = self.tmp / f"logs-{way}"
                logs.mkdir()
                with mock.patch.object(safe_push, "run", run), \
                        contextlib.redirect_stdout(io.StringIO()), \
                        contextlib.ExitStack() as stack:
                    if raised is not None:
                        stack.enter_context(self.assertRaises(raised))
                    safe_push.run_together(steps, self.root, safe_push.Report(), logs, 11,
                                           "", "FAIL", types.MappingProxyType({}), 2)
                self.assertEqual({s: signal.getsignal(s) for s in signals}, mine)
                self.assertTrue(during)     # the first check's run() is called, at least
                for seen in during:
                    self.assertEqual(len({id(h) for h in seen.values()}), 1, seen)
                    self.assertTrue(all(h is not mine[s] for s, h in seen.items()), seen)

    def test_a_signal_recorded_before_thread_start_prevents_the_check(self):
        marks = self.marks()
        steps = [self.stand_in(marks, "first"), self.stand_in(marks, "after")]
        real_thread = threading.Thread
        starts = []

        class Signalling(real_thread):
            def start(self):
                starts.append(self)
                if len(starts) == 2:
                    signal.getsignal(signal.SIGINT)(signal.SIGINT, None)
                super().start()

        logs = self.tmp / "logs-signal-before-start"
        logs.mkdir()
        with mock.patch.object(safe_push.threading, "Thread", Signalling), \
                contextlib.redirect_stdout(io.StringIO()), \
                self.assertRaises(KeyboardInterrupt):
            safe_push.run_together(steps, self.root, safe_push.Report(), logs, 11, "", "FAIL",
                                   types.MappingProxyType({}), 2)
        self.assertEqual(len(starts), 2)
        self.assertFalse((marks / "after.start").exists())

    def test_a_signal_recorded_while_the_harness_waits_does_not_hang_it(self):
        # The only check's thread reads the signal recorded once the harness already waits
        # for an end, and begins no check: it must still give one, or the wait never ends.
        marks = self.marks()
        steps = [self.stand_in(marks, "only")]
        waiting, hung = threading.Event(), []
        real_thread = threading.Thread

        class Bounded(queue.SimpleQueue):
            def get(self, *args, **kwargs):
                waiting.set()
                try:
                    return super().get(timeout=HOLD)
                except queue.Empty:     # the signal's exception would come in its place
                    hung.append(True)
                    raise

        class Late(real_thread):
            def run(self):
                waiting.wait(HOLD)
                signal.getsignal(signal.SIGINT)(signal.SIGINT, None)
                super().run()

        logs = self.tmp / "logs-signal-while-waiting"
        logs.mkdir()
        with mock.patch.object(safe_push.queue, "SimpleQueue", Bounded), \
                mock.patch.object(safe_push.threading, "Thread", Late), \
                contextlib.redirect_stdout(io.StringIO()), \
                self.assertRaises(KeyboardInterrupt):
            safe_push.run_together(steps, self.root, safe_push.Report(), logs, 11, "", "FAIL",
                                   types.MappingProxyType({}), 2)
        self.assertEqual(hung, [], "the harness waited for an end no thread gives")
        self.assertFalse((marks / "only.start").exists())

    def test_signalled_raises_what_the_handlers_raise(self):
        # Python's own for SIGINT, and _terminate, as main() sets it, for SIGTERM and
        # SIGHUP.
        for signum, handler in ((signal.SIGINT, signal.default_int_handler),
                                (signal.SIGTERM, safe_push._terminate),
                                (signal.SIGHUP, safe_push._terminate)):
            with self.subTest(signal=signum.name):
                with self.assertRaises(KeyboardInterrupt) as ours:
                    safe_push.signalled(signum)
                with self.assertRaises(KeyboardInterrupt) as theirs:
                    handler(signum, None)
                self.assertEqual(ours.exception.args, theirs.exception.args)

    def test_an_end_lost_to_an_exception_is_not_waited_for(self):
        # An exception comes just after the queue has given up the quick check's end, which
        # is lost; the held check is released only then. The pass runs on a thread of the
        # test's own, so that a pass waiting for the lost end fails the test, not wedges it.
        marks = self.marks()
        release = marks / "release"
        steps = [self.stand_in(marks, "quick"), self.stand_in(marks, "held", hold="release")]
        lost, outcome = [], []

        class Losing(queue.SimpleQueue):
            def get(self, *args, **kw):
                item = super().get(*args, **kw)
                if not lost:
                    lost.append(item[0])
                    release.touch()
                    raise RuntimeError("after the end was taken")
                return item

        def pass_():
            try:
                self.run_steps(steps, 2, {"quick", "held"})
                outcome.append(("returned", None))
            except BaseException as e:
                outcome.append((e, self.marked(marks, "end")))
        with mock.patch.object(safe_push.queue, "SimpleQueue", Losing):
            runner = threading.Thread(target=pass_, daemon=True)
            runner.start()
            runner.join(HOLD)
        self.assertFalse(runner.is_alive(), f"the pass still waited {HOLD} s on")
        [(raised, ended)] = outcome
        self.assertIsInstance(raised, RuntimeError)
        self.assertEqual(str(raised), "after the end was taken")
        self.assertEqual(lost, ["quick"])
        self.assertEqual(ended, {"quick", "held"}, "the pass raised before the checks ended")

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
        at_return = sorted(p.name for p in marks.iterdir())
        self.assertEqual(len(starts), 2)
        # Each thread joined: one that let its check begin was waited for, and one that did
        # not begins none after this.
        for thread in starts:
            thread.join(HOLD)
            self.assertFalse(thread.is_alive())
        self.assertEqual(sorted(p.name for p in marks.iterdir()), at_return,
                         "a check ran on after the pass")
        self.assertEqual(self.marked(marks, "start"), self.marked(marks, "end"))


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
        self.assertIsInstance(checks.after, types.MappingProxyType)

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
        "python3 -I tests/test_concurrent_passes.py",
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
        # Each says why, in a comment line of its own whose word is its declaration's.
        for entry in entries:
            word = "Concurrent" if entry.concurrent else "Alone"
            self.assertIn(f"\n# {word} (#608)", "\n" + (REPO / entry.path).read_text(),
                          entry.path)


if __name__ == "__main__":
    unittest.main()
