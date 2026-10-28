"""Break the project on purpose, and check that it notices.

Each test makes one small change that must be caught, runs the check that should
catch it, and puts everything back. Run from the repo root after `lake build` and
`lake env lean Certificate/Facts.lean`, with `Certificate/axioms.lock` and the review
records current. CI's `negative` job runs it on every push to main, and on a pull request
of class R3 and above (scripts/risk.py); the cadence runs it on main
every six hours.

Each plant is a file of its own in scripts/negative/, named for the plant: `<name>.py`,
the name lower-case letters, digits and underscores, beginning with a letter. The file
holds, in this order: its description, as the module docstring (what it plants, which
check must refuse it, and what that check must say); its imports, among them
`import negative_tests as nt`, through which it reaches the helpers here; `BUILDS`, True
only for a plant that runs `lake build`; any constants and helpers of its own; and
`def plant() -> None:`, which plants the change, runs the check and puts everything back.
Helpers that more than one plant uses, or that tests/test_negative_tests.py tests, stay
here. Adding a plant is adding one file: there is no number to choose and no list to edit.

The plants run in a stable order: every plant whose `BUILDS` is False, by name, then every
plant whose `BUILDS` is True, by name. Each is named, with its file, before it runs, and
its elapsed time is printed after it, restoration included. The entry Git status is taken
first of all, before the regressions, the first of which loads the plants' folder in a
process of its own, and so before any plant's file is read: a file that a plant's file
writes as it loads shows in the closing comparison too. The closing list gives each
failure under the plant that added it, and the run's own (the restoration and final
checks) under a heading of their own; a full run that passes prints how many plants it
ran just before its closing tick.
`--plant NAME`, given once or more, runs just those plants, inside the same Git bracket
and with the same closing check of the unplanted tree, and a run it narrows closes by
saying how many of the plants it ran and that the others were not run; an unknown name
exits 2, naming the plants there are. `--counts-only` runs the file-only regressions and
count_markers alone, without the Git bracket.

`--workers N` runs the chosen plants in N workers at once, N cut to the number of plants
chosen; with one, the run is the one described here, with no worker and no worktree.
STOICHEIA_NEGATIVE_WORKERS gives N when `--workers` is absent, unset or empty meaning one,
so that the pre-flight and any other caller choose it without changing their commands. In
either, anything but a whole number from 1 exits 2, naming it. `--counts-only` takes no
workers: it refuses `--workers` and passes the variable over.

Each worker is a Git worktree of its own at the tree's commit, never a copy of a `.git`
file, made with `git worktree add --detach --no-checkout` outside the tree, under the
system's temporary directory (`stoicheia-negative-*`). TMPDIR chooses that directory, so
the run asks `git rev-parse --is-inside-work-tree` there, with a worker's environment: if
it is inside a Git work tree, where a fixture meant to have no repository above it would
find one, the run fails before any worker is made, naming it and TMPDIR. A worker is
given the tree's state, not just its commit: every file Git lists that is present,
tracked or untracked and not ignored, with its mode, a symbolic link as a link; the tree's
index, refreshed; and a clone of `.lake` (`cp -c -R` on macOS, whose copies share their
blocks until one side writes; `cp -a --reflink=auto` elsewhere), in which no file may be a
symbolic link or have a second name, since a plant that builds writes there. So in the
pre-flight's pass with origin/main's checks it lacks the files the commit adds while its
index lists them, as the tree does. Its `git status --porcelain` must be the tree's entry
status, or the run fails before any plant runs. It runs its own copy of this file in its
own tree, its share given by `--plant`, its output to a log of its own, with the run's
environment but for the variables that name a repository or a build, lest every worker
read one index or one build, and STOICHEIA_NEGATIVE_WORKERS (WITHHELD, and every `LAKE…`).

The shares are dealt longest first, by the seconds each plant took as
tests/negative_times.json records them (`--times-from-log LOG` writes it from a run's time
lines): each plant, heaviest first, ties going to a plant that builds and then to the
stable order, goes to the worker with the least so far, and each worker runs its share in
the stable order. A plant the record does not name weighs their median; with no record,
every plant weighs the same. The deal is printed on stderr, so stdout is unchanged, and
changes only the speed, never a verdict: a stale record only balances less well.

A worker is a run that `--plant` narrows, with all of its bracket: its entry status, the
guard, `nothing refused`, the closing check of its unplanted tree, the guard after it and
its final status. Only the file-only regressions are left to the run that made it, which
runs them once, before it makes any worker, where a one-worker run runs them, and keeps a
bracket of its own round the whole; its tree is never planted. Each worker writes one
report (`--worker-report FILE`, given only by a run with workers): each plant's output and
the failures it added, in order; its own failures; and its exit status. Once every worker
has ended, the run prints each chosen plant's output in the stable order, its failures
under its heading, so that its stdout is a one-worker run's apart from the times; then the
run's own failures, any one of which fails it: a worker's own, named by the worker and its
plants; a worker that crashed (one that exited other than 0 or 1, or whose report is
missing, unreadable, lacks a field the run reads or has one of the wrong type, lacks a
plant it was given or disagrees with its exit), with its log's tail, its plants that did
not report counting as not run, the other workers' reports read all the same; and a
worker's tree whose Git status, read once the worker has ended, is not the entry status,
which catches a worker that ended without its `finally` (os._exit, a signal). Interrupted,
the run interrupts each worker still running and waits for it (stop), and in its `finally`
it removes every worker's tree with `git worktree remove --force --force`, with SIGINT
ignored, each whatever became of those before it; one that Git cannot remove is deleted,
with a note that its record in the repository's worktree list stays until Git prunes it.
The run never runs `git worktree prune`, which would prune other trees' records too. As
with a plant's restoration (below), a forced kill defeats this: a run ended by SIGKILL, or
by a signal Python does not turn into an exception, leaves its workers running and their
trees registered.

The loader is checked too. It lists scripts/negative/ itself, never Git's index, so the
pre-flight's pass with origin/main's checks, which takes out the files a commit adds, runs
main's plants. It compiles each plant from the file's text, never from bytecode, so
nothing in a `__pycache__` runs in a plant's place; and run as a script, this file
registers itself as `negative_tests`, the name the plants import, rather than being
imported a second time through Python's cache. A missing or empty folder; a folder that
is, or passes through, a symbolic link; an entry that is not a regular file named
`[a-z][a-z0-9_]*.py` (a symbolic link or a directory among them), other than the directory
`__pycache__` and a regular file `.DS_Store`, the folder settings Finder writes and Git
ignores, which is named on stdout and passed over; a file that raises as it loads, a
SyntaxError or a SystemExit among them; and a file with no description, no `BUILDS` of
True or False, or no `plant` callable with no arguments: each is a fault naming the file
and the reason, and the run fails before anything is planted.

The plants share this module, and the modules they reach through it (check_fidelity,
check_kernel, generated_counts, heath and subprocess), so one plant's file could change
how every later plant is judged. Before any plant's file is read, their names are noted
with the object each holds. A file that adds, rebinds or deletes a name of this module,
or rebinds or deletes a name of one of the others (adding one there is no fault), as it
loads or while its plant() runs, is a fault naming the file, and the name is put back;
the names are looked at once more after the closing check of the unplanted tree, where a
change fails the run "after the closing check". The failures and refusals recorded before
a plant only grow, so a plant() that changes them fails by its name, and they are put
back as they were, with any it added after them kept. A plant() that raises SystemExit,
by sys.exit or a check's `main` run in process, fails the run by its name, and the run
goes on to the next plant. A run that ran fewer plants than it chose fails too: its loop
ends early only when the list of the plants chosen changes as it runs.

Each check that catches its plant records a refusal (expect_failure does, and `refused`
for a plant that judges a refusal itself, as stale_page does); a plant that records none
and adds no failure fails the run by its name, since nothing refused what it planted.
That guard catches a plant that runs no check, or returns before its first. It does not
catch a plant that calls `refused` with no check behind it, nor one that drops some of its
cases: a single refusal satisfies it.

These guards catch a mistake, not a file written to deceive: a plant's file runs in the
runner's process with its full power, so the security review reads each plant's file as
code of the runner. They do not see a shared object changed in place other than those two
lists (a helper's `__code__` replaced, a dict of a helper module changed); and a file that
ends the process itself (os._exit, a signal) is not caught in process, and leaves with the
status it chooses. Review reads each plant's file for them.

The copies of merge_conflict_markers and count_markers, and stale_page's list of
generated outputs, read Git's tracked files. One absent from the work tree is named on
stdout and passed over: as a note under the check inputs, since the pre-flight's pass with
origin/main's checks takes out the files a commit adds there while Git's index still lists
them (scripts/safe_push.py, step 4); as a failure anywhere else. The rule is
generated_counts.absent_tracked's, which check_fidelity.py and render.py follow for the
tracked Markdown they read.

These faults exercise the style and link checks, page freshness, an audit pin, a
complete book's figures and mishnah, leanchecker's loading of compiled files and its
kernel replay, part 4 of the restriction and the proof of every cited law, as well as
check_fidelity.py's, which most plants run. `check_kernel.py`'s own `--self-test`
withholds Postulate 5 from nanoda alone.

Every new plant restores its inputs in `finally`; the freshness plant also restores
all renderer outputs.
The seven that build, changed_audit_pin, cited_law_unproved, construction_in_clean_laws,
corrupt_olean, ill_typed_proof, planted_assumptions and retired_rule_used, attempt a
restoration build; if it fails or is interrupted, every file in `.lake/build` returns to
its saved contents and presence or absence before the plant, including dependent modules,
hashes and traces.
planted_assumptions always restores or removes `Planted.*` outputs in a nested `finally`.
Every plant reports its elapsed time, restoration included. An outer `finally` compares
Git status with the entry status, including on interruption, without replacing an
exception already in flight.
Temporary-directory regressions run before the plants, without Lean. Exits non-zero if a
fault goes unnoticed or a restoration check fails. Restoration needs writable files and
an opportunity for `finally` to finish; a forced process kill cannot provide it.
Standard library only; Python 3.11 or later, for the review records.
"""

import argparse
import inspect
import io
import json
import os
import re
import shutil
import signal
import stat
import statistics
import subprocess
import sys
import tempfile
import types
from collections.abc import Callable
from contextlib import contextmanager, redirect_stdout
from pathlib import Path
from time import perf_counter
from typing import NamedTuple

# The plants reach these, as the tests do, through this module: nt.check_fidelity and so on.
import check_fidelity
import check_kernel
import generated_counts
import heath

ROOT = heath.ROOT
PLANTED = ROOT / "Elements" / "Foundations" / "Tacit" / "Planted.lean"
failures: list[str] = []
refusals: list[str] = []
# What is generated, whole or in part (heath.py's "Generated regions", #578).
GENERATED = (*(name.rstrip("/") for name in heath.GENERATED_WHOLE), *heath.REGIONS)
# The plants' folder, from ROOT, and the name of a plant's file in it.
PLANTS = Path("scripts", "negative")
PLANT_FILE = re.compile(r"[a-z][a-z0-9_]*\.py")
# The modules the plants reach through this one, as nt.<module>: a plant may add a name to
# one, but not rebind or delete one (guard).
SHARED = ("check_fidelity", "check_kernel", "generated_counts", "heath", "subprocess")
# Names the guard passes over. Python's warnings machinery adds `__warningregistry__` to the
# module a warning is attributed to, ignored warnings too, so a warning raised through a
# helper here would read as a plant's change; it decides only which warnings repeat.
UNGUARDED = frozenset({"__warningregistry__"})
# The workers (the docstring): the variable that gives their number, the variables a worker
# is started without, besides every `LAKE…` (the audit of #607), the record of
# the plants' times, from ROOT, and a plant's line in it as a run prints it (run_plant).
WORKERS = "STOICHEIA_NEGATIVE_WORKERS"
WITHHELD = frozenset({"GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
                      "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES",
                      "GIT_NAMESPACE", "GIT_PREFIX", "LEAN_PATH", WORKERS})
TIMES = Path("tests", "negative_times.json")
TIME_LINE = re.compile(r"  ([a-z][a-z0-9_]*): (\d+\.\d+)s \(including restoration\)")
TIMES_ABOUT = ("Seconds each plant of scripts/negative_tests.py took, restoration included, "
               "to a tenth of a second, written by `python3 scripts/negative_tests.py "
               "--times-from-log` from the time lines of {count} plants in the log {log}. "
               "`--workers N` deals the plants out by these times, longest first; a plant "
               "missing here weighs their median, and with no file every plant weighs the "
               "same. A stale time only balances the workers less well: it changes no "
               "verdict.")


# `True.intro` given as a proof of `False`, added past the kernel as the read-through found
# possible (docs/reports/read-through-01.md). The source scan refuses both commands, so they
# are compiled from a copy of I.1 it never reads. `Lean.Elab.Command` defines the monad
# `run_cmd` runs in, so it is the least of Lean's library the plant can import, and it
# brings `addDecl` with it. Here, not in scripts/negative/ill_typed_proof.py, because
# tests/test_negative_tests.py reads them.
ILL_TYPED = "Elements.BookI.planted_ill_typed"
ILL_TYPED_LEAN = ("\nopen Lean in\nset_option debug.skipKernelTC true in\n"
                  "run_cmd Elab.Command.liftCoreM <| addDecl <| .thmDecl {\n"
                  f"  name := `{ILL_TYPED}, levelParams := [],\n"
                  "  type := mkConst ``False, value := mkConst ``True.intro }\n")


# A proposition imported by Book Zero in each spelling Lean 4.35 accepts; in the five
# forms that Lean's header allows after `module`, which Lean refuses while the edition's
# files are not modules, so that the rule is ready for when they are; and in forms Lean
# may read as one (#200). Each comes with what must be caught besides its file and line.
# Here, not in scripts/negative/book_zero_imports.py, because tests/test_negative_tests.py
# reads them.
BOOK_ZERO_SPELLINGS = (
    ("two spaces", "import  Elements.BookI.Prop01\n"),
    ("a line break", "import\n  Elements.BookI.Prop01\n"),
    ("a remark between", "import /- a remark -/ Elements.BookI.Prop01\n"),
    ("a line comment between", "import -- a remark\n  Elements.BookI.Prop01\n"),
    ("a nested remark between", "import /- a /- nested -/ remark -/ Elements.BookI.Prop01\n"),
    ("nothing before «…»", "import«Elements».BookI.Prop01\n"),
    ("nothing around a remark", "import/- a remark -/Elements.BookI.Prop01\n"),
    ("«Elements»", "import «Elements».BookI.Prop01\n"),
    ("«BookI»", "import Elements.«BookI».Prop01\n"),
    ("a second import on the line",
     "import Elements.Figure.Lines import Elements.BookI.Prop01\n"),
    ("public import", "module\npublic import Elements.BookI.Prop01\n"),
    ("meta import", "module\nmeta import Elements.BookI.Prop01\n"),
    ("public meta import", "module\npublic meta import Elements.BookI.Prop01\n"),
    ("import all", "module\nimport all Elements.BookI.Prop01\n"),
    ("meta import all", "module\nmeta import all Elements.BookI.Prop01\n"),
    ("a path in «…»", "import «Elements/BookI».Prop01\n", "cannot read this import for certain"),
    ("another case", "import elements.booki.Prop01\n"),
    ("the Kelvin sign", "import Elements.BooKI.Prop01\n"),
    ("through Elements.Companions", "import Elements.Companions\n",
     "`Elements.Companions` brings one in: Elements/Companions.lean imports `Elements.Book"),
)
# A file of Book Zero with the same import only in text, beside a Book Zero import.
BOOK_ZERO_TEXT = ("Elements/Figure/PlantedImportText.lean",
                  "import Elements.Figure.Lines\n"
                  "-- import Elements.BookI.Prop01\n"
                  "/- import Elements.BookI.Prop01 -/\n"
                  'def plantedImportText : String := "import Elements.BookI.Prop01"\n'
                  "def «import Elements.BookI.Prop01» : Nat := 1\n")


# The restriction's names and guards for figure_guard_over_all_points, and its helpers
# plant_figure_guard and declaration_lines. Here, not in
# scripts/negative/figure_guard_over_all_points.py, because tests/test_negative_tests.py
# reads them.
RESTRICTION = "Elements/Foundations/Superposition/Restriction.lean"
RESTRICT = "theorem Rule.Figure.restrict"
IFF_FIGURE = "theorem Rule.iff_figure"
RESTRICT_NAME = "Elements.Superposition.Rule.Figure.restrict"
# The two guards `figure_guard_over_all_points` adds to `Rule.Figure`. The control speaks of the figure's own points and
# straight line, as the embedding keeps them; the plant ranges over every point: the
# straight line through D and G holds no other point.
OVER_THE_FIGURE = ("(I.Between (v.pt d) (v.pt a) (v.pt g) → "
                   "I.SameSide (v.pt b) (v.pt h) (v.line l))")
OVER_ALL_POINTS = "(∀ X : I.Point, I.OnLine X (v.line l) → X = v.pt d ∨ X = v.pt g)"
# In both runs the proof of `Rule.Figure.restrict` introduces the new guard as `hX` and
# passes it from J to I through the embedding.
THROUGH_THE_EMBEDDING = ("(by simpa [Interpretation.Embedding.val, e.onLine_iff, e.between_iff, "
                         "e.sameSide_iff] using hX)")


def plant_figure_guard(text: str, guard: str) -> str:
    """The restriction's text with `guard` added to `Rule.Figure` after the guards, the proof
    of `Rule.Figure.restrict` taking it as `hX` and passing it through the embedding,
    `Rule.iff_figure` and its docstring left out, and `#print axioms` of
    `Rule.Figure.restrict` appended, to show whether it was proved."""
    iff = declaration_lines(text, IFF_FIGURE)
    lines = text.split("\n")
    # Line numbers from 1: the docstring opens at `doc`, and a blank line follows the proof.
    doc = max(n for n in range(1, iff.start) if lines[n - 1].startswith("/--"))
    assert lines[iff.stop - 1] == "", f"{RESTRICTION}: expected a blank line after {IFF_FIGURE}"
    text = "\n".join(lines[:doc - 1] + lines[iff.stop:])
    edits = (
        ("¬ I.OnLine (v.pt h) (v.line l) → (∀ ℓ ∈ Γ, ℓ.Holds v) → φ.Holds v",
         f"¬ I.OnLine (v.pt h) (v.line l) →\n      {guard} →\n"
         "      (∀ ℓ ∈ Γ, ℓ.Holds v) → φ.Holds v"),
        ("intro n m Γ a b c d g h l φ dφ v hT hd hg hdg hh hΓ",
         "intro n m Γ a b c d g h l φ dφ v hT hd hg hdg hh hX hΓ"),
        ("(fun hh' => hh (e.onLine_iff.1 hh'))\n    fun ℓ hℓ",
         f"(fun hh' => hh (e.onLine_iff.1 hh'))\n    {THROUGH_THE_EMBEDDING}\n    fun ℓ hℓ"),
    )
    for old, new in edits:
        assert text.count(old) == 1, f"{RESTRICTION}: expected one {old!r}; update this test"
        text = text.replace(old, new)
    return text + f"\n#print axioms {RESTRICT_NAME}\n"


def declaration_lines(text: str, head: str) -> range:
    """The lines of the declaration that starts with `head`, up to the next blank line."""
    assert text.count(head) == 1, f"{RESTRICTION}: expected one {head!r}; update this test"
    start = text.index(head)
    end = text.find("\n\n", start)
    first = text[:start].count("\n") + 1
    return range(first, text[:end if end >= 0 else len(text)].count("\n") + 2)


# The files cited_law_unproved plants in and expects the refusal from. Here, not in
# scripts/negative/cited_law_unproved.py, because tests/test_negative_tests.py reads them.
SYNTAX = "Elements/Foundations/Superposition/Syntax.lean"
HOLDS_ALL = "Elements/BookI/Prop08.lean"


def run(*cmd: str) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)


def tracked_names() -> tuple[subprocess.CompletedProcess, list[str]]:
    """List tracked names without text mode changing control characters in them."""
    result = subprocess.run(("git", "ls-files", "-z"), cwd=ROOT, capture_output=True)
    names = [name.decode() for name in result.stdout.split(b"\0") if name]
    return result, names


def fidelity(*args: str) -> subprocess.CompletedProcess:
    return run(sys.executable, "scripts/check_fidelity.py", *args)


def replace_once(rel: str, old: str, new: str) -> str:
    """Change `old` to `new` in the file, and return the text to put back."""
    path = ROOT / rel
    text = path.read_text()
    assert text.count(old) == 1, f"{rel}: expected one {old!r}"
    path.write_text(text.replace(old, new))
    return text


def refused(message: str) -> None:
    """Record that a check refused what the running plant planted, and say so."""
    refusals.append(message)
    print(f"✓ {message}")


def expect_failure(name: str, result: subprocess.CompletedProcess, *wanted: str,
                   unwanted: tuple = ()) -> None:
    """The check must fail, saying each of `wanted` and none of `unwanted`."""
    out = result.stdout + result.stderr
    missing = [w for w in wanted if w not in out]
    present = [u for u in unwanted if u in out]
    if result.returncode == 0 or missing or present:
        detail = []
        if missing:
            detail.append(f"missing {', '.join(repr(m) for m in missing)}")
        if present:
            detail.append(f"wrongly says {', '.join(repr(p) for p in present)}")
        failures.append(f"{name}: not caught" + (f" ({'; '.join(detail)})" if detail else ""))
        print(out[-3000:])
    else:
        refused(f"{name}: caught")


def expect_success(name: str, result: subprocess.CompletedProcess) -> bool:
    if result.returncode != 0:
        message = f"{name}: exit {result.returncode}"
        failures.append(message)
        print(f"✗ {message}")
        output = (result.stdout + result.stderr)[-3000:]
        if output:
            print(output, end="" if output.endswith("\n") else "\n")
        return False
    return True


class BuildOutputs:
    """Save build files without a suffix list, including outputs of dependents.

    A pattern can select just a temporary module for cleanup after a successful
    build too. Rescanning on restore removes files absent when the snapshot was made.
    """

    def __init__(self, pattern: str = "**/*"):
        self.root = ROOT / ".lake/build"
        self.pattern = pattern
        self.saved = {p: p.read_bytes() for p in self.files()}

    def files(self) -> set[Path]:
        return {p for p in self.root.glob(self.pattern) if p.is_file()}

    def restore(self) -> None:
        for path in self.files() - self.saved.keys():
            path.unlink()
        for path, data in self.saved.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)


def rebuild_restored(name: str, outputs: BuildOutputs, *targets: str,
                     force: Path | None = None) -> bool:
    """Keep the restoration build, with saved files as fallback on failure or interrupt."""
    rebuilt = False
    try:
        if force is not None:
            # Lake removes companion outputs too when rebuilding this module.
            force.unlink()
        rebuilt = expect_success(name, run("lake", "build", *targets))
        return rebuilt
    finally:
        if not rebuilt:
            outputs.restore()


def absent_tracked(rels: list[str | Path]) -> list[str | Path]:
    """The tracked paths of `rels` absent from the work tree, each named on stdout.

    The rule is generated_counts.absent_tracked's, which the count checks follow too: one
    under the check inputs is noted, and the caller goes on with what is present, since the
    pre-flight's pass with origin/main's checks (scripts/safe_push.py, step 4) takes out
    the files a commit adds there while Git's index still lists them. One absent outside
    the check inputs is a failure too, so none goes unseen. Any other error from the work
    tree, as for a path in a directory of mode 000, is raised.
    """
    missing, faults = generated_counts.absent_tracked(ROOT, rels)
    for message in faults:
        if message not in failures:
            failures.append(message)
        print(f"✗ {message}")
    return missing


def copy_marker_files(root: Path, names: list[str]) -> None:
    """Copy the tracked files for merge_conflict_markers, skipping symlinks without reading
    targets, and naming those absent from the work tree (absent_tracked)."""
    absent_tracked([name for name in names if name])
    for name in names:
        source = ROOT / name
        if name and not source.is_symlink() and source.is_file():
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)


def generated_files() -> set[Path]:
    paths = set()
    for rel in GENERATED:
        path = ROOT / rel
        if path.is_dir():
            paths.update(p for p in path.rglob("*") if p.is_file())
        elif path.exists():
            paths.add(path)
    tracked = generated_counts.tracked_markdown(ROOT)
    missing = set(absent_tracked(tracked))
    for rel in tracked:
        path = ROOT / rel
        if (rel not in missing and not generated_counts.whole_output(rel)
                and not generated_counts.historical(rel)
                and generated_counts.START.search(path.read_text())):
            paths.add(path)
    return paths


def entry(facts: dict, ref: str) -> dict:
    return next(p for p in facts["propositions"] if p["ref"] == ref)


def with_facts(change) -> subprocess.CompletedProcess:
    """Run check_fidelity.py on a copy of facts.json changed by `change`; the real
    facts.json is not touched."""
    facts = json.loads((ROOT / "facts.json").read_text())
    change(facts)
    with tempfile.TemporaryDirectory() as tmp:
        copy = Path(tmp) / "facts.json"
        copy.write_text(json.dumps(facts, ensure_ascii=False))
        return fidelity("--facts", str(copy))


@contextmanager
def count_source_copy():
    """Copy tracked sources plus current Python tools and checks/ under /tmp, with no
    build or .git.

    Git reads the original index through GIT_DIR; GIT_WORK_TREE points only at the
    copy. No Git command writes. Include new Python sources, and the files of the registry
    of checks, which render.py reads, before they are committed.
    A tracked file absent from the work tree is named (absent_tracked), not copied.
    """
    tracked, names = tracked_names()
    tracked.check_returncode()
    git_dir = run("git", "rev-parse", "--absolute-git-dir")
    git_dir.check_returncode()
    paths = {Path(p) for p in names}
    paths.difference_update(absent_tracked(sorted(paths)))
    paths.update(p.relative_to(ROOT) for p in (ROOT / "scripts").glob("*.py"))
    paths.update(p.relative_to(ROOT) for p in (ROOT / "checks").glob("*") if p.is_file())
    with tempfile.TemporaryDirectory(prefix="stoicheia-counts-", dir="/tmp") as tmp:
        copy = Path(tmp)
        for rel in paths:
            target = copy / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / rel, target)
        yield copy, {**os.environ, "GIT_DIR": git_dir.stdout.strip(),
                     "GIT_WORK_TREE": str(copy)}


# The source scan on a tree of its own, and the scratch copy of I.1 the source-scan plants
# share: here, not in a plant's file, because several plants use them and
# tests/test_negative_tests.py tests rules_in.
def rules_in(root: Path) -> subprocess.CompletedProcess:
    """check_fidelity's source scan, run on the tree at `root` instead of the edition's."""
    saved_root, saved_errors = check_fidelity.ROOT, list(check_fidelity.errors)
    check_fidelity.ROOT = root
    check_fidelity.errors.clear()
    try:
        check_fidelity.check_rules()
        found = list(check_fidelity.errors)
    finally:
        check_fidelity.ROOT = saved_root
        check_fidelity.errors[:] = saved_errors
    return subprocess.CompletedProcess([], 1 if found else 0, "\n".join(found) + "\n", "")


def scratch_plants(name: str, plants: tuple, kept: tuple = (), prohibited: tuple = ()) -> None:
    """Plant each of `plants`, (word, Lean), and each line of `kept` in a scratch copy of
    I.1's file, in a temporary tree whose only file it is, and run check_fidelity.py's
    source scan on that tree (`rules_in`): the edition's own files are never touched. The
    copy must pass unplanted. Planted, each of `plants` must be refused on the line of its
    command, `set_option` or `#guard_msgs`, by `word`, or, for a word `literal …`, on the
    line of that string literal, by the approximate token-declaration-span diagnostic, or,
    for a plant (finding, Lean, text), by that finding on the line where the text first
    stands; and no line of `kept` refused, nor any text in `prohibited` reported."""
    rel = "Elements/BookI/Prop01.lean"
    marker = "\nend Elements.BookI\n"
    source = (ROOT / rel).read_text()
    assert source.count(marker) == 1, f"{rel}: expected one {marker!r}; update this test"
    planted = source.replace(marker, "\n/-! Planted by scripts/negative_tests.py. -/\n"
                             + "\n".join([plant[1] for plant in plants] + list(kept)) + "\n"
                             + marker)

    def line(lean: str, anchor: str) -> int:
        assert planted.count(lean) == 1, f"{lean!r}: planted more than once; update this test"
        return planted[:planted.index(lean) + lean.index(anchor)].count("\n") + 1

    command = re.compile(r"#?\w+")
    wanted = [f"{rel}:{line(lean, at[0])}: {word}" if at else
              (f"{rel}:{line(lean, word)}: declares an axiom outside "
               "Elements/Foundations/") if word == "axiom" else
              (f"{rel}:{line(lean, word[8:])}: finds a string literal whose trimmed text is "
               f"`{word[8:]}` in an approximate token-declaration span")
              if word.startswith("literal ") else
              f"{rel}:{line(lean, command.match(word)[0])}: uses `{word}`"
              for word, lean, *at in plants]
    unwanted = prohibited + tuple(f"{rel}:{n}:" for lean in kept
                                   for n in range(line(lean, lean),
                                                  line(lean, lean) + lean.count("\n") + 1))
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        path = root / rel
        path.parent.mkdir(parents=True)
        path.write_text(source)
        if not expect_success(f"{name}: the unplanted scratch copy of {rel}", rules_in(root)):
            return
        path.write_text(planted)
        expect_failure(name, rules_in(root), *wanted, unwanted=unwanted)


# An audit pin: the message `#print axioms` gives, as `#guard_msgs` holds it. The message
# stops at the first end of a docstring, so a pin never runs across another `#guard_msgs`
# (a statement pin's `#check`) to the next `#print axioms`. Here, with rewritten_pins, not
# in scripts/negative/construction_in_clean_laws.py, because tests/test_negative_tests.py
# reads them.
AUDIT_PIN = re.compile(r"/--\n(info: (?:(?!\n-/\n).)*?)\n-/\n#guard_msgs in\n"
                       r"#print axioms (\S+)\n", re.S)


def rewritten_pins(rel: str) -> str | None:
    """The audit file `rel` with every `#print axioms` pin rewritten to what Lean prints now,
    as an author would after changing a proof: Lean prints the pinned names in a probe file
    with the audit file's own imports, so each must be declared in what it imports, as
    every name Audit/Superposition.lean pins is. Each message begins with its name, quoted,
    and runs to the next. Every `#print axioms` command of the file must be read as a pin.
    None, with the failure recorded, if they cannot all be read or printed."""
    text = (ROOT / rel).read_text()
    imports = [line for line in text.splitlines() if line.startswith("import ")]
    names = [m[2] for m in AUDIT_PIN.finditer(text)]
    commands = len(re.findall(r"^#print axioms ", text, re.M))
    if len(names) != commands:
        failures.append(f"printing the pins of {rel}: {commands} `#print axioms` commands, "
                        f"but {len(names)} pins read; update this test")
        return None
    with tempfile.TemporaryDirectory(prefix="stoicheia-pins-") as tmp:
        probe = Path(tmp) / "Pins.lean"
        probe.write_text("\n".join(imports + [f"#print axioms {n}" for n in names]) + "\n")
        result = run("lake", "env", "lean", str(probe))
    if not expect_success(f"printing the pins of {rel}", result):
        return None
    out = re.sub(r"^\S*Pins\.lean:\d+:\d+: info: ", "", result.stdout, flags=re.M)
    starts, at = [], 0
    for name in names:
        found = re.compile(rf"^'{re.escape(name)}' ", re.M).search(out, at)
        if found is None:
            break
        starts.append(found.start())
        at = found.end()
    if not names or len(starts) != len(names) or out[:starts[0]].strip():
        failures.append(f"printing the pins of {rel}: expected one message for each of "
                        f"{len(names)} pins, in order, and nothing else")
        print(result.stdout[-3000:])
        return None
    fresh = iter("info: " + out[a:b].rstrip() for a, b in zip(starts, starts[1:] + [len(out)]))
    return AUDIT_PIN.sub(lambda m: m[0].replace(m[1], next(fresh), 1), text)


class Plant(NamedTuple):
    """A plant as its file gives it: the name is the file's."""
    name: str
    path: Path
    description: str
    builds: bool
    plant: Callable[[], None]


def shown(path: Path) -> str:
    """A path as a run names it: from ROOT when it lies beneath."""
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return str(path)


def guard() -> Callable[[], list[str]]:
    """Note the names of this module and of SHARED, each with the object it holds, and
    return a function that gives each change since as a reason (`rebinds
    check_fidelity.check_lock`) and puts it back: a name of this module added, rebound or
    deleted, or one of SHARED's rebound or deleted. A plant's file that changed one could
    change how every later plant is judged: count a check that passes as a refusal, say,
    or run no plant at all. The callers make the function before any plant's file is read
    and hold it themselves, and it reads only what it noted, so no plant can rebind it."""
    unguarded = UNGUARDED
    noted = [("negative_tests", globals(), True)]
    noted += [(name, vars(globals()[name]), False) for name in SHARED]
    saved = [(label, names, dict(names), own) for label, names, own in noted]

    def changes() -> list[str]:
        reasons = []
        for label, names, before, own in saved:
            for name in sorted((before.keys() | names.keys()) - unguarded):
                if name not in names:
                    reasons.append(f"deletes {label}.{name}")
                    names[name] = before[name]
                elif name not in before:
                    if own:
                        reasons.append(f"adds {label}.{name}")
                        del names[name]
                elif names[name] is not before[name]:
                    reasons.append(f"rebinds {label}.{name}")
                    names[name] = before[name]
        return reasons
    return changes


def shared_change(reason: str, when: str) -> str:
    """How a fault names a change to a shared name (guard)."""
    return (f"{reason} {when} (put back); a plant leaves the names it shares with the "
            "runner as it finds them")


def load_plant(path: Path) -> Plant | list[str]:
    """The plant in `path`, compiled from the file's text, never from bytecode, and run as
    a module of its own, `negative_plant_<name>`; or what is wrong with it."""
    module_name = f"negative_plant_{path.stem}"
    module = types.ModuleType(module_name)
    module.__file__ = str(path)
    sys.modules[module_name] = module
    try:
        code = compile(path.read_text(encoding="utf-8"), str(path), "exec", dont_inherit=True)
        exec(code, vars(module))
    except (Exception, SystemExit) as error:
        sys.modules.pop(module_name, None)
        return [f"does not load: {type(error).__name__}: {error}"]
    reasons = []
    doc = module.__doc__
    description = inspect.cleandoc(doc).strip() if isinstance(doc, str) else ""
    if not description:
        reasons.append("no description: its module docstring is missing or empty")
    if not hasattr(module, "BUILDS"):
        reasons.append("no BUILDS: True if the plant runs `lake build`, else False")
    elif not isinstance(module.BUILDS, bool):
        reasons.append(f"BUILDS is {module.BUILDS!r}, not True or False")
    function = getattr(module, "plant", None)
    if function is None:
        reasons.append("no plant(): the function that plants the change and checks it")
    elif not callable(function):
        reasons.append(f"plant is {type(function).__name__}, not a function")
    else:
        try:
            inspect.signature(function).bind()
        except TypeError:
            reasons.append("plant() must take no arguments")
        except ValueError:
            reasons.append("plant()'s signature cannot be read")
    if reasons:
        return reasons
    return Plant(path.stem, path, description, module.BUILDS, function)


def load_plants(folder: Path | None = None) -> tuple[list[Plant], list[str]]:
    """The plants in `folder` (ROOT / PLANTS when None), in the stable order: those whose
    BUILDS is False, by name, then those whose BUILDS is True, by name. With them, the
    faults, each naming its path: a folder that is, or passes through, a symbolic link
    (below ROOT, resolved, when the folder lies beneath it); an entry other than the
    directory __pycache__ and a regular file .DS_Store, which is named on stdout, that is
    not a regular file with a plant's name directly in the folder; a file that does not
    load, lacks a part, or changes a shared name as it loads (guard); and a missing or
    empty folder. The folder is listed, never Git, so a file the pre-flight takes out is
    not looked for."""
    folder = ROOT / PLANTS if folder is None else folder
    try:
        expected = ROOT.resolve() / folder.relative_to(ROOT)
    except ValueError:
        expected = folder.absolute()
    real = folder.resolve()
    if real != expected:
        return [], [f"{shown(folder)}: the plants' folder is, or passes through, a symbolic "
                    f"link (it resolves to {real}); plants are read only from a real folder"]
    try:
        entries = sorted(folder.iterdir())
    except OSError as error:
        return [], [f"{shown(folder)}: the plants' folder cannot be listed "
                    f"({type(error).__name__}: {error.strerror or error})"]
    changes = guard()
    plants, faults = [], []
    for path in entries:
        if path.name == "__pycache__" and path.is_dir() and not path.is_symlink():
            continue
        if path.name == ".DS_Store" and path.is_file() and not path.is_symlink():
            print(f"note: {shown(path)} passed over: Finder's settings for the folder, "
                  "which Git ignores, not a plant")
            continue
        if path.is_symlink():
            faults.append(f"{shown(path)}: a symbolic link, which is not read; a plant is "
                          "a regular file")
        elif path.is_dir():
            faults.append(f"{shown(path)}: a directory, not a plant's file")
        elif not path.is_file():
            faults.append(f"{shown(path)}: not a regular file")
        elif not PLANT_FILE.fullmatch(path.name):
            faults.append(f"{shown(path)}: not a plant's file name, which is "
                          "[a-z][a-z0-9_]*.py")
        elif path.resolve().parent != real:
            faults.append(f"{shown(path)}: resolves to {path.resolve()}, which is not "
                          "directly in the plants' folder")
        else:
            loaded = load_plant(path)
            reasons = [shared_change(reason, "as it loads") for reason in changes()]
            if isinstance(loaded, Plant) and not reasons:
                plants.append(loaded)
            else:
                reasons = ([] if isinstance(loaded, Plant) else loaded) + reasons
                faults += [f"{shown(path)}: {reason}" for reason in reasons]
    if not plants and not faults:
        faults.append(f"{shown(folder)}: no plants")
    return sorted(plants, key=lambda p: (p.builds, p.name)), faults


def run_plant(plant: Plant, sources: dict[int, str],
              changes: Callable[[], list[str]]) -> None:
    """Run one plant, named before and timed after. Fail it, by its name, if its plant()
    raises SystemExit; if it changes a shared name (`changes`, from guard, which puts the
    name back) or the failures or refusals recorded before it, which only grow (put back
    as they were, with any after them kept), both seen first, in `finally`, so that what
    follows reads the runner's own; or if it neither records a refusal nor adds a failure.
    `sources` gains the plant's heading for each failure it added, by its index in
    `failures`."""
    path = shown(plant.path)
    print(f"{plant.name} ({path})")
    failed, caught = len(failures), len(refusals)
    recorded = failures[:], refusals[:]
    started = perf_counter()
    exited, code = False, None
    try:
        plant.plant()
    except SystemExit as error:
        exited, code = True, error.code
    finally:
        changed = changes()
        rewritten = False
        for entries, earlier in zip((failures, refusals), recorded):
            if entries[:len(earlier)] != earlier:
                entries[:] = earlier + entries[len(earlier):]
                rewritten = True
        print(f"  {plant.name}: {perf_counter() - started:.2f}s (including restoration)")
        for reason in changed:
            message = f"{plant.name}: {path} {shared_change(reason, 'as it runs')}"
            failures.append(message)
            print(f"✗ {message}")
        if rewritten:
            message = f"{plant.name}: changed the failures or refusals recorded before it"
            failures.append(message)
            print(f"✗ {message}")
    if exited:
        message = f"{plant.name}: plant() exited ({code!r}) instead of returning"
        failures.append(message)
        print(f"✗ {message}")
    if len(failures) == failed and len(refusals) == caught:
        message = f"{plant.name}: nothing refused what {path} planted"
        failures.append(message)
        print(f"✗ {message}")
    for i in range(failed, len(failures)):
        sources[i] = f"{plant.name} ({path}):"


def choose(parser: argparse.ArgumentParser, args: argparse.Namespace,
           sources: dict[int, str]) -> tuple[list[Plant], int] | None:
    """The plants the run asks for, loaded, and how many plants there are; or None when
    the folder has a fault, each recorded under the loader's heading. An unknown name for
    --plant exits 2."""
    plants, faults = load_plants()
    if faults:
        for fault in faults:
            sources[len(failures)] = f"loading the plants ({PLANTS}/):"
            failures.append(fault)
            print(f"✗ {fault}")
        return None
    names = [p.name for p in plants]
    wanted = ["count_markers"] if args.counts_only else args.plant or names
    unknown = [name for name in dict.fromkeys(wanted) if name not in names]
    if unknown:
        parser.error(f"no plant {', '.join(map(repr, unknown))} in {PLANTS}/; "
                     f"the plants are {', '.join(names)}")
    return [p for p in plants if p.name in wanted], len(plants)


def close(sources: dict[int, str], ran: int = 0, total: int = 0) -> int:
    """The closing list of failures, each under the plant that added it, and the exit
    status. A run that passes gives how many of the `total` plants it `ran`: just before
    its closing tick in a full run, and in it when --plant narrowed the run."""
    if not failures:
        if ran < total:
            print(f"✓ every change planted by {ran} of the {total} plants was caught; "
                  "the others were not run (--plant)")
        else:
            print(f"{ran} of {total} plant{'' if total == 1 else 's'} run")
            print("✓ every planted change was caught")
        return 0
    print(f"{len(failures)} negative-test failure(s):")
    groups: dict[str, list[str]] = {}
    for i, f in enumerate(failures):
        groups.setdefault(sources.get(i, "outside any plant:"), []).append(f)
    for heading, messages in groups.items():
        print(heading)
        for f in messages:
            print("  ✗ " + f)
    return 1


REGRESSIONS = (("restoration regressions", "tests/test_negative_tests.py"),
               ("count regressions", "tests/test_generated_counts.py"),
               ("decision entry regressions", "tests/test_decision_entries.py"),
               ("risk class regressions", "tests/test_risk.py"),
               ("lock regressions", "tests/test_axiom_lock.py"))


def regressions() -> bool:
    """Run the file-only regressions, in order, each without Lean; False at the first that
    fails, which expect_success records."""
    for name, test in REGRESSIONS:
        if not expect_success(name, run(sys.executable, "-I", test)):
            return False
        print(f"✓ {name} passed (without Lean)")
    return True


def worker_count(parser: argparse.ArgumentParser, args: argparse.Namespace) -> int:
    """The workers the run asks for: --workers, or else STOICHEIA_NEGATIVE_WORKERS, unset or
    empty for one. A worker, --times-from-log and --counts-only read no variable, so that one
    the lane sets for every run leaves them as they are, and take no --workers. Anything but
    a whole number from 1 exits 2, naming it."""
    if args.workers is not None:
        text, named = args.workers, "--workers"
        if args.worker_report is not None or args.times_from_log is not None:
            parser.error("--workers is for a run of the plants, not with --worker-report or "
                         "--times-from-log")
        if args.counts_only:
            parser.error("--workers is not for --counts-only, which takes no workers")
    elif (args.worker_report is None and args.times_from_log is None and not args.counts_only
          and os.environ.get(WORKERS)):
        text, named = os.environ[WORKERS], WORKERS
    else:
        return 1
    if not (text.isascii() and text.isdigit() and int(text) >= 1):
        parser.error(f"{named} must be a whole number from 1, not {text!r}")
    return int(text)


def recorded_times() -> dict[str, float]:
    """The seconds by plant that tests/negative_times.json records: none without the file,
    as in the pre-flight's pass with a main that has none, or with one that cannot be read,
    which is named on stderr, since the record only balances the workers."""
    try:
        data = json.loads((ROOT / TIMES).read_text(encoding="utf-8"))
        return {str(name): float(seconds) for name, seconds in data["seconds"].items()}
    except FileNotFoundError:
        return {}
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        print(f"note: {TIMES} cannot be read ({type(error).__name__}: {error}); every plant "
              "weighs the same", file=sys.stderr)
        return {}


def deal(plants: list[Plant], count: int,
         seconds: dict[str, float]) -> tuple[list[list[Plant]], list[float]]:
    """`plants` dealt to `count` workers, longest first: each plant, heaviest first, ties
    going to a plant that builds and then to the order of `plants`, goes to the worker with
    the least weight so far, then the fewest plants, then the lowest number. A plant weighs
    its `seconds`, or their median when it has none; with none at all, every plant weighs
    the same. Each share keeps the order of `plants`, and every plant is in exactly one;
    with each share, its weight."""
    median = statistics.median(seconds.values()) if seconds else 1.0
    weight = [seconds.get(p.name, median) for p in plants]
    shares: list[list[int]] = [[] for _ in range(count)]
    loads = [0.0] * count
    for i in sorted(range(len(plants)), key=lambda i: (-weight[i], not plants[i].builds, i)):
        k = min(range(count), key=lambda k: (loads[k], len(shares[k]), k))
        shares[k].append(i)
        loads[k] += weight[i]
    return [[plants[i] for i in sorted(share)] for share in shares], loads


def write_times(log: Path) -> int:
    """`--times-from-log LOG`: tests/negative_times.json, from the time lines of a run's
    output in LOG, each to a tenth of a second, sorted by name, the log named by its folder
    and file. 1, with nothing written, when LOG cannot be read, times a plant twice or
    times none."""
    try:
        text = log.read_text(encoding="utf-8", errors="replace")
    except OSError as error:
        print(f"No times written to {TIMES}: {error}", file=sys.stderr)
        return 1
    seconds: dict[str, float] = {}
    twice = []
    for line in text.splitlines():
        found = TIME_LINE.fullmatch(line)
        if found:
            if found[1] in seconds:
                twice.append(found[1])
            seconds[found[1]] = round(float(found[2]), 1)
    if twice or not seconds:
        print(f"No times written to {TIMES}: {log} "
              + (f"times {', '.join(twice)} more than once, so it is not one run's output"
                 if twice else "holds no plant's time line"), file=sys.stderr)
        return 1
    where = log.resolve()
    data = {"about": TIMES_ABOUT.format(count=len(seconds),
                                        log=f"{where.parent.name}/{where.name}"),
            "seconds": dict(sorted(seconds.items()))}
    (ROOT / TIMES).write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n",
                              encoding="utf-8")
    print(f"Wrote {TIMES}: {len(seconds)} plants.")
    return 0


class Tee(io.TextIOBase):
    """Text written to `stream`, and a copy of it kept."""

    def __init__(self, stream):
        self.stream, self.copy = stream, io.StringIO()

    def write(self, text: str) -> int:
        self.copy.write(text)
        return self.stream.write(text)

    def flush(self) -> None:
        self.stream.flush()


def run_reported(plant: Plant, sources: dict[int, str], changes: Callable[[], list[str]],
                 report: dict) -> None:
    """run_plant, in a worker: what the plant prints is printed and kept, and `report`
    gains it with the failures the plant added, noting their places in `failures`."""
    start = len(failures)
    tee = Tee(sys.stdout)
    with redirect_stdout(tee):
        run_plant(plant, sources, changes)
    report["plants"].append({"name": plant.name, "output": tee.copy.getvalue(),
                             "failures": failures[start:]})
    report["taken"].update(range(start, len(failures)))


def write_report(path: Path, report: dict, status: int | None) -> None:
    """A worker's report: each plant's output and failures, the failures recorded outside
    any plant, and the exit status (None when the run raised). Written beside `path` and
    moved over it, so that no one reads half of one."""
    data = {"plants": report["plants"],
            "failures": [f for i, f in enumerate(failures) if i not in report["taken"]],
            "status": status}
    partial = path.with_name(path.name + ".partial")
    partial.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
    os.replace(partial, path)


def worker_env() -> dict[str, str]:
    """The run's environment, but for WITHHELD and every `LAKE…`."""
    return {name: value for name, value in os.environ.items()
            if name not in WITHHELD and not name.startswith("LAKE")}


def in_tree(tree: Path, *cmd: str) -> subprocess.CompletedProcess:
    """A command in `tree`, a worker's or the run's directory, with a worker's environment."""
    return subprocess.run(cmd, cwd=tree, env=worker_env(), capture_output=True, text=True)


def linked(root: Path) -> Path | None:
    """The first entry under `root` that is a symbolic link, or a file with a second name."""
    for folder, folders, files in os.walk(root):
        for name in folders + files:
            path = Path(folder, name)
            info = path.lstat()
            if stat.S_ISLNK(info.st_mode) or (stat.S_ISREG(info.st_mode) and info.st_nlink > 1):
                return path
    return None


def make_worker(tree: Path, entry: str) -> tuple[str, str] | None:
    """Make a worker's tree at `tree` (the docstring): None when its Git status is `entry`,
    the tree's entry status; else what is wrong, to follow "worker k's tree", and what to
    show with it."""
    added = run("git", "worktree", "add", "--detach", "--no-checkout", str(tree), "HEAD")
    if added.returncode != 0:
        return f"could not be made: git worktree add: exit {added.returncode}", (
            added.stdout + added.stderr)
    listed = subprocess.run(("git", "ls-files", "-z", "--cached", "--others",
                             "--exclude-standard"), cwd=ROOT, capture_output=True)
    if listed.returncode != 0:
        return f"could not be made: git ls-files: exit {listed.returncode}", (
            listed.stderr.decode(errors="replace"))
    try:
        for name in dict.fromkeys(name.decode() for name in listed.stdout.split(b"\0") if name):
            source, target = ROOT / name, tree / name
            if source.is_symlink() or source.is_file():
                target.parent.mkdir(parents=True, exist_ok=True)
                if source.is_symlink():
                    target.symlink_to(os.readlink(source))
                else:
                    shutil.copy2(source, target)
        indexes = [run("git", "rev-parse", "--git-path", "index"),
                   in_tree(tree, "git", "rev-parse", "--git-path", "index")]
        if any(index.returncode != 0 for index in indexes):
            return "could not be made: git rev-parse --git-path index failed", "".join(
                index.stderr for index in indexes)
        shutil.copyfile(ROOT / indexes[0].stdout.strip(), tree / indexes[1].stdout.strip())
    except OSError as error:
        return f"could not be made: {type(error).__name__}: {error}", ""
    in_tree(tree, "git", "update-index", "-q", "--refresh")
    lake = ROOT / ".lake"
    if lake.is_symlink():
        return ("could not be made: .lake is a symbolic link; a worker needs a build of its "
                "own"), ""
    if lake.exists():
        flags = ("-c", "-R") if sys.platform == "darwin" else ("-a", "--reflink=auto")
        copied = run("cp", *flags, str(lake), str(tree / ".lake"))
        if copied.returncode != 0:
            return (f"could not be made: cp {' '.join(flags)} .lake: exit {copied.returncode}",
                    copied.stdout + copied.stderr)
        shared = linked(tree / ".lake")
        if shared is not None:
            return (f"could not be made: {shared.relative_to(tree)} is a symbolic link or has "
                    "a second name; a worker's build shares nothing"), ""
    status = in_tree(tree, "git", "status", "--porcelain")
    if status.returncode != 0 or status.stdout != entry:
        return "does not match the tree under test", status.stdout + status.stderr
    return None


def well_formed(report) -> bool:
    """Whether `report` has the form write_report gives it: every field read_report and
    run_workers read is there, with its type, `status` among them, which may be None but
    not missing."""
    def strings(value) -> bool:
        return isinstance(value, list) and all(isinstance(s, str) for s in value)
    return (isinstance(report, dict) and {"plants", "failures", "status"} <= report.keys()
            and strings(report["failures"])
            and (report["status"] is None or type(report["status"]) is int)
            and isinstance(report["plants"], list)
            and all(isinstance(p, dict) and isinstance(p.get("name"), str)
                    and isinstance(p.get("output"), str) and strings(p.get("failures"))
                    for p in report["plants"]))


def read_report(path: Path, names: list[str], code: int) -> tuple[list[dict], list[str],
                                                                   list[str]]:
    """What a worker that was given the plants `names` and exited with `code` reported: the
    plants it ran, in order, each with its output and failures; its own failures; and why
    it crashed, if it did (the docstring). A report that names other plants than its own,
    in their order, is trusted for none."""
    crashed = [] if code in (0, 1) else [f"exit {code}"]
    try:
        report = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return [], [], crashed + ["no report"]
    except (OSError, ValueError) as error:
        return [], [], crashed + [f"its report cannot be read ({type(error).__name__}: "
                                  f"{error})"]
    if not well_formed(report):
        return [], [], crashed + ["its report is not in the form a worker writes"]
    plants, own = report["plants"], report["failures"]
    given = [p["name"] for p in plants]
    if given != names[:len(given)]:
        crashed.append(f"its report names {', '.join(given) or 'no plant'}, not its plants "
                       "in order")
        plants = []
    elif len(given) < len(names):
        crashed.append(f"its report lacks {', '.join(names[len(given):])}")
    found = own or any(p["failures"] for p in report["plants"])
    if code in (0, 1) and (report["status"] != code or (code == 0) == bool(found)):
        crashed.append(f"its exit disagrees with its report (status {report['status']!r}, "
                       f"{'with' if found else 'without'} failures)")
    return plants, own, crashed


def stop(workers: list[subprocess.Popen]) -> None:
    """Interrupt each worker still running, so that its `finally` restores its tree, and
    wait for every one; interrupted while waiting, kill them all, wait, and raise. The
    workers share the run's process group, so a worker the terminal's interrupt has already
    reached is interrupted a second time here, which may cut its `finally` short. Its tree
    is removed either way (remove), and the tree under test is never planted: only the
    workers' trees are."""
    for worker in workers:
        if worker.poll() is None:
            worker.send_signal(signal.SIGINT)
    try:
        for worker in workers:
            worker.wait()
    except BaseException:
        for worker in workers:
            worker.kill()
        for worker in workers:
            worker.wait()
        raise


def remove(trees: list[Path], base: Path) -> None:
    """Remove the workers' trees, each with Git's record of it, then `base`, with their
    reports and logs: SIGINT ignored throughout, and the previous handler put back after,
    so that an interruption leaves none of them; each removal whatever became of those
    before it. A tree that Git cannot remove is deleted, with a note that its record stays
    until Git prunes it: never `git worktree prune`, which would prune other trees' too."""
    previous = signal.signal(signal.SIGINT, signal.SIG_IGN)
    try:
        for k, tree in enumerate(trees, 1):
            try:
                if not tree.exists():
                    continue
                removed = run("git", "worktree", "remove", "--force", "--force", str(tree))
                if removed.returncode == 0:
                    continue
                why = f"exit {removed.returncode}: {(removed.stdout + removed.stderr).strip()}"
            except Exception as error:
                why = f"{type(error).__name__}: {error}"
            shutil.rmtree(tree, ignore_errors=True)
            print(f"note: git worktree remove could not remove worker {k}'s tree ({why}); "
                  f"{tree} was deleted, and its record in the repository's worktree list "
                  "stays until Git prunes it")
        shutil.rmtree(base, ignore_errors=True)
    finally:
        signal.signal(signal.SIGINT, previous)


def run_workers(chosen: list[Plant], count: int, entry: str, sources: dict[int, str]) -> int:
    """Run `chosen` in `count` workers (the docstring), `entry` the tree's entry status, and
    print what they found: each plant's output in the stable order, its failures recorded
    under its heading in `sources`, then the run's own. Return how many plants reported.
    Every worker's tree is removed before it returns or raises."""
    seconds = recorded_times()
    shares, loads = deal(chosen, count, seconds)
    if seconds:
        print(f"The plants in {count} workers, dealt longest first by {TIMES}:",
              file=sys.stderr)
        unmeasured = [p.name for p in chosen if p.name not in seconds]
        if unmeasured:
            print(f"  no time for {', '.join(unmeasured)}: each weighs their median, "
                  f"{statistics.median(seconds.values()):g} s", file=sys.stderr)
    else:
        print(f"The plants in {count} workers, dealt in turn: with no times in {TIMES}, "
              "every plant weighs the same:", file=sys.stderr)
    for k, (share, load) in enumerate(zip(shares, loads), 1):
        print(f"  worker {k}{f', about {load:.0f} s' if seconds else ''}: "
              f"{', '.join(p.name for p in share)}", file=sys.stderr)
    base = Path(tempfile.mkdtemp(prefix="stoicheia-negative-")).resolve()
    trees = [base / f"worker-{k}" for k in range(1, count + 1)]
    workers: list[subprocess.Popen] = []
    try:
        # A failure or "false" is the good answer: no repository above the workers' trees.
        inside = in_tree(base, "git", "rev-parse", "--is-inside-work-tree")
        if inside.returncode == 0 and inside.stdout.strip() != "false":
            tmpdir = os.environ.get("TMPDIR")
            message = (f"the run's directory {base} is inside a Git work tree, where a "
                       "plant's fixture would find a repository above it; no worker was "
                       "made: set TMPDIR elsewhere ("
                       + (f"it is {tmpdir!r})" if tmpdir is not None else "it is not set)"))
            failures.append(message)
            print(f"✗ {message}")
            return 0
        for k, tree in enumerate(trees, 1):
            fault = make_worker(tree, entry)
            if fault is not None:
                message, shown_with = f"worker {k}'s tree {fault[0]}", fault[1]
                failures.append(message)
                print(f"✗ {message}" + (":" if shown_with else ""))
                if shown_with:
                    print(shown_with, end="" if shown_with.endswith("\n") else "\n")
                return 0
        env = worker_env()
        for k, (tree, share) in enumerate(zip(trees, shares), 1):
            with open(base / f"worker-{k}.log", "wb") as log:
                workers.append(subprocess.Popen(
                    [sys.executable, str(tree / "scripts/negative_tests.py"),
                     *(arg for p in share for arg in ("--plant", p.name)),
                     "--worker-report", str(base / f"worker-{k}.json")],
                    cwd=tree, env=env, stdin=subprocess.DEVNULL, stdout=log,
                    stderr=subprocess.STDOUT))
        for worker in workers:
            worker.wait()
        reports = [read_report(base / f"worker-{k}.json", [p.name for p in share],
                               worker.returncode)
                   for k, (share, worker) in enumerate(zip(shares, workers), 1)]
        outputs = {p["name"]: p for plants, _, _ in reports for p in plants}
        for plant in chosen:
            if plant.name in outputs:
                sys.stdout.write(outputs[plant.name]["output"])
                for failure in outputs[plant.name]["failures"]:
                    sources[len(failures)] = f"{plant.name} ({shown(plant.path)}):"
                    failures.append(failure)
        for k, (tree, share, (_, own, crashed)) in enumerate(zip(trees, shares, reports), 1):
            label = f"worker {k} ({', '.join(p.name for p in share)})"
            for failure in own:
                failures.append(f"{label}: {failure}")
                print(f"✗ {label}: {failure}")
            if crashed:
                message = f"{label} crashed: {'; '.join(crashed)}"
                failures.append(message)
                print(f"✗ {message}; its log ends:")
                tail = (base / f"worker-{k}.log").read_text(encoding="utf-8",
                                                            errors="replace")[-3000:]
                if tail:
                    print(tail, end="" if tail.endswith("\n") else "\n")
            after = in_tree(tree, "git", "status", "--porcelain")
            if after.returncode != 0 or after.stdout != entry:
                message = f"worker {k}'s tree did not return to its entry Git status"
                failures.append(message)
                print(f"✗ {message}:")
                output = after.stdout + after.stderr
                if output:
                    print(output, end="" if output.endswith("\n") else "\n")
        return len(outputs)
    finally:
        try:
            stop(workers)
        finally:
            remove(trees, base)


def bracket(parser: argparse.ArgumentParser, args: argparse.Namespace,
            sources: dict[int, str], workers: int, report: dict | None = None) -> int:
    """The run in its Git bracket, and its closing list and exit status: the chosen plants
    in `workers` workers when that is more than one, else here, each kept in `report` when
    the run is a worker's."""
    # First of all: the restoration regressions load the real plants' folder, so a file
    # that a plant's file writes as it loads, there or here, shows at the close.
    before = run("git", "status", "--porcelain")
    if not expect_success("entry Git status", before):
        return 1
    ran = total = 0
    try:
        # A worker leaves the regressions to the run that made it, which ran them first.
        if report is not None or regressions():
            changes = guard()  # as for --counts-only
            loaded = choose(parser, args, sources)
            if loaded is not None:
                chosen, total = loaded
                expected = len(chosen)
                count = min(workers, expected)
                if count > 1:
                    ran = run_workers(chosen, count, before.stdout, sources)
                else:
                    for plant in chosen:
                        if report is None:
                            run_plant(plant, sources, changes)
                        else:
                            run_reported(plant, sources, changes, report)
                        ran += 1
                # Fewer only when the list of the plants chosen changes as the loop runs, or
                # when a worker does not report them all.
                if ran < expected:
                    message = f"only {ran} of the {expected} plants chosen were run"
                    failures.append(message)
                    print(f"✗ {message}")
                restored = fidelity()
                if restored.returncode != 0:
                    failures.append("the unplanted tree failed check_fidelity.py")
                    print((restored.stdout + restored.stderr)[-3000:])
                else:
                    print("✓ the unplanted tree passes check_fidelity.py")
                for reason in changes():
                    message = shared_change(reason, "after the closing check")
                    failures.append(message)
                    print(f"✗ {message}")
    finally:
        original = sys.exception()
        try:
            after = run("git", "status", "--porcelain")
            if expect_success("final Git status", after):
                if after.stdout != before.stdout:
                    message = "the working tree did not return to its entry Git status"
                    failures.append(message)
                    print(f"✗ {message}:")
                    output = after.stdout + after.stderr
                    if output:
                        print(output, end="" if output.endswith("\n") else "\n")
                else:
                    print("✓ working tree restored to its entry Git status")
        except BaseException as error:
            if original is None:
                raise
            print(f"Final Git status also failed: {type(error).__name__}: {error}")
    return close(sources, ran, total)


def main(argv=()) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    only = parser.add_mutually_exclusive_group()
    only.add_argument("--counts-only", action="store_true",
                      help="only the count plants and file-only regressions; no build needed")
    only.add_argument("--plant", action="append", metavar="NAME",
                      help=f"only the plant {PLANTS}/NAME.py, in the usual Git bracket; "
                           "may be given more than once")
    only.add_argument("--times-from-log", metavar="LOG",
                      help=f"write {TIMES} from the plants' time lines in LOG, a run's output")
    parser.add_argument("--workers", metavar="N",
                        help="run the plants in N workers, each in a worktree of its own "
                             f"(default: {WORKERS} if set, else 1)")
    parser.add_argument("--worker-report", metavar="FILE", help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    if args.worker_report is not None and not args.plant:
        parser.error("--worker-report is for a worker, which is given its plants by --plant")
    workers = worker_count(parser, args)
    if args.times_from_log is not None:
        return write_times(Path(args.times_from_log))
    sources: dict[int, str] = {}
    if args.counts_only:
        if not regressions():
            return 1
        # Made before any plant's file is read, and held here, so no plant can rebind it.
        changes = guard()
        loaded = choose(parser, args, sources)
        if loaded is None:
            return close(sources)
        run_plant(loaded[0][0], sources, changes)
        if failures:
            print("\n".join(failures))
            return 1
        print("✓ count plants passed; other plants were not run (--counts-only)")
        return 0
    if args.worker_report is None:
        return bracket(parser, args, sources, workers)
    # A worker: its output goes to a log, line by line, so that a crash leaves what it
    # printed; and its report is written whatever happens.
    if isinstance(sys.stdout, io.TextIOWrapper):
        sys.stdout.reconfigure(line_buffering=True)
    report: dict = {"plants": [], "taken": set()}
    status = None
    try:
        status = bracket(parser, args, sources, 1, report)
        return status
    finally:
        write_report(Path(args.worker_report), report, status)


if __name__ == "__main__":
    # The plants import this module by its name: register the running module under it,
    # rather than importing the file a second time, through Python's cache, so that they
    # and the runner share one module, with one `failures` and one `refusals`.
    sys.modules["negative_tests"] = sys.modules[__name__]
    sys.exit(main(sys.argv[1:]))
