"""Break the project on purpose, and check that it notices.

Each test makes one small change that must be caught, runs the check that should
catch it, and puts everything back. Run from the repo root after `lake build` and
`lake env lean Certificate/Facts.lean`, with `Certificate/axioms.lock` and the review
records current; CI runs it on every push.

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
its elapsed time is printed after it, restoration included. The closing list gives each
failure under the plant that added it, and the run's own (the restoration and final
checks) under a heading of their own. `--plant NAME`, given once or more, runs just those
plants, inside the same Git bracket and with the same closing check of the unplanted tree;
an unknown name exits 2, naming the plants there are. `--counts-only` runs the file-only
regressions and count_markers alone, without the Git bracket.

The loader is checked too. It lists scripts/negative/ itself, never Git's index, so the
pre-flight's pass with origin/main's checks, which takes out the files a commit adds, runs
main's plants. A missing or empty folder; an entry, other than the directory
`__pycache__`, that is not a regular file named `[a-z][a-z0-9_]*.py` (a symbolic link or a
directory among them); a file that raises on import, a SyntaxError among them; and a file
with no description, no `BUILDS` of True or False, or no `plant` callable with no
arguments: each is a fault naming the file and the reason, and the run fails before
anything is planted. Each check that catches its plant records a refusal (expect_failure
does, and `refused` for a plant that judges a refusal itself, as stale_page does); a plant
that records none and adds no failure fails the run by its name, since nothing refused
what it planted.

The copies of merge_conflict_markers and count_markers, and stale_page's list of
generated outputs, read Git's tracked files. One absent from the work tree is named on
stdout and passed over: as a note under the check inputs, since the pre-flight's pass with
origin/main's checks takes out the files a commit adds there while Git's index still lists
them (scripts/safe_push.py, step 4); as a failure anywhere else. The rule is
generated_counts.absent_tracked's, which check_fidelity.py and render.py follow for the
tracked Markdown they read.

These faults exercise the style and link checks, page freshness, an audit pin, a
complete book's figures and mishnah, and leanchecker's loading of compiled files and its
kernel replay, as well as the earlier checks. `check_kernel.py`'s own `--self-test`
withholds Postulate 5 from nanoda alone.

Every new plant restores its inputs in `finally`; the freshness plant also restores
all renderer outputs.
The four that build, changed_audit_pin, corrupt_olean, ill_typed_proof and
planted_assumptions, attempt a restoration build; if it fails or is interrupted, every
file in `.lake/build` returns to its saved contents and presence or absence before the
plant, including dependent modules, hashes and traces. planted_assumptions always
restores or removes `Planted.*` outputs in a nested `finally`. Every plant reports its
elapsed time, restoration included. An outer `finally` compares Git status with the entry status, including on interruption, without
replacing an exception already in flight.
Temporary-directory regressions run first, without Lean. Exits non-zero if a fault
goes unnoticed or a restoration check fails. Restoration needs writable files and
an opportunity for `finally` to finish; a forced process kill cannot provide it.
Standard library only; Python 3.11 or later, for the review records.
"""

import argparse
import importlib.util
import inspect
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections.abc import Callable
from contextlib import contextmanager
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
GENERATED = ("facts.json", "book", "CERTIFICATE.md", "GRAPH.md", "README.md",
             "docs/PROGRAM.md")
# The plants' folder, from ROOT, and the name of a plant's file in it.
PLANTS = Path("scripts", "negative")
PLANT_FILE = re.compile(r"[a-z][a-z0-9_]*\.py")


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
    """Copy tracked sources plus current Python tools under /tmp, with no build or .git.

    Git reads the original index through GIT_DIR; GIT_WORK_TREE points only at the
    copy. No Git command writes. Include new Python sources before they are committed.
    A tracked file absent from the work tree is named (absent_tracked), not copied.
    """
    tracked, names = tracked_names()
    tracked.check_returncode()
    git_dir = run("git", "rev-parse", "--absolute-git-dir")
    git_dir.check_returncode()
    paths = {Path(p) for p in names}
    paths.difference_update(absent_tracked(sorted(paths)))
    paths.update(p.relative_to(ROOT) for p in (ROOT / "scripts").glob("*.py"))
    with tempfile.TemporaryDirectory(prefix="stoicheia-counts-", dir="/tmp") as tmp:
        copy = Path(tmp)
        for rel in paths:
            target = copy / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / rel, target)
        yield copy, {**os.environ, "GIT_DIR": git_dir.stdout.strip(),
                     "GIT_WORK_TREE": str(copy)}


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


def load_plant(path: Path) -> Plant | list[str]:
    """The plant in `path`, imported under a module name of its own, or what is wrong
    with it."""
    module_name = f"negative_plant_{path.stem}"
    spec = importlib.util.spec_from_file_location(module_name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    try:
        spec.loader.exec_module(module)
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
    faults, each naming its path: an entry other than the directory __pycache__ that is
    not a regular file with a plant's name, a file that does not load or lacks a part,
    and a missing or empty folder. The folder is listed, never Git, so a file the
    pre-flight takes out is not looked for."""
    folder = ROOT / PLANTS if folder is None else folder
    try:
        entries = sorted(folder.iterdir())
    except OSError as error:
        return [], [f"{shown(folder)}: the plants' folder cannot be listed "
                    f"({type(error).__name__}: {error.strerror or error})"]
    plants, faults = [], []
    for path in entries:
        if path.name == "__pycache__" and path.is_dir() and not path.is_symlink():
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
        else:
            loaded = load_plant(path)
            if isinstance(loaded, Plant):
                plants.append(loaded)
            else:
                faults += [f"{shown(path)}: {reason}" for reason in loaded]
    if not plants and not faults:
        faults.append(f"{shown(folder)}: no plants")
    return sorted(plants, key=lambda p: (p.builds, p.name)), faults


def run_plant(plant: Plant, sources: dict[int, str]) -> None:
    """Run one plant, named before and timed after, and fail it if it neither recorded a
    refusal nor added a failure. `sources` gains the plant's heading for each failure it
    added, by its index in `failures`."""
    path = shown(plant.path)
    print(f"{plant.name} ({path})")
    failed, caught = len(failures), len(refusals)
    started = perf_counter()
    try:
        plant.plant()
    finally:
        print(f"  {plant.name}: {perf_counter() - started:.2f}s (including restoration)")
    if len(failures) == failed and len(refusals) == caught:
        message = f"{plant.name}: nothing refused what {path} planted"
        failures.append(message)
        print(f"✗ {message}")
    for i in range(failed, len(failures)):
        sources[i] = f"{plant.name} ({path}):"


def close(sources: dict[int, str]) -> int:
    """The closing list of failures, each under the plant that added it, and the exit
    status."""
    if not failures:
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


def main(argv=()) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    only = parser.add_mutually_exclusive_group()
    only.add_argument("--counts-only", action="store_true",
                      help="only the count plants and file-only regressions; no build needed")
    only.add_argument("--plant", action="append", metavar="NAME",
                      help=f"only the plant {PLANTS}/NAME.py, in the usual Git bracket; "
                           "may be given more than once")
    args = parser.parse_args(argv)
    if not expect_success("restoration regressions",
                          run(sys.executable, "-I", "tests/test_negative_tests.py")):
        return 1
    print("✓ restoration regressions passed (without Lean)")
    if not expect_success("count regressions",
                          run(sys.executable, "-I", "tests/test_generated_counts.py")):
        return 1
    print("✓ count regressions passed (without Lean)")
    if not expect_success("decision entry regressions",
                          run(sys.executable, "-I", "tests/test_decision_entries.py")):
        return 1
    print("✓ decision entry regressions passed (without Lean)")
    plants, faults = load_plants()
    sources: dict[int, str] = {}
    if faults:
        for fault in faults:
            sources[len(failures)] = f"loading the plants ({PLANTS}/):"
            failures.append(fault)
            print(f"✗ {fault}")
        return close(sources)
    names = [p.name for p in plants]
    wanted = ["count_markers"] if args.counts_only else args.plant or names
    unknown = [name for name in dict.fromkeys(wanted) if name not in names]
    if unknown:
        parser.error(f"no plant {', '.join(map(repr, unknown))} in {PLANTS}/; "
                     f"the plants are {', '.join(names)}")
    chosen = [p for p in plants if p.name in wanted]
    if args.counts_only:
        run_plant(chosen[0], sources)
        if failures:
            print("\n".join(failures))
            return 1
        print("✓ count plants passed; other plants were not run (--counts-only)")
        return 0
    before = run("git", "status", "--porcelain")
    if not expect_success("entry Git status", before):
        return 1
    try:
        for plant in chosen:
            run_plant(plant, sources)
        restored = fidelity()
        if restored.returncode != 0:
            failures.append("the unplanted tree failed check_fidelity.py")
            print((restored.stdout + restored.stderr)[-3000:])
        else:
            print("✓ the unplanted tree passes check_fidelity.py")
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
    return close(sources)


if __name__ == "__main__":
    # The plants import this module by its name; run that copy, not __main__, so that they
    # and the runner share one `failures` and one `refusals`.
    import negative_tests
    sys.exit(negative_tests.main(sys.argv[1:]))
