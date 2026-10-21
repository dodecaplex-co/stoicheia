"""Check the formal model's compiled proofs again, by Lean's kernel, apart from the build.

`lake build` in `model/` has Lean's kernel check each declaration of the formal model as it
is elaborated. This script checks every one of them a second time, from the `.olean` files
the build wrote. Lean's leanchecker replays through Lean's kernel each declaration of each
compiled module of the model's own two libraries, `Model` and `Check`: the two roots,
`model/Model.lean` and `model/Check.lean`, and every module under `model/Model/` and
`model/Check/`, private declarations included. The modules are listed from those files, and
the package's own build folder (`model/.lake/build/lib/lean`) is walked for every compiled
module, so a new module is never missed: a source with no compiled file, a module compiled
outside the two libraries (from a new root or a new library in `model/lakefile.toml`), a
link, or a build not up to date with the sources, is an error, not a silent skip.
leanchecker is given the two roots, and replays every compiled module whose name begins
with one; it is asked which modules it replayed, and the check fails unless they are
exactly the modules listed, so a compiled module whose source is gone fails it too. A
rejection names the module and the declaration that leanchecker names.

leanchecker runs first as `check_kernel.py` runs it for `Elements`, but without `--fresh`:
each module's own declarations are replayed into the environment of its imports, and that
environment is loaded from the compiled files, not replayed. Then it runs with `--fresh` on
`Check`, which never imports Mathlib (`model/lakefile.toml`), and replays every declaration
of `Check`'s whole environment from nothing, into an empty one: Lean's own library as
`Check` loads it (`Init`, `Std` and `Lean`, through `Check/Generator.lean`'s
`import Lean`), the library's modules that `Check` imports, the plain-Lean part of `Model`,
and `Check`. So `Model`'s modules over Mathlib are replayed once, into an environment
loaded with Mathlib's, and `Check`, with all it loads, is replayed from nothing. The first
replay is kept for `Check` as well: it accounts for every compiled module by name, so a
module compiled but not imported by `Check.lean`, which `--fresh Check` would never load,
is replayed all the same, and a rejection there names its module; the replay from nothing
names only the declaration.

What neither replays: the declarations of Mathlib and of the packages it requires. They are
left to Mathlib's own checks: a daily job (`.github/workflows/daily.yml` in Mathlib) replays
Mathlib and Batteries from nothing with leanchecker, and checks Mathlib with nanoda, on
Mathlib's master branch as it stands each day, not on the release this package pins. Of
Lean's own library, everything that `Check` loads is replayed here from nothing, on the
pinned toolchain, the 1,227 `Lean` modules among it, 435 of which lie outside Mathlib's
environment. It holds all of Lean's library that `Model` loads but five of `Lake`'s
modules, which `Model` loads through Mathlib (`Lake.Build.Trace`, `Lake.Config.Glob`,
`Lake.Util.Date`, `Lake.Util.String`, `Lake.Util.Version`): those lie within Mathlib's
environment, which Mathlib's daily job replays, on Mathlib's toolchain rather than the one
pinned here. Lean's core library (`Init`) and the library's declarations that `Check`
imports are replayed from nothing by `check_kernel.py` too, in CI's `check` job, from that
job's own build. As in `check_kernel.py`, it is the same kernel that `lake build` runs, so
this catches a declaration that reached a compiled file without the kernel's check, not a
fault in the kernel; and it replays any axiom it meets, so which axioms the proofs rest on
is `model/Model/Audit.lean`'s check, not this one's.

One source is not replayed, by name (NOT_COMPILED): `model/Check/Write.lean` writes the
generated files whenever Lean elaborates it, so `lake build` never compiles it, and it
leaves no compiled declaration. The check fails if that file goes, so the exception cannot
outlive it; if it is ever compiled, it is replayed with the rest.

Kim Morrison and Sebastian Ullrich wrote leanchecker; it began as Kim Morrison's
lean4checker (https://github.com/leanprover/lean4checker), and now ships with Lean. We
thank them warmly. It comes with the toolchain that `model/lean-toolchain` pins, so nothing
is installed. Run it from anywhere, with Python 3.11 or later:

    python3 scripts/check_model_kernel.py               the check, after `lake build` in model/
    python3 scripts/check_model_kernel.py --self-test   the planted faults and the control

The self-test plants a fault of the kind the check exists to catch. In a temporary directory
outside the repository it writes small packages of the model's shape, which import only
Lean, so it needs no Mathlib, builds each with `lake build`, and runs the same check on it.
The control adds a true theorem to the environment from a `run_cmd` with the kernel's check
switched off (`debug.skipKernelTC`, under which `addDecl` calls Lean's
`addDeclWithoutChecking`), and must pass. Each plant adds a theorem of `False`, proved by
`True.intro`, the same way: once in a `Check` file and once in a `Model` module, whose
compiled file comes in three parts. `lake build` accepts both, and the check must fail on
each, naming its module and its declaration. Two more plants lie outside the libraries'
names, where leanchecker, given the two roots, would never look: one in a second root of
`Model` (`roots = ["Model", "Helper"]`), one in a third library that `Check` imports. On
each, the check must fail at its walk of the build folder, naming the module. A last plant
lies in a package of its own that `Check` requires and imports, as the model's `Check`
requires the edition: the walk and the first replay never look there, and pass it, and the
replay from nothing must fail on it, naming the declaration. A source the build never
compiled, and a compiled module whose source is gone, must each fail too, naming the module.
Exits 1 on any failure. Standard library only.

The first replay runs its modules in parallel, and each loads its imports' environment
afresh, Mathlib's for each module that imports it: on a machine with sixteen threads one run
reached a 49 GB footprint. So it runs on two threads (LEAN_NUM_THREADS, unless that is set
already), which peaked near 2.6 GB and took about a minute for the whole model. The replay
from nothing is one task, which more threads do not speed: on two threads and on four it
took 95 and 112 seconds, with a resident peak of 1.5 GB, on a machine busy with other
builds.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MODEL = ROOT / "model"
LIBRARIES = ("Model", "Check")
# The library whose whole environment is replayed from nothing as well: it never imports
# Mathlib, so that environment is Lean's own library and the edition's, not Mathlib's.
FRESH = "Check"
# Sources that `lake build` never compiles, by design, each with the reason.
NOT_COMPILED = {
    ("Check", "Write"): "it writes the generated files whenever Lean elaborates it, so "
                        "`lake build` never compiles it",
}
THREADS = "2"
PLAIN_PART = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


class Rejected(Exception):
    """The check's verdict against a package; the message names what failed."""


def fail(message: str) -> None:
    print(f"✗ model kernel: {message}", file=sys.stderr)
    sys.exit(1)


def rel(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def shown(parts: tuple[str, ...]) -> str:
    """A module's name as Lean prints it, with «» round a part that is not a plain word."""
    return ".".join(p if PLAIN_PART.fullmatch(p) else f"«{p}»" for p in parts)


def parsed(text: str) -> tuple[str, ...]:
    """A name as Lean prints it, read back into its parts: split at each dot outside «»."""
    parts, part, quoted = [], "", False
    for ch in text.strip():
        if quoted:
            if ch == "»":
                quoted = False
            else:
                part += ch
        elif ch == "«":
            quoted = True
        elif ch == ".":
            parts.append(part)
            part = ""
        else:
            part += ch
    parts.append(part)
    return tuple(parts)


def tail(text: str, size: int = 4000) -> str:
    return text if len(text) <= size else "…" + text[-size:]


def run(cmd: list[str], cwd: Path, **kw) -> subprocess.CompletedProcess:
    try:
        return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, **kw)
    except OSError as e:
        fail(f"cannot run {cmd[0]} ({e}); is elan's bin folder (`~/.elan/bin`) on "
             "the PATH?")


def toolchain_bin() -> Path:
    """The pinned toolchain's bin folder, where leanchecker lives."""
    done = run(["lean", "--print-prefix"], MODEL)
    if done.returncode != 0:
        fail(f"cannot ask Lean for its toolchain:\n{tail(done.stderr)}")
    folder = Path(done.stdout.strip()) / "bin"
    if not (folder / "leanchecker").exists():
        fail(f"leanchecker is not in {folder}; the pinned toolchain should carry it")
    return folder


def sources(package: Path) -> dict[tuple[str, ...], Path]:
    """Every module of the package's two libraries, by the parts of its name, with its
    source: each library's root, and every Lean file beneath the library's folder."""
    found: dict[tuple[str, ...], Path] = {}
    for library in LIBRARIES:
        root = package / f"{library}.lean"
        if root.is_symlink() or not root.is_file():
            raise Rejected(f"{rel(root)}, the root of the library {library}, is missing "
                           "or is a link")
        found[(library,)] = root
        if (package / library).is_symlink():
            raise Rejected(f"{rel(package / library)} is a link, which no check follows")
        for folder, subfolders, files in os.walk(package / library):
            here = Path(folder)
            for name in sorted(subfolders + files):
                path = here / name
                if path.is_symlink():
                    raise Rejected(f"{rel(path)} is a link, which no check follows")
                stem, dot, extension = name.rpartition(".")
                if path.is_dir() or not dot or extension.lower() != "lean":
                    continue
                if extension != "lean" or "." in stem:
                    raise Rejected(f"{rel(path)}: a module's source is named <name>.lean, "
                                   "in lower case and with no other dot, or Lake may not "
                                   "build it")
                found[(library, *path.relative_to(package / library).parts[:-1], stem)] = path
    return found


def build_folder(package: Path) -> Path:
    """Where Lake writes the package's own compiled modules."""
    return package / ".lake" / "build" / "lib" / "lean"


def compiled_file(package: Path, parts: tuple[str, ...]) -> Path:
    return build_folder(package).joinpath(*parts[:-1], parts[-1] + ".olean")


def compiled(package: Path) -> list[tuple[str, ...]]:
    """Every module compiled into the package's own build folder, by the parts of its
    name: one for each `.olean` file beneath it, in any case of the extension."""
    lib = build_folder(package)
    found = []
    for folder, subfolders, files in os.walk(lib):
        here = Path(folder)
        for name in sorted(subfolders + files):
            path = here / name
            if path.is_symlink():
                raise Rejected(f"{rel(path)} is a link in the build folder, which no "
                               "check follows")
            if path.is_file() and name.lower().endswith(".olean"):
                found.append((*path.relative_to(lib).parts[:-1], name[:-len(".olean")]))
    return found


def to_replay(package: Path, modules: dict[tuple[str, ...], Path]) -> list[tuple[str, ...]]:
    """The modules whose compiled files leanchecker must replay: all of them, but a source
    named in NOT_COMPILED that has none. Any other source without one is an error, and so
    is a module compiled into the package's build folder outside the two libraries, which
    leanchecker, given only their names, would never replay."""
    for parts in NOT_COMPILED:
        if parts not in modules:
            raise Rejected(f"NOT_COMPILED excuses {shown(parts)}, which has no source here: "
                           "remove it from the list")
    out = run(["lake", "build", "--no-build"], package)
    if out.returncode != 0:
        raise Rejected(f"the build in {rel(package)} is not up to date with its sources, "
                       f"so its compiled files are not theirs: run `lake build` there "
                       f"first\n{tail(out.stdout + out.stderr)}")
    listed = []
    for parts, source in sorted(modules.items()):
        if compiled_file(package, parts).is_file():
            listed.append(parts)
        elif parts not in NOT_COMPILED:
            raise Rejected(f"{shown(parts)} has a source, {rel(source)}, but no compiled "
                           f"file, so nothing of it could be replayed: is it imported by "
                           f"its library's root, {parts[0]}.lean?")
    for parts in compiled(package):
        if parts[0] not in LIBRARIES:
            raise Rejected(f"{shown(parts)} is compiled in this package but is in "
                           f"neither {' nor '.join(LIBRARIES)}, so leanchecker would not "
                           "replay it: a new root or library must be added to this check")
    return listed


def leanchecker(package: Path, bin_: Path, *args: str) -> subprocess.CompletedProcess:
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", THREADS)
    return run(["lake", "env", str(bin_ / "leanchecker"), "-v", *args], package, env=env)


def replay(package: Path, bin_: Path, modules: list[tuple[str, ...]]) -> None:
    """Have leanchecker replay every declaration of each module, and check that it
    replayed exactly these modules."""
    # Without --fresh, leanchecker replays every compiled module whose name begins with a
    # name it is given, and it searches every compiled file on the path, Mathlib's
    # thousands, once for each: so it is given the two roots, not each module (fifty-five
    # names took eleven minutes, not one), and its own account of what it replayed is
    # checked against the list below.
    done = leanchecker(package, bin_, *LIBRARIES)
    said = done.stdout + done.stderr
    if done.returncode != 0:
        module = re.search(r"leanchecker found a problem in (.+)", said)
        declaration = re.search(r"while replaying declaration '(.+?)':\n", said)
        if module and declaration:
            raise Rejected(f"leanchecker rejects the declaration {declaration.group(1)} of "
                           f"the module {module.group(1)}: "
                           f"{tail(said[declaration.end():].strip())}")
        if module:
            raise Rejected(f"leanchecker rejects the module {module.group(1)}:\n{tail(said)}")
        raise Rejected(f"leanchecker failed:\n{tail(said)}")
    replayed = {parsed(m) for m in re.findall(r"^replaying (.+)$", done.stdout, re.M)}
    missing = sorted(set(modules) - replayed)
    if missing:
        raise Rejected("leanchecker passed without replaying "
                       + ", ".join(shown(m) for m in missing))
    extra = sorted(replayed - set(modules))
    if extra:
        raise Rejected("leanchecker also replayed " + ", ".join(shown(m) for m in extra)
                       + ", compiled with no source here: remove the compiled files a "
                       "deleted source left behind, so that what is replayed is what the "
                       "sources are")


def replay_fresh(package: Path, bin_: Path) -> None:
    """Have leanchecker replay every declaration of FRESH's whole environment, Lean's own
    library among it, from nothing, into an empty environment."""
    done = leanchecker(package, bin_, "--fresh", FRESH)
    said = done.stdout + done.stderr
    whole = f"the whole environment of {FRESH} from nothing"
    if done.returncode != 0:
        declaration = re.search(r"while replaying declaration '(.+?)':\n", said)
        if declaration:
            raise Rejected(f"leanchecker, replaying {whole}, rejects the declaration "
                           f"{declaration.group(1)}: "
                           f"{tail(said[declaration.end():].strip())}")
        raise Rejected(f"leanchecker failed, replaying {whole}:\n{tail(said)}")
    if not re.search(rf"^replaying {FRESH} with --fresh$", done.stdout, re.M):
        raise Rejected(f"leanchecker passed without replaying {whole}:\n{tail(said)}")


def check(package: Path, bin_: Path) -> list[tuple[str, ...]]:
    modules = to_replay(package, sources(package))
    replay(package, bin_, modules)
    replay_fresh(package, bin_)
    return modules


# The self-test's packages: the model's two libraries, a `Model` of Lean modules and a
# `Check` of plain files, importing only Lean.
LAKEFILE = """name = "planted"
defaultTargets = ["Model", "Check"]

[[lean_lib]]
name = "Model"

[[lean_lib]]
name = "Check"
"""
# The same, but with a module outside the two libraries' names: in a second root of
# `Model`, and in a third library that `Check` imports.
SECOND_ROOT = LAKEFILE.replace('name = "Model"\n',
                               'name = "Model"\nroots = ["Model", "Helper"]\n')
THIRD_LIBRARY = LAKEFILE + '\n[[lean_lib]]\nname = "Extra"\n'
# The same, with a package of its own that `Check` requires and imports, as the model's
# `Check` requires the edition: its build folder is its own, not this package's.
REQUIRED = LAKEFILE + '\n[[require]]\nname = "required"\npath = "required"\n'


def unchecked(name: str, statement: str, proof: str, module: bool) -> str:
    """A file that adds `theorem name : statement := proof` without the kernel's check."""
    head = "module\n\nmeta import Lean\n" if module else "import Lean\n"
    return head + f"""
open Lean in
run_cmd Elab.Command.liftCoreM do
  withOptions (debug.skipKernelTC.set · true) do
    addDecl <| .thmDecl
      {{ name := `{name}, levelParams := [], type := mkConst ``{statement},
        value := mkConst ``{proof} }}
"""


CONTROL = {
    "Model.lean": "module\n\npublic import Model.Sound\npublic import Model.Laws.«odd-name»\n",
    "Model/Sound.lean": unchecked("Sound.model", "True", "True.intro", module=True),
    "Model/Laws/odd-name.lean": "module\n\npublic theorem OddName.holds : True := trivial\n",
    "Check.lean": "import Check.Sound\n",
    "Check/Sound.lean": unchecked("Sound.check", "True", "True.intro", module=False),
    "Check/Write.lean": "-- Never compiled, as the model's Check/Write.lean is not.\n",
}

# (name, files over the control's, extra build targets, sources removed after the build,
#  words the rejection must name, or None for the control, which must pass)
CASES = [
    ("the control, with a true theorem added without the kernel's check",
     {}, [], [], None),
    ("a theorem of False added without the kernel's check, in a Check file",
     {"Check.lean": "import Check.Sound\nimport Check.Planted\n",
      "Check/Planted.lean": unchecked("Planted.checkFalse", "False", "True.intro",
                                      module=False)},
     [], [], ["Check.Planted", "Planted.checkFalse"]),
    ("a theorem of False added without the kernel's check, in a Model module",
     {"Model.lean": CONTROL["Model.lean"] + "public import Model.Planted\n",
      "Model/Planted.lean": unchecked("Planted.modelFalse", "False", "True.intro",
                                      module=True)},
     [], [], ["Model.Planted", "Planted.modelFalse"]),
    ("a theorem of False added without the kernel's check, in a second root of Model",
     {"lakefile.toml": SECOND_ROOT,
      "Helper.lean": unchecked("Planted.helperFalse", "False", "True.intro",
                               module=False)},
     [], [], ["Helper", "neither Model nor Check"]),
    ("a theorem of False added without the kernel's check, in a third library",
     {"lakefile.toml": THIRD_LIBRARY,
      "Check.lean": "import Check.Sound\nimport Extra\n",
      "Extra.lean": unchecked("Planted.extraFalse", "False", "True.intro", module=False)},
     [], [], ["Extra", "neither Model nor Check"]),
    ("a theorem of False added without the kernel's check, in a package that Check "
     "requires and imports",
     {"lakefile.toml": REQUIRED,
      "Check.lean": "import Check.Sound\nimport Required\n",
      "required/lakefile.toml": 'name = "required"\n\n[[lean_lib]]\nname = "Required"\n',
      "required/Required.lean": unchecked("Planted.requiredFalse", "False", "True.intro",
                                          module=False)},
     [], [], ["Planted.requiredFalse", "from nothing"]),
    ("a source the build never compiled",
     {"Model/Unbuilt.lean": "module\n\npublic theorem Unbuilt.holds : True := trivial\n"},
     [], [], ["Model.Unbuilt", "no compiled file"]),
    ("a compiled module whose source is gone",
     {"Model/Gone.lean": "module\n\npublic theorem Gone.holds : True := trivial\n"},
     ["Model.Gone"], ["Model/Gone.lean"], ["Model.Gone", "no source"]),
]


def self_test(bin_: Path) -> None:
    toolchain = (MODEL / "lean-toolchain").read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory(prefix="check-model-kernel-") as tmp:
        if ROOT == Path(tmp).resolve() or ROOT in Path(tmp).resolve().parents:
            fail(f"the temporary directory {tmp} is inside the repository; set TMPDIR "
                 "elsewhere")
        for number, (name, files, targets, removed, expected) in enumerate(CASES, 1):
            package = Path(tmp) / f"case{number}"
            for path, text in {**CONTROL, "lakefile.toml": LAKEFILE,
                               "lean-toolchain": toolchain, **files}.items():
                (package / path).parent.mkdir(parents=True, exist_ok=True)
                (package / path).write_text(text, encoding="utf-8")
            for target in [[], *([t] for t in targets)]:
                built = run(["lake", "build", *target], package)
                if built.returncode != 0:
                    fail(f"self-test, {name}: lake build refused the package, so the "
                         f"case shows nothing:\n{tail(built.stdout + built.stderr)}")
            for path in removed:
                (package / path).unlink()
            try:
                check(package, bin_)
            except Rejected as e:
                if expected is None:
                    fail(f"self-test, {name}: the check rejected the control: {e}")
                unnamed = [word for word in expected if word not in str(e)]
                if unnamed:
                    fail(f"self-test, {name}: the check failed, but without naming "
                         f"{', '.join(unnamed)}: {e}")
                print(f"  self-test, {name}: the check fails, as it must: "
                      f"{str(e).splitlines()[0]}")
            else:
                if expected is not None:
                    fail(f"self-test, {name}: the check passed, and must not")
                print(f"  self-test, {name}: lake build accepts it and the check passes")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--self-test", action="store_true",
                        help="plant faults in small packages of the model's shape, which "
                             "need no Mathlib, and expect the check to catch each")
    args = parser.parse_args()

    bin_ = toolchain_bin()
    if args.self_test:
        self_test(bin_)
        print(f"✓ model kernel self-test: lake build accepts each theorem of False added "
              f"without the kernel's check, and the check rejects each, naming it: the "
              f"replay in Model and in Check, the build folder's walk in a second root and "
              f"in a third library, the replay from nothing in a package that Check "
              f"requires; the control passes, and a module without a compiled file or a "
              f"source fails")
        return

    try:
        modules = check(MODEL, bin_)
    except Rejected as e:
        fail(str(e))
    excused = "".join(f"; {shown(parts)} is not replayed: {reason}"
                      for parts, reason in NOT_COMPILED.items() if parts not in modules)
    print(f"✓ model kernel: Lean's kernel accepts again every declaration of the "
          f"{len(modules)} compiled modules of Model and Check, replayed by leanchecker "
          f"into their imports' environments, which are loaded, Mathlib's among them, "
          f"and every declaration of the whole environment of {FRESH}, Lean's own "
          f"library among it, replayed from nothing{excused}")


if __name__ == "__main__":
    main()
