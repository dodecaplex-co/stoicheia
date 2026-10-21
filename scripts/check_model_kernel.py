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
rejection names the module and the declaration that leanchecker names. And what is replayed
is the package's own compiled files, not a copy of them: each module root lies in one folder
of Lean's search path, since Lean loads a module from the first folder that holds its root.
Before either replay, the search path that leanchecker gets through `lake env` is read, and
a root (a folder, or an `.olean` file, at the top of one of its folders) found in two
folders is an error naming both, the names compared without case, which macOS's file system
ignores by default: a copy of `Check` in the build folder of a package that the model
requires, which comes earlier on the path, would otherwise be replayed in place of the
package's own.

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
each, the check must fail at its walk of the build folder, naming the module. Another plant
lies in a package of its own that `Check` requires and imports, as the model's `Check`
requires the edition: the walk and the first replay never look there, and pass it, and the
replay from nothing must fail on it, naming the declaration. A last plant, in a `Check`
file, comes after a copy of `Check`, compiled without it, is put in the build folder of such
a required package, earlier on the search path: both replays would replay the copy and pass
it, so the check must fail before them, naming `Check` and both folders. A source the build
never compiled, and a compiled module whose source is gone, must each fail too, naming the
module. A current compiled module that its library root does not import must pass, while an
edit to its source without another build must fail, naming it. The self-test also interrupts
an untimed command and times out another after each has started a descendant, and requires
both descendants to stop. Exits 1 on any failure. Standard library only.

The first replay runs its modules in parallel, and each loads its imports' environment
afresh, Mathlib's for each module that imports it: on a machine with sixteen threads one run
reached a 49 GB footprint. So it runs on two threads (LEAN_NUM_THREADS, unless that is set
already), which peaked near 2.6 GB and took about a minute for the whole model. The replay
from nothing is one task, which more threads do not speed: on two threads and on four it
took 95 and 112 seconds, with a resident peak of 1.5 GB, on a machine busy with other
builds. Past fifteen minutes the replay from nothing is stopped, and the check fails:
`Check` would then be loading far more than it does, Mathlib's environment perhaps.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MODEL = ROOT / "model"
LIBRARIES = ("Model", "Check")
# The library whose whole environment is replayed from nothing as well: it never imports
# Mathlib, so that environment is Lean's own library and the edition's, not Mathlib's.
FRESH = "Check"
# Seconds after which the replay from nothing is stopped: it takes about two minutes for
# `Check`, and one that loaded Mathlib's environment would run far longer.
FRESH_TIMEOUT = 900
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


def run(cmd: list[str], cwd: Path, timeout: float | None = None,
        **kw) -> subprocess.CompletedProcess:
    """Run a command in its own process group, capturing its output. Stop the whole group
    if it outlives a timeout (which raises subprocess.TimeoutExpired), or if the script is
    interrupted or terminated: `lake env` runs its command as a child, which stopping
    `lake` alone would leave running."""
    try:
        child = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, text=True, process_group=0, **kw)
    except OSError as e:
        fail(f"cannot run {cmd[0]} ({e}); is elan's bin folder (`~/.elan/bin`) on "
             "the PATH?")
    try:
        out, err = child.communicate(timeout=timeout)
    except BaseException:
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        child.communicate()
        raise
    return subprocess.CompletedProcess(cmd, child.returncode, out, err)


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
    listed = []
    for parts, source in sorted(modules.items()):
        if compiled_file(package, parts).is_file():
            listed.append(parts)
        elif parts not in NOT_COMPILED:
            raise Rejected(f"{shown(parts)} has a source, {rel(source)}, but no compiled "
                           f"file, so nothing of it could be replayed: is it imported by "
                           f"its library's root, {parts[0]}.lean?")
    targets = [parts[0] if len(parts) == 1 else "+" + shown(parts) for parts in listed]
    out = run(["lake", "build", "--no-build", *targets], package)
    if out.returncode != 0:
        raise Rejected(f"the build in {rel(package)} is not up to date with its sources, "
                       f"so its compiled files are not theirs: run `lake build` there "
                       f"first\n{tail(out.stdout + out.stderr)}")
    for parts in compiled(package):
        if parts[0] not in LIBRARIES:
            raise Rejected(f"{shown(parts)} is compiled in this package but is in "
                           f"neither {' nor '.join(LIBRARIES)}, so leanchecker would not "
                           "replay it: a new root or library must be added to this check")
    return listed


def lake_env(package: Path, *cmd: str,
             timeout: float | None = None) -> subprocess.CompletedProcess:
    """Run a command through `lake env` in the package, as leanchecker is run, so that it
    gets the environment Lake gives leanchecker there, Lean's search path among it."""
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", THREADS)
    return run(["lake", "env", *cmd], package, timeout=timeout, env=env)


def leanchecker(package: Path, bin_: Path, *args: str,
                timeout: float | None = None) -> subprocess.CompletedProcess:
    return lake_env(package, str(bin_ / "leanchecker"), "-v", *args, timeout=timeout)


def search_path(package: Path) -> list[Path]:
    """The folders in which leanchecker, run through `lake env` in the package, looks for
    compiled modules, in Lean's order (`initSearchPath`): those of LEAN_PATH, then the
    library of the toolchain at LEAN_SYSROOT."""
    said = []
    for name in ("LEAN_PATH", "LEAN_SYSROOT"):
        done = lake_env(package, "printenv", name)
        if done.returncode != 0:
            raise Rejected(f"cannot ask Lake for {name} in {rel(package)}, so the search "
                           f"path that leanchecker gets is unknown:\n"
                           f"{tail(done.stdout + done.stderr)}")
        said.append(done.stdout.rstrip("\n"))
    lean_path, sysroot = said
    return ([package / p for p in lean_path.split(os.pathsep) if p]
            + [package / sysroot / "lib" / "lean"])


def one_folder_each(package: Path) -> None:
    """Refuse a module root (a folder, or an `.olean` file, at the top of a folder of the
    search path) found in more than one folder of it: Lean loads a module from the first
    folder that holds its root, so leanchecker would replay a copy earlier on the path in
    place of the package's own. Roots are compared without case, since a file system that
    ignores it, as macOS's does by default, finds `check/` where Lean asks for `Check/`."""
    folders: list[Path] = []
    for folder in search_path(package):
        if folder.is_dir() and folder.resolve() not in folders:
            folders.append(folder.resolve())
    own = build_folder(package).resolve()
    if own not in folders:
        raise Rejected(f"{rel(own)}, the package's own build folder, is not on the search "
                       "path that leanchecker gets, so it would not replay what is there")
    seen: dict[str, Path] = {}
    for folder in folders:
        for entry in sorted(folder.iterdir()):
            if entry.is_dir():
                root = entry.name
            elif entry.name.lower().endswith(".olean"):
                root = entry.name[:-len(".olean")]
            else:
                continue
            first = seen.setdefault(root.casefold(), folder)
            if first != folder:
                raise Rejected(f"{root} is compiled in {rel(first)} and in {rel(folder)}: "
                               "Lean loads a module from the first folder of its search "
                               "path that holds its root, so leanchecker would replay that "
                               "copy in place of the other")


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
    try:
        done = leanchecker(package, bin_, "--fresh", FRESH, timeout=FRESH_TIMEOUT)
    except subprocess.TimeoutExpired:
        raise Rejected(f"the replay from nothing of {FRESH}'s environment ran past "
                       f"{FRESH_TIMEOUT // 60} minutes: does {FRESH} now import Mathlib? "
                       "model/lakefile.toml says it never does") from None
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
    one_folder_each(package)
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

REQUIRED_PACKAGE = {
    "required/lakefile.toml": 'name = "required"\n\n[[lean_lib]]\nname = "Required"\n',
}

# (name, files over the control's, extra build targets, files changed after the build,
#  sources removed after the build, a shadow or None, words the rejection must name, with
#  {package} for the case's folder, or None for a control, which must pass). A shadow is a
#  library whose compiled files are copied, after the build, into the build folder of the
#  package in `required/`, and files then written over the package's own, which is built
#  again.
CASES = [
    ("the control, with a true theorem added without the kernel's check",
     {}, [], {}, [], None, None),
    ("a theorem of False added without the kernel's check, in a Check file",
     {"Check.lean": "import Check.Sound\nimport Check.Planted\n",
      "Check/Planted.lean": unchecked("Planted.checkFalse", "False", "True.intro",
                                      module=False)},
     [], {}, [], None, ["Check.Planted", "Planted.checkFalse"]),
    ("a theorem of False added without the kernel's check, in a Model module",
     {"Model.lean": CONTROL["Model.lean"] + "public import Model.Planted\n",
      "Model/Planted.lean": unchecked("Planted.modelFalse", "False", "True.intro",
                                      module=True)},
     [], {}, [], None, ["Model.Planted", "Planted.modelFalse"]),
    ("a theorem of False added without the kernel's check, in a second root of Model",
     {"lakefile.toml": SECOND_ROOT,
      "Helper.lean": unchecked("Planted.helperFalse", "False", "True.intro",
                               module=False)},
     [], {}, [], None, ["Helper", "neither Model nor Check"]),
    ("a theorem of False added without the kernel's check, in a third library",
     {"lakefile.toml": THIRD_LIBRARY,
      "Check.lean": "import Check.Sound\nimport Extra\n",
      "Extra.lean": unchecked("Planted.extraFalse", "False", "True.intro", module=False)},
     [], {}, [], None, ["Extra", "neither Model nor Check"]),
    ("a theorem of False added without the kernel's check, in a package that Check "
     "requires and imports",
     {"lakefile.toml": REQUIRED,
      "Check.lean": "import Check.Sound\nimport Required\n",
      **REQUIRED_PACKAGE,
      "required/Required.lean": unchecked("Planted.requiredFalse", "False", "True.intro",
                                          module=False)},
     [], {}, [], None, ["Planted.requiredFalse", "from nothing"]),
    ("a theorem of False added without the kernel's check, in a Check file, with a copy "
     "of Check compiled without it in the build folder of a package that Check requires",
     {"lakefile.toml": REQUIRED,
      "Check.lean": "import Check.Sound\nimport Check.Planted\nimport Required\n",
      **REQUIRED_PACKAGE,
      "required/Required.lean": "theorem Required.holds : True := trivial\n",
      "Check/Planted.lean": "theorem Planted.shadowHolds : True := trivial\n"},
     [], {}, [],
     ("Check", {"Check/Planted.lean": unchecked("Planted.shadowFalse", "False",
                                                "True.intro", module=False)}),
     ["Check is compiled in {package}/required/.lake/build/lib/lean",
      "and in {package}/.lake/build/lib/lean"]),
    ("a source the build never compiled",
     {"Model/Unbuilt.lean": "module\n\npublic theorem Unbuilt.holds : True := trivial\n"},
     [], {}, [], None, ["Model.Unbuilt", "no compiled file"]),
    ("a compiled module whose source is gone",
     {"Model/Gone.lean": "module\n\npublic theorem Gone.holds : True := trivial\n"},
     ["Model.Gone"], {}, ["Model/Gone.lean"], None, ["Model.Gone", "no source"]),
    ("a current compiled module that its library root does not import",
     {"Model/Unimported.lean":
      "module\n\npublic theorem Unimported.holds : True := trivial\n"},
     ["Model.Unimported"], {}, [], None, None),
    ("a stale compiled module that its library root does not import",
     {"Model/Unimported.lean":
      "module\n\npublic theorem Unimported.holds : True := trivial\n"},
     ["Model.Unimported"],
     {"Model/Unimported.lean":
      "module\n\npublic theorem Unimported.changed : True := trivial\n"},
     [], None, ["Model.Unimported", "not up to date"]),
]


def write(package: Path, files: dict[str, str]) -> None:
    for path, text in files.items():
        (package / path).parent.mkdir(parents=True, exist_ok=True)
        (package / path).write_text(text, encoding="utf-8")


def build(package: Path, name: str, targets: list[str]) -> None:
    for target in [[], *([t] for t in targets)]:
        built = run(["lake", "build", *target], package)
        if built.returncode != 0:
            fail(f"self-test, {name}: lake build refused the package, so the case shows "
                 f"nothing:\n{tail(built.stdout + built.stderr)}")


def copy_compiled(package: Path, library: str, into: Path) -> None:
    """Copy the library's compiled files at the top of the package's build folder, its
    folder and its root's files, into another folder."""
    into.mkdir(parents=True, exist_ok=True)
    for entry in build_folder(package).iterdir():
        if entry.name == library or entry.name.startswith(library + "."):
            if entry.is_dir():
                shutil.copytree(entry, into / entry.name)
            else:
                shutil.copy2(entry, into / entry.name)


def self_test(bin_: Path) -> None:
    toolchain = (MODEL / "lean-toolchain").read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory(prefix="check-model-kernel-") as tmp:
        if ROOT == Path(tmp).resolve() or ROOT in Path(tmp).resolve().parents:
            fail(f"the temporary directory {tmp} is inside the repository; set TMPDIR "
                 "elsewhere")
        for number, case in enumerate(CASES, 1):
            name, files, targets, after, removed, shadow, expected = case
            package = Path(tmp).resolve() / f"case{number}"
            write(package, {**CONTROL, "lakefile.toml": LAKEFILE,
                            "lean-toolchain": toolchain, **files})
            build(package, name, targets)
            if shadow:
                library, then = shadow
                copy_compiled(package, library, build_folder(package / "required"))
                write(package, then)
                build(package, name, [])
            write(package, after)
            for path in removed:
                (package / path).unlink()
            try:
                check(package, bin_)
            except Rejected as e:
                if expected is None:
                    fail(f"self-test, {name}: the check rejected the control: {e}")
                unnamed = [word for word in
                           (w.replace("{package}", str(package)) for w in expected)
                           if word not in str(e)]
                if unnamed:
                    fail(f"self-test, {name}: the check failed, but without naming "
                         f"{', '.join(unnamed)}: {e}")
                print(f"  self-test, {name}: the check fails, as it must: "
                      f"{str(e).splitlines()[0]}")
            else:
                if expected is not None:
                    fail(f"self-test, {name}: the check passed, and must not")
                print(f"  self-test, {name}: lake build accepts it and the check passes")


DESCENDANT = """import os
import sys
import time

fd = os.open(sys.argv[1], os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
while True:
    os.write(fd, b"x")
    time.sleep(0.01)
"""

PARENT = """import subprocess
import sys
import time

subprocess.Popen([sys.executable, "-c", sys.argv[2], sys.argv[1]])
time.sleep(60)
"""


def wait_for_heartbeat(path: Path) -> None:
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline:
        if path.is_file() and path.stat().st_size:
            return
        time.sleep(0.01)
    fail("process-cleanup self-test: the descendant never started")


def require_stopped(path: Path, case: str) -> None:
    wait_for_heartbeat(path)
    first = path.stat().st_size
    time.sleep(0.2)
    second = path.stat().st_size
    time.sleep(0.2)
    if first != second or second != path.stat().st_size:
        fail(f"process-cleanup self-test: {case} left its descendant running")


def process_cleanup_self_test() -> None:
    with tempfile.TemporaryDirectory(prefix="check-model-kernel-processes-") as tmp:
        folder = Path(tmp)
        timed = folder / "timed"
        try:
            run([sys.executable, "-c", PARENT, str(timed), DESCENDANT], ROOT, timeout=0.5)
        except subprocess.TimeoutExpired:
            pass
        else:
            fail("process-cleanup self-test: the timed command did not time out")
        require_stopped(timed, "a timeout")

        untimed = folder / "untimed"
        previous = signal.getsignal(signal.SIGTERM)

        def cancel(_number, _frame) -> None:
            sys.exit(128 + signal.SIGTERM)

        def interrupt() -> None:
            deadline = time.monotonic() + 5
            while time.monotonic() < deadline:
                if untimed.is_file() and untimed.stat().st_size:
                    break
                time.sleep(0.01)
            os.kill(os.getpid(), signal.SIGTERM)

        signal.signal(signal.SIGTERM, cancel)
        thread = threading.Thread(target=interrupt)
        thread.start()
        try:
            try:
                run([sys.executable, "-c", PARENT, str(untimed), DESCENDANT], ROOT)
            except SystemExit as e:
                if e.code != 128 + signal.SIGTERM:
                    raise
            else:
                fail("process-cleanup self-test: the untimed command was not interrupted")
        finally:
            thread.join()
            signal.signal(signal.SIGTERM, previous)
        require_stopped(untimed, "an interruption of an untimed command")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--self-test", action="store_true",
                        help="plant faults in small packages of the model's shape, which "
                             "need no Mathlib, and expect the check to catch each")
    parser.add_argument("--self-test-process-cleanup", action="store_true",
                        help="interrupt and time out commands with descendants, and expect "
                             "the whole process group to stop")
    args = parser.parse_args()

    # A terminated or hung-up script exits through SystemExit, so run() stops the command's
    # process group and the temporary folder is removed, as on an interrupt.
    for number in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(number, lambda n, frame: sys.exit(128 + n))
    if args.self_test_process_cleanup:
        process_cleanup_self_test()
        print("✓ model kernel process-cleanup self-test: an interruption of an untimed "
              "command and a timeout stop their descendants")
        return
    bin_ = toolchain_bin()
    if args.self_test:
        self_test(bin_)
        process_cleanup_self_test()
        print(f"✓ model kernel self-test: lake build accepts each theorem of False added "
              f"without the kernel's check, and the check rejects each, naming it: the "
              f"replay in Model and in Check, the build folder's walk in a second root and "
              f"in a third library, the replay from nothing in a package that Check "
              f"requires, and the search path's check where a copy of Check compiled "
              f"without the plant lies earlier on it, naming both folders; the control "
              f"and a current unimported module pass; a module without a compiled file "
              f"or a source and a stale unimported module fail; interrupted and timed-out "
              f"commands stop their descendants")
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
