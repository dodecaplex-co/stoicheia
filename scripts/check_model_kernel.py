"""Check the formal model's compiled proofs again, by Lean's kernel, apart from the build.

`lake build` in `model/` has Lean's kernel check each declaration of the formal model as it
is elaborated. This script checks every one of them a second time, from the `.olean` files
the build wrote. Lean's leanchecker replays through Lean's kernel each declaration of each
compiled module of the model's own two libraries, `Model` and `Check`: the two roots,
`model/Model.lean` and `model/Check.lean`, and every module under `model/Model/` and
`model/Check/`, private declarations included. The modules are listed from those files, so
a new module is never missed: a source with no compiled file, or a build not up to date
with the sources, is an error, not a silent skip. leanchecker is given the two roots, and
replays every compiled module whose name begins with one; it is asked which modules it
replayed, and the check fails unless they are exactly the modules listed, so a compiled
module whose source is gone fails it too. A rejection names the module and the declaration
that leanchecker names.

leanchecker runs as `check_kernel.py` runs it for `Elements`, but without `--fresh`: each
module's own declarations are replayed into the environment of its imports, and that
environment is loaded from the compiled files, not replayed. So the declarations of Mathlib
and of the packages it requires are not checked here again. That is left to Mathlib's own
checks: a daily job (`.github/workflows/daily.yml` in Mathlib) replays Mathlib and
Batteries from nothing with leanchecker, and checks Mathlib with nanoda, on Mathlib's master
branch as it stands each day, not on the release this package pins. The library's
declarations that `Check` imports, and Lean's own, are replayed from nothing by
`check_kernel.py`, in CI's `check` job. As there, it is the same kernel that
`lake build` runs, so this catches a declaration that reached a compiled file without the
kernel's check, not a fault in the kernel; and it replays any axiom it meets, so which
axioms the proofs rest on is `model/Model/Audit.lean`'s check, not this one's.

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
each, naming its module and its declaration. A source the build never compiled, and a
compiled module whose source is gone, must each fail too, naming the module. Exits 1 on any
failure. Standard library only.

leanchecker replays its modules in parallel, and each loads its imports' environment afresh,
Mathlib's for each module that imports it: on a machine with sixteen threads one run reached
a 49 GB footprint. So it runs on two threads (LEAN_NUM_THREADS, unless that is set already),
which peaked near 2.6 GB and took about a minute for the whole model.
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
        fail(f"cannot run {cmd[0]} ({e}); is elan's `lake` on the PATH?")


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


def compiled_file(package: Path, parts: tuple[str, ...]) -> Path:
    return package.joinpath(".lake", "build", "lib", "lean", *parts[:-1], parts[-1] + ".olean")


def to_replay(package: Path, modules: dict[tuple[str, ...], Path]) -> list[tuple[str, ...]]:
    """The modules whose compiled files leanchecker must replay: all of them, but a source
    named in NOT_COMPILED that has none. Any other source without one is an error."""
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
    return listed


def replay(package: Path, bin_: Path, modules: list[tuple[str, ...]]) -> None:
    """Have leanchecker replay every declaration of each module, and check that it
    replayed exactly these modules."""
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", THREADS)
    # Without --fresh, leanchecker replays every compiled module whose name begins with a
    # name it is given, and it searches every compiled file on the path, Mathlib's
    # thousands, once for each: so it is given the two roots, not each module (fifty-five
    # names took eleven minutes, not one), and its own account of what it replayed is
    # checked against the list below.
    done = run(["lake", "env", str(bin_ / "leanchecker"), "-v", *LIBRARIES], package,
               env=env)
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


def check(package: Path, bin_: Path) -> list[tuple[str, ...]]:
    modules = to_replay(package, sources(package))
    replay(package, bin_, modules)
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
            for path, text in {**CONTROL, **files, "lakefile.toml": LAKEFILE,
                               "lean-toolchain": toolchain}.items():
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
        print(f"✓ model kernel self-test: lake build accepts both theorems of False added "
              f"without the kernel's check, and the replay rejects each, naming it; the "
              f"control passes, and a module without a compiled file or a source fails")
        return

    try:
        modules = check(MODEL, bin_)
    except Rejected as e:
        fail(str(e))
    excused = "".join(f"; {shown(parts)} is not replayed: {reason}"
                      for parts, reason in NOT_COMPILED.items() if parts not in modules)
    print(f"✓ model kernel: Lean's kernel accepts again every declaration of the "
          f"{len(modules)} compiled modules of Model and Check, replayed by leanchecker "
          f"into their imports' environments, which are loaded, Mathlib's among them"
          f"{excused}")


if __name__ == "__main__":
    main()
