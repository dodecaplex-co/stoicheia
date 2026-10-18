"""Check every proof again, from the compiled library, with two kernels.

`lake build` has Lean's kernel check each declaration as it is elaborated. This script
checks the result a second and a third time, from the `.olean` files that the build wrote
and the certificate reads:

1. **leanchecker** replays the whole environment of `Elements`, every declaration down to
   Lean's own, through Lean's kernel. It would catch a declaration that reached the
   compiled files without the kernel's check.
2. **nanoda**, a type checker for Lean written separately from Lean, in Rust, checks the
   same declarations, exported with `leanexport`. It admits only the axioms of
   `Certificate/axioms.lock` and Lean's three (`propext`, `Classical.choice`,
   `Quot.sound`): any declaration that needs another axiom, as `sorryAx` or the compiler's
   `Lean.ofReduceBool`, is an error.

Both programs come with the Lean toolchain that `lean-toolchain` pins, in the folder
`lean --print-prefix` names, so nothing is installed. Run it from anywhere, after
`lake build`:

    python3 scripts/check_kernel.py               both checks
    python3 scripts/check_kernel.py --self-test   both, then nanoda again with Postulate 5
                                                  withheld, which must fail

The self-test plants a fault of the kind the check exists to catch: a proof resting on an
axiom it is not allowed. Exits 1 on any failure. Standard library only.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOCK = ROOT / "Certificate" / "axioms.lock"
STANDARD = ["propext", "Classical.choice", "Quot.sound"]
WITHHELD = "Elements.Postulate5"


def fail(message: str) -> None:
    print(f"✗ kernel: {message}", file=sys.stderr)
    sys.exit(1)


def toolchain_bin() -> Path:
    """The toolchain's bin folder, where leanchecker, leanexport and nanoda_bin live."""
    try:
        out = subprocess.run(["lake", "env", "lean", "--print-prefix"], cwd=ROOT,
                             capture_output=True, text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError) as e:
        fail(f"cannot ask Lean for its toolchain ({e}); is `lake` on the PATH?")
    folder = Path(out) / "bin"
    for tool in ("leanchecker", "leanexport", "nanoda_bin"):
        if not (folder / tool).exists():
            fail(f"{tool} is not in {folder}; the pinned toolchain should carry it")
    return folder


def locked_axioms() -> list[str]:
    """The axioms of the lock, by their full Lean names."""
    text = LOCK.read_text(encoding="utf-8")
    section = re.search(r"^\[axioms\][^\n]*\n(.*?)(?=^\[|\Z)", text, re.M | re.S)
    if not section:
        fail(f"no [axioms] section in {LOCK.relative_to(ROOT)}")
    names = re.findall(r'^"([^"]+)" =', section.group(1), re.M)
    if not names:
        fail(f"no axioms read from {LOCK.relative_to(ROOT)}")
    return [f"Elements.{n}" for n in names]


def run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, **kw)


def nanoda(bin_: Path, export: Path, permitted: list[str], work: Path) -> subprocess.CompletedProcess:
    config = work / "nanoda.json"
    config.write_text(json.dumps({
        "export_file_path": str(export),
        "use_stdin": False,
        "permitted_axioms": STANDARD + permitted,
        "unpermitted_axiom_hard_error": False,
        "nat_extension": True,
        "string_extension": True,
        "print_success_message": True,
    }), encoding="utf-8")
    return run([str(bin_ / "nanoda_bin"), str(config)])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--self-test", action="store_true",
                        help="also withhold Postulate 5 from nanoda, and expect it to fail")
    args = parser.parse_args()

    bin_ = toolchain_bin()
    axioms = locked_axioms()

    replay = run(["lake", "env", str(bin_ / "leanchecker"), "Elements"])
    if replay.returncode != 0:
        print(replay.stdout[-4000:], replay.stderr[-4000:], sep="\n", file=sys.stderr)
        fail("leanchecker rejected the environment of Elements")
    print("  leanchecker: the environment of Elements replays through Lean's kernel")

    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        export = work / "Elements.export"
        with export.open("w", encoding="utf-8") as out:
            done = subprocess.run(["lake", "env", str(bin_ / "leanexport"), "Elements"],
                                  cwd=ROOT, stdout=out, stderr=subprocess.PIPE, text=True)
        if done.returncode != 0:
            print(done.stderr[-4000:], file=sys.stderr)
            fail("leanexport could not export Elements")

        checked = nanoda(bin_, export, axioms, work)
        summary = re.search(r"Checked (\d+) declarations with no typechecker errors",
                            checked.stdout)
        if checked.returncode != 0 or not summary:
            print(checked.stdout[-4000:], checked.stderr[-4000:], sep="\n", file=sys.stderr)
            fail("nanoda rejected a declaration, or one needs an axiom outside the lock")
        print(f"  nanoda: {summary.group(1)} declarations check, with the {len(axioms)} "
              f"axioms of the lock and Lean's three")

        if args.self_test:
            planted = nanoda(bin_, export, [a for a in axioms if a != WITHHELD], work)
            if planted.returncode == 0:
                fail(f"nanoda passed with {WITHHELD} withheld, which I.29 needs")
            print(f"  self-test: with {WITHHELD} withheld, nanoda fails, as it must")

    print("✓ kernel: two kernels accept every declaration of Elements")


if __name__ == "__main__":
    main()
