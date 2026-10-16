"""Break the project on purpose, and check that it notices.

Each test makes one small change that must be caught, runs the check that should
catch it, and puts everything back. Run from the repo root after `lake build` and
`lake env lean Certificate/Facts.lean`; CI runs it on every push.

1. An edited Heath word: `check_fidelity.py` fails on I.1.
2. The README's "Try breaking it": I.1 takes its radii from the wrong circle, and
   Lean refuses the proof.
3. Postulate 5 used in I.16, a planted Euclidean-only rule (`Tacit.Euclidean`) used
   there too, and an axiom declared in I.16's own file after a docstring on the same
   line: the certificate, recomputed, fails `check_fidelity.py` for each, and for
   the count of Euclid's assumptions.

The files changed are restored, and so is `facts.json`; after test 3 the proofs are
built again from the restored files. Exits non-zero if any change goes unnoticed.
Standard library only.
"""

import subprocess
import sys

import heath

ROOT = heath.ROOT
PLANTED = ROOT / "Elements" / "Foundations" / "Tacit" / "Planted.lean"
failures: list[str] = []


def run(*cmd: str) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)


def replace_once(rel: str, old: str, new: str) -> str:
    """Change `old` to `new` in the file, and return the text to put back."""
    path = ROOT / rel
    text = path.read_text()
    assert text.count(old) == 1, f"{rel}: expected one {old!r}"
    path.write_text(text.replace(old, new))
    return text


def expect_failure(name: str, result: subprocess.CompletedProcess, *wanted: str) -> None:
    out = result.stdout + result.stderr
    missing = [w for w in wanted if w not in out]
    if result.returncode == 0 or missing:
        failures.append(f"{name}: not caught"
                        + (f" (missing {', '.join(repr(m) for m in missing)})" if missing else ""))
        print(out[-2000:])
    else:
        print(f"✓ {name}: caught")


def heath_word() -> None:
    rel = "heath/I/01.md"
    saved = replace_once(rel, "With centre A and distance AB", "With centre A and radius AB")
    try:
        expect_failure("an edited Heath word", run(sys.executable, "scripts/check_fidelity.py"),
                       "I.1: the `--` comments don't match Heath's proof")
    finally:
        (ROOT / rel).write_text(saved)


def wrong_radii() -> None:
    rel = "Elements/BookI/Prop01.lean"
    saved = replace_once(rel, "Definition15 hA_BCD hC_BCD hB_BCD", "Definition15 hB_ACE hC_ACE hA_ACE")
    try:
        expect_failure("the README's wrong radii in I.1", run("lake", "env", "lean", rel), "error")
    finally:
        (ROOT / rel).write_text(saved)


def planted_assumptions() -> None:
    rel = "Elements/BookI/Prop16.lean"
    facts = (ROOT / "facts.json").read_text()
    PLANTED.write_text(
        "import Elements.Foundations.Words\n\n"
        "namespace Elements.Tacit.Euclidean\n\n"
        "/-- A rule planted by scripts/negative_tests.py. -/\n"
        "axiom planted : True\n\n"
        "end Elements.Tacit.Euclidean\n")
    saved = (ROOT / rel).read_text()
    text = "import Elements.Foundations.Tacit.Planted\n" + saved
    text = text.replace("namespace Elements.BookI\n",
                        "namespace Elements.BookI\n\n/-- Planted. -/ axiom sneaky : True\n", 1)
    head = ("theorem Prop16 {A B C D : Point} (hABC : Triangle A B C) (hBCD : Between B C D) :\n"
            "    ∠ C B A < ∠ A C D ∧ ∠ B A C < ∠ A C D := by\n")
    assert text.count(head) == 1, "Prop16's statement has changed; update this test"
    text = text.replace(head, head + "  have _p5 := @Postulate5\n"
                        "  have _planted := @Elements.Tacit.Euclidean.planted\n"
                        "  have _sneaky := @Elements.BookI.sneaky\n")
    (ROOT / rel).write_text(text)
    try:
        build = run("lake", "build")
        if build.returncode != 0:
            failures.append("the planted assumptions: the changed I.16 did not build")
            print((build.stdout + build.stderr)[-2000:])
            return
        run("lake", "env", "lean", "Certificate/Facts.lean")
        expect_failure("Postulate 5, a Euclidean-only rule and a hidden axiom in I.16",
                       run(sys.executable, "scripts/check_fidelity.py"),
                       "I.16: rests on Postulate5, Tacit.Euclidean.planted before I.29",
                       "BookI.sneaky: an axiom declared in Elements.BookI.Prop16, outside",
                       "I.16: rests on BookI.sneaky",
                       "declares 88 axioms, not 87")
    finally:
        (ROOT / rel).write_text(saved)
        PLANTED.unlink(missing_ok=True)
        (ROOT / "facts.json").write_text(facts)
        rebuilt = run("lake", "build")
        if rebuilt.returncode != 0:
            failures.append("the restored files did not build again")


def main() -> int:
    heath_word()
    wrong_radii()
    planted_assumptions()
    if failures:
        print(f"{len(failures)} change(s) went unnoticed:")
        for f in failures:
            print("  ✗ " + f)
        return 1
    print("✓ every planted change was caught")
    return 0


if __name__ == "__main__":
    sys.exit(main())
