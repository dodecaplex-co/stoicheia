"""Break the project on purpose, and check that it notices.

Each test makes one small change that must be caught, runs the check that should
catch it, and puts everything back. Run from the repo root after `lake build` and
`lake env lean Certificate/Facts.lean`, with `Certificate/axioms.lock` and the review
records current; CI runs it on every push.

1. An edited Heath word: `check_fidelity.py` fails on I.1.
2. The README's "Try breaking it": I.1 takes its radii from the wrong circle, and
   Lean refuses the proof.
3. Without a build, on a copy of `facts.json`: Postulate 1 weakened in the printed
   statements no longer matches the axiom lock; `Touches`, a word only Book III's
   statements use, given another meaning no longer matches it either; a changed
   statement of III.1's porism makes III.1's review record stale; and `Centre`, no
   longer among the opaque primitives (as if it had been made a `def`), is caught.
4. A changed Lean file makes its review record stale (I.1).
5. III.16's review record without its unformalized passage leaves a run of `--` lines
   with no Lean beneath it undeclared.
6. A remark planted in I.5 between two sentences that share one step of Lean leaves the
   first with no Lean of its own: a remark ends a run and carries nothing. A second
   remark, between the next sentence and its Lean, does not stop that Lean carrying it.
7. A `native_decide` in a proposition's file (I.16), read from the source, is caught.
8. One build with planted assumptions, the certificate recomputed:
   - in I.16, Postulate 5, a planted Euclidean-only rule (`Tacit.Euclidean.planted`)
     and an axiom declared in I.16's own file after a docstring on the same line:
     each is caught, so are the count of Euclid's assumptions and the two planted
     axioms missing from `Certificate/axioms.lock`;
   - in I.15's porism, which I.15 does not use: Postulate 5, superposition and the
     later I.22, each caught as the porism's, "I.15 Por.: …", and I.15 not blamed;
   - a helper of I.16 that mentions I.22 only in its statement: the certificate's
     walk reads types as well as proofs, so I.16 is caught citing a later proposition;
   - a `sorry` in I.16's proof: Book I is complete, so I.16 not proved is caught.

The checks these do not plant a fault for are named in README.md's table, "What the
checks show": check_style.py, check_links.py, the pages' freshness and the audit lemmas.

The files changed are restored, and so is `facts.json`; after test 8 the proofs are
built again from the restored files. Exits non-zero if any change goes unnoticed.
Standard library only; Python 3.11 or later, for the review records.
"""

import json
import subprocess
import sys
import tempfile
from pathlib import Path

import check_fidelity
import heath

ROOT = heath.ROOT
PLANTED = ROOT / "Elements" / "Foundations" / "Tacit" / "Planted.lean"
failures: list[str] = []


def run(*cmd: str) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)


def fidelity(*args: str) -> subprocess.CompletedProcess:
    return run(sys.executable, "scripts/check_fidelity.py", *args)


def replace_once(rel: str, old: str, new: str) -> str:
    """Change `old` to `new` in the file, and return the text to put back."""
    path = ROOT / rel
    text = path.read_text()
    assert text.count(old) == 1, f"{rel}: expected one {old!r}"
    path.write_text(text.replace(old, new))
    return text


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
        print(f"✓ {name}: caught")


def heath_word() -> None:
    rel = "heath/I/01.md"
    saved = replace_once(rel, "With centre A and distance AB", "With centre A and radius AB")
    try:
        expect_failure("an edited Heath word", fidelity(),
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


def weakened_postulate() -> None:
    def weaken(facts):
        # "Ne A B → …" becomes "Ne A B → False → …": a Postulate 1 that says nothing.
        types = facts["axiom_types"]
        s = types["Postulate1"]
        types["Postulate1"] = s.replace("Ne A B →", "Ne A B → False →", 1) if "Ne A B →" in s \
            else "False → " + s
    expect_failure("Postulate 1 weakened in facts.json", with_facts(weaken),
                   "Postulate1: its statement is not the one in Certificate/axioms.lock")


def changed_word() -> None:
    def change(facts):
        # A straight line "touches" a circle without the clause that A and B differ. The
        # statements name the word without its meaning, so no printed statement and no
        # review fingerprint moves: only the lock can see it.
        words = facts["vocabulary"]
        words["Touches"] = words["Touches"].replace("And (Ne A B) ", "", 1) + " "
    expect_failure("Touches given another meaning in facts.json", with_facts(change),
                   "Touches: its definition is not the one in Certificate/axioms.lock")


def stale_statement() -> None:
    def change(facts):
        e = entry(facts, "III.1 Por.")
        e["statement"] = e["statement"] + " → True"
    expect_failure("a changed statement of III.1's porism", with_facts(change),
                   "III.1: its statement has changed since it was reviewed")


def primitive_not_opaque() -> None:
    def change(facts):
        facts["opaque"] = [w for w in facts["opaque"] if w != "Centre"]
    expect_failure("a primitive word no longer opaque", with_facts(change),
                   "Centre: no longer an opaque primitive")


def native_decide() -> None:
    rel = "Elements/BookI/Prop16.lean"
    saved = replace_once(rel, "\nend Elements.BookI", "\n/-- Planted by scripts/negative_tests.py. "
                         "-/\ntheorem planted_native : 2 + 2 = 4 := by native_decide\n\n"
                         "end Elements.BookI")
    try:
        expect_failure("a native_decide in I.16's file", fidelity(),
                       f"{rel}: uses native_decide")
    finally:
        (ROOT / rel).write_text(saved)


def stale_lean() -> None:
    path = ROOT / "Elements" / "BookI" / "Prop01.lean"
    saved = path.read_text()
    path.write_text(saved + "\n-- A line planted by scripts/negative_tests.py.\n")
    try:
        expect_failure("a changed Lean file under a review record", fidelity(),
                       "I.1: its Lean file has changed since it was reviewed")
    finally:
        path.write_text(saved)


def toml_blocks(text: str) -> list[str]:
    """A TOML file cut before each table header, so that whole tables can be dropped."""
    blocks, current = [], []
    for line in text.splitlines(keepends=True):
        if line.lstrip().startswith("[") and current:
            blocks.append("".join(current))
            current = []
        current.append(line)
    blocks.append("".join(current))
    return blocks


def undeclared_run() -> None:
    """Drop the [[passage]] tables that begin within III.16's run of `--` lines with no
    Lean beneath it (the unformalized angle clauses), and the run must be caught."""
    import tomllib
    record = heath.review_path("III", 16)
    src = heath.lean_path("III", 16).read_text()
    runs = check_fidelity.uncarried_runs(src, 16)
    starts = check_fidelity.sentence_starts(check_fidelity.proof_lines(src, 16))
    saved = record.read_text()
    kept, dropped = [], []
    for block in toml_blocks(saved):
        table = tomllib.loads(block).get("passage", [{}])[0] if block.lstrip().startswith("[[passage]]") else {}
        at = check_fidelity._plain(table.get("at", "")) if table else None
        if at and any(ln in run.lines and words.startswith(at) for run in runs for ln, words in starts):
            dropped.append(table.get("kind"))
        else:
            kept.append(block)
    if "unformalized" not in dropped:
        failures.append("III.16's unformalized passage: review/III/16.toml declares none in "
                        "the run of `--` lines with no Lean beneath it; update this test")
        return
    record.write_text("".join(kept))
    try:
        expect_failure("III.16's record without its unformalized passage", fidelity(),
                       "III.16: the `--` lines from")
    finally:
        record.write_text(saved)


def remark_ends_run() -> None:
    """A remark between two sentences of I.5 that share one step of Lean. The first
    sentence then has no Lean before the next run of `--` lines, and must be caught; the
    second keeps its Lean, beneath a remark of its own, and must not be."""
    rel = "Elements/BookI/Prop05.lean"
    first = "and in these AB is equal to AC,"
    second = "the remainder BF is equal to the remainder CG."
    saved = replace_once(rel, f"  -- {first}\n  -- {second}\n",
                         f"  -- {first}\n"
                         "  /- Planted by scripts/negative_tests.py: these words have no Lean. -/\n"
                         f"  -- {second}\n"
                         "  /- Planted too: a remark between a sentence and its Lean. -/\n")
    line = saved[:saved.index(f"-- {first}")].count("\n") + 1
    try:
        expect_failure("a sentence with no Lean before a remark in I.5", fidelity(),
                       f"I.5: the `--` lines from {first!r} ({rel}:{line}) have no Lean",
                       unwanted=("I.5: the `--` lines from 'the remainder BF",))
    finally:
        (ROOT / rel).write_text(saved)


def planted_assumptions() -> None:
    facts = (ROOT / "facts.json").read_text()
    PLANTED.write_text(
        "import Elements.Foundations.Words\n\n"
        "namespace Elements.Tacit.Euclidean\n\n"
        "/-- A rule planted by scripts/negative_tests.py. -/\n"
        "axiom planted : True\n\n"
        "end Elements.Tacit.Euclidean\n")

    # I.16: Postulate 5, the planted rule, a hidden axiom, and a helper whose statement
    # alone mentions the later I.22.
    rel16 = "Elements/BookI/Prop16.lean"
    saved16 = (ROOT / rel16).read_text()
    text = "import Elements.Foundations.Tacit.Planted\nimport Elements.BookI.Prop22\n" + saved16
    text = text.replace(
        "namespace Elements.BookI\n",
        "namespace Elements.BookI\n\n/-- Planted. -/ axiom sneaky : True\n\n"
        "/-- Planted: only the statement mentions I.22, and the proof is `trivial`. -/\n"
        "theorem Prop16.typeOnly : (fun _ => True) @Elements.BookI.Prop22 := trivial\n", 1)
    head = ("theorem Prop16 {A B C D : Point} (hABC : Triangle A B C) (hBCD : Between B C D) :\n"
            "    ∠ C B A < ∠ A C D ∧ ∠ B A C < ∠ A C D := by\n")
    assert text.count(head) == 1, "Prop16's statement has changed; update this test"
    text = text.replace(head, head + "  have _p5 := @Postulate5\n"
                        "  have _planted := @Elements.Tacit.Euclidean.planted\n"
                        "  have _sneaky := @Elements.BookI.sneaky\n"
                        "  have _typeOnly : True := Prop16.typeOnly\n"
                        "  have _unproved : True := sorry\n")

    # I.15's porism: Postulate 5, superposition and the later I.22 (which does not
    # import I.15), none of them used by I.15 itself.
    rel15 = "Elements/BookI/Prop15.lean"
    saved15 = (ROOT / rel15).read_text()
    porism = saved15.find("theorem Prop15.porism")
    proof = saved15.find(":= by\n", porism)
    assert porism >= 0 and proof >= 0, "Prop15.porism has changed; update this test"
    proof += len(":= by\n")
    text15 = ("import Elements.BookI.Prop22\n" + saved15[:proof]
              + "  have _p5 := @Postulate5\n"
              "  have _sup := @Tacit.superposition\n"
              "  have _later := @Elements.BookI.Prop22\n" + saved15[proof:])

    (ROOT / rel16).write_text(text)
    (ROOT / rel15).write_text(text15)
    try:
        build = run("lake", "build")
        if build.returncode != 0:
            failures.append("the planted assumptions: the changed I.15 and I.16 did not build")
            print((build.stdout + build.stderr)[-3000:])
            return
        run("lake", "env", "lean", "Certificate/Facts.lean")
        result = fidelity()
        expect_failure("Postulate 5, a Euclidean-only rule and a hidden axiom in I.16",
                       result,
                       "I.16: rests on Postulate5, Tacit.Euclidean.planted before I.29",
                       "BookI.sneaky: an axiom declared in Elements.BookI.Prop16, outside",
                       "I.16: rests on BookI.sneaky",
                       "declares 88 axioms, not 87")
        expect_failure("the planted axioms missing from the lock", result,
                       "Tacit.Euclidean.planted: an assumption not in Certificate/axioms.lock",
                       "BookI.sneaky: an assumption not in Certificate/axioms.lock")
        expect_failure("Postulate 5, superposition and a later citation in I.15's porism only",
                       result,
                       "I.15 Por.: rests on Postulate5 before I.29",
                       "I.15 Por.: uses superposition directly (only I.4 and I.8 may)",
                       "I.15 Por.: cites I.22, which does not come before it",
                       unwanted=("✗ I.15: rests on", "✗ I.15: uses superposition",
                                 "✗ I.15: cites"))
        expect_failure("a later proposition named only in a helper's statement", result,
                       "I.16: cites I.22, which does not come before it")
        expect_failure("a sorry in I.16, in a complete book", result,
                       "I.16: Book I is complete, but I.16 is not proved")
    finally:
        (ROOT / rel16).write_text(saved16)
        (ROOT / rel15).write_text(saved15)
        PLANTED.unlink(missing_ok=True)
        (ROOT / "facts.json").write_text(facts)
        rebuilt = run("lake", "build")
        if rebuilt.returncode != 0:
            failures.append("the restored files did not build again")


def main() -> int:
    heath_word()
    wrong_radii()
    weakened_postulate()
    changed_word()
    stale_statement()
    primitive_not_opaque()
    stale_lean()
    undeclared_run()
    remark_ends_run()
    native_decide()
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
