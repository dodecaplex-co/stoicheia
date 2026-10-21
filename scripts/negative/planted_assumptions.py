"""One build with planted assumptions, the certificate recomputed, and `check_fidelity.py` run
on it:

- in I.16, Postulate 5, a planted Euclidean-only rule (`Tacit.Euclidean.planted`) and an
  axiom declared in I.16's own file after a docstring on the same line: each is caught, so
  are the count of Euclid's assumptions and the two planted axioms missing from
  `Certificate/axioms.lock`;
- in I.15's porism, which I.15 does not use: Postulate 5, superposition and the later I.22,
  each caught as the porism's, "I.15 Por.: …", and I.15 not blamed;
- a helper of I.16 that mentions I.22 only in its statement: the certificate's walk reads
  types as well as proofs, so I.16 is caught citing a later proposition;
- a `sorry` in I.16's proof: Book I is complete, so I.16 not proved is caught.

If the planted files do not build, the plant fails. The sources and `facts.json` are put
back and rebuilt, and the planted module's outputs are always restored or removed.
"""

import negative_tests as nt

BUILDS = True


def plant() -> None:
    # The count of Euclid's assumptions is the lock's, read before anything is planted:
    # the planted rule makes one more, whatever the foundations hold.
    lock = nt.check_fidelity.read_lock()
    assert lock is not None, "Certificate/axioms.lock is missing"
    locked = len(lock[0])

    facts = (nt.ROOT / "facts.json").read_text()
    outputs = nt.BuildOutputs()
    planted_outputs = nt.BuildOutputs("**/Elements/Foundations/Tacit/Planted.*")

    # I.16: Postulate 5, the planted rule, a hidden axiom, and a helper whose statement
    # alone mentions the later I.22.
    rel16 = "Elements/BookI/Prop16.lean"
    saved16 = (nt.ROOT / rel16).read_text()
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
    saved15 = (nt.ROOT / rel15).read_text()
    porism = saved15.find("theorem Prop15.porism")
    proof = saved15.find(":= by\n", porism)
    assert porism >= 0 and proof >= 0, "Prop15.porism has changed; update this test"
    proof += len(":= by\n")
    text15 = ("import Elements.BookI.Prop22\n" + saved15[:proof]
              + "  have _p5 := @Postulate5\n"
              "  have _sup := @Tacit.superposition\n"
              "  have _later := @Elements.BookI.Prop22\n" + saved15[proof:])

    try:
        nt.PLANTED.write_text(
            "import Elements.Foundations.Words\n\n"
            "namespace Elements.Tacit.Euclidean\n\n"
            "/-- A rule planted by scripts/negative_tests.py. -/\n"
            "axiom planted : True\n\n"
            "end Elements.Tacit.Euclidean\n")
        (nt.ROOT / rel16).write_text(text)
        (nt.ROOT / rel15).write_text(text15)
        build = nt.run("lake", "build")
        if build.returncode != 0:
            nt.failures.append("the planted assumptions: the changed I.15 and I.16 did not build")
            print((build.stdout + build.stderr)[-3000:])
            return
        nt.run("lake", "env", "lean", "Certificate/Facts.lean")
        result = nt.fidelity()
        nt.expect_failure("Postulate 5, a Euclidean-only rule and a hidden axiom in I.16",
                          result,
                          "I.16: rests on Postulate5, Tacit.Euclidean.planted before I.29",
                          "BookI.sneaky: an axiom declared in Elements.BookI.Prop16, outside",
                          "I.16: rests on BookI.sneaky",
                          f"declares {locked + 1} axioms, not {locked}")
        nt.expect_failure("the planted axioms missing from the lock", result,
                          "Tacit.Euclidean.planted: an assumption not in Certificate/axioms.lock",
                          "BookI.sneaky: an assumption not in Certificate/axioms.lock")
        nt.expect_failure("Postulate 5, superposition and a later citation in I.15's porism only",
                          result,
                          "I.15 Por.: rests on Postulate5 before I.29",
                          "I.15 Por.: uses superposition directly (only I.4 and I.8 may)",
                          "I.15 Por.: cites I.22, which does not come before it",
                          unwanted=("✗ I.15: rests on", "✗ I.15: uses superposition",
                                 "✗ I.15: cites"))
        nt.expect_failure("a later proposition named only in a helper's statement", result,
                          "I.16: cites I.22, which does not come before it")
        nt.expect_failure("a sorry in I.16, in a complete book", result,
                          "I.16: Book I is complete, but I.16 is not proved")
    finally:
        (nt.ROOT / rel16).write_text(saved16)
        (nt.ROOT / rel15).write_text(saved15)
        nt.PLANTED.unlink(missing_ok=True)
        (nt.ROOT / "facts.json").write_text(facts)
        try:
            nt.rebuild_restored("the restored files build", outputs)
        finally:
            planted_outputs.restore()
