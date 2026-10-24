"""One build with a construction rule planted in two clean laws' proofs: Postulate 1 in
Metric 3's (`Cited.holds_lenSymm`), `Tacit.circles_meet` in Metric 4's
(`Cited.holds_angleSymm`). Every pin of `Audit/Superposition.lean` is rewritten to what
Lean then prints, and `lake build Audit` must pass, so the pins cannot see the plants. The
certificate recomputed, `check_fidelity.py` fails on the expectations on `cited_laws`,
Metric 3's law in I.4 and in I.8 and Metric 4's in I.4, each with its construction rule,
and on nothing the unplanted tree did not already show. The pins are rewritten by
AUDIT_PIN and rewritten_pins, in scripts/negative_tests.py, where
tests/test_negative_tests.py reads them.
"""

import subprocess

import negative_tests as nt

BUILDS = True

# Each clean law's proof, and the construction rule planted in it: the text that begins its
# proof, and what replaces it.
LAW_PLANTS = (
    ("Postulate1", ":= fun v _ => len_symm (v.pt .A) (v.pt .B)\n",
     ":= by\n  have _planted := @Postulate1\n  exact fun v _ => len_symm (v.pt .A) (v.pt .B)\n"),
    ("Tacit.circles_meet",
     "theorem Cited.holds_angleSymm : Cited.angleSymm.Holds primitives := by\n",
     "theorem Cited.holds_angleSymm : Cited.angleSymm.Holds primitives := by\n"
     "  have _planted := @Tacit.circles_meet\n"),
)


def problems(result: subprocess.CompletedProcess) -> set[str]:
    """The problems a check_fidelity.py run lists, one line each."""
    return {line.strip() for line in result.stdout.splitlines() if line.strip().startswith("✗ ")}


def plant() -> None:
    """Postulate 1 planted in the proof of Metric 3's law, and `Tacit.circles_meet` in Metric
    4's, two laws I.4 cites (I.8 cites the first too), with every pin of
    Audit/Superposition.lean rewritten to what Lean then prints. The audit builds, so its
    pins cannot see the plants; the certificate's expectations on `cited_laws` catch each,
    by its entry and law, and check_fidelity.py finds nothing else that the unplanted tree
    did not already show (#150)."""
    rel, audit = "Elements/Figure/Superposition.lean", "Audit/Superposition.lean"
    baseline = problems(nt.fidelity())
    saved = {p: (nt.ROOT / p).read_text() for p in (rel, audit, "facts.json")}
    outputs = nt.BuildOutputs()
    try:
        for _, old, new in LAW_PLANTS:
            nt.replace_once(rel, old, new)
        if not nt.expect_success("the planted laws build", nt.run("lake", "build")):
            return
        changed = nt.rewritten_pins(audit)
        if changed is None:
            return
        if changed == saved[audit]:
            nt.failures.append("the planted laws: no pin of Audit/Superposition.lean changed; "
                               "update this test")
            return
        (nt.ROOT / audit).write_text(changed)
        if not nt.expect_success("the planted laws' audit, its pins rewritten to match",
                                 nt.run("lake", "build", "Audit")):
            return
        if not nt.expect_success("the planted laws' certificate",
                                 nt.run("lake", "env", "lean", "Certificate/Facts.lean")):
            return
        result = nt.fidelity()
        caught = {"Postulate 1 in the proof of Metric 3's law, its pins rewritten": (
                      "I.4: its construction_rules for the cited law lenSymm is "
                      "['Postulate1'], not []",
                      "I.8: its construction_rules for the cited law lenSymm is "
                      "['Postulate1'], not []"),
                  "Tacit.circles_meet in the proof of Metric 4's law, its pins rewritten": (
                      "I.4: its construction_rules for the cited law angleSymm is "
                      "['Tacit.circles_meet'], not []",)}
        for name, wanted in caught.items():
            nt.expect_failure(name, result, *wanted)
        expected = [w for wanted in caught.values() for w in wanted]
        others = sorted(p for p in problems(result) - baseline
                        if not any(p.startswith(f"✗ {w}") for w in expected))
        if others:
            nt.failures.append("the planted laws: check_fidelity.py also reported "
                               + "; ".join(others))
        else:
            print("✓ the planted laws: nothing but the cited_laws expectations caught them")
    finally:
        for p, text in saved.items():
            (nt.ROOT / p).write_text(text)
        nt.rebuild_restored("the restored laws build", outputs, "Elements", "Audit")
