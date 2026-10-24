"""An axiom dropped from an audit lemma's expected list, the first project axiom of
`Audit.III_2`'s pin in `Audit/Overlaps.lean`: `lake build Audit` must fail with the file's
name, a `#guard_msgs` mismatch, the lemma and the axiom dropped; the restored audit must
build.
"""

import re

import negative_tests as nt

BUILDS = True


def plant() -> None:
    rel = "Audit/Overlaps.lean"
    path = nt.ROOT / rel
    saved = path.read_bytes()
    pins = list(re.finditer(rb"'Audit\.III_2' depends on axioms: \[([^\]]*)\]", saved))
    assert len(pins) == 1, "expected exactly one Audit.III_2 axiom pin"
    pin = pins[0]
    axioms = [a.strip() for a in pin[1].split(b",") if a.strip()]
    dropped = next((a for a in axioms if a.startswith(b"Elements.")), None)
    assert dropped is not None, "Audit.III_2's pin has no project axiom to drop"
    remaining = axioms.copy()
    remaining.remove(dropped)
    changed = saved[:pin.start(1)] + b", ".join(remaining) + saved[pin.end(1):]
    outputs = nt.BuildOutputs()
    try:
        path.write_bytes(changed)
        nt.expect_failure("an axiom dropped from Audit.III_2's pin", nt.run("lake", "build", "Audit"),
                          f"{rel}:", "Docstring on `#guard_msgs` does not match generated message",
                          "Audit.III_2", dropped.decode())
    finally:
        path.write_bytes(saved)
        nt.rebuild_restored("the restored audit build", outputs, "Audit")
