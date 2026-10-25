"""Without a build: Circle 2, `Tacit.inside_of_between`, taken out of the axiom lock (restored
after) and out of the tables of `facts.json`, read into memory, and given as proved in its
`proved_rules`, citing nothing in its `proved_rule_cites`. Proved without a forbidden axiom
beneath it or a citation of III.2, Circle 2 must be refused by name:
`check_fidelity.check_lock` must say that it is proved without another forbidden circle
rule. Proved from Circle 3 while Circle 3 is a locked axiom, it must pass; once Circle 3 has
left the lock, proved after III.2, the plant puts it back in the lock and in the copy's
tables of axioms, with the statement it keeps, for both cases. The check's earlier findings
are kept.
"""

import json
import subprocess

import negative_tests as nt

BUILDS = False

# Circle 3's statement as the lock prints it, which it keeps as a theorem.
OUTSIDE_TYPE = ("∀ {A B C : Elements.Point} {α : Elements.Circle}, Or (Elements.InsideCircle A α) "
                "(Elements.OnCircle A α) → Not (Elements.InsideCircle C α) → Elements.Between A C B "
                "→ Elements.OutsideCircle B α")
OUTSIDE_MODULE = "Elements.Foundations.Tacit.Diagram"


def plant() -> None:
    """A proved Circle 2, citing nothing, must bring in locked Circle 3."""
    inside, outside = "Tacit.inside_of_between", "Tacit.outside_of_between"
    path = nt.ROOT / "Certificate/axioms.lock"
    saved = path.read_bytes()
    saved_errors = list(nt.check_fidelity.errors)
    axioms, vocabulary = nt.check_fidelity.read_lock(path)
    axioms.pop(inside, None)
    locked = outside in axioms
    axioms.setdefault(outside, OUTSIDE_TYPE)
    try:
        path.write_text(nt.check_fidelity.render_lock(axioms, vocabulary))
        for dependencies in ([], [outside]):
            facts = json.loads((nt.ROOT / "facts.json").read_text())
            for table in ("axiom_types", "axiom_modules"):
                facts[table].pop(inside, None)
            if not locked:
                facts["axiom_types"][outside] = OUTSIDE_TYPE
                facts["axiom_modules"][outside] = OUTSIDE_MODULE
                for table in ("proved_rules", "proved_rule_cites"):
                    facts.get(table, {}).pop(outside, None)
            facts.setdefault("proved_rules", {})[inside] = dependencies
            facts.setdefault("proved_rule_cites", {})[inside] = []
            nt.check_fidelity.errors.clear()
            nt.check_fidelity.check_lock(facts, path)
            found = list(nt.check_fidelity.errors)
            result = subprocess.CompletedProcess([], int(bool(found)), "\n".join(found), "")
            if not dependencies:
                nt.expect_failure("Circle 2 proved without a forbidden axiom", result,
                                  f"{inside} (Circle 2): proved without another forbidden circle rule")
            elif nt.expect_success("Circle 2 proved from locked Circle 3", result):
                print("✓ Circle 2 proved from locked Circle 3: allowed")
    finally:
        path.write_bytes(saved)
        nt.check_fidelity.errors[:] = saved_errors
