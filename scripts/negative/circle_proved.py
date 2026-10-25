"""Without a build: Circle 2, `Tacit.inside_of_between`, taken out of the axiom lock (restored
after) and out of the tables of `facts.json`, read into memory, and given as proved in its
`proved_rules`, its `proved_rule_cites` as facts.json gives it, which for Circle 2 cites
nothing. Proved without a forbidden axiom beneath it or a citation of III.2, Circle 2 must
be refused by name: `check_fidelity.check_lock` must say that it is proved without another
forbidden circle rule. Proved from Circle 3, still in the lock, it must pass. The check's
earlier findings are kept.
"""

import json
import subprocess

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """A proved Circle 2, citing nothing in facts.json, must bring in locked Circle 3."""
    inside, outside = "Tacit.inside_of_between", "Tacit.outside_of_between"
    path = nt.ROOT / "Certificate/axioms.lock"
    saved = path.read_bytes()
    saved_errors = list(nt.check_fidelity.errors)
    axioms, vocabulary = nt.check_fidelity.read_lock(path)
    axioms.pop(inside, None)
    try:
        path.write_text(nt.check_fidelity.render_lock(axioms, vocabulary))
        for dependencies in ([], [outside]):
            facts = json.loads((nt.ROOT / "facts.json").read_text())
            for table in ("axiom_types", "axiom_modules"):
                facts[table].pop(inside, None)
            facts.setdefault("proved_rules", {})[inside] = dependencies
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
