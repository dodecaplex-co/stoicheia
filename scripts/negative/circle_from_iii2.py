"""Without a build: Circle 3, `Tacit.outside_of_between`, and Circle 2,
`Tacit.inside_of_between`, both taken out of the axiom lock (restored after) and out of the
tables of `facts.json`, read into memory, and given as proved in its `proved_rules` with no
forbidden axiom beneath either, as they will be once Circle 3 is proved after III.2. Citing
nothing in `proved_rule_cites`, each must be refused by name: `check_fidelity.check_lock`
must say that it is proved without another forbidden circle rule or a proof that cites
III.2. Citing III.2, with III.2's real entry from `facts.json`, both must pass. Citing
III.2 when III.2's entry is made circular, Circle 3 added to its axioms, each must be
refused by name, as proved from an III.2 that itself rests on Circle 3. The check's earlier
findings are kept.
"""

import json
import subprocess

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """Circle 2 and Circle 3 proved with no forbidden axiom beneath them must cite a sound
    III.2."""
    rules = {"Tacit.inside_of_between": "Circle 2", "Tacit.outside_of_between": "Circle 3"}
    outside = "Tacit.outside_of_between"
    path = nt.ROOT / "Certificate/axioms.lock"
    saved = path.read_bytes()
    saved_errors = list(nt.check_fidelity.errors)
    axioms, vocabulary = nt.check_fidelity.read_lock(path)
    for name in rules:
        axioms.pop(name, None)
    try:
        path.write_text(nt.check_fidelity.render_lock(axioms, vocabulary))
        for case in ("nothing", "III.2", "circular"):
            facts = json.loads((nt.ROOT / "facts.json").read_text())
            for table in ("axiom_types", "axiom_modules"):
                for name in rules:
                    facts[table].pop(name, None)
            for name in rules:
                facts.setdefault("proved_rules", {})[name] = []
                facts.setdefault("proved_rule_cites", {})[name] = (
                    [] if case == "nothing" else ["III.2"])
            if case == "circular":
                nt.entry(facts, "III.2")["axioms"].append(outside)
            nt.check_fidelity.errors.clear()
            nt.check_fidelity.check_lock(facts, path)
            found = list(nt.check_fidelity.errors)
            result = subprocess.CompletedProcess([], int(bool(found)), "\n".join(found), "")
            if case == "nothing":
                nt.expect_failure(
                    "Circle 2 and Circle 3 proved citing nothing", result,
                    *(f"{name} ({rule}): proved without another forbidden circle rule"
                      for name, rule in rules.items()), "or a proof that cites III.2")
            elif case == "III.2":
                if nt.expect_success("Circle 2 and Circle 3 proved from III.2", result):
                    print("✓ Circle 2 and Circle 3 proved from III.2: allowed")
            else:
                nt.expect_failure(
                    "Circle 2 and Circle 3 proved from an III.2 resting on Circle 3", result,
                    *(f"{name} ({rule}): proved by a proof that cites III.2, but III.2 "
                      f"itself rests on {outside} (Circle 3)" for name, rule in rules.items()))
    finally:
        path.write_bytes(saved)
        nt.check_fidelity.errors[:] = saved_errors
