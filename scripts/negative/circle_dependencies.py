"""Without a build, each on a copy of `facts.json` of its own: the name of Circle 2, now a
theorem, deliberately added to III.3's axioms, and Circle 3 to I.15's porism or II.1's
general companion. `check_fidelity.py --facts` must refuse all three by the entry's name,
as resting on the rule, which is forbidden for every entry, and must not blame I.15 or II.1
themselves.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    for ref, axiom, rule in (
        ("III.3", "Tacit.inside_of_between", "Circle 2"),
        ("I.15 Por.", "Tacit.outside_of_between", "Circle 3"),
        ("II.1 general", "Tacit.outside_of_between", "Circle 3"),
    ):
        def change(facts):
            nt.entry(facts, ref)["axioms"].append(axiom)
        nt.expect_failure(f"{rule} in {ref}'s axioms", nt.with_facts(change),
                          f"{ref}: rests on {axiom} ({rule}), forbidden for every entry",
                          unwanted=(f"{ref.split()[0]}: rests on {axiom}",) if " " in ref else ())
