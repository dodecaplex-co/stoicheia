"""Without a build, on a copy of `facts.json`: Common Notion 4 for figures
(`Tacit.figures_coincide`) among I.5's direct axioms is caught, while I.4, the one entry that
may have it there, given it too, is not blamed. `check_fidelity.py --facts` must fail, saying
that I.5 uses Common Notion 4 for figures directly, and must not say that I.4 does.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """Common Notion 4 for figures among I.5's direct axioms, on a copy of facts.json, is
    caught; I.4, the one entry that may have it there, is given the same axiom and is not
    blamed."""
    name = "Tacit.figures_coincide"

    def change(facts):
        for ref in ("I.4", "I.5"):
            direct = nt.entry(facts, ref)["direct_axioms"]
            if name not in direct:
                direct.append(name)
    nt.expect_failure("Common Notion 4 for figures among I.5's direct axioms in facts.json",
                      nt.with_facts(change),
                      "I.5: uses Common Notion 4 for figures directly (only I.4 may)",
                      unwanted=("I.4: uses Common Notion 4 for figures directly",))
