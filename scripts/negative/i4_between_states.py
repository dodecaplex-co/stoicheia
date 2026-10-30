"""Without a build, on a copy of `facts.json`: I.4 between its two states (#517), its area
clause resting on Metric 9 through its law, `areaCongruent`, or on Common Notion 4 for
figures (`Tacit.figures_coincide`) among its `own_axioms`, is caught. In the one tree I.4 has
both, the axiom given it while it still cites seven laws; in the other, neither, the law
taken out of its `cited_laws` while the axiom is not among its own. Either is made from
whichever state `facts.json` is in. `check_fidelity.py --facts` must fail each by the
expectation with `one_of` on I.4, saying that none of its states holds and naming each with
what sank it.
"""

import json

import negative_tests as nt

BUILDS = False

AXIOM = "Tacit.figures_coincide"
LAW = "areaCongruent"
# Metric 9's law as main's facts.json gives it, for a tree made from the other state.
AREA_LAW = {"proofs": [{"name": "Superposition.Cited.holds_areaCongruent", "line": 76,
                        "file": "Elements/Figure/Superposition.lean"}],
            "law": LAW, "construction_rules": []}


def between(axiom: bool, law: bool):
    """A change to facts.json that leaves I.4 with the new axiom among its own_axioms or not
    (`axiom`), and Metric 9's law among its cited_laws or not (`law`)."""
    def change(facts):
        p = nt.entry(facts, "I.4")
        own = [a for a in p["own_axioms"] if a != AXIOM]
        p["own_axioms"] = sorted(own + [AXIOM]) if axiom else own
        cited = next((c for c in p["cited_laws"] if c["law"] == LAW), AREA_LAW)
        laws = [c for c in p["cited_laws"] if c["law"] != LAW]
        p["cited_laws"] = laws[:2] + [cited] + laws[2:] if law else laws
    return change


def plant() -> None:
    """I.4 with both Metric 9's law and Common Notion 4 for figures, and with neither, on a
    copy of facts.json: each is in neither state, and is caught by the one expectation."""
    pins = json.loads((nt.ROOT / "tests/certificate_expectations.json").read_text())
    numbers = [i for i, x in enumerate(pins["expectations"], 1)
               if x.get("ref") == "I.4" and "one_of" in x]
    if len(numbers) != 1:
        nt.failures.append(f"I.4 between its states: expected one expectation with `one_of` on "
                           f"I.4, found {len(numbers)}; update this test")
        return
    none = (f"I.4: tests/certificate_expectations.json, expectation {numbers[0]} asks that "
            "exactly one of its states hold, and none does")
    states = ('The state "Metric 9" fails: ', 'The state "Common Notion 4 for figures" fails: ')
    for name, change, sunk in (
            ("I.4 with Metric 9's law and Common Notion 4 for figures both",
             between(axiom=True, law=True),
             (f"I.4: its own_axioms should not include {AXIOM}",
              "I.4: its cited_laws has 7 names beginning '', not 6")),
            ("I.4 with neither Metric 9's law nor Common Notion 4 for figures",
             between(axiom=False, law=False),
             (f"I.4: its cited_laws should include {LAW}",
              f"I.4: its own_axioms should include {AXIOM}"))):
        nt.expect_failure(name, nt.with_facts(change), none, *states, *sunk)
