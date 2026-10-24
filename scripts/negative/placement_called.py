"""Without a build, on a copy of `facts.json`: placement (`BookIII.placement`) among III.26's
shared steps is caught, while III.24, the one entry that may call on it, given it too, is
not blamed. `check_fidelity.py --facts` must fail, saying that III.26 calls on
BookIII.placement, and must not say that III.24 calls on anything.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """Placement among the shared steps of III.26, on a copy of facts.json, is caught; III.24,
    the one entry that may call on it, is given the same step and is not blamed."""
    step = {"name": "BookIII.placement", "brings_in": ["I.7"],
            "file": "Elements/BookIII/Placement.lean", "line": 1}

    def change(facts):
        for ref in ("III.24", "III.26"):
            steps = nt.entry(facts, ref)["shared_steps"]
            if not any(s.get("name") == step["name"] for s in steps):
                steps.append(dict(step))
    nt.expect_failure("placement among III.26's shared steps in facts.json", nt.with_facts(change),
                      "III.26: calls on BookIII.placement",
                      unwanted=("III.24: calls on",))
