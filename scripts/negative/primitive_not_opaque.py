"""Without a build, on a copy of `facts.json`: `Centre`, no longer among the opaque primitives
(as if it had been made a `def`), is caught. `check_fidelity.py --facts` on the copy must
fail, saying that Centre is no longer an opaque primitive.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    def change(facts):
        facts["opaque"] = [w for w in facts["opaque"] if w != "Centre"]
    nt.expect_failure("a primitive word no longer opaque", nt.with_facts(change),
                      "Centre: no longer an opaque primitive")
