"""Without a build, on a copy of `facts.json`: `Touches`, a word only Book III's statements
use, given another meaning (a straight line touching a circle without the clause that A and
B differ) no longer matches the axiom lock. The statements name the word without its
meaning, so no printed statement and no review fingerprint moves, and only the lock can see
it: `check_fidelity.py --facts` on the copy must fail, saying that the definition of
Touches is not the one in `Certificate/axioms.lock`.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    def change(facts):
        # A straight line "touches" a circle without the clause that A and B differ. The
        # statements name the word without its meaning, so no printed statement and no
        # review fingerprint moves: only the lock can see it.
        words = facts["vocabulary"]
        words["Touches"] = words["Touches"].replace("And (Ne A B) ", "", 1) + " "
    nt.expect_failure("Touches given another meaning in facts.json", nt.with_facts(change),
                      "Touches: its definition is not the one in Certificate/axioms.lock")
