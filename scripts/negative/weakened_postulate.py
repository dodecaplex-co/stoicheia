"""Without a build, on a copy of `facts.json`: Postulate 1 weakened in the printed statements
("Ne A B →" made "Ne A B → False →", a Postulate 1 that says nothing) no longer matches the
axiom lock. `check_fidelity.py --facts` on the copy must fail, saying that the statement of
Postulate1 is not the one in `Certificate/axioms.lock`. The real `facts.json` is not
touched.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    def weaken(facts):
        # "Ne A B → …" becomes "Ne A B → False → …": a Postulate 1 that says nothing.
        types = facts["axiom_types"]
        s = types["Postulate1"]
        types["Postulate1"] = s.replace("Ne A B →", "Ne A B → False →", 1) if "Ne A B →" in s \
            else "False → " + s
    nt.expect_failure("Postulate 1 weakened in facts.json", nt.with_facts(weaken),
                      "Postulate1: its statement is not the one in Certificate/axioms.lock")
