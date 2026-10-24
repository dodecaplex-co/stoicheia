"""Without a build, on a copy of `facts.json`: a changed statement of III.1's porism makes
III.1's review record stale. `check_fidelity.py --facts` on the copy must fail, saying that
III.1's statement has changed since it was reviewed.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    def change(facts):
        e = nt.entry(facts, "III.1 Por.")
        e["statement"] = e["statement"] + " → True"
    nt.expect_failure("a changed statement of III.1's porism", nt.with_facts(change),
                      "III.1: its statement has changed since it was reviewed")
