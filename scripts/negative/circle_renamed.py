"""Circle 3 renamed in the axiom lock (restored after) and in a copy of `facts.json` alike,
`Tacit.outside_of_between` made `Tacit.Circle.outside_of_between`: the two still agree, so
the missing name is what must show that the check no longer refuses the rule.
`check_fidelity.py --facts` must fail, saying that Tacit.outside_of_between (Circle 3) is
not an axiom in `Certificate/axioms.lock`, and must not call it an assumption not in the
lock, or no longer an axiom.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """Circle 3 renamed in the lock and in a copy of facts.json alike: the two still agree,
    so the missing name is what must show that the check no longer refuses it. (III.2's
    [overlap] names the rule and is refused as well; the plant does not rely on that.)"""
    old, new = "Tacit.outside_of_between", "Tacit.Circle.outside_of_between"
    rel = "Certificate/axioms.lock"
    saved = nt.replace_once(rel, f'"{old}" =', f'"{new}" =')

    def change(facts):
        for table in ("axiom_types", "axiom_modules"):
            facts[table][new] = facts[table].pop(old)
    try:
        nt.expect_failure("Circle 3 renamed in the lock and facts.json", nt.with_facts(change),
                          f"{old} (Circle 3): not an axiom in {rel}",
                          unwanted=("an assumption not in", "no longer an axiom"))
    finally:
        (nt.ROOT / rel).write_text(saved)
