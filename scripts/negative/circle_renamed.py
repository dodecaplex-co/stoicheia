"""Circle 3 renamed where the certificate keeps it, `Tacit.outside_of_between` made
`Tacit.Circle.outside_of_between`: in the axiom lock (restored after) and in a copy of
`facts.json` alike while it is an axiom, so that the two still agree; in the copy's
`proved_rules` and `proved_rule_cites` once it is a theorem proved after III.2. Either way
the missing name is what must show that the check no longer refuses the rule.
`check_fidelity.py --facts` must fail, saying that Tacit.outside_of_between (Circle 3) is
not an axiom in `Certificate/axioms.lock`, and must not call it an assumption not in the
lock, or no longer an axiom.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """Circle 3 renamed in the lock and in a copy of facts.json alike, or in the copy's
    tables of proved rules once it has left the lock: the missing name is what must show
    that the check no longer refuses it. (While it is an axiom, III.2's [overlap] names the
    rule and is refused as well; the plant does not rely on that.)"""
    old, new = "Tacit.outside_of_between", "Tacit.Circle.outside_of_between"
    rel = "Certificate/axioms.lock"
    locked = f'"{old}" =' in (nt.ROOT / rel).read_text()
    saved = nt.replace_once(rel, f'"{old}" =', f'"{new}" =') if locked else None
    tables = ("axiom_types", "axiom_modules") if locked else ("proved_rules", "proved_rule_cites")

    def change(facts):
        for table in tables:
            facts[table][new] = facts[table].pop(old)
    try:
        nt.expect_failure("Circle 3 renamed in the lock and facts.json" if locked
                          else "Circle 3 renamed among facts.json's proved rules",
                          nt.with_facts(change),
                          f"{old} (Circle 3): not an axiom in {rel}",
                          unwanted=("an assumption not in", "no longer an axiom"))
    finally:
        if saved is not None:
            (nt.ROOT / rel).write_text(saved)
