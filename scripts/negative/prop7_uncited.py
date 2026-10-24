"""I.7's law, `.prop7`, removed from `Prop8.cites`, with the arm of I.8's case split that
proves it: Lean refuses I.8's file, as `lake build` would, at the derivation's citation of
the law (`Derives.prop7`), whose `by decide` finds `Cited.prop7 ∈ cites` false. The build
catches it, before the certificate runs; the expectation on I.8's `cited_laws` is not
reached.
"""

import negative_tests as nt

BUILDS = False

# I.7's law taken out of I.8's list, with the arm of its case split that proves it, and the
# derivation's citation of the law, where Lean must refuse it.
PROP7_PLANT = (
    ("abbrev cites : List Cited := [.lenSymm, .neOfLen, .rayUnique, .prop7]\n",
     "abbrev cites : List Cited := [.lenSymm, .neOfLen, .rayUnique]\n"),
    ("    rcases hc with rfl | rfl | rfl | rfl\n", "    rcases hc with rfl | rfl | rfl\n"),
    ("    · exact Prop8.holds_prop7\n", ""),
)
PROP7_CITED = "    .prop7 Guard.ne_DG Guard.on_D Guard.on_G hGD_side hGE_DE hGF_DF\n"


def plant() -> None:
    """`.prop7` removed from `Prop8.cites`, and the arm of I.8's case split that proves
    I.7's law with it, so that nothing else fails: Lean refuses I.8's file, as `lake build`
    would, at the derivation's citation of the law (`Derives.prop7`), whose `by decide`
    finds `Cited.prop7 ∈ cites` false. The build catches it, before the certificate runs,
    so the expectation on I.8's `cited_laws` is not what catches it (#150)."""
    rel = "Elements/BookI/Prop08.lean"
    path = nt.ROOT / rel
    saved = path.read_text()
    planted = saved
    for old, new in PROP7_PLANT:
        assert planted.count(old) == 1, f"{rel}: expected one {old!r}"
        planted = planted.replace(old, new)
    assert planted.count(PROP7_CITED) == 1, f"{rel}: expected one citation of I.7's law"
    line = planted[:planted.index(PROP7_CITED)].count("\n") + 1
    try:
        path.write_text(planted)
        nt.expect_failure("`.prop7` removed from I.8's cited laws",
                          nt.run("lake", "env", "lean", rel),
                          f"{rel}:{line}:", "Cited.prop7 ∈ cites", "is false")
    finally:
        path.write_text(saved)
