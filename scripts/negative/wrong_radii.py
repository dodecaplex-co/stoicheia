"""The README's "Try breaking it": I.1 takes its radii from the wrong circle, its
`Definition15 hA_BCD hC_BCD hB_BCD` made `Definition15 hB_ACE hC_ACE hA_ACE` in
`Elements/BookI/Prop01.lean`, and Lean refuses the proof: `lake env lean` on the file must
fail with an error.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    rel = "Elements/BookI/Prop01.lean"
    saved = nt.replace_once(rel, "Definition15 hA_BCD hC_BCD hB_BCD", "Definition15 hB_ACE hC_ACE hA_ACE")
    try:
        nt.expect_failure("the README's wrong radii in I.1", nt.run("lake", "env", "lean", rel), "error")
    finally:
        (nt.ROOT / rel).write_text(saved)
