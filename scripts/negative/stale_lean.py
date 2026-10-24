"""A changed Lean file makes its review record stale: a comment line planted at the end of
I.1's `Elements/BookI/Prop01.lean`, and `check_fidelity.py` must fail, saying that I.1's
Lean file has changed since it was reviewed.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    path = nt.ROOT / "Elements" / "BookI" / "Prop01.lean"
    saved = path.read_text()
    path.write_text(saved + "\n-- A line planted by scripts/negative_tests.py.\n")
    try:
        nt.expect_failure("a changed Lean file under a review record", nt.fidelity(),
                          "I.1: its Lean file has changed since it was reviewed")
    finally:
        path.write_text(saved)
