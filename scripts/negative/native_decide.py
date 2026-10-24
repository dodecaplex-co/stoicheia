"""A `native_decide` in a proposition's file (I.16, `Elements/BookI/Prop16.lean`), in a planted
theorem, read from the source, is caught: `check_fidelity.py` must fail, naming the file and
line that use it.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    rel = "Elements/BookI/Prop16.lean"
    saved = nt.replace_once(rel, "\nend Elements.BookI", "\n/-- Planted by scripts/negative_tests.py. "
                            "-/\ntheorem planted_native : 2 + 2 = 4 := by native_decide\n\n"
                            "end Elements.BookI")
    try:
        text = (nt.ROOT / rel).read_text()
        line = text[:text.index("by native_decide")].count("\n") + 1
        nt.expect_failure("a native_decide in I.16's file", nt.fidelity(),
                          f"{rel}:{line}: uses native_decide")
    finally:
        (nt.ROOT / rel).write_text(saved)
