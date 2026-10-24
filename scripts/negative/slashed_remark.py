"""A remark written `/-/- … -/`, which Lean reads as one whole remark, planted in I.5
between the Lean of one sentence and the next sentence, and a plain remark after that
sentence, which leaves it with no Lean: the sentence is caught, and the one after the
second remark, which keeps its Lean, is not, nor is any passage of I.5's record said
to begin no sentence (#206). A reader that began the first remark's body at its third
character, as `_blank_remarks` did before the scripts shared one comment reader, took
its `/-/-` for two openings, read everything after it in the theorem as remark, missed
the sentence, and found three of the record's passages beginning no sentence.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """A remark written `/-/- … -/` in I.5, which Lean reads whole, before a sentence
    that a plain remark then leaves with no Lean: the sentence must be caught, and the
    sentence after the plain remark, which keeps its Lean, must not be, nor any passage of
    I.5's record said to begin no sentence. A reader that took the `/-/-` for two openings
    read the rest of the theorem as remark (#206)."""
    rel = "Elements/BookI/Prop05.lean"
    first = "and in these AB is equal to AC,"
    second = "the remainder BF is equal to the remainder CG."
    saved = nt.replace_once(rel, f"  -- {first}\n  -- {second}\n",
                            "  /-/- Planted by scripts/negative_tests.py: Lean ends this "
                            "remark here. -/\n"
                            f"  -- {first}\n"
                            "  /- Planted too: these words have no Lean. -/\n"
                            f"  -- {second}\n")
    try:
        planted = (nt.ROOT / rel).read_text()
        line = planted[:planted.index(f"-- {first}")].count("\n") + 1
        nt.expect_failure("a sentence with no Lean after a `/-/- … -/` remark in I.5", nt.fidelity(),
                          f"I.5: the `--` lines from {first!r} ({rel}:{line}) have no Lean",
                          unwanted=("I.5: the `--` lines from 'the remainder BF",
                                    "does not begin a sentence of the `--` lines of theorem Prop5"))
    finally:
        (nt.ROOT / rel).write_text(saved)
