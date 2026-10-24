"""A remark planted in I.5 (`Elements/BookI/Prop05.lean`) between two sentences that share one
step of Lean leaves the first with no Lean of its own: a remark ends a run and carries
nothing. `check_fidelity.py` must fail, saying that the `--` lines from "and in these AB is
equal to AC," have no Lean, with their file and line. A second remark, between the next
sentence and its Lean, does not stop that Lean carrying it: the lines from "the remainder
BF" must not be named.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """A remark between two sentences of I.5 that share one step of Lean. The first
    sentence then has no Lean before the next run of `--` lines, and must be caught; the
    second keeps its Lean, beneath a remark of its own, and must not be."""
    rel = "Elements/BookI/Prop05.lean"
    first = "and in these AB is equal to AC,"
    second = "the remainder BF is equal to the remainder CG."
    saved = nt.replace_once(rel, f"  -- {first}\n  -- {second}\n",
                            f"  -- {first}\n"
                            "  /- Planted by scripts/negative_tests.py: these words have no Lean. -/\n"
                            f"  -- {second}\n"
                            "  /- Planted too: a remark between a sentence and its Lean. -/\n")
    line = saved[:saved.index(f"-- {first}")].count("\n") + 1
    try:
        nt.expect_failure("a sentence with no Lean before a remark in I.5", nt.fidelity(),
                          f"I.5: the `--` lines from {first!r} ({rel}:{line}) have no Lean",
                          unwanted=("I.5: the `--` lines from 'the remainder BF",))
    finally:
        (nt.ROOT / rel).write_text(saved)
