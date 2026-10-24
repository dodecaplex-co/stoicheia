"""A lemma of the `Placement` namespace named in Book III's shared steps (`Squares.lean`),
outside placement's own files, III.24's and `Arcs.lean`, read from the source, is caught:
`check_fidelity.py` must say that its line names `Placement`. The word in a comment on the
line before cites nothing, and must not be caught.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """A lemma of the `Placement` namespace named in Squares.lean, Book III's shared steps,
    read from the source: caught on its line. The word in a comment on the line before
    cites nothing, and is not caught."""
    rel = "Elements/BookIII/Squares.lean"
    marker = "\nend Elements\n"
    saved = nt.replace_once(rel, marker,
                            "\n-- The word placement, in a comment, cites nothing.\n"
                            "/-- Planted by scripts/negative_tests.py. -/\n"
                            "theorem planted_placement : True := (fun _ => trivial) @Placement.dist\n"
                            + marker)
    before = saved[:saved.index(marker)].count("\n") + 1
    try:
        nt.expect_failure("a lemma of placement named in Squares.lean", nt.fidelity(),
                          f"{rel}:{before + 3}: names `Placement`",
                          unwanted=(f"{rel}:{before + 1}:",))
    finally:
        (nt.ROOT / rel).write_text(saved)
