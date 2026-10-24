"""I.1's figure, idea figure and mishnah, each removed in turn: Book I is complete, so
`check_fidelity.py` must fail naming the missing file, "I.1: <file> is missing", and not
the other two. Each is restored byte for byte.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """I.1's figure, idea figure and mishnah, each taken away in turn: Book I is complete,
    so `check_fidelity.py` names the one missing, and not the other two."""
    rels = ("figures/I/01.svg", "figures/I/01-idea.svg", "mishnah/I/01.md")
    for rel in rels:
        path = nt.ROOT / rel
        saved = path.read_bytes()
        try:
            path.unlink()
            nt.expect_failure(f"I.1's {rel} missing from a complete book", nt.fidelity(),
                              f"I.1: {rel} is missing",
                              unwanted=tuple(f"I.1: {other} is missing" for other in rels
                                             if other != rel))
        finally:
            path.write_bytes(saved)
