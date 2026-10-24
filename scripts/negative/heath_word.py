"""An edited Heath word in I.1: "With centre A and distance AB", in `heath/I/01.md`, made
"radius". `check_fidelity.py` must fail on I.1, saying that its `--` comments don't match
Heath's proof.
"""

import negative_tests as nt

BUILDS = False


def plant() -> None:
    rel = "heath/I/01.md"
    saved = nt.replace_once(rel, "With centre A and distance AB", "With centre A and radius AB")
    try:
        nt.expect_failure("an edited Heath word", nt.fidelity(),
                          "I.1: the `--` comments don't match Heath's proof")
    finally:
        (nt.ROOT / rel).write_text(saved)
