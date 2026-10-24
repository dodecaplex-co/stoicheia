"""Counting congruence constructors instead of `Coincidence.step` in the certificate,
`Certificate/Facts.lean`: `tests/test_certificate.py` must fail on transformers with no
step. The restored certificate must pass the same regression, including its real-step
cases.
"""

import sys

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """Rebuilding constructors must not invent a coincidence step."""
    rel = "Certificate/Facts.lean"
    path = nt.ROOT / rel
    saved = path.read_bytes()
    try:
        nt.replace_once(
            rel, "used.contains coincidenceStep",
            "([`Elements.Superposition.Derives.len_congr,\n"
            "           `Elements.Superposition.Derives.angle_congr,\n"
            "           `Elements.Superposition.Derives.area_congr]).any used.contains",
        )
        nt.expect_failure(
            "constructor counting reports a step in a transformer",
            nt.run(sys.executable, "-I", "tests/test_certificate.py"),
            "FAIL: test_transformers_without_step_do_not_count",
            "AssertionError: Lists differ: ['C.N. 4'] != []",
        )
    finally:
        path.write_bytes(saved)
    nt.expect_success("the restored certificate regression",
                      nt.run(sys.executable, "-I", "tests/test_certificate.py"))
