"""Counting congruence constructors instead of `Coincidence.step` in the certificate,
`Certificate/Facts.lean`: `tests/test_certificate.py` must fail on transformers with no
step. The restored certificate must pass the same regression, including its real-step
cases. Both runs are of `CommonNotion4Tests`, the class that compiles the C.N. 4 fixture
and holds the transformer cases, no step and real steps alike; the file's other classes
run in the check registry, on the certificate as committed.
"""

import sys

import negative_tests as nt

BUILDS = False

# The class of tests/test_certificate.py whose cases judge the constructor count.
CLASS = "CommonNotion4Tests"


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
            nt.run(sys.executable, "-I", "tests/test_certificate.py", CLASS),
            f"FAIL: test_transformers_without_step_do_not_count (__main__.{CLASS}",
            "AssertionError: Lists differ: ['C.N. 4'] != []",
        )
    finally:
        path.write_bytes(saved)
    nt.expect_success("the restored certificate regression",
                      nt.run(sys.executable, "-I", "tests/test_certificate.py", CLASS))
