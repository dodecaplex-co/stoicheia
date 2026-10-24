"""A repeated dated heading in the decisions page makes `check_queue.py --tree .`
refuse with exit 1.
"""

import sys

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """The tree scan must refuse a date heading repeated in the decisions page."""
    rel = "docs/briefs/0002-decisions.md"
    path = nt.ROOT / rel
    saved = path.read_bytes()
    heading = next(line for line in saved.splitlines() if line.startswith(b"## "))
    try:
        path.write_bytes(saved + b"\n" + heading + b"\n")
        result = nt.run(sys.executable, "scripts/check_queue.py", "--tree", ".")
        nt.expect_failure("a repeated dated heading in the decisions page", result,
                          rel, "repeated dated heading")
        if result.returncode != 1:
            nt.failures.append(f"queue repeated heading: expected exit 1, got {result.returncode}")
    finally:
        path.write_bytes(saved)
