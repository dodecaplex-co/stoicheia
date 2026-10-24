"""A relative link to a missing file, `book/I/planted-missing-page.md`, added to README.md:
`check_links.py` must fail, naming the link with its source file and line, and saying that
there is no such file.
"""

import sys

import negative_tests as nt

BUILDS = False


def plant() -> None:
    path = nt.ROOT / "README.md"
    target = "book/I/planted-missing-page.md"
    assert not (nt.ROOT / target).exists(), f"{target} exists; update this test"
    saved = path.read_bytes()
    line = saved.count(b"\n") + 2
    try:
        path.write_bytes(saved + f"\n[Planted missing page]({target})\n".encode())
        nt.expect_failure("a relative link to a missing page",
                          nt.run(sys.executable, "scripts/check_links.py"),
                          f"README.md:{line}: {target}: no such file: {target}")
    finally:
        path.write_bytes(saved)
