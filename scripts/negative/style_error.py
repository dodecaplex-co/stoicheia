"""An em dash in I.1's mishnah, `mishnah/I/01.md`: `check_style.py` must fail with S1 and the
file's name.
"""

import sys

import negative_tests as nt

BUILDS = False


def plant() -> None:
    rel = "mishnah/I/01.md"
    path = nt.ROOT / rel
    saved = path.read_bytes()
    try:
        path.write_bytes(saved + ("\nA planted punctuation fault " + chr(0x2014)
                                  + " here.\n").encode())
        nt.expect_failure("an em dash in I.1's mishnah",
                          nt.run(sys.executable, "scripts/check_style.py"),
                          f"S1 {rel}:", "S1 an em dash")
    finally:
        path.write_bytes(saved)
