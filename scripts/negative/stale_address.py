"""An address of the repository on GitHub under an owner other than its home, dodecaplex-co,
planted three times: in a generated page, `book/I/01.md`, as a link to an issue; in
`CITATION.cff`, as its `repository-code`; and in `NOTICE`, as a bare `owner/stoicheia`.
`check_address.py` must fail each time, naming the file and line, saying the address
names an owner other than the repository's home, and saying what to write for the form
found: `github.com/dodecaplex-co/stoicheia` for the two web addresses,
`dodecaplex-co/stoicheia` for the bare one. Then a byte that is not UTF-8 (a Latin-1 é)
is planted in `NOTICE`, and the check must fail saying `NOTICE: cannot be read`.
A stand-in owner plays the old address, which the check refuses as it refuses any owner
but the home, and which no new file names.
"""

import sys

import negative_tests as nt

BUILDS = False

OWNER = "someone-else"
STAND_IN = f"https://github.com/{OWNER}/stoicheia"
STAND_IN_BARE = f"{OWNER}/stoicheia"
HOME = "https://github.com/dodecaplex-co/stoicheia"
SAID = ("an address of this repository on GitHub names an owner other than the "
        "repository's home")
WRITE_HOSTED = "write github.com/dodecaplex-co/stoicheia"
WRITE_BARE = "write dodecaplex-co/stoicheia, or a local path from ./ or ~/"


def plant() -> None:
    page = nt.ROOT / "book" / "I" / "01.md"
    saved = page.read_bytes()
    line = saved.count(b"\n") + 2
    try:
        page.write_bytes(saved + f"\n[An issue]({STAND_IN}/issues/1)\n".encode())
        nt.expect_failure("a generated page naming another owner's address",
                          nt.run(sys.executable, "scripts/check_address.py"),
                          f"book/I/01.md:{line}: {SAID}; {WRITE_HOSTED}")
    finally:
        page.write_bytes(saved)

    rel = "CITATION.cff"
    text = (nt.ROOT / rel).read_text(encoding="utf-8")
    number = text[:text.index(HOME)].count("\n") + 1
    saved = nt.replace_once(rel, HOME, STAND_IN)
    try:
        nt.expect_failure("CITATION.cff naming another owner's address",
                          nt.run(sys.executable, "scripts/check_address.py"),
                          f"CITATION.cff:{number}: {SAID}; {WRITE_HOSTED}")
    finally:
        (nt.ROOT / rel).write_text(saved, encoding="utf-8")

    notice = nt.ROOT / "NOTICE"
    saved = notice.read_bytes()
    line = saved.count(b"\n") + 2
    try:
        notice.write_bytes(saved + f"\nThe source: {STAND_IN_BARE}.\n".encode())
        nt.expect_failure("NOTICE naming another owner's repository, bare",
                          nt.run(sys.executable, "scripts/check_address.py"),
                          f"NOTICE:{line}: {SAID}; {WRITE_BARE}")
    finally:
        notice.write_bytes(saved)

    try:
        notice.write_bytes(saved + b"\nCaf\xe9.\n")
        nt.expect_failure("NOTICE that cannot be decoded as UTF-8",
                          nt.run(sys.executable, "scripts/check_address.py"),
                          "NOTICE: cannot be read (not UTF-8 at byte")
    finally:
        notice.write_bytes(saved)
