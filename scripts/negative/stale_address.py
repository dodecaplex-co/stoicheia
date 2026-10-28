"""An address of the repository on GitHub under an owner other than its home, dodecaplex-co,
planted three times: in a generated page, `book/I/01.md`, as a link to an issue; in
`CITATION.cff`, as its `repository-code`; and in `NOTICE`, as a bare `owner/stoicheia`.
`check_address.py` must fail each time, naming the file and line and saying the address
names an owner other than the repository's home.
A stand-in owner plays the old address, which the check refuses as it refuses any owner
but the home, and which no new file names.
"""

import sys

import negative_tests as nt

BUILDS = False

STAND_IN = "https://github.com/someone-else/stoicheia"
SAID = "names an owner other than the repository's home"


def plant() -> None:
    page = nt.ROOT / "book" / "I" / "01.md"
    saved = page.read_bytes()
    line = saved.count(b"\n") + 2
    try:
        page.write_bytes(saved + f"\n[An issue]({STAND_IN}/issues/1)\n".encode())
        nt.expect_failure("a generated page naming another owner's address",
                          nt.run(sys.executable, "scripts/check_address.py"),
                          f"book/I/01.md:{line}: an address of this repository on GitHub {SAID}")
    finally:
        page.write_bytes(saved)

    home = "https://github.com/dodecaplex-co/stoicheia"
    rel = "CITATION.cff"
    text = (nt.ROOT / rel).read_text(encoding="utf-8")
    number = text[:text.index(home)].count("\n") + 1
    saved = nt.replace_once(rel, home, STAND_IN)
    try:
        nt.expect_failure("CITATION.cff naming another owner's address",
                          nt.run(sys.executable, "scripts/check_address.py"),
                          f"CITATION.cff:{number}: an address of this repository on GitHub {SAID}")
    finally:
        (nt.ROOT / rel).write_text(saved, encoding="utf-8")

    notice = nt.ROOT / "NOTICE"
    saved = notice.read_bytes()
    line = saved.count(b"\n") + 2
    try:
        notice.write_bytes(saved + b"\nThe source: someone-else/stoicheia.\n")
        nt.expect_failure("NOTICE naming another owner's repository, bare",
                          nt.run(sys.executable, "scripts/check_address.py"),
                          f"NOTICE:{line}: an address of this repository on GitHub {SAID}")
    finally:
        notice.write_bytes(saved)
