"""Check that the pages and current documents give the repository's address as its home.

The repository moved to the organization dodecaplex-co on 27 October 2026, and its
address is `https://github.com/dodecaplex-co/stoicheia`. An address of a repository named
`stoicheia` on GitHub, in any of the forms GitHub serves (`github.com/<owner>/stoicheia`,
`git@github.com:<owner>/stoicheia`, `<owner>.github.io/stoicheia` and
`raw.githubusercontent.com/<owner>/stoicheia`), must name the owner `dodecaplex-co`,
written so. Every other owner is refused, the old address among them, so that the check
never needs to name it.

It reads every Markdown file and `CITATION.cff` that Git knows of, tracked or new but not
ignored: the generated pages and the documents read as current guidance. Code, fenced or
inline, is read too, since a command to copy is a place a reader takes the address from.
The dated records are passed over: the decision entries and the decisions page
(`docs/decisions/`, `docs/briefs/0002-decisions.md`), the briefs (`docs/briefs/`) and the
reports (`docs/reports/`). They were true when written, GitHub's redirect serves their
links, and an entry is never edited ([WORKFLOW, section 4](../docs/WORKFLOW.md),
"The repository's address"). How many addresses they hold that the check would refuse
elsewhere is printed, so a run shows that the exemption is what lets them pass.

    python3 scripts/check_address.py              every file in scope
    python3 scripts/check_address.py FILE ...     just these, if in scope
    python3 scripts/check_address.py --self-test  the cases below, then every file

Exits 1 if any address is refused, printing each as `file:line: what is wrong`; the owner
it names is not printed. Standard library only.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HOME = "dodecaplex-co"

# The dated records: folders, and their files, kept as they were written.
DATED = ("docs/decisions/", "docs/briefs/", "docs/reports/")
# Folders never searched when git cannot list the files.
SKIP_DIRS = {".git", ".lake", ".claude", "__pycache__", "node_modules"}

# An owner as GitHub allows it: letters, digits and single hyphens. The repository's name
# must end there: `stoicheia-tools` is another repository, and `stoicheia.git` this one.
OWNER = r"[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?"
NAME_END = r"(?![A-Za-z0-9_-])"
ADDRESS = re.compile(
    rf"(?:\bgithub\.com[/:]|\braw\.githubusercontent\.com/)(?P<a>{OWNER})/stoicheia{NAME_END}"
    rf"|(?<![A-Za-z0-9-])(?P<b>{OWNER})\.github\.io/stoicheia{NAME_END}",
    re.I)


def in_scope(name: str) -> bool:
    """Is the file, by its path from the root, a page or a current document?"""
    if name.startswith(DATED):
        return False
    return name.endswith(".md") or name == "CITATION.cff"


def problems(text: str) -> list[tuple[int, str]]:
    """(line, what is wrong) for every address in `text` that does not name the home."""
    found = []
    for number, line in enumerate(text.split("\n"), 1):
        for m in ADDRESS.finditer(line):
            owner = m.group("a") or m.group("b")
            if owner == HOME:
                continue
            what = ("names the home in other capitals" if owner.lower() == HOME
                    else "names an owner other than the repository's home")
            found.append((number, f"an address of this repository on GitHub {what}; "
                                  f"write github.com/{HOME}/stoicheia"))
    return found


def candidates() -> list[str]:
    """Every file Git knows of, tracked or new but not ignored, by its path from the root;
    without git, every file under ROOT outside SKIP_DIRS."""
    try:
        out = subprocess.run(["git", "ls-files", "-co", "--exclude-standard", "-z"],
                             cwd=ROOT, capture_output=True, check=True).stdout.decode()
        names = {f for f in out.split("\0") if f}
    except (OSError, subprocess.CalledProcessError):
        names = set()
        for d, dirs, files in os.walk(ROOT):
            dirs[:] = [x for x in dirs if x not in SKIP_DIRS]
            names |= {(Path(d) / f).relative_to(ROOT).as_posix() for f in files}
    return sorted(n for n in names if (ROOT / n).is_file())


def rel(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def self_test() -> list[str]:
    """Each case is (path, text, lines refused); a stand-in owner plays the old one."""
    other = "someone-else"
    cases = [
        ("book/I/01.md", f"[a commit](https://github.com/{other}/stoicheia/commit/abc)", [1]),
        ("README.md", f"```toml\ngit = \"https://github.com/{other}/stoicheia\"\n```", [2]),
        ("README.md", f"`require stoicheia from git \"https://github.com/{other}/stoicheia\"`", [1]),
        ("CITATION.cff", f'repository-code: "https://github.com/{other}/stoicheia"', [1]),
        ("docs/WORKFLOW.md", f"git@github.com:{other}/stoicheia.git", [1]),
        ("docs/STYLE.md", f"https://{other}.github.io/stoicheia/", [1]),
        ("docs/STYLE.md", f"https://raw.githubusercontent.com/{other}/stoicheia/main/x", [1]),
        ("docs/STYLE.md", f"http://www.github.com/{other}/Stoicheia", [1]),
        ("docs/STYLE.md", f"GitHub.com/{other}/stoicheia/issues/1", [1]),
        ("docs/STYLE.md", "https://github.com/Dodecaplex-Co/stoicheia", [1]),
        ("docs/STYLE.md", f"[x](https://github.com/{other}/stoicheia/issues/1) and "
                          f"[y](https://github.com/{other}/stoicheia/pull/2)", [1, 1]),
        ("docs/STYLE.md", "https://github.com/dodecaplex-co/stoicheia/issues/626", []),
        ("docs/STYLE.md", "git@github.com:dodecaplex-co/stoicheia.git", []),
        ("docs/STYLE.md", f"https://github.com/{other}/stoicheia-tools", []),
        ("docs/STYLE.md", "https://github.com/leanprover/lean4", []),
        ("docs/STYLE.md", f"https://example.com/{other}/stoicheia", []),
    ]
    faults = []
    for name, text, lines in cases:
        got = [n for n, _ in problems(text)]
        if got != lines:
            faults.append(f"self-test: {name}: {text!r}: refused lines {got}, expected {lines}")
    scope = [("book/III/37.md", True), ("CITATION.cff", True), ("mishnah/intro/I.md", True),
             ("tests/model/MODEL.md", True), ("docs/decisions/2026-10-21-file-names.md", False),
             ("docs/briefs/0002-decisions.md", False), ("docs/briefs/book-I.md", False),
             ("docs/reports/overlaps.md", False), ("scripts/render.py", False),
             ("review/I/01.toml", False)]
    for name, wanted in scope:
        if in_scope(name) != wanted:
            faults.append(f"self-test: {name}: in scope {not wanted}, expected {wanted}")
    count = len(cases) + len(scope)
    print(f"self-test: {count} cases" + (f", {len(faults)} wrong" if faults else " read rightly"))
    return faults


def main(argv: list[str]) -> int:
    faults = []
    if argv[:1] == ["--self-test"]:
        faults = self_test()
        argv = argv[1:]
    names = [rel(Path(a).resolve()) for a in argv] if argv else candidates()
    checked = refused = dated = dated_files = 0
    for name in names:
        try:
            text = (ROOT / name).read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        if not in_scope(name):
            if name.startswith(DATED) and name.endswith(".md"):
                n = len(problems(text))
                dated += n
                dated_files += 1 if n else 0
            continue
        checked += 1
        for number, what in problems(text):
            refused += 1
            print(f"{name}:{number}: {what}")
    for fault in faults:
        print(fault)
    note = (f"; the dated records, kept as written, hold {dated} other addresses "
            f"in {dated_files} files")
    if refused or faults:
        print(f"✗ address: {refused} refused in {checked} pages and documents{note}")
        return 1
    print(f"✓ address: every address of the repository in {checked} pages and documents "
          f"names github.com/{HOME}/stoicheia{note}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
