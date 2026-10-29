"""Check that the pages and documents in scope give the repository's address as its home.

The repository moved to the organization dodecaplex-co on 27 October 2026, and its
address is `https://github.com/dodecaplex-co/stoicheia`. An address of a repository named
`stoicheia` on GitHub, in any of the forms GitHub serves (`github.com/<owner>/stoicheia`,
with or without `www.` and a port, `git@github.com:<owner>/stoicheia`,
`<owner>.github.io/stoicheia`, `raw.githubusercontent.com/<owner>/stoicheia`,
`codeload.github.com/<owner>/stoicheia` and `api.github.com/repos/<owner>/stoicheia`), or
as the bare `<owner>/stoicheia` that `gh` and the citation read and the bare
`repos/<owner>/stoicheia` that `gh api` reads, must name the owner `dodecaplex-co`,
written so. Every other owner is refused, the old address among them, so that the check
never needs to name it. A bare `<owner>/stoicheia` is read as a local path, and passed
over, when a letter, digit, `.`, `/`, `~`, `_` or `-` stands just before it
(`.git/stoicheia`, `~/.cache/stoicheia`); so a path is written from `./` or `~/`. It is
passed over too when an `@` stands just before it (an npm scope, `@<owner>/stoicheia`),
or when it stands in another site's address after that address's `?` or `#`. The name
must end there: `stoicheia.git`, `stoicheia.wiki` and `stoicheia.wiki.git` are this
repository, and `stoicheia-tools` or `stoicheia.notes` another; and the host must be
GitHub's own (`not-github.com` is not).

It reads every Markdown file Git knows of, tracked or new but not ignored, and the root's
`CITATION.cff`, `LICENSE` and `NOTICE`. Code, fenced or inline, is read too, since a
command to copy is a place a reader takes the address from; code and configuration files
(`.py`, `.yml`, `.toml`, `.json`, `.lean`) are not read. Three folders are exempt. The
decision entries and the decisions page (`docs/decisions/`, `docs/briefs/0002-decisions.md`)
and the reports (`docs/reports/`) are dated records, kept as written: they were true when
written, GitHub's redirect serves their links, and an entry is never edited. The briefs
(`docs/briefs/`) are exempt as a whole, the current book briefs among them (`book-I.md`,
`book-II.md`, `0004-book-III.md`, `0012-book-IV.md`), which keep their links until their
briefs are next revised ([WORKFLOW, section 4](../docs/WORKFLOW.md), "The repository's
address"). The check refuses nothing in the exempt folders, so an old address added there
passes; it prints how many addresses their Markdown files hold that it would refuse
elsewhere, so a run shows that the exemption is what lets them pass.

    python3 scripts/check_address.py              every file in scope
    python3 scripts/check_address.py FILE ...     just these, judged if in scope
    python3 scripts/check_address.py --self-test  the cases below, then every file

Exits 1 if any address is refused, printing each as `file:line: what is wrong`, with what
to write for the form found; the owner it names is not printed. A file in scope, or a
named file outside the exempt folders, that cannot be read or decoded as UTF-8 is refused
too, as `file: cannot be read (why)`. Exits 2, with a usage line, on an argument beginning
`--` other than `--self-test`. Standard library only.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HOME = "dodecaplex-co"

# The exempt folders: the dated records, kept as they were written, and the briefs.
DATED = ("docs/decisions/", "docs/briefs/", "docs/reports/")
# Folders never searched when git cannot list the files.
SKIP_DIRS = {".git", ".lake", ".claude", "__pycache__", "node_modules"}

# The documents at the root that are neither Markdown nor in a folder.
ROOT_DOCUMENTS = ("CITATION.cff", "LICENSE", "NOTICE")

# An owner in the check's fixed syntax: letters, digits and hyphens, with a letter or digit
# at each end. The repository's name must end there, with or without `.wiki` and `.git`:
# a `.`, `_`, `-`, letter or digit
# after it makes another name (`stoicheia.notes`, `stoicheia-tools`), but a full stop
# ending a sentence does not. A host must stand alone (`not-github.com` is not GitHub), and
# a bare `<owner>/stoicheia` or `repos/<owner>/stoicheia` must not continue a path
# (`.git/stoicheia`, `~/.cache/stoicheia`, `~/repos/<owner>/stoicheia`), follow an `@` (an
# npm scope) or stand in another site's address after its `?` or `#` (URL, read by
# in_url_query_or_fragment). The groups a and b
# are addresses with a host, c and d bare ones.
OWNER = r"[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?"
NAME_END = r"(?:\.wiki)?(?:\.git)?(?![A-Za-z0-9_-])(?!\.[A-Za-z0-9_-])"
HOST = r"(?<![A-Za-z0-9._-])"
BARE = r"(?<![A-Za-z0-9@._/~-])"
PORT = r"(?::\d+)?"
ADDRESS = re.compile(
    rf"{HOST}(?:(?:www\.)?github\.com{PORT}[/:]|api\.github\.com{PORT}/repos/"
    rf"|codeload\.github\.com{PORT}/|raw\.githubusercontent\.com{PORT}/)"
    rf"(?P<a>{OWNER})/stoicheia{NAME_END}"
    rf"|{HOST}(?P<b>{OWNER})\.github\.io{PORT}/stoicheia{NAME_END}"
    rf"|{BARE}repos/(?P<d>{OWNER})/stoicheia{NAME_END}"
    rf"|{BARE}(?P<c>{OWNER})/stoicheia{NAME_END}",
    re.I)
URL = re.compile(
    r"(?:(?<![A-Za-z0-9+.-])[A-Za-z][A-Za-z0-9+.-]*:|"
    r"(?<![A-Za-z0-9_+./:-]))//[^\s<>()\[\]{}\"']+", re.I)
GITHUB_URL = re.compile(
    rf"^(?:[A-Za-z][A-Za-z0-9+.-]*:)?//(?:[^/?#@]*@)?"
    rf"(?:(?:www\.)?github\.com|api\.github\.com|codeload\.github\.com"
    rf"|raw\.githubusercontent\.com|{OWNER}\.github\.io){PORT}(?:[/?#]|$)", re.I)
# What to write instead, by the form found: with a host, or bare (where a local path the
# check reads as bare is written from `./` or `~/`).
WRITE_HOSTED = f"write github.com/{HOME}/stoicheia"
WRITE_BARE = f"write {HOME}/stoicheia, or a local path from ./ or ~/"

USAGE = "usage: check_address.py [--self-test] [FILE ...]"


def in_scope(name: str) -> bool:
    """Is the file, by its path from the root, one the check judges: Markdown, or a root
    document, outside the exempt folders?"""
    if name.startswith(DATED):
        return False
    return name.endswith(".md") or name in ROOT_DOCUMENTS


def problems(text: str) -> list[tuple[int, str]]:
    """(line, what is wrong) for every address in `text` that does not name the home."""
    found = []
    for number, line in enumerate(text.split("\n"), 1):
        for m in ADDRESS.finditer(line):
            if (m.group("c") or m.group("d")) and in_url_query_or_fragment(line, m.start()):
                continue
            owner = m.group("a") or m.group("b") or m.group("c") or m.group("d")
            if owner == HOME:
                continue
            what = ("names the home in other capitals" if owner.lower() == HOME
                    else "names an owner other than the repository's home")
            write = WRITE_HOSTED if m.group("a") or m.group("b") else WRITE_BARE
            found.append((number,
                          f"an address of this repository on GitHub {what}; {write}"))
    return found


def in_url_query_or_fragment(line: str, offset: int) -> bool:
    for match in URL.finditer(line):
        if not match.start() <= offset < match.end():
            continue
        address = match.group()
        if GITHUB_URL.match(address):
            return False
        starts = [i for mark in "?#" if (i := address.find(mark)) >= 0]
        return bool(starts) and offset > match.start() + min(starts)
    return False


def options(argv: list[str]) -> tuple[bool, list[str], list[str]]:
    """(the self-test asked for, the files named, the options not known) in `argv`."""
    unknown = [a for a in argv if a.startswith("--") and a != "--self-test"]
    files = [a for a in argv if not a.startswith("--")]
    return "--self-test" in argv, files, unknown


def read(path: Path) -> tuple[str | None, str]:
    """(the file's text, "") or (None, why it cannot be read or decoded as UTF-8)."""
    try:
        return decoded(path.read_bytes())
    except OSError as error:
        return None, error.strerror or type(error).__name__


def decoded(data: bytes) -> tuple[str | None, str]:
    """(the text, "") or (None, where the bytes are not UTF-8)."""
    try:
        return data.decode("utf-8"), ""
    except UnicodeDecodeError as error:
        return None, f"not UTF-8 at byte {error.start}"


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
    """Each case is (path, text, lines refused); a stand-in owner plays the old one. Then
    the advice given for each form, the files in scope, the options, and the reading."""
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
        ("docs/STYLE.md", f"https://github.com:443/{other}/stoicheia", [1]),
        ("docs/STYLE.md", f"https://api.github.com:443/repos/{other}/stoicheia", [1]),
        ("docs/STYLE.md", f"https://codeload.github.com:443/{other}/stoicheia/zip/main", [1]),
        ("docs/STYLE.md", f"https://raw.githubusercontent.com:443/{other}/stoicheia/main/x", [1]),
        ("docs/STYLE.md", f"https://{other}.github.io:443/stoicheia/", [1]),
        ("docs/STYLE.md", f"https://user@github.com/{other}/stoicheia.git", [1]),
        ("docs/STYLE.md", f"See github.com/{other}/stoicheia.", [1]),
        ("docs/STYLE.md", f"`gh repo clone {other}/stoicheia`", [1]),
        ("docs/STYLE.md", f"the repository {other}/stoicheia, cited", [1]),
        ("NOTICE", f"({other}/stoicheia)", [1]),
        ("docs/STYLE.md", "`gh repo clone dodecaplex-co/stoicheia`", []),
        ("docs/STYLE.md", f"https://github.com/{other}/stoicheia.notes", []),
        ("docs/STYLE.md", f"https://not-github.com/{other}/stoicheia", []),
        ("docs/STYLE.md", f"https://not_github.com/{other}/stoicheia", []),
        ("docs/STYLE.md", f"https://gist.github.com/{other}/stoicheia", []),
        ("docs/STYLE.md", "copied to `.git/stoicheia/safe-push`", []),
        ("docs/STYLE.md", "`~/.cache/stoicheia/harness/` and `~/.venvs/stoicheia/bin`", []),
        ("docs/STYLE.md", "`~/dev/stoicheia` and `./dev/stoicheia`", []),
        ("README.md", '<img src="assets/stoicheia-social.png">', []),
        ("docs/STYLE.md", f"https://api.github.com/repos/{other}/stoicheia/releases", [1]),
        ("docs/STYLE.md", f"https://codeload.github.com/{other}/stoicheia/zip/main", [1]),
        ("docs/STYLE.md", f"`gh api repos/{other}/stoicheia/pulls`", [1]),
        ("docs/STYLE.md", f"https://github.com/{other}/stoicheia.wiki", [1]),
        ("docs/STYLE.md", f"git clone https://github.com/{other}/stoicheia.wiki.git", [1]),
        ("docs/STYLE.md", "https://api.github.com/repos/dodecaplex-co/stoicheia", []),
        ("docs/STYLE.md", "https://codeload.github.com/dodecaplex-co/stoicheia/zip/main", []),
        ("docs/STYLE.md", "`gh api repos/dodecaplex-co/stoicheia/pulls`", []),
        ("docs/STYLE.md", "https://github.com/dodecaplex-co/stoicheia.wiki.git", []),
        ("docs/STYLE.md", f"https://github.com/{other}/stoicheia.wikis", []),
        ("docs/STYLE.md", f"`~/repos/{other}/stoicheia`, `./repos/{other}/stoicheia`", []),
        ("docs/STYLE.md", f"https://api.github.com/{other}/stoicheia", []),
        ("docs/STYLE.md", f"@{other}/stoicheia", []),
        ("docs/STYLE.md", f"https://example.com/?repo={other}/stoicheia", []),
        ("docs/STYLE.md", f"https://example.com/#repo={other}/stoicheia", []),
        ("docs/STYLE.md", f"https://example.com/?repo=repos/{other}/stoicheia", []),
        ("docs/STYLE.md", f"https://github.com/search?q={other}/stoicheia", [1]),
        ("docs/STYLE.md", f"https://github.com/search#repo={other}/stoicheia", [1]),
        ("docs/STYLE.md", f"https://github.com/search?q=repos/{other}/stoicheia", [1]),
        ("docs/STYLE.md", f"https://github.com/search#repo=repos/{other}/stoicheia", [1]),
        ("docs/STYLE.md", f"https://example.com/?repo={other}/stoicheia and "
                          f"{other}/stoicheia", [1]),
        ("docs/STYLE.md", f"https://example.com/?repo=https://github.com/{other}/stoicheia", [1]),
        ("docs/STYLE.md", "https://api.github.com:443/repos/dodecaplex-co/stoicheia", []),
        ("docs/STYLE.md", "https://dodecaplex-co.github.io:443/stoicheia", []),
        ("docs/STYLE.md", f"//example.com/?repo={other}/stoicheia", []),
        ("docs/STYLE.md", f"//example.com/#repo={other}/stoicheia", []),
        ("docs/STYLE.md", f"//example.com/?repo={other}/stoicheia and "
                          f"https://github.com/{other}/stoicheia", [1]),
        ("docs/STYLE.md", f"//github.com/{other}/stoicheia", [1]),
        ("docs/STYLE.md", f"mailto:{other}/stoicheia@example.com", [1]),
        ("docs/STYLE.md", f"mailto:{other}/stoicheia.git@example.com", [1]),
        ("docs/STYLE.md", f"mailto:{other}/stoicheia.wiki.git@example.com", [1]),
        ("docs/STYLE.md", f"{other}/stoicheia", [1]),
        ("docs/STYLE.md", f"{other}/stoicheia.wiki.git", [1]),
        ("docs/STYLE.md", f"{other}/stoicheia@abc1234", [1]),
        ("docs/STYLE.md", f"uses: {other}/stoicheia@main", [1]),
        ("docs/STYLE.md", f"https://github.com/{other}/stoicheia@example.com", [1]),
    ]
    faults = []
    for name, text, lines in cases:
        got = [n for n, _ in problems(text)]
        if got != lines:
            faults.append(f"self-test: {name}: {text!r}: refused lines {got}, expected {lines}")
    hosted, bare = WRITE_HOSTED, WRITE_BARE
    advice = [(f"https://github.com/{other}/stoicheia", hosted),
              (f"git@github.com:{other}/stoicheia.git", hosted),
              (f"https://{other}.github.io/stoicheia/", hosted),
              (f"https://{other}.github.io:443/stoicheia/", hosted),
              (f"https://api.github.com/repos/{other}/stoicheia", hosted),
              (f"https://raw.githubusercontent.com:443/{other}/stoicheia/main/x", hosted),
              (f"`gh repo clone {other}/stoicheia`", bare),
              (f"`gh api repos/{other}/stoicheia`", bare),
              ("`dev/stoicheia`, a local path read as bare", bare)]
    for text, wanted in advice:
        got = [what for _, what in problems(text)]
        if len(got) != 1 or not got[0].endswith(f"; {wanted}"):
            faults.append(f"self-test: {text!r}: advised {got}, expected {wanted!r}")
    scope = [("book/III/37.md", True), ("CITATION.cff", True), ("mishnah/intro/I.md", True),
             ("tests/model/MODEL.md", True), ("LICENSE", True), ("NOTICE", True),
             ("LICENSE-PROSE.md", True), ("docs/decisions/2026-10-21-file-names.md", False),
             ("docs/briefs/0002-decisions.md", False), ("docs/briefs/book-I.md", False),
             ("docs/reports/overlaps.md", False), ("scripts/render.py", False),
             ("review/I/01.toml", False), ("docs/briefs/book-II.md", False),
             ("docs/briefs/0004-book-III.md", False), ("docs/briefs/0012-book-IV.md", False),
             ("docs/decisions/2026-10-28-repository-address.md", False)]
    for name, wanted in scope:
        if in_scope(name) != wanted:
            faults.append(f"self-test: {name}: in scope {not wanted}, expected {wanted}")
    # (arguments, the options refused): only --self-test is known, written in full.
    argued = [(["--self-tset"], ["--self-tset"]), (["--self"], ["--self"]),
              (["--self-test", "README.md"], []), (["README.md", "--self-test"], []),
              (["--", "README.md"], ["--"]), (["NOTICE"], [])]
    for argv, wanted in argued:
        if options(argv)[2] != wanted:
            faults.append(f"self-test: options {argv}: refused {options(argv)[2]}, "
                          f"expected {wanted}")
    # (what is read, whether it can be): a path through a file, which no file can have,
    # bytes that are not UTF-8 (a Latin-1 é, a lone continuation byte), and bytes that are.
    reading = [(read(Path(__file__).resolve() / "none"), False),
               (decoded(b"caf\xe9"), False), (decoded(b"\x80"), False),
               (decoded("café".encode()), True)]
    for number, ((text, why), wanted) in enumerate(reading, 1):
        if (text is not None) != wanted or bool(why) == wanted:
            faults.append(f"self-test: reading case {number}: read {text is not None} "
                          f"({why}), expected {wanted}")
    made = []
    commands = []
    try:
        for folder, data in [(ROOT / "docs/briefs", b"\x80"),
                             (ROOT, b"\x80"),
                             (ROOT / "docs/briefs",
                              f"https://github.com/{other}/stoicheia\n".encode())]:
            with tempfile.NamedTemporaryFile(dir=folder, suffix=".md", delete=False) as file:
                file.write(data)
                made.append(Path(file.name))
        missing_exempt = made[0].with_name(made[0].stem + "-missing.md")
        missing_scoped = made[1].with_name(made[1].stem + "-missing.md")
        commands = [
            ([missing_exempt], 0, "✓ address", "cannot be read"),
            ([made[0]], 0, "✓ address", "cannot be read"),
            ([made[2]], 0, "hold 1 other addresses in 1 files", "cannot be read"),
            ([missing_scoped], 1, "cannot be read", "✓ address"),
            ([made[1]], 1, "cannot be read (not UTF-8", "✓ address"),
        ]
        for arguments, wanted_status, wanted, unwanted in commands:
            result = subprocess.run([sys.executable, str(Path(__file__).resolve()),
                                     *(str(path) for path in arguments)],
                                    cwd=ROOT, capture_output=True, text=True)
            if (result.returncode != wanted_status or wanted not in result.stdout
                    or unwanted in result.stdout):
                faults.append(f"self-test: command {arguments}: status {result.returncode}, "
                              f"output {result.stdout!r}; expected {wanted_status}, {wanted!r}")
    finally:
        for path in made:
            path.unlink(missing_ok=True)
    count = (len(cases) + len(advice) + len(scope) + len(argued) + len(reading)
             + len(commands))
    print(f"self-test: {count} cases" + (f", {len(faults)} wrong" if faults else " read rightly"))
    return faults


def main(argv: list[str]) -> int:
    testing, files, unknown = options(argv)
    if unknown:
        print(USAGE, file=sys.stderr)
        print(f"check_address.py: error: unrecognised arguments: {' '.join(unknown)}",
              file=sys.stderr)
        return 2
    faults = self_test() if testing else []
    names = [rel(Path(a).resolve()) for a in files] if files else candidates()
    checked = refused = dated = dated_files = 0
    for name in names:
        # A file named is read whatever its scope; of the rest, only the files in scope and
        # the exempt folders' Markdown, which is counted.
        exempt = name.startswith(DATED)
        scoped, counted = in_scope(name), exempt and name.endswith(".md")
        if not (files or scoped or counted):
            continue
        checked += 1 if scoped else 0
        text, why = read(ROOT / name)
        if text is None:
            if scoped or (files and not exempt):
                refused += 1
                print(f"{name}: cannot be read ({why})")
            continue
        if not scoped:
            if counted:
                n = len(problems(text))
                dated += n
                dated_files += 1 if n else 0
            continue
        for number, what in problems(text):
            refused += 1
            print(f"{name}:{number}: {what}")
    for fault in faults:
        print(fault)
    note = (f"; the exempt folders, the dated records and the briefs, hold {dated} other "
            f"addresses in {dated_files} files")
    if refused or faults:
        failed = "self-test failed; " if faults else ""
        print(f"✗ address: {failed}{refused} refused in {checked} pages and documents{note}")
        return 1
    print(f"✓ address: every address of the repository in {checked} pages and documents "
          f"names github.com/{HOME}/stoicheia{note}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
