"""Check every tracked path against the standard for file names, types and modes.

The owner asked, on 21 October 2026, "Can we standardize the file names and types so we
don't have silliness with messy paths?" WORKFLOW.md, section 4, "File names", states the
standard in words; its lists live here, each a named constant, so that a change to the
standard is a visible change of one line. The script reads Git's index
(`git ls-files -s -z`, which honours GIT_INDEX_FILE): what is staged for the next commit,
which in CI and in safe_push's fresh worktree is the commit itself, and never the working
tree; it never opens or follows a file. Each finding names the path, the rule and the
reason.

P1. Characters. ASCII letters, digits, ".", "_", "-" and "/" only; no empty segment, no
    "." or ".." segment, and no segment that begins or ends with "." or "-", save
    `.github` as the first segment and `.gitignore` and `.gitkeep` as a file's name. At
    most 160 characters in all and 100 in a segment. No segment whose stem, in any case,
    is a Windows device name (CON, PRN, AUX, NUL, COM0 to COM9, LPT0 to LPT9).
P2. No case twins. No two paths, and no two of their folders, alike once Unicode NFC
    normalisation and case folding are applied: a disk that ignores case, as macOS's does
    by default, checks the two out as one, so `Scripts/json.py` beside `scripts/heath.py`
    is a twin of the folder `scripts`. Nor one path or folder listed twice, as a tree made
    by hand (`git mktree`) can list it, and `--rev` reads it.
P3. Extensions. In lower case, from EXTENSIONS; a file without one only at a path of
    EXTENSIONLESS.
P4. Types by folder. The top-level folders of TOP_FOLDERS; at the root, the files of
    ROOT_FILES and Markdown named in capitals, words joined by single hyphens; in each
    folder the types of FOLDER_TYPES, and the files of FOLDER_FILES and DOT_FILES at their
    own paths.
P5. Names where they are mechanical. A book's pages, texts, mishnah, reading lines, review
    records and figures are named by its Roman numeral and the proposition's number
    (NAMES); a brief by four digits and a slug, or as a book's brief; a Lean file of the
    edition's libraries by Lean module names, with BookR and PropNN under Elements/, save
    the model's laws, directly in LAW_FOLDER, which keep the model's lower-case names
    (LAW_STEM); no lakefile.lean anywhere; a Python file so that it can be imported.
P6. Modes. A file is 100644, or 100755 exactly when it is one of EXECUTABLES: no
    symbolic link (120000) and no submodule (160000).

A new book's paths already fit: Book IV's, and Book X's 115 propositions. A new extension,
top-level folder, executable or named file is a change to the lists here, so to a
protected path, and lands first, in a pull request of its own.

    python3 scripts/check_paths.py                  the index
    python3 scripts/check_paths.py --rev <commit>   a commit's tree instead, for a reviewer
    python3 scripts/check_paths.py --self-test      planted cases first, then the index
    python3 -I tests/test_check_paths.py            the rules' cases, which CI runs first

The self-test plants a fault of each rule in memory, beside good paths (Book IV's and
Book X's among them), and fails if a fault passes or a good path is refused. Exits 1 on
any finding. Standard library only; Python 3.11 or later. A module planted beside the
script (scripts/unicodedata.py, say) is never read in its place.
"""

import os
import sys

# Run as `python3 scripts/check_paths.py`, Python puts the script's own folder first on
# sys.path, so a module planted there would stand in for the standard library's and could
# pass any tree. sys is built in, and site has loaded os before any script runs, so
# neither is read from the folder; it is taken off before any other import. For the same
# reason there is no `from __future__` import: it is an import like any other, and would
# read a planted scripts/__future__.py first. A script that imports this one keeps its own
# sys.path.
if __name__ == "__main__":
    sys.path[:] = [p for p in sys.path if os.path.realpath(p or os.curdir)
                   != os.path.dirname(os.path.realpath(__file__))]

import argparse  # noqa: E402
import keyword  # noqa: E402
import re  # noqa: E402
import subprocess  # noqa: E402
import unicodedata  # noqa: E402
from collections import Counter, defaultdict  # noqa: E402
from pathlib import Path  # noqa: E402

SCRIPT = Path(__file__).resolve()

# P1: the characters of a path.
PATH_CHARACTERS = re.compile(r"[A-Za-z0-9._/-]+")
# P1: the longest path and the longest segment, in characters (today's: 81 and 53).
MAX_PATH = 160
MAX_SEGMENT = 100
# P1: the folder that may begin with a dot, as the first segment only.
DOT_FOLDERS = frozenset({".github"})
# P1: the file names that may begin with a dot (where they stand is P4's, DOT_FILES).
DOT_NAMES = frozenset({".gitignore", ".gitkeep"})
# P1: Windows's device names, refused as a segment's stem in any case.
DEVICES = frozenset({"CON", "PRN", "AUX", "NUL", *(f"COM{n}" for n in range(10)),
                     *(f"LPT{n}" for n in range(10))})
# P3: the extensions the tree uses, in lower case.
EXTENSIONS = frozenset({"md", "svg", "lean", "toml", "py", "txt", "json", "png", "jsonl",
                        "yml", "sha256", "sh", "lock", "cff", "bib"})
# P3: the files without an extension, by exact path.
EXTENSIONLESS = frozenset({"LICENSE", "NOTICE", "lean-toolchain", "model/lean-toolchain",
                           "scripts/hooks/pre-push", "scripts/hooks/safe-push"})
# P4: the top-level folders.
TOP_FOLDERS = frozenset({".github", "Audit", "Certificate", "Elements", "Staging", "assets",
                         "book", "checks", "docs", "figures", "heath", "mishnah", "model", "reading",
                         "review", "scripts", "tests"})
# P4: the files at the root, beside Markdown named in capitals (ROOT_MARKDOWN).
ROOT_FILES = frozenset({".gitignore", "AGENTS.md", "Audit.lean", "CERTIFICATE.md",
                        "CITATION.cff", "CLAUDE.md", "CONTRIBUTING.md", "Elements.lean",
                        "GRAPH.md", "LICENSE", "LICENSE-PROSE.md", "NOTICE", "README.md",
                        "Staging.lean", "facts.json", "lake-manifest.json", "lakefile.toml",
                        "lean-toolchain"})
# P4: further Markdown at the root, named in capitals as README.md is: words of capitals
# and digits joined by single hyphens, as LICENSE-PROSE.md is.
ROOT_MARKDOWN = re.compile(r"[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*\.md")
# P4: the types each top-level folder holds, by extension.
FOLDER_TYPES = {
    ".github": frozenset({"md", "yml"}),
    "Audit": frozenset({"lean"}),
    "Certificate": frozenset({"md", "lean"}),
    "Elements": frozenset({"lean"}),
    "Staging": frozenset({"lean"}),
    "assets": frozenset({"md", "svg", "png"}),
    "book": frozenset({"md"}),
    "checks": frozenset({"toml"}),
    "docs": frozenset({"md", "toml", "bib", "json", "jsonl", "lean"}),
    "figures": frozenset({"svg"}),
    "heath": frozenset({"md"}),
    "mishnah": frozenset({"md"}),
    "model": frozenset({"lean", "md", "json", "toml", "sha256"}),
    "reading": frozenset({"md"}),
    "review": frozenset({"toml"}),
    "scripts": frozenset({"py", "sh", "toml", "txt"}),
    "tests": frozenset({"py", "json", "lean", "md", "toml", "sha256", "txt"}),
}
# P4: the files a folder holds by exact path, beside its types.
FOLDER_FILES = frozenset({"Audit/screen.py", "Certificate/axioms.lock", "checks/README.md",
                          "model/lean-toolchain", "review/SCHEMA.md", "scripts/hooks/pre-push",
                          "scripts/hooks/safe-push", "scripts/test_safe_push_times.json"})
# P4: the dot files, by exact path: .gitignore at the root and in model/, .gitkeep in Staging/.
DOT_FILES = frozenset({".gitignore", "model/.gitignore", "Staging/.gitkeep"})
# P5: the thirteen books, by Roman numeral (R).
BOOK = r"(?:I|II|III|IV|V|VI|VII|VIII|IX|X|XI|XII|XIII)"
# P5: a proposition's number (NN): two digits, and three from 100 on, for Book X's 115.
NUMBER = r"(?:0[1-9]|[1-9][0-9]|[1-9][0-9]{2})"
# P5: the names of each folder whose names are mechanical, and how a finding gives them.
NAMES = {
    "book": (re.compile(rf"book/{BOOK}/(?:{NUMBER}|front|index)\.md|book/names\.md"),
             "book/R/NN.md, book/R/front.md, book/R/index.md or book/names.md"),
    "heath": (re.compile(rf"heath/{BOOK}/(?:{NUMBER}|front)\.md"),
              "heath/R/NN.md or heath/R/front.md"),
    "mishnah": (re.compile(rf"mishnah/{BOOK}/{NUMBER}\.md|mishnah/intro/{BOOK}\.md"),
                "mishnah/R/NN.md or mishnah/intro/R.md"),
    "reading": (re.compile(rf"reading/{BOOK}/{NUMBER}\.md"), "reading/R/NN.md"),
    "review": (re.compile(rf"review/{BOOK}/{NUMBER}\.toml|review/SCHEMA\.md|review/terms\.toml"),
               "review/R/NN.toml, review/SCHEMA.md or review/terms.toml"),
    "figures": (re.compile(rf"figures/{BOOK}/{NUMBER}(?:-idea|-modern)?\.svg"),
                "figures/R/NN.svg, figures/R/NN-idea.svg or figures/R/NN-modern.svg"),
}
# P5: R and NN, as a finding explains them.
NAMES_KEY = "R a book, I to XIII; NN a proposition, 01 to 99, then 100 on"
# P5: a brief: four digits and a slug of letters and digits joined by hyphens, or a book's.
BRIEF = re.compile(rf"docs/briefs/(?:[0-9]{{4}}-[A-Za-z0-9]+(?:-[A-Za-z0-9]+)*|book-{BOOK})\.md")
# P5: the folders whose Lean files are modules of the edition's libraries (and the root's).
LEAN_TREES = frozenset({"Elements", "Staging", "Audit", "model"})
# P5: a segment of a Lean module's name.
MODULE = re.compile(r"[A-Z][A-Za-z0-9]*")
# P5: a book's folder under Elements/, and a proposition's file there.
BOOK_MODULE = re.compile(rf"Book{BOOK}")
PROP_MODULE = re.compile(rf"Prop{NUMBER}")
# P5: the folder of the model's laws, whose files directly in it are named in lower case.
LAW_FOLDER = "model/Model/Laws"
# P5: a law's stem there, after its group as model/README.md lists it: words joined by "-".
LAW_STEM = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
# P5: a Python file's name, which can be imported.
PYTHON = re.compile(r"[a-z][a-z0-9_]*\.py")
# P6: the executable files, by exact path; each is 100755, and no other file is.
EXECUTABLES = frozenset({"scripts/check_release_gate.py", "scripts/copy_acceptance_checks.sh",
                         "scripts/hooks/pre-push", "scripts/hooks/safe-push",
                         "scripts/install_hooks.sh", "scripts/safe_push.py"})
# P6: the modes a file may have, plain and executable.
PLAIN, EXECUTABLE = "100644", "100755"

# Git's escapes, for a path shown as Git quotes it.
ESCAPES = {7: "\\a", 8: "\\b", 9: "\\t", 10: "\\n", 11: "\\v", 12: "\\f", 13: "\\r",
           34: '\\"', 92: "\\\\"}


def fail(message: str) -> None:
    print(f"✗ paths: {message}", file=sys.stderr)
    sys.exit(1)


def shown(path: str) -> str:
    """A path as a finding gives it: as it is when it keeps to P1's characters, else quoted
    and escaped as Git quotes a path, byte by byte, so that nothing in it is hidden."""
    if PATH_CHARACTERS.fullmatch(path):
        return path
    out = []
    for byte in path.encode("utf-8", "surrogateescape"):
        if byte in ESCAPES:
            out.append(ESCAPES[byte])
        elif 0x20 <= byte < 0x7F:
            out.append(chr(byte))
        else:
            out.append(f"\\{byte:03o}")
    return '"' + "".join(out) + '"'


def quoted(name: str) -> str:
    """A name inside a finding's reason, in single quotes and escaped as `shown` escapes a
    path, so that a finding is always one line of printable ASCII."""
    return f"'{shown(name)}'"


def character(c: str) -> str:
    """A character P1 refuses, named for a finding."""
    if c == " ":
        return "a space"
    if 0xDC80 <= ord(c) <= 0xDCFF:
        return "a byte that is not UTF-8"
    if 0x20 < ord(c) < 0x7F:
        return f"'{c}'"
    return f"U+{ord(c):04X}"


def characters(path: str) -> list[str]:
    """P1: the characters, segments and lengths of a path."""
    reasons = []
    if not PATH_CHARACTERS.fullmatch(path):
        bad = sorted({c for c in path if not PATH_CHARACTERS.fullmatch(c)})
        reasons.append(f"holds {', '.join(character(c) for c in bad)}; a path is ASCII "
                       "letters, digits, '.', '_', '-' and '/'")
    if len(path) > MAX_PATH:
        reasons.append(f"{len(path)} characters long; a path is at most {MAX_PATH}")
    segments = path.split("/")
    if "" in segments:
        reasons.append("has an empty segment")
    for i, segment in enumerate(segments):
        if not segment:
            continue
        if segment in (".", ".."):
            reasons.append(f"has a '{segment}' segment")
            continue
        last = i == len(segments) - 1
        if segment[0] in ".-" or segment[-1] in ".-":
            if not ((segment in DOT_FOLDERS and i == 0) or (segment in DOT_NAMES and last)):
                reasons.append(f"{quoted(segment)} begins or ends with '.' or '-'; only "
                               ".github, first, and .gitignore and .gitkeep, last, may")
        if len(segment) > MAX_SEGMENT:
            reasons.append(f"a segment {len(segment)} characters long; a segment is at "
                           f"most {MAX_SEGMENT}")
        if segment.split(".")[0].upper() in DEVICES:
            reasons.append(f"{quoted(segment)} is named as a Windows device "
                           f"({segment.split('.')[0].upper()}), which Windows cannot check out")
    return reasons


def fold(name: str) -> str:
    """A name as a disk that ignores case and Unicode normal forms sees it."""
    return unicodedata.normalize("NFC", unicodedata.normalize("NFC", name).casefold())


def twins(paths: list[str], directories: list[str] | tuple[str, ...] = ()) -> list[tuple[str, str]]:
    """P2: each path or folder alike with another once folded, with the reason. A folder is
    named with a trailing '/' and the first path under it, and a file and a folder of one
    name are twins too, since a disk holds only one of them."""
    first: dict[str, str] = {}            # each path and folder, and the first path under it
    for directory in sorted(set(directories)):
        first.setdefault(directory + "/", directory)
        parts = directory.split("/")
        for i in range(1, len(parts)):
            first.setdefault("/".join(parts[:i]) + "/", directory)
    for path in sorted(paths):
        first.setdefault(path, path)
        parts = path.split("/")
        for i in range(1, len(parts)):
            first.setdefault("/".join(parts[:i]) + "/", path)
    groups: dict[str, list[str]] = defaultdict(list)
    for name in first:
        groups[fold(name.rstrip("/"))].append(name)
    found = []
    for group in groups.values():
        if len(group) < 2:
            continue
        for name in sorted(group):
            others = ", ".join(shown(o) for o in sorted(group) if o != name)
            where = f" (the folder of {shown(first[name])})" if name.endswith("/") else ""
            found.append((name, f"a case twin of {others}{where}: they differ only in case "
                                "or Unicode form, and a disk that ignores case holds one"))
    return found


def extension(path: str) -> list[str]:
    """P3: an extension in lower case from EXTENSIONS, or a file of EXTENSIONLESS. The
    extension is what follows the name's last dot, matched exactly, so README.MD and x.Md
    are refused."""
    base = path.rsplit("/", 1)[-1]
    if base.startswith("."):
        return []                 # a dot name: P1 says which may be, and P4 where
    stem, dot, ext = base.rpartition(".")
    if not dot:
        return [] if path in EXTENSIONLESS else [
            "has no extension; a file without one is named in EXTENSIONLESS"]
    if ext in EXTENSIONS:
        return []
    if ext.isascii() and ext.lower() in EXTENSIONS:
        return [f"the extension .{ext} is not in lower case"]
    return [f"{quoted('.' + ext)} is not an extension the tree uses (EXTENSIONS: "
            f"{' '.join(sorted(EXTENSIONS))})"]


def placement(path: str) -> list[str]:
    """P4: the folder a path stands in, and the types that folder holds."""
    parts = path.split("/")
    base = parts[-1]
    if len(parts) == 1:
        if path in ROOT_FILES or ROOT_MARKDOWN.fullmatch(path):
            return []
        return ["not a file of the root, which holds ROOT_FILES and Markdown named in "
                "capitals, words joined by single hyphens, as README.md and LICENSE-PROSE.md"]
    top = parts[0]
    if top not in TOP_FOLDERS:
        return [f"'{shown(top)}/' is not a top-level folder (TOP_FOLDERS)"]
    if base in DOT_NAMES:
        if path in DOT_FILES:
            return []
        return [f"{base} stands only at " + " and ".join(
            sorted(p for p in DOT_FILES if p.rsplit("/", 1)[-1] == base))]
    if path in FOLDER_FILES or base.startswith("."):
        return []                 # named by exact path, or P1's to refuse
    stem, dot, ext = base.rpartition(".")
    if not dot:
        return [f"a file without an extension in {top}/ stands only at a path of "
                "FOLDER_FILES"]
    if ext not in FOLDER_TYPES[top]:
        return [f".{ext} is not a type {top}/ holds ("
                f"{' '.join('.' + t for t in sorted(FOLDER_TYPES[top]))})"]
    return []


def directory_placement(path: str) -> list[str]:
    """P4 where an explicit directory may stand. Its leaves, not the directory itself,
    determine the types it holds."""
    top = path.split("/", 1)[0]
    if top not in TOP_FOLDERS:
        return [f"'{shown(top)}/' is not a top-level folder (TOP_FOLDERS)"]
    return []


def module(parts: list[str]) -> list[str]:
    """P5: a Lean file of Elements/, Staging/, Audit/, model/ or the root, by Lean module
    names; model/ is a package of its own, whose modules begin below it. A file directly in
    LAW_FOLDER is one of the model's laws, and its stem is LAW_STEM instead."""
    names = parts[1:] if parts[0] == "model" else list(parts)
    names[-1] = names[-1][:-len(".lean")]
    law = "/".join(parts[:-1]) == LAW_FOLDER
    reasons = []
    bad = [n for n in (names[:-1] if law else names) if not MODULE.fullmatch(n)]
    if bad:
        reasons.append(f"{', '.join(quoted(n) for n in bad)} not a Lean module name: a "
                       "capital letter, then letters and digits")
    if law and not LAW_STEM.fullmatch(names[-1]):
        reasons.append(f"{quoted(names[-1])} is not a law's name in {LAW_FOLDER}/: words of "
                       "lower-case letters and digits joined by '-', as model/README.md "
                       "lists the laws")
    if parts[0] == "Elements" and len(names) > 1:
        if names[1].startswith("Book") and not BOOK_MODULE.fullmatch(names[1]):
            reasons.append(f"{quoted(names[1])} is not a book's folder, BookR (BookI to "
                           "BookXIII)")
        if re.match(r"Prop[0-9]", names[-1]) and not PROP_MODULE.fullmatch(names[-1]):
            reasons.append(f"{quoted(names[-1])} is not a proposition's file, PropNN "
                           "(Prop01.lean, never Prop1.lean)")
    return reasons


def names(path: str) -> list[str]:
    """P5: the names that are mechanical."""
    parts = path.split("/")
    top, base = parts[0], parts[-1]
    if base.casefold() == "lakefile.lean":
        return ["a build file written in Lean; the packages' build files are lakefile.toml"]
    reasons = []
    if top in NAMES and len(parts) > 1 and not NAMES[top][0].fullmatch(path):
        reasons.append(f"not a name {top}/ holds: {NAMES[top][1]} ({NAMES_KEY})")
    if path.startswith("docs/briefs/") and not BRIEF.fullmatch(path):
        reasons.append("not a brief's name: docs/briefs/NNNN-<slug>.md, four digits and "
                       "words of letters and digits joined by hyphens, or docs/briefs/book-R.md")
    if base.endswith(".py"):
        stem = base[:-len(".py")]
        if not PYTHON.fullmatch(base):
            reasons.append("not an importable Python name: a lower-case letter, then "
                           "lower-case letters, digits and underscores")
        elif keyword.iskeyword(stem):
            reasons.append(f"not an importable Python name: {quoted(stem)} is a Python "
                           "keyword")
    if base.endswith(".lean") and (len(parts) == 1 or top in LEAN_TREES):
        reasons += module(parts)
    return reasons


def mode(mode_: str, path: str) -> list[str]:
    """P6: plain, or executable exactly when the path is one of EXECUTABLES."""
    if mode_ == "120000":
        return ["a symbolic link (120000); the tree holds no links"]
    if mode_ == "160000":
        return ["a submodule (160000); the tree holds none"]
    if mode_ not in (PLAIN, EXECUTABLE):
        return [f"mode {shown(mode_)}; a file is {PLAIN}, or {EXECUTABLE} when it is "
                "executable"]
    if mode_ == EXECUTABLE and path not in EXECUTABLES:
        return [f"executable ({EXECUTABLE}), but not one of EXECUTABLES"]
    if mode_ == PLAIN and path in EXECUTABLES:
        return [f"one of EXECUTABLES, but not executable ({PLAIN})"]
    return []


def findings(entries: list[tuple[str, str]],
             directories: list[str] | tuple[str, ...] = ()) -> list[str]:
    """Every finding for the (mode, path) entries, one line each, by rule and then path:
    "P<rule> <path>: <reason>". A path among the entries more than once is P2's: a tree
    names a path once, and a disk holds one of them. Explicit directories are separate
    from leaves, so an ordinary directory and a child do not look like two listings of the
    same folder; P3, P5 and P6 apply only to leaves. P4 judges only what P3 passes, and P5
    what both pass, so that one fault is not reported three times over."""
    found: set[tuple[int, str, str]] = set()
    paths = sorted({path for _, path in entries})
    for path, n in Counter(path for _, path in entries).items():
        if n > 1:
            found.add((2, path, f"listed {n} times; a tree names a path once, and a disk "
                                "holds one of them"))
    for mode_, path in set(entries):
        found.update((6, path, r) for r in mode(mode_, path))
    for directory, n in Counter(directories).items():
        if n > 1:
            found.add((2, directory + "/", f"listed {n} times; a tree names a directory "
                                            "once, and a disk holds one of them"))
    for directory in sorted(set(directories)):
        found.update((1, directory + "/", r) for r in characters(directory))
        found.update((4, directory + "/", r) for r in directory_placement(directory))
    for path in paths:
        found.update((1, path, r) for r in characters(path))
        types = extension(path)
        found.update((3, path, r) for r in types)
        if not types:
            where = placement(path)
            found.update((4, path, r) for r in where)
            if not where:
                found.update((5, path, r) for r in names(path))
    found.update((2, name, reason) for name, reason in twins(paths, directories))
    return [f"P{rule} {shown(path)}: {reason}" for rule, path, reason in sorted(found)]


# The self-test's planted faults: the rule that must catch each, the entries, and the path
# or folder its finding must name.
PLANTED: tuple[tuple[int, tuple[tuple[str, str], ...], str], ...] = (
    (1, ((PLAIN, "book/I/Planted page.md"),), "book/I/Planted page.md"),
    (1, ((PLAIN, "docs/café.md"),), "docs/café.md"),
    (1, ((PLAIN, "docs/tab\there.md"),), "docs/tab\there.md"),
    (1, ((PLAIN, "docs//empty.md"),), "docs//empty.md"),
    (1, ((PLAIN, "docs/../escape.md"),), "docs/../escape.md"),
    (1, ((PLAIN, "docs/./here.md"),), "docs/./here.md"),
    (1, ((PLAIN, "docs/-dash.md"),), "docs/-dash.md"),
    (1, ((PLAIN, "docs/dash-/a.md"),), "docs/dash-/a.md"),
    (1, ((PLAIN, "docs/.hidden.md"),), "docs/.hidden.md"),
    (1, ((PLAIN, "docs/.github/a.md"),), "docs/.github/a.md"),
    (1, ((PLAIN, "docs/" + "a" * 101 + ".md"),), "docs/" + "a" * 101 + ".md"),
    (1, ((PLAIN, "docs/" + "/".join(["abcdefghij"] * 15) + ".md"),),
     "docs/" + "/".join(["abcdefghij"] * 15) + ".md"),
    (1, ((PLAIN, "docs/con.md"),), "docs/con.md"),
    (1, ((PLAIN, "docs/Lpt9/a.md"),), "docs/Lpt9/a.md"),
    (1, ((PLAIN, "docs/aux.tar.md"),), "docs/aux.tar.md"),
    (1, ((PLAIN, "docs/com0.md"),), "docs/com0.md"),
    (1, ((PLAIN, "docs/LPT0/a.md"),), "docs/LPT0/a.md"),
    (2, ((PLAIN, "README.md"), (PLAIN, "readme.md")), "readme.md"),
    (2, ((PLAIN, "scripts/a.py"), (PLAIN, "Scripts/json.py")), "Scripts/"),
    # An accented e, composed (NFC) and decomposed (NFD): escapes, so no editor merges them.
    (2, ((PLAIN, "docs/caf\u00e9.md"), (PLAIN, "docs/cafe\u0301.md")), "docs/cafe\u0301.md"),
    (2, ((PLAIN, "docs/Notes"), (PLAIN, "docs/notes/a.md")), "docs/notes/"),
    (2, ((PLAIN, "README.md"), (PLAIN, "README.md")), "README.md"),
    (3, ((PLAIN, "docs/notes.MD"),), "docs/notes.MD"),
    (3, ((PLAIN, "docs/notes.markdown"),), "docs/notes.markdown"),
    (3, ((PLAIN, ".github/workflows/ci.yaml"),), ".github/workflows/ci.yaml"),
    (3, ((PLAIN, "assets/page.htm"),), "assets/page.htm"),
    (3, ((PLAIN, "docs/Makefile"),), "docs/Makefile"),
    (4, ((PLAIN, "book/I/01.svg"),), "book/I/01.svg"),
    (4, ((PLAIN, "notes/a.md"),), "notes/a.md"),
    (4, ((PLAIN, "notes.txt"),), "notes.txt"),
    (4, ((PLAIN, "Readme.md"),), "Readme.md"),
    (4, ((PLAIN, "TRAILING-.md"),), "TRAILING-.md"),
    (4, ((PLAIN, "DOUBLE--HYPHEN.md"),), "DOUBLE--HYPHEN.md"),
    (4, ((PLAIN, ".gitattributes"),), ".gitattributes"),
    (4, ((PLAIN, ".gitmodules"),), ".gitmodules"),
    (4, ((PLAIN, "docs/.gitignore"),), "docs/.gitignore"),
    (4, ((PLAIN, "Staging/Stage5/.gitkeep"),), "Staging/Stage5/.gitkeep"),
    (4, ((PLAIN, "figures/I/01.png"),), "figures/I/01.png"),
    (4, ((PLAIN, "lakefile.lean"),), "lakefile.lean"),
    (5, ((PLAIN, "review/I/1.toml"),), "review/I/1.toml"),
    (5, ((PLAIN, "book/XIV/01.md"),), "book/XIV/01.md"),
    (5, ((PLAIN, "heath/I/index.md"),), "heath/I/index.md"),
    (5, ((PLAIN, "figures/I/01-sketch.svg"),), "figures/I/01-sketch.svg"),
    (5, ((PLAIN, "mishnah/I/00.md"),), "mishnah/I/00.md"),
    (5, ((PLAIN, "reading/I/1000.md"),), "reading/I/1000.md"),
    (5, ((PLAIN, "docs/briefs/13-book-V.md"),), "docs/briefs/13-book-V.md"),
    (5, ((PLAIN, "Elements/BookI/Prop1.lean"),), "Elements/BookI/Prop1.lean"),
    (5, ((PLAIN, "Elements/Book1/Prop01.lean"),), "Elements/Book1/Prop01.lean"),
    (5, ((PLAIN, "Elements/BookI/prop_01.lean"),), "Elements/BookI/prop_01.lean"),
    (5, ((PLAIN, "model/lakefile.lean"),), "model/lakefile.lean"),
    (5, ((PLAIN, "docs/lakefile.lean"),), "docs/lakefile.lean"),
    (5, ((PLAIN, "Staging/stage5/A.lean"),), "Staging/stage5/A.lean"),
    (5, ((PLAIN, "model/Model/Laws/Angles.lean"),), "model/Model/Laws/Angles.lean"),
    (5, ((PLAIN, "model/Model/Laws/areas_p5.lean"),), "model/Model/Laws/areas_p5.lean"),
    (5, ((PLAIN, "model/Model/laws.lean"),), "model/Model/laws.lean"),
    (5, ((PLAIN, "model/Model/Laws/sub/x.lean"),), "model/Model/Laws/sub/x.lean"),
    (5, ((PLAIN, "model/Model/Laws/lakefile.lean"),), "model/Model/Laws/lakefile.lean"),
    (5, ((PLAIN, "Elements/angles.lean"),), "Elements/angles.lean"),
    (5, ((PLAIN, "scripts/check-paths.py"),), "scripts/check-paths.py"),
    (5, ((PLAIN, "scripts/class.py"),), "scripts/class.py"),
    (6, (("120000", "docs/link.md"),), "docs/link.md"),
    (6, (("160000", "docs/sub"),), "docs/sub"),
    (6, ((EXECUTABLE, "scripts/heath.py"),), "scripts/heath.py"),
    (6, ((PLAIN, "scripts/safe_push.py"),), "scripts/safe_push.py"),
    (6, (("100664", "docs/a.md"),), "docs/a.md"),
)
# The self-test's good paths, which must pass together: today's kinds, and a new book's.
GOOD: tuple[tuple[str, str], ...] = (
    (PLAIN, ".github/workflows/ci.yml"), (PLAIN, ".gitignore"), (PLAIN, "README.md"),
    (PLAIN, "SECURITY.md"), (PLAIN, "CODE-OF-CONDUCT.md"), (PLAIN, "LICENSE"),
    (PLAIN, "lean-toolchain"),
    (PLAIN, "Elements.lean"), (PLAIN, "Elements/BookI/Prop01.lean"),
    (PLAIN, "Elements/BookIV/Prop16.lean"), (PLAIN, "Elements/BookX/Prop115.lean"),
    (PLAIN, "Elements/Foundations/Tacit/Metric.lean"), (PLAIN, "Staging/.gitkeep"),
    (PLAIN, "Staging/Stage3/Prop23Point.lean"), (PLAIN, "Audit/screen.py"),
    (PLAIN, "Certificate/axioms.lock"), (PLAIN, "book/IV/01.md"), (PLAIN, "book/IV/front.md"),
    (PLAIN, "book/IV/index.md"), (PLAIN, "book/names.md"), (PLAIN, "heath/X/115.md"),
    (PLAIN, "mishnah/IV/16.md"), (PLAIN, "mishnah/intro/XIII.md"), (PLAIN, "reading/X/100.md"),
    (PLAIN, "review/X/115.toml"), (PLAIN, "review/SCHEMA.md"), (PLAIN, "review/terms.toml"),
    (PLAIN, "figures/IV/01-modern.svg"), (PLAIN, "figures/IV/01-idea.svg"),
    (PLAIN, "figures/X/115.svg"), (PLAIN, "docs/briefs/0013-book-V.md"),
    (PLAIN, "docs/briefs/book-IV.md"), (PLAIN, "docs/references.bib"),
    (PLAIN, "model/.gitignore"), (PLAIN, "model/lean-toolchain"),
    (PLAIN, "model/Model/Euclidean/Pasch.lean"), (PLAIN, "model/Model/Laws/areas-p5.lean"),
    (PLAIN, "model/Model/Laws/ratios.lean"), (PLAIN, "tests/model/results/summary.txt"),
    (PLAIN, "assets/stoicheia-logo.png"), (PLAIN, "scripts/audit/jev_questions.py"),
    *((EXECUTABLE, path) for path in sorted(EXECUTABLES)),
)


def self_test() -> list[str]:
    """Each planted fault caught by its own rule, naming its path; the good paths pass."""
    problems = []
    for rule, entries, name in PLANTED:
        found = findings(list(entries))
        if not any(f.startswith(f"P{rule} {shown(name)}: ") for f in found):
            problems.append(f"{shown(name)} was not caught by P{rule}"
                            + (f"; found: {'; '.join(found)}" if found else ""))
    problems += [f"a good path refused: {f}" for f in findings(list(GOOD))]
    return problems


def repository() -> tuple[Path, dict[str, str]]:
    """The repository the script stands in, as Git names its work tree, and the environment
    its Git reads run in. An inherited GIT_DIR or GIT_WORK_TREE that names another is
    refused, saying what to do: a Git alias run from a linked worktree sets GIT_DIR, and the
    check would judge the wrong index. Those reads run from the work tree's root, so each
    relative variable keeps the meaning Git gives it from the caller's directory: GIT_DIR
    and GIT_WORK_TREE are taken from there, and GIT_INDEX_FILE from the root, where Git
    reads it once it has entered the work tree, save that a caller outside the work tree
    with an explicit pair, which Git does not enter, has it taken from its own directory."""
    inherited = [name for name in ("GIT_DIR", "GIT_WORK_TREE") if name in os.environ]
    remedy = ((f"; {' and '.join(inherited)} {'is' if len(inherited) == 1 else 'are'} set "
               "(a Git alias run from a linked worktree sets GIT_DIR): run the check with "
               "neither (env -u GIT_DIR -u GIT_WORK_TREE python3 scripts/check_paths.py)")
              if inherited else "")
    discovery_env = os.environ.copy()
    discovery_env.pop("GIT_DIR", None)
    discovery_env.pop("GIT_WORK_TREE", None)
    active_env = os.environ.copy()
    caller = Path.cwd()
    for name in ("GIT_DIR", "GIT_WORK_TREE"):
        value = active_env.get(name)
        if value and not Path(value).is_absolute():
            active_env[name] = str((caller / value).resolve())

    def location(env: dict[str, str] | None) -> tuple[Path, Path]:
        try:
            done = subprocess.run(
                ["git", "rev-parse", "--show-toplevel", "--absolute-git-dir"],
                cwd=SCRIPT.parent, env=env, capture_output=True, text=True)
        except OSError as e:
            fail(f"cannot run Git ({e})")
        if done.returncode != 0:
            fail(f"cannot find the repository from {SCRIPT.parent}: {done.stderr.strip()}"
                 + remedy)
        lines = done.stdout.splitlines()
        if len(lines) != 2:
            fail(f"cannot read Git's repository location from {SCRIPT.parent}" + remedy)
        return Path(lines[0]).resolve(), Path(lines[1]).resolve()

    expected_top, expected_git_dir = location(discovery_env)
    script_root = SCRIPT.parent.parent
    if expected_top != script_root:
        fail(f"Git's work tree is {expected_top}, not the script's repository {script_root}; "
             "run the check from the repository's own work tree")
    top, git_dir = location(active_env)
    if top != script_root:
        fail(f"Git's work tree is {top}, not the script's repository {script_root}"
             + (remedy or "; run the check from the repository's own work tree"))
    if git_dir != expected_git_dir:
        fail(f"Git's directory is {git_dir}, not the script's repository Git directory "
             f"{expected_git_dir}" + (remedy or "; run the check from the repository's "
                                         "own work tree"))
    index = active_env.get("GIT_INDEX_FILE")
    if (index and not Path(index).is_absolute()
            and all(name in os.environ for name in ("GIT_DIR", "GIT_WORK_TREE"))
            and caller != top and top not in caller.parents):
        active_env["GIT_INDEX_FILE"] = str((caller / index).resolve())
    return top, active_env


def git(root: Path, *args: str, env: dict[str, str] | None = None) -> bytes:
    try:
        done = subprocess.run(["git", *args], cwd=root, env=env, capture_output=True)
    except OSError as e:
        fail(f"cannot run Git ({e})")
    if done.returncode != 0:
        fail(f"git {' '.join(args)}: {done.stderr.decode(errors='replace').strip()}")
    return done.stdout


def entries_of(listing: bytes) -> list[tuple[str, str]]:
    """The (mode, path) entries of `git ls-files -s -z`, every one: each record is the mode
    and other fields, a tab, and the path, as bytes. A path that is not UTF-8 keeps its
    bytes as surrogates, which P1 refuses."""
    entries = []
    for record in listing.split(b"\0"):
        if not record:
            continue
        fields, tab, path = record.partition(b"\t")
        if not tab or not fields:
            fail(f"cannot read Git's entry {record!r}")
        entries.append((fields.split(b" ", 1)[0].decode("ascii", "replace"),
                        path.decode("utf-8", "surrogateescape")))
    return sorted(entries)


def tree_entries_of(listing: bytes) -> tuple[list[tuple[str, str]], list[str]]:
    """The leaves and explicit directories of `git ls-tree -r -t -z`, kept separately and
    every one, so that a path or folder listed twice is seen, and an empty folder too."""
    entries, directories = [], []
    for record in listing.split(b"\0"):
        if not record:
            continue
        fields, tab, raw_path = record.partition(b"\t")
        words = fields.split()
        if not tab or len(words) != 3:
            fail(f"cannot read Git's tree entry {record!r}")
        mode_, kind = words[:2]
        path = raw_path.decode("utf-8", "surrogateescape")
        if kind == b"tree":
            directories.append(path)
        else:
            entries.append((mode_.decode("ascii", "replace"), path))
    return sorted(entries), sorted(directories)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--rev", metavar="COMMIT",
                        help="judge this commit's tree instead of the index")
    parser.add_argument("--self-test", action="store_true",
                        help="first plant a fault of each rule in memory, and expect each caught")
    args = parser.parse_args(argv)

    if args.self_test:
        problems = self_test()
        if problems:
            for problem in problems:
                print(f"✗ paths: self-test: {problem}")
            return 1
        print(f"  self-test: {len(PLANTED)} planted faults, each caught by its rule; "
              f"{len(GOOD)} good paths, Book IV's and Book X's among them, pass")

    root, repository_env = repository()
    if args.rev is None:
        # The index lists a path once, save once at each stage of a merge left unresolved,
        # so an entry repeated there is taken once; a tree's entries are all kept, and a
        # path listed twice among them is P2's.
        entries = sorted(set(entries_of(
            git(root, "ls-files", "-s", "-z", env=repository_env))))
        directories = []
        judged = "tracked paths of the index"
    else:
        commit = git(root, "rev-parse", "--verify", "--quiet", "--end-of-options",
                     f"{args.rev}^{{commit}}", env=repository_env).decode().strip()
        entries, directories = tree_entries_of(
            git(root, "ls-tree", "-r", "-t", "-z", "--full-tree", commit,
                env=repository_env))
        judged = f"paths of {args.rev} ({commit[:12]})"
    count = len({path for _, path in entries})
    found = findings(entries, directories)
    if found:
        for finding in found:
            print(f"✗ {finding}")
        print(f"\n{len(found)} path finding(s) among {count} {judged} (WORKFLOW, section 4, "
              "\"File names\"; the lists are in scripts/check_paths.py)")
        return 1
    print(f"✓ paths: all {count} {judged} follow the standard for names, types and modes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
