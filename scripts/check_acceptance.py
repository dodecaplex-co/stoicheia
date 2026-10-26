"""Check Books I-III against the acceptance checklist, and write the report.

The checklist is docs/ACCEPTANCE.md, its one home: what each item asks, and whether a
machine or a reviewer answers it. This script answers the machine's items for every
proposition of Books I-III, for each book and for the edition as a whole, and reads the
reviewer's items from the review records (`review/<book>/NN.toml`, `[review] items`) and
from each book's acceptance record (`docs/reports/acceptance/book-<book>.toml`). It
writes every failure to docs/reports/acceptance-books-I-III.md and, with --json, writes
the verdicts beside it; it changes nothing else.

    python3 scripts/check_acceptance.py            every item
    python3 scripts/check_acceptance.py --quick    the kernel replay and the model tests
                                                   not run (each reported as not run)
    python3 scripts/check_acceptance.py --output PATH   the report written to PATH
    python3 scripts/check_acceptance.py --json PATH     every item's verdict written to
                                                        PATH as well, for --compare
    python3 scripts/check_acceptance.py --compare MAIN PR
                                                   no check run: whether every item that
                                                   passes in MAIN passes in PR, two files
                                                   that --json wrote (P10 and E6 aside)

Run it on a built tree, as CI's `check` job leaves one: after `lake build`, `lake build
Audit` and `lake env lean Certificate/Facts.lean`, with `lake` on the PATH, Python 3.11 or
later, and the history of the commits the records name (a full clone, not a shallow one).
It reuses the checks it stands on rather than restating them: `check_fidelity.py`'s
functions, in this process, and `check_style.py`, `check_links.py`, `check_kernel.py`,
`heath.py` and the model tests, each run as CI runs it, its findings sorted by the
proposition or book whose file they name; and `render.py`'s functions, to regenerate the
pages in memory and compare them with the files, writing nothing.

The check that every Lean name a catalogue gives is declared, by asking Lean itself,
follows Patrick Massot's `leanblueprint checkdecls`, which checks that every declaration a
blueprint names exists in the project; we are grateful for the idea.

In checking mode it exits 0 only when every item passes and every check ran; 1 otherwise,
the report written either way; 2 when it cannot begin (no facts.json, say). Standard
library only.

With --compare it runs no check, and reads two files of verdicts that one copy of this
script wrote with --json: main's, then the pull request's. It exits 0 when every item that
passes in the first passes in the second, so that a pass may not turn into a fail; 1 when
one does not, each such item listed with why; and 2 when either file is not this script's
verdicts, or the two were written by different copies of it, which would not judge alike.
P10 and E6 turning into a fail are listed and not held (STAGING_ITEMS): they read Staging/
alone, and staging a statement before its proof is the workflow's own way in. CI's
`acceptance` job in `.github/workflows/ci.yml` runs it on every pull request.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import check_fidelity as cf
import check_style
import heath
import render

ROOT = heath.ROOT
REPORT = ROOT / "docs" / "reports" / "acceptance-books-I-III.md"
BOOK_RECORDS = ROOT / "docs" / "reports" / "acceptance"
PY = sys.executable or "python3"

# ---------------------------------------------------------------------------------------
# The items, as docs/ACCEPTANCE.md numbers and names them. A change here is a change there.

PROP_ITEMS = [
    ("P1", "proved", "machine", "proved, with its porism and companions, each with its certificate"),
    ("P2", "record", "machine", "a current record at the stage `full`, its reviewer, run and commit"),
    ("P3", "scope", "machine", "full, or a limitation the checklist names; no other argument"),
    ("P4", "disclosed", "machine", "every exception on the page; no disclosure in the mishnah alone"),
    ("P5", "policies", "machine", "the certificate's policies"),
    ("P6", "runs", "machine", "every run of `--` lines carried or declared; the notes shown"),
    ("P7", "text", "machine", "Heath's text, quotations, letters, links and scans"),
    ("P8", "figures", "machine", "both figures, by the figure rules; the case named"),
    ("P9", "style", "machine", "the style rules; the page regenerated clean"),
    ("P10", "staging", "machine", "nothing of it left in Staging"),
    ("P11", "statement", "review", "the statement says what the enunciation says"),
    ("P12", "passages", "review", "every substantive passage carried or truly named"),
    ("P13", "representations", "review", "representations with their bridges"),
    ("P14", "commentary", "review", "the commentary accurate and specific"),
    ("P15", "figures", "review", "the figures agree with the proof"),
    ("P16", "signoff", "review", "a reviewer other than the author signs off"),
]
BOOK_ITEMS = [
    ("B1", "pages", "machine", "the book's pages and completion summary generated and current"),
    ("B2", "catalogues", "machine", "the gap and overlap catalogues current"),
    ("B3", "read-through", "review", "read straight through: it flows, in one voice"),
    ("B4", "limitations", "review", "the limitations deliberate, few and plainly stated"),
]
EDITION_ITEMS = [
    ("E1", "kernel", "machine", "every proof replayed by Lean's kernel and by nanoda"),
    ("E2", "certificate", "machine", "the lock, the axioms, the entries and the pinned facts"),
    ("E3", "contracts", "machine", "the shared contracts (`heath.py`)"),
    ("E4", "model", "machine", "the model tests"),
    ("E5", "edition", "machine", "the edition's other pages, links and style"),
    ("E6", "staging", "machine", "nothing else staged"),
]
REVIEW_ITEMS = {key: item for item, key, kind, _ in PROP_ITEMS if kind == "review"}
NA_ALLOWED = {"representations"}       # a proposition may use no special representation
BOOK_REVIEW_ITEMS = {key: item for item, key, kind, _ in BOOK_ITEMS if kind == "review"}

# P3. The deliberate limitations of Books I-III (docs/ACCEPTANCE.md, "The limitations
# allowed"): each proposition, the scope it may keep and the tag that must say why. Every
# other statement is full (stage 4b's goal, brief 0007), and no route is "alternative".
# A row goes when its record becomes full: P3 refuses an allowance for a full statement.
ALLOWED_LIMITS = {}

# P4. A sentence of a mishnah that says our statement or the Lean leaves something of
# Euclid's out, when the record declares no departure at all. A coarse guard: P14, the
# reviewer's reading of the commentary, is the real check. An exception names the
# proposition and the reason, and is printed in the report.
DISCLOSURE_SUBJECT = re.compile(
    r"\b(?:our|the) (?:statement|theorem|Lean|formal statement)s?\b|\bour Lean\b", re.I)
DISCLOSURE = re.compile(
    r"\b(?:restrict\w*|exclud\w*|omit\w*|left out|leaves?\b[^.;]{0,40}?\bout\b|"
    r"does not (?:prove|state|cover|carry)|do not (?:prove|state|cover)|"
    r"is not (?:proved|stated|formali[sz]ed)|not formali[sz]ed|extra hypothes\w*)", re.I)
DISCLOSURE_EXCEPTIONS: dict[str, str] = {}

# P5. Placement may be cited only by III.24 and by the theorems on arcs (brief 0005,
# stage 3): every other file of Elements/ is searched for it, comments aside.
PLACEMENT = re.compile(r"\bplacement\b|\bPlacement\.[A-Za-z_]")
PLACEMENT_HOMES = ("Elements/BookIII/Placement.lean", "Elements/BookIII/Placement/",
                   "Elements/BookIII/Arcs.lean", "Elements/BookIII/Prop24.lean")

# The check_style rules each item reads; the rest belong to P9 (or B1, B2 and E5).
TEXT_RULES = {"S8", "S9", "S17"}
FIGURE_RULES = {"S13", "S14", "S15", "S16", "S20", "S21", "S24", "S25", "S26"}

# B2. Backticked words of a catalogue that are not Lean declarations, and need none: the
# placeholder of a pattern, a field of facts.json, a tactic.
PLACEHOLDER = re.compile(r"(?:^|\.)PropN(?:\.|$)")
TACTICS = {"grind", "simp", "omega", "decide", "rfl", "exact", "sorry", "ac_rfl"}

# ---------------------------------------------------------------------------------------
# Findings: a failure is a message for one item of one proposition, book or the edition.

failures: dict[tuple[str, str], list[str]] = {}
not_run: dict[tuple[str, str], str] = {}


def fail(where: str, item: str, message: str) -> None:
    found = failures.setdefault((where, item), [])
    if message.rstrip() not in found:       # two checks may say the same thing once
        found.append(message.rstrip())


def skip(where: str, item: str, why: str) -> None:
    not_run[(where, item)] = why


def refs():
    for book, count in heath.BOOKS.items():
        for n in range(1, count + 1):
            yield book, n, f"{book}.{n}"


def owner(path: str) -> str | None:
    """Whose a file is: "I.5" for a proposition's own files, "Book I" for a book's, None
    for the edition's."""
    path = path.strip().lstrip("./")
    m = (re.fullmatch(r"(?:mishnah|reading|heath|review|book)/([IVX]+)/(\d\d)\.(?:md|toml)", path)
         or re.fullmatch(r"figures/([IVX]+)/(\d\d)(?:-idea|-modern)?\.svg", path)
         or re.fullmatch(r"Elements/Book([IVX]+)/Prop(\d\d)\.lean", path))
    if m and m.group(1) in heath.BOOKS and 1 <= int(m.group(2)) <= heath.BOOKS[m.group(1)]:
        return f"{m.group(1)}.{int(m.group(2))}"
    m = (re.fullmatch(r"mishnah/intro/([IVX]+)\.md", path)
         or re.fullmatch(r"book/([IVX]+)/(?:index|front)\.md", path)
         or re.fullmatch(r"docs/reports/gaps-book-([IVX]+)\.md", path))
    if m and m.group(1) in heath.BOOKS:
        return f"Book {m.group(1)}"
    return None


MESSAGE_REF = re.compile(r"^([IVX]+\.\d+(?: Por\.| [A-Za-z_][\w']*)?): ")
MESSAGE_PATH = re.compile(r"^([\w./-]+\.(?:lean|md|toml|svg|json))(?::\d+)?: ")


def whose_message(message: str) -> str | None:
    """The proposition or book a check's message is about: by the reference it begins
    with ("III.1 Por.: …" is III.1's), or by the file it names first."""
    m = MESSAGE_REF.match(message)
    if m:
        try:
            parent = heath.parse_ref(m.group(1)).parent
        except ValueError:
            parent = None
        if parent and parent.split(".")[0] in heath.BOOKS:
            return parent
    m = MESSAGE_PATH.match(message)
    return owner(m.group(1)) if m else None


def captured(fn, *args):
    """Run one of check_fidelity's checks; return (its value, its failures)."""
    cf.errors.clear()
    value = fn(*args)
    found = list(cf.errors)
    cf.errors.clear()
    return value, found


def run(cmd: list[str], timeout: int = 1800) -> subprocess.CompletedProcess:
    try:
        return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired) as e:
        return subprocess.CompletedProcess(cmd, 127, "", str(e))


def home() -> str | None:
    """The home directory, which tail() writes as ~; None when it is unknown or is the
    filesystem's root."""
    try:
        path = Path.home()
    except (RuntimeError, KeyError):
        return None
    return str(path) if path.is_absolute() and len(path.parts) > 1 else None


HOME = home()


def tail(text: str, lines: int = 12) -> str:
    text = text.replace(str(ROOT), ".")
    if HOME:
        text = text.replace(HOME, "~")
    return "\n".join(text.strip().splitlines()[-lines:])


_commits: dict[str, str | None] = {}


def commit_problem(commit: str) -> str | None:
    """None when the commit is in this repository and HEAD descends from it; else why."""
    if commit not in _commits:
        if not heath.COMMIT.fullmatch(commit):
            _commits[commit] = "is not a commit (7 to 40 lower-case hex digits)"
        elif run(["git", "cat-file", "-e", f"{commit}^{{commit}}"]).returncode != 0:
            _commits[commit] = ("is not a commit of this repository (a shallow clone lacks "
                                "the history: fetch it in full)")
        elif run(["git", "merge-base", "--is-ancestor", commit, "HEAD"]).returncode != 0:
            _commits[commit] = "is not in the history of HEAD"
        else:
            _commits[commit] = None
    return _commits[commit]


# ---------------------------------------------------------------------------------------
# Lean names, asked of Lean (B2): the idea of leanblueprint's checkdecls.

def unknown_names(sections: list[tuple[str, list[str]]], imports: list[str]):
    """Ask Lean about names: each section is (the namespaces to open, the names), and a
    name is known if Lean knows it in any section that asks for it. Returns (the names
    Lean knows in none, None) or (None, why Lean could not be asked)."""
    lines = [f"import {m}" for m in imports]
    where: dict[int, str] = {}
    asked: set[str] = set()
    for opens, names in sections:
        lines += ["", "section", f"open {opens}"]
        for name in names:
            lines.append(f"#check @{name}")
            where[len(lines)] = name
            asked.add(name)
        lines.append("end")
    if not asked:
        return set(), None
    with tempfile.TemporaryDirectory() as tmp:
        probe = Path(tmp) / "AcceptanceNames.lean"
        probe.write_text("\n".join(lines) + "\n", encoding="utf-8")
        done = run(["lake", "env", "lean", str(probe)], timeout=900)
    out = (done.stdout + done.stderr).replace(str(probe), probe.name)
    errors = list(re.finditer(rf"{re.escape(probe.name)}:(\d+):\d+: error", out))
    if done.returncode != 0 and not errors:
        return None, "Lean could not be asked (is the tree built, Audit too?): " + tail(out, 4)
    if any(int(m.group(1)) not in where for m in errors):
        return None, "Lean failed before the names (build Audit: `lake build Audit`): " + tail(out, 4)
    failed: dict[str, int] = {}
    for m in errors:
        name = where[int(m.group(1))]
        failed[name] = failed.get(name, 0) + 1
    tries = {name: sum(1 for _, names in sections if name in names) for name in asked}
    return {name for name, k in failed.items() if k == tries[name]}, None


def catalogue_names(text: str, fields: set[str]) -> list[str]:
    """The backticked Lean names of a catalogue, less those that need no declaration."""
    return [n for n in check_style.lean_names(text)
            if not PLACEHOLDER.search(n) and n not in fields and n not in TACTICS]


# ---------------------------------------------------------------------------------------
# The machine's items.

def check_certificate(facts: dict) -> None:
    """check_fidelity's checks, each failure sorted to its item: Heath's text (P7), the
    house rules (P5), the lock and the axioms (E2), the entries (a proposition's P5, or
    its P8 or P9 for a missing figure or mishnah; E2 for those that name no one
    proposition), the pinned facts (E2) and the records (P2, P6)."""
    def sort(found: list[str], item: str) -> None:
        for msg in found:
            who = whose_message(msg)
            if who and not who.startswith("Book"):
                fail(who, item, msg)
            else:
                fail("edition", "E2", msg)

    sort(captured(cf.check_fidelity)[1], "P7")
    sort(captured(cf.check_rules)[1], "P5")
    count, found = captured(cf.check_lock, facts)
    _, more = captured(cf.check_axioms, facts, count)
    for msg in found + more:
        fail("edition", "E2", msg)
    by_ref, found = captured(cf.entries_by_ref, facts)
    _, more = captured(cf.check_entries, facts, by_ref)
    for msg in found + more:
        who = whose_message(msg)
        if who is None or who.startswith("Book"):
            fail("edition", "E2", msg)
        elif "is complete, but" in msg:
            continue                    # P1 reads the statuses itself
        elif msg.rstrip().endswith("is missing"):
            fail(who, "P8" if "figures/" in msg else "P9", msg)
        else:
            fail(who, "P5", msg)
    _, found = captured(cf.check_expectations, by_ref, cf.EXPECTATIONS, facts)
    for msg in found:
        fail("edition", "E2", msg)
    _, found = captured(cf.check_reviews, facts, by_ref)
    for msg in found:
        who = whose_message(msg)
        if who is None or who.startswith("Book"):
            fail("edition", "E2", msg)
        elif ("have no Lean beneath them" in msg or "does not begin a sentence" in msg
              or "`helper`" in msg):
            fail(who, "P6", msg)
        else:
            fail(who, "P2", msg)


def check_style_rules() -> None:
    """check_style.py as CI runs it, each failure sorted by the file it names: a
    proposition's review record to P9, whatever its rule. Each finding is quoted whole, as
    one code span."""
    done = run([PY, "scripts/check_style.py", "--quiet"])
    found = 0
    for line in done.stdout.splitlines():
        m = re.match(r"^\s*✗ (S\d+) (\S+?)(?::(\d+))?: (.*)$", line)
        if not m:
            continue
        found += 1
        rule, path, number, msg = m.groups()
        # The style check reads the report this run replaces, and E5 quotes its findings in
        # the new one. Each finding goes in whole, as one code span whose fence is one
        # backtick longer than the longest run of backticks in it, with a space inside each
        # end. S12 then finds no name in it, for the span opens with the rule and the file,
        # and S1, S7, S8 and the other text rules find nothing in quoted code; so no finding
        # on the old report comes back in the next one (issue #178). And a reader sees each
        # message exactly as the check printed it: GitHub takes no `<book>` for HTML and
        # sets no `2*a*b` in italic.
        text = f"{rule} {path}{':' + number if number else ''}: {msg}"
        fence = "`" * (max(map(len, re.findall(r"`+", text)), default=0) + 1)
        text = f"{fence} {text} {fence}"
        who = owner(path)
        if who is None:
            fail("edition", "E5", text)
        elif who.startswith("Book"):
            fail(who, "B2" if "gaps-book" in path else "B1", text)
        elif path.lstrip("./").startswith("review/"):
            fail(who, "P9", text)
        elif rule in TEXT_RULES:
            fail(who, "P7", text)
        elif rule in FIGURE_RULES:
            fail(who, "P8", text)
        else:
            fail(who, "P9", text)
    if done.returncode != 0 and not found:
        fail("edition", "E5", "check_style.py failed before its rules ran:\n" +
             tail(done.stdout + done.stderr))


def check_links() -> None:
    """check_links.py over every Markdown file, each broken link sorted by its file."""
    done = run([PY, "scripts/check_links.py"])
    found = 0
    for line in done.stdout.splitlines():
        m = re.match(r"^(\S+?):(\d+): (.*)$", line)
        if not m:
            continue
        found += 1
        path = m.group(1)
        who = owner(path)
        if who is None:
            fail("edition", "E5", f"broken link, {line}")
        elif who.startswith("Book"):
            fail(who, "B2" if "gaps-book" in path else "B1", f"broken link, {line}")
        else:
            fail(who, "P7", f"broken link, {line}")
    if done.returncode != 0 and not found:
        fail("edition", "E5", "check_links.py failed:\n" + tail(done.stdout + done.stderr))


def check_runs(quick: bool) -> None:
    """The edition-wide checks run as CI runs them: heath.py (E3), the kernel replay (E1)
    and the model tests (E4)."""
    done = run([PY, "scripts/heath.py"])
    if done.returncode != 0:
        fail("edition", "E3", "heath.py fails:\n" + tail(done.stdout + done.stderr))
    if quick:
        skip("edition", "E1", "--quick")
        skip("edition", "E4", "--quick")
        return
    done = run([PY, "scripts/check_kernel.py", "--self-test"])
    if done.returncode != 0:
        fail("edition", "E1", "check_kernel.py --self-test fails:\n"
             + tail(done.stdout + done.stderr))
    done = run([PY, "-I", "tests/model/run.py", "--fast"])
    if done.returncode != 0:
        fail("edition", "E4", "tests/model/run.py --fast fails:\n" + tail(done.stdout + done.stderr))


def load_records() -> dict:
    """ref -> its record (stamps not required, defaults filled in), or None; an
    unreadable record fails P2 here, once."""
    records = {}
    for book, n, ref in refs():
        try:
            records[ref] = heath.load_review(book, n, require_stamp=False)
        except heath.ReviewError as e:
            records[ref] = None
            fail(ref, "P2", str(e))
    return records


def record_problems(record: dict) -> list[str]:
    """Why a record is not a current record at the stage `full` (P2), beyond what
    check_fidelity says (the schema, the stamps, and a full record's reviewer and run):
    its stage, its commit and its item keys."""
    out = []
    rv = record["review"]
    if rv["stage"] != "full":
        out.append(f"the record is at the stage `{rv['stage']}`, not `full`: every substantive "
                   "passage is to be classified (review/SCHEMA.md, \"Two stages\")")
    if "commit" in rv:
        problem = commit_problem(rv["commit"])
        if problem:
            out.append(f"its commit {rv['commit']} {problem}")
    for key in sorted(set(rv["items"]) - set(REVIEW_ITEMS)):
        out.append(f"[review] items: `{key}` is not an item key of docs/ACCEPTANCE.md "
                   f"({', '.join(REVIEW_ITEMS)})")
    return out


def declares_departure(record: dict, terms: dict) -> bool:
    st, tags = record["statement"], record.get("representation", {}).get("tags", [])
    return (st["scope"] != "full" or record["route"]["kind"] != "euclid" or "overlap" in record
            or any(terms.get(t, {}).get("kind") == "scope" or t == "hypothesis-dropped"
                   for t in tags)
            or any(p["kind"] in ("different", "unformalized") for p in record["passage"]))


def mishnah_disclosures(book: str, n: int) -> list[str]:
    """Sentences of the mishnah, outside quotations and code, that say our statement or
    the Lean leaves something out."""
    path = ROOT / "mishnah" / book / f"{n:02d}.md"
    if not path.exists():
        return []
    raw = path.read_text(encoding="utf-8")
    text = check_style.blank_quotes(check_style.blank_code(check_style.straighten(raw)))
    found = []
    for off, sentence in check_style.sentences(text):
        if DISCLOSURE_SUBJECT.search(sentence) and DISCLOSURE.search(sentence):
            found.append(" ".join(raw[off:off + len(sentence)].split()))
    return found


def page_header(page: str) -> str:
    """The header row of the page's table under "What it rests on"."""
    _, _, rest = page.partition("## What it rests on")
    for line in rest.splitlines():
        if line.startswith("| |"):
            return line
    return ""


def staged() -> dict[str, list[str]]:
    """Every declaration under Staging/, by file: {path: [full names, without
    `Elements.`]}, read with its namespaces as check_fidelity reads Elements/."""
    decl = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
        r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+"
        r"([^\s:({\[]+)")
    out = {}
    for path in sorted((ROOT / "Staging").rglob("*.lean")):
        stack: list[list[str]] = []
        names = []
        for line in cf.without_comments(path.read_text(encoding="utf-8")).splitlines():
            m = re.match(r"^\s*(namespace|section|end)\b\s*(\S*)", line)
            if m:
                word, name = m.groups()
                if word == "namespace":
                    stack.append(name.split("."))
                elif word == "section":
                    stack.append([])
                elif stack:
                    stack.pop()
                continue
            m = decl.match(line)
            if m:
                full = ".".join([p for frame in stack for p in frame] + [m.group(1)])
                names.append(full[len("Elements."):] if full.startswith("Elements.") else full)
        out[path.relative_to(ROOT).as_posix()] = names
    return out


# A proposition's module, `Elements.Book<book>.Prop<n>`, or a module beneath it, once
# `cf.folded` has put it in NFKC and case-folded it (#200).
PROP_MODULE = re.compile(r"elements\.book([ivx]+)\.prop(\d+)(?=\.|$)")


def staged_imports(path: str) -> tuple[list[tuple[str, int]], list[int]]:
    """The propositions the staged file `path` imports, each as its book and number, and
    the line of each import the scan cannot read for certain. The imports are read as
    check_fidelity's rule 3 reads Book Zero's (`cf.imports`): from the file's bytes, in the
    Lean as `cf.read_lean` gives it, so that a comment or a string never makes one, and
    whitespace, a comment or a name in «…» never hides one; and a module is compared as
    that rule compares it, in NFKC and case-folded (`cf.folded`)."""
    code = cf.read_lean(cf.lean_text(ROOT / path))[0]
    imported, unread = [], []
    for offset, module in cf.imports(code):
        if module is None:
            unread.append(cf.line_of(code, offset))
        elif m := PROP_MODULE.match(cf.folded(module)):
            imported.append((m[1].upper(), int(m[2])))
    return imported, unread


def staged_refs(path: str, names: list[str]) -> set[str]:
    """The propositions of Books I-III a staged file's declarations are for: a name with
    `PropN` in it, under `Book<book>`; or, without one, in a file whose folder names the
    book, or which imports `PropN` of one book alone (the prototype of mixed angles
    declares `MixedAngles.Prop16.…` and imports `Elements.BookIII.Prop16`), its imports
    read by `staged_imports`."""
    imported, _ = staged_imports(path)
    folder = re.search(r"/Book([IVX]+)/", path)
    found = set()
    for name in names:
        prop = re.search(r"(?:^|\.)Prop(\d+)(?:\.|$)", name)
        if not prop:
            continue
        n = int(prop.group(1))
        book = re.search(r"(?:^|\.)Book([IVX]+)(?:\.|$)", name)
        books = {b for b, k in imported if k == n}
        b = book.group(1) if book else folder.group(1) if folder else (
            next(iter(books)) if len(books) == 1 else None)
        if b in heath.BOOKS and 1 <= n <= heath.BOOKS[b]:
            found.add(f"{b}.{n}")
    return found


def check_propositions(facts: dict, records: dict) -> None:
    """P1 to P10 for each proposition: what check_fidelity, check_style and check_links
    have not already said."""
    facts_by_ref = {p["ref"]: p for p in facts["propositions"]}
    terms = heath.load_terms()
    docs = render.load_axiom_docs()
    for book, n, ref in refs():
        p = facts_by_ref.get(ref)
        record = records.get(ref)
        attached = render.attached_entries(p, facts_by_ref)
        page_path = ROOT / "book" / book / f"{n:02d}.md"
        page = page_path.read_text(encoding="utf-8") if page_path.exists() else ""
        if not page:
            fail(ref, "P9", f"book/{book}/{n:02d}.md is missing")

        # P1: proved, with all it carries, each shown with its certificate.
        if not p:
            fail(ref, "P1", f"{ref} has no entry in facts.json")
        else:
            for e in [p] + attached:
                if e.get("status") != "proved":
                    fail(ref, "P1", f"{e['ref']} is {e.get('status')}, not proved: no `sorry` "
                         "may stand in it or beneath it")
            header = page_header(page)
            for e in attached:
                label = render.attached_label(e)
                if label not in header:
                    fail(ref, "P1", f"the page shows no certificate for {e['ref']}: its column "
                         f"{label} is not under \"What it rests on\"")
            listed = set(record["statement"]["companions"]) if record else set()
            for e in attached:
                if e.get("kind") == "companion" and e["ref"] not in listed:
                    fail(ref, "P1", f"the companion {e['ref']} is certified, but the record's "
                         "`companions` does not list it, so its scope is not counted")

        # P7: Heath's source note names the scan leaves, so that the page links the scans.
        if not render.SCAN_LEAVES.search(heath.read(book, n)[0]):
            fail(ref, "P7", f"heath/{book}/{n:02d}.md: its source note names no scan leaf, so "
                 "the page cannot link Heath's page images")

        if record is None:
            continue

        # P2: a current record at the stage `full`.
        for problem in record_problems(record):
            fail(ref, "P2", problem)

        # P3: full, or one of the limitations the checklist allows; no other argument.
        st, route = record["statement"], record["route"]
        tags = record.get("representation", {}).get("tags", [])
        allowed = ALLOWED_LIMITS.get(ref)
        if st["scope"] != "full":
            if not allowed or st["scope"] != allowed[0]:
                fail(ref, "P3", f"the statement is {st['scope']}: every statement of Books "
                     "I-III is full but for the limitations docs/ACCEPTANCE.md names")
            elif allowed[1] not in tags:
                fail(ref, "P3", f"a {allowed[0]} statement allowed only as `{allowed[1]}`, "
                     "and the record does not carry that tag")
        elif allowed:
            fail(ref, "P3", f"the statement is full, so its allowance as a {allowed[0]} "
                 f"statement with `{allowed[1]}` is stale: its row in ALLOWED_LIMITS and in "
                 "docs/ACCEPTANCE.md's table is to go")
        if route["kind"] == "alternative":
            fail(ref, "P3", "the route is an alternative argument, which is no deliberate "
                 "limitation of Books I-III: Euclid's own argument is due")

        # P4: every exception on the page, and none in the mishnah alone.
        if page:
            try:
                line = render.in_lean_line(p, record, book, n)
                table = render.field_table(book, n, p, record, attached, docs)
                cmap = render.clause_map(record)
            except Exception as e:      # a record render.py cannot show is a failure here
                fail(ref, "P4", f"render.py cannot show the record: {tail(str(e))}")
            else:
                if line not in page:
                    fail(ref, "P4", "the line under the enunciation is not the one the record "
                         "gives: regenerate the page (render.py)")
                if table not in page:
                    fail(ref, "P4", "the field table under \"In Lean\" is not the one the "
                         "record gives: regenerate the page (render.py)")
                if cmap and cmap not in page:
                    fail(ref, "P4", "the clause map is not on the page: regenerate it")
        if any(q["kind"] == "unformalized" for q in record["passage"]) and "coverage" not in record:
            fail(ref, "P4", "a passage is left unformalized, and the record has no [coverage] "
                 "clause map to say what stays in Euclid's words")
        if ref not in DISCLOSURE_EXCEPTIONS and not declares_departure(record, terms):
            for sentence in mishnah_disclosures(book, n):
                fail(ref, "P4", f"the mishnah discloses a departure the record does not "
                     f"declare: \"{sentence}\"")

        # P6: every passage note shown on the page.
        for q in record["passage"]:
            if q.get("note") and page and q["note"] not in page:
                fail(ref, "P6", f"the note of the passage at \"{q['at']}\" is not on the page")

        # P8: a figure of one case names it, when the theorem covers several.
        several = st["companions"] or any(q["kind"] == "case" for q in record["passage"])
        if several and not (record.get("figure") or {}).get("case"):
            fail(ref, "P8", "the theorem covers several cases (a `case` passage or a "
                 "companion), and [figure] gives no `case` for the caption to name")

    # P5: placement cited only by III.24 and the arcs.
    for path in sorted((ROOT / "Elements").rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        if rel.startswith(PLACEMENT_HOMES):
            continue
        code = cf.without_comments(path.read_text(encoding="utf-8"))
        m = PLACEMENT.search(code)
        if m:
            who = owner(rel)
            line = code[:m.start()].count("\n") + 1
            fail(who or "edition", "P5" if who else "E2",
                 f"{rel}:{line}: cites placement, which only III.24 and the theorems on arcs "
                 "may cite")

    check_staging()


def check_staging() -> None:
    """P10 and E6: nothing left in Staging. An import in a staged file that declares
    anything, which the scan cannot read for certain, fails E6, naming its file and line,
    since which propositions the file imports cannot then be told; it fails closed, and
    never lets a file pass."""
    for path, names in staged().items():
        if not names:
            continue
        for line in staged_imports(path)[1]:
            fail("edition", "E6", f"{path}:{line}: an import the scan cannot read for "
                 "certain, so which propositions this file imports cannot be told: each part of the module's name must be a plain name, in «…» or not, "
                 "and whitespace must follow it")
        found = staged_refs(path, names)
        for ref in sorted(found, key=heath.prop_key):
            fail(ref, "P10", f"{path} still stages declarations for {ref}: once proved, a "
                 "statement moves to Elements/ and its staged copy is deleted")
        if not found:
            fail("edition", "E6", f"{path} still stages {len(names)} declaration(s), for no "
                 "one proposition: move them to Elements/ or retire them")


def check_review_items(records: dict, facts: dict) -> None:
    """P11 to P16, from the records: each `pass` (or `n/a` where allowed), in a record at
    the stage `full` whose stamps are current."""
    facts_by_ref = {p["ref"]: p for p in facts["propositions"]}
    for book, n, ref in refs():
        record = records.get(ref)
        why = None
        if record is None:
            why = "the record cannot be read (P2)"
        elif record["review"]["stage"] != "full":
            why = f"the record is at the stage `{record['review']['stage']}` (P2)"
        elif not render.record_current(ref, record, facts_by_ref):
            why = "the record's stamps are not current (P2)"
        elif "commit" in record["review"] and commit_problem(record["review"]["commit"]):
            commit = record["review"]["commit"]
            why = f"the record's commit {commit} {commit_problem(commit)} (P2)"
        elif "commit" not in record["review"] or "," not in record["review"]["reviewer"]:
            why = "the record names no commit, or no reviewer with a role (P2)"
        for key, item in REVIEW_ITEMS.items():
            if why:
                fail(ref, item, f"not yet assessed: {why}")
                continue
            verdict = record["review"]["items"].get(key)
            ok = verdict == "pass" or (verdict == "n/a" and key in NA_ALLOWED)
            if not ok:
                fail(ref, item, f"[review] items: `{key}` is {verdict!r}, not \"pass\""
                     if verdict else f"[review] items: `{key}` is not recorded")


def check_books(facts: dict, records: dict) -> None:
    """B1 to B4 for each book, and E5's generated pages."""
    facts_by_ref = {p["ref"]: p for p in facts["propositions"]}
    shown = records                 # an unreadable record renders as unreviewed
    docs = render.load_axiom_docs()
    # The fields of facts.json, which a catalogue may name in backticks.
    fields = set(facts) | {k for p in facts["propositions"] for k in p}
    check_overlap_names(fields)

    def same(path: Path, make, who: str, item: str) -> None:
        try:
            want = make()
        except (Exception, SystemExit) as e:
            fail(who, item, f"render.py cannot write {path.relative_to(ROOT)}: {tail(str(e))}")
            return
        have = path.read_text(encoding="utf-8") if path.exists() else None
        if have != want:
            fail(who, item, f"{path.relative_to(ROOT).as_posix()} is not as render.py writes "
                 "it: regenerate it")

    # P9: each page regenerated clean.
    for book, n, ref in refs():
        count, titles = render.BOOKS[book]
        path = ROOT / "book" / book / f"{n:02d}.md"
        if path.exists():
            same(path, lambda: render.page(book, n, count, titles, facts_by_ref, docs, shown),
                 ref, "P9")

    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    try:
        filled = render.readme(readme, facts_by_ref, shown)
    except (Exception, SystemExit) as e:
        filled = None
        fail("edition", "E5", f"render.py cannot fill README.md's scope rows: {tail(str(e))}")
    regions = {m.group(2): m.group(0) for m in render.SCOPE_MARKERS.finditer(readme)}
    wanted = {m.group(2): m.group(0) for m in render.SCOPE_MARKERS.finditer(filled or "")}

    for book, (count, titles) in render.BOOKS.items():
        who = f"Book {book}"
        # B1: the book's pages and its completion summary.
        same(ROOT / "book" / book / "index.md",
             lambda: render.index(book, count, titles, facts_by_ref, shown), who, "B1")
        same(ROOT / "book" / book / "front.md", lambda: render.front(book), who, "B1")
        if book not in regions:
            fail(who, "B1", f"README.md has no <!-- scope:{book} --> markers for the book's "
                 "completion summary")
        elif filled is not None and regions[book] != wanted.get(book):
            fail(who, "B1", "README.md's completion summary for the book is not as render.py "
                 "writes it: regenerate it")

        # B2: the gap catalogue's Lean names, and the overlap catalogue's rows.
        gaps = ROOT / "docs" / "reports" / f"gaps-book-{book}.md"
        if not gaps.exists():
            fail(who, "B2", f"{gaps.relative_to(ROOT)} is missing")
        else:
            names = catalogue_names(gaps.read_text(encoding="utf-8"), fields)
            unknown, why = unknown_names(
                [(f"Elements Elements.Book{book} Elements.Tacit", names)], ["Elements"])
            if why:
                fail(who, "B2", f"{gaps.relative_to(ROOT)}: {why}")
            for name in sorted(unknown or ()):
                fail(who, "B2", f"{gaps.relative_to(ROOT)} names `{name}`, which Lean does not "
                     "know: the catalogue has fallen behind the Lean")
        check_overlap_rows(book, records, who)

        # B3 and B4: the book's acceptance record.
        check_book_record(book)

    # E5: the pages of the whole edition.
    same(ROOT / "CERTIFICATE.md", lambda: render.certificate(facts_by_ref, docs, shown),
         "edition", "E5")
    same(ROOT / "GRAPH.md", lambda: render.graph(facts_by_ref), "edition", "E5")
    program = render.PROGRAM.read_text(encoding="utf-8")
    same(render.PROGRAM, lambda: render.program_page(program, facts_by_ref, shown,
                                                     render.load_program()), "edition", "E5")


OVERLAPS = ROOT / "docs" / "reports" / "overlaps.md"


def overlap_table() -> list[tuple[str, str]]:
    """(the proposition, the row) for each row of the overlap catalogue's table whose first
    cell is the reference alone: that proposition's own overlap. The rows on a rule's use
    in other proofs ("I.13, a case of it, in 17 proofs from II.1 on") are read by no record,
    and not counted."""
    rows = []
    for line in OVERLAPS.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^\| \[([IVX]+\.\d+)\]\([^)]*\) \|(.*)$", line)
        if m:
            rows.append((m.group(1), m.group(2)))
    return rows


def check_overlap_names(fields: set[str]) -> None:
    """The Lean names of the overlap catalogue (its rules, its audit lemmas): each that
    Lean does not know, with Audit built, fails E2, since the catalogue serves every
    book."""
    if not OVERLAPS.exists():
        return
    names = catalogue_names(OVERLAPS.read_text(encoding="utf-8"), fields)
    sections = [(f"Elements Elements.Book{b} Elements.Tacit", names) for b in heath.BOOKS]
    unknown, why = unknown_names(sections, ["Elements", "Audit"])
    if why:
        fail("edition", "E2", f"docs/reports/overlaps.md: {why}")
    for name in sorted(unknown or ()):
        fail("edition", "E2", f"docs/reports/overlaps.md names `{name}`, which Lean does not "
             "know, with Audit built: the catalogue has fallen behind the Lean")


def check_overlap_rows(book: str, records: dict, who: str) -> None:
    """B2's overlap half: every record of the book with an [overlap] has a row of its own
    (`overlap_table`) naming its rules, and no such row is for a proposition whose record
    declares none. (The catalogue's Lean names are E2's: `check_overlap_names`.)"""
    if not OVERLAPS.exists():
        fail(who, "B2", "docs/reports/overlaps.md is missing")
        return
    rows = overlap_table()
    for _, n, ref in ((b, n, r) for b, n, r in refs() if b == book):
        record = records.get(ref)
        ov = record.get("overlap") if record else None
        mine = [row for r, row in rows if r == ref]
        if ov and not mine:
            fail(who, "B2", f"{ref}'s record declares an overlap with {ov['rule']}, and the "
                 "overlap catalogue has no row for it")
        for rule in ([ov["rule"]] + ov.get("also", [])) if ov else []:
            short = rule.split(".")[-1]
            if mine and not any(f"`{short}`" in row for row in mine):
                fail(who, "B2", f"the overlap catalogue's row for {ref} does not name "
                     f"`{short}`, the rule its record declares")
        if mine and not ov:
            fail(who, "B2", f"the overlap catalogue has a row for {ref}, and its record "
                 "declares no [overlap]")


BOOK_RECORD_KEYS = {"verdict", "reviewer", "commit", "evidence"}


def check_book_record(book: str) -> None:
    """B3 and B4, from docs/reports/acceptance/book-<book>.toml: for each, a verdict of
    "pass", a reviewer with a role, the commit read, and the report it rests on."""
    who = f"Book {book}"
    path = BOOK_RECORDS / f"book-{book}.toml"
    rel = path.relative_to(ROOT).as_posix()
    if not path.exists():
        for key, item in BOOK_REVIEW_ITEMS.items():
            fail(who, item, f"not yet recorded: {rel} does not exist")
        return
    try:
        data = heath._toml().loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        for item in BOOK_REVIEW_ITEMS.values():
            fail(who, item, f"{rel} cannot be read: {e}")
        return
    for section in sorted(set(data) - set(BOOK_REVIEW_ITEMS)):
        fail(who, "B3", f"{rel}: unknown section [{section}] (the sections are: "
             f"{', '.join(BOOK_REVIEW_ITEMS)})")
    for key, item in BOOK_REVIEW_ITEMS.items():
        t = data.get(key)
        if not isinstance(t, dict):
            fail(who, item, f"not yet recorded: {rel} has no [{key}]")
            continue
        for k in sorted(set(t) - BOOK_RECORD_KEYS):
            fail(who, item, f"{rel}: [{key}] has an unknown key `{k}`")
        for k in sorted(BOOK_RECORD_KEYS - set(t)):
            fail(who, item, f"{rel}: [{key}] has no `{k}`")
        if t.get("verdict", "pass") != "pass":
            fail(who, item, f"{rel}: [{key}] verdict is {t.get('verdict')!r}, not \"pass\"")
        if "reviewer" in t and "," not in str(t["reviewer"]):
            fail(who, item, f"{rel}: [{key}] reviewer names no role")
        if "commit" in t:
            problem = commit_problem(str(t["commit"]))
            if problem:
                fail(who, item, f"{rel}: [{key}] commit {t['commit']} {problem}")
        if "evidence" in t:
            # A path from the repository's root to a file it tracks: an absolute path, one
            # that climbs out with "..", or an untracked, ignored or git-internal file names
            # no file of the edition.
            given = Path(str(t["evidence"]))
            found = (ROOT / given).resolve()
            if (given.is_absolute() or not found.is_relative_to(ROOT) or not found.is_file()
                    or run(["git", "--literal-pathspecs", "ls-files", "--error-unmatch", "--",
                            found.relative_to(ROOT).as_posix()]).returncode != 0):
                fail(who, item, f"{rel}: [{key}] evidence {t['evidence']} is not a tracked "
                     "file of the repository (a path from its root, as docs/reports/…)")


# ---------------------------------------------------------------------------------------
# The report.

# The digits of the report's revision: heath.COMMIT's form (7 to 40), which the style
# check's S12 reads as a commit beside the word "Revision" (STYLE, section 8). Git's own
# short form varies with the clone and with core.abbrev, and a short form under 7 digits
# that begins with a letter is a name S12 puts to Lean (issue #178).
REVISION_DIGITS = 12


def revision(output: Path, *more: Path) -> str:
    """The commit whose files were read, with REVISION_DIGITS digits: HEAD, or, while
    HEAD's commits change nothing but the report, the commit before them, so that
    regenerating the report on the same files writes the same report. Any other change,
    staged, unstaged or untracked (a new book record, say), is noted as not yet
    committed; the files this run writes (`output` and `more`, the verdicts of --json)
    are not."""
    short = f"--short={REVISION_DIGITS}"
    head = run(["git", "rev-parse", short, "HEAD"])
    if head.returncode != 0:
        return "not a git checkout"
    reports = {REPORT.relative_to(ROOT).as_posix()}
    for path in (output, *more):
        try:
            reports.add(path.resolve().relative_to(ROOT).as_posix())
        except ValueError:
            pass
    commit = head.stdout.strip()
    while True:
        changed = run(["git", "diff", "--name-only", f"{commit}^", commit])
        parent = run(["git", "rev-parse", short, f"{commit}^"])
        if changed.returncode or parent.returncode or not changed.stdout.split() \
                or not set(changed.stdout.split()) <= reports:
            break
        commit = parent.stdout.strip()
    status = run(["git", "status", "--porcelain", "--untracked-files=all"])
    dirty = [ln for ln in status.stdout.splitlines() if ln[3:].strip() not in reports]
    return f"`{commit}`" + (", with changes not yet committed" if dirty else "")


def cell(where: str, item: str) -> str:
    if (where, item) in not_run:
        return "not run"
    return "✗" if (where, item) in failures else "✓"


def page_link(ref: str, up: str = "../../") -> str:
    b, n = ref.split(".")
    return f"[{ref}]({up}book/{b}/{int(n):02d}.md)"


def report(output: Path, facts: dict, quick: bool, more: tuple = ()) -> str:
    items = {i: (k, kind, label) for i, k, kind, label in PROP_ITEMS + BOOK_ITEMS + EDITION_ITEMS}
    total = len(failures)
    props = [ref for _, _, ref in refs()]
    clean = [r for r in props if not any(w == r for w, _ in failures)]
    out = ["<!-- Generated by scripts/check_acceptance.py. Do not edit by hand. -->",
           "# Acceptance of Books I–III: the report", "",
           "What [`scripts/check_acceptance.py`](../../scripts/check_acceptance.py) finds "
           "against [the acceptance checklist](../ACCEPTANCE.md), item by item: for each of "
           "the 99 propositions, for each book and for the edition as a whole. A [machine] "
           "item is checked by the script; a [review] item is read from the records, and "
           "passes only when a reviewer has recorded it. The checklist says what each item "
           "asks. ✓ passes; ✗ fails, and every failure is listed at the end.", "",
           f"- **Revision:** {revision(output, *more)}.",
           f"- **Lean:** facts.json as Lean {facts.get('lean_version', '?')} wrote it.",
           "- **Run:** " + ("`--quick`: the kernel replay (E1) and the model tests (E4) were "
                            "not run, and a check not run is not a pass."
                            if quick else "every item."), "",
           "## Summary", ""]
    if total == 0 and not not_run:
        out += ["**No failures.** Every item of the checklist passes.", ""]
    else:
        out += [f"**{total} failing item{'s' if total != 1 else ''}**"
                + (f", and {len(not_run)} not run" if not_run else "")
                + f". {len(clean)} of the 99 propositions pass every item of their own.", ""]
    out += ["Failing propositions, item by item:", "",
            "| Item | | Kind | " + " | ".join(f"Book {b}" for b in heath.BOOKS) + " |",
            "|---|---|---|" + "---|" * len(heath.BOOKS)]
    for item, key, kind, label in PROP_ITEMS:
        counts = []
        for b, c in heath.BOOKS.items():
            k = sum(1 for n in range(1, c + 1) if (f"{b}.{n}", item) in failures)
            counts.append(f"{k} of {c}")
        out.append(f"| {item} | {key}: {label} | {kind} | " + " | ".join(counts) + " |")
    out += ["", "## The whole edition", "", "| Item | | Kind | Result |", "|---|---|---|---|"]
    for item, key, kind, label in EDITION_ITEMS:
        out.append(f"| {item} | {key}: {label} | {kind} | {cell('edition', item)} |")
    if DISCLOSURE_EXCEPTIONS:
        out += ["", "Exceptions to P4's search of the mishnah, each with its reason:", ""]
        out += [f"- {ref}: {why}" for ref, why in sorted(DISCLOSURE_EXCEPTIONS.items(),
                                                       key=lambda x: heath.prop_key(x[0]))]
    out.append("")
    for book, count in heath.BOOKS.items():
        who = f"Book {book}"
        out += [f"## Book {book}", "", "| Item | | Kind | Result |", "|---|---|---|---|"]
        for item, key, kind, label in BOOK_ITEMS:
            out.append(f"| {item} | {key}: {label} | {kind} | {cell(who, item)} |")
        ids = [i for i, *_ in PROP_ITEMS]
        out += ["", "| | " + " | ".join(ids) + " |", "|---|" + "---|" * len(ids)]
        for n in range(1, count + 1):
            ref = f"{book}.{n}"
            out.append(f"| {page_link(ref)} | " + " | ".join(cell(ref, i) for i in ids) + " |")
        out.append("")
    out += ["## Every failure", ""]
    if not failures and not not_run:
        out += ["None.", ""]
    order = ["edition"] + [f"Book {b}" for b in heath.BOOKS] + props
    ids = [i for i, *_ in EDITION_ITEMS + BOOK_ITEMS + PROP_ITEMS]
    for where in order:
        mine = sorted((item for w, item in failures if w == where), key=ids.index)
        skipped = sorted((item for w, item in not_run if w == where), key=ids.index)
        if not mine and not skipped:
            continue
        title = "The whole edition" if where == "edition" else where
        out += [f"### {title}", ""]
        for item in skipped:
            out.append(f"- **{item} {items[item][0]}:** not run ({not_run[(where, item)]}).")
        review_waiting = [i for i in mine if items[i][1] == "review" and where in props
                          and all(m.startswith("not yet assessed") for m in failures[(where, i)])]
        if len(review_waiting) > 1:
            reason = failures[(where, review_waiting[0])][0]
            if all(failures[(where, i)] == [reason] for i in review_waiting):
                out.append(f"- **{review_waiting[0]}–{review_waiting[-1]} (the review items):** "
                           f"{reason}.")
                mine = [i for i in mine if i not in review_waiting]
        for item in mine:
            msgs = failures[(where, item)]
            head = f"- **{item} {items[item][0]}:**"
            if len(msgs) == 1 and "\n" not in msgs[0]:
                out.append(f"{head} {msgs[0]}")
                continue
            out.append(head)
            for msg in msgs:
                first, *rest = msg.splitlines()
                out.append(f"  - {first}")
                if rest:
                    out += ["", "    ```text"] + [f"    {line}" for line in rest] + ["    ```", ""]
        out.append("")
    return "\n".join(out).rstrip("\n") + "\n"


# ---------------------------------------------------------------------------------------
# The verdicts as JSON (--json), and the comparison of two runs (--compare), which CI's
# `acceptance` job in .github/workflows/ci.yml makes between main and a pull request.

VERDICTS_FORMAT = 1
VERDICT_WORDS = ("pass", "fail", "not run")

# The items --compare lists but does not hold when they turn from a pass into a fail. P10
# and E6 read Staging/ alone, and a statement that a stage adds or changes is staged before
# its proof (docs/WORKFLOW.md, section 2), so they turn into a fail exactly when a pull
# request stages something, as the workflow has it do. Only the full gate holds them. A
# pass of theirs that turns into "not run", or goes missing, is held like any other.
STAGING_ITEMS = ("P10", "E6")


def checker_id() -> str:
    """This copy of the script, by its bytes. --compare compares only verdicts that one
    copy wrote, so that main and the pull request are judged alike."""
    return "sha256:" + hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def cells() -> list[tuple[str, str]]:
    """Every item of every proposition, book and the edition, in the report's order, and
    any other a failure names."""
    out = [("edition", i) for i, *_ in EDITION_ITEMS]
    out += [(f"Book {b}", i) for b in heath.BOOKS for i, *_ in BOOK_ITEMS]
    out += [(ref, i) for _, _, ref in refs() for i, *_ in PROP_ITEMS]
    known = set(out)
    out += sorted((set(failures) | set(not_run)) - known)
    return out


def verdicts(output: Path, quick: bool, more: tuple = ()) -> dict:
    """Every item's verdict, "pass", "fail" or "not run", with the failure's messages or
    the reason it was not run."""
    result: dict = {"format": VERDICTS_FORMAT, "checker": checker_id(),
                    "revision": revision(output, *more).replace("`", ""),
                    "run": "--quick" if quick else "every item", "verdicts": {}, "notes": {}}
    for where, item in cells():
        verdict = cell(where, item)
        word = {"✓": "pass", "✗": "fail"}.get(verdict, verdict)
        result["verdicts"].setdefault(where, {})[item] = word
        if (where, item) in not_run:
            result["notes"].setdefault(where, {})[item] = [f"not run ({not_run[(where, item)]})"]
        elif (where, item) in failures:
            result["notes"].setdefault(where, {})[item] = list(failures[(where, item)])
    return result


def read_verdicts(path: Path) -> dict:
    """A file that --json wrote; ValueError, saying why, for anything else."""
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as e:
        raise ValueError(f"{path} cannot be read as JSON ({e})")
    table = data.get("verdicts") if isinstance(data, dict) else None
    if not isinstance(data, dict) or data.get("format") != VERDICTS_FORMAT \
            or not isinstance(data.get("checker"), str) or not isinstance(table, dict) \
            or not all(isinstance(items, dict) and all(v in VERDICT_WORDS for v in items.values())
                       for items in table.values()):
        raise ValueError(f"{path} is not a file of verdicts that check_acceptance.py --json "
                         f"writes (format {VERDICTS_FORMAT})")
    if not isinstance(data.get("notes"), dict):
        data["notes"] = {}
    return data


def place(where: str, item: str) -> tuple:
    """The report's order: the edition, the books, then the propositions; items in their
    lists' order."""
    ids = [i for i, *_ in EDITION_ITEMS + BOOK_ITEMS + PROP_ITEMS]
    rank = ids.index(item) if item in ids else len(ids)
    if where == "edition":
        return (0, (), rank, item)
    if where.startswith("Book "):
        return (1, (where,), rank, item)
    try:
        key = tuple(heath.prop_key(where))
    except (ValueError, KeyError, IndexError, TypeError):
        key = (where,)
    return (2, key, rank, item)


def regressions(before: dict, after: dict) -> list[tuple[str, str, str]]:
    """Each item that passes in `before` and does not in `after`: (where, item, its
    verdict in `after`, or "missing" when `after` has none). A check not run is not a
    pass, so a pass that turns into "not run" is one."""
    lost = []
    for where, items in before["verdicts"].items():
        for item, verdict in items.items():
            now = after["verdicts"].get(where, {}).get(item, "missing")
            if verdict == "pass" and now != "pass":
                lost.append((where, item, now))
    return sorted(lost, key=lambda x: place(x[0], x[1]))


def compare(before_path: Path, after_path: Path) -> int:
    """--compare: 0 when every item that passes in the first file passes in the second,
    save the staging items' fails (STAGING_ITEMS), which are listed; 1 when one does not,
    each listed with why; 2 when either is not a file of verdicts, or the two came from
    different copies of this script."""
    try:
        before, after = read_verdicts(before_path), read_verdicts(after_path)
    except ValueError as e:
        print(f"✗ acceptance: {e}")
        return 2
    if before["checker"] != after["checker"]:
        print("✗ acceptance: the two files of verdicts were written by different copies of "
              "check_acceptance.py, which need not judge alike: run one copy on both trees")
        return 2
    labels = {i: key for i, key, *_ in PROP_ITEMS + BOOK_ITEMS + EDITION_ITEMS}

    def show(cells) -> None:
        for where, item, now in cells:
            notes = after["notes"].get(where, {}).get(item) if isinstance(
                after["notes"].get(where), dict) else None
            why = str(notes[0]).splitlines()[0] if isinstance(notes, list) and notes else ""
            label = f" {labels[item]}" if item in labels else ""
            print(f"  {where}, {item}{label}: {now}" + (f": {why}" if why else ""))

    lost = regressions(before, after)
    staged = [x for x in lost if x[1] in STAGING_ITEMS and x[2] == "fail"]
    lost = [x for x in lost if x not in staged]
    passing = sum(v == "pass" for items in before["verdicts"].values() for v in items.values())
    gained = sum(v == "pass" and before["verdicts"].get(w, {}).get(i) != "pass"
                 for w, items in after["verdicts"].items() for i, v in items.items())
    rest = sum(v != "pass" for items in after["verdicts"].values() for v in items.values())
    first = f"main ({before.get('revision', '?')})"
    second = f"the pull request ({after.get('revision', '?')})"
    if lost:
        one = len(lost) == 1
        print(f"✗ acceptance: {len(lost)} item{'' if one else 's'} that pass{'es' if one else ''} "
              f"on {first} {'does' if one else 'do'} not pass on {second}; a pass may not "
              "turn into a fail:")
        show(lost)
    if staged:
        one = len(staged) == 1
        print(f"{'Besides, n' if lost else 'N'}ot held: {len(staged)} staging "
              f"item{'' if one else 's'} that pass{'es' if one else ''} on {first} and "
              f"fail{'s' if one else ''} on {second}, for what it stages, as a statement is "
              "staged before its proof (docs/WORKFLOW.md, section 2); only the full gate "
              f"holds {'it' if one else 'them'}:")
        show(staged)
    if lost:
        print("Every failure, with what to do about it, is in the pull request's report.")
        return 1
    print(f"✓ acceptance: no item that passes on {first} fails on {second}"
          + ((", save the staging item above" if len(staged) == 1 else
              ", save the staging items above") if staged else "")
          + f": {passing - len(staged)} pass on both, {gained} more pass on the pull request, "
          f"and {rest} still fail or were not run there")
    return 0


# ---------------------------------------------------------------------------------------

def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--quick", action="store_true",
                        help="skip the kernel replay (E1) and the model tests (E4), "
                             "reporting each as not run")
    parser.add_argument("--output", type=Path, default=REPORT,
                        help="where to write the report (default: %(default)s)")
    parser.add_argument("--json", type=Path, metavar="PATH",
                        help="write every item's verdict to PATH as well, as JSON, for "
                             "--compare")
    parser.add_argument("--compare", type=Path, nargs=2, metavar=("MAIN", "PR"),
                        help="run no check: exit 1 when an item that passes in MAIN does "
                             "not pass in PR, save a staging item's fail (P10, E6), two "
                             "files that --json wrote")
    args = parser.parse_args(argv)
    if args.compare:
        if args.quick or args.json or args.output != REPORT:
            parser.error("--compare runs no check, and takes no other option")
        return compare(*args.compare)

    facts_path = ROOT / "facts.json"
    if not facts_path.exists():
        print("facts.json is missing: run `lake build` and `lake env lean "
              "Certificate/Facts.lean` first")
        return 2
    try:
        heath._toml()
    except RuntimeError as e:
        print(e)
        return 2
    facts = json.loads(facts_path.read_text(encoding="utf-8"))

    check_certificate(facts)
    records = load_records()
    check_propositions(facts, records)
    check_review_items(records, facts)
    check_books(facts, records)
    check_style_rules()
    check_links()
    check_runs(args.quick)

    more = (args.json,) if args.json else ()
    text = report(args.output, facts, args.quick, more)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text, encoding="utf-8")
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(verdicts(args.output, args.quick, more), indent=1,
                                        ensure_ascii=False) + "\n", encoding="utf-8")
    try:
        shown = args.output.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        shown = str(args.output)
    by_kind = {"machine": 0, "review": 0}
    kinds = {i: kind for i, _, kind, _ in PROP_ITEMS + BOOK_ITEMS + EDITION_ITEMS}
    for _, item in failures:
        by_kind[kinds[item]] += 1
    if failures or not_run:
        print(f"✗ acceptance: {len(failures)} failing item(s), {by_kind['machine']} [machine] "
              f"and {by_kind['review']} [review]" + (f", and {len(not_run)} not run"
                                                    if not_run else "")
              + f"; every failure is in {shown}")
        return 1
    print(f"✓ acceptance: every item of docs/ACCEPTANCE.md passes for Books I–III ({shown})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
