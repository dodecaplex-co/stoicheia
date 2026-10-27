"""Read Heath's text (heath/<book>/NN.md) into enunciation + proof paragraphs, and keep
the small contracts the other scripts share:

* references: `parse_ref`, `prop_key` ("I.40", "III.1 Por.", "I.40 general");
* Heath's porisms: `heath_porisms`, `heath_porism`;
* the main theorem of a Lean file: `theorem_span`;
* fingerprints of statements, files and records: `fingerprint`, `review_fingerprint`,
  `file_hash`, `text_hash`;
* the review records, review/<book>/NN.toml: `load_review`, `validate_review`,
  `load_terms` (the schema is review/SCHEMA.md);
* Lean read as Lean 4.35's tokenizer reads it, its comments, literals and names:
  `read_lean`, `without_comments`, `lean_comments` and `comment_end` (#206, #349);
* what is generated, the one account of it: `GENERATED_WHOLE`, the files generated whole
  (facts.json, which `lake env lean Certificate/Facts.lean` writes, and book/,
  CERTIFICATE.md and GRAPH.md, which render.py writes), and `REGIONS`, the files render.py
  writes only between markers, with `RegionError`, `regions`, `outside`, `bodies` and
  `fill`, which read them; and the inline counts' markers (#578).

Shared by scaffold_book.py, check_fidelity.py and render.py, and the generated regions also
by safe_push.py, check_queue.py, generated_counts.py and negative_tests.py. Standard
library only. Reading review records needs Python 3.11 or later, for tomllib; the rest runs
on older Pythons too. `python3 scripts/heath.py` checks the
contracts against themselves: the examples in review/SCHEMA.md, review/terms.toml and
every review record present; and that the reader of Lean reads deep and long runs of
string holes in under half a second each (`READER_PLANTS`, #390), and refuses as quickly
strings nested past their budget (`READER_REFUSED`); and that it reads a name on through a
`.` after its «…» part as Lean does, and marks a raw string after `℃.` as one it cannot
read for certain (`READER_NAMES`, #430); and that today's README.md, docs/PROGRAM.md and
docs/WORKFLOW.md hold their regions as `regions` requires, that a hand deletion inside a
region leaves the part written by hand as it was, that one outside every region's body is
refused or seen, and that `fill` refuses a write that reaches outside a body
(`REGION_PLANTS`, #578).
"""

from __future__ import annotations

import bisect
import functools
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import NamedTuple


def _toml():
    """tomllib, imported only where a record is read, so that the scripts which never
    read one still run on a Python older than 3.11."""
    try:
        import tomllib
    except ModuleNotFoundError:
        raise RuntimeError("reading review records needs Python 3.11 or later (tomllib)") from None
    return tomllib

ROOT = Path(__file__).resolve().parent.parent

HTML_COMMENT = re.compile(r"<!--.*?-->", re.S)
CITATION = re.compile(r"\[([^\[\]]*?)\]")


def heath_path(book: str, n: int) -> Path:
    return ROOT / "heath" / book / f"{n:02d}.md"


def read(book: str, n: int):
    """Return (source_comment, enunciation, [proof paragraphs])."""
    raw = heath_path(book, n).read_text()
    source = ""
    m = HTML_COMMENT.match(raw.strip())
    if m:
        source = m.group(0)[4:-3].strip()
    text = HTML_COMMENT.sub("", raw)
    paras = [p.strip() for p in text.split("\n\n") if p.strip()]
    paras = [" ".join(p.split()) for p in paras if not p.startswith("# ")]
    enunciation = paras[0].replace("*", "").strip()
    return source, enunciation, paras[1:]


def bracketed(book: str, n: int) -> bool:
    """Is the whole proposition in Heath's square brackets, as III. 12 is? He prints the
    opening bracket before the heading ("[Proposition 12."), which `read` leaves out with
    the heading; the closing one follows "Q. E. D." and stays in the proof."""
    text = HTML_COMMENT.sub("", heath_path(book, n).read_text())
    return any(line.startswith("# [") for line in text.splitlines())


ROMAN = ["I", "II", "III", "IV", "V", "VI", "VII", "VIII", "IX", "X", "XI", "XII", "XIII"]

# The books carried into Lean so far, and how many propositions each has.
# `Certificate/Facts.lean` keeps the same list.
BOOKS = {"I": 48, "II": 14, "III": 37}


def arabic(book: str) -> int:
    """The number of a book from its Roman numeral: "I" is 1, "II" is 2, "XIII" is 13."""
    return ROMAN.index(book) + 1


# What a reference names: a proposition ("I.40"), its porism ("III.1 Por."), or a
# companion theorem beside it ("I.40 general", for `Prop40.general`). This order is the
# third place of `prop_key`.
KINDS = ("proposition", "porism", "companion")

REF = re.compile(r"([IVX]+)\.\s*(\d+)(?:(?:,\s*|\s+)(Por\.)|\s+([A-Za-z_][\w']*))?")


class Ref(NamedTuple):
    """A reference taken apart: `parse_ref("III.1 Por.")` is
    `Ref(book="III", n=1, kind="porism", name="porism")`.

    `name` is the last part of the Lean declaration's name: None for the proposition
    itself (`Prop1`), "porism" for its porism (`Prop1.porism`), and the companion's own
    name for a companion ("general" for `Prop40.general`). `str()` gives the reference
    back in its one written form: "III.1", "III.1 Por.", "I.40 general"."""
    book: str
    n: int
    kind: str
    name: str | None

    def __str__(self) -> str:
        base = f"{self.book}.{self.n}"
        if self.kind == "porism":
            return f"{base} Por."
        if self.kind == "companion":
            return f"{base} {self.name}"
        return base

    @property
    def parent(self) -> str:
        """The proposition this belongs to: "III.1" for "III.1 Por." and for "III.1"."""
        return f"{self.book}.{self.n}"

    @property
    def lean(self) -> str:
        """The Lean declaration: "Elements.BookIII.Prop1.porism" for "III.1 Por."."""
        base = f"Elements.Book{self.book}.Prop{self.n}"
        return f"{base}.{self.name}" if self.name else base


def parse_ref(ref: str) -> Ref:
    """Take apart a reference: "I.40", "III.1 Por." or "I.40 general".

    Heath's spacing and comma are accepted too ("I. 4", "III. 1, Por."); `str()` of the
    result is the written form. A porism is always "Por.", never a companion called
    "porism". Raises ValueError on anything else."""
    m = REF.fullmatch(ref.strip())
    if not m:
        raise ValueError(f"not a reference: {ref!r} (expected one like 'I.40', "
                         "'III.1 Por.' or 'I.40 general')")
    book, num, porism, name = m.groups()
    if book not in ROMAN:
        raise ValueError(f"not a reference: {ref!r} ({book} is not a book of the Elements)")
    n = int(num)
    if n < 1:
        raise ValueError(f"not a reference: {ref!r} (propositions are numbered from 1)")
    if porism:
        return Ref(book, n, "porism", "porism")
    if name:
        if name.lower() in ("por", "porism"):
            raise ValueError(f"not a reference: {ref!r} (a porism is written "
                             f"'{book}.{n} Por.')")
        return Ref(book, n, "companion", name)
    return Ref(book, n, "proposition", None)


def prop_key(ref: "str | Ref"):
    """Sort references by book, then by number, then the proposition before its porism
    and its porism before its companions: I.3 before I.10, I.48 before II.1, IX before
    X, and III.1 before III.1 Por. before III.1 general.

    The key is (arabic(book), n, 0 | 1 | 2). Two companions of one proposition share a
    key: sort by `(prop_key(r), r)` for a fixed order among them."""
    r = ref if isinstance(ref, Ref) else parse_ref(ref)
    return (arabic(r.book), r.n, KINDS.index(r.kind))


def normalize(s: str) -> str:
    return " ".join(s.split())


def citations(paragraphs):
    """Propositions Euclid cites, e.g. {"I.4", "II.6"} from "[I. 4]", "[C.N. 1; II. 6]".

    A porism is cited with its proposition: "[III. 1, Por.]" cites III.1."""
    found = set()
    for p in paragraphs:
        for inner in CITATION.findall(p):
            for part in inner.split(";"):
                part = part.strip()
                m = re.fullmatch(r"([IVX]+)\.\s*(\d+)(?:,\s*Por\.)?", part)
                if m:
                    found.add(f"{m.group(1)}.{int(m.group(2))}")
    return found


# A justification in a bracket: a proposition ("I. 4"), or a postulate, definition or
# common notion, which a later book may cite with its book ("I. Post. 5", "I. Def. 15").
JUSTIFICATION = re.compile(
    r"(?:([IVX]+)\.\s*)?(Post\.|Def\.|C\.N\.)\s*(\d+)|([IVX]+)\.\s*(\d+)(?:,\s*Por\.)?")


def justifications(paragraphs):
    """Every bracketed justification Euclid gives: Post. 3, Def. 15, C.N. 1, I. 4 …

    A bracket may hold several, as "[C.N. 1; I. 30]" or "[Post. 4 and C.N. 1]".
    Book II cites Book I's Postulate 5 as "[I. Post. 5]". The postulates and common
    notions are Book I's alone, so that is Post. 5; definitions are numbered book by
    book, so "[I. Def. 15]" in a later book stays "I. Def. 15". A porism counts as its
    proposition: "[III. 16, Por.]" is III. 16.
    """
    found = []
    for p in paragraphs:
        for inner in CITATION.findall(p):
            for part in re.split(r";|\band\b", inner):
                m = JUSTIFICATION.fullmatch(" ".join(part.split()))
                if not m:
                    continue
                book, kind, num, pbook, pnum = m.groups()
                if pbook:
                    part = f"{pbook}. {int(pnum)}"
                elif book and kind == "Def.":
                    part = f"{book}. Def. {int(num)}"
                else:
                    part = f"{kind} {int(num)}"
                if part not in found:
                    found.append(part)
    return found


# Heath's porisms. A porism is a paragraph of the proof that opens "PORISM.", or
# "[PORISM." where Heath brackets it as probably interpolated (I.15).

PORISM = re.compile(r"\[?PORISM\.")


def heath_porism(book: str, n: int) -> str | None:
    """Heath's porism to proposition n of the book, the paragraph as he prints it (I.15's
    in his square brackets), or None if he prints none."""
    _, _, proof = read(book, n)
    return next((p for p in proof if PORISM.match(p)), None)


def heath_porisms() -> frozenset:
    """Every (book, n) in `BOOKS` whose proof in Heath has a porism paragraph: in Books
    I-III, ("I", 15), ("III", 1) and ("III", 16)."""
    return frozenset((book, n) for book, count in BOOKS.items()
                     for n in range(1, count + 1) if heath_porism(book, n))


# The main theorem of a proposition's Lean file.

class TheoremSpan(NamedTuple):
    """Where `theorem PropN` lies in the text `src` of its Lean file.

    `src[start:end]` is the whole declaration, from its docstring's `/--` to the next
    top-level declaration, the namespace's `end` or the end of the file;
    `src[body:end]` is what follows `theorem PropN` and the one blank after it: the
    statement and the proof; `doc` is the docstring's text, between `/--` and `-/`.
    Before `start` come the file's header and its helpers; from `end` on, the porism,
    the companions and anything else after the main theorem."""
    start: int
    body: int
    end: int
    doc: str


def theorem_span(src: str, n: int) -> TheoremSpan | None:
    """Find the documented `theorem PropN` in `src`; None if there is none."""
    m = re.search(r"/--((?:(?!-/).)*?)-/\s*theorem Prop%d\s" % n, src, re.S)
    if not m:
        return None
    # The theorem runs until the next top-level declaration or the namespace end.
    rest = src[m.end():]
    stop = re.search(r"^(end |theorem |lemma |def |structure |/--|/-!|@\[)", rest, re.M)
    end = m.end() + (stop.start() if stop else len(rest))
    return TheoremSpan(m.start(), m.end(), end, m.group(1))


def lean_path(book: str, n: int) -> Path:
    """The Lean file of a proposition, which also holds its porism and companions."""
    return ROOT / "Elements" / f"Book{book}" / f"Prop{n:02d}.lean"


# Fingerprints: "sha256:" and the first 16 hex digits of a SHA-256.

HASH = re.compile(r"sha256:[0-9a-f]{16}")


def _sha(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()[:16]


def fingerprint(*statements: str) -> str:
    """A short hash of one or more printed statements, whitespace aside: each statement
    with its runs of whitespace made one space, joined by newlines."""
    return _sha("\n".join(normalize(s) for s in statements).encode())


def review_fingerprint(facts: dict, ref: str) -> str:
    """The `fingerprint` a review record of the proposition `ref` must carry: of the
    `statement` of its facts.json entry, then those of its `attached` entries (its
    porism, then its companions) in the order listed. A change to any of them is a
    change to what the record reviewed (Certificate/FIELDS.md, review/SCHEMA.md)."""
    by_ref = {p["ref"]: p for p in facts["propositions"]}
    entries = [by_ref[ref]] + [by_ref[a] for a in by_ref[ref].get("attached", [])]
    missing = [e["ref"] for e in entries if "statement" not in e]
    if missing:
        raise KeyError(f"facts.json has no `statement` for {', '.join(missing)}: rerun "
                       "`lake env lean Certificate/Facts.lean`")
    return fingerprint(*(e["statement"] for e in entries))


def file_hash(path) -> str:
    """A short hash of a file's exact bytes, in the form `fingerprint` uses. A review
    record's `lean` is the file_hash of `lean_path(book, n)`."""
    return _sha(Path(path).read_bytes())


def text_hash(source: str) -> str:
    """A review record's `text` stamp: a short hash of what the record says, read from
    `source`, its TOML. Every section counts but [review], which holds the stamps and the
    reviewer's account of the reading, and [statement] counts without its `fingerprint`,
    a stamp of the statements; so writing a stamp never changes the text it stamps.
    Comments, layout and the order of keys do not count: the record as TOML reads it is
    written as JSON with its keys sorted, and hashed. Raises ValueError when `source` is
    not valid TOML."""
    tomllib = _toml()
    try:
        record = tomllib.loads(source)
    except tomllib.TOMLDecodeError as e:
        raise ValueError(f"not valid TOML: {e}") from None
    record.pop("review", None)
    if isinstance(record.get("statement"), dict):
        record["statement"].pop("fingerprint", None)
    return _sha(json.dumps(record, sort_keys=True, ensure_ascii=False, separators=(",", ":"),
                           default=str).encode())


# The review records, review/<book>/NN.toml. review/SCHEMA.md says what each field
# means; this is the machine's half of it.

REVIEW = ROOT / "review"
NOTE_LIMIT = 160  # characters in [statement] note, shown in the page's field table
SHORT_LIMIT = 70  # characters in [statement] short, which stands beside the badge
SCOPES = ("full", "restricted", "partial")
ROUTES = ("euclid", "modified", "alternative")
PASSAGES = ("carried", "helper", "grouped", "case", "given", "different", "unformalized")
OVERLAPS = ("states", "gives", "step")  # [overlap] kind, the catalogue's three kinds
STAGES = ("exceptions", "full")
VERDICTS = ("pass", "fail", "n/a")
TAG_KINDS = ("scope", "representation")
COMMIT = re.compile(r"[0-9a-f]{7,40}")
WORD = re.compile(r"[a-z][a-z0-9]*(?:-[a-z0-9]+)*")
# A name as a proof binds it, for a passage's `unused`: one Lean identifier, with no dots,
# as `hCHG_EHC` or `FC`, or `this`, the name of a `have` that gives none.
BOUND_NAME = re.compile(r"[^\W\d][\w'!?₀-₉]*")

_STR, _LIST, _TABLE, _NAMES, _BOOL = "string", "list", "table", "names", "boolean"
# Each section's keys, as (type, required). A "stamp" key is written by
# scripts/review_stamp.py, and required unless an unstamped record is asked for.
# [review] `text` is a stamp too, but not yet required: the records stamped before it
# gain it from `review_stamp.py --migrate-text`, or from a reader (docs/WORKFLOW.md,
# section 6), and it becomes "stamp" once every record carries it.
FIELDS = {
    "statement": {"scope": (_STR, True), "hypotheses": (_LIST, False),
                  "omitted": (_LIST, False), "note": (_STR, False),
                  "short": (_STR, False), "fingerprint": (_STR, "stamp"),
                  "companions": (_LIST, False)},
    "route": {"kind": (_STR, True), "note": (_STR, False)},
    "representation": {"tags": (_LIST, True), "note": (_STR, False)},
    "overlap": {"rule": (_STR, True), "also": (_LIST, False), "kind": (_STR, True),
                "note": (_STR, False)},
    "coverage": {"checked": (_LIST, False), "explains": (_LIST, False),
                 "text_only": (_LIST, False)},
    "passage": {"at": (_STR, True), "kind": (_STR, True), "helper": (_STR, False),
                "note": (_STR, False), "unused": (_NAMES, False)},
    "figure": {"case": (_STR, False), "every_case": (_BOOL, False),
               "some_cases": (_BOOL, False), "note": (_STR, False)},
    "review": {"stage": (_STR, True), "commit": (_STR, "stamp"), "lean": (_STR, "stamp"),
               "text": (_STR, False), "reviewer": (_STR, True), "run": (_STR, False),
               "items": (_TABLE, False)},
}
REQUIRED = ("statement", "route", "review")


class ReviewError(ValueError):
    """A review record (or review/terms.toml) that is missing, unreadable or breaks
    review/SCHEMA.md. `where` is the file, `problems` each fault found in it."""

    def __init__(self, where: str, problems: list[str]):
        self.where, self.problems = where, problems
        detail = problems[0] if len(problems) == 1 else "".join(f"\n  - {p}" for p in problems)
        super().__init__(f"{where}: {detail}")


def review_path(book: str, n: int) -> Path:
    return REVIEW / book / f"{n:02d}.toml"


def _rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def load_terms() -> dict:
    """review/terms.toml: the tags a record's [representation] may carry, as
    {tag: {"kind": "scope" | "representation", "meaning": "one line"}}, and, for a tag
    that changes how a whole statement is read, a few words to stand beside the badge,
    `badge`."""
    path = REVIEW / "terms.toml"
    tomllib = _toml()
    try:
        data = tomllib.loads(path.read_text())
    except (OSError, tomllib.TOMLDecodeError) as e:
        raise ReviewError(_rel(path), [str(e)]) from None
    tags = data.get("tag")
    if set(data) != {"tag"} or not isinstance(tags, dict) or not tags:
        raise ReviewError(_rel(path), ["expected [tag.<name>] tables and nothing else"])
    problems = []
    for name, t in tags.items():
        if not WORD.fullmatch(name):
            problems.append(f"tag {name!r}: a tag is lower-case words joined by hyphens")
        if not isinstance(t, dict) or not {"kind", "meaning"} <= set(t) <= {
                "kind", "meaning", "badge"}:
            problems.append(f"tag {name!r}: needs `kind` and `meaning`, may have `badge`, "
                            "and nothing else")
            continue
        if "badge" in t and (not isinstance(t["badge"], str) or not t["badge"].strip()
                             or "\n" in t["badge"] or len(t["badge"]) > SHORT_LIMIT):
            problems.append(f"tag {name!r}: `badge` is a few plain words on one line, at "
                            f"most {SHORT_LIMIT} characters")
        if t["kind"] not in TAG_KINDS:
            problems.append(f"tag {name!r}: `kind` is one of {', '.join(TAG_KINDS)}")
        if not isinstance(t["meaning"], str) or not t["meaning"].strip() or "\n" in t["meaning"]:
            problems.append(f"tag {name!r}: `meaning` is one line of plain words")
    if problems:
        raise ReviewError(_rel(path), problems)
    return tags


def _shape(record, require_stamp: bool) -> list[str]:
    """The faults of form: unknown or missing sections and keys, and wrong types."""
    problems = []
    bad = problems.append
    if not isinstance(record, dict):
        return ["a record is a TOML table"]
    for section in record:
        if section not in FIELDS:
            bad(f"unknown section [{section}] (the sections are: {', '.join(FIELDS)})")
    for section in REQUIRED:
        if section not in record:
            bad(f"[{section}] is missing")
    tables = []
    for section, fields in FIELDS.items():
        value = record.get(section)
        if value is None:
            continue
        if section == "passage":
            if isinstance(value, list) and all(isinstance(t, dict) for t in value):
                tables += [(f"[[passage]] {i}", t, fields) for i, t in enumerate(value, 1)]
            else:
                bad("passages are an array of tables: write each as [[passage]]")
        elif isinstance(value, dict):
            tables.append((f"[{section}]", value, fields))
        else:
            bad(f"[{section}] must be a table")
    for label, table, fields in tables:
        for key in table:
            if key not in fields:
                bad(f"{label}: unknown key `{key}` (the keys are: {', '.join(fields)})")
        for key, (kind, required) in fields.items():
            if key not in table:
                if required is True:
                    bad(f"{label}: `{key}` is missing")
                elif required == "stamp" and require_stamp:
                    bad(f"{label}: `{key}` is missing (scripts/review_stamp.py writes it)")
                continue
            v = table[key]
            if kind == _STR and not (isinstance(v, str) and v.strip()):
                bad(f"{label}: `{key}` must be a non-empty string")
            elif kind == _LIST and not (isinstance(v, list)
                                        and all(isinstance(x, str) and x.strip() for x in v)):
                bad(f"{label}: `{key}` must be a list of non-empty strings")
            elif kind == _TABLE and not isinstance(v, dict):
                bad(f"{label}: `{key}` must be a table")
            elif kind == _NAMES:
                if not (isinstance(v, list) and v and all(isinstance(x, str) for x in v)):
                    bad(f"{label}: `{key}` must be a non-empty list of names; leave it out "
                        "when there are none")
                    continue
                for x in v:
                    if x == "_" or not BOUND_NAME.fullmatch(x):
                        bad(f"{label}: `{key}`: {x!r} is not a name as a proof binds it: one "
                            "Lean identifier, as 'hAB_FC' or 'FC', or 'this' for a `have` "
                            "that gives no name")
                for x in sorted({x for x in v if v.count(x) > 1}):
                    bad(f"{label}: `{key}` lists {x!r} twice")
            elif kind == _BOOL and not isinstance(v, bool):
                bad(f"{label}: `{key}` must be true or false")
    return problems


def validate_review(record: dict, book: str, n: int, *, require_stamp: bool = True,
                    where: str | None = None) -> dict:
    """Check a parsed review record of proposition n of the book against
    review/SCHEMA.md, and return it with the defaults filled in: [statement]
    hypotheses, omitted and companions, [coverage]'s three lists, `passage` and
    [review] items, each empty when not given. Raises ReviewError naming every fault.

    With require_stamp=False `fingerprint`, `commit` and `lean` may be absent, for
    scripts/review_stamp.py to write. `text`, also a stamp, may be absent either way, for
    now (see FIELDS). Whether the stamps are current (the fingerprint against facts.json,
    `lean` against the file, `text` against the record) is check_fidelity's business, not
    this function's."""
    where = where or _rel(review_path(book, n))
    problems = _shape(record, require_stamp)
    if problems:
        raise ReviewError(where, problems)
    bad = problems.append

    st, route, rv = record["statement"], record["route"], record["review"]
    for key in ("hypotheses", "omitted", "companions"):
        st.setdefault(key, [])
    if "coverage" in record:
        for key in FIELDS["coverage"]:
            record["coverage"].setdefault(key, [])
    record.setdefault("passage", [])
    rv.setdefault("items", {})

    def plain(s: str) -> str:
        return normalize(s.replace("*", ""))

    _, enunciation, proof = read(book, n)
    enunciation = plain(enunciation)
    porism = plain(heath_porism(book, n) or "")
    proof_text = plain(" ".join(proof))

    # [statement]
    scope = st["scope"]
    if scope not in SCOPES:
        bad(f"[statement]: `scope` is one of {', '.join(SCOPES)}, not {scope!r}")
    note = st.get("note", "")
    if scope in ("restricted", "partial") and not note:
        bad(f"[statement]: a {scope} statement needs a `note`, shown beside the badge")
    if len(note) > NOTE_LIMIT:
        bad(f"[statement]: `note` has {len(note)} characters; the limit is {NOTE_LIMIT}")
    if "\n" in note:
        bad("[statement]: `note` is one line")
    short = st.get("short", "")
    if scope in ("restricted", "partial") and not short:
        bad(f"[statement]: a {scope} statement needs a `short`, a few words shown beside "
            "the badge")
    if len(short) > SHORT_LIMIT:
        bad(f"[statement]: `short` has {len(short)} characters; the limit is {SHORT_LIMIT}")
    if "\n" in short or short.rstrip().endswith("."):
        bad("[statement]: `short` is a few words on one line, with no full stop")
    if short[:1].isupper() and not re.match(r"[A-Z]{2}|[A-Z]\b|Euclid", short):
        bad("[statement]: `short` begins with a small letter, since it follows a colon "
            "or a bracket")
    if scope == "full" and (st["hypotheses"] or st["omitted"]):
        bad("[statement]: a full statement has no `hypotheses` and no `omitted`")
    if scope == "restricted" and not st["hypotheses"]:
        bad("[statement]: a restricted statement lists its extra `hypotheses`")
    if scope == "restricted" and st["omitted"]:
        bad("[statement]: a statement with `omitted` clauses is partial, not restricted")
    if scope == "partial" and not st["omitted"]:
        bad("[statement]: a partial statement lists its `omitted` clauses")
    if scope == "partial" and "coverage" not in record:
        bad("a partial statement needs a [coverage] clause map")
    for q in st["omitted"]:
        if plain(q) not in enunciation and plain(q) not in porism:
            bad(f"[statement]: omitted {q!r} is not quoted from Heath's enunciation or porism")
    for c in st["companions"]:
        try:
            r = parse_ref(c)
        except ValueError as e:
            bad(f"[statement]: companions: {e}")
            continue
        if r.kind != "companion" or r.parent != f"{book}.{n}":
            bad(f"[statement]: companions: {c!r} is not a companion of {book}.{n} "
                f"(write '{book}.{n} <name>', as 'I.40 general')")
    if "fingerprint" in st and not HASH.fullmatch(st["fingerprint"]):
        bad("[statement]: `fingerprint` is 'sha256:' and 16 hex digits")

    # [route]
    if route["kind"] not in ROUTES:
        bad(f"[route]: `kind` is one of {', '.join(ROUTES)}, not {route['kind']!r}")
    elif route["kind"] != "euclid" and "note" not in route:
        bad(f"[route]: a {route['kind']} route needs a `note` saying how it differs")

    # [representation]
    if "representation" in record:
        tags = record["representation"]["tags"]
        terms = load_terms()
        if not tags:
            bad("[representation]: `tags` is empty; leave the section out instead")
        if len(set(tags)) != len(tags):
            bad("[representation]: a tag is listed twice")
        for t in tags:
            if t not in terms:
                bad(f"[representation]: tag {t!r} is not in review/terms.toml")
            elif terms[t]["kind"] == "scope" and scope == "full":
                bad(f"[representation]: tag {t!r} narrows the statement, but its scope is full")

    # [overlap]
    if "overlap" in record:
        ov = record["overlap"]
        if any(re.search(r"\s", r) for r in [ov["rule"]] + ov.get("also", [])):
            bad("[overlap]: `rule` and `also` name axioms as facts.json writes them, "
                "as 'Tacit.circle_eq'")
        if ov["kind"] not in OVERLAPS:
            bad(f"[overlap]: `kind` is one of {', '.join(OVERLAPS)}, the overlap catalogue's "
                f"three kinds, not {ov['kind']!r}")
        elif ov["kind"] == "step" and "note" not in ov:
            bad("[overlap]: a rule that supplies a step needs a `note` saying which step, "
                "and in which proof")

    # [coverage]
    if "coverage" in record:
        cov = record["coverage"]
        if not any(cov[k] for k in FIELDS["coverage"]):
            bad("[coverage]: the clause map is empty")
        for q in cov["text_only"]:
            if plain(q) not in enunciation and plain(q) not in proof_text:
                bad(f"[coverage]: text_only {q!r} is not quoted from Heath")

    # [figure]: `every_case` and `some_cases` say only which words lead the caption, so the
    # section still needs a `case` or a `note`, and each the `case` that names the cases
    # drawn; `some_cases` its `note` too, naming the cases left undrawn; and the two keys
    # are alternative declarations.
    if "figure" in record:
        fig = record["figure"]
        if "case" not in fig and "note" not in fig:
            bad("[figure]: give its `case`, its `note`, or both; or leave the section out")
        if fig.get("every_case") and "case" not in fig:
            bad("[figure]: `every_case` needs the `case` that names the cases the figure "
                "draws, for the caption \"Drawn for every case: …\"")
        if fig.get("some_cases") and "case" not in fig:
            bad("[figure]: `some_cases` needs the `case` that names the cases the figure "
                "draws, for the caption \"Drawn for some of its cases: …\"")
        if fig.get("some_cases") and "note" not in fig:
            bad("[figure]: `some_cases` needs the `note` that names the cases the theorem "
                "covers and the figure does not draw")
        if "every_case" in fig and "some_cases" in fig:
            bad("[figure]: `every_case` and `some_cases` cannot appear together")

    # [[passage]]
    seen = set()
    for i, p in enumerate(record["passage"], 1):
        label = f"[[passage]] {i}"
        kind = p["kind"]
        if kind not in PASSAGES:
            bad(f"{label}: `kind` is one of {', '.join(PASSAGES)}, not {kind!r}")
        elif kind != "carried" and "note" not in p:
            bad(f"{label}: a {kind} passage needs a `note`, shown on the page")
        if kind == "helper" and "helper" not in p:
            bad(f"{label}: a helper passage names its `helper`")
        if kind == "different" and route["kind"] == "euclid":
            bad(f"{label}: a passage argued another way changes Euclid's route: make the "
                "[route] modified (or alternative), or the passage another kind")
        if "helper" in p and re.search(r"\s", p["helper"]):
            bad(f"{label}: `helper` is one Lean name, as 'Prop1.middle'")
        at = plain(p["at"])
        found = proof_text.count(at)
        if found == 0:
            bad(f"{label}: `at` {p['at']!r} is not quoted from Heath's proof")
        elif found > 1:
            bad(f"{label}: `at` {p['at']!r} occurs {found} times in Heath's proof; "
                "quote enough words to name one place")
        if at in seen:
            bad(f"{label}: another passage is already `at` {p['at']!r}")
        seen.add(at)

    # [review]
    if rv["stage"] not in STAGES:
        bad(f"[review]: `stage` is one of {', '.join(STAGES)}, not {rv['stage']!r}")
    if "commit" in rv and not COMMIT.fullmatch(rv["commit"]):
        bad("[review]: `commit` is a git commit, 7 to 40 lower-case hex digits")
    if "lean" in rv and not HASH.fullmatch(rv["lean"]):
        bad("[review]: `lean` is 'sha256:' and 16 hex digits")
    if "text" in rv and not HASH.fullmatch(rv["text"]):
        bad("[review]: `text` is 'sha256:' and 16 hex digits")
    if rv["stage"] == "full" and ("run" not in rv or "," not in rv["reviewer"]):
        bad("[review]: a full review names its `run`, and its `reviewer` with a role, as "
            "'Claude Opus 5.5, records crew', so the reviewer can be told from the authors")
    for key, verdict in rv["items"].items():
        if not WORD.fullmatch(key):
            bad(f"[review]: items: {key!r} is not an item key (lower-case words and hyphens)")
        if verdict not in VERDICTS:
            bad(f"[review]: items: {key} is one of {', '.join(VERDICTS)}, not {verdict!r}")

    if problems:
        raise ReviewError(where, problems)
    return record


def load_review(book: str, n: int, *, require_stamp: bool = True) -> dict:
    """Read and check review/<book>/NN.toml; return it as a dict, defaults filled in
    (see `validate_review`), or raise ReviewError with the file and every fault."""
    path = review_path(book, n)
    if not path.exists():
        raise ReviewError(_rel(path), ["missing: every proposition has a review record "
                                       "(review/SCHEMA.md)"])
    tomllib = _toml()
    try:
        record = tomllib.loads(path.read_text())
    except tomllib.TOMLDecodeError as e:
        raise ReviewError(_rel(path), [f"not valid TOML: {e}"]) from None
    return validate_review(record, book, n, require_stamp=require_stamp, where=_rel(path))


def _schema_examples():
    """The worked examples in review/SCHEMA.md: each ```toml block whose first line is a
    comment naming its record, "# review/III/16.toml"."""
    text = (REVIEW / "SCHEMA.md").read_text()
    for block in re.findall(r"```toml\n(.*?)```", text, re.S):
        m = re.match(r"# review/([IVX]+)/(\d+)\.toml\n", block)
        if m:
            yield m.group(1), int(m.group(2)), block


# Generated regions (#578): the one account of what is generated, read alike by render.py
# and generated_counts.py, by safe_push.py, whose harness carries origin/main's copy of this
# file beside it, so that a commit is never judged by its own boundaries, and by
# check_queue.py and the negative suite; the merge queue's lane is to read it from the main
# clone. The files of GENERATED_WHOLE are generated whole ("book/" is a folder): facts.json,
# which `lake env lean Certificate/Facts.lean` writes, and book/, CERTIFICATE.md and
# GRAPH.md, which render.py writes. render.py writes each file of REGIONS only between its
# markers: there the body is generated, and the markers and every byte outside them are
# written by hand. README.md holds a book's completion
# summary between `<!-- scope:I -->` and `<!-- /scope:I -->`, inline in its table's row, a
# region for each book of BOOKS (groups: 1 the opener, 2 the book, 3 the body, 4 the
# closer); docs/PROGRAM.md its status table between `<!-- status -->` and
# `<!-- /status -->`, and docs/WORKFLOW.md section 8's first command block between
# `<!-- checks -->` and `<!-- /checks -->` (groups: 1 the opener, 2 the body, 3 the
# closer), each of their markers a whole line, since WORKFLOW's prose quotes the markers
# inline. The groups are named too: open, name (README.md's book), body and close.
GENERATED_WHOLE = ("facts.json", "book/", "CERTIFICATE.md", "GRAPH.md")
REGIONS = {
    "README.md": re.compile(r"(?P<open><!-- scope:(?P<name>[IVX]+) -->)(?P<body>.*?)"
                            r"(?P<close><!-- /scope:(?P=name) -->)", re.S),
    "docs/PROGRAM.md": re.compile(r"(?P<open>^<!-- status -->\n)(?P<body>.*?)"
                                  r"(?P<close>^<!-- /status -->$)", re.S | re.M),
    "docs/WORKFLOW.md": re.compile(r"(?P<open>^<!-- checks -->\n)(?P<body>.*?)"
                                   r"(?P<close>^<!-- /checks -->$)", re.S | re.M),
}
# The word of each file's markers, and the files whose markers stand each on a line of its
# own: a region of those is named by its word, and one of README.md by its book.
MARKER_WORDS = {"README.md": "scope", "docs/PROGRAM.md": "status", "docs/WORKFLOW.md": "checks"}
LINE_MARKERS = ("docs/PROGRAM.md", "docs/WORKFLOW.md")
# An inline count (generated_counts.py): what begins a comment that looks like one of its
# markers, its opener and its closer; render.py writes its value, between them. A value is
# read up to the first newline or count comment, never past one, as generated_counts.markers
# reads it, and so in linear time: a long line of openers with no closer is read once.
COUNT_START = re.compile(r"<!--\s*(?:/\s*)?count\b", re.I)
COUNT_OPEN = re.compile(r"<!-- count:([A-Za-z0-9]+(?:[-:][A-Za-z0-9]+)*) -->")
COUNT_CLOSE = "<!-- /count -->"
COUNT_VALUE = re.compile(f"({COUNT_OPEN.pattern})(?:[^<\\n]|<(?!(?i:!--\\s*(?:/\\s*)?count\\b)))*"
                         f"({re.escape(COUNT_CLOSE)})")


class RegionError(ValueError):
    """A file of REGIONS whose markers are not as render.py writes between them: the
    message names the file, the line and what is wrong."""


def _region_name(path: str, m: re.Match) -> str:
    return m.groupdict().get("name") or MARKER_WORDS[path]


def _cut(token: str) -> str:
    """`token` as a RegionError shows it: its first 80 characters, and "..." if cut."""
    return token if len(token) <= 80 else token[:80] + "..."


def _marker_text(path: str) -> re.Pattern:
    """What begins a comment that looks like a marker of `path`, in any case and spacing.
    The spaces after `<!--` are read by one `\\s*` alone, the second standing only after a
    `/`, so that a long run of them is read once, never tried again split another way
    (possessive quantifiers would do the same, but need Python 3.11)."""
    return re.compile(rf"<!--\s*(?:/\s*)?{MARKER_WORDS[path]}\b", re.I)


def _marked_body(path: str, m: re.Match) -> bool:
    """Whether the body of the region `m` holds text that looks like a marker of `path`."""
    return _marker_text(path).search(m["body"]) is not None


def _marker_like(path: str, text: str):
    """Each comment of `text` that looks like a marker of `path`, as (its offset, its
    text): in README.md, a comment that begins `<!-- scope` or `<!-- /scope`, in any case
    and spacing, to its `-->` (or the end of the text, when it has none); in the others, a
    line whose first characters but spaces begin such a comment, the whole line."""
    word = MARKER_WORDS[path]
    if path in LINE_MARKERS:
        for m in re.finditer(rf"^[ \t]*<!--\s*(?:/\s*)?{word}\b.*$", text, re.I | re.M):
            yield m.start(), m.group(0)
        return
    for m in _marker_text(path).finditer(text):
        end = text.find("-->", m.end())
        yield m.start(), text[m.start():end + 3 if end >= 0 else len(text)]


def regions(path: str, text: str) -> list[re.Match]:
    """The regions of `path` in `text`, in order, as REGIONS reads them; a path not in
    REGIONS has none. RegionError, naming the line, at the first comment that looks like
    a marker but is not exactly one (for status and checks, alone on its line), a closer
    with no opener, an opener with no closer, a region inside another, the same region
    twice, or a README.md region for a book not in BOOKS; when a region is missing:
    README.md holds one for each book of BOOKS, in any order, docs/PROGRAM.md one status
    and docs/WORKFLOW.md one checks; and at text in a region's body that looks like a
    marker, even not alone on its line. A token is shown cut to 80 characters."""
    pattern = REGIONS.get(path)
    if pattern is None:
        return []
    word = MARKER_WORDS[path]

    def line(i: int) -> int:
        return text.count("\n", 0, i) + 1

    def label(name: str) -> str:
        return name if path in LINE_MARKERS else f"{word}:{name}"
    if path in LINE_MARKERS:
        shape = f"`<!-- {word} -->` or `<!-- /{word} -->`, alone on its line"
        marker = re.compile(rf"<!-- (/?)({word}) -->")
    else:
        shape = f"`<!-- {word}:BOOK -->` or `<!-- /{word}:BOOK -->`"
        marker = re.compile(rf"<!-- (/?){word}:([IVX]+) -->")
    opened, found = None, {}
    for start, token in _marker_like(path, text):
        where = f"{path}:{line(start)}"
        m = marker.fullmatch(token)
        if m is None:
            raise RegionError(f"{where}: {_cut(token)!r} looks like a marker but is not one: "
                              f"a marker is exactly {shape}")
        closer, name = m.group(1) == "/", m.group(2)
        if path not in LINE_MARKERS and name not in BOOKS:
            raise RegionError(f"{where}: {_cut(token)!r} names Book {_cut(name)}, which is not "
                              f"one of the books carried into Lean ({', '.join(BOOKS)})")
        if not closer and opened is not None:
            raise RegionError(f"{where}: {_cut(token)!r} opens a region inside the "
                              f"{label(opened[0])} region opened at line {line(opened[1])}")
        if not closer and name in found:
            raise RegionError(f"{where}: {_cut(token)!r} opens a second {label(name)} region; "
                              f"the first opens at line {line(found[name])}")
        if closer and opened is None:
            raise RegionError(f"{where}: {_cut(token)!r} closes no region")
        if closer and opened[0] != name:
            raise RegionError(f"{where}: {_cut(token)!r} stands inside the {label(opened[0])} "
                              f"region opened at line {line(opened[1])}")
        if closer:
            found[name], opened = opened[1], None
        else:
            opened = name, start
    if opened is not None:
        raise RegionError(f"{path}:{line(opened[1])}: the {label(opened[0])} region opened "
                          "here has no closer")
    missing = [label(name) for name in (BOOKS if path not in LINE_MARKERS else [word])
               if name not in found]
    if missing:
        raise RegionError(f"{path}: no {' or '.join(missing)} region: it must hold "
                          + (f"one {word} region for each of the books carried into Lean "
                             f"({', '.join(BOOKS)})" if path not in LINE_MARKERS
                             else f"one {word} region"))
    matches = list(pattern.finditer(text))
    if [(_region_name(path, m), m.start()) for m in matches] != sorted(found.items(),
                                                                       key=lambda f: f[1]):
        raise RegionError(f"{path}: its markers pair otherwise than REGIONS reads them")
    # A marker's text inside a body but not alone on its line (in status and checks, which
    # the scan above reads only at a line's start), as `<!-- /status --> by hand` after a
    # row: render.py would write over it, so it is refused here, and `outside` reads it as
    # written by hand.
    for m in matches:
        if inner := _marker_text(path).search(m["body"]):
            at = m.start("body") + inner.start()
            end = text.find("-->", at)
            token = text[at:end + 3 if end >= 0 else m.end("body")]
            raise RegionError(f"{path}:{line(at)}: {_cut(token)!r} looks like a marker, inside "
                              f"the body of the {label(_region_name(path, m))} region opened at "
                              f"line {line(m.start())}: a body holds no marker's text")
    return matches


def outside(path: str, text: str, counts: bool = False) -> str:
    """`text` with the body of each region of `path` emptied and its markers kept, and,
    with `counts`, each inline count's value emptied too, between its opener and its
    closer, in any file: the part written by hand, to compare. It never refuses: a region
    whose markers are broken, or whose body holds a marker's text, is not emptied, so that
    a change to a marker, or to a region so broken, shows here as a change to the part
    written by hand."""
    pattern = REGIONS.get(path)
    if pattern is not None:
        text = pattern.sub(lambda m: m[0] if _marked_body(path, m) else m["open"] + m["close"],
                           text)
    if counts:
        text = COUNT_VALUE.sub(lambda m: m[1] + m[3], text)
    return text


def bodies(path: str, text: str) -> list[tuple[str, str]]:
    """The (name, body) of each region of `path` in `text` that REGIONS reads, in order,
    less any whose body holds a marker's text: the part render.py writes, the bodies
    `outside` empties, to compare. Like `outside`, it never refuses."""
    pattern = REGIONS.get(path)
    return ([(_region_name(path, m), m["body"]) for m in pattern.finditer(text)
             if not _marked_body(path, m)] if pattern else [])


def fill(path: str, text: str, write) -> str:
    """`text` with the body of each region of `path` replaced by write(name, body), the
    name a README.md region's book or the word of another's markers. RegionError, before
    `write` is called, when the markers are not as `regions` requires; and after, when
    what was written changes a byte outside every body, or leaves markers `regions`
    refuses."""
    if not regions(path, text):
        return text
    new = REGIONS[path].sub(lambda m: m["open"] + write(_region_name(path, m), m["body"])
                            + m["close"], text)
    if outside(path, new) != outside(path, text):
        raise RegionError(f"{path}: what was written between the markers reaches outside "
                          "them: a byte outside every region would change")
    try:
        regions(path, new)
    except RegionError as e:
        raise RegionError(f"what was written between the markers breaks them: {e}") from None
    return new


# The regions' plants (#578), hand edits of today's README.md, docs/PROGRAM.md and
# docs/WORKFLOW.md, each (what it does, the file, its verdict, the edit). A deletion inside
# a region is "inside": `regions` accepts it, `outside` is as it was and `bodies` shows it,
# for it touches only what render.py writes, and writes back (`fill`, given today's
# bodies, gives back today's file), so that the freshness check and safe_push's guard of
# the generated pages refuse the page left stale. A marker deleted or bent, a region
# deleted with its markers, doubled or put inside another, or a marker's text put in a
# body, is "refused": `regions` raises RegionError, and `outside` shows the change. A word
# of prose deleted is "seen": `regions` accepts it, `outside` shows it and `bodies` does
# not.
def _region(path: str, text: str, name: str) -> re.Match:
    return next(m for m in REGIONS[path].finditer(text) if _region_name(path, m) == name)


def _put(text: str, span: tuple[int, int], put: str = "") -> str:
    return text[:span[0]] + put + text[span[1]:]


def _in_body(path: str, text: str, name: str, edit) -> str:
    m = _region(path, text, name)
    return _put(text, m.span("body"), edit(m["body"]))


def _without_line(text: str, k: int) -> str:
    lines = text.splitlines(True)
    return "".join(lines[:k] + lines[k + 1:])


def _line_end(text: str, k: int) -> int:
    """The offset of the newline that ends line k of `text`."""
    return len("".join(text.splitlines(True)[:k + 1])) - 1


def _without_word(text: str, i: int) -> str:
    """`text` less the first word at or after `i`, and the space after it."""
    start = len(text) - len(text[i:].lstrip())
    return text[:start] + text[text.index(" ", start) + 1:]


def _nested(path: str, text: str) -> str:
    """README.md with Book II's region, markers and all, moved into Book I's body."""
    two = _region(path, text, "II")
    text = _put(text, two.span())
    one = _region(path, text, "I")
    return _put(text, (one.start("body"),) * 2, two.group(0))


def _renamed(path: str, text: str) -> str:
    """README.md with Book III's markers renamed for the first book not carried into Lean."""
    other = next(book for book in ROMAN if book not in BOOKS)
    return (text.replace("<!-- scope:III -->", f"<!-- scope:{other} -->")
            .replace("<!-- /scope:III -->", f"<!-- /scope:{other} -->"))


REGION_PLANTS = [
    ("a row of the status table deleted", "docs/PROGRAM.md", "inside",
     lambda p, t: _in_body(p, t, "status", lambda b: _without_line(b, 3))),
    ("half of Book II's summary deleted", "README.md", "inside",
     lambda p, t: _in_body(p, t, "II", lambda b: b[len(b) // 2:])),
    ("a line of the checks block deleted", "docs/WORKFLOW.md", "inside",
     lambda p, t: _in_body(p, t, "checks", lambda b: _without_line(b, 2))),
    ("Book III's opener deleted", "README.md", "refused",
     lambda p, t: _put(t, _region(p, t, "III").span("open"))),
    ("the closer deleted", "docs/PROGRAM.md", "refused",
     lambda p, t: _put(t, _region(p, t, "status").span("close"))),
    ("Book III's region deleted with its markers", "README.md", "refused",
     lambda p, t: _put(t, _region(p, t, "III").span())),
    ("the region deleted with its markers", "docs/WORKFLOW.md", "refused",
     lambda p, t: _put(t, _region(p, t, "checks").span())),
    ("the region doubled", "docs/PROGRAM.md", "refused",
     lambda p, t: _put(t, (_region(p, t, "status").end(),) * 2,
                       "\n" + _region(p, t, "status").group(0))),
    ("Book I's region doubled", "README.md", "refused",
     lambda p, t: t + _region(p, t, "I").group(0) + "\n"),
    ("a word after the opener", "docs/WORKFLOW.md", "refused",
     lambda p, t: _put(t, _region(p, t, "checks").span("open"), "<!-- checks --> by hand\n")),
    ("a word inside Book I's opener", "README.md", "refused",
     lambda p, t: _put(t, _region(p, t, "I").span("open"), "<!-- scope:I draft -->")),
    ("the opener indented", "docs/PROGRAM.md", "refused",
     lambda p, t: _put(t, _region(p, t, "status").span("open"), "  <!-- status -->\n")),
    ("Book III's markers renamed for a book not carried into Lean", "README.md", "refused",
     _renamed),
    ("Book II's region moved inside Book I's", "README.md", "refused", _nested),
    ("a closer's text after a row of the status table", "docs/PROGRAM.md", "refused",
     lambda p, t: _in_body(p, t, "status", lambda b: _put(b, (_line_end(b, 3),) * 2,
                                                         " <!-- /status --> by hand"))),
    ("a closer quoted on a line of the checks block", "docs/WORKFLOW.md", "refused",
     lambda p, t: _in_body(p, t, "checks", lambda b: _put(b, (_line_end(b, 1) + 1,) * 2,
                                                         "`<!-- /checks -->`\n"))),
    ("a word of prose after Book II's region deleted", "README.md", "seen",
     lambda p, t: _without_word(t, _region(p, t, "II").end())),
    ("a word of prose after the status table deleted", "docs/PROGRAM.md", "seen",
     lambda p, t: _without_word(t, _region(p, t, "status").end())),
]
# Each verdict as (`regions` refuses it, `outside` shows it, `bodies` shows it), None where
# the plant does not ask.
REGION_VERDICTS = {"inside": (False, False, True), "refused": (True, True, None),
                   "seen": (False, True, False)}


def _region_faults() -> tuple[list[str], int]:
    """The faults of `regions`, `outside`, `bodies` and `fill` on today's README.md,
    docs/PROGRAM.md and docs/WORKFLOW.md and on REGION_PLANTS; and how many writes `fill`
    refuses as reaching outside a body."""
    faults, real = [], {}
    for path in REGIONS:
        try:
            real[path] = (ROOT / path).read_text()
        except OSError as e:
            faults.append(f"cannot read today's {path}: {e}")
    for path, text in real.items():
        try:
            found = regions(path, text)
        except RegionError as e:
            faults.append(f"regions refuses today's {path}: {e}")
            continue
        want = len(BOOKS) if path not in LINE_MARKERS else 1
        if len(found) != want:
            faults.append(f"regions finds {len(found)} regions in today's {path}, not {want}")
        if fill(path, text, lambda name, body: body) != text:
            faults.append(f"fill changes today's {path} when it writes each body back")
    if faults:
        return faults, 0
    today = {path: dict(bodies(path, text)) for path, text in real.items()}
    for what, path, verdict, edit in REGION_PLANTS:
        text = edit(path, real[path])
        if verdict == "inside":
            try:
                back = fill(path, text, lambda name, body: today[path][name])
            except RegionError as e:
                back = f"RegionError: {e}"
            if back != real[path]:
                faults.append(f"{path}, {what}: fill, given today's bodies, does not give "
                              f"back today's {path}")
        try:
            regions(path, text)
            refused = False
        except RegionError:
            refused = True
        got = (refused, outside(path, text) != outside(path, real[path]),
               bodies(path, text) != bodies(path, real[path]))
        if any(want is not None and want != g for g, want in zip(got, REGION_VERDICTS[verdict])):
            faults.append(f"{path}, {what}: regions {'refuses' if got[0] else 'accepts'} it, "
                          f"outside {'shows' if got[1] else 'does not show'} it and bodies "
                          f"{'shows' if got[2] else 'does not show'} it, where a plant "
                          f"{verdict} expects {REGION_VERDICTS[verdict]}")
    # fill: a write that closes its region early and puts prose after it reaches outside its
    # body, and so does one that puts a marker's text in a body, since `outside` keeps that
    # region whole, as written by hand; each is refused by fill's comparison of `outside`.
    # And where a marker is gone, fill refuses before it writes.
    reached = 0
    for path, after in [("docs/PROGRAM.md", "<!-- /status -->\nProse.\n"),
                        ("docs/WORKFLOW.md", "<!-- /checks -->\nProse.\n"),
                        ("README.md", "<!-- scope:II -->")]:
        try:
            fill(path, real[path], lambda name, body: body + after)
            faults.append(f"fill accepts a write into {path} that reaches outside its body")
        except RegionError as e:
            if "reaches outside" in str(e):
                reached += 1
            else:
                faults.append(f"fill refuses a write into {path} that reaches outside its "
                              f"body, but not as one: {e}")
    called, readme = [], real["README.md"]
    try:
        fill("README.md", _put(readme, _region("README.md", readme, "III").span("open")),
             lambda name, body: called.append(name) or body)
        faults.append("fill fills README.md with Book III's opener deleted")
    except RegionError:
        pass
    if called:
        faults.append(f"fill writes the regions {called} before it refuses README.md's markers")
    # An inline count's value is emptied with `counts`, and only with it.
    count = "A <!-- count:axioms -->49<!-- /count --> b."
    if (outside("docs/STYLE.md", count), outside("docs/STYLE.md", count, counts=True)) != \
            (count, "A <!-- count:axioms --><!-- /count --> b."):
        faults.append("outside does not empty an inline count's value with counts alone")
    return faults, reached


# The reader's time (#390). Before #390 the reader of Lean read a string with holes
# afresh in each hole that held it, and a string not after INTERPOLATED both ways each
# time: its time grew exponentially with the depth of nested holes, and as the square of
# the length of a run of them, and its recursion, three frames for each depth, met
# Python's default limit at a depth of about 330. Each plant is read in a child process,
# given READER_TIMEOUT seconds, so that a reader as slow as that one fails the check
# rather than hangs it, and must take less than READER_SECONDS. Each must also read as
# that reader reads it, or reads it made smaller where it cannot: the offsets of the
# strings it cannot read for certain (`unsure`), the offsets of its strings, in order, and
# the first one's text. That reader does not finish the first plant in READER_TIMEOUT
# seconds and takes seconds over the next two; the next two, deeper than its recursion
# limit, it cannot read at all; and the sixth, where each hole walked the comment it opens
# to the end of the text, takes it more than a second. The seventh, a quote and then a
# name of 2500 «…» parts, each holding a brace and a quote, reads as the reader before
# #430 read it; a reader that read a name whole, as #430's does, but walked the rest of
# the name afresh in each hole that begins within one of its parts, took 1.19 to 1.38
# seconds over it (#430). READER_REFUSED, strings nested past their budget
# (STRINGS_PER_CHARACTER), the reader must refuse as quickly.
READER_TIMEOUT, READER_SECONDS = 20, 0.5
READER_PLANTS = [
    ("holes nested 200 deep", '"{' * 200, range(0, 400, 4), range(0, 400, 4), "{"),
    ("a run of 4000 strings with holes", '"{"' * 4000, range(0, 12000, 3),
     range(0, 12000, 3), "{"),
    ("a run of 2400 interpolated strings", 's!"{"' * 2400, range(2, 12000, 5),
     range(2, 12000, 5), "{"),
    ("holes nested 2000 deep", '"{' * 2000, range(0, 4000, 4), range(0, 4000, 4), "{"),
    ("interpolated strings nested 2000 deep, all closed", 's!"{' * 2000 + '}"' * 2000, [],
     range(7998, 0, -4), "{}"),
    ("a run of 2400 strings whose holes open a block comment", '"{/-"' * 2400,
     range(0, 12000, 5), range(0, 12000, 5), "{/-"),
    ("a name of 2500 parts, each holding a hole's brace and a quote, after a quote",
     '"' + ".".join(['«{"»'] * 2500), [0], [0], "«{"),
]
READER_REFUSED = ("interpolated strings nested 10,000 deep, all closed",
                  's!"{' * 10000 + '}"' * 10000)
# A name read whole (#430). Each plant is a declaration's last binder and the rest of it,
# which Lean 4.35 refuses after `theorem planted (s : String) `, with "unexpected token"
# at the quote after the name, since an argument needs a space before it; through a
# command that takes a name and then a string with no space between them, it reads the
# name and a plain string. Each is (that text, the offsets of the literals the reader
# cannot read for certain, and each string it reads, as its offset and its text).
# After `«a».` and `x.«b».`, Lean reads `r` or `s!` on into the name, `«a».r`,
# `x.«b».r` or `«a».s!`, before a plain string, and so now does the reader, which read a
# raw string or an interpolated one there until #430. After `℃.`, Lean reads the name
# `℃.r` or `℃.s!` too, but after a token `+℃` it reads `+℃`, `.` and a raw string or its
# own `s!`; so there the reader reads the raw string but marks it as one it cannot read
# for certain, and reads the string after `s!` as a plain one, marked where its braces
# could be holes, as after `℃s!` (`closed_up`). Lean reads `"{"a"}"` after a name as the
# string `{`, the name `a` and the string `}`.
READER_NAMES = [
    ('(h : «a».r"\\") := " = s := rfl) : True := trivial', [], [(10, '") := ')]),
    ('(h : x.«b».r"\\") := " = s := rfl) : True := trivial', [], [(12, '") := ')]),
    ('(h : ℃.r"\\") := " = s := rfl) : True := trivial', [7],
     [(9, "\\"), (16, " = s := rfl) : True := trivial")]),
    ('(h : «a».s!"{"a"}" = s) : True := trivial', [11], [(11, "{"), (15, "}")]),
    ('(h : x.«b».s!"{"a"}" = s) : True := trivial', [13], [(13, "{"), (17, "}")]),
    ('(h : ℃.s!"{"a"}" = s) : True := trivial', [9], [(9, "{"), (13, "}")]),
]
_READER_CHILD = """\
import importlib.util, json, sys, time
spec = importlib.util.spec_from_file_location("heath", sys.argv[1])
heath = importlib.util.module_from_spec(spec)
spec.loader.exec_module(heath)
src, strings = sys.stdin.read(), []
start = time.perf_counter()
try:
    unsure = heath.read_lean(src, strings)[1]
except ValueError as e:
    print(json.dumps({"seconds": time.perf_counter() - start, "refused": str(e)}))
else:
    print(json.dumps({"seconds": time.perf_counter() - start, "unsure": unsure,
                      "strings": [i for i, _ in strings], "first": strings[0][1]}))
"""


def _reader_time() -> list[str]:
    """The faults of the reader's time and reading on READER_PLANTS and READER_REFUSED."""
    faults = []
    for name, src, *want in READER_PLANTS + [READER_REFUSED]:
        try:
            run = subprocess.run([sys.executable, "-I", "-c", _READER_CHILD,
                                  str(Path(__file__).resolve())], input=src,
                                 capture_output=True, text=True, timeout=READER_TIMEOUT)
        except subprocess.TimeoutExpired:
            faults.append(f"read_lean on {name}: not done in {READER_TIMEOUT} seconds")
            continue
        if run.returncode:
            last = (run.stderr.strip().splitlines() or ["no message"])[-1]
            faults.append(f"read_lean on {name}: failed: {last}")
            continue
        got = json.loads(run.stdout)
        if got["seconds"] >= READER_SECONDS:
            faults.append(f"read_lean on {name}: took {got['seconds']:.2f} seconds; the limit "
                          f"is {READER_SECONDS}")
        if not want:
            if "refused" not in got:
                faults.append(f"read_lean on {name}: reads it, where it should refuse it, "
                              "past the budget of its strings (STRINGS_PER_CHARACTER)")
            continue
        unsure, strings, first = want
        if "refused" in got:
            faults.append(f"read_lean on {name}: refuses it: {got['refused']}")
        elif (got["unsure"], got["strings"], got["first"]) != (list(unsure), list(strings),
                                                                first):
            faults.append(f"read_lean on {name}: reads it otherwise than the plant expects "
                          "(its unsure strings, where its strings begin, or its first "
                          "string's text)")
    return faults


def _reader_names() -> list[str]:
    """The faults of the reader's reading of READER_NAMES."""
    faults = []
    for src, unsure, strings in READER_NAMES:
        got: list = []
        read = read_lean(src, got)[1], got
        if read != (unsure, strings):
            faults.append(f"read_lean({src!r}) gives the unsure offsets and strings {read}, "
                          f"not {(unsure, strings)}, as Lean 4.35 reads it (#430)")
    return faults


def _self_test() -> int:
    """Check the contracts against themselves; return the number of faults."""
    faults = []
    for text, want in [("I.40", ("I", 40, "proposition", None)),
                       ("III.1 Por.", ("III", 1, "porism", "porism")),
                       ("III. 1, Por.", ("III", 1, "porism", "porism")),
                       ("I.40 general", ("I", 40, "companion", "general")),
                       ("I. 4", ("I", 4, "proposition", None))]:
        if tuple(parse_ref(text)) != want:
            faults.append(f"parse_ref({text!r}) is {tuple(parse_ref(text))}, not {want}")
    for text in ("III.1 Por.", "I.40 general", "XIII.18"):
        if str(parse_ref(text)) != text:
            faults.append(f"str(parse_ref({text!r})) is {str(parse_ref(text))!r}")
    for text in ("I.40 porism", "Def. 15", "I.0", "Q.1", "I.40 Por"):
        try:
            parse_ref(text)
            faults.append(f"parse_ref({text!r}) should fail")
        except ValueError:
            pass
    order = ["I.3", "I.10", "I.15", "I.15 Por.", "I.40", "I.40 general", "I.48", "II.1",
             "III.1", "III.1 Por.", "IX.1", "X.1"]
    if sorted(reversed(order), key=prop_key) != order:
        faults.append(f"prop_key sorts {order} as {sorted(reversed(order), key=prop_key)}")
    early = {p for p in heath_porisms() if p[0] in ("I", "II", "III")}
    if early != {("I", 15), ("III", 1), ("III", 16)}:
        faults.append(f"heath_porisms() finds {sorted(early)} in Books I-III")
    try:
        load_terms()
    except ReviewError as e:
        faults.append(str(e))
    tomllib = _toml()
    examples = 0
    for book, n, block in _schema_examples():
        examples += 1
        try:
            example = validate_review(tomllib.loads(block), book, n,
                                      where=f"review/SCHEMA.md, the example for {book}.{n}")
        except (ReviewError, tomllib.TOMLDecodeError) as e:
            faults.append(str(e))
            continue
        # The examples' `text` stamps are the test values of text_hash.
        if example["review"].get("text") != text_hash(block):
            faults.append(f"review/SCHEMA.md, the example for {book}.{n}: its `text` is "
                          f"{example['review'].get('text', '(none)')}, but text_hash gives "
                          f"{text_hash(block)}")
    # [overlap] `kind`: required, one of the catalogue's three kinds, and "step" with its
    # note. A record with no kind is rejected, so no page words an overlap by a guess.
    for overlap, ok in [({"rule": "Tacit.circle_eq", "kind": "gives"}, True),
                        ({"rule": "Tacit.circle_eq", "kind": "states"}, True),
                        ({"rule": "Tacit.circle_eq"}, False),
                        ({"rule": "Tacit.angle_le_two_right", "kind": "step",
                          "note": "Metric 5 supplies I.13's upper bound on an angle in Prop47.within."}, True),
                        ({"rule": "Tacit.angle_le_two_right", "kind": "step"}, False),
                        ({"rule": "Tacit.circle_eq", "kind": "contains"}, False)]:
        record = {"statement": {"scope": "full"}, "route": {"kind": "euclid"},
                  "overlap": dict(overlap),
                  "review": {"stage": "exceptions", "reviewer": "Claude Opus 5.5"}}
        try:
            validate_review(record, "I", 7, require_stamp=False, where="a test record")
            if not ok:
                faults.append(f"validate_review accepts [overlap] {overlap}")
        except ReviewError as e:
            if ok:
                faults.append(str(e))
    # [[passage]] `unused`: a non-empty list of distinct names, each as a proof binds it.
    # Whether the Lean beneath binds them is check_fidelity's business.
    for unused, ok in [(["FC", "GB"], True), (["this"], True), (["hAB_FC'", "h₁"], True),
                       ([], False), ("FC", False), (["FC", "FC"], False), ([""], False),
                       (["_"], False), (["h FC"], False), (["hAB.1"], False),
                       (["2FC"], False), ([["FC"]], False)]:
        record = {"statement": {"scope": "full"}, "route": {"kind": "euclid"},
                  "passage": [{"at": "and let the straight lines FC, GB be joined",
                               "kind": "carried", "unused": unused}],
                  "review": {"stage": "exceptions", "reviewer": "Claude Opus 5.5"}}
        try:
            validate_review(record, "I", 5, require_stamp=False, where="a test record")
            if not ok:
                faults.append(f"validate_review accepts [[passage]] unused = {unused!r}")
        except ReviewError as e:
            if ok:
                faults.append(str(e))
    records = 0
    for book, count in BOOKS.items():
        for n in range(1, count + 1):
            if review_path(book, n).exists():
                records += 1
                try:
                    load_review(book, n)
                except ReviewError as e:
                    faults.append(str(e))
    faults += _reader_time()
    faults += _reader_names()
    region_faults, reached = _region_faults()
    faults += region_faults
    for f in faults:
        print("  ✗ " + f)
    if not faults:
        print(f"✓ contracts: references, porisms, review/terms.toml, {examples} examples in "
              f"review/SCHEMA.md and {records} review records hold")
        print(f"✓ the reader of Lean reads its {len(READER_PLANTS)} plants of deep and long "
              f"runs of string holes in under {READER_SECONDS} seconds each, and refuses "
              "strings nested past their budget as quickly")
        print(f"✓ the reader of Lean reads its {len(READER_NAMES)} plants of a raw or an "
              "interpolated string after a name's `.` as Lean 4.35 reads them, or marks "
              "what it cannot read for certain")
        kinds = [verdict for _, _, verdict, _ in REGION_PLANTS]
        print(f"✓ the generated regions of {', '.join(REGIONS)} hold today; of "
              f"{len(REGION_PLANTS)} hand edits, the {kinds.count('inside')} inside a region "
              f"leave the part written by hand as it was and fill writes today's file back, "
              f"the {kinds.count('refused')} to markers or a marker's text are refused and "
              f"seen, the {kinds.count('seen')} to prose are seen; fill refuses the {reached} "
              f"writes that reach outside a body (two close their region early, one puts a "
              f"marker's text in a body) and, before it writes, a file whose marker is gone")
    return len(faults)


# #206's one reader of Lean: its comments, strings, character literals, raw strings
# and names, read as Lean 4.35's tokenizer reads them. It moved here from
# check_fidelity.py, which imports it, so that safe_push.py, which carries this file
# with it as the harness, reads Lean with it too (#349; the coordinator's ruling of
# 22 October 23:50). It uses nothing else of this file but `re`, `functools` and `bisect`.

# Lean's tokens, as its tokenizer starts them: an identifier begins with a letter or `_`,
# a raw string with `r`, any `#`s and `"`, a character literal with `'`; a number with a
# digit, so that the `'` after one begins a character literal. A string just after one of
# INTERPOLATED is read with its `{…}` holes, as Lean reads it.
# A name's parts, each a run of FIRST and REST or a «…» part, are joined by a `.` before
# FIRST or `«` (NAME_GOES_ON), as Lean 4.35's `identFnAux` joins them: IDENT reads plain
# parts so joined, and a «…» name is read on through the parts after it (`_name`). Lean
# reads `«a».r"\") := "`, `x.«b».r"…"` and `«a».s!"{"` as the names `«a».r`, `x.«b».r`
# and `«a».s!`, each before a plain string, not as a raw string or an interpolated one
# after a `.` (#430).
# After a term, an adjacent `.` can begin a projection field: Lean reads `p.1` as `p` and
# the field `.1`, its digits alone (FIELD). It can also be a declared notation token. When
# the number after it runs past FIELD through `_` or an exponent, keep NUMBER's longer
# boundary, which is the reading Lean's longest parser can select for that notation; an
# ordinary projection such as `p.1.succ` keeps FIELD. Lean's field index never begins with
# 0, so `.0x1`, `.0b1` or `.01` after a `.` is always a number. Whitespace or a comment
# ends the adjacency on which a projection depends.
# A number ends where Lean 4.35's tokenizer ends it (its `numberFnAux`): binary, octal,
# hexadecimal or decimal digits, `_` between them, and a decimal's point and exponent,
# never a `..` after it. Lean reads `1set_option` as `1` and `set_option`, and
# `p.1set_option` as `p`, `.1` and `set_option`, so a number or field with a letter, a
# digit or `_` just after it is blanked: the scan's `\b` then sees the word after it
# begin (#197).
# A name is made of the characters Lean 4.35 takes for one, `isIdFirst` to begin it and
# `isIdRest` to go on (Init/Meta/Defs.lean): ID_FIRST and ID_REST, range by range. Outside
# a name, any other character that Python's `\w` takes for a letter or a digit, as the `¹`
# of the postfix `⁻¹`, which no name holds, the `ₐ` of `:=ₐ`, which no name begins with,
# Mathlib's `ᗮ` or a `λ`, Lean reads as part of a token or not at all, so it is blanked:
# Lean reads `1⁻¹set_option` as `1`, `⁻¹` and `set_option`, and the scan's `\b` then sees
# `set_option` begin (#234).
# check_rules conservatively refuses a string literal in the approximate span of a command
# that may declare tokens when its text ends in a character a name may hold
# (DECLARES_TOKENS). Lean's own tokens, and those of a library the file imports, are not
# read as tokens: docs/FORMALIZATION.md, section 7, says which of them the scan may misread.
LETTER_LIKE = ("\u03b1-\u03ba\u03bc-\u03c9"                # Greek small letters, but λ
               "\u0391-\u039f\u03a1\u03a2\u03a4-\u03a9"    # Greek capitals, but Π and Σ
               "\u03ca-\u03fb"                             # Coptic
               "\u1f00-\u1ffe"                             # polytonic Greek
               "\u2100-\u214f"                             # the letterlike symbols
               "\U0001d49c-\U0001d59f"                     # script, double-struck, Fraktur
               "\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u00ff"   # Latin-1 letters, but × and ÷
               "\u0100-\u017f")                            # Latin Extended-A
# isSubScriptAlnum: the subscript digits ₀ to ₉, the subscript letters ₐ to ₜ, ᵢ to ᵪ and ⱼ.
SUBSCRIPT_ALNUM = "\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
ID_FIRST = "A-Za-z_" + LETTER_LIKE                          # isIdFirst
ID_REST = ID_FIRST + "0-9'!?" + SUBSCRIPT_ALNUM             # isIdRest
# The scan's name, though, stops before a character of those ranges that `\w` does not take,
# as `℃`, `№` or `⅋`, 96 in all, which no file uses: Lean reads the longest token it knows,
# so after a token ending in one, as `+℃`, which check_rules refuses when the file declares
# it, or one a library declares, it reads `2 +℃1set_option` as `2`, `+℃`, `1` and
# `set_option`, and a scan that took `℃1set_option` for one name would miss the command, as
# the scan before #234 did not.
# Ending a name early, or blanking a character, can only show the scan more words, but
# where what follows, closed up, is a character literal, a raw string, or an `s!`, `m!`,
# `f!` or `throwError` before a string: Lean may read on through the `'`, the `r` or the
# word as part of a name or a token, so that a `"` or `}` the scan takes for a literal's
# text opens a string or closes a hole (`a℃'}'`, `⁻¹'"'`), or a string the scan reads
# with holes is a plain one (`a℃s!"{"`). Such a place is known by the run of name
# characters just before it, which holds a character outside ASCII (`closed_up`): there
# the scan refuses the literal or the raw string, and reads the string after such a word
# as a plain one, refused if Lean could read its braces as holes (#234). The run is read
# on through each `.` before a character that may begin a name (DOTTED_RUN), as Lean
# reads on through it: Lean reads `℃.r"\") := "` as the name `℃.r` and a plain string,
# but `+℃.r"\"` as `+℃`, `.` and a raw string where the file declares the token `+℃`,
# so the scan refuses the raw string after `℃.`, and takes no `s!` there to begin an
# interpolated string (#430).
FIRST, REST = f"(?=\\w)[{ID_FIRST}]", f"(?:(?=[\\w'!?])[{ID_REST}])"
IDENT = re.compile(f"{FIRST}{REST}*(?:\\.{FIRST}{REST}*)*")
NAME_GOES_ON = re.compile(f"\\.(?:{FIRST}|«)")
NAME_CHAR = re.compile(f"[\\w{ID_REST}]")
NAME_RUN = re.compile(f"[\\w{ID_REST}]+")
DOTTED_RUN = re.compile(f"{NAME_RUN.pattern}(?:\\.(?=[{ID_FIRST}]){NAME_RUN.pattern})*")
NON_ASCII = re.compile(r"[^\x00-\x7f]")
NUMBER = re.compile(r"0[bB](?:_*[01])+|0[oO](?:_*[0-7])+|0[xX](?:_*[0-9a-fA-F])+|"
                    r"[0-9](?:_*[0-9])*(?:(?!\.\.)\.(?:[0-9](?:_*[0-9])*)?)?"
                    r"(?:[eE][+-]?[0-9](?:_*[0-9])*)?")
FIELD = re.compile(r"[1-9][0-9]*")
WORD_CHAR = re.compile(r"\w")   # one character `\w` takes (not WORD, a key or a tag)
RAW = re.compile(r'r(#*)"')
CHAR = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\\n'])'")
INTERPOLATED = {"s!", "m!", "f!", "throwError"}
# The escapes of a Lean 4.35 string literal (`quotedCharCoreFn`): `\\`, `\"`, `\'`, `\n`,
# `\t` and `\r`, `\x` and two hexadecimal digits, `\u` and four, and a gap, a `\` before a
# line feed, which Lean reads, with the blanks after it, as nothing.
ESCAPE = re.compile(r"\\(?:x([0-9a-fA-F]{2})|u([0-9a-fA-F]{4})|(\n[ \t\r\n]*)|(.))", re.S)
# A `"` or `{` that no `\` escapes: one after a run of `\`s of even length, or none. A
# string's text, from just after its opening quote or a hole's `}`, runs to the first such
# `"` read plain, and to the first such `"` or `{` read with holes; no run of `\`s reaches
# back past that quote or `}`, so the stops found in the whole of `src` serve every
# string (`_Ends`).
STOP = re.compile(r'(?<!\\)(?:\\\\)*["{]')
# `strings` holds each string's whole text, its holes and the strings in them included, so
# that its texts grow as the square of the depth of nested holes: `s!"{` nested 20,000
# deep, 120,000 characters, gives 1.2 billion (#390). So read_lean refuses, before it
# builds them, a text whose strings, each counted from its opening quote past its closing
# one, a raw string by its text, come to more than STRINGS_PER_CHARACTER characters for
# each of its own and STRINGS_SPARE more. Those are at most the text's length times the
# depth to which its strings nest; so 1024 admits strings nested 1024 deep in any text,
# three times the depth at which the reader's recursion before #390 stopped, and so
# refuses no text that reader could read. The repository's Lean comes to at most 0.176
# for each character (Elements/Companions.lean, 560 of 3182, at c609656e). The budget
# counts characters, not bytes: a string holding a character outside the Basic
# Multilingual Plane takes 4 bytes for each of its characters, so the texts may still
# take some 4 KB of memory for each character of the source. STRINGS_SPARE lets a short
# text nest deeper still. The fifth of READER_PLANTS, 2000 levels in 12,000 characters,
# needs 12,002,000, within a budget of 29,065,216.
STRINGS_PER_CHARACTER, STRINGS_SPARE = 1024, 1 << 24


def read_lean(src: str, strings: list | None = None) -> tuple[str, list[int]]:
    """The Lean as Lean's tokenizer reads it, with its comments (`--` to the end of the
    line, and `/- … -/` blocks, docstrings and nested ones among them), the text of its
    string and character literals, raw strings among them, and each `[` or `]` in a «…»
    name blanked; the code in an interpolated string's `{…}` holes is kept. Newlines stay,
    so lines keep their numbers. Also the offset of each string the scan cannot read for
    certain: one with a `{`, not after INTERPOLATED, whose two readings, plain and with
    holes, end in different places, since its braces may be text or holes of code; and of
    each character literal or raw string closed up to a name or token that Lean may read
    on through its `'` or its `r` (`closed_up`). Each string's two readings, and where
    each hole closes, are found once, however deep the holes nest (`_Ends`, #390).
    `strings`, if given, gains each string literal read as code, raw strings among them,
    as its offset and its text as Lean reads it (`lean_string`), for `declared_tokens`;
    and if their spans would pass their budget (STRINGS_PER_CHARACTER), this raises
    ValueError before it builds them."""
    marks: list[tuple[str, int, int]] = []
    _read_code(src, 0, marks)
    if strings is not None:
        held = sum(j - i for kind, i, j in marks if kind in ("string", "raw"))
        budget = STRINGS_PER_CHARACTER * len(src) + STRINGS_SPARE
        if held > budget:
            raise ValueError(f"read_lean: the strings of this Lean come to {held:,} "
                             f"characters, past their budget of {budget:,} for its "
                             f"{len(src):,}: strings nested too deep in each other's holes "
                             "(STRINGS_PER_CHARACTER, #390)")
    out, unsure = list(src), []
    for kind, i, j in marks:
        if kind == "comment":
            continue
        if kind == "unsure":
            unsure.append(i)
            continue
        if kind in ("string", "raw"):
            if strings is not None and kind == "raw":
                strings.append((i, src[i:j]))
            elif strings is not None:
                closed = j - 1 > i and src[j - 1] == '"'
                strings.append((i, lean_string(src[i + 1:j - 1 if closed else j])))
            continue
        for k in range(i, j):
            if out[k] != "\n" and (kind == "text" or out[k] in "[]"):
                out[k] = " "
    return "".join(out), unsure


def without_comments(src: str) -> str:
    """The Lean with its comments and the text of its string literals blanked, as
    `read_lean` reads it: what `scripts/render.py` searches for a declaration's uses, so a
    name in a comment, a docstring or a string is no use."""
    return read_lean(src)[0]


def lean_comments(src: str) -> list[tuple[int, int]]:
    """Each comment of the Lean `src`, in order, as `read_lean` reads them: its offset
    and the offset where it ends (`comment_end`), the end of `src` for a block that no
    `-/` closes. A comment in an interpolated string's hole is one; a `--` or `/-` within
    a comment, a string or a character literal begins none."""
    marks: list[tuple[str, int, int]] = []
    _read_code(src, 0, marks)
    return [(i, j) for kind, i, j in marks if kind == "comment"]


def comment_end(src: str, i: int) -> int | None:
    """Where the comment that begins at `i`, with `--` or `/-`, ends, as Lean 4.35 reads
    it (`whitespace` and `finishCommentBlock` in Lean/Parser/Basic.lean): a `--` comment
    at the line feed that ends its line, or the end of `src`; a `/- … -/` block,
    docstrings and nested blocks among them, just past the `-/` that closes it, or None
    if none does. A block's body begins at its fourth character, after `/--` or `/-!`,
    and past the third of any other `/-`, which Lean passes over, so that `/-/- -/` is a
    whole comment and the `-/` of `/--/` closes nothing. `_read_code`, and so
    `read_lean` and `lean_comments`, and check_style's notes call this (#206). It uses
    nothing else of this file, so that a program that cannot import it holds a copy, word
    for word, which its tests hold to this one: the Jev generator, and risk.py from
    #349's second train."""
    if src.startswith("--", i):
        end = src.find("\n", i)
        return len(src) if end < 0 else end
    j, nested = i + 3, 1
    while j < len(src):
        pair = src[j:j + 2]
        nested += (pair == "/-") - (pair == "-/")
        j += 2 if pair in ("/-", "-/") else 1
        if not nested:
            return j
    return None


def _find(src: str, s: str, i: int) -> int:
    """The offset of `s` in `src` from `i` on, or the end of `src`."""
    k = src.find(s, i)
    return len(src) if k < 0 else k


@functools.lru_cache(maxsize=8)
def closed_up(src: str) -> bytes:
    """For each offset of `src`, and its end, 1 where the run of name characters just
    before it (NAME_CHAR), read on through each `.` before a character that may begin a
    name (DOTTED_RUN), holds a character outside ASCII: one the reader blanks, as `¹`,
    one of the 96 before which it ends a name, as `℃`, or a letter of a name it may have
    ended there. Lean may read on through what begins at such an offset, as part of the
    name or of a token, where the scan begins something new; ASCII alone, a name is read
    whole and a number ends where Lean ends it. In one pass, however long the runs."""
    out = bytearray(len(src) + 1)
    for run in DOTTED_RUN.finditer(src):
        if odd := NON_ASCII.search(src, run.start(), run.end()):
            out[odd.end():run.end() + 1] = b"\x01" * (run.end() - odd.start())
    return bytes(out)


def _read_code(src: str, i: int, marks: list, hole: bool = False) -> int:
    """Read Lean from `i` to the end or, in a hole, to the `}` that closes it, and return
    that offset. `marks` gains the text of each comment and literal ("text"), each
    comment again ("comment", `comment_end`), each «…» part of a name ("name"), each string,
    character literal or raw string the scan cannot read for certain ("unsure"), and each
    string literal, from its opening quote past its closing one ("string"), and raw
    string's text ("raw"). Each string is read once, the one way `_Ends` finds it is
    read."""
    return _run(_code(src, i, marks, _Ends(src), hole))


def _read_string(src: str, i: int, marks: list, interpolated: bool) -> int:
    """Read the string at `i` and return the offset past it: with its holes, as an
    interpolated string, if it follows INTERPOLATED or both readings end in one place."""
    return _run(_string(src, i, marks, interpolated, _Ends(src)))


def _read_interpolated(src: str, i: int, marks: list) -> int | None:
    """The offset past the string at `i` read as an interpolated string, with its text
    marked and its holes read as code; None if it does not close."""
    return _run(_interpolated(src, i, marks, _Ends(src)))


def _run(reading):
    """The value of `reading`, a generator that yields each reading it rests on, a
    generator too, and is sent back that reading's value. They run on a stack of this
    function's own, not on Python's, so that no depth of nested holes reaches Python's
    recursion limit, which the reader's recursion before #390 met at a depth of about
    330, under the default limit of 1000 frames."""
    stack, value = [reading], None
    while stack:
        try:
            stack.append(stack[-1].send(value))
            value = None
        except StopIteration as done:
            stack.pop()
            value = done.value
    return value


def _code(src: str, i: int, marks: list, ends: _Ends, hole: bool = False):
    """`_read_code`'s reading, for `_run`, with `ends` to say how each string is read."""
    depth, previous, can_project, field_dot = 0, "", False, False
    closed = closed_up(src)
    while i < len(src):
        c = src[i]
        if c == '"':
            j = yield _string(src, i, marks, previous in INTERPOLATED, ends)
            marks.append(("string", i, j))
            previous, can_project, field_dot = c, True, False
        elif c == "}" and hole and not depth:
            return i
        else:
            depth += (c == "{") - (c == "}")
            j, token, can_project, field_dot = _token(src, i, closed, can_project, field_dot,
                                                      marks)
            previous = previous if token is None else token
        i = j
    return len(src)


def _token(src: str, i: int, closed: bytes, can_project: bool, field_dot: bool,
           marks: list, ends: _Ends | None = None) -> tuple[int, str | None, bool, bool]:
    """Read the token at `i`, which is no `"`, as `_read_code` reads it: `marks` gains
    its marks, and this returns the offset past it, the token as the scan's `previous`,
    which is asked only whether it is one of INTERPOLATED (a raw string or a «…» name by
    its first character alone, and None for a comment or a blank, which leave `previous`
    as it was), and the scan's `can_project` and `field_dot` after it. A `{` or `}` is
    read alone, as most characters that begin no other token are; whether a `}` closes a
    hole is the caller's to say. A blank, which begins no other token, is tried first.
    Where a comment, a raw string or a «…» name ends comes from `ends` if given, as the
    scan of holes (`_Ends.hole`) gives it, since other holes may begin within one; else
    from `comment_end`, `_name` and `_find`, as the reading that writes the marks, which passes
    each place once, gives it."""
    c, j = src[i], i + 1
    if c.isspace():
        return j, None, False, False
    if src.startswith(("--", "/-"), i):
        end = comment_end(src, i) if ends is None else ends.comment_end(i)
        j = len(src) if end is None else end
        marks.append(("text", i, j))
        marks.append(("comment", i, j))
        return j, None, False, False
    if m := RAW.match(src, i):
        close = '"' + m[1]
        k = _find(src, close, m.end()) if ends is None else ends.find(close, m.end())
        if closed[i]:
            marks.append(("unsure", i, k))
        marks.append(("text", m.end(), k))
        marks.append(("raw", m.end(), k))
        return min(k + len(close), len(src)), c, True, False
    if c == "«":
        # A «…» part, and the parts of the name after it (#430).
        return _name(src, i, marks) if ends is None else ends.name(i), c, True, False
    if m := IDENT.match(src, i):
        # An `s!` or its kin where Lean may read on through it begins no interpolated
        # string for certain (`closed_up`).
        return m.end(), "" if closed[i] else m[0], True, False
    if m := NUMBER.match(src, i):
        if field_dot and (field := FIELD.match(src, i)):
            tail = src[field.end():m.end()]
            if "_" not in tail and "e" not in tail and "E" not in tail:
                m = field
        if WORD_CHAR.match(src, m.end()):
            marks.append(("text", i, m.end()))
        return m.end(), m[0], True, False
    if WORD_CHAR.match(c):
        # Outside a name, a character `\w` takes that no name begins with, as the `¹`
        # that ends `⁻¹`: blanked. After such a token Lean may read `.1` as a field.
        marks.append(("text", i, j))
        return j, c, True, False
    if c == "'" and src[j:j + 1] != "'" and (m := CHAR.match(src, i)):
        if closed[i]:
            marks.append(("unsure", i, m.end()))
        marks.append(("text", i + 1, m.end() - 1))
        return m.end(), c, True, False
    if c == ".":
        return j, c, False, can_project
    return j, c, c in ")]}·⟩›", False


def _name(src: str, i: int, marks: list) -> int:
    """The offset past the «…» name at `i`, read on as Lean 4.35's `identFnAux` reads a
    name: its parts (`_part`) joined by a `.` before FIRST or `«` (NAME_GOES_ON), so that
    `«a».r` is one name. `marks` gains each «…» part ("name"). A name that begins with
    plain parts IDENT reads, and the scan reads the `.` and the «…» name after them as
    tokens of their own, which give the same marks and leave the scan as one token
    would."""
    while True:
        j = _part(src, i)
        if src[i] == "«":
            marks.append(("name", i, j))
        if not NAME_GOES_ON.match(src, j):
            return j
        i = j + 1


def _part(src: str, i: int, ends: _Ends | None = None) -> int:
    """The offset past the part of a name that begins at `i`: a «…» part just past the
    `»` that ends it, found by `ends` if given, or the end of `src`; else a run of FIRST
    and REST, or of such runs joined by a `.` (IDENT)."""
    if src[i] == "«":
        return min((_find(src, "»", i) if ends is None else ends.find("»", i)) + 1, len(src))
    return IDENT.match(src, i).end()


def _string(src: str, i: int, marks: list, interpolated: bool, ends: _Ends):
    """`_read_string`'s reading, for `_run`. Its holes are read only if `ends` reads it with
    them; and unless it follows INTERPOLATED, no comment in them, at any depth, is marked
    "comment", though its text is blanked."""
    end, holes = yield ends.string(i, interpolated)
    if holes:
        inner = marks if interpolated else []
        yield _interpolated(src, i, inner, ends)
        if inner is not marks:
            marks += [mark for mark in inner if mark[0] != "comment"]
        return end
    marks.append(("text", i + 1, end))
    if "{" in src[i:end]:
        marks.append(("unsure", i, end))
    return end


def _interpolated(src: str, i: int, marks: list, ends: _Ends):
    """`_read_interpolated`'s reading, for `_run`."""
    j = start = i + 1
    while j < len(src):
        if src[j] == "\\":
            j += 2
        elif src[j] == '"':
            marks.append(("text", start, j))
            return j + 1
        elif src[j] == "{":
            marks.append(("text", start, j))
            j = yield _code(src, j + 1, marks, ends, hole=True)
            if j >= len(src):
                return None
            j = start = j + 1
        else:
            j += 1
    return None


class _Ends:
    """Where the strings of the Lean `src` end and its holes close, each found once (#390).

    A string's reading with holes rests on its holes' readings, which rest on the strings
    in them, and so on; and a string not after INTERPOLATED is read both ways, to see
    whether the two end in one place. Read afresh wherever it was met, as before #390,
    that took time exponential in the depth of nested holes, and growing as the square of
    the length of a long run of them. Here the end of a reading with holes is found once
    for each place where its text goes on, just after the opening quote or a hole's `}`
    (`text`), and the close of a hole once for each place, and state of the scan, that
    the code of a hole passes through (`hole`): the scan's tokens from a place rest only
    on that place, on whether the token before it is one of INTERPOLATED, and on
    `can_project` and `field_dot`, never on how deep in braces the scan is, so scans that
    meet go on as one. A hole may also begin within a comment, a raw string or a name's
    «…» part that an earlier hole reads whole, as each hole of `"{/-"` written 2400 times
    begins within the block that the hole before it opens, and each hole after a quote
    and a name of 2500 parts `«{"»` within a part of that name, which a hole before it
    reads to the name's end (#430); so where such a token ends comes from
    `comment_end`, `name` and `find`, which walk no place of a block or part of a name
    twice and list the offsets of each line feed, `»` or raw string's closer once. The
    methods that rest on others are generators, for `_run`."""

    def __init__(self, src: str):
        self.src, self.closed = src, closed_up(src)
        self.texts: dict[int, int | None] = {}
        self.closes: dict[tuple[int, bool, bool, bool], int] = {}
        self.blocks: dict[int, int | None] = {}
        self.names: dict[int, int] = {}
        self.found: dict[str, list[int]] = {}

    @functools.cached_property
    def stops(self) -> list[int]:
        """The offset of each `"` and `{` of `src` that no `\\` escapes (STOP), found when
        the first string is met."""
        return [m.end() - 1 for m in STOP.finditer(self.src)]

    @functools.cached_property
    def quotes(self) -> list[int]:
        """The offset of each `"` of `src` that no `\\` escapes."""
        return [k for k in self.stops if self.src[k] == '"']

    def plain(self, i: int) -> int:
        """The offset past the string at `i` read plain: past the first `"` after `i` that
        no `\\` escapes (STOP), or the end of `src`."""
        k = bisect.bisect_right(self.quotes, i)
        return self.quotes[k] + 1 if k < len(self.quotes) else len(self.src)

    def string(self, i: int, interpolated: bool):
        """The offset past the string at `i`, and whether it is read with its holes: so if
        it follows INTERPOLATED (`interpolated`) and closes so, or if both readings end in
        one place; else plain."""
        end = yield self.text(i + 1)
        plain = self.plain(i)
        if end == plain or (interpolated and end is not None):
            return end, True
        return plain, False

    def text(self, p: int):
        """The offset past a string read with holes whose text goes on at `p`, or None if
        it does not close so: its text runs to the first `"` or `{` that no `\\` escapes
        (STOP), and each hole to the `}` that closes it (`hole`)."""
        passed = []
        while p not in self.texts:
            passed.append(p)
            k = bisect.bisect_left(self.stops, p)
            if k == len(self.stops):
                end = None
                break
            if self.src[self.stops[k]] == '"':
                end = self.stops[k] + 1
                break
            p = yield self.hole(self.stops[k] + 1)
            if p == len(self.src):
                end = None
                break
            p += 1
        else:
            end = self.texts[p]
        for q in passed:
            self.texts[q] = end
        return end

    def hole(self, h: int):
        """The offset of the `}` that closes the hole whose code begins at `h`, or the end
        of `src` if none does. Each place the scan passes, with the state of the scan
        there, waits at its depth in braces for the `}` that closes that depth, where a
        hole whose code began at that place, in that state, would close; where that is
        known already, the scan goes straight to it. So no place and state is passed
        twice, whatever the holes that pass it. That bounds the places passed, not the
        time: a token is read to its end at each place and state that begins it, and other
        holes may begin within a long comment, raw string or name, so where one of those
        ends comes from `comment_end`, `name` and `find`, not from a walk to it afresh."""
        src, closes, ignored = self.src, self.closes, []
        i, interpolated, can_project, field_dot = h, False, False, False
        waiting: list[list] = [[]]
        while True:
            place = (i, interpolated, can_project, field_dot)
            if place in closes:
                m = closes[place]
            elif i < len(src) and src[i] != "}":
                waiting[-1].append(place)
                if src[i] == '"':
                    i, _ = yield self.string(i, interpolated)
                    interpolated, can_project, field_dot = False, True, False
                else:
                    c = src[i]
                    i, token, can_project, field_dot = _token(src, i, self.closed,
                                                              can_project, field_dot, ignored,
                                                              self)
                    interpolated = interpolated if token is None else token in INTERPOLATED
                    if c == "{":
                        waiting.append([])
                continue
            else:
                waiting[-1].append(place)
                m = i
            # The `}` at `m` closes every place waiting at this depth; the end, every one.
            for level in waiting if m == len(src) else waiting[-1:]:
                for place in level:
                    closes[place] = m
            if m == len(src) or len(waiting) == 1:
                return m
            waiting.pop()
            # Past a `}` read alone, as `_token` reads one.
            i, interpolated, can_project, field_dot = m + 1, False, True, False

    def comment_end(self, i: int) -> int | None:
        """`comment_end(src, i)`: for a `--` comment the next line feed (`find`), for a
        block the end of its walk (`block`)."""
        return self.find("\n", i) if self.src[i] == "-" else self.block(i + 3)

    def block(self, p: int) -> int | None:
        """Where `comment_end`'s walk of a block, from `p` with one block open, closes it:
        just past the `-/` that does, or None if none does. As in `hole`, each place the
        walk passes waits at its depth for the `-/` that closes that depth, where a walk
        from that place would close its block; where that is known already, the walk goes
        straight to it. So no place is walked twice, however many holes begin within
        one block."""
        src, ends, waiting = self.src, self.blocks, [[]]
        while True:
            if p in ends:
                m = ends[p]
            elif p < len(src) and (pair := src[p:p + 2]) != "-/":
                waiting[-1].append(p)
                if pair == "/-":
                    waiting.append([])
                p += 2 if pair == "/-" else 1
                continue
            else:
                waiting[-1].append(p)
                m = p + 2 if p < len(src) else None
            # The `-/` just before `m` closes every place waiting at this depth; the end,
            # every one.
            for level in waiting if m is None else waiting[-1:]:
                for place in level:
                    ends[place] = m
            if m is None or len(waiting) == 1:
                return m
            waiting.pop()
            p = m

    def name(self, i: int) -> int:
        """`_name(src, i, marks)`: the offset past the «…» name at `i`, each of the parts
        it walks remembered with that offset, so that a walk from a part already walked
        goes straight to it, and no part is walked twice, however many holes begin within
        the name's «…» parts."""
        passed = []
        while i not in self.names:
            passed.append(i)
            j = _part(self.src, i, self)
            if not NAME_GOES_ON.match(self.src, j):
                break
            i = j + 1
        else:
            j = self.names[i]
        for p in passed:
            self.names[p] = j
        return j

    def find(self, s: str, i: int) -> int:
        """`_find(src, s, i)`, from the offsets of `s` in `src`, listed in one pass over
        `src` for each `s`: a line feed, `»`, or a raw string's closing `"` and its `#`s.
        A text of n characters asks for at most about √(2n) closers, since each number of
        `#`s needs an `r`, those `#`s and a `"` of its own; so at most that many passes."""
        if s not in self.found:
            self.found[s], k = [], self.src.find(s)
            while k >= 0:
                self.found[s].append(k)
                k = self.src.find(s, k + 1)
        found = self.found[s]
        k = bisect.bisect_left(found, i)
        return found[k] if k < len(found) else len(self.src)


def lean_string(body: str) -> str:
    """A string literal's text between its quotes, as Lean reads it (ESCAPE)."""
    def escape(m: re.Match) -> str:
        if m[1] or m[2]:
            return chr(int(m[1] or m[2], 16))
        return "" if m[3] else {"n": "\n", "t": "\t", "r": "\r"}.get(m[4], m[4])
    return ESCAPE.sub(escape, body)


if __name__ == "__main__":
    sys.exit(1 if _self_test() else 0)
