"""Check the house style's hard rules, and report its defaults.

The rules are those of docs/STYLE.md, section 8, which is their one home: S1 to S21
fail the script, and D1 to D11, D13 and D14 are listed for a reader to judge and fail
nothing. Run from anywhere; the paths are the repository's.

    python3 scripts/check_style.py              # every rule, S12 included
    python3 scripts/check_style.py --no-lean    # S12 skipped, for an unbuilt tree
    python3 scripts/check_style.py --quiet      # the reports as counts only
    python3 scripts/check_style.py --require-idea-letters   # S21 on every figure, as the switch is
    python3 -I tests/test_check_style.py        # the rules' cases, which CI runs first

S12 asks Lean whether each backticked name in the mishnah exists, so it needs a built
tree (`lake build`) and `lake` on the PATH; without them the script fails and says so,
unless `--no-lean` is given. CI runs it after `lake build`.

What the scopes cover (STYLE, section 8):

* Prose: mishnah/<book>/NN.md, mishnah/intro/<book>.md, reading/<book>/NN.md.
* Mishnah: mishnah/<book>/NN.md alone.
* Catalogues: docs/reports/gaps-book-*.md.
* README: README.md, without its section "How it was made".
* Lean notes: in Elements/**/*.lean, the text of `/- … -/` blocks and docstrings, save
  the docstring of each `theorem PropN`, which is Heath's enunciation. The `--` lines
  are Heath's proof and out of scope.
* Generated: CERTIFICATE.md, GRAPH.md, book/<book>/index.md. A failure here is mended
  in scripts/render.py or in the source it reads.
* Idea figures, figures/<book>/NN-idea.svg; Euclid's figures, figures/<book>/NN.svg.

"Outside quotations" means with every "…" span (within one paragraph), every link
target `](…)`, every code span and every fenced code block blanked first. HTML comments
are never shown to a reader, and are blanked everywhere. Blanking keeps every line in
its place, so each finding names its line. A blanked span reads as spaces, so the words
of a phrase may stand apart across one: S3 finds "I think" in 'as I "so" think'.

The words of a phrase in S2 to S7, S9, S11 and D7 to D10 are found however a line or a
comment wraps them: they may stand apart by spaces or tabs (and commas, between S9's
letters), or by one line break with the next line's indent and comment leader ("--" in
Lean, ">" in a Markdown quotation). A blank line ends such a phrase, save S2's "first
mate" and the "Definition N" of S7 and D10, whose words may stand apart by any white
space. Those patterns are tested on such phrases, case by case (below).

S2's crew words match whole words in any case, plurals and possessives included ("the
bosuns", "the crew's"). The figure rules also ask for a <title>: "I.N at a glance" on an
idea figure, "Euclid I.N: …" on Euclid's (STYLE, section 7). A known departure a rule
cannot see is right is listed below with its reason, and printed on every run; one that
no longer applies fails. An idea figure marks a point Heath leaves without a letter in the
figure itself, with `data-unlettered` and its reason (S21), and those are printed too.
S20 judges a letter's ink by the fill under it, an angle's wedge included.

How the rules read a phrase, and how S20 reads a letter on and beside an angle's wedge,
are tested case by case in tests/test_check_style.py, which needs no Lean. CI runs it just
before this script, in the order of docs/WORKFLOW.md, section 8; a defect fixed in that
reading comes with a case there. Standard library only.
"""

from __future__ import annotations

import argparse
import math
import re
import shutil
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET
from collections import defaultdict
from pathlib import Path

import heath

ROOT = heath.ROOT

# ---------------------------------------------------------------------------------------
# Exceptions. Each is a known departure that the rule cannot see is right, with its
# reason. Add one only with a reason a reviewer can check; never to quiet a real fault.

# S16: letters drawn in Euclid's figure that are not in Heath's text, or the reverse.
# {(book, n): {"extra": {letters drawn but not in the text}, "missing": {...}, "why": …}}
LETTER_EXCEPTIONS = {
    ("II", 7): {
        "extra": {"H", "N"},
        "why": "Heath's figure (scan leaf n408) letters H and N, where the parallels "
               "through G meet AD and DE; his text says only \"let the figure be drawn\"",
    },
    ("II", 14): {
        "extra": {"C"},
        "why": "Heath's figure (scan leaf n429) letters C, a corner of the parallelogram "
               "his text calls BD, and the text never names it",
    },
}

# S21, the switch (STYLE, sections 7 and 8). While the figures at a glance were gaining
# Heath's letters, this was False: S21 held an idea figure only once it carried a letter,
# and D14 listed, book by book, the figures with none yet. Every figure now carries its
# letters, so it is True, and S21 fails every idea figure with a point unlettered; D14 is
# empty. Never set it back to quiet a figure: letter the figure.
IDEA_LETTERS_REQUIRED = True

# ---------------------------------------------------------------------------------------
# Findings.

failures: list[tuple[str, str, int, str]] = []   # (rule, file, line, message)
reports: dict[str, list[tuple[str, int, str]]] = defaultdict(list)

RULES = {
    "S1": "an em dash",
    "S2": "crew talk outside quotations",
    "S3": "the first person singular outside quotations",
    "S4": "a hedge for a checker outside quotations",
    "S5": "Heath's references called Euclid's, or Postulate 5 'never needed'",
    "S6": "'tacit assumption' or 'tacit law' outside quotations",
    "S7": "a definition without its book",
    "S8": "a curly quotation mark",
    "S9": "an italic letter",
    "S10": "TeX in the mishnah",
    "S11": "a retired refrain",
    "S12": "a backticked Lean name that Lean does not know",
    "S13": "an idea figure's caption missing or over 50 words",
    "S14": "an idea figure's canvas, colours or title",
    "S15": "a Euclid's figure's canvas, letters, colours, strokes, caption or title",
    "S16": "figure letters not all and only Heath's",
    "S17": "a further-reading file's shape or links",
    "S18": "a book with pages and no introduction",
    "S19": "a book introduction that does not link the book's brief",
    "S20": "an idea figure's letter not Heath's, or not italic, 14 and in the ink of what it stands on",
    "S21": "a point of an idea figure without its letter",
}

REPORTS = {
    "D1": "a mishnah outside 250–450 words",
    "D2": "a mishnah's paragraph count, or a paragraph over 120 words",
    "D3": "a mishnah paragraph without a bold lead, or the modern way not last",
    "D4": "a mishnah with more than four distinct Lean names",
    "D5": "an idea caption over 40 words, or of more than two sentences",
    "D6": "'first', 'only', 'better', 'best', 'unlike': a comparison or a claim to priority?",
    "D7": "'Lean cannot' (say what our representation does)",
    "D8": "'gives no citation' and its kin (say 'Heath gives no reference')",
    "D9": "'need' joined to Postulate 5 (say 'uses')",
    "D10": "S6 or S7 outside their failing scope",
    "D11": "Euclid's figure strokes or dots off the usual widths",
    "D13": "a reading line that does not begin 'For '",
    "D14": "figures at a glance not yet lettered (S21 holds them once the switch is on)",
}


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def fail(rule: str, path: Path, line: int, message: str) -> None:
    failures.append((rule, rel(path), line, message))


def report(rule: str, path: Path, line: int, message: str) -> None:
    reports[rule].append((rel(path), line, message))


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def excerpt(text: str, start: int, end: int, width: int = 50) -> str:
    """The match with a little context, on one line."""
    a = max(0, start - width)
    b = min(len(text), end + width)
    s = " ".join(text[a:b].split())
    return ("…" if a else "") + s + ("…" if b < len(text) else "")


# ---------------------------------------------------------------------------------------
# Blanking: each helper returns a string of the same length, with the spans it removes
# turned to spaces and their newlines kept.

def _blank(m: re.Match) -> str:
    return re.sub(r"[^\n]", " ", m.group(0))


FENCE = re.compile(r"^[ \t]*```.*?^[ \t]*```[^\n]*$", re.S | re.M)
CODE_SPAN = re.compile(r"`[^`\n]+`")
HTML_COMMENT = re.compile(r"<!--.*?-->", re.S)
# The "(…)" after a link's "]", one level of parentheses inside allowed.
LINK_TARGET = re.compile(r"(?<=\])\((?:[^()\n]|\([^()\n]*\))*\)")
PARAGRAPH_BREAK = re.compile(r"(\n[ \t]*\n)")
QUOTATION = re.compile(r'"[^"]*"')
# Square brackets that are not a link's text: Heath's references, [Def. 15].
SQUARE = re.compile(r"\[[^\[\]\n]*\](?![(\[])")


def blank_code(text: str) -> str:
    """Fenced blocks, code spans and HTML comments blanked: what a reader reads as prose,
    quotations included."""
    text = FENCE.sub(_blank, text)
    text = HTML_COMMENT.sub(_blank, text)
    text = CODE_SPAN.sub(_blank, text)
    return LINK_TARGET.sub(_blank, text)


def blank_quotes(text: str) -> str:
    """Each "…" span blanked, within one paragraph: an unmatched quotation mark never
    swallows the paragraphs after it."""
    parts = PARAGRAPH_BREAK.split(text)
    return "".join(p if PARAGRAPH_BREAK.fullmatch(p) else QUOTATION.sub(_blank, p)
                   for p in parts)


def straighten(text: str) -> str:
    """Curly apostrophes and quotation marks made straight, so that "Euclid’s own" is
    caught as "Euclid's own". S8 reports the curly marks themselves."""
    return text.translate(str.maketrans({"’": "'", "‘": "'", "“": '"', "”": '"'}))


def paragraphs(text: str):
    """(offset, paragraph) for each paragraph of a Markdown text, trimmed."""
    off = 0
    for part in PARAGRAPH_BREAK.split(text):
        if part.strip() and not PARAGRAPH_BREAK.fullmatch(part):
            yield off + len(part) - len(part.lstrip()), part.strip()
        off += len(part)


SENTENCE_END = re.compile(r'(?<=[.?!])["\')*]*\s+(?=["*(\[`]?[A-Z])')


# A paragraph break, or a new line opening a heading, a list item or a table row.
BLOCK_BREAK = re.compile(r"\n[ \t]*\n|\n(?=[ \t]*(?:#|[-*] |\d+\. |\|))")


def sentences(text: str):
    """(offset, sentence), split at a paragraph, heading, list item or table row, and after
    ".", "?" or "!" before a capital. "I.29", "vol. 1" and "C.N. 1" stay whole; "Def. I.15"
    is split, which no rule here minds."""
    start = 0
    for m in list(BLOCK_BREAK.finditer(text)) + [None]:
        end = m.start() if m else len(text)
        block = text[start:end]
        at = 0
        for s in SENTENCE_END.finditer(block):
            yield start + at, block[at:s.start()]
            at = s.end()
        yield start + at, block[at:]
        start = m.end() if m else len(text)


# ---------------------------------------------------------------------------------------
# The files of each scope.

def books_with_pages() -> list[str]:
    found = set(heath.BOOKS)
    for d in ("mishnah", "book", "figures"):
        base = ROOT / d
        if base.is_dir():
            found |= {p.name for p in base.iterdir() if p.is_dir() and p.name in heath.ROMAN}
    return sorted(found, key=heath.arabic)


def numbered(directory: Path, suffix: str) -> list[Path]:
    """NN<suffix> files of a book directory, in order."""
    if not directory.is_dir():
        return []
    return sorted(p for p in directory.iterdir() if re.fullmatch(r"\d\d" + re.escape(suffix), p.name))


def mishnah_files() -> list[Path]:
    return [p for b in books_with_pages() for p in numbered(ROOT / "mishnah" / b, ".md")]


def intro_files() -> list[Path]:
    return sorted((ROOT / "mishnah" / "intro").glob("*.md"), key=lambda p: heath.arabic(p.stem)
                  if p.stem in heath.ROMAN else 99)


def reading_files() -> list[Path]:
    return [p for b in books_with_pages() for p in numbered(ROOT / "reading" / b, ".md")]


def catalogue_files() -> list[Path]:
    return sorted((ROOT / "docs" / "reports").glob("gaps-book-*.md"))


def generated_files() -> list[Path]:
    files = [ROOT / "CERTIFICATE.md", ROOT / "GRAPH.md"]
    files += [ROOT / "book" / b / "index.md" for b in books_with_pages()]
    return [p for p in files if p.exists()]


def ref_of(path: Path) -> str | None:
    """"I.5" for mishnah/I/05.md, reading/I/05.md or figures/I/05-idea.svg."""
    m = re.fullmatch(r"(\d\d)(?:-idea)?\.(?:md|svg)", path.name)
    if m and path.parent.name in heath.ROMAN:
        return f"{path.parent.name}.{int(m.group(1))}"
    return None


def readme_text() -> str:
    """README.md, with its section "How it was made" blanked (it says how the work was
    done, and may name the roles)."""
    text = (ROOT / "README.md").read_text(encoding="utf-8")
    m = re.search(r"^## How it was made[^\n]*\n.*?(?=^## |\Z)", text, re.S | re.M)
    if m:
        text = text[:m.start()] + _blank(m) + text[m.end():]
    return text


def lean_notes(path: Path) -> str:
    """The Lean file with everything but its notes blanked: the text inside each `/- … -/`
    block and docstring (nested blocks included), save the docstring of `theorem PropN`,
    which is Heath's enunciation. The `--` lines outside blocks are Heath's proof."""
    m = re.fullmatch(r"Prop(\d+)\.lean", path.name)
    n = int(m.group(1)) if m and path.parent.name.startswith("Book") else None
    return notes_text(path.read_text(encoding="utf-8"), n)


def notes_text(src: str, n: int | None = None) -> str:
    """`lean_notes` of a Lean source; `n` names the `theorem PropN` whose docstring is
    blanked."""
    skip = None
    if n is not None:
        span = heath.theorem_span(src, n)
        if span is not None:
            skip = span.start
    spans = []   # (first, last) character of each note's text
    i, depth, inner = 0, 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            if depth == 0:
                opener = 3 if src.startswith(("/--", "/-!"), i) else 2
                inner = i + opener if i != skip else -1
            depth += 1
            i += 2
        elif depth and src.startswith("-/", i):
            depth -= 1
            if depth == 0 and inner >= 0:
                spans.append((inner, i))
            i += 2
        elif depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
        else:
            i += 1
    out = re.sub(r"[^\n]", " ", src)
    for a, b in spans:
        out = out[:a] + src[a:b] + out[b:]
    return out


def lean_files() -> list[Path]:
    return sorted((ROOT / "Elements").rglob("*.lean"))


# ---------------------------------------------------------------------------------------
# The text rules. Each pattern is matched on the text the rule names (raw, without code,
# or outside quotations); every match is one finding.

# Between two words of a phrase: spaces, or one line break with the next line's indent
# and its comment leader ("--" in Lean, ">" in a Markdown quotation), so that a phrase is
# found however a line or a comment wraps it. A blank line ends the phrase. ANY_GAP is
# GAP or any white space, a blank line included: the gap of S2's "first mate" and of
# "Definition N", which have always been found across one.
GAP = r"(?:[ \t]+|[ \t]*\n[ \t]*(?:(?:--|>)[ \t]*)?)"
ANY_GAP = rf"(?:\s+|{GAP})"
LEADER = re.compile(r"\n[ \t]*(?:--|>)")


def flat(s: str) -> str:
    """A match on one line, as a finding shows it: "Lean\\n  -- cannot" is "Lean cannot"."""
    return " ".join(LEADER.sub(" ", s).split())


def phrase(*ps: str, gap: str = GAP) -> str:
    """The alternatives `ps`, each a pattern whose spaces stand for `gap`: "Lean cannot"
    matches "Lean cannot", "Lean\\ncannot" and "Lean\\n  -- cannot"."""
    return "(?:" + "|".join(p.replace(" ", gap) for p in ps) + ")"


def words(*ws: str) -> str:
    """Whole words of a list, plurals and possessives allowed: crew, crews, crew's. The
    words of "first mate" may stand apart by any white space, or wrap as GAP allows."""
    return r"\b" + phrase(*ws, gap=ANY_GAP) + r"(?:s|es)?\b"


EM_DASH = re.compile("—")
CREW = re.compile(words("crew", "captain", "first mate", "bosun", "sailor", "voyage", "fleet",
                        "enforcer", "polisher"), re.I)
# "Book I was …" is a book, not a person: an "I" right after the word "Book" or "Books"
# and one space, on one line, is passed over. After any other gap ("Book  I", "Book\nI")
# it is found, as it always was.
FIRST_PERSON = re.compile(r"(?<!\bBook )(?<!\bBooks )"
                          + phrase(r"\bI (?:am|was|have|think|found|would)\b")
                          + r"|\b[Mm](?:y|e)\b")
HEDGE = re.compile(phrase(r"\bnote that\b", r"\bstrictly speaking\b", r"\bit is worth noting\b"),
                   re.I)
# "never need" or "never needs" with Postulate 5, a postulate, parallels or "it" later in
# the same clause: "never need it", "I.1 to I.28 never need the fifth postulate".
EUCLID_CITES = re.compile(phrase(
    r"\bEuclid cites\b", r"\bEuclid's own bracketed\b",
    r"\bnever needs?\b(?=[^.;:!?]{0,40}?\b(?:it|postulates?|parallels?)\b)"), re.I)
TACIT = re.compile(phrase(r"\btacit (?:assumptions?|laws?)\b"), re.I)
DEFINITION = re.compile(phrase(r"\b(?:Definitions?|Defs?\.) \d+\b", gap=ANY_GAP))
CURLY = re.compile("[“”‘’]")
# Between two letters of S9's run: GAP, with commas among its spaces and tabs ("*AB, CD*",
# "*AB,\nCD*"). A blank line ends the run.
LETTER_GAP = r"(?:[ \t,]+|[ \t,]*\n[ \t]*(?:(?:--|>)[ \t]*)?[ \t,]*)"
ITALIC_LETTER = re.compile(r"(?:^|[^*])(\*[A-Z]+[′₀-₉]*(?:" + LETTER_GAP + r"[A-Z]+[′₀-₉]*)*\*)"
                           r"(?:$|[^*])", re.M)
TEX = re.compile(r"\\|\^\{|\$")
LEAN_CANNOT = re.compile(phrase(r"\bLean (?:cannot|can't|can not)\b"), re.I)
NO_CITATION = re.compile(phrase(r"\bno citations?\b"), re.I)
COMPARISON = re.compile(r"\b(?:first|only|better|best|unlike)\b", re.I)
NEED = re.compile(r"\bneed(?:s|ed)?\b", re.I)
POSTULATE_5 = re.compile(phrase(r"\bPostulate 5\b", r"\bPost\. 5\b", r"\bparallel postulate\b",
                                r"\bfifth postulate\b"), re.I)

# S11: retired refrains of STYLE section 3, and the mishnah allowed each ("nowhere" is
# the empty set).
REFRAINS = [
    (re.compile(phrase(r"\bcertificate (?:cites|records)\b")), set()),
    (re.compile(phrase(r"\bOf the postulates\b")), set()),
    (re.compile(phrase(r"\bbesides Euclid's\b")), set()),
    (re.compile(phrase(r"\bjust Euclid's three\b")), set()),
    (re.compile(phrase(r"\bcomes in through\b")), {"I.29"}),
    (re.compile(phrase(r"\bLean (?:wants it said|asks why|makes us say so)\b")),
     {"I.1", "I.5", "I.22"}),
    (re.compile(phrase(r"\b[Uu]ses Postulate 1\b")), {"I.1", "I.3"}),
    (re.compile(phrase(r"\bbrings it in\b")), {"I.1", "I.3"}),
    (re.compile(phrase(r"\bwith no letter\b")), set()),
    (re.compile(phrase(r"\bproves it once\b")), set()),
    (re.compile(phrase(r"\bWe give his argument once\b")), set()),
    (re.compile(phrase(r"\band the Lean cites it\.")), set()),
]
RETIRED_LEADS = re.compile(
    r"^\*\*" + phrase(r"What Lean made us say\.", r"What else Lean made us say\.",
                      r"What it rests on\.", r"Where the parallels meet\.", r"Naming the pieces\.",
                      r"Where [A-Z]+ falls\.") + r"\*\*", re.M)
UNDER_I31 = re.compile(phrase(r"\bunder I\.31\b"))
PROCLUS = re.compile(r"\bProclus\b")


def proclus_under_i31(text: str) -> list[tuple[int, int]]:
    """S11's "under I.31" in a sentence naming Proclus: the span of each in `text`."""
    spans = []
    for off, sent in sentences(text):
        m = UNDER_I31.search(sent)
        if m and PROCLUS.search(sent):
            spans.append((off + m.start(), off + m.end()))
    return spans


def find_all(rule: str, pattern: re.Pattern, path: Path, text: str, shown: str | None = None,
             *, failing: bool = True, what: str = "") -> None:
    """Each match of `pattern` in `text` (already blanked as the rule asks) is a finding.
    `shown` is the text the excerpt is taken from, so the reader sees the words."""
    shown = text if shown is None else shown
    for m in pattern.finditer(text):
        a, b = (m.span(1) if m.groups() and m.group(1) else m.span())
        found = flat(m.group(1) if m.groups() and m.group(1) else m.group(0))
        msg = f'{what}"{found}": {excerpt(shown, a, b)}'
        (fail if failing else report)(rule, path, line_of(text, a), msg)


def check_text(path: Path, raw: str, scopes: set[str]) -> None:
    """The text rules for one file, by the scopes it belongs to."""
    raw = raw.replace("\r\n", "\n")
    straight = straighten(raw)
    code_free = blank_code(straight)
    outside = blank_quotes(code_free)
    prose, cat, readme = "prose" in scopes, "catalogue" in scopes, "readme" in scopes
    notes, gen = "lean" in scopes, "generated" in scopes

    if prose or cat or readme or notes:
        find_all("S1", EM_DASH, path, blank_code(raw), raw)
        find_all("S2", CREW, path, outside, raw)
        find_all("S3", FIRST_PERSON, path, outside, raw)
    if prose or cat or notes:
        find_all("S4", HEDGE, path, outside, raw)
    if prose or cat or readme or notes or gen:
        find_all("S5", EUCLID_CITES, path, outside, raw)
    if prose or gen:
        find_all("S6", TACIT, path, outside, raw)
    elif cat or readme or notes:
        find_all("D10", TACIT, path, outside, raw, failing=False)
    defs = SQUARE.sub(_blank, outside)
    if prose:
        find_all("S7", DEFINITION, path, defs, raw)
    elif cat or readme or notes:
        find_all("D10", DEFINITION, path, defs, raw, failing=False)
    if prose or cat:
        find_all("S8", CURLY, path, blank_code(raw), raw)
    if prose or cat or notes:
        find_all("S9", ITALIC_LETTER, path, code_free, raw)
    if prose or readme:
        find_all("D6", COMPARISON, path, outside, raw, failing=False)
    if prose or cat or notes:
        find_all("D7", LEAN_CANNOT, path, outside, raw, failing=False)
    if prose or cat:
        find_all("D8", NO_CITATION, path, outside, raw, failing=False)
    if prose or cat or readme or notes:
        for off, sent in sentences(outside):
            if NEED.search(sent) and POSTULATE_5.search(sent):
                m = NEED.search(sent)
                report("D9", path, line_of(outside, off + m.start()),
                       excerpt(raw, off + m.start(), off + m.end(), 70))


# ---------------------------------------------------------------------------------------
# The mishnah: TeX, refrains, shape, Lean names.

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_.₀-₉]*")
FILE_NAME = re.compile(r".*\.(?:lean|json|md|svg|py|toml|txt|lock)$")


def lean_names(text: str) -> list[str]:
    """The backticked Lean names of a text, file names aside, in order of first use."""
    names = []
    for m in CODE_SPAN.finditer(FENCE.sub(_blank, text)):
        inner = m.group(0)[1:-1].strip()
        if IDENT.fullmatch(inner) and not FILE_NAME.fullmatch(inner) and inner not in names:
            names.append(inner)
    return names


def check_mishnah(path: Path, raw: str) -> None:
    ref = ref_of(path)
    text = FENCE.sub(_blank, HTML_COMMENT.sub(_blank, raw))
    for m in TEX.finditer(text):
        fail("S10", path, line_of(text, m.start()), f'"{m.group(0)}": {excerpt(raw, m.start(), m.end())}')
    for pattern, allowed in REFRAINS:
        if ref in allowed:
            continue
        for m in pattern.finditer(text):
            where = ("only " + ", ".join(sorted(allowed, key=heath.prop_key))) if allowed else "nowhere"
            fail("S11", path, line_of(text, m.start()),
                 f'"{flat(m.group(0))}" (allowed {where}): {excerpt(raw, m.start(), m.end())}')
    for a, b in proclus_under_i31(text):
        fail("S11", path, line_of(text, a),
             f'"under I.31" beside Proclus (allowed nowhere): {excerpt(raw, a, b)}')
    for m in RETIRED_LEADS.finditer(text):
        fail("S11", path, line_of(text, m.start()), f"retired lead {flat(m.group(0))}")

    # Its usual shape (reported).
    count = len(text.split())
    if not 250 <= count <= 450:
        report("D1", path, 1, f"{count} words")
    paras = list(paragraphs(text))
    if not 3 <= len(paras) <= 5:
        report("D2", path, 1, f"{len(paras)} paragraphs")
    for k, (off, p) in enumerate(paras, 1):
        n = len(p.split())
        if n > 120:
            report("D2", path, line_of(text, off), f"paragraph {k} is {n} words")
        if not re.match(r'\*\*(?:[^*]|\*[^*]+\*)+?[.?]["\']?\*\*(?:\s|$)', p):
            report("D3", path, line_of(text, off), f"paragraph {k} has no bold lead: {p[:60]}…")
    if paras and not paras[-1][1].startswith("**The modern way.**"):
        report("D3", path, line_of(text, paras[-1][0]), "the last paragraph is not **The modern way.**")
    names = lean_names(raw)
    if len(names) > 4:
        report("D4", path, 1, f"{len(names)} Lean names: {', '.join(names)}")


def check_lean_names(mishnah: list[Path]) -> int:
    """S12: every backticked name in the mishnah is one Lean knows, with `Elements`,
    `Elements.Book<book>` and `Elements.Tacit` open. One Lean run checks every book, each
    in its own section. Returns how many names were put to Lean."""
    lines = ["import Elements"]
    where: dict[int, tuple[str, list[Path]]] = {}
    by_book: dict[str, dict[str, list[Path]]] = defaultdict(lambda: defaultdict(list))
    for path in mishnah:
        for name in lean_names(path.read_text(encoding="utf-8")):
            by_book[path.parent.name][name].append(path)
    for book in sorted(by_book, key=heath.arabic):
        lines += ["", "section", f"open Elements Elements.Book{book} Elements.Tacit"]
        for name in sorted(by_book[book]):
            lines.append(f"#check @{name}")
            where[len(lines)] = (name, by_book[book][name])
        lines.append("end")
    with tempfile.TemporaryDirectory() as tmp:
        probe = Path(tmp) / "StyleNames.lean"
        probe.write_text("\n".join(lines) + "\n", encoding="utf-8")
        try:
            run = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT,
                                 capture_output=True, text=True, timeout=900)
        except (OSError, subprocess.TimeoutExpired) as e:
            fail("S12", ROOT / "mishnah", 0, f"could not run Lean ({e}); build the tree with "
                 "`lake build`, or pass --no-lean")
            return 0
    out = run.stdout + run.stderr
    errors = list(re.finditer(rf"{re.escape(probe.name)}:(\d+):\d+: error(?:\([^)]*\))?: (.*)", out))
    if run.returncode != 0 and not errors:
        fail("S12", ROOT / "mishnah", 0, "Lean failed before checking a name (is the tree "
             "built? run `lake build`, or pass --no-lean):\n      " + out.strip()[:400])
        return 0
    for m in errors:
        line = int(m.group(1))
        if line not in where:
            fail("S12", ROOT / "mishnah", 0, f"Lean: {m.group(2)} (is the tree built? run "
                 "`lake build`, or pass --no-lean)")
            continue
        name, paths = where[line]
        for path in paths:
            raw = path.read_text(encoding="utf-8")
            at = max(raw.find(f"`{name}`"), 0)
            fail("S12", path, line_of(raw, at), f"`{name}`: {m.group(2).strip()}")
    return len(where)


# ---------------------------------------------------------------------------------------
# Further reading and the introductions.

WEB_LINK = re.compile(r"\]\((https?://[^)\s]+)\)|href=\"(https?://[^\"]+)\"")


def reading_links() -> set[str]:
    text = (ROOT / "docs" / "reading.md").read_text(encoding="utf-8")
    return {a or b for a, b in WEB_LINK.findall(text)}


def check_reading(path: Path, raw: str, allowed: set[str]) -> None:
    lines = [(k, l) for k, l in enumerate(raw.splitlines(), 1) if l.strip()]
    if not 1 <= len(lines) <= 3:
        fail("S17", path, 1, f"{len(lines)} lines; a reading file has one to three")
    for k, l in lines:
        if not l.startswith("- "):
            fail("S17", path, k, f"not a list item: {l[:60]}")
        elif not l.startswith("- For "):
            report("D13", path, k, l[2:62] + "…")
    for m in WEB_LINK.finditer(raw):
        url = m.group(1) or m.group(2)
        if url not in allowed:
            fail("S17", path, line_of(raw, m.start()), f"{url} is not given by docs/reading.md")


def check_intros() -> None:
    present = {p.stem for p in intro_files()}
    for book in books_with_pages():
        has_pages = any((ROOT / d / book).is_dir() for d in ("mishnah", "book"))
        if has_pages and book not in present:
            fail("S18", ROOT / "mishnah" / "intro", 0, f"Book {book} has pages and no "
                 f"mishnah/intro/{book}.md")
    for path in intro_files():
        raw = path.read_text(encoding="utf-8")
        if not re.search(rf"\]\([^)]*briefs/(?:\d{{4}}-)?book-{re.escape(path.stem)}\.md(?:#[^)]*)?\)", raw):
            fail("S19", path, 1, f"no link to Book {path.stem}'s brief in docs/briefs/")


# ---------------------------------------------------------------------------------------
# Figures.

SVG = "{http://www.w3.org/2000/svg}"
IDEA_COLOURS = {"#fbf7ee", "#d0312d", "#f2b705", "#1f5aa6", "#222222"}
WHITE = {"#fff", "#ffffff", "white"}
EUCLID_COLOURS = {"#fbf7ee", "#3b2f2f", "#8c7b62", "#a0522d", "#e9dcc0"}
COLOUR_ATTRS = ("fill", "stroke", "stop-color", "color", "flood-color", "lighting-color")
DRAWN = {"line", "path", "polyline", "polygon", "circle", "ellipse", "rect"}
FILLED = DRAWN - {"line"}
INHERITED = ("fill", "fill-rule", "stroke", "stroke-width", "font-size", "font-style",
             "text-anchor")
LETTER = re.compile(r"[A-Z][′'₀-₉]*")

# The letters of a figure at a glance (S20, S21; STYLE, section 7). Lengths are in the
# canvas's units, 400 × 300.
IDEA_INK = "#222222"            # a letter on the parchment or on yellow
IDEA_INK_ON_DARK = "#fbf7ee"    # a letter on red, blue or black, in the parchment's colour
DARK = {"#d0312d", "#1f5aa6", "#222222"}
IDEA_LETTER_SIZE = 14
BYRNE = {"#d0312d", "#f2b705", "#1f5aa6", "#222222"}
NEAR = 30.0      # the farthest a letter's centre may stand from its point
MARK = 25.0      # a straight line shorter than this is a mark (an equals sign), not a point
SAME = 8.0       # points nearer than this are one point (a corner where two lines end)
DOT = 6.0        # a filled circle of this radius at most is a dot
UNLETTERED = "data-unlettered"
NUM = re.compile(r"[-+]?(?:\d+\.?\d*|\.\d+)(?:[eE][-+]?\d+)?")
IDENTITY = (1.0, 0.0, 0.0, 1.0, 0.0, 0.0)

# A path's `d`, read for the fill a letter stands on (S20): its commands, the numbers each
# takes, and how finely its arcs and curves are followed in straight pieces.
PATH_COMMAND = re.compile(r"[\s,]*([MmZzLlHhVvCcSsQqTtAa])")
PATH_NUMBER = re.compile(r"[\s,]*(" + NUM.pattern + ")")
PATH_FLAG = re.compile(r"[\s,]*([01])")
PATH_ARITY = {"m": 2, "l": 2, "h": 1, "v": 1, "c": 6, "s": 4, "q": 4, "t": 2, "a": 7}
ARC_STEP = math.radians(3)   # an arc, in a straight piece to each 3 degrees of its sweep
CURVE_STEPS = 32             # a Bézier curve, in this many straight pieces

# data-unlettered marks in the idea figures, printed on every run:
# {(file, reason): [elements, points]}
idea_exemptions: dict[tuple[str, str], list[int]] = defaultdict(lambda: [0, 0])


def tag(el) -> str:
    return el.tag[len(SVG):] if el.tag.startswith(SVG) else el.tag


def style_of(el) -> dict[str, str]:
    """An element's presentation attributes, its `style` declarations overriding them."""
    attrs = {k: v.strip() for k, v in el.attrib.items()}
    for decl in attrs.pop("style", "").split(";"):
        if ":" in decl:
            k, v = decl.split(":", 1)
            attrs[k.strip()] = v.strip()
    return attrs


def walk(el, inherited=None):
    """(element, its own attributes, its effective inherited ones) for the whole tree."""
    for el, own, eff, _, _ in placed(el, IDENTITY, inherited):
        yield el, own, eff


def placed(el, m=IDENTITY, inherited=None, exempt=None):
    """walk(), with each element's place: (element, own attributes, effective inherited
    ones, its transform composed with its ancestors', and the data-unlettered in force as
    (the element that carries it, its reason), or None)."""
    inherited = dict(inherited or {})
    own = style_of(el)
    eff = dict(inherited)
    eff.update({k: own[k] for k in INHERITED if k in own})
    m = compose(m, transform_of(own.get("transform")))
    if UNLETTERED in el.attrib:
        exempt = (el, " ".join(el.attrib[UNLETTERED].split()))
    yield el, own, eff, m, exempt
    for child in el:
        yield from placed(child, m, eff, exempt)


def text_of(el) -> str:
    return "".join(el.itertext()).strip()


def number(value: str | None) -> float | None:
    if value is None:
        return None
    m = re.fullmatch(r"\s*([0-9.]+)\s*(?:px)?\s*", value)
    return float(m.group(1)) if m else None


def coord(value: str | None) -> float:
    """A coordinate attribute's first number (x="10" or x="10 24"), or 0, SVG's default."""
    m = NUM.search(value or "")
    return float(m.group(0)) if m else 0.0


def compose(a, b):
    """The affine map a after b, each as the six numbers of SVG's matrix(a b c d e f)."""
    return (a[0] * b[0] + a[2] * b[1], a[1] * b[0] + a[3] * b[1],
            a[0] * b[2] + a[2] * b[3], a[1] * b[2] + a[3] * b[3],
            a[0] * b[4] + a[2] * b[5] + a[4], a[1] * b[4] + a[3] * b[5] + a[5])


def transform_of(value: str | None):
    """A `transform` attribute as one affine map: translate, scale, rotate, skewX, skewY
    and matrix, applied as SVG applies them, the last first."""
    m = IDENTITY
    for name, args in re.findall(r"([A-Za-z]+)\s*\(([^)]*)\)", value or ""):
        v = [float(x) for x in NUM.findall(args)]
        if not v:
            continue
        if name == "translate":
            t = (1.0, 0.0, 0.0, 1.0, v[0], v[1] if len(v) > 1 else 0.0)
        elif name == "scale":
            t = (v[0], 0.0, 0.0, v[1] if len(v) > 1 else v[0], 0.0, 0.0)
        elif name == "rotate":
            c, s = math.cos(math.radians(v[0])), math.sin(math.radians(v[0]))
            t = (c, s, -s, c, 0.0, 0.0)
            if len(v) >= 3:
                t = compose(compose((1.0, 0.0, 0.0, 1.0, v[1], v[2]), t),
                            (1.0, 0.0, 0.0, 1.0, -v[1], -v[2]))
        elif name == "skewX":
            t = (1.0, 0.0, math.tan(math.radians(v[0])), 1.0, 0.0, 0.0)
        elif name == "skewY":
            t = (1.0, math.tan(math.radians(v[0])), 0.0, 1.0, 0.0, 0.0)
        elif name == "matrix" and len(v) == 6:
            t = tuple(v)
        else:
            continue
        m = compose(m, t)
    return m


def at(m, x: float, y: float) -> tuple[float, float]:
    return (m[0] * x + m[2] * y + m[4], m[1] * x + m[3] * y + m[5])


def back(m, x: float, y: float) -> tuple[float, float] | None:
    """The point that the affine map m takes to (x, y), or None if m flattens the plane."""
    det = m[0] * m[3] - m[1] * m[2]
    if abs(det) < 1e-12:
        return None
    x, y = x - m[4], y - m[5]
    return ((m[3] * x - m[2] * y) / det, (m[0] * y - m[1] * x) / det)


def bezier(ps, t: float) -> tuple[float, float]:
    """The point at t of the Bézier curve with control points ps (de Casteljau)."""
    while len(ps) > 1:
        ps = [(a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1])) for a, b in zip(ps, ps[1:])]
    return ps[0]


def arc_points(x1: float, y1: float, rx: float, ry: float, phi: float, large: float,
               sweep: float, x2: float, y2: float) -> list[tuple[float, float]]:
    """An elliptical arc of a path, from (x1, y1) to (x2, y2), as the points along it after
    the first, its centre found from its ends as SVG's implementation notes find it."""
    if (x1, y1) == (x2, y2):
        return []
    rx, ry = abs(rx), abs(ry)
    if rx == 0 or ry == 0:
        return [(x2, y2)]
    c, s = math.cos(math.radians(phi)), math.sin(math.radians(phi))
    dx, dy = (x1 - x2) / 2, (y1 - y2) / 2
    px, py = c * dx + s * dy, -s * dx + c * dy
    grow = (px / rx) ** 2 + (py / ry) ** 2
    if grow > 1:
        rx, ry = rx * math.sqrt(grow), ry * math.sqrt(grow)
    num = (rx * ry) ** 2 - (rx * py) ** 2 - (ry * px) ** 2
    k = math.sqrt(max(0.0, num / ((rx * py) ** 2 + (ry * px) ** 2)))
    if large == sweep:
        k = -k
    qx, qy = k * rx * py / ry, -k * ry * px / rx
    cx, cy = c * qx - s * qy + (x1 + x2) / 2, s * qx + c * qy + (y1 + y2) / 2
    start = math.atan2((py - qy) / ry, (px - qx) / rx)
    turn = (math.atan2((-py - qy) / ry, (-px - qx) / rx) - start) % math.tau
    if not sweep and turn > 0:
        turn -= math.tau
    n = max(1, math.ceil(abs(turn) / ARC_STEP))
    pts = []
    for i in range(1, n):
        a = start + turn * i / n
        ex, ey = rx * math.cos(a), ry * math.sin(a)
        pts.append((cx + c * ex - s * ey, cy + s * ex + c * ey))
    return pts + [(x2, y2)]


def path_rings(d: str) -> list[list[tuple[float, float]]]:
    """A path's subpaths as the rings of points its fill closes: straight segments as they
    are, arcs and curves in short straight pieces. A path is read as far as it is well
    formed, as SVG draws it."""
    rings: list[list[tuple[float, float]]] = []
    ring: list[tuple[float, float]] = []
    x = y = sx = sy = 0.0
    cmd, ctrl, pos = "", None, 0
    while True:
        found = PATH_COMMAND.match(d, pos)
        if found:
            cmd, pos = found.group(1), found.end()
        elif cmd in ("", "Z", "z"):
            break
        kind = cmd.lower()
        if kind == "z":
            if len(ring) > 1:
                rings.append(ring)
            ring, x, y, ctrl = [(sx, sy)], sx, sy, None
            continue
        args = []
        for i in range(PATH_ARITY[kind]):
            got = (PATH_FLAG if kind == "a" and i in (3, 4) else PATH_NUMBER).match(d, pos)
            if not got:
                break
            args.append(float(got.group(1)))
            pos = got.end()
        if len(args) < PATH_ARITY[kind]:
            break
        ox, oy = (x, y) if cmd.islower() else (0.0, 0.0)
        pairs = [(ox + args[i], oy + args[i + 1]) for i in range(0, len(args) - 1, 2)]
        if kind == "m":
            if len(ring) > 1:
                rings.append(ring)
            (x, y), ctrl = pairs[0], None
            sx, sy, ring = x, y, [(x, y)]
            cmd = "l" if cmd == "m" else "L"
            continue
        if kind == "h":
            pts, ctrl = [(ox + args[0], y)], None
        elif kind == "v":
            pts, ctrl = [(x, oy + args[0])], None
        elif kind == "l":
            pts, ctrl = pairs, None
        elif kind == "a":
            pts = arc_points(x, y, *args[:5], ox + args[5], oy + args[6])
            ctrl = None
        else:
            if kind in "st":
                same = ctrl is not None and ctrl[0] == ("c" if kind == "s" else "q")
                pairs.insert(0, (2 * x - ctrl[1][0], 2 * y - ctrl[1][1]) if same else (x, y))
            curve = [(x, y)] + pairs
            pts = [bezier(curve, i / CURVE_STEPS) for i in range(1, CURVE_STEPS + 1)]
            ctrl = ("c" if kind in "cs" else "q", curve[-2])
        ring += pts
        x, y = ring[-1]
    if len(ring) > 1:
        rings.append(ring)
    return rings


def enclosed(rings, x: float, y: float, evenodd: bool) -> bool:
    """Whether (x, y) lies within the rings by SVG's fill rule, nonzero or evenodd."""
    winding = 0
    for ring in rings:
        for (x1, y1), (x2, y2) in zip(ring, ring[1:] + ring[:1]):
            if (y1 > y) != (y2 > y) and x < x1 + (y - y1) * (x2 - x1) / (y2 - y1):
                winding += 1 if y2 > y1 else -1
    return winding % 2 == 1 if evenodd else winding != 0


def inside(el, own, x: float, y: float, evenodd: bool = False) -> bool:
    """Whether (x, y), in the element's own coordinates, lies within the fill of a polygon,
    polyline, path, rect, circle or ellipse."""
    t = tag(el)
    if t in ("polygon", "polyline"):
        v = [float(n) for n in NUM.findall(own.get("points", ""))]
        return enclosed([list(zip(v[0::2], v[1::2]))], x, y, evenodd)
    if t == "path":
        return enclosed(path_rings(own.get("d", "")), x, y, evenodd)
    if t == "rect":
        x0, y0 = coord(own.get("x")), coord(own.get("y"))
        return x0 <= x <= x0 + coord(own.get("width")) and y0 <= y <= y0 + coord(own.get("height"))
    if t == "circle":
        return math.dist((x, y), (coord(own.get("cx")), coord(own.get("cy")))) <= coord(own.get("r"))
    if t == "ellipse":
        rx, ry = coord(own.get("rx")), coord(own.get("ry"))
        return rx > 0 and ry > 0 and ((x - coord(own.get("cx"))) / rx) ** 2 + (
            (y - coord(own.get("cy"))) / ry) ** 2 <= 1
    return False


def fill_under(root, x: float, y: float) -> str:
    """The colour a letter's middle stands on: the fill of the last polygon, polyline,
    path (an angle's wedge), rect, circle or ellipse drawn over it, not transparent
    (transforms applied), or else the parchment."""
    under = "#fbf7ee"
    for el, own, eff, m, _ in placed(root):
        fill = (eff.get("fill") or "black").strip().lower()
        if tag(el) not in FILLED or fill == "none":
            continue
        opacity = number(own.get("fill-opacity"))
        if opacity is not None and opacity < 0.5:
            continue
        p = back(m, x, y)
        evenodd = (eff.get("fill-rule") or "nonzero").strip() == "evenodd"
        if p is not None and inside(el, own, *p, evenodd):
            under = fill
    return under


def svg_root(path: Path):
    try:
        return ET.parse(path).getroot()
    except ET.ParseError as e:
        fail("S14" if path.stem.endswith("-idea") else "S15", path, 0, f"not well-formed SVG: {e}")
        return None


def caption_text_rules(path: Path, el, kind: str) -> None:
    """S1 and S2 in a figure's title and caption."""
    text = text_of(el)
    if "—" in text:
        fail("S1", path, 0, f"em dash in the {kind}: {text[:60]}")
    for m in CREW.finditer(blank_quotes(text)):
        fail("S2", path, 0, f'"{m.group(0)}" in the {kind}')


def colours(path: Path, root, allowed: set[str], rule: str) -> None:
    bad = defaultdict(int)
    for el, own, _ in walk(root):
        for k in COLOUR_ATTRS:
            v = own.get(k)
            if v is None or v.lower() == "none":
                continue
            if v.lower() not in allowed:
                bad[f"{k}={v}"] += 1
    for what, n in sorted(bad.items()):
        fail(rule, path, 0, f"colour {what} ({n}×) is not in the palette")


def check_idea(path: Path, ref: str, required: bool) -> int:
    """S13, S14, S20 and S21 for one idea figure. Returns how many of its points wait for
    a letter while it is in the transition (no letter yet, the switch off), else 0."""
    root = svg_root(path)
    if root is None:
        return 0
    vb = " ".join(root.get("viewBox", "").replace(",", " ").split())
    if vb != "0 0 400 300":
        fail("S14", path, 0, f"viewBox {vb or 'missing'}, not 0 0 400 300")
    title = root.find(f"{SVG}title")
    if title is None or not text_of(title):
        fail("S14", path, 0, "no <title>")
    else:
        caption_text_rules(path, title, "title")
        if not re.fullmatch(rf"{re.escape(ref)} at a glance(?:: .+)?", " ".join(text_of(title).split())):
            fail("S14", path, 0, f"title \"{text_of(title)}\" is not \"{ref} at a glance\", "
                 "with a name after a colon if it has one")
    desc = root.find(f"{SVG}desc")
    if desc is None or not text_of(desc):
        fail("S13", path, 0, "no caption (<desc>)")
    else:
        caption_text_rules(path, desc, "caption")
        text = " ".join(text_of(desc).split())
        n = len(text.split())
        if n > 50:
            fail("S13", path, 0, f"caption of {n} words; 50 at most")
        ends = len(re.findall(r"[.?!][\"')]*(?=\s|$)", text))
        if n > 40 or ends > 2:
            report("D5", path, 0, f"caption of {n} words, {ends} sentence(s)")
    colours(path, root, IDEA_COLOURS | WHITE, "S14")
    return check_idea_letters(path, root, required)


def drawn_letters(path: Path) -> set[str] | None:
    """The letters Euclid's figure draws, which S16 holds to Heath's text; None when there
    is no figure to read (S15 says why)."""
    try:
        root = ET.parse(path).getroot()
    except (OSError, ET.ParseError):
        return None
    return {text_of(el) for el in root.iter() if tag(el) == "text" and LETTER.fullmatch(text_of(el))}


def letter_centre(own, eff, m, s: str) -> tuple[float, float]:
    """About where a letter's glyph stands: x and y give the start of its baseline (its
    middle or its end, by text-anchor), and a capital in Georgia is about 0.6 em wide and
    0.7 em high."""
    size = number(eff.get("font-size")) or 16.0
    w = 0.6 * size * len(s)
    shift = {"middle": 0.0, "end": -w / 2}.get((eff.get("text-anchor") or "start").strip(), w / 2)
    return at(m, coord(own.get("x")) + shift, coord(own.get("y")) - 0.35 * size)


def idea_points(root) -> list[tuple[str, tuple[float, float], tuple | None]]:
    """(kind, where, exemption) for each point an idea figure shows (S21): a dot (a filled
    circle of radius 6 at most), each end of a straight line drawn in a Byrne colour or
    black and 25 long at least, and each corner of a polygon filled or stroked in one.
    White grid lines, parchment dividers, paths (the angles and arcs) and polylines (the
    right-angle marks) show no points. `exemption` is the data-unlettered in force."""
    out = []
    for el, own, eff, m, exempt in placed(root):
        t = tag(el)
        fill = (eff.get("fill") or "black").strip().lower()
        stroke = (eff.get("stroke") or "none").strip().lower()
        if t == "circle":
            if 0 < coord(own.get("r")) <= DOT and fill != "none":
                out.append(("a dot", at(m, coord(own.get("cx")), coord(own.get("cy"))), exempt))
        elif t == "line" and stroke in BYRNE:
            a = at(m, coord(own.get("x1")), coord(own.get("y1")))
            b = at(m, coord(own.get("x2")), coord(own.get("y2")))
            if math.dist(a, b) >= MARK:
                out += [("an end of a straight line", a, exempt), ("an end of a straight line", b, exempt)]
        elif t == "polygon" and (fill in BYRNE or stroke in BYRNE):
            v = [float(x) for x in NUM.findall(own.get("points", ""))]
            out += [("a corner of a polygon", at(m, x, y), exempt) for x, y in zip(v[0::2], v[1::2])]
    return out


def ink_fault(root, eff, centre: tuple[float, float], s: str) -> str | None:
    """S20's ink for letter s, its glyph's middle at `centre`: what is wrong with it, or
    None. It is #222222 on the parchment or yellow, and #fbf7ee on red, blue or black."""
    dark = fill_under(root, *centre) in DARK
    ink = IDEA_INK_ON_DARK if dark else IDEA_INK
    if (eff.get("fill") or "black").strip().lower() == ink:
        return None
    return (f"letter {s} in {eff.get('fill') or 'black'}, not {ink}: a letter "
            f"on {'red, blue or black' if dark else 'the parchment or yellow'} is in {ink}")


def check_idea_letters(path: Path, root, required: bool) -> int:
    """S20: each letter is one of Heath's, as Euclid's figure draws it, italic, at 14, in
    the figure's black, or in the parchment's colour where it stands on red, blue or
    black. S21: each point the figure shows has a letter within 30 of it, or is marked
    data-unlettered with its reason. Returns the points waiting for a letter while the
    figure is in the transition, else 0."""
    euclid = path.with_name(path.name.replace("-idea", ""))
    heaths = drawn_letters(euclid)
    letters = []
    for el, own, eff, m, _ in placed(root):
        if tag(el) != "text":
            continue
        s = text_of(el)
        if not re.search(r"[A-Za-z]", s):
            continue
        if not LETTER.fullmatch(s):
            fail("S20", path, 0, f"<text>{s}</text>: an idea figure's text is Heath's letters, "
                 "one to a <text>, or numbers on a fill")
            continue
        if heaths is None:
            fail("S20", path, 0, f"letter {s}, and no {euclid.name} to take Heath's letters from")
        elif s not in heaths:
            fail("S20", path, 0, f"letter {s} is not one of Heath's letters as {euclid.name} "
                 f"draws them ({', '.join(sorted(heaths))})")
        centre = letter_centre(own, eff, m, s)
        fault = ink_fault(root, eff, centre, s)
        if fault:
            fail("S20", path, 0, fault)
        if number(eff.get("font-size")) != IDEA_LETTER_SIZE:
            fail("S20", path, 0, f"letter {s} at font-size {eff.get('font-size')}, not {IDEA_LETTER_SIZE}")
        if (eff.get("font-style") or "normal").strip() != "italic":
            fail("S20", path, 0, f"letter {s} is not italic")
        letters.append(centre)

    points = idea_points(root)
    for el in root.iter():
        if UNLETTERED not in el.attrib:
            continue
        why = " ".join(el.attrib[UNLETTERED].split())
        excused = sum(1 for _, _, ex in points if ex is not None and ex[0] is el)
        if len(why.split()) < 2:
            fail("S21", path, 0, f'<{tag(el)} {UNLETTERED}="{why}">: give the reason Heath '
                 "leaves these points without letters, in words")
        if not excused:
            fail("S21", path, 0, f'<{tag(el)} {UNLETTERED}="{why}"> marks no point a letter '
                 "would go to (a dot, an end of a straight line, a corner); remove it")
        tally = idea_exemptions[(rel(path), why)]
        tally[0] += 1
        tally[1] += excused

    groups: list[list] = []
    for p in points:
        for g in groups:
            if math.dist(g[0][1], p[1]) < SAME:
                g.append(p)
                break
        else:
            groups.append([p])
    waiting = []
    for g in groups:
        shown = [p for p in g if p[2] is None]
        if shown and not any(math.dist(p[1], c) <= NEAR for p in shown for c in letters):
            waiting.append(shown)
    if not letters and not required:
        return len(waiting)
    for shown in waiting:
        kinds = " and ".join(sorted({k for k, _, _ in shown}))
        x, y = shown[0][1]
        fail("S21", path, 0, f"the point at ({x:.0f}, {y:.0f}), {kinds}, has no letter "
             f"within {NEAR:g}: give it Heath's letter, or mark what draws it {UNLETTERED} "
             "with the reason his figure gives it none")
    return 0


def heath_letters(book: str, n: int) -> set[str]:
    """The capital letters of Heath's text, as STYLE section 8 gives the command: comments,
    headings, Heath's references, "Q. E. D.", "Q. E. F.", "I say" and "PORISM." taken out,
    then every word wholly in capitals, letter by letter."""
    text = HTML_COMMENT.sub("", heath.heath_path(book, n).read_text(encoding="utf-8"))
    found = set()
    for line in text.splitlines():
        if line.startswith("#"):
            continue
        line = re.sub(r"\[[^\]\n]*\]", "", line)
        line = re.sub(r"Q\. E\. [DF]\.", "", line)
        line = line.replace("I say", "").replace("PORISM.", "")
        for w in re.findall(r"\b[A-Z]+\b", line):
            found.update(w)
    return found


def check_euclid(path: Path, ref: str) -> None:
    root = svg_root(path)
    if root is None:
        return
    book, n = ref.split(".")
    n = int(n)
    vb = root.get("viewBox", "").replace(",", " ").split()
    width = float(vb[2]) if len(vb) == 4 else None
    if width is None or not 400 <= width <= 440:
        fail("S15", path, 0, f"viewBox width {width}, not 400 to 440")
    title = root.find(f"{SVG}title")
    if title is None or not text_of(title):
        fail("S15", path, 0, "no <title>")
    else:
        caption_text_rules(path, title, "title")
        if not re.fullmatch(rf"Euclid {re.escape(ref)}: .+", " ".join(text_of(title).split())):
            fail("S15", path, 0, f"title \"{text_of(title)}\" is not \"Euclid {ref}: …\"")
    if root.find(f".//{SVG}desc") is not None:
        fail("S15", path, 0, "a caption (<desc>): Euclid's figure has none")
    colours(path, root, EUCLID_COLOURS, "S15")

    drawn = set()
    thin, heavy = defaultdict(int), defaultdict(int)
    usual = defaultdict(int)
    for el, own, eff in walk(root):
        t = tag(el)
        if t == "text":
            s = text_of(el)
            if LETTER.fullmatch(s):
                drawn.add(s[0])
                size = number(eff.get("font-size"))
                if size != 17:
                    fail("S15", path, 0, f"letter {s} at font-size {eff.get('font-size')}, not 17")
            continue
        if t not in DRAWN:
            continue
        stroke = (eff.get("stroke") or "none").lower()
        if stroke != "none":
            w = number(eff.get("stroke-width"))
            w = 1.0 if w is None else w
            if w < 1.2:
                thin[w] += 1
            elif w > 3.2:
                heavy[w] += 1
            expected = {"#3b2f2f": (1.6, 1.6), "#8c7b62": (1.3, 1.3), "#a0522d": (2.4, 2.6)}.get(stroke)
            if expected and not expected[0] <= w <= expected[1]:
                usual[f"{stroke} stroke {w:g} (usual {expected[0]:g}"
                      + (f" to {expected[1]:g})" if expected[1] != expected[0] else ")")] += 1
        elif t == "circle" and (eff.get("fill") or "").lower() in ("#3b2f2f", "#a0522d"):
            r = number(own.get("r"))
            if r is not None and r != 2.6:
                usual[f"dot of radius {r:g} (usual 2.6)"] += 1
    for w, k in sorted(thin.items()):
        fail("S15", path, 0, f"stroke-width {w:g} ({k}×) is under 1.2")
    for w, k in sorted(heavy.items()):
        fail("S15", path, 0, f"stroke-width {w:g} ({k}×) is over 3.2")
    if usual:
        report("D11", path, 0, "; ".join(f"{what} ×{k}" for what, k in sorted(usual.items())))

    # S16: all and only Heath's letters.
    text = heath_letters(book, n)
    exc = LETTER_EXCEPTIONS.get((book, n), {})
    extra = drawn - text - exc.get("extra", set())
    missing = text - drawn - exc.get("missing", set())
    if extra:
        fail("S16", path, 0, f"draws {', '.join(sorted(extra))}, not in heath/{book}/{n:02d}.md")
    if missing:
        fail("S16", path, 0, f"does not draw {', '.join(sorted(missing))}, which "
             f"heath/{book}/{n:02d}.md names")
    for side, letters in (("extra", exc.get("extra", set())), ("missing", exc.get("missing", set()))):
        stale = letters - drawn if side == "extra" else letters & drawn
        if stale:
            fail("S16", path, 0, f"the exception for {', '.join(sorted(stale))} in "
                 "LETTER_EXCEPTIONS no longer applies; remove it")


def check_figures(required: bool) -> None:
    for book in books_with_pages():
        d = ROOT / "figures" / book
        waiting = []
        for path in numbered(d, "-idea.svg"):
            left = check_idea(path, ref_of(path), required)
            if left:
                waiting.append(f"{path.name[:2]} ({left})")
        for path in numbered(d, ".svg"):
            check_euclid(path, ref_of(path))
        if waiting:
            report("D14", d, 0, f"{len(waiting)} without letters, with the points each "
                   f"has to letter: {', '.join(waiting)}")


# ---------------------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--no-lean", action="store_true",
                        help="skip S12, which needs a built tree")
    parser.add_argument("--quiet", action="store_true",
                        help="give the reports as counts, without each finding")
    parser.add_argument("--require-idea-letters", action="store_true",
                        help="hold every idea figure to S21, as IDEA_LETTERS_REQUIRED = True "
                             "does; it is on, so this changes nothing unless it is turned off")
    args = parser.parse_args()
    required = IDEA_LETTERS_REQUIRED or args.require_idea_letters

    mishnah = mishnah_files()
    for path in mishnah:
        raw = path.read_text(encoding="utf-8")
        check_text(path, raw, {"prose"})
        check_mishnah(path, raw)
    for path in intro_files():
        check_text(path, path.read_text(encoding="utf-8"), {"prose"})
    allowed = reading_links()
    for path in reading_files():
        raw = path.read_text(encoding="utf-8")
        check_text(path, raw, {"prose"})
        check_reading(path, raw, allowed)
    for path in catalogue_files():
        check_text(path, path.read_text(encoding="utf-8"), {"catalogue"})
    check_text(ROOT / "README.md", readme_text(), {"readme"})
    for path in lean_files():
        check_text(path, lean_notes(path), {"lean"})
    for path in generated_files():
        check_text(path, path.read_text(encoding="utf-8"), {"generated"})
    check_intros()
    check_figures(required)
    if "D14" in reports:
        print("note: S21 holds only the idea figures that carry a letter, until "
              "IDEA_LETTERS_REQUIRED is set (STYLE, section 8); D14 lists the rest")
    if args.no_lean:
        print("note: S12 skipped (--no-lean); the mishnah's Lean names were not checked")
    elif shutil.which("lake") is None:
        fail("S12", ROOT / "mishnah", 0, "`lake` is not on the PATH; build the tree, or pass --no-lean")
    else:
        names = check_lean_names(mishnah)
        print(f"S12: {names} backticked names of the mishnah put to Lean, book by book")

    if not args.quiet:
        print("Exceptions the script allows, each with its reason:")
        for (book, n), exc in sorted(LETTER_EXCEPTIONS.items(), key=lambda x: heath.prop_key(f"{x[0][0]}.{x[0][1]}")):
            letters = sorted(exc.get("extra", set()) | exc.get("missing", set()))
            print(f"  S16 figures/{book}/{n:02d}.svg ({', '.join(letters)}): {exc['why']}")
        for (f, why), (elements, points) in sorted(idea_exemptions.items()):
            print(f"  S21 {f} ({elements} marked {UNLETTERED}, {points} point(s)): {why}")
    if reports:
        total = sum(len(v) for v in reports.values())
        print(f"Reported for a reader to judge ({total}; these fail nothing):")
        for rule in sorted(reports, key=lambda r: int(r[1:])):
            hits = reports[rule]
            print(f"  {rule} {REPORTS[rule]}: {len(hits)}")
            if not args.quiet:
                for f, line, msg in hits:
                    print(f"      {f}{':' + str(line) if line else ''}: {msg}")
    if failures:
        print(f"\n{len(failures)} style failure(s) (docs/STYLE.md, section 8):")
        for rule, f, line, msg in sorted(failures, key=lambda x: (int(x[0][1:]), x[1], x[2])):
            print(f"  ✗ {rule} {f}{':' + str(line) if line else ''}: {msg}")
        by_rule = defaultdict(int)
        for rule, *_ in failures:
            by_rule[rule] += 1
        print("  by rule: " + ", ".join(f"{r} {RULES[r]} ({k})"
                                       for r, k in sorted(by_rule.items(), key=lambda x: int(x[0][1:]))))
        return 1
    rules = "S1–S21" if not args.no_lean else "S1–S11 and S13–S21"
    print(f"\n✓ style: the hard rules hold ({rules})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
