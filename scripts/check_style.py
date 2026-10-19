"""Check the house style's hard rules, and report its defaults.

The rules are those of docs/STYLE.md, section 8, which is their one home: S1 to S22
fail the script, and D4 to D11, D14 and D15 are listed for a reader to judge and fail
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

S10 refuses TeX in the mishnah, save `$…$` in a paragraph that opens
`**The modern way.**`, which ends where Markdown ends a paragraph (`MODERN_WAY_ENDS`);
and there it refuses the shapes of span known to break on GitHub (STYLE, section
4, "Mathematics"). Sample spans tried on GitHub on 18 October found most of them, and
showed its Markdown taking away backslashes inside a span, so Markdown reads there; by
CommonMark's rules for emphasis, checked with a CommonMark parser and not tried on GitHub,
a `*`, or a `_` after anything but a letter or a digit, pairs with another across two
spans, so a span holds no `*`, `~` or backtick, and a `_` only straight after a letter or
a digit. A shape not yet found may still break: the reviewer's checklist, item 5 (STYLE,
section 8), which sees each span rendered on GitHub, stays the guard. The tests hold
cases on both sides of that boundary.

S2's crew words match whole words in any case, plurals and possessives included ("the
bosuns", "the crew's"). The figure rules also ask for a <title>: "I.N at a glance" on an
idea figure, "Euclid I.N: …" on Euclid's (STYLE, section 7). A known departure a rule
cannot see is right is listed below with its reason, and printed on every run; one that
no longer applies fails. An idea figure marks a point Heath leaves without a letter in the
figure itself, with `data-unlettered` and its reason (S21), and those are printed too.
S20 judges a letter's ink by the fill under it, an angle's wedge included. S22 measures
a letter as Georgia draws its capital, upright or italic, by the convex hull of its
outline's points (GLYPHS_UPRIGHT, GLYPHS_ITALIC), against every stroke and dot of its
figure and the canvas's edge.

How the rules read a phrase, S10's boundary for TeX, how S20 reads a letter on and beside
an angle's wedge, and how S22 measures a letter against the strokes beside it are tested
case by case in tests/test_check_style.py, which needs no Lean. CI runs it just before
this script, in the order of docs/WORKFLOW.md, section 8; a defect fixed in that reading
comes with a case there. Standard library only.
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

# Upright letters, the switch (STYLE, sections 4, 7 and 8). Heath's letters take one style
# in the text and in the figures, upright, by the owner's decision of 18 October. The
# figures were drawn with italic letters and are set upright in a change of their own;
# while they are, this is False: S15 and S20 take a figure's letters italic or upright, one
# style in each figure, and D15 lists the figures still italic. Once every figure is
# upright it is True, and S15 and S20 fail an italic letter. Never set it back to quiet a
# figure: set the figure upright.
UPRIGHT_LETTERS_REQUIRED = False

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
    "S10": "TeX in the mishnah, outside a well-formed $…$ of the modern way",
    "S11": "a retired refrain",
    "S12": "a backticked Lean name that Lean does not know",
    "S13": "an idea figure's caption missing or over 50 words",
    "S14": "an idea figure's canvas, colours or title",
    "S15": "a Euclid's figure's canvas, letters, colours, strokes, caption or title",
    "S16": "figure letters not all and only Heath's",
    "S17": "a further-reading file's shape or links",
    "S18": "a book with pages and no introduction",
    "S19": "a book introduction that does not link the book's brief",
    "S20": "an idea figure's letter not Heath's, or not in the figure's one style, at 14 and in the ink of what it stands on",
    "S21": "a point of an idea figure without its letter",
    "S22": "one letter, one point: a letter drawn twice in a figure, or near a stroke, a dot or the edge",
}

REPORTS = {
    "D4": "a mishnah with more than four distinct Lean names",
    "D5": "an idea caption over 40 words, or of more than two sentences",
    "D6": "'first', 'only', 'better', 'best', 'unlike': a comparison or a claim to priority?",
    "D7": "'Lean cannot' (say what our representation does)",
    "D8": "'gives no citation' and its kin (say 'Heath gives no reference')",
    "D9": "'need' joined to Postulate 5 (say 'uses')",
    "D10": "S6 or S7 outside their failing scope",
    "D11": "Euclid's figure strokes or dots off the usual widths",
    "D14": "figures at a glance not yet lettered (S21 holds them once the switch is on)",
    "D15": "figures whose letters are still italic (S15 and S20 hold them upright once the switch is on)",
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
# The mishnah: TeX, refrains, Lean names.

# S10's one exception (STYLE, section 4, "Mathematics"): in a paragraph that opens
# MODERN_WAY, and ends at MODERN_WAY_ENDS, mathematics may stand between single dollars,
# and the check refuses the shapes of span known to break on GitHub. Its renderer, read with
# sample spans on 18 October, opens a span only at a line's start, after white space or
# after "(", and closes it only before white space, a line's end or a mark of
# MATH_CLOSES_BEFORE; it renders no span that crosses a line or begins or ends with a
# space; its Markdown takes away a backslash before a punctuation mark (\{ becomes {, \,
# becomes ,); and it escapes <, > and & inside a span twice. The lost backslashes show
# that its Markdown reads inside a span, so the refusals of *, _, ~ and a backtick follow
# CommonMark's rules, checked with a CommonMark parser and not tried on GitHub: a *, or a
# _ after anything but a letter or a digit, can open emphasis and pair with another across
# two spans; GFM reads ~ as strikethrough; and a backtick opens code. A shape not found
# here may still break, and the reviewer's checklist, item 5 (STYLE, section 8: each span
# seen rendered on GitHub), stays the guard.
MODERN_WAY = "**The modern way.**"
# Where the modern way's paragraph ends, as CommonMark ends a paragraph, with GFM's
# tables: at a blank line, or before a line, indented at most three spaces, that opens a
# block allowed to interrupt a paragraph. Those are an ATX heading; a bullet list item, or
# an ordered one numbered 1, with some text; a block quotation; a code fence; an HTML
# block, read here as any line opening a tag, "<!" or "<?", a little wider than
# CommonMark's (it lets "<span>" go on); a thematic break or a setext underline; and a
# table, whose next line is a delimiter row. Any other line, "|z| is one", "2. So" or
# "#check", goes on with it.
MODERN_WAY_ENDS = re.compile(
    r"\n[ \t]*\n|\n(?= {0,3}(?:#{1,6}(?:[ \t]|$)"
    r"|[-+*][ \t]+\S|0{0,8}1[.)][ \t]+\S|>|```|~~~|<[A-Za-z/!?]"
    r"|([-*_])(?:[ \t]*\1){2,}[ \t]*$|(?:=+|-+)[ \t]*$"
    r"|[^\n]*\n {0,3}(?=[^\n]*\|)\|?(?:[ \t]*:?-+:?[ \t]*\|)*[ \t]*:?-+:?[ \t]*\|?[ \t]*$))",
    re.M)
MATH_OPENS_AFTER = " \t\n("
MATH_CLOSES_BEFORE = " \t\n.,;:!?)]'\"’”–-/"
MATH_ESCAPE = re.compile(r"\\[!-/:-@\[-`{-~]")      # a backslash before ASCII punctuation
MATH_HTML = re.compile(r"[<>&]")


def math_fault(text: str, a: int, b: int) -> str | None:
    """The shape known to break on GitHub that the span from the `$` at `a` to the `$` at
    `b` of `text` has, or None."""
    body = text[a + 1:b]
    if not body:
        return "$$: display mathematics is not allowed; write $…$ within the sentence"
    if "\n" in body:
        return "a $…$ across a line break, which GitHub does not render; keep it on one line"
    if body[0].isspace() or body[-1].isspace():
        return "a space just inside a $: GitHub renders $x$, not $ x $"
    before = text[a - 1] if a else "\n"
    if before not in MATH_OPENS_AFTER:
        return (f"the opening $ follows {before!r}: GitHub opens $…$ only at a line's start, "
                "after a space or after (")
    after = text[b + 1] if b + 1 < len(text) else "\n"
    if after not in MATH_CLOSES_BEFORE:
        return (f"the closing $ comes before {after!r}: GitHub closes $…$ only before a space, "
                "a line's end or one of . , ; : ! ? ) ] ' \" - – /")
    m = MATH_ESCAPE.search(body)
    if m:
        return (f"{m.group(0)} inside $…$: GitHub's Markdown takes away a backslash before a "
                "punctuation mark; write \\lbrace, \\rbrace, \\thinspace, \\Vert")
    if "*" in body:
        return "* inside $…$, which GitHub's Markdown can read as emphasis; write \\ast"
    for i, c in enumerate(body):
        if c == "_" and not (i and body[i - 1].isalnum()):
            where = f"after {body[i - 1]!r} inside" if i else "first in"
            return (f"a _ {where} $…$, which GitHub's Markdown can read as emphasis; "
                    "put a subscript straight after a letter or digit, x_{1}^{2} rather "
                    "than x^{2}_{1}, \\mathrm{A_1} rather than \\mathrm{A}_1")
    if "~" in body:
        return ("~ inside $…$, which GitHub's Markdown can read as strikethrough; write a "
                "space or \\sim")
    if "`" in body:
        return "a backtick inside $…$, which GitHub's Markdown reads as code"
    depth = 0
    for c in body:
        depth += {"{": 1, "}": -1}.get(c, 0)
        if depth < 0:
            break
    if depth:
        return "the braces { } inside $…$ do not balance"
    m = MATH_HTML.search(body)
    if m:
        return (f"{m.group(0)} inside $…$, which GitHub escapes twice; write \\lt, \\gt, "
                "\\le, \\ge")
    return None


def tex_findings(text: str) -> list[tuple[int, int, str]]:
    """S10 on a mishnah, fenced blocks and HTML comments already blanked: (start, end,
    message) for each finding. TeX (a backslash, `^{` or `$`) is refused everywhere, save
    in a `$…$` span of a paragraph that opens MODERN_WAY, a paragraph ended as
    MODERN_WAY_ENDS says; there every `$` pairs with the next, and no span may have a shape
    known to break on GitHub (math_fault)."""
    found, outside = [], text
    start = 0
    for brk in list(MODERN_WAY_ENDS.finditer(text)) + [None]:
        end = brk.start() if brk else len(text)
        block, at = text[start:end], start
        start = brk.end() if brk else len(text)
        if not block.lstrip().startswith(MODERN_WAY):
            continue
        dollars = [at + m.start() for m in re.finditer(r"\$", block)]
        for k in range(0, len(dollars), 2):
            a = dollars[k]
            if k + 1 == len(dollars):
                found.append((a, a + 1, "an unpaired $: each $ that opens mathematics in the "
                              "modern way closes it in the same paragraph"))
                b = a
            else:
                b = dollars[k + 1]
                fault = math_fault(text, a, b)
                if fault:
                    found.append((a, b + 1, fault))
            outside = outside[:a] + re.sub(r"[^\n]", " ", outside[a:b + 1]) + outside[b + 1:]
    for m in TEX.finditer(outside):
        found.append((m.start(), m.end(), f'"{m.group(0)}", TeX outside a $…$ of the modern way'))
    return sorted(found)


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
    for a, b, msg in tex_findings(text):
        fail("S10", path, line_of(text, a), f"{msg}: {excerpt(raw, a, b)}")
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
INHERITED = ("fill", "fill-rule", "stroke", "stroke-width", "stroke-linecap", "font-size",
             "font-style", "text-anchor")
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

# One letter, one point (S22; STYLE, sections 7 and 8). A letter names one thing: a figure
# draws it once, or once in each of Heath's figures where they stand side by side, and it
# stands clear of every stroke, every dot and the canvas's edge, so that no line runs
# through it and it is not read as another point's. A letter is measured as Georgia, the
# figures' font, draws its capital, upright or italic as the figure sets it: by the convex
# hull of the points of the capital's outline, on its curves and off them, which holds the
# ink. GLYPHS_UPRIGHT and GLYPHS_ITALIC give each capital's advance and that hull's
# corners, x and y in turn with y up, in the font's units, EM to the em: a coarse shape,
# read from the fonts with fontTools once, so that the script needs neither. The hull
# misses no stroke that comes near the ink; it also spans a letter's hollows (an L's
# corner, a K's notch), so a stroke that ends in one is found while the ink is clear. A
# prime or a subscript after the capital is not measured, but its advance (SUFFIXES, the
# same upright and italic) places the capital when the label is anchored at its middle or
# its end.
CLEAR = 2.0     # the least room between a letter's hull and a stroke, a dot or the edge
EM = 2048
SUFFIXES = {"′": 658, "'": 441, **{chr(0x2080 + i): 1024 for i in range(10)}}
# The figures where two or three of Heath's figures stand side by side, one to a case
# (STYLE, section 7): the x of each straight cut between two of them, in the canvas's
# units. A letter belongs to the case its hull's middle stands in, is drawn once in each,
# and stands wholly on one side of every cut.
SIDE_BY_SIDE = {
    ("III", 25): (150.0, 275.0),
    ("III", 33): (147.0, 290.0),
    ("III", 35): (222.0,),
    ("III", 36): (190.0,),
}
GLYPHS_UPRIGHT = {
    "A": (1374, (-41, 0, 1421, 0, 1421, 71, 739, 1439, 659, 1439, -41, 71)),
    "B": (1339, (95, 0, 857, 0, 1026, 48, 1162, 141, 1248, 287, 1248, 483, 1170, 1196,
            1094, 1316, 972, 1389, 833, 1419, 102, 1419, 95, 71)),
    "C": (1315, (78, 526, 184, 255, 273, 161, 363, 67, 596, -33, 919, -33, 1203, 148, 1289,
            359, 1227, 1419, 859, 1450, 613, 1450, 365, 1342, 182, 1143, 78, 866)),
    "D": (1534, (94, 0, 828, 0, 1102, 84, 1212, 169, 1321, 254, 1457, 520, 1457, 896, 1315,
            1184, 1098, 1340, 850, 1419, 102, 1419, 94, 71)),
    "E": (1338, (86, 0, 1264, 0, 1291, 418, 1184, 1419, 86, 1419)),
    "F": (1227, (86, 0, 701, 0, 983, 444, 1199, 1064, 1199, 1419, 86, 1419)),
    "G": (1485, (78, 530, 190, 258, 379, 69, 631, -33, 894, -33, 1158, 31, 1291, 91, 1471,
            567, 1471, 640, 1278, 1419, 911, 1450, 641, 1450, 378, 1339, 185, 1137, 78,
            860)),
    "H": (1669, (98, 0, 1567, 0, 1567, 1419, 98, 1419)),
    "I": (798, (79, 0, 718, 0, 718, 1419, 79, 1419)),
    "J": (1060, (11, 149, 214, -34, 482, -34, 645, 42, 755, 168, 808, 316, 1006, 1348,
            1006, 1419, 380, 1419, 11, 372)),
    "K": (1422, (102, 0, 1475, 0, 1475, 71, 1393, 1419, 102, 1419)),
    "L": (1236, (98, 0, 1207, 0, 1237, 422, 697, 1419, 98, 1419)),
    "M": (1899, (48, 0, 1806, 0, 1806, 71, 1804, 1419, 57, 1419, 48, 71)),
    "N": (1571, (24, 1348, 48, 0, 1237, -14, 1324, -14, 1554, 1348, 1554, 1419, 24, 1419)),
    "O": (1524, (80, 550, 183, 273, 363, 77, 614, -34, 901, -34, 1147, 70, 1336, 263, 1444,
            539, 1444, 876, 1338, 1153, 1153, 1347, 903, 1453, 626, 1453, 377, 1349, 188,
            1152, 80, 881)),
    "P": (1249, (91, 1348, 98, 0, 707, 0, 1184, 958, 1184, 1228, 937, 1419, 91, 1419)),
    "Q": (1524, (80, 550, 178, 283, 353, 86, 923, -346, 1051, -385, 1238, -385, 1373, -356,
            1418, -343, 1444, 574, 1444, 876, 1338, 1153, 1153, 1347, 903, 1453, 626, 1453,
            377, 1349, 188, 1152, 80, 881)),
    "R": (1437, (98, 0, 1480, 0, 1480, 71, 1201, 1172, 1127, 1301, 1065, 1341, 1001, 1382,
            843, 1419, 98, 1419)),
    "S": (1149, (94, 485, 108, -1, 490, -29, 791, -29, 1069, 215, 1069, 482, 1001, 1419,
            661, 1451, 477, 1451, 319, 1392, 261, 1340, 200, 1285, 134, 1145)),
    "T": (1267, (15, 1034, 298, 0, 968, 0, 1251, 1034, 1251, 1419, 15, 1419)),
    "U": (1549, (74, 1348, 260, 294, 328, 147, 395, 90, 463, 33, 663, -34, 871, -34, 1046,
            13, 1125, 67, 1205, 123, 1303, 297, 1533, 1348, 1533, 1419, 74, 1419)),
    "V": (1365, (-38, 1348, 628, -18, 711, -18, 1407, 1348, 1407, 1419, -38, 1419)),
    "W": (1998, (-4, 1348, 536, -18, 1447, -18, 2028, 1348, 2028, 1419, -4, 1419)),
    "X": (1455, (13, 0, 1457, 0, 1457, 71, 1410, 1419, 27, 1419, 13, 71)),
    "Y": (1260, (-44, 1348, 292, 0, 956, 0, 1314, 1348, 1314, 1419, -44, 1419)),
    "Z": (1232, (27, 0, 1167, 0, 1214, 443, 1190, 1419, 127, 1419, 84, 1018, 27, 35)),
}
GLYPHS_ITALIC = {
    "A": (1374, (-160, 0, 1302, 0, 1317, 66, 952, 1439, 872, 1439, -145, 66)),
    "B": (1339, (-29, 0, 768, 0, 965, 55, 1051, 113, 1131, 167, 1236, 340, 1298, 1077,
            1298, 1234, 1236, 1333, 1126, 1394, 1003, 1419, 306, 1419, 290, 1353)),
    "C": (1315, (100, 400, 183, 190, 328, 43, 522, -33, 830, -33, 1140, 143, 1266, 358,
            1427, 1419, 1041, 1452, 751, 1452, 448, 1302, 340, 1178, 228, 1049, 100, 721)),
    "D": (1534, (-29, 0, 769, 0, 1096, 116, 1229, 229, 1357, 338, 1515, 669, 1515, 1024,
            1398, 1241, 1209, 1368, 997, 1419, 306, 1419, -14, 66)),
    "E": (1338, (-37, 0, 1141, 0, 1264, 418, 1388, 1419, 290, 1419, -22, 66)),
    "F": (1227, (-35, 0, 583, 0, 963, 444, 1322, 1064, 1404, 1419, 291, 1419, 275, 1353)),
    "G": (1485, (100, 403, 187, 191, 341, 43, 547, -33, 745, -33, 874, -13, 1021, 24, 1124,
            64, 1190, 91, 1481, 572, 1496, 640, 1482, 1419, 1093, 1452, 781, 1452, 467,
            1311, 235, 1064, 100, 733)),
    "H": (1669, (-25, 0, 1444, 0, 1756, 1353, 1771, 1419, 302, 1419, -10, 66)),
    "I": (798, (-44, 0, 595, 0, 907, 1353, 922, 1419, 283, 1419, -29, 66)),
    "J": (1060, (-50, 106, 118, -34, 373, -34, 545, 44, 679, 166, 762, 315, 1194, 1353,
            1209, 1419, 579, 1419, -50, 329)),
    "K": (1422, (-21, 0, 1336, 0, 1353, 66, 1597, 1419, 306, 1419, -6, 66)),
    "L": (1236, (-25, 0, 1084, 0, 1211, 422, 901, 1419, 302, 1419, -10, 66)),
    "M": (1899, (-76, 0, 1682, 0, 1698, 66, 1993, 1353, 2008, 1419, 260, 1419)),
    "N": (1571, (-75, 0, 1109, -14, 1199, -14, 1743, 1353, 1759, 1419, 229, 1419, 213,
            1353)),
    "O": (1496, (100, 288, 404, -34, 811, -34, 1108, 107, 1224, 229, 1337, 348, 1477, 683,
            1477, 1138, 1169, 1453, 766, 1453, 465, 1311, 240, 1067, 100, 734)),
    "P": (1249, (-25, 0, 584, 0, 1205, 822, 1312, 1012, 1312, 1266, 1097, 1419, 295, 1419,
            280, 1353)),
    "Q": (1496, (100, 290, 393, -24, 780, -386, 1000, -386, 1171, -357, 1232, -338, 1477,
            683, 1477, 1138, 1169, 1453, 766, 1453, 465, 1311, 240, 1067, 100, 734)),
    "R": (1437, (-26, 0, 1354, 0, 1370, 66, 1330, 1219, 1269, 1323, 1168, 1385, 1026, 1419,
            302, 1419)),
    "S": (1149, (-9, -1, 370, -29, 614, -29, 815, 41, 973, 169, 1065, 353, 1199, 1419, 825,
            1451, 641, 1451, 448, 1383, 380, 1326, 310, 1267, 225, 1105, 89, 485)),
    "T": (1267, (130, 1034, 174, 0, 844, 0, 1366, 1034, 1455, 1419, 219, 1419)),
    "U": (1549, (212, 144, 449, -34, 749, -34, 931, 8, 1016, 57, 1104, 108, 1245, 289,
            1721, 1353, 1737, 1419, 278, 1419, 262, 1353, 212, 313)),
    "V": (1365, (151, 1353, 501, -18, 584, -18, 1599, 1353, 1614, 1419, 166, 1419)),
    "W": (1998, (182, 1353, 408, -18, 1322, -18, 2217, 1353, 2232, 1419, 197, 1419)),
    "X": (1455, (-110, 0, 1321, 0, 1336, 66, 1614, 1419, 243, 1419, -95, 66)),
    "Y": (1260, (143, 1353, 169, 0, 833, 0, 1501, 1353, 1517, 1419, 159, 1419)),
    "Z": (1232, (-90, 0, 1048, 0, 1198, 443, 1387, 1419, 326, 1419, 190, 1018, -81, 35)),
}

# data-unlettered marks in the idea figures, printed on every run:
# {(file, reason): [elements, points]}
idea_exemptions: dict[tuple[str, str], list[int]] = defaultdict(lambda: [0, 0])

# The figures whose letters are still italic, while UPRIGHT_LETTERS_REQUIRED is False (D15):
# {book: {"of Euclid's figures": [NN, …], "figures at a glance": [NN, …]}}
italic_figures: dict[str, dict[str, list[str]]] = defaultdict(lambda: defaultdict(list))


def letter_style(eff) -> str:
    """A letter's font-style: "normal" (upright, SVG's default) or what it is set to."""
    return (eff.get("font-style") or "normal").strip().lower()


def check_letter_style(path: Path, rule: str, found: list[tuple[str, str]]) -> None:
    """S15's and S20's style of a figure's letters, each (letter, its font-style): upright,
    or, while UPRIGHT_LETTERS_REQUIRED is False, italic, one style in each figure (STYLE,
    sections 4 and 7). A figure still italic is listed for D15."""
    styles: dict[str, list[str]] = defaultdict(list)
    for s, style in found:
        styles[style].append(s)
    for style, letters in sorted(styles.items()):
        if style not in ("normal", "italic"):
            fail(rule, path, 0, f"letter(s) {', '.join(letters)} in font-style {style}: "
                 "Heath's letters are upright (STYLE, section 4)")
    if "italic" not in styles:
        return
    if UPRIGHT_LETTERS_REQUIRED:
        fail(rule, path, 0, f"letter(s) {', '.join(styles['italic'])} italic: Heath's letters "
             "are upright (STYLE, section 4)")
    elif "normal" in styles:
        fail(rule, path, 0, f"letter(s) {', '.join(styles['italic'])} italic beside "
             f"{', '.join(styles['normal'])} upright: one style in each figure, upright as "
             "the figure is converted (STYLE, section 8)")
    else:
        kind = "figures at a glance" if path.stem.endswith("-idea") else "of Euclid's figures"
        italic_figures[path.parent.name][kind].append(path.name[:2])


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


def path_rings(d: str, closed: list[bool] | None = None) -> list[list[tuple[float, float]]]:
    """A path's subpaths as the rings of points its fill closes: straight segments as they
    are, arcs and curves in short straight pieces. A path is read as far as it is well
    formed, as SVG draws it. Given a list `closed`, it gains a flag for each ring: whether
    a Z closes it, as its stroke is drawn (S22)."""
    rings: list[list[tuple[float, float]]] = []
    ring: list[tuple[float, float]] = []

    def keep(shut: bool) -> None:
        if len(ring) > 1:
            rings.append(ring)
            if closed is not None:
                closed.append(shut)

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
            keep(True)
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
            keep(False)
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
    keep(False)
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
    """S13, S14, S20, S21 and S22 for one idea figure. Returns how many of its points wait
    for a letter while it is in the transition (no letter yet, the switch off), else 0."""
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
    one_letter_one_point(path, root)
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
    """S20: each letter is one of Heath's, as Euclid's figure draws it, upright (or, while
    UPRIGHT_LETTERS_REQUIRED is False, italic, one style in the figure), at 14, in the
    figure's black, or in the parchment's colour where it stands on red, blue or black.
    S21: each point the figure shows has a letter within 30 of it, or is marked
    data-unlettered with its reason. Returns the points waiting for a letter while the
    figure is in the transition, else 0."""
    euclid = path.with_name(path.name.replace("-idea", ""))
    heaths = drawn_letters(euclid)
    letters, styles = [], []
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
        styles.append((s, letter_style(eff)))
        letters.append(centre)
    check_letter_style(path, "S20", styles)

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


def glyph_hull(own, eff, m, s: str) -> list[tuple[float, float]]:
    """The corners of the hull of letter s's capital (S22), upright or italic as its
    font-style sets it, where the text element puts it: x and y give the start of its
    baseline (its middle or its end, by text-anchor, the whole label's advance counted,
    a prime or a subscript after the capital included), at its font-size, transforms
    applied."""
    glyphs = GLYPHS_ITALIC if letter_style(eff) == "italic" else GLYPHS_UPRIGHT
    advance, corners = glyphs[s[0]]
    whole = advance + sum(SUFFIXES.get(c, 0) for c in s[1:])
    k = (number(eff.get("font-size")) or 16.0) / EM
    x = coord(own.get("x")) + {"middle": -whole * k / 2, "end": -whole * k}.get(
        (eff.get("text-anchor") or "start").strip(), 0.0)
    y = coord(own.get("y"))
    return [at(m, x + corners[i] * k, y - corners[i + 1] * k)
            for i in range(0, len(corners), 2)]


def stretch(m) -> float:
    """The most an affine map m lengthens any length: its larger singular value. A
    stroke's width and a dot's radius are taken at this, so that a map that stretches one
    way more than another never makes them seem thinner than they are (S22)."""
    a, b, c, d = m[:4]
    t, det = a * a + b * b + c * c + d * d, a * d - b * c
    return math.sqrt((t + math.sqrt(max(0.0, t * t - 4 * det * det))) / 2)


def length(value: str | None) -> float | None:
    """An attribute that is one number, in any spelling SVG allows ("50", "5e1", "50px"),
    or None."""
    m = re.fullmatch(r"\s*(" + NUM.pattern + r")\s*(?:px)?\s*", value or "")
    return float(m.group(1)) if m else None


def rect_outline(own) -> list[tuple[float, float]] | None:
    """A rect's outline, its corners rounded by rx and ry as SVG rounds them (one given
    stands for both, and each is at most half the side), in short straight pieces; None
    when it has no width or no height, and SVG draws nothing."""
    x0, y0 = coord(own.get("x")), coord(own.get("y"))
    w, h = coord(own.get("width")), coord(own.get("height"))
    if w <= 0 or h <= 0:
        return None
    rx, ry = length(own.get("rx")), length(own.get("ry"))
    rx = ry if rx is None else rx
    ry = rx if ry is None else ry
    rx, ry = min(rx or 0.0, w / 2), min(ry or 0.0, h / 2)
    if rx <= 0 or ry <= 0:
        return [(x0, y0), (x0 + w, y0), (x0 + w, y0 + h), (x0, y0 + h), (x0, y0)]
    out = []
    quarter = max(1, round(math.pi / 2 / ARC_STEP))
    for cx, cy, start in ((x0 + w - rx, y0 + ry, -90), (x0 + w - rx, y0 + h - ry, 0),
                          (x0 + rx, y0 + h - ry, 90), (x0 + rx, y0 + ry, 180)):
        for i in range(quarter + 1):
            a = math.radians(start + 90 * i / quarter)
            out.append((cx + rx * math.cos(a), cy + ry * math.sin(a)))
    return out + out[:1]


def strokes(root):
    """(what it is, its points, half its width) for each stroke a figure draws, as a run
    of straight pieces: a line, a polyline, a polygon or a rect's outline (its corners
    rounded as rx and ry round them), each subpath of a path (closed where a Z closes it),
    a circle or an ellipse in short straight pieces; transforms applied, the width taken
    at the most the transform stretches it, a dashed stroke read whole, and a stroke SVG
    does not draw (a circle of no radius, a rect of no width, a run of no length with
    butt caps) left out (S22)."""
    for el, own, eff, m, _ in placed(root):
        t = tag(el)
        w = number(eff.get("stroke-width"))
        w = 1.0 if w is None else w
        if t not in DRAWN or (eff.get("stroke") or "none").strip().lower() == "none" or w <= 0:
            continue
        if t == "line":
            runs = [[(coord(own.get("x1")), coord(own.get("y1"))),
                     (coord(own.get("x2")), coord(own.get("y2")))]]
        elif t in ("polyline", "polygon"):
            v = [float(n) for n in NUM.findall(own.get("points", ""))]
            run = list(zip(v[0::2], v[1::2]))
            runs = [run + run[:1] if t == "polygon" else run]
        elif t == "path":
            closed: list[bool] = []
            rings = path_rings(own.get("d", ""), closed)
            runs = [ring + ring[:1] if shut else ring for ring, shut in zip(rings, closed)]
        elif t == "rect":
            outline = rect_outline(own)
            runs = [outline] if outline else []
        else:
            cx, cy = coord(own.get("cx")), coord(own.get("cy"))
            rx = coord(own.get("r")) if t == "circle" else coord(own.get("rx"))
            ry = coord(own.get("r")) if t == "circle" else coord(own.get("ry"))
            steps = round(math.tau / ARC_STEP)
            runs = [] if rx <= 0 or ry <= 0 else [
                [(cx + rx * math.cos(i * ARC_STEP), cy + ry * math.sin(i * ARC_STEP))
                 for i in range(steps + 1)]]
        half = w / 2 * stretch(m)
        kind = "a dashed line" if eff.get("stroke-dasharray") and t == "line" else \
            ("an " if t == "ellipse" else "a ") + t
        butt = (eff.get("stroke-linecap") or "butt").strip() == "butt"
        for run in runs:
            if len(run) > 1 and not (butt and all(p == run[0] for p in run)):
                yield kind, [at(m, x, y) for x, y in run], half


def dots(root):
    """(where, radius) for each dot a figure draws: a filled circle of radius DOT at most,
    transforms applied, its radius taken at the most the transform stretches it (S22, as
    S21 reads a dot)."""
    for el, own, eff, m, _ in placed(root):
        r = coord(own.get("r"))
        filled = (eff.get("fill") or "black").strip().lower() != "none"
        if tag(el) == "circle" and 0 < r <= DOT and filled:
            yield at(m, coord(own.get("cx")), coord(own.get("cy"))), r * stretch(m)


def point_gap(p, a, b) -> float:
    """How far the point p stands from the straight piece ab."""
    dx, dy = b[0] - a[0], b[1] - a[1]
    n = dx * dx + dy * dy
    t = 0.0 if n == 0 else max(0.0, min(1.0, ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / n))
    return math.hypot(p[0] - a[0] - t * dx, p[1] - a[1] - t * dy)


def crosses(a, b, c, d) -> bool:
    """Whether the straight pieces ab and cd cross."""
    def side(p, q, r):
        return (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0])
    return side(a, b, c) * side(a, b, d) < 0 and side(c, d, a) * side(c, d, b) < 0


def hull_gap(hull, a, b) -> float:
    """How far the straight piece ab stands from the convex polygon `hull`: 0 if it meets
    it."""
    if enclosed([hull], *a, False) or enclosed([hull], *b, False):
        return 0.0
    gap = math.inf
    for c, d in zip(hull, hull[1:] + hull[:1]):
        if crosses(a, b, c, d):
            return 0.0
        gap = min(gap, point_gap(c, a, b), point_gap(a, c, d), point_gap(b, c, d))
    return gap


def nearest(hull, pieces, spots) -> tuple[float, str] | None:
    """How near a stroke (less half its width) or a dot (less its radius) comes to a
    letter's hull, and what it is; None if none comes within CLEAR."""
    xs, ys = [p[0] for p in hull], [p[1] for p in hull]
    best = None
    for kind, run, half in pieces:
        reach = CLEAR + half
        lo_x, hi_x = min(xs) - reach, max(xs) + reach
        lo_y, hi_y = min(ys) - reach, max(ys) + reach
        for a, b in zip(run, run[1:]):
            if max(a[0], b[0]) < lo_x or min(a[0], b[0]) > hi_x \
                    or max(a[1], b[1]) < lo_y or min(a[1], b[1]) > hi_y:
                continue
            gap = hull_gap(hull, a, b) - half
            if gap < CLEAR and (best is None or gap < best[0]):
                best = (gap, kind)
    for p, r in spots:
        gap = (0.0 if enclosed([hull], *p, False) else
               min(point_gap(p, c, d) for c, d in zip(hull, hull[1:] + hull[:1]))) - r
        if gap < CLEAR and (best is None or gap < best[0]):
            best = (gap, "a dot")
    return best


def one_letter_one_point(path: Path, root, cuts: tuple[float, ...] = ()) -> None:
    """S22: a figure draws each letter once, or, where Heath's figures stand side by side
    with `cuts` between them, once in each, every letter wholly on one side of every cut;
    and each letter stands CLEAR of every stroke, every dot and the canvas's edge,
    measured by the hull of its capital as Georgia draws it, upright or italic."""
    vb = [float(v) for v in NUM.findall(root.get("viewBox", ""))]
    pieces, spots = list(strokes(root)), list(dots(root))
    count: dict[tuple[int, str], int] = defaultdict(int)
    for el, own, eff, m, _ in placed(root):
        s = text_of(el)
        if tag(el) != "text" or not LETTER.fullmatch(s):
            continue
        hull = glyph_hull(own, eff, m, s)
        xs, ys = [p[0] for p in hull], [p[1] for p in hull]
        where = f"letter {s} at ({coord(own.get('x')):g}, {coord(own.get('y')):g})"
        count[(sum(1 for c in cuts if (min(xs) + max(xs)) / 2 > c), s)] += 1
        for c in cuts:
            if min(xs) < c < max(xs):
                fail("S22", path, 0, f"{where} stands across the cut at x {c:g} between two "
                     "of the figures side by side (SIDE_BY_SIDE)")
        near = nearest(hull, pieces, spots)
        if near:
            gap, kind = near
            fail("S22", path, 0, f"{where} meets {kind}" if gap <= 0 else
                 f"{where} stands {gap:.1f} from {kind}, under {CLEAR:g}: move it clear")
        if len(vb) == 4:
            edge = min(min(xs) - vb[0], vb[0] + vb[2] - max(xs),
                       min(ys) - vb[1], vb[1] + vb[3] - max(ys))
            if edge < CLEAR:
                fail("S22", path, 0, f"{where} stands {max(edge, 0):.1f} from the canvas's "
                     f"edge, under {CLEAR:g}")
    for (case, s), k in sorted(count.items()):
        if k > 1:
            fail("S22", path, 0, f"letter {s} drawn {k} times"
                 + (f" in the figure {case + 1} of {len(cuts) + 1} side by side" if cuts else "")
                 + ": one letter names one point")


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

    drawn, styles = set(), []
    thin, heavy = defaultdict(int), defaultdict(int)
    usual = defaultdict(int)
    for el, own, eff in walk(root):
        t = tag(el)
        if t == "text":
            s = text_of(el)
            if LETTER.fullmatch(s):
                drawn.add(s[0])
                styles.append((s, letter_style(eff)))
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
    check_letter_style(path, "S15", styles)

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
    one_letter_one_point(path, root, SIDE_BY_SIDE.get((book, n), ()))


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
        for kind, names in sorted(italic_figures[book].items()):
            report("D15", d, 0, f"{len(names)} {kind} with italic letters: " + ", ".join(names))


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
    if "D15" in reports:
        print("note: S15 and S20 take italic letters, one style in each figure, until "
              "UPRIGHT_LETTERS_REQUIRED is set (STYLE, section 8); D15 lists the figures")
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
    rules = "S1–S22" if not args.no_lean else "S1–S11 and S13–S22"
    print(f"\n✓ style: the hard rules hold ({rules})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
