"""Read Heath's text (heath/<book>/NN.md) into enunciation + proof paragraphs.

Shared by scaffold_book.py, check_fidelity.py and render.py. Standard library only.
"""

import re
from pathlib import Path

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


ROMAN = ["I", "II", "III", "IV", "V", "VI", "VII", "VIII", "IX", "X", "XI", "XII", "XIII"]

# The books carried into Lean so far, and how many propositions each has.
# `Certificate/Facts.lean` keeps the same list.
BOOKS = {"I": 48, "II": 14, "III": 37}


def arabic(book: str) -> int:
    """The number of a book from its Roman numeral: "I" is 1, "II" is 2, "XIII" is 13."""
    return ROMAN.index(book) + 1


def prop_key(ref: str):
    """Sort references by book, then by number: I.3 before I.10, I.48 before II.1,
    and IX before X."""
    book, num = ref.split(".")
    return (arabic(book), int(num))


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
