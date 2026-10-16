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
BOOKS = {"I": 48, "II": 14}


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
    """Propositions Euclid cites, e.g. {"I.4", "II.6"} from "[I. 4]", "[C.N. 1; II. 6]"."""
    found = set()
    for p in paragraphs:
        for inner in CITATION.findall(p):
            for part in inner.split(";"):
                part = part.strip()
                m = re.fullmatch(r"([IVX]+)\.\s*(\d+)", part)
                if m:
                    found.add(f"{m.group(1)}.{int(m.group(2))}")
    return found


def justifications(paragraphs):
    """Every bracketed justification Euclid gives: Post. 3, Def. 15, C.N. 1, I. 4 …

    A bracket may hold several, as "[C.N. 1; I. 30]" or "[Post. 4 and C.N. 1]".
    """
    found = []
    for p in paragraphs:
        for inner in CITATION.findall(p):
            for part in re.split(r";|\band\b", inner):
                part = " ".join(part.split())
                if re.fullmatch(r"(Post\.|Def\.|C\.N\.|[IVX]+\.)\s*\d+", part):
                    part = re.sub(r"\.\s*(\d+)", r". \1", part)
                    if part not in found:
                        found.append(part)
    return found
