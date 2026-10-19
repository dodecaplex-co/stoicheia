#!/usr/bin/env python3
"""The cases of scripts/check_style.py: how its rules read a phrase, TeX, and a letter.

    python3 -I tests/test_check_style.py        # well under a second; no Lean, no network

Each case is a short text, or a small figure, with the finding its rule should make of
it, put to the script's own patterns and functions:

* the phrase cases: each wording rule finds its phrase however a line or a comment wraps
  it, and not across a blank line (save S2's and S7's), inside a quotation or in one of
  Heath's `--` lines; and S3 still finds an "I" after "Book" when anything but one space
  stands between them;
* the TeX cases: S10 allows `$…$` only in a paragraph that opens
  "**The modern way.**", with balanced delimiters and no shape known to break on
  GitHub; TeX outside such a span still fails, in the modern way as elsewhere;
* the ink cases: S20 judges a letter on an angle's wedge, a filled path, by the wedge's
  fill, within its three ends and beyond its chord out to its arc, and not beyond the
  arc; however the wedge is spelled (an absolute arc, a relative arc, a cubic curve), and
  wherever a transform moves it;
* the scope cases (#66): which texts of a review record the rules read, and on which
  lines; the docstring render.py shows, found again in its file; S12's reading of a
  `name : type`; S22's reading of letters in backticks, one code span at a time; and the
  reach of 19 October, whose findings in a file of REACH_PENDING are reported only for the
  rules the file is listed for, while every other finding in that file still fails.

CI's `check` job runs this file just before check_style.py, and scripts/safe_push.py runs
it in the same place (docs/WORKFLOW.md, section 8), so a case read wrongly stops the
checks before the style check's findings are read. When a rule is found reading a phrase,
TeX or a letter wrongly, its fix comes with a case here that the old rule fails (WORKFLOW,
section 8, "A guard defect gets a regression"). Python 3.11 or later; standard library.
"""

from __future__ import annotations

import sys
import unittest
import xml.etree.ElementTree as ET
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import check_style as style  # noqa: E402

# ---------------------------------------------------------------------------------------
# The phrase cases. (D7 once let "Lean\ncannot" through, in a docstring.)

PHRASE_CASES = [   # (rule, its search, the text as the rule reads it, a finding?)
    ("D7", style.LEAN_CANNOT.search, "as if picking it up. Lean\ncannot move a figure", True),
    ("D7", style.LEAN_CANNOT.search, "the note says Lean\n  -- cannot move it", True),
    ("D7", style.LEAN_CANNOT.search, "> what Lean\n> can't do", True),
    ("D7", style.LEAN_CANNOT.search, "Lean  can not", True),
    ("D7", style.LEAN_CANNOT.search, "what Lean\n\ncannot", False),
    ("D7", style.LEAN_CANNOT.search, "Leancannot", False),
    ("S2", style.CREW.search, "the first\n  -- mate", True),
    ("S2", style.CREW.search, "the first\n\nmate", True),
    ("S3", style.FIRST_PERSON.search, "as I\nthink", True),
    ("S3", style.FIRST_PERSON.search, "as I\n  -- would say", True),
    ("S3", style.FIRST_PERSON.search, "Book I was proved", False),
    ("S3", style.FIRST_PERSON.search, "Books I have read", False),
    ("S3", style.FIRST_PERSON.search, "Book I\nwas proved", False),
    ("S3", style.FIRST_PERSON.search, "in Book  I was", True),
    ("S3", style.FIRST_PERSON.search, "in Book\tI was", True),
    ("S3", style.FIRST_PERSON.search, "in Book\nI was", True),
    ("S3", style.FIRST_PERSON.search, "the Book\n  -- I would say", True),
    ("S3", style.FIRST_PERSON.search, "Books\n> I have", True),
    ("S3", style.FIRST_PERSON.search, "the eBook I have", True),
    ("S4", style.HEDGE.search, "strictly\nspeaking", True),
    ("S4", style.HEDGE.search, "it is worth\n   noting", True),
    ("S5", style.EUCLID_CITES.search, "Euclid\ncites I.3", True),
    ("S5", style.EUCLID_CITES.search, "I.1 to I.28 never\n  -- need it", True),
    ("S6", style.TACIT.search, "a tacit\nassumption", True),
    ("S7", style.DEFINITION.search, "by Definition\n15", True),
    ("S7", style.DEFINITION.search, "by Definition\n\n15", True),
    ("S9", style.ITALIC_LETTER.search, "the line *AB, CD*", True),
    ("S9", style.ITALIC_LETTER.search, "the line *AB,\nCD*", True),
    ("S9", style.ITALIC_LETTER.search, "> the line *AB\n> CD*", True),
    ("S9", style.ITALIC_LETTER.search, "the line *AB,\n\nCD*", False),
    ("D10", style.DEFINITION.search, "by Def.\n  -- 15", True),
    ("D8", style.NO_CITATION.search, "gives no\ncitation", True),
    ("D9", style.POSTULATE_5.search, "the parallel\npostulate", True),
    ("S11", style.REFRAINS[0][0].search, "the certificate\nrecords", True),
    ("S11", style.RETIRED_LEADS.search, "**What it\nrests on.**", True),
    ("S11", style.proclus_under_i31, "Proclus puts it under I.31.", True),
    ("S11", style.proclus_under_i31, "Proclus puts it under\nI.31.", True),
    ("S11", style.proclus_under_i31, "As Proclus says, it falls\n> under\n> I.31.", True),
    ("S11", style.proclus_under_i31, "Proclus puts it under\n\nI.31.", False),
    ("S11", style.proclus_under_i31, "Proclus says so. It falls under\nI.31.", False),
    # Read as the Lean notes are read (Heath's `--` lines out of scope), and as the prose
    # is read (quotations and code blanked first).
    ("D7", style.LEAN_CANNOT.search,
     style.notes_text("/-- We build it, for Lean\ncannot move a figure. -/\n"
                      "theorem T : True := trivial\n"), True),
    ("D7", style.LEAN_CANNOT.search,
     style.notes_text("theorem T : True := by\n  -- Lean\n  -- cannot\n  trivial\n"), False),
    ("D7", style.LEAN_CANNOT.search,
     style.blank_quotes(style.blank_code('He wrote "what Lean\ncannot" once.')), False),
    ("S3", style.FIRST_PERSON.search,
     style.blank_quotes(style.blank_code('as I "so" think')), True),
]

# ---------------------------------------------------------------------------------------
# The TeX cases: mishnahs on both sides of S10's modern-way boundary.

MW = style.MODERN_WAY + " "
TEX_CASES = [   # (a mishnah, as S10 reads it, a finding?)
    (MW + r"Then $e^{i\theta}$ turns B through $\theta$.", False),
    (MW + r"Put $\mathrm{A}$ at $0$; the angle is $\pi/2$, and $a_1 + b_1$ is real.", False),
    (MW + r"It is $\frac{e^{i\gamma}-e^{i\alpha}}{e^{i\beta}-e^{i\alpha}}$, and ($x$) too.", False),
    (MW + r"For $0 \lt b \lt a$, $a\thinspace b$ and $\lbrace x \rbrace$ hold.", False),
    ("**A lead.** Plain words.\n\n" + MW + r"It is $z \mapsto e^{i\theta} z$.", False),
    ("Plain words, with θ and π and (a + b)², and no lead.", False),
    (MW + r"Then $z^\ast$ and $w^\ast$ are conjugates.", False),
    (MW + r"Then $x_{1}^{2}$ and $a_{n}$ are terms.", False),
    (MW + r"Then $\theta_1$ and $\vec{u_1}$ are given.", False),
    (MW + "Then $x$ holds, and the modulus\n|z| is one, so $y$ is too.", False),
    (MW + "Then $x$ holds, and the sum is\n2. So $y$ is two.", False),
    (MW + "Then $x$ holds, as Lean's\n#check shows for $y$ too.", False),
    (r"**A lead.** Then $e^{i\theta}$ turns it.", True),
    (r"Then e^{iθ} turns it, in a paragraph with no lead.", True),
    (MW + r"Then e^{iθ} turns it.", True),
    (MW + r"Then \theta turns it.", True),
    (MW + r"Then $e^{i\theta}$ turns it, and \pi is half a turn.", True),
    (MW + r"Then $e^{i\theta}$ and $x turn it.", True),
    (MW + r"Then $e^{i\theta$ turns it.", True),
    (MW + r"Then $e^{i\theta}}{$ turns it.", True),
    (MW + r"Then $$x^2$$ is a square.", True),
    (MW + r"Then $ x $ is padded.", True),
    (MW + "Then $x +\ny$ crosses a line.", True),
    (MW + r"Then the$x$ is glued before.", True),
    (MW + r"Then $x$s is glued after.", True),
    (MW + r'Then "$x$" is quoted.', True),
    (MW + r"Then $\{x\}$ loses its backslashes.", True),
    (MW + r"Then $a\,b$ loses its backslash.", True),
    (MW + r"Then $a < b$ is escaped twice.", True),
    (MW + r"Then $z^*$ and $w^*$ are read as emphasis.", True),
    (MW + r"Then $a*b*c$ is read as emphasis.", True),
    (MW + r"Then $\vec{u}_{1}$ and $\vec{v}_{2}$ are read as emphasis.", True),
    (MW + r"Then $x^{2}_{1}$ has its subscript after a brace.", True),
    (MW + r"Then $x~y$ is read as strikethrough.", True),
    (MW + r"Then $a`b$ holds a backtick.", True),
    ("**A lead.** A paragraph.\n" + MW + r"Then $x$ is in the lead's paragraph.", True),
    (MW + "Plain words.\n\nThen $x$ is in the next paragraph.", True),
    (MW + "Then $x$ holds.\n- and $y$ in a list item.", True),
    (MW + "Then $x$ holds.\n# $y$ a heading", True),
    (MW + "Then $x$ holds.\n+ and $y$ in a list item.", True),
    (MW + "Then $x$ holds.\n1) and $y$ in a list item.", True),
    (MW + "Then $x$ holds.\n> and $y$ in a quotation.", True),
    (MW + "Then $x$ holds.\n| $y$ | z |\n| --- | --- |", True),
    (r"**The modern way** without its full stop: $x$.", True),
]

# ---------------------------------------------------------------------------------------
# The ink cases: a letter on an angle's wedge, read as S20 reads a figure's letters.
# (S20 once read no paths, and let a black letter on a blue wedge through.)

INK_WEDGES = (   # a quarter wedge of radius 34 at (200, 150), below and right of it
    "M200,150 L234,150 A34,34 0 0,1 200,184 Z",
    "m200,150 l34,0 a34,34 0 0,1 -34,34 z",
    "M200,150 H234 C234,168.78 218.78,184 200,184 Z",
)
BLUE_WEDGE = '<path d="{wedge}" fill="#1f5aa6"/>'
YELLOW_ON_RED = ('<polygon points="150,100 300,100 300,250 150,250" fill="#d0312d"/>'
                 '<path d="{wedge}" fill="#f2b705"/>')
MOVED_WEDGE = '<g transform="translate(-100,20)"><path d="{wedge}" fill="#1f5aa6"/></g>'
WITHIN, ON_ARC, BEYOND = (215.0, 160.0), (221.2, 171.2), (226.9, 176.9)
MOVED = (121.2, 191.2)   # ON_ARC, where MOVED_WEDGE stands
IDEA_INK, IDEA_INK_ON_DARK = style.IDEA_INK, style.IDEA_INK_ON_DARK   # #222222, #fbf7ee

INK_CASES = [   # (what is drawn under the letter, its glyph's middle, its ink, a finding?)
    (BLUE_WEDGE, WITHIN, IDEA_INK, True),
    (BLUE_WEDGE, WITHIN, IDEA_INK_ON_DARK, False),
    (BLUE_WEDGE, ON_ARC, IDEA_INK, True),
    (BLUE_WEDGE, ON_ARC, IDEA_INK_ON_DARK, False),
    (BLUE_WEDGE, BEYOND, IDEA_INK, False),
    (BLUE_WEDGE, BEYOND, IDEA_INK_ON_DARK, True),
    (YELLOW_ON_RED, ON_ARC, IDEA_INK, False),
    (YELLOW_ON_RED, ON_ARC, IDEA_INK_ON_DARK, True),
    (MOVED_WEDGE, MOVED, IDEA_INK, True),
    (MOVED_WEDGE, MOVED, IDEA_INK_ON_DARK, False),
    (MOVED_WEDGE, ON_ARC, IDEA_INK, False),
]


def ink_finding(drawn: str, x: float, y: float, ink: str) -> bool:
    """Whether S20 finds fault with a letter A in `ink`, its glyph's middle at (x, y), on
    a parchment canvas with `drawn` under it."""
    size = style.IDEA_LETTER_SIZE
    root = ET.fromstring(
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 300">'
        f'<rect width="400" height="300" fill="#fbf7ee"/>{drawn}'
        f'<text x="{x}" y="{y + 0.35 * size}" text-anchor="middle" font-size="{size}" '
        f'font-style="italic" fill="{ink}">A</text></svg>')
    return any(style.ink_fault(root, eff, style.letter_centre(own, eff, m, "A"), "A")
               for el, own, eff, m, _ in style.placed(root) if style.tag(el) == "text")


# ---------------------------------------------------------------------------------------
# The scope cases (#66). (S7 and S12 once skipped the review notes, the reports, the front
# pages and the rendered docstrings, and let "Definition 8" and `hnearer` onto the pages.)

SAMPLE_RECORD = """# review/I/99.toml: a comment no page shows, `hX : T` and Definition 8 in it
[statement]
scope = "restricted"
hypotheses = ["the arms not in one straight line (`hX : ¬ Collinear A B C`)"]
note = "As Definition 8 asks."
short = "arms not in one straight line"

[[passage]]
at = "as Definition 8 says"
kind = "helper"
helper = "Prop9.apart"
note = "By \\"Definition 15\\" in quotation marks, and `Prop9.apart`."

[figure]
case = "D on the side of Definition 3"
"""

SAMPLE_TACIT = """/-! The transfer rules: Definition 15 here is in no page. -/
namespace Elements.Tacit
/-- A point at the radius is on the circle
(the half Definition 15 does not give). -/
axiom on_circle : True
end Elements.Tacit
"""


def note_lines(raw: str, rule, *, names: bool = False) -> list[int]:
    """The lines of the review notes of `raw` in which `rule` finds something, read as
    check_text reads a note for S7 (outside quotations and square brackets), or, with
    `names`, in which S12 finds a name."""
    out = []
    for line0, _, text, last in style.review_texts(raw):
        read = style.SQUARE.sub(style._blank, style.blank_quotes(style.blank_code(
            style.straighten(text))))
        m = None if names else rule.search(read)
        if names and style.lean_names(text):
            out.append(line0 + 1)
        elif m:
            out.append(style.text_lines(read, line0, last)(m.start()))
    return out


SAMPLE_TOML_EDGES = """[statement]
scope = "restricted" # "As Definition 8 says." in a comment
note = \"\"\"
The first line,
then Definition 8.\"\"\"
short = "As Definition 8 says."
hypotheses = ["one\\nDefinition 9"]
"""

SAMPLE_TOML_MORE = """[statement]
note = \"\"\"Note

that one is \\
  given.\"\"\"
short = \"\"\"As Definition 8 says, "so\"\"\"\"\"
"""


def lean_note_findings(src: str, rendered=(), lines: bool = False) -> list:
    """The failures and reports of check_lean_notes on a Lean source, as a file of the
    foundations, with `rendered` its rendered docstrings, (axiom, doc) each, or, with
    `lines`, each failure as (rule, line); the script's own lists are left as they were."""
    saved = (list(style.failures), dict(style.reports))
    try:
        style.failures.clear()
        style.reports.clear()
        docs = []
        for name, doc in rendered:
            line = next(k for k, l in enumerate(src.splitlines(), 1) if f"axiom {name}" in l)
            span = style.docstring_span(src, line, doc)
            docs.append(style.Rendered(name, *span, doc))
        style.check_lean_notes(style.ROOT / "Elements" / "Foundations" / "Sample.lean", src,
                               docs)
        if lines:
            return sorted((r, line) for r, _, line, _ in style.failures)
        return sorted([r for r, *_ in style.failures] + [r for r in style.reports])
    finally:
        style.failures[:] = saved[0]
        style.reports.clear()
        style.reports.update(saved[1])


def s12_asks(texts, audit_built: bool):
    """What s12_plan asks of Lean: the names of its old groups and of its new ones, the
    audit lemmas left unchecked and the words of NOT_DECLARED in use."""
    old, new, unchecked, used = style.s12_plan(texts, audit_built)
    return (sorted(n for g in old.values() for n in g), sorted(n for g in new.values() for n in g),
            unchecked, sorted(used))


MISHNAH = style.ROOT / "mishnah" / "I" / "99.md"
CATALOGUE = style.REPORTS_DIR / "overlaps.md"


def s22(text: str) -> list[str]:
    """What S22 finds in a text: each code span of letters alone."""
    return [m.group(1) for m in style.LETTERS_IN_CODE.finditer(style.letter_spans(text))]


def spans_of(src: str, line: int, doc: str) -> str | None:
    """The text of the docstring `docstring_span` finds above line `line`, or None."""
    span = style.docstring_span(src, line, doc)
    return src[span[0]:span[1]] if span else None


SCOPE_CASES = [   # (rule, its reading, the text, what it should give)
    ("S12", style.lean_names, "(`hBCE : Between B C E`)", ["hBCE"]),
    ("S12", style.lean_names, "(`h₁ : Triangle A₁ A₂ A₄`)", ["h₁"]),
    ("S12", style.lean_names, "as in I.5 (`Prop5.base`)", ["Prop5.base"]),
    ("S12", style.lean_names, "(`Between B C E`)", []),
    ("S12", style.lean_names, "(`∠ A B C`)", []),
    ("S12", style.lean_names, "`x := 1`", []),
    ("S12", style.lean_names, "(`hBCE:Between B C E`, `hBCE' : P`)", ["hBCE", "hBCE'"]),
    ("S12", style.lean_names, "`a :: l`", []),
    ("S12", style.lean_names, "the edition at `https://example.org/x`", []),
    # A comment's quotation is no string; a multi-line string starts below its quotes;
    # an escaped line break in a one-line string reads as a space.
    ("S7", lambda raw: note_lines(raw, style.DEFINITION), SAMPLE_TOML_EDGES, [5, 6, 7]),
    ("S7", lambda raw: [t for _, k, t, _ in style.review_texts(raw)
                        if k == "statement.hypotheses"], SAMPLE_TOML_EDGES, ["one\nDefinition 9"]),
    # A line break after a backslash, and quotation marks before the closing three.
    ("S4", lambda raw: note_lines(raw, style.HEDGE), SAMPLE_TOML_MORE, []),
    ("S7", lambda raw: note_lines(raw, style.DEFINITION), SAMPLE_TOML_MORE, [6]),
    ("S7", lambda raw: note_lines(raw, style.DEFINITION),
     '[statement]\nnote = """\\\nDefinition 3."""\n', [3]),
    ("S7", lambda raw: style.review_texts(raw), "statement = 1\nfigure = [1]\n", []),
    ("S7", lambda raw: style.review_texts(raw, terms=True), "tag = 1\n", []),
    # The mishnah is asked as before: every name, with Elements alone.
    ("S12", lambda ts: s12_asks(ts, False),
     [style.NamedText(MISHNAH, "`direct_axioms`, `Audit.x`, `hX : T`", "E", held=True)],
     (["Audit.x", "direct_axioms", "hX"], [], [], ["direct_axioms"])),
    ("S12", lambda ts: s12_asks(ts, False),
     [style.NamedText(CATALOGUE, "`direct_axioms`, `Audit.x`, `Prop5.base`", "E")],
     ([], ["Prop5.base"], ["Audit.x"], ["direct_axioms"])),
    ("S12", lambda ts: s12_asks(ts, True),
     [style.NamedText(CATALOGUE, "`Audit.x`", "E")], ([], ["Audit.x"], [], [])),
    # Every rule of the Lean notes reads all of them, the rendered docstrings among them,
    # and S6 and S7 read a rendered docstring as the pages show it.
    ("S4", lean_note_findings, "/- Note -/\n/-- that it lies on a line. -/\naxiom a : True\n",
     ["S4"]),
    ("S4", lambda src: lean_note_findings(src, [("a", "that it lies on a line.")]),
     "/- Note -/\n/-- that it lies on a line. -/\naxiom a : True\n", ["S4"]),
    ("S6", lambda src: lean_note_findings(src, [("a", "A tacit assumption.")]),
     "/-- A tacit\n\nassumption. -/\naxiom a : True\n", ["S6"]),
    ("D10", lean_note_findings, "/-- A tacit\nassumption. -/\naxiom a : True\n", ["D10"]),
    ("D10", lambda src: lean_note_findings(src, [("a", "assumption here.")]),
     "/- A tacit -/\n/-- assumption here. -/\naxiom a : True\n", ["D10"]),
    ("D10", lambda src: lean_note_findings(src, [("a", "Apply `Definition 8`.")]),
     "/-- Apply `Definition\n8`. -/\naxiom a : True\n", ["D10"]),
    ("S7", lambda src: lean_note_findings(src, [("a", "As Definition 8 says.")]),
     "/-- As Definition\n8 says. -/\naxiom a : True\n", ["S7"]),
    ("D10", lambda src: lean_note_findings(src, [("a", "A point exists.")]),
     "/- A tacit -/\n/-- A point exists. -/\naxiom a : True\n/- assumption -/\n", []),
    ("S7", lambda src: lean_note_findings(src, [("r", "A point at the radius is on the circle "
                                                     "(Definition 15).")], lines=True),
     "namespace Elements.Tacit\n/-- A point at the radius\nis on the circle (Definition 15). -/"
     "\naxiom r : True\n", [("S7", 3)]),
    ("D4", lambda t: style.lean_names(t, binders=False), "(`hBCE : Between B C E`)", []),
    ("S7", lambda raw: note_lines(raw, style.DEFINITION), SAMPLE_RECORD, [5, 15]),
    ("S12", lambda raw: note_lines(raw, None, names=True), SAMPLE_RECORD, [4, 12]),
    ("S7", lambda raw: [k for _, k, _, _ in style.review_texts(raw)], SAMPLE_RECORD,
     ["statement.hypotheses", "statement.note", "statement.short", "passage.note",
      "figure.case"]),
    ("S7", lambda raw: style.review_texts("not = [toml"), "", []),
    ("S7", lambda src: spans_of(src, 5, "A point at the radius is on the circle (the half "
                                "Definition 15 does not give)."), SAMPLE_TACIT,
     " A point at the radius is on the circle\n(the half Definition 15 does not give). "),
    ("S7", lambda src: spans_of(src, 5, "Another docstring."), SAMPLE_TACIT, None),
    ("S7", lambda src: spans_of(src, 2, "On one line."), "namespace Elements.Tacit\n"
     "/-- On one line. -/ axiom one : True\n", " On one line. "),
    ("S7", lambda src: spans_of(src, 2, "The transfer rules: Definition 15 here is in no "
                                "page."), SAMPLE_TACIT, None),
    ("S22", s22, "the straight line `PQ` and the circle `ABCD`", ["PQ", "ABCD"]),
    ("S22", s22, "`AB, CD` and `A′B′` and `A₁A₂`", ["AB, CD", "A′B′", "A₁A₂"]),
    ("S22", s22, "a lone letter `P`, the Lean's variable, and `M₁`", ["P", "M₁"]),
    ("S22", s22, "the copy `G E C'` of ABC", ["G E C'"]),
    ("S22", s22, "`∠ A B C`, `Prop5.base`, `Centre E ABCD`, `B ≠ C`, `hAB`", []),
    ("S22", s22, "`x` AB `y`", []),
    ("S22", s22, "`AB,CD` and ``AB`CD`` and `A\nB`", ["AB,CD"]),
    ("S22", s22, "`AB\n# `CD`", ["CD"]),
    ("S22", s22, "\\`X and `AB`", ["AB"]),
    ("S22", lambda t: s22(style.FENCE.sub(style._blank, t)), "```\n`AB`\n```\n`CD`",
     ["CD"]),
    ("S7", style.is_catalogue, style.REPORTS_DIR / "overlaps.md", True),
    ("S7", style.is_catalogue, style.REPORTS_DIR / "gaps-book-II.md", True),
    ("S7", style.is_catalogue, style.REPORTS_DIR / "gaps-book-I-supplement.md", True),
    ("S7", style.is_report, style.REPORTS_DIR / "read-through-01.md", True),
    ("S7", style.is_report, style.REPORTS_DIR / "gaps-book-II.md", False),
    ("S7", style.is_report, style.REPORTS_DIR / "outside-review-02.md", False),
    ("S7", style.is_report, style.REPORTS_DIR / "crew" / "voyage-01.md", False),
]


def findings(path, text: str, scopes: set[str], *, pending: str | None, new: bool = False):
    """The failures and the D16 reports of check_text on `text`, as the file `path`, with
    that file listed in REACH_PENDING for the rules `pending`, or not listed; the script's
    own lists are left as they were."""
    saved = (list(style.failures), dict(style.reports), set(style.reach_found),
             dict(style.REACH_PENDING))
    try:
        style.failures.clear()
        style.reports.clear()
        style.REACH_PENDING.clear()
        if pending:
            style.REACH_PENDING[style.rel(path)] = (pending, "a test")
        style.check_text(path, text, scopes, new=new)
        return (sorted(r for r, *_ in style.failures),
                sorted(m.split(":")[0] for _, _, m in style.reports.get("D16", [])))
    finally:
        style.failures[:] = saved[0]
        style.reports.clear()
        style.reports.update(saved[1])
        style.reach_found.clear()
        style.reach_found.update(saved[2])
        style.REACH_PENDING.clear()
        style.REACH_PENDING.update(saved[3])


GAPS = style.REPORTS_DIR / "gaps-book-I.md"
REACH_TEXT = "As Definition 15 says \u2014 and `PQ`."
RECORD = style.ROOT / "review" / "I" / "99.toml"
ALL = "S1 S7 S22"
REACH_CASES = [   # (file, scopes, a new text?, the rules it is listed for, (failures, D16))
    # A gap catalogue was held to S1 before, and is still; S7 and S22 are the reach.
    (GAPS, {"catalogue"}, False, ALL, (["S1"], ["S22", "S7"])),
    (GAPS, {"catalogue"}, False, None, (["S1", "S22", "S7"], [])),
    # A review note is new: while its file is listed for every rule, every finding is
    # reported.
    (RECORD, {"review"}, True, ALL, ([], ["S1", "S22", "S7"])),
    (RECORD, {"review"}, True, None, (["S1", "S22", "S7"], [])),
    # The prose was held to all three before (S22 aside), listed or not.
    (style.ROOT / "mishnah" / "I" / "99.md", {"prose"}, False, ALL, (["S1", "S7"], ["S22"])),
    # A file listed for some rules is held at once to every other rule of the reach.
    (GAPS, {"catalogue"}, False, "S7", (["S1", "S22"], ["S7"])),
    (RECORD, {"review"}, True, "S12", (["S1", "S22", "S7"], [])),
    (style.ROOT / "Elements" / "Foundations" / "Sample.lean", {"lean"}, False, "S22",
     (["S1"], ["S22"])),
]


# ---------------------------------------------------------------------------------------

class Phrases(unittest.TestCase):
    """The phrase cases, each put to its rule's search."""

    def test_phrase_cases(self):
        for rule, search, text, want in PHRASE_CASES:
            with self.subTest(rule=rule, text=text):
                self.assertEqual(bool(search(text)), want,
                                 f"{rule} {'misses' if want else 'wrongly finds'} {text!r}")

    test_phrase_cases.__doc__ = (f"The wording rules read {len(PHRASE_CASES)} wrapped and "
                                 "unwrapped phrases rightly")


class Tex(unittest.TestCase):
    """The TeX cases, each read as S10 reads a mishnah."""

    def test_tex_cases(self):
        for text, want in TEX_CASES:
            with self.subTest(text=text):
                self.assertEqual(bool(style.tex_findings(text)), want,
                                 f"S10 {'misses' if want else 'wrongly finds'} {text!r}")

    test_tex_cases.__doc__ = (f"S10 reads {len(TEX_CASES)} mishnahs on either side of "
                              "the modern way's $…$ rightly")


class Ink(unittest.TestCase):
    """The ink cases, each with each spelling of the wedge."""

    def test_ink_cases(self):
        for under, (x, y), ink, want in INK_CASES:
            for wedge in INK_WEDGES:
                drawn = under.format(wedge=wedge)
                with self.subTest(drawn=drawn, at=(x, y), ink=ink):
                    self.assertEqual(ink_finding(drawn, x, y, ink), want,
                                     f"S20 {'misses' if want else 'wrongly finds'} a letter "
                                     f"in {ink} at ({x:g}, {y:g}) on {drawn}")

    test_ink_cases.__doc__ = (f"S20 reads the ink of {len(INK_CASES) * len(INK_WEDGES)} "
                              "letters on angles' wedges rightly")


class Scopes(unittest.TestCase):
    """The scope cases: the texts the rules read since #66, and how they read them."""

    def test_scope_cases(self):
        for rule, read, text, want in SCOPE_CASES:
            with self.subTest(rule=rule, text=text):
                self.assertEqual(read(text), want, f"{rule} reads {text!r} wrongly")

    test_scope_cases.__doc__ = (f"The new scopes read {len(SCOPE_CASES)} records, docstrings, "
                                "names and letters rightly")

    def test_reach_cases(self):
        for path, scopes, new, pending, want in REACH_CASES:
            with self.subTest(path=style.rel(path), pending=pending):
                self.assertEqual(findings(path, REACH_TEXT, scopes, pending=pending, new=new),
                                 want)

    test_reach_cases.__doc__ = (f"The reach of 19 October is reported in a listed file for "
                                f"the rules it is listed for, and all else fails, in "
                                f"{len(REACH_CASES)} cases")


if __name__ == "__main__":
    unittest.main(verbosity=2)
