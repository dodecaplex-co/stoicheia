#!/usr/bin/env python3
"""The cases of scripts/check_style.py: how its rules read a phrase, TeX, and a letter.

    python3 -I tests/test_check_style.py        # no Lean, no network

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
  rules the file is listed for, while every other finding in that file still fails, and
  whose rules are reported as done one by one, as each is left with no finding;
* the acceptance case: check_acceptance.py sorts a style finding in a review record to
  its proposition's P9, the item for the record's notes, and every other as before;
* the conflict-marker cases: S23 reads tracked UTF-8 text and copies without Git,
  refuses each marker kind even in Markdown fences and comments, allows setext headings
  over ordinary paragraphs but refuses possible reference definitions throughout a block,
  raises on traversal errors and skips symlinks; S12 keeps Git's index.

CI's `check` job runs this file just before check_style.py, and scripts/safe_push.py runs
it in the same place (docs/WORKFLOW.md, section 8), so a case read wrongly stops the
checks before the style check's findings are read. When a rule is found reading a phrase,
TeX or a letter wrongly, its fix comes with a case here that the old rule fails (WORKFLOW,
section 8, "A guard defect gets a regression"). Python 3.11 or later; standard library.
"""

from __future__ import annotations

import os
import runpy
import sys
import tempfile
import unittest
import xml.etree.ElementTree as ET
from collections import defaultdict
from contextlib import ExitStack, redirect_stdout
from io import StringIO
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import check_style as style  # noqa: E402
import negative_tests as plants  # noqa: E402

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
    for note in style.review_texts(raw):
        read = style.SQUARE.sub(style._blank, style.blank_quotes(style.blank_code(
            style.straighten(note.text))))
        m = None if names else rule.search(read)
        if names:
            out.extend(note.line_at(use.at) for use in style.lean_name_occurrences(note.text))
        elif m:
            out.append(note.line_at(m.start()))
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

SAMPLE_TOML_DUPLICATES = """[statement]
scope = "partial"
omitted = ["Definition 8"]
note = "Definition 8"
hypotheses = [
  "Definition 8",
  "Definition 8",
]
short = "partial"

[[passage]]
at = "Definition 8"
kind = "helper"
helper = "Prop1.first"
note = "Definition 8"

[[passage]]
at = "Definition 8"
kind = "helper"
helper = "Prop1.second"
note = "Definition 8"
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
    return [style.flat(m.group(1))
            for m in style.LETTERS_IN_CODE.finditer(style.letter_spans(text))]


def main_named_records() -> list[style.NamedText]:
    """The records main gives S12, with other checks replaced by stubs."""
    captured = []

    def remember(texts):
        captured.extend(texts)
        return 0, []

    with ExitStack() as stack:
        for name in ("check_text", "check_mishnah", "check_reading", "check_intros",
                     "check_figures"):
            stack.enter_context(patch.object(style, name))
        stack.enter_context(patch.object(style, "check_lean_notes", return_value=[]))
        stack.enter_context(patch.object(style, "rendered_docstrings", return_value={}))
        stack.enter_context(patch.object(style, "check_lean_names", side_effect=remember))
        stack.enter_context(patch.object(style, "reach_done", return_value=[]))
        stack.enter_context(patch.object(style.shutil, "which", return_value="lake"))
        stack.enter_context(patch.object(sys, "argv", ["check_style.py"]))
        with redirect_stdout(StringIO()):
            style.main()
    return captured


def main_named_texts() -> dict[Path, str]:
    """The paths and namespaces main gives S12."""
    return {text.path: text.opens for text in main_named_records()}


def failure_lines(text: str, rule: str) -> list[int]:
    """The lines at which check_text fails `rule` in a prose text."""
    saved = (list(style.failures), dict(style.reports), set(style.reach_found))
    try:
        style.failures.clear()
        style.reports.clear()
        style.reach_found.clear()
        style.check_text(MISHNAH, text, {"prose"})
        return [line for found, _, line, _ in style.failures if found == rule]
    finally:
        style.failures[:] = saved[0]
        style.reports.clear()
        style.reports.update(saved[1])
        style.reach_found.clear()
        style.reach_found.update(saved[2])


def lean_failure(text: str, line_at=None) -> list[tuple[int, bool]]:
    """The line and binder hint of an S12 failure returned by Lean for `text`."""
    saved = (list(style.failures), dict(style.reports), style.subprocess.run)

    def reject(args, **_):
        probe = Path(args[-1])
        line = next(k for k, value in enumerate(probe.read_text().splitlines(), 1)
                    if value.startswith("#check"))
        return SimpleNamespace(returncode=1, stdout="",
                               stderr=f"{probe.name}:{line}:1: error: unknown identifier")

    try:
        style.failures.clear()
        style.reports.clear()
        style.subprocess.run = reject
        named = style.NamedText(MISHNAH, text, "Elements", held=True, line_at=line_at)
        old, _, _, _ = style.s12_plan([named], False)
        style.lean_probe(old, ["Elements"])
        return [(line, "Hypotheses in words" in message)
                for rule, _, line, message in style.failures if rule == "S12"]
    finally:
        style.failures[:] = saved[0]
        style.reports.clear()
        style.reports.update(saved[1])
        style.subprocess.run = saved[2]


def review_s12_failures(raw: str) -> list[tuple[int, str]]:
    """The S12 failures after known names in reader-visible review fields pass Lean."""
    saved = (list(style.failures), dict(style.reports), set(style.reach_found),
             style.subprocess.run)
    path = style.ROOT / "review" / "I" / "99.toml"
    try:
        style.failures.clear()
        style.reports.clear()
        style.reach_found.clear()
        notes = style.review_texts(raw)
        named = [style.NamedText(path, note.text, style.book_opens("I"),
                                 line_at=note.line_at,
                                 hypothesis=note.key == "statement.hypotheses")
                 for note in notes]
        _, new, _, _ = style.s12_plan(named, False)
        style.subprocess.run = lambda *_args, **_kwargs: SimpleNamespace(
            returncode=0, stdout="", stderr="")
        style.lean_probe(new, ["Elements"])
        return [(line, message) for rule, _, line, message in style.failures if rule == "S12"]
    finally:
        style.failures[:] = saved[0]
        style.reports.clear()
        style.reports.update(saved[1])
        style.reach_found.clear()
        style.reach_found.update(saved[2])
        style.subprocess.run = saved[3]


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
    ("S12", style.lean_names, r"`not\` `Missing.name`", ["Missing.name"]),
    ("S12", style.lean_names, "`x\n2. y` `Missing.name`", ["Missing.name"]),
    ("S12", style.lean_names, "`x\n01. y` `Missing.name`", []),
    ("S12", style.lean_names, "`x\n1. \n` `Missing.name`", ["Missing.name"]),
    ("S12", style.lean_names, "[x](https://example.test/`) visible `Missing.name`",
     ["Missing.name"]),
    ("S12", style.lean_names, "[x](/my `Missing.name`)", ["Missing.name"]),
    ("S12", style.lean_names, "[x]( \"a `Missing.name` b\")", ["Missing.name"]),
    ("S12", style.lean_names, r"[x](a\ `Missing.name`)", ["Missing.name"]),
    ("S12", style.lean_names, "[x](/u (a(b `Missing.name`))", ["Missing.name"]),
    ("S22", s22, "[x](/my `AB`)", ["AB"]),
    ("S12", style.lean_names, "[x](<https://example.test/`>) visible `Missing.name`",
     ["Missing.name"]),
    ("S12", style.lean_names, "[x](<bad<url `Missing.name`>)", ["Missing.name"]),
    ("S12", style.lean_names, "[x](/my \"title`\") visible `Missing.name`",
     ["Missing.name"]),
    ("S12", style.lean_names, "[x]: https://example.test/`\nvisible `Missing.name`",
     ["Missing.name"]),
    ("S12", style.lean_names, "Foo\n[x]: /baz`\nvisible `Missing.name`", ["visible"]),
    ("S12", style.lean_names, "[x]: /baz extra`\nvisible `Missing.name`", ["visible"]),
    ("S12", style.lean_names,
     "[x]: /one\n[y]: https://example.test/`\nvisible `Missing.name`", ["Missing.name"]),
    ("S12", style.lean_names, "[x]: /url\n \"title `Missing.name`\"", []),
    ("S12", style.lean_names, "[x]: /url\n 'title `Missing.name`'", []),
    ("S12", style.lean_names, "[x]: /url\n (title `Missing.name`)", []),
    ("S12", style.lean_names,
     "[x]: /url\n \"title `Missing.name`\" trailing", ["Missing.name"]),
    ("S12", style.lean_names, r"[x]: a\ `Missing.name`", ["Missing.name"]),
    ("S12", style.lean_names, "<https://example.test/`> visible `Missing.name`",
     ["Missing.name"]),
    ("S12", style.lean_names, r"\<https://x/`Missing.name`>", ["Missing.name"]),
    ("S12", style.lean_names, r"\\<https://x/`Missing.name`>", []),
    ("S12", style.lean_names, "``[x](url`)`` `Missing.name`", ["Missing.name"]),
    ("S12", style.lean_names, "[x `](url`) visible `Missing.name`", ["Missing.name"]),
    ("S12", style.lean_names, "[see `foo](bar)` and `Missing.name`", ["Missing.name"]),
    ("S12", style.lean_names, "`[` x](<u`Missing.name`>)", ["Missing.name"]),
    ("S12", style.lean_names,
     "[outer [inner](url)](bad `Missing.name`)", ["Missing.name"]),
    ("S12", style.lean_names,
     "[outer [inner](url)](bad`Missing.name`)", ["Missing.name"]),
    ("S12", style.lean_names,
     "![outer [inner](url)](bad`Missing.name`)", []),
    ("S12", style.lean_names,
     "[outer ![inner](url)](bad`Missing.name`)", []),
    ("S22", lambda t: [content for _, _, content in style.markdown_code_spans(t)],
     "[see `foo](bar)` and `Missing.name`", ["foo](bar)", "Missing.name"]),
    ("S22", s22, "[`AB](x)` `CD`", ["CD"]),
    ("S12", style.lean_names, "`Missing.name'`", ["Missing.name'"]),
    ("S12", style.lean_names, "`Missing'.name'`", ["Missing'.name'"]),
    ("S12", style.lean_names, "'the `foo` 's", ["foo"]),
    ("S12", style.lean_names, "`Missing.name\n1. `", []),
    ("S12", style.lean_names, "2. `Missing.name\n3. `", []),
    ("S12", style.lean_names,
     "<!-- old: `Missing.name` --> visible `Prop5.base`", ["Prop5.base"]),
    ("S12", style.lean_names, "<!-- old: `Missing.name`", []),
    ("S12", style.lean_names, "`<!--` visible `Prop5.base`", ["Prop5.base"]),
    ("S12", style.lean_names,
     "> <!-- old:\n> `Missing.name`\nvisible `Prop5.base`", ["Prop5.base"]),
    ("S12", style.lean_names,
     "- <!-- old:\n  `Missing.name`\nvisible `Prop5.base`", ["Prop5.base"]),
    ("S12", lean_failure,
     "<!-- `Missing.name : T` -->\nvisible `Missing.name`", [(2, False)]),
    ("S12", lambda text: lean_failure(text, lambda at: 40 + style.line_of(text, at)),
     "<!-- `Missing.name` -->\nvisible `Missing.name : T`", [(42, True)]),
    ("S12", lean_failure,
     "> <!-- old:\n> `Missing.name : T`\nvisible `Missing.name`", [(3, False)]),
    # A comment and a code span are read in source order: the first to open hides the
    # other's markers inside it.
    ("S12", style.lean_names, "Prefix <!-- `old --> visible `Missing.name`", ["Missing.name"]),
    ("S12", lean_failure, "Prefix <!-- `old -->\nvisible `Missing.name`", [(2, False)]),
    ("S12", style.lean_names, "`<!--` visible `Prop5.base` -->", ["Prop5.base"]),
    ("S12", style.lean_names, "a <!-- `x` --> b `Prop5.base` <!-- `Missing.name` -->",
     ["Prop5.base"]),
    ("S12", style.lean_names, "an unclosed <!-- `Missing.name`", ["Missing.name"]),
    ("S12", style.lean_names, "\\<!-- `Missing.name` -->", ["Missing.name"]),
    ("S12", style.lean_names, "> a <!-- x\n> `y` --> `Missing.name`", ["Missing.name"]),
    ("S12", style.lean_names, "text <!-- a\n\n`b` --> `Missing.name`", ["b", "Missing.name"]),
    ("S7", lambda t: failure_lines(t, "S7"), "Prefix <!-- `old --> Definition 8 `x`", [1]),
    ("S22", lambda t: failure_lines(t, "S22"), "Before <!-- `x -->\n`AB`", [2]),
    ("S7", lambda t: failure_lines(t, "S7"), "<!-- hidden\n--> Definition 8", [2]),
    ("S22", style.blank_html_comments, "> a <!-- x\n> `y` --> `AB`",
     "> a       \n>         `AB`"),
    # A comment's quotation is no string; a multi-line string starts below its quotes;
    # an escaped line break in a one-line string reads as a space.
    ("S7", lambda raw: note_lines(raw, style.DEFINITION), SAMPLE_TOML_EDGES, [5, 6, 7]),
    ("S7", lambda raw: [note.text for note in style.review_texts(raw)
                        if note.key == "statement.hypotheses"], SAMPLE_TOML_EDGES,
     ["one\nDefinition 9"]),
    # A line break after a backslash, and quotation marks before the closing three.
    ("S4", lambda raw: note_lines(raw, style.HEDGE), SAMPLE_TOML_MORE, []),
    ("S7", lambda raw: note_lines(raw, style.DEFINITION), SAMPLE_TOML_MORE, [6]),
    ("S7", lambda raw: note_lines(raw, style.DEFINITION), SAMPLE_TOML_DUPLICATES,
     [4, 6, 7, 15, 21]),
    ("S7", lambda raw: note_lines(raw, style.DEFINITION),
     '[statement]\nnote = """\\\nDefinition 3."""\n', [3]),
    ("S7", lambda raw: note_lines(raw, style.DEFINITION),
     '[statement]\nnote = """before \\\n  Definition 8"""\n', [3]),
    ("S7", lambda raw: note_lines(raw, style.DEFINITION),
     "[statement]\nnote = '''\nbefore\nDefinition 9'''\n", [4]),
    ("S7", lambda raw: note_lines(raw, style.DEFINITION),
     '[statement]\nnote = "before\\nDefinition 10"\n', [2]),
    ("S7", lambda raw: note_lines(raw, style.DEFINITION),
     "[statement]\nnote = 'Definition 11'\n", [2]),
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
     "/-- Apply `Definition\n8`. -/\naxiom a : True\n", []),
    ("S7", lambda src: lean_note_findings(src, [("a", "As Definition 8 says.")]),
     "/-- As Definition\n8 says. -/\naxiom a : True\n", ["S7"]),
    ("D10", lambda src: lean_note_findings(src, [("a", "A point exists.")]),
     "/- A tacit -/\n/-- A point exists. -/\naxiom a : True\n/- assumption -/\n", []),
    ("S7", lambda src: lean_note_findings(src, [("r", "A point at the radius is on the circle "
                                                     "(Definition 15).")], lines=True),
     "namespace Elements.Tacit\n/-- A point at the radius\nis on the circle (Definition 15). -/"
     "\naxiom r : True\n", [("S7", 3)]),
    ("S22", lean_note_findings, "/- `x -/\n/- `AB` -/\n", ["S22"]),
    ("D4", lambda t: style.lean_names(t, binders=False), "(`hBCE : Between B C E`)", []),
    ("S7", lambda raw: note_lines(raw, style.DEFINITION), SAMPLE_RECORD, [5, 15]),
    ("S12", lambda raw: note_lines(raw, None, names=True), SAMPLE_RECORD, [4, 12]),
    ("S7", lambda raw: [note.key for note in style.review_texts(raw)], SAMPLE_RECORD,
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
    ("S22", s22, "`AB,CD` and ``AB`CD`` and `A\nB`", ["AB,CD", "A B"]),
    ("S22", s22, "the straight lines `AB,\nCD`", ["AB, CD"]),
    ("S22", s22, "> `AB,\n> CD`", ["AB, CD"]),
    ("S22", s22, "> `AB,\nCD`", ["AB, CD"]),
    ("S22", s22, "- `AB,\n  CD`", ["AB, CD"]),
    ("S22", lambda t: [content for _, _, content in style.markdown_code_spans(t)],
     "` AB,\nCD `", ["AB, CD"]),
    ("S22", lambda t: failure_lines(t, "S22"), "Before\n`AB,\nCD`", [2]),
    ("S22", lambda t: failure_lines(t, "S22"), "Before\n> `AB,\nCD`", [2]),
    ("S7", lambda t: failure_lines(t, "S7"),
     "plain `Definition\n8` text\nDefinition 9", [3]),
    ("S22", s22, "`AB\n# `CD`", ["CD"]),
    ("S22", s22, "# `AB\n`CD`", ["CD"]),
    ("S22", s22, "> `AB,\n# CD`", []),
    ("S22", s22, "`AB\n\n`EF`", ["EF"]),
    ("S22", s22, "\\`X and `AB`", ["AB"]),
    ("S22", s22, "```\n`AB`\n```\n`CD`", ["CD"]),
    ("S22", s22, "~~~\n`AB`\n~~~\n`CD`", ["CD"]),
    ("S12", style.lean_names, "    `Missing.name`", []),
    ("S12", style.lean_names, "\t`Missing.name`", []),
    ("S12", style.lean_names, "paragraph\n    `Missing.name`", ["Missing.name"]),
    ("S12", style.lean_names, "- paragraph\n      `Missing.name`", ["Missing.name"]),
    ("S12", style.lean_names, "- paragraph\n\n      `Missing.name`", []),
    ("S12", style.lean_names, ">     `Missing.name`", []),
    ("S12", style.lean_names, "> paragraph\n>     `Missing.name`", ["Missing.name"]),
    ("S22", s22, "> ```\n> `CD`\nordinary `AB`", ["AB"]),
    ("S22", lambda t: failure_lines(t, "S22"),
     "> ```\n> `CD`\nordinary `AB`", [3]),
    ("S22", s22, "> ```\n> hidden\n- `AB,\n- CD`", []),
    ("S22", s22, "- ```\n  `CD`\nordinary `AB`", ["AB"]),
    ("S22", s22, "H |\n--- |\n`AB\nCD`", []),
    ("S12", style.lean_names, "H |\n--- |\n`Missing.name\n`", []),
    ("S22", lambda t: [content for _, _, content in style.markdown_code_spans(t)],
     "A | B\n--- | ---\n`AB \\| CD` | `EF`", [r"AB \| CD", "EF"]),
    ("S22", lambda t: failure_lines(t, "S22"),
     "A | B\n--- | ---\nplain | `AB`", [3]),
    ("S12", style.lean_names,
     "A | B\n--- | ---\nok | ok | `Missing.name`", []),
    ("S12", style.lean_names,
     "A | B\n--- | ---\nok | `Missing.name` | ignored", ["Missing.name"]),
    ("S12", style.lean_names,
     "A | B\n--- | ---\n[x]: `Missing.name` | ok", ["Missing.name"]),
    ("S7", style.is_catalogue, style.REPORTS_DIR / "overlaps.md", True),
    ("S7", style.is_catalogue, style.REPORTS_DIR / "gaps-book-II.md", True),
    ("S7", style.is_catalogue, style.REPORTS_DIR / "gaps-book-I-supplement.md", True),
    ("S7", style.is_report, style.REPORTS_DIR / "read-through-01.md", True),
    ("S7", style.is_report, style.REPORTS_DIR / "gaps-book-II.md", False),
    ("S7", style.is_report, style.REPORTS_DIR / "outside-review-02.md", False),
    ("S7", style.is_report, style.REPORTS_DIR / "crew" / "voyage-01.md", False),
]


def reach_run(path, text: str, scopes: set[str], pending: str | None, new: bool, read):
    """What `read()` gives after check_text on `text`, as the file `path`, with that file
    listed in REACH_PENDING for the rules `pending`, or not listed; the script's own lists
    are left as they were."""
    saved = (list(style.failures), dict(style.reports), set(style.reach_found),
             dict(style.REACH_PENDING))
    try:
        style.failures.clear()
        style.reports.clear()
        style.reach_found.clear()
        style.REACH_PENDING.clear()
        if pending:
            style.REACH_PENDING[style.rel(path)] = (pending, "a test")
        style.check_text(path, text, scopes, new=new)
        return read()
    finally:
        style.failures[:] = saved[0]
        style.reports.clear()
        style.reports.update(saved[1])
        style.reach_found.clear()
        style.reach_found.update(saved[2])
        style.REACH_PENDING.clear()
        style.REACH_PENDING.update(saved[3])


def findings(path, text: str, scopes: set[str], *, pending: str | None, new: bool = False):
    """The failures and the D16 reports of check_text on `text`, as the file `path`, with
    that file listed in REACH_PENDING for the rules `pending`, or not listed."""
    return reach_run(path, text, scopes, pending, new, lambda: (
        sorted(r for r, *_ in style.failures),
        sorted(m.split(":")[0] for _, _, m in style.reports.get("D16", []))))


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
GAPS_REL = style.rel(GAPS)
DONE_CASES = [   # (a text of the gap catalogue, the rules it is listed for, --no-lean?, done)
    # Listed for two rules, with a finding of one: the other is done, and the entry is not.
    (REACH_TEXT, "S7 S12", False, [(GAPS_REL, ["S12"], False)]),
    # No finding of a rule it is listed for: the entry is done, though an em dash fails.
    ("Plain words \u2014 and more.", "S7 S22", False, [(GAPS_REL, ["S7", "S22"], True)]),
    # Under --no-lean S12 found nothing, so it is never done; S7 and S22 still are.
    ("Plain words.", "S12", True, []),
    ("Plain words.", "S22", True, [(GAPS_REL, ["S22"], True)]),
    ("Plain words.", "S7 S12", True, [(GAPS_REL, ["S7"], False)]),
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

    def test_review_hypothesis_binders_are_words(self):
        """A known declaration cannot make binder syntax pass in a hypothesis field."""
        raw = ('[statement]\n'
               'note = "The postulate is `Postulate5`."\n'
               'hypotheses = ["the condition (`Postulate5 : P`)"]\n')
        found = review_s12_failures(raw)
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0][0], 3)
        self.assertIn("write the hypothesis in words", found[0][1])

    def test_review_hypothesis_fields_reach_s12(self):
        """Main retains which reader-visible review strings are hypotheses."""
        actual = sorted((str(text.path), text.text) for text in main_named_records()
                        if text.hypothesis)
        expected = sorted((str(path), note.text) for path in style.review_files()
                          for note in style.review_texts(path.read_text(encoding="utf-8"))
                          if note.key == "statement.hypotheses")
        self.assertEqual(actual, expected)

    def test_reports_reach_s12(self):
        """Every eligible ordinary report is among the texts main gives S12."""
        named = main_named_texts()
        self.assertEqual({path: named.get(path) for path in style.report_files()},
                         {path: style.every_book_opens() for path in style.report_files()})

    def test_report_token_classification(self):
        """Reports distinguish declarations from syntax, files and explicitly named objects."""
        vocabulary = ({"axiom", "native_decide", "implemented_by"},
                      {"Elements", "Elements.BookIII"})
        cases = [
            ("`NOTICE:59-60`, `README:17`, `references.bib:9` and `references.bib`", []),
            ("`NOTICE` and `README`", ["NOTICE", "README"]),
            ("The file `NOTICE`, the `README` page and the script `check_fidelity`.", []),
            ("The files `NOTICE` and `README`.", []),
            ("It passes `check_fidelity`.", ["check_fidelity"]),
            ("The declaration `README` is missing.", ["README"]),
            ("The declaration `README.md` is missing.", ["README.md"]),
            ("The declaration `grind` is missing.", ["grind"]),
            ("`Squares.lean` is a nested repository file.", []),
            ("The theorem `Squares.lean` is missing.", ["Squares.lean"]),
            ("The declaration `references.bib`, the `NOTICE` theorem and the files "
             "`README`, `check_fidelity`.", ["NOTICE", "references.bib"]),
            ("The declarations `Elements` and `axiom`.", ["Elements", "axiom"]),
            ("`NOTICE : Point` and `README : Point`", ["NOTICE", "README"]),
            ("`axiom`, `native_decide`, `implemented_by`", []),
            ("`Elements` and `Elements.BookIII`", []),
            ("The namespace `Example.Geometry`. Later, `Example.Geometry`.", []),
            ("The namespace `Example.Geometry`. Then `Example.geometry`.", ["Example.geometry"]),
            ("<!-- namespace `Missing.name` -->\n`Missing.name`", ["Missing.name"]),
            ("The tactics\n`external_step` / `external_finish`.", []),
            ("`external_step` and `Exceeds.nearVertexOpen`",
             ["Exceeds.nearVertexOpen", "external_step"]),
            ("Internet Archive scans: vol. 4 (a supplement) is `another_scan_04`.", []),
            ("An Internet Archive scan `another_scan_04`.", []),
            ("`another_scan_04` is a name to check.", ["another_scan_04"]),
            ("The revision read at `abcdef1`.", []),
            ("`abcdef1`", ["abcdef1"]),
            ("The record has stage `full`, with a `helper` passage.", []),
            ("`full` and `helper`", ["full", "helper"]),
            ("The `axiom_modules` field of `facts.json`.", []),
            ("The record's `helper : Point`.", ["helper"]),
            ("The `Example.` family and `Example.missing`.", ["Example.missing"]),
            ("A tactic `external_step`.\n\nA declaration `external_step`.", ["external_step"]),
        ]
        path = style.REPORTS_DIR / "sample.md"
        for raw, want in cases:
            with self.subTest(raw=raw):
                named = style.NamedText(path, raw, style.every_book_opens())
                old, new, unchecked, _ = style.s12_plan([named], True, vocabulary)
                self.assertFalse(old)
                self.assertFalse(unchecked)
                self.assertEqual(sorted(n for g in new.values() for n in g), want)

    def test_explicit_declaration_does_not_use_exemption(self):
        """An explicit declaration use is checked rather than satisfying NOT_DECLARED."""
        path = style.REPORTS_DIR / "sample.md"
        named = style.NamedText(path, "The declaration `grind` is missing.",
                                style.every_book_opens())
        _, new, _, used = style.s12_plan([named], True, ({"grind"}, set()))
        self.assertEqual(sorted(n for group in new.values() for n in group), ["grind"])
        self.assertNotIn("grind", used)

    def test_only_page_axioms_have_rendered_docstrings(self):
        """Rendered-docstring scope follows the axioms shown on proposition pages."""
        shown = {doc.name for docs in style.rendered_docstrings().values() for doc in docs}
        self.assertIn("Tacit.add_assoc", shown)
        self.assertNotIn("Tacit.exists_point_inside_circle", shown)

    def test_report_classification_keeps_mishnah_enforcement(self):
        """The report's syntax and namespace classification cannot excuse a mishnah name."""
        raw = "`axiom` and `Elements` and `NOTICE` and `grind` and `Unknown.name`."
        named = style.NamedText(MISHNAH, raw, style.book_opens("I"), held=True)
        old, new, _, _ = style.s12_plan([named], True, ({"axiom"}, {"Elements"}))
        self.assertEqual(sorted(n for g in old.values() for n in g),
                         ["Elements", "NOTICE", "Unknown.name", "axiom", "grind"])
        self.assertFalse(new)

    def test_report_vocabulary_failure_is_not_pending(self):
        """A failed syntax query fails S12 itself, even when its report is pending."""
        path = style.REPORTS_DIR / "sample.md"
        with ExitStack() as stack:
            stack.enter_context(patch.object(style, "failures", []))
            stack.enter_context(patch.object(style, "lean_short", []))
            stack.enter_context(patch.object(style, "REACH_PENDING",
                                             {style.rel(path): ("S12", "a test")}))
            stack.enter_context(patch.object(style.subprocess, "run", return_value=
                SimpleNamespace(returncode=1, stdout="", stderr="could not import Elements")))
            named = style.NamedText(path, "`Missing.name`", style.every_book_opens())
            self.assertEqual(style.report_vocabulary([named]), (set(), set()))
            self.assertEqual(len(style.failures), 1)
            self.assertEqual(style.failures[0][:2], ("S12", style.rel(style.SCRIPT)))
            self.assertTrue(style.lean_short)
            self.assertFalse(style.reach_done())

    def test_report_pending_names_and_error_limit(self):
        """A report's unknown name fails without S12 pending, including after 100 errors."""
        path = style.REPORTS_DIR / "sample.md"

        def reject(args, **_):
            self.assertIn("-DmaxErrors=0", args)
            probe = Path(args[-1])
            errors = [f"{probe.name}:{k}:1: error: unknown identifier"
                      for k, line in enumerate(probe.read_text().splitlines(), 1)
                      if line.startswith("#check")]
            return SimpleNamespace(returncode=1, stdout="\n".join(errors), stderr="")

        for pending, want_fail, want_defer in ((None, 1, 0), ("S7", 1, 0), ("S12", 0, 1)):
            with self.subTest(pending=pending), ExitStack() as stack:
                stack.enter_context(patch.object(style, "failures", []))
                stack.enter_context(patch.object(style, "reports", defaultdict(list)))
                stack.enter_context(patch.object(style, "reach_found", set()))
                stack.enter_context(patch.object(style, "REACH_PENDING",
                    {style.rel(path): (pending, "a test")} if pending else {}))
                stack.enter_context(patch.object(style.subprocess, "run", side_effect=reject))
                named = style.NamedText(path, "A name:\n`Exceeds.nearVertexOpen`.",
                                       style.every_book_opens())
                _, groups, _, _ = style.s12_plan([named], False)
                self.assertEqual(style.lean_probe(groups, ["Elements"]), 1)
                self.assertEqual(len(style.failures), want_fail)
                self.assertEqual(len(style.reports.get("D16", [])), want_defer)
                if want_fail:
                    self.assertEqual(style.failures[0][:3], ("S12", style.rel(path), 2))
                else:
                    self.assertEqual(style.reports["D16"][0][:2], (style.rel(path), 2))
                    self.assertFalse(style.reach_done())

        with ExitStack() as stack:
            stack.enter_context(patch.object(style, "failures", []))
            stack.enter_context(patch.object(style, "reports", defaultdict(list)))
            stack.enter_context(patch.object(style, "reach_found", set()))
            stack.enter_context(patch.object(style, "REACH_PENDING",
                                             {style.rel(path): ("S12", "a test")}))
            stack.enter_context(patch.object(style.subprocess, "run", side_effect=reject))
            raw = " ".join(f"`Missing.name{k:03}`" for k in range(105))
            later = style.REPORTS_DIR / "later.md"
            named = [style.NamedText(path, raw, style.every_book_opens()),
                     style.NamedText(later, "`ZMissing.later`", style.every_book_opens())]
            _, groups, _, _ = style.s12_plan(named, False)
            self.assertEqual(style.lean_probe(groups, ["Elements"]), 106)
            self.assertEqual(len(style.reports["D16"]), 105)
            self.assertEqual(len(style.failures), 1)
            self.assertEqual(style.failures[0][:3], ("S12", style.rel(later), 1))

    def test_reach_cases(self):
        for path, scopes, new, pending, want in REACH_CASES:
            with self.subTest(path=style.rel(path), pending=pending):
                self.assertEqual(findings(path, REACH_TEXT, scopes, pending=pending, new=new),
                                 want)

    test_reach_cases.__doc__ = (f"The reach of 19 October is reported in a listed file for "
                                f"the rules it is listed for, and all else fails, in "
                                f"{len(REACH_CASES)} cases")

    def test_done_cases(self):
        for text, pending, no_lean, want in DONE_CASES:
            with self.subTest(text=text, pending=pending, no_lean=no_lean):
                self.assertEqual(reach_run(GAPS, text, {"catalogue"}, pending, False,
                                           lambda: style.reach_done(no_lean)), want)

    test_done_cases.__doc__ = (f"A rule of a listed file with no finding of it left is "
                               f"reported as done, and the entry once all its rules are, in "
                               f"{len(DONE_CASES)} more reach cases")

    def test_done_without_lean(self):
        """S12 is not reported done when Lean could not be run, as without `lake`"""
        name = style.NamedText(GAPS, "`Unknown.name`", "Elements")
        use = style.NameUse(name, 0, False)
        saved = (os.environ.get("PATH"), list(style.lean_short))
        try:
            with tempfile.TemporaryDirectory() as empty:
                os.environ["PATH"] = empty   # no `lake` to be found
                style.lean_short.clear()
                done = reach_run(GAPS, "Plain words.", {"catalogue"}, "S7 S12", False, lambda: (
                    style.lean_probe({"Elements": {"Unknown.name": [use]}}, ["Elements"]),
                    sorted(r for r, *_ in style.failures), style.reach_done(False)))
        finally:
            if saved[0] is None:
                os.environ.pop("PATH", None)
            else:
                os.environ["PATH"] = saved[0]
            style.lean_short[:] = saved[1]
        self.assertEqual(done, (0, ["S12"], [(GAPS_REL, ["S7"], False)]))


class ConflictMarkers(unittest.TestCase):
    """Raw text, including fences, and the boundary between separators and headings."""

    def test_edges_with_and_without_labels(self):
        for char, kind in (("<", "opening"), ("|", "base"), (">", "closing")):
            for ending in ("", " ours", " ", "\r", " ours\r"):
                with self.subTest(char=char, ending=ending):
                    text = "A paragraph.\n" + char * 7 + ending + "\n"
                    self.assertEqual(style.conflict_markers(text, markdown=True), [(2, kind)])

    def test_exact_edge_width_and_boundary(self):
        for char in "<|>":
            for line in (char * 6, char * 8, char * 8 + " ours", char * 7 + "ours",
                         char * 7 + "\tours", " " + char * 7 + " ours"):
                with self.subTest(line=line):
                    self.assertEqual(style.conflict_markers(line, markdown=False), [])

    def test_middle_between_edges_after_paragraph(self):
        for ending in ("", "  ", "\r", " \t\r"):
            with self.subTest(ending=ending):
                text = "\n".join(("<" * 7 + " ours", "A paragraph.", "=" * 7 + ending,
                                  "The other side.", ">" * 7 + " theirs"))
                self.assertEqual(style.conflict_markers(text, markdown=True),
                                 [(1, "opening"), (3, "middle"), (5, "closing")])

    def test_diff3_block(self):
        text = "\n".join(("<" * 7, "Ours.", "|" * 7, "Base.", "=" * 7,
                          "Theirs.", ">" * 7))
        self.assertEqual(style.conflict_markers(text, markdown=True),
                         [(1, "opening"), (3, "base"), (5, "middle"), (7, "closing")])

    def test_middle_needs_both_edges_to_override_setext(self):
        for text, expected in (
            ("\n".join(("<" * 7, "A heading", "=" * 7)), [(1, "opening")]),
            ("\n".join(("A heading", "=" * 7, ">" * 7)), [(3, "closing")]),
            ("\n".join(("<" * 7, ">" * 7, "A heading", "=" * 7)),
             [(1, "opening"), (2, "closing")]),
        ):
            with self.subTest(text=text):
                self.assertEqual(style.conflict_markers(text, markdown=True), expected)

    def test_lone_middle_in_non_markdown(self):
        for ending in ("", " ", "\r"):
            with self.subTest(ending=ending):
                self.assertEqual(style.conflict_markers("Text.\n" + "=" * 7 + ending,
                                                       markdown=False), [(2, "middle")])

    def test_setext_headings_of_any_length(self):
        for width in (1, 6, 7, 8, 80):
            for paragraph in ("A heading", "A paragraph\ncontinued", "#hashtag",
                              "#" * 7 + " is paragraph text"):
                with self.subTest(width=width, paragraph=paragraph):
                    self.assertEqual(style.conflict_markers(
                        paragraph + "\n" + "=" * width + " \r\n", markdown=True), [])

    def test_middle_after_completed_setext_heading(self):
        for char in "=-":
            for width in (1, 3, 7, 8):
                with self.subTest(char=char, width=width):
                    text = "Heading\n   " + char * width + " \t\n" + "=" * 7
                    self.assertEqual(style.conflict_markers(text, markdown=True),
                                     [(3, "middle")])

    def test_middle_in_comment_blocks(self):
        for indent in ("", " ", "   "):
            for ending in ("", "\n-->"):
                with self.subTest(indent=indent, ending=ending):
                    text = indent + "<!--\nComment text\n" + "=" * 7 + ending
                    self.assertEqual(style.conflict_markers(text, markdown=True),
                                     [(3, "middle")])
        for comment in ("<!-- one line -->", "<!--\ncomment\n-->"):
            text = comment + "\n" + "=" * 7
            self.assertEqual(style.conflict_markers(text, markdown=True),
                             [(text.count("\n") + 1, "middle")])

    def test_comment_fences_do_not_escape_the_comment(self):
        for fence in ("```", "~~~~"):
            for gap in ("", "\n"):
                with self.subTest(fence=fence, gap=gap):
                    text = "<!--\n" + fence + "\n-->\n" + gap + "Heading\n" + "=" * 7
                    self.assertEqual(style.conflict_markers(text, markdown=True), [])
        for char, kind in (("<", "opening"), ("|", "base"), ("=", "middle"),
                           (">", "closing")):
            text = "<!--\n```\nComment text\n" + char * 7 + "\n-->"
            self.assertEqual(style.conflict_markers(text, markdown=True), [(4, kind)])

    def test_comment_openers_in_fences_do_not_escape_the_fence(self):
        text = "\n".join(("```", "<!--", "```", "Heading", "=" * 7))
        self.assertEqual(style.conflict_markers(text, markdown=True), [])

    def test_middle_in_html_blocks(self):
        for html in ("<div>", "<div>\nbody", "<div>\nbody\n</div>",
                     "<script>\ncode\n</script>", "<?instruction?>", "<!DOCTYPE html>",
                     "<![CDATA[text]]>", '<x title="a>b">', "<source src=x"):
            with self.subTest(html=html):
                text = html + "\n" + "=" * 7
                self.assertEqual(style.conflict_markers(text, markdown=True),
                                 [(text.count("\n") + 1, "middle")])

    def test_html_block_termination_restores_paragraph_headings(self):
        for html in ("<div>\nbody\n</div>", "<script>\ncode\n</script>"):
            with self.subTest(html=html):
                text = html + "\n\nHeading\n" + "=" * 7
                self.assertEqual(style.conflict_markers(text, markdown=True), [])

    def test_html_blocks_keep_exact_width_and_edge_detection(self):
        for width in (6, 8):
            self.assertEqual(style.conflict_markers("<div>\n" + "=" * width,
                                                   markdown=True), [])
        text = "<div>\n" + "<" * 7 + " ours\n" + ">" * 7 + " theirs"
        self.assertEqual(style.conflict_markers(text, markdown=True),
                         [(2, "opening"), (3, "closing")])

    def test_inline_html_remains_paragraph_text(self):
        for paragraph in ('Text <x title="a>b">', '<x title="a>b"> trailing'):
            with self.subTest(paragraph=paragraph):
                self.assertEqual(style.conflict_markers(
                    paragraph + "\n" + "=" * 7, markdown=True), [])

    def test_middle_after_gfm_table_delimiter_and_rows(self):
        for table in ("| A | B |\n| --- | --- |",
                      "A | B\n--- | ---\nleft | right\nnext | row",
                      "| A | B |\n| --- | --- |\nplain"):
            with self.subTest(table=table):
                text = table + "\n" + "=" * 7
                self.assertEqual(style.conflict_markers(text, markdown=True),
                                 [(text.count("\n") + 1, "middle")])

    def test_gfm_table_termination_restores_paragraph_headings(self):
        table = "| A | B |\n| --- | --- |\nplain\n"
        for boundary in ("\n", "# Boundary\n", "---\n", "> quote\n\n", "- item\n\n",
                         "```\ncode\n```\n", "<div>\nbody\n\n"):
            with self.subTest(boundary=boundary):
                text = table + boundary + "Heading\n" + "=" * 7
                self.assertEqual(style.conflict_markers(text, markdown=True), [])

    def test_gfm_tables_keep_exact_width_and_edge_detection(self):
        table = "| A | B |\n| --- | --- |\n"
        for width in (6, 8):
            self.assertEqual(style.conflict_markers(table + "=" * width, markdown=True), [])
        text = table + "|" * 7 + " base\n" + ">" * 7
        self.assertEqual(style.conflict_markers(text, markdown=True),
                         [(3, "base"), (4, "closing")])

    def test_multiline_reference_definition_taints_the_block(self):
        for definition in ("[\nfoo\n]: /url", "  [\nfoo\n]:", "[\nfo\\]o\n]: /url"):
            with self.subTest(definition=definition):
                text = definition + "\n" + "=" * 7
                self.assertEqual(style.conflict_markers(text, markdown=True),
                                 [(text.count("\n") + 1, "middle")])

    def test_multiline_reference_candidate_resets_or_remains_paragraph_text(self):
        for prefix in ("[\nfoo\n\n", "[\nfoo\n] not a definition\n"):
            with self.subTest(prefix=prefix):
                self.assertEqual(style.conflict_markers(
                    prefix + "Heading\n" + "=" * 7, markdown=True), [])

    def test_multiline_reference_keeps_exact_middle_width(self):
        definition = "[\nfoo\n]: /url\n"
        for width in (6, 8):
            with self.subTest(width=width):
                self.assertEqual(style.conflict_markers(
                    definition + "=" * width, markdown=True), [])

    def test_middle_after_indented_code(self):
        for indent in ("    ", "\t", "  \t"):
            for prefix in ("", "Paragraph\n\n"):
                with self.subTest(indent=indent, prefix=prefix):
                    text = prefix + indent + "code\n" + "=" * 7
                    self.assertEqual(style.conflict_markers(text, markdown=True),
                                     [(text.count("\n") + 1, "middle")])

    def test_indented_continuation_is_still_a_paragraph(self):
        for indent in ("    ", "\t", "  \t"):
            with self.subTest(indent=indent):
                text = "Heading\n" + indent + "continued\n" + "=" * 7
                self.assertEqual(style.conflict_markers(text, markdown=True), [])

    def test_middle_after_link_reference_definition(self):
        for indent in ("", " ", "   "):
            for destination in ("destination", "<somewhere>", 'destination "Title"'):
                with self.subTest(indent=indent, destination=destination):
                    text = indent + "[label]: " + destination + "\n" + "=" * 7
                    self.assertEqual(style.conflict_markers(text, markdown=True),
                                     [(2, "middle")])
        text = "[label]: destination\nHeading\ncontinued\n" + "=" * 7
        self.assertEqual(style.conflict_markers(text, markdown=True), [(4, "middle")])

    def test_reference_shape_inside_paragraph_refuses_middle(self):
        text = "Heading\n[label]: destination\n" + "=" * 7
        self.assertEqual(style.conflict_markers(text, markdown=True), [(3, "middle")])

    def test_reference_definition_bypasses_through_scanner(self):
        definitions = ("[label]:\n /url", '[label]: /url\n "Title"',
                       r"[la\]bel]: /url")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "definition.md"
            for definition in definitions:
                with self.subTest(definition=definition):
                    path.write_text(definition + "\n" + "=" * 7 + "\n")
                    with patch.object(style, "ROOT", root), \
                            patch.object(style, "failures", []):
                        style.check_conflict_markers()
                        self.assertEqual(style.failures, [
                            ("S23", "definition.md", definition.count("\n") + 2,
                             "middle merge-conflict marker"),
                        ])

    def test_possible_reference_definition_taints_whole_block(self):
        for indent in ("", " ", "  ", "   "):
            for label in ("label", r"la\[bel", r"la\]bel", r"la\[b\]el", r"label\\"):
                for prefix in ("", "Heading\n"):
                    with self.subTest(indent=indent, label=label, prefix=prefix):
                        text = (prefix + indent + "[" + label + "]:\n /url\n"
                                '"Title"\ncontinued\n' + "=" * 7)
                        self.assertEqual(style.conflict_markers(text, markdown=True),
                                         [(text.count("\n") + 1, "middle")])

    def test_doubtful_reference_heading_uses_eight_equals(self):
        # Extra words make paragraph text, but refusal is the deliberate price
        # of treating every possible definition prefix conservatively.
        for width in (1, 6, 7, 8, 80):
            with self.subTest(width=width):
                text = "[label]: destination extra words\n" + "=" * width
                expected = [(2, "middle")] if width == 7 else []
                self.assertEqual(style.conflict_markers(text, markdown=True), expected)

    def test_middle_after_block_quote_or_list_item_is_refused(self):
        for start in ("> quote", "- item", "* item", "+ item", "1. item", "12) item",
                      "Para\n> quote", "Para\n- item"):
            with self.subTest(start=start):
                text = start + "\n" + "=" * 7
                line = text.count("\n") + 1
                self.assertEqual(style.conflict_markers(text, markdown=True), [(line, "middle")])
                self.assertEqual(style.conflict_markers(start + "\n" + "=" * 8, markdown=True), [])
        for text in ("-item\n", "1.5 metres\n", "*emphasis* here\n"):
            with self.subTest(paragraph=text):
                self.assertEqual(style.conflict_markers(text + "=" * 7, markdown=True), [])

    def test_reference_definition_stops_at_block_boundary(self):
        for boundary in ("\n", "<!-- comment -->\n", "<!--\ncomment\n-->\n",
                         "```\ncode\n```\n", "# Heading\n", "---\n",
                         "Heading\n" + "=" * 8 + "\n"):
            with self.subTest(boundary=boundary):
                text = "[label]: /url\n" + boundary + "Heading\ncontinued\n" + "=" * 7
                self.assertEqual(style.conflict_markers(text, markdown=True), [])

    def test_brackets_without_reference_prefix_remain_paragraph_text(self):
        for line in ("[label] text", "[label] : /url", r"\[label]: /url",
                     "Text [label]: /url", "[unescaped[bracket]: /url"):
            with self.subTest(line=line):
                self.assertEqual(style.conflict_markers(line + "\n" + "=" * 7,
                                                       markdown=True), [])

    def test_lone_middle_without_paragraph(self):
        for previous in ("", "  ", "#", "## A heading", "   ### Heading",
                         "---", "* * *", "___"):
            with self.subTest(previous=previous):
                self.assertEqual(style.conflict_markers(previous + "\n" + "=" * 7,
                                                       markdown=True), [(2, "middle")])
        self.assertEqual(style.conflict_markers("=" * 7, markdown=True), [(1, "middle")])

    def test_middle_after_each_marker(self):
        for char, kind in (("<", "opening"), ("|", "base"), (">", "closing"),
                           ("=", "middle")):
            with self.subTest(char=char):
                self.assertEqual(style.conflict_markers(char * 7 + "\n" + "=" * 7,
                                                       markdown=True),
                                 [(1, kind), (2, "middle")])

    def test_other_equals_lines(self):
        for line in ("=" * 6, "=" * 8, "=" * 7 + " label", " " + "=" * 7):
            with self.subTest(line=line):
                self.assertEqual(style.conflict_markers(line, markdown=False), [])

    def test_markers_in_fences(self):
        for fence in ("```", "~~~~"):
            for char, kind in (("<", "opening"), ("|", "base"), ("=", "middle"),
                               (">", "closing")):
                with self.subTest(fence=fence, char=char):
                    text = "\n".join((fence + "text", "A code line.", char * 7, fence))
                    self.assertEqual(style.conflict_markers(text, markdown=True), [(3, kind)])

    def test_middle_at_fence_boundaries(self):
        for text, line in (
            ("\n".join(("```text", "=" * 7, "```")), 2),
            ("\n".join(("~~~", "code", "~~~", "=" * 7)), 4),
            ("\n".join(("````", "```", "paragraph", "=" * 7)), 4),
            ("\n".join(("~~~", "```", "paragraph", "=" * 7)), 4),
        ):
            with self.subTest(text=text):
                self.assertEqual(style.conflict_markers(text, markdown=True), [(line, "middle")])
        self.assertEqual(style.conflict_markers(
            "\n".join(("```", "code", "```", "A heading", "=" * 7)), markdown=True), [])
        self.assertEqual(style.conflict_markers("```not`a fence\n" + "=" * 7,
                                               markdown=True), [])

    def test_lines_are_counted_by_newlines(self):
        text = "Text with a Unicode separator \u2028 here.\r\n" + "|" * 7 + "\r\n"
        self.assertEqual(style.conflict_markers(text, markdown=True), [(2, "base")])

    def test_raw_files_and_binary_detection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            marker = ("|" * 7 + " base\n").encode()
            for name, data in {
                "notes.md": b"<!--\n" + marker + b"-->\n",
                "image.bin": marker,  # The bytes decide, not the extension.
                "nul.txt": marker + b"\0",
                "non-utf8.txt": marker + b"\xff",
                "heading.MD": b"Heading\n" + ("=" * 7).encode(),
            }.items():
                (root / name).write_bytes(data)
            with patch.object(style, "ROOT", root), patch.object(style, "failures", []):
                style.check_conflict_markers()
                self.assertEqual(sorted(style.failures), [
                    ("S23", "image.bin", 1, "base merge-conflict marker"),
                    ("S23", "notes.md", 2, "base merge-conflict marker"),
                ])

    def test_copy_walk_omits_build_and_cache_directories(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "source.txt").write_text("text")
            for folder in (".lake", "model/.lake", "build", "dist", "_build",
                           "__pycache__", ".pytest_cache", ".mypy_cache", ".ruff_cache",
                           ".tox", ".venv", "venv", "node_modules"):
                path = root / folder
                path.mkdir(parents=True, exist_ok=True)
                (path / "ignored.txt").write_text("<" * 7)
            self.assertEqual(list(style.repository_files(root)), [root / "source.txt"])

    def test_git_list_is_nul_delimited_and_unpruned(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            names = ["tracked.txt", "line\nbreak.txt", "build/tracked.txt"]
            for name in names + ["untracked.txt"]:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("text")
            listing = SimpleNamespace(stdout=("\0".join(names) + "\0").encode())
            with patch.object(Path, "exists", return_value=True), \
                    patch.object(style.subprocess, "run", return_value=listing) as run:
                self.assertEqual(list(style.repository_files(root)), [root / name for name in names])
                run.assert_called_once_with(["git", "ls-files", "-z"], cwd=root,
                                            capture_output=True, check=True)

    def test_no_git_executable_in_a_checkout_stops_the_scan(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "source.txt").write_text("text")
            with patch.object(Path, "exists", return_value=True), \
                    patch.object(style.subprocess, "run", side_effect=FileNotFoundError):
                with self.assertRaises(FileNotFoundError):
                    list(style.repository_files(root))

    def test_git_failure_is_not_an_empty_scan(self):
        with patch.object(Path, "exists", return_value=True), \
                patch.object(style.subprocess, "run",
                             side_effect=style.subprocess.CalledProcessError(128, "git")):
            with self.assertRaises(style.subprocess.CalledProcessError):
                list(style.repository_files(style.ROOT))

    def test_walk_error_names_the_unread_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            blocked = root / "docs" / "briefs"
            blocked.mkdir(parents=True)
            (blocked / "marker.md").write_text("|" * 7)
            scandir = os.scandir

            def unreadable(path):
                if Path(path) == blocked:
                    raise PermissionError(13, "Permission denied", str(path))
                return scandir(path)

            with patch.object(style, "ROOT", root), \
                    patch.object(style.os, "scandir", side_effect=unreadable):
                with self.assertRaisesRegex(OSError, str(blocked)):
                    style.check_conflict_markers()

    def test_symlinks_are_not_scanned(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "copy"
            root.mkdir()
            outside = Path(tmp) / "outside"
            outside.mkdir()
            (outside / "marker.md").write_text("|" * 7)
            links = [root / "file.md", root / "folder", root / "missing.md"]
            for link, target in zip(links, (outside / "marker.md", outside,
                                           outside / "missing.md")):
                link.symlink_to(target)
            (root / "ordinary.md").write_text("|" * 7)
            for tracked in (False, True):
                with self.subTest(tracked=tracked), ExitStack() as stack:
                    stack.enter_context(patch.object(style, "ROOT", root))
                    stack.enter_context(patch.object(style, "failures", []))
                    if tracked:
                        stack.enter_context(patch.object(style, "repository_files",
                            return_value=links + [root / "ordinary.md"]))
                    style.check_conflict_markers()
                    self.assertEqual(style.failures,
                        [("S23", "ordinary.md", 1, "base merge-conflict marker")])

    def test_marker_copy_does_not_dereference_symlinks(self):
        with tempfile.TemporaryDirectory() as tmp:
            source, copy = Path(tmp) / "source", Path(tmp) / "copy"
            source.mkdir()
            copy.mkdir()
            outside = Path(tmp) / "outside"
            outside.write_text("|" * 7)
            (source / "link.md").symlink_to(outside)
            (source / "missing.md").symlink_to(Path(tmp) / "missing")
            (source / "ordinary.md").write_text("A paragraph.")
            with patch.object(plants, "ROOT", source):
                plants.copy_marker_files(copy, ["link.md", "missing.md", "ordinary.md"])
            self.assertEqual((copy / "ordinary.md").read_text(), "A paragraph.")
            for name in ("link.md", "missing.md"):
                path = copy / name
                self.assertTrue(path.is_symlink() or not path.exists())


class TrackedFiles(unittest.TestCase):
    """S12 has no filesystem fallback, and importing the check needs no Git."""

    def test_git_index_ignores_untracked_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Bogus.missing").write_text("untracked")
            listing = SimpleNamespace(returncode=0, stdout="docs/kept.md\0", stderr="")
            with patch.object(style, "ROOT", root), \
                    patch.object(style.subprocess, "run", return_value=listing) as run:
                self.assertEqual(style.tracked_file_index(),
                    (frozenset({"docs/kept.md"}), frozenset({"kept.md"})))
                run.assert_called_once_with(["git", "ls-files", "-z"], cwd=root,
                                            capture_output=True, text=True)

    def test_git_failure_without_metadata_still_raises(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Bogus.missing").write_text("untracked")
            listing = SimpleNamespace(returncode=128, stdout="", stderr="not a git repository")
            with patch.object(style, "ROOT", root), \
                    patch.object(style.subprocess, "run", return_value=listing):
                with self.assertRaisesRegex(RuntimeError, "could not list tracked files"):
                    style.tracked_file_index()

    def test_import_does_not_build_the_git_index(self):
        with patch.object(style.subprocess, "run", side_effect=FileNotFoundError) as run:
            runpy.run_path(str(style.SCRIPT), run_name="style_import_probe")
            run.assert_not_called()

    def test_report_classification_cannot_use_the_fallback_walk(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Bogus.missing").write_text("untracked")
            named = style.NamedText(root / "report.md", "`Bogus.missing`",
                                   style.every_book_opens())
            occurrence, = style.lean_name_occurrences(named.text, all_uses=True)
            listing = SimpleNamespace(returncode=128, stdout="", stderr="not a git repository")
            with patch.object(style, "ROOT", root), \
                    patch.object(style, "TRACKED_FILE_INDEX", None), \
                    patch.object(style.subprocess, "run", return_value=listing):
                with self.assertRaisesRegex(RuntimeError, "could not list tracked files"):
                    style.report_non_declaration(named, occurrence, (set(), set()))
                self.assertIsNone(style.TRACKED_FILE_INDEX)


class Acceptance(unittest.TestCase):
    """The acceptance case: how check_acceptance.py sorts the style check's findings."""

    def test_review_record_findings_are_style(self):
        """A record's finding is its proposition's P9, whatever its rule; others as before"""
        import check_acceptance as acceptance
        out = "\n".join([
            "  ✗ S8 review/I/05.toml:7: a curly quotation mark",
            "  ✗ S9 review/I/06.toml:3: a styled letter",
            "  ✗ S8 mishnah/I/07.md:2: a curly quotation mark",
            "  ✗ S13 figures/I/08.svg: a letter not Heath's",
            "  ✗ S12 mishnah/I/09.md:4: an unknown name",
        ])
        with ExitStack() as stack:
            stack.enter_context(patch.object(acceptance, "failures", {}))
            stack.enter_context(patch.object(acceptance, "run", return_value=SimpleNamespace(
                returncode=1, stdout=out, stderr="")))
            acceptance.check_style_rules()
            self.assertEqual(sorted(acceptance.failures),
                             [("I.5", "P9"), ("I.6", "P9"), ("I.7", "P7"), ("I.8", "P8"),
                              ("I.9", "P9")])


if __name__ == "__main__":
    unittest.main(verbosity=2)
