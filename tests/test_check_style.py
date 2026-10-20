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
* the clearance cases: S26 finds a stroke through a letter, or nearer it than 2 less half
  its width (given as an attribute or inherited), and not one clear of it;
  reads a stroke of none as no stroke and a dashed one whole; closes a path's stroke only
  where a Z closes it, a polygon's always and a polyline's never; finds a circle or an
  ellipse through a letter and not one round it, a dot beside it, a dot or a short stroke
  wholly within it, and each of the canvas's four edges; leaves out a circle of no radius,
  a rect of no width and a line of no length with butt caps, and follows a rect's rounded
  corners for the admitted radius spellings; follows a transform, of a stroke or of the
  letter, taking a width and a radius at the most it stretches them; measures a letter
  upright or italic, and at its size, as its figure sets it, and places it by its anchor
  and the whole label's advance; reads admitted decimal widths alike, mitre joins with
  inherited stroke-linejoin and the default limit of 4, and round caps on single-point
  closed subpaths. Offsets, explicit mitre limits and square caps require refusal.
  Both figure entry points require its findings.
  And it finds a letter drawn twice, or twice in one of
  several figures side by side, or across the cut between them, and reads A and A′ as two
  letters; and it names a line dashed by itself or by its group as a dashed line.
* the input cases: both complete figure checks refuse elements, attributes, numbers,
  transforms, keywords and path commands outside main's SVG language before measuring;
  cases using CSS, scale transforms, units, exponents or other excluded features require
  their exact refusal, separately from admitted geometry cases. Point labels require an
  effective supported Georgia declaration; effective
  strokes and bold weights, unmeasured label characters and incomplete ellipse radii fail.
  Numeric inputs and cubic subdivision
  are bounded; non-finite geometry and decoder failures report the figure and leave
  subsequent figures checked. Cubic subdivision includes its chord error, and malformed
  lists take linear time;
* the scope cases (#66): which texts of a review record the rules read, and on which
  lines; the docstring render.py shows, found again in its file; S12's reading of a
  `name : type`; S22's reading of letters in backticks, one code span at a time; and the
  reach of 19 October, whose findings in a file of REACH_PENDING are reported only for the
  rules the file is listed for, while every other finding in that file still fails, and
  whose rules are reported as done one by one, as each is left with no finding;
* the acceptance case: check_acceptance.py sorts a style finding in a review record to
  its proposition's P9, the item for the record's notes, and every other as before.

CI's `check` job runs this file just before check_style.py, and scripts/safe_push.py runs
it in the same place (docs/WORKFLOW.md, section 8), so a case read wrongly stops the
checks before the style check's findings are read. When a rule is found reading a phrase,
TeX or a letter wrongly, its fix comes with a case here that the old rule fails (WORKFLOW,
section 8, "A guard defect gets a regression"). Python 3.11 or later; standard library.
"""

from __future__ import annotations

import os
import subprocess
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
# The clearance cases: strokes and dots beside a letter, read as S26 reads a figure.
# (S26 is new: Argon's second review of the book-III release found seven letters of
# Euclid's figures crossed by strokes, and no rule then measured how near they came. A
# first review of S26 found it took a stroke's width at a transform's mean stretch, read a
# rect's rounded corners as square, drew a circle of no radius, placed an anchored label
# with a prime by its capital alone, and counted a letter drawn twice in one of several
# figures side by side as once in each; a second found a radius spelled 5e1 read as none,
# and a line of no length with butt caps read as drawn. Their admitted geometry or exact
# allow-list refusal has a case below. An
# independent review then found no case for an ellipse, a polyline, a dot or a stroke
# wholly within a letter, the canvas's right, top and foot, a letter's size or transform,
# or a prime, so that S26 could lose any of them and every case still pass; those cases
# are below too.)

LINE = '<line x1="100" y1="{y}" x2="200" y2="{y}" stroke="#3b2f2f" stroke-width="1.6"/>'
UPRIGHT_STROKE = '<line x1="{x}" y1="90" x2="{x}" y2="104" stroke="#3b2f2f" stroke-width="1.6"/>'
CLEAR_CASES = [   # (what is drawn beside a letter at (150, 100), at 17; the letter, its
                  # font-style and text-anchor; a finding?)
    (LINE.format(y=90), "A", "italic", "start", True),       # through the letter
    (LINE.format(y=110), "A", "italic", "start", False),     # 9 below its baseline
    (LINE.format(y=101.5), "A", "italic", "start", True),    # 1.5 below it: 0.7, less the width
    (LINE.format(y=101.5), "A", "normal", "start", True),
    (LINE.format(y=102.5), "A", "italic", "start", True),    # 2.5 below it: 1.7
    (LINE.format(y=103.5), "A", "italic", "start", False),   # 3.5 below it: 2.7
    ('<g stroke="#3b2f2f" stroke-width="4"><line x1="100" y1="103.5" x2="200" y2="103.5"/>'
     '</g>', "A", "italic", "start", True),                  # a width inherited: 1.5
    ('<line x1="100" y1="90" x2="200" y2="90" stroke="none"/>', "A", "italic", "start", False),
    ('<line x1="100" y1="90" x2="200" y2="90" stroke="#3b2f2f" stroke-dasharray="2 5"/>',
     "A", "italic", "start", True),
    ('<path d="M110,94 V150 H200 V94" fill="none" stroke="#3b2f2f"/>',
     "A", "italic", "start", False),
    ('<path d="M110,94 V150 H200 V94 Z" fill="none" stroke="#3b2f2f"/>',
     "A", "italic", "start", True),
    ('<circle cx="155" cy="94" r="30" fill="none" stroke="#8c7b62"/>',
     "A", "italic", "start", False),
    ('<circle cx="155" cy="94" r="6" fill="none" stroke="#8c7b62"/>',
     "A", "italic", "start", True),
    ('<ellipse cx="155" cy="94" rx="20" ry="4" fill="none" stroke="#8c7b62"/>',
     "A", "italic", "start", True),                          # an ellipse through it
    ('<ellipse cx="155" cy="94" rx="40" ry="30" fill="none" stroke="#8c7b62"/>',
     "A", "italic", "start", False),                         # and one round it
    ('<polyline points="140,94 170,94 170,140" fill="none" stroke="#3b2f2f"/>',
     "A", "italic", "start", True),                          # a polyline through it
    ('<polyline points="110,94 110,150 200,150 200,94" fill="none" stroke="#3b2f2f"/>',
     "A", "italic", "start", False),                         # open: no side along 94
    ('<polygon points="110,94 110,150 200,150 200,94" fill="none" stroke="#3b2f2f"/>',
     "A", "italic", "start", True),                          # closed: a side along 94
    # Wholly within an upright H, 4 or more from its hull's sides: a dot, a short stroke.
    ('<circle cx="157" cy="94" r="1" fill="#3b2f2f"/>', "H", "normal", "start", True),
    ('<line x1="155" y1="93" x2="158" y2="93" stroke="#3b2f2f" stroke-width="0.5"/>',
     "H", "normal", "start", True),
    ('<circle cx="155" cy="94" r="0" fill="none" stroke="#8c7b62"/>',
     "A", "italic", "start", False),                         # no radius: SVG draws nothing
    ('<circle cx="155" cy="94" r="0" fill="none" stroke="#8c7b62" stroke-linecap="round"/>',
     "A", "italic", "start", False),                         # whatever its caps
    ('<rect x="155" y="80" width="0" height="30" fill="none" stroke="#3b2f2f"/>',
     "A", "italic", "start", False),                         # no width: SVG draws nothing
    ('<rect x="150" y="100" width="100" height="100" fill="none" stroke="#3b2f2f"/>',
     "A", "italic", "start", True),                          # its corner at the letter
    ('<rect x="150" y="100" width="100" height="100" rx="50" fill="none" stroke="#3b2f2f"/>',
     "A", "italic", "start", False),                         # a circle, 12.9 clear
    ('<line x1="155" y1="94" x2="155" y2="94" stroke="#3b2f2f"/>',
     "A", "italic", "start", False),                         # no length, butt caps: nothing
    ('<line x1="155" y1="94" x2="155" y2="94" stroke="#3b2f2f" stroke-linecap="round"/>',
     "A", "italic", "start", True),                          # no length, round caps: a dot
    ('<circle cx="156" cy="104" r="2.6" fill="#3b2f2f"/>', "A", "italic", "start", True),
    ('<circle cx="156" cy="108" r="2.6" fill="#3b2f2f"/>', "A", "italic", "start", False),
    (LINE.format(y=114), "A", "italic", "start", False),
    ('<g transform="translate(0,-20)">' + LINE.format(y=114) + '</g>',
     "A", "italic", "start", True),
    # An E's top right corner stands 1.7 further right italic than upright.
    ('<line x1="163.5" y1="84" x2="163.5" y2="90" stroke="#3b2f2f" stroke-width="1.6"/>',
     "E", "italic", "start", True),
    ('<line x1="163.5" y1="84" x2="163.5" y2="90" stroke="#3b2f2f" stroke-width="1.6"/>',
     "E", "normal", "start", False),
    # Anchored at its middle or its end, the letter stands left of x; a prime after it
    # moves it further, by the prime's advance, 5.5 at 17.
    (UPRIGHT_STROKE.format(x=145), "A", "italic", "middle", True),
    (UPRIGHT_STROKE.format(x=145), "A", "italic", "start", False),
    (UPRIGHT_STROKE.format(x=135), "A", "italic", "end", True),
    (UPRIGHT_STROKE.format(x=135), "A", "italic", "start", False),
    (UPRIGHT_STROKE.format(x=132), "A′", "italic", "end", True),
    (UPRIGHT_STROKE.format(x=132), "A", "italic", "end", False),
]
CLEAR_REFUSAL_CASES = [   # (excluded drawing, element, attribute, value)
    ('<line x1="100" y1="103.5" x2="200" y2="103.5" '
     'style="stroke:#3b2f2f;stroke-width:4"/>',
     "line", "style", "stroke:#3b2f2f;stroke-width:4"),
    ('<rect x="150" y="100" width="100" height="100" rx="5e1" fill="none" '
     'stroke="#3b2f2f"/>', "rect", "rx", "5e1"),
    ('<g transform="scale(1,4)"><line x1="100" y1="26" x2="200" y2="26" '
     'stroke="#3b2f2f" stroke-width="1.6"/></g>', "g", "transform", "scale(1,4)"),
    ('<g transform="scale(1,4)"><circle cx="156" cy="26.25" r="1" '
     'fill="#3b2f2f"/></g>', "g", "transform", "scale(1,4)"),
]
EDGE_CASES = [   # (a letter A's x and y; a finding?)
    (1, 100, True),         # by the left edge
    (390, 100, True),       # by the right: it ends at 400.9
    (150, 13, True),        # by the top: its apex at 1.1
    (150, 299, True),       # by the foot: 1 above it
    (150, 100, False),
]
TWICE_CASES = [   # (the x of each letter A, at y 100; the cuts between figures side by
                  # side; a finding?)
    ((150,), (), False),
    ((60, 180), (), True),
    ((60, 300), (200,), False),         # once in each of two figures
    ((60, 120, 300), (200,), True),     # twice in the first
    ((60,), (64,), True),               # across the cut
]


def s26_findings(drawn: str, letters: str, cuts: tuple[float, ...] = ()) -> list[str]:
    """S26's findings on a parchment canvas with `drawn` and `letters` on it."""
    root = ET.fromstring(
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 300" font-family="Georgia">'
        f'<rect width="400" height="300" fill="#fbf7ee"/>{drawn}{letters}</svg>')
    before = len(style.failures)
    style.one_letter_one_point(style.ROOT / "figures" / "case.svg", root, cuts)
    found = [msg for rule, _, _, msg in style.failures[before:] if rule == "S26"]
    del style.failures[before:]
    return found


def letter(s: str, x: float = 150, y: float = 100, font_style: str = "italic",
           anchor: str = "start", size: float = 17) -> str:
    return (f'<text x="{x}" y="{y}" font-size="{size:g}" font-style="{font_style}" '
            f'text-anchor="{anchor}">{s}</text>')


def figure_fixture(idea: bool):
    """A fixed canvas, three labels and a short stroke for the complete figure checks."""
    ink, size = ("#222222", 14) if idea else ("#3b2f2f", 17)
    title = "I.1 at a glance" if idea else "Euclid I.1: three labels"
    desc = "<desc>A short stroke [black].</desc>" if idea else ""
    cx, cy = (200, 52) if idea else (194, 54)
    ex, ey = (363, 155.6) if idea else (353, 156)
    anchor = "middle" if idea else "start"
    return ET.fromstring(
        '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 300" font-family="Georgia">'
        f'<title>{title}</title>{desc}'
        '<rect width="400" height="300" rx="10" fill="#fbf7ee"/>'
        f'<line x1="145" y1="150" x2="165" y2="150" stroke="{ink}" stroke-width="1.6"/>'
        f'<g fill="{ink}">'
        + letter("A", x=132, y=172, size=size, anchor=anchor)
        + letter("C", x=cx, y=cy, size=size, anchor=anchor)
        + letter("E", x=ex, y=ey, size=size, anchor=anchor)
        + '</g></svg>')


def figure_findings(root, idea: bool):
    """Both complete checks, with a fixed figure and its fixed set of Heath's letters."""
    path = style.ROOT / "figures" / "I" / ("01-idea.svg" if idea else "01.svg")
    with patch.object(style, "svg_root", return_value=root), \
            patch.object(style, "drawn_letters", return_value={"A", "C", "E"}), \
            patch.object(style, "heath_letters", return_value={"A", "C", "E"}), \
            patch.object(style, "failures", []), \
            patch.object(style, "reports", defaultdict(list)):
        if idea:
            style.check_idea(path, "I.1", True)
        else:
            style.check_euclid(path, "I.1")
        return list(style.failures)


def figure_run(first, idea: bool, reference: bytes | None = None):
    """Parse a bad figure, then a distinct collision, through the production file loop.
    `reference` instead puts bad bytes in the Euclid figure read by an idea's S20."""
    with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
        root = Path(tmp)
        folder = root / "figures" / "I"
        folder.mkdir(parents=True)
        suffix = "-idea.svg" if idea else ".svg"
        path = folder / ("01" + suffix)
        raw = first if isinstance(first, bytes) else ET.tostring(first)
        path.write_bytes(raw)
        if idea:
            (folder / "01.svg").write_bytes(
                reference if reference is not None else ET.tostring(figure_fixture(False)))
            (folder / "02.svg").write_bytes(ET.tostring(figure_fixture(False)))
        second = figure_fixture(idea)
        e = next(el for el in second.iter() if style.text_of(el) == "E")
        e.set("x", "0")
        e.set("text-anchor", "end")
        (folder / ("02" + suffix)).write_bytes(ET.tostring(second))
        stack.enter_context(patch.object(style, "ROOT", root))
        stack.enter_context(patch.object(style, "books_with_pages", return_value=["I"]))
        stack.enter_context(patch.object(style, "heath_letters", return_value={"A", "C", "E"}))
        stack.enter_context(patch.object(style, "failures", []))
        stack.enter_context(patch.object(style, "reports", defaultdict(list)))
        stack.enter_context(patch.object(style, "italic_figures",
                                        defaultdict(lambda: defaultdict(list))))
        style.check_figures(True)
        return list(style.failures)


PLACE_CASES = [   # (what is drawn; the letters, as markup; a finding?)
    # At 17 an A's apex stands 1.3 from a line at 86, its width taken off; at 14, 3.4.
    (LINE.format(y=86), letter("A"), True),
    (LINE.format(y=86), letter("A", size=14), False),
    # A transform on the letter moves it: up 20, onto the line at 90.
    (LINE.format(y=90), '<g transform="translate(0,-20)">' + letter("A", y=120) + "</g>",
     True),
    (LINE.format(y=90), letter("A", y=120), False),
    # A and A′ name two points, each drawn once; A′ drawn twice is a repeat.
    ("", letter("A", x=60) + letter("A′", x=300), False),
    ("", letter("A′", x=60) + letter("A′", x=300), True),
]

KIND_CASES = [   # (a line drawn through a letter A at (150, 100); what S26 calls it)
    ('<line x1="100" y1="90" x2="200" y2="90" stroke="#3b2f2f" stroke-dasharray="2 5"/>',
     "a dashed line"),
    ('<g stroke-dasharray="2 5"><line x1="100" y1="90" x2="200" y2="90" stroke="#3b2f2f"/>'
     '</g>', "a dashed line"),                               # dashed by its group
    ('<line x1="100" y1="90" x2="200" y2="90" stroke="#3b2f2f" stroke-dasharray="none"/>',
     "a line"),                                              # none: drawn solid
]


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


def svg_refusal(kind, attr=None, value=None):
    """The diagnostic expected when a case is outside the declared input language."""
    what = f"<{kind}>" + (f" {attr} {value!r}" if attr is not None else "")
    return f"{what} is outside S26's SVG allow-list"


def pi_refusal(target, data):
    instruction = target + (f" {data}" if data else "")
    return f"processing instruction {instruction!r} is outside S26's SVG allow-list"


DTD_CASES = (
    ('<!DOCTYPE svg [<!ENTITY family "Georgia">]>', '&family;'),
    ('<!DOCTYPE svg [<!ENTITY first "Geor"><!ENTITY family "&first;gia">]>', '&family;'),
    ('<!DOCTYPE svg SYSTEM "x.dtd">', 'Georgia'),
    ('<!DOCTYPE svg PUBLIC "figure" "x.dtd">', 'Georgia'),
    ('<!DOCTYPE svg [<!ENTITY % family "Georgia">]>', 'Georgia'),
    ('<!DOCTYPE svg>', 'Georgia'),
)
DTD_REFUSAL = "DTD or entity declaration is outside S26's SVG allow-list"


def dtd_figure(idea, declaration, family):
    return declaration.encode("ascii") + ET.tostring(figure_fixture(idea)).replace(
        b'font-family="Georgia"', f'font-family="{family}"'.encode("ascii"))


class SvgGate(unittest.TestCase):
    """The closed SVG input language, through both complete figure checks."""

    def assert_refused(self, root, idea, *names):
        found = [f for f in figure_findings(root, idea) if f[0] == "S26"]
        path = "figures/I/01-idea.svg" if idea else "figures/I/01.svg"
        self.assertTrue(found, (idea, names))
        self.assertTrue(all(f[1:3] == (path, 0) for f in found), found)
        for name in names:
            self.assertTrue(any(name in f[3] for f in found), (name, found))

    def assert_continued(self, found, idea, message, first_path=None, rule="S26"):
        suffix = "-idea.svg" if idea else ".svg"
        first_path = first_path or "figures/I/01" + suffix
        self.assertTrue(any(r == rule and p == first_path and message in msg
                            for r, p, _, msg in found), found)
        self.assertTrue(any(r == "S26" and p == "figures/I/02" + suffix
                            and "letter E" in msg and "canvas's edge" in msg
                            for r, p, _, msg in found), found)

    def test_nesting_depth_and_continuation(self):
        """Refuse excessive nesting before recursion, then check the next figure."""
        for idea in (False, True):
            for depth in (17, 1100):
                with self.subTest(idea=idea, depth=depth):
                    # Build bytes directly: ElementTree's serialiser is recursive too.
                    raw = (b'<svg xmlns="http://www.w3.org/2000/svg">'
                           + b"<g>" * depth + b"</g>" * depth + b"</svg>")
                    self.assert_continued(figure_run(raw, idea), idea,
                                          "nesting exceeds 16 levels below the root")

    def test_nesting_depth_boundary(self):
        for idea in (False, True):
            with self.subTest(idea=idea):
                root = figure_fixture(idea)
                parent = root
                for _ in range(16):
                    parent = ET.SubElement(parent, style.SVG + "g")
                self.assertEqual(figure_findings(root, idea), [])
                ET.SubElement(parent, style.SVG + "g")
                self.assertEqual(figure_findings(root, idea), [
                    ("S26", "figures/I/01" + ("-idea.svg" if idea else ".svg"), 0,
                     "SVG nesting exceeds 16 levels below the root")])

    def test_stroked_labels(self):
        for idea in (False, True):
            for placement in ("own", "group", "root"):
                with self.subTest(idea=idea, placement=placement):
                    root = figure_fixture(idea)
                    e = next(el for el in root.iter() if style.text_of(el) == "E")
                    group = next(el for el in root.iter() if e in list(el))
                    e.attrib.update(x="150", y="100", **{"font-size": "17",
                                         "font-style": "normal", "text-anchor": "start"})
                    ink = "#222222" if idea else "#3b2f2f"
                    ET.SubElement(root, "line", {"x1": "145", "y1": "103.5", "x2": "170",
                                  "y2": "103.5", "stroke": ink, "stroke-width": "1.6"})
                    target = {"own": e, "group": group, "root": root}[placement]
                    target.attrib.update(stroke=ink, **{"stroke-width": "1.6"})
                    self.assert_refused(root, idea, "letter E", "stroke")
                    # An explicit reset overrides every ancestor.
                    for el in root.iter():
                        if style.tag(el) == "text":
                            el.set("stroke", "none")
                    self.assertEqual([f for f in figure_findings(root, idea) if f[0] == "S26"], [])

    def test_bold_labels_and_numerals(self):
        for idea in (False, True):
            for placement in ("own", "group", "root"):
                with self.subTest(idea=idea, placement=placement):
                    root = figure_fixture(idea)
                    e = next(el for el in root.iter() if style.text_of(el) == "E")
                    group = next(el for el in root.iter() if e in list(el))
                    e.attrib.update(x="150", y="100", **{"font-size": "17",
                                         "font-style": "normal", "text-anchor": "start"})
                    ET.SubElement(root, "line", {"x1": "163.6", "y1": "80", "x2": "163.6",
                                  "y2": "105", "stroke-width": "1.6",
                                  "stroke": "#222222" if idea else "#3b2f2f"})
                    target = {"own": e, "group": group, "root": root}[placement]
                    target.set("font-weight", "bold")
                    self.assert_refused(root, idea, "letter E", "font-weight")
                    for el in root.iter():
                        if style.tag(el) == "text":
                            el.set("font-weight", "normal")
                    # Main's bold numerical annotations remain allowed, inherited too.
                    for content in ("9", "16", "25"):
                        attrs = {"x": "250", "y": "230"}
                        if placement == "own":
                            attrs["font-weight"] = "bold"
                        ET.SubElement(target if placement != "own" else group, "text", attrs).text = content
                    self.assertEqual([f for f in figure_findings(root, idea) if f[0] == "S26"], [])

    def test_missing_label_font_family(self):
        """A default font cannot borrow Georgia's clearance at either entry point."""
        for idea in (False, True):
            for missing in (("A", "C", "E"), ("E",)):
                with self.subTest(idea=idea, missing=missing):
                    root = figure_fixture(idea)
                    del root.attrib["font-family"]
                    for el in root.iter():
                        if style.tag(el) == "text" and style.text_of(el) not in missing:
                            el.set("font-family", "Georgia")
                    # E clears this stroke by 2.04 in Georgia; a default font can differ.
                    x = "355.33" if idea else "349.85"
                    ET.SubElement(root, "line", {
                        "x1": x, "x2": x, "y1": "138", "y2": "160",
                        "stroke": "#222222" if idea else "#3b2f2f", "stroke-width": "1.6"})
                    path = "figures/I/01" + ("-idea.svg" if idea else ".svg")
                    self.assertEqual(figure_findings(root, idea), [
                        ("S26", path, 0, f"letter {s} has effective font-family None: "
                         "outside S26's SVG allow-list") for s in missing])

    def test_supported_label_font_families(self):
        """Main's three Georgia declarations work on the root, a group or each label."""
        for idea in (False, True):
            for family in ("Georgia", "Georgia, serif", "Georgia, 'Times New Roman', serif"):
                for placement in ("root", "group", "own"):
                    with self.subTest(idea=idea, family=family, placement=placement):
                        root = figure_fixture(idea)
                        del root.attrib["font-family"]
                        labels = [el for el in root.iter() if style.tag(el) == "text"]
                        group = next(el for el in root.iter() if labels[0] in list(el))
                        targets = {"root": [root], "group": [group], "own": labels}[placement]
                        for target in targets:
                            target.set("font-family", family)
                        x = "355.33" if idea else "349.85"
                        ET.SubElement(root, "line", {
                            "x1": x, "x2": x, "y1": "138", "y2": "160",
                            "stroke": "#222222" if idea else "#3b2f2f", "stroke-width": "1.6"})
                        self.assertEqual(figure_findings(root, idea), [])

    def test_unsupported_label_font_families(self):
        for idea in (False, True):
            for family in ("", "serif", "Times New Roman", "Arial, Georgia", "Georgia, sans-serif"):
                for placement in ("root", "group", "own"):
                    with self.subTest(idea=idea, family=family, placement=placement):
                        root = figure_fixture(idea)
                        e = next(el for el in root.iter() if style.text_of(el) == "E")
                        group = next(el for el in root.iter() if e in list(el))
                        target = {"root": root, "group": group, "own": e}[placement]
                        target.set("font-family", family)
                        path = "figures/I/01" + ("-idea.svg" if idea else ".svg")
                        self.assertEqual(figure_findings(root, idea), [
                            ("S26", path, 0, svg_refusal(style.tag(target), "font-family", family))])

    def test_raw_label_content(self):
        for idea in (False, True):
            for char in ("\u00a0", "\u2002", "\u2003", "\u202f", "\u3000", "\u200b", "\u0301"):
                for content in (char + "E", "E" + char, "E" + char + "′"):
                    with self.subTest(idea=idea, content=content):
                        root = figure_fixture(idea)
                        e = next(el for el in root.iter() if style.text_of(el) == "E")
                        e.text = content
                        self.assert_refused(root, idea, "<text>", "unmeasured")
            for content in (" E ", "\tE\t", "\rE\r", "\nE\n", " \t\r\nE \t\r\n"):
                with self.subTest(idea=idea, content=content):
                    root = figure_fixture(idea)
                    next(el for el in root.iter() if style.text_of(el) == "E").text = content
                    self.assertEqual(figure_findings(root, idea), [])

    def test_explicit_ellipse_radii(self):
        for idea in (False, True):
            for missing in ("rx", "ry", "both"):
                for fill in ("none", "#222222" if idea else "#3b2f2f"):
                    with self.subTest(idea=idea, missing=missing, fill=fill):
                        root = figure_fixture(idea)
                        e = next(el for el in root.iter() if style.text_of(el) == "E")
                        e.attrib.update(x="150", y="100", **{"font-size": "17",
                                             "font-style": "normal", "text-anchor": "start"})
                        ellipse = ET.SubElement(root, "ellipse", {"cx": "150", "cy": "100",
                                     "rx": "8", "ry": "8", "fill": fill, "stroke-width": "1.6",
                                     "stroke": "#222222" if idea else "#3b2f2f"})
                        for attr in (("rx", "ry") if missing == "both" else (missing,)):
                            del ellipse.attrib[attr]
                        self.assert_refused(root, idea, "<ellipse>", "rx", "ry")

    def test_numeric_bounds_and_continuation(self):
        for idea in (False, True):
            for big in ("10000.1", "-10000.1", "9" * 308, "0." + "0" * 330 + "1"):
                for attr, value in (("x1", big), ("r", big), ("stroke-width", big),
                                    ("points", f"0 0 {big} 100"),
                                    ("viewBox", f"0 0 {big} 300"),
                                    ("stroke-dasharray", f"1 {big}"),
                                    ("transform", f"translate({big},0)"),
                                    ("d", f"M150 100 C{big} 100 {big} 100 160 100"),
                                    ("d", f"M150 100 A{big} 8 0 0 1 160 100")):
                    with self.subTest(idea=idea, attr=attr, value=value[:40]):
                        root = figure_fixture(idea)
                        shape = ET.SubElement(root, "path", {"fill": "none",
                                              "stroke": "#222222" if idea else "#3b2f2f",
                                              "stroke-width": "1.6"})
                        shape.set(attr, value)
                        self.assert_refused(root, idea, attr, "allow-list")
                        self.assert_continued(figure_run(root, idea), idea, "allow-list")
            root = figure_fixture(idea)
            ET.SubElement(root, "line", {"x1": "-10000", "x2": "10000", "stroke": "none"})
            self.assertEqual(figure_findings(root, idea), [])

    def test_curve_limits_and_continuation(self):
        for idea in (False, True):
            root = figure_fixture(idea)
            ET.SubElement(root, "path", {"d": "M100 100 C100 200 200 200 200 100",
                          "stroke": "#222222" if idea else "#3b2f2f", "fill": "none",
                          "stroke-width": "1.6"})
            # Exhaust the budget on a small curve to exercise the failure path quickly.
            for depth in (0, 1):
                with self.subTest(idea=idea, depth=depth), \
                        patch.object(style, "CURVE_MAX_DEPTH", depth, create=True):
                    self.assert_continued(figure_run(root, idea), idea, "subdivision limit")
            distance = style.point_gap
            for bad in (float("inf"), float("nan")):
                def nonfinite(p, a, b):
                    return bad if p == (100.0, 200.0) else distance(p, a, b)
                with self.subTest(idea=idea, intermediate=bad), \
                        patch.object(style, "point_gap", side_effect=nonfinite):
                    self.assert_continued(figure_run(root, idea), idea, "non-finite")

    def test_arc_arithmetic_and_continuation(self):
        for idea in (False, True):
            for radius in ("0." + "0" * 309 + "1", "0." + "0" * 160 + "1"):
                for fill in ("none", "#222222" if idea else "#3b2f2f"):
                    with self.subTest(idea=idea, radius=radius, fill=fill):
                        root = figure_fixture(idea)
                        ET.SubElement(root, "path", {
                            "d": f"M100 100 A{radius} 1 0 0 1 200 100", "fill": fill,
                            "stroke": "#222222" if idea else "#3b2f2f", "stroke-width": "1.6"})
                        self.assert_continued(figure_run(root, idea), idea, "non-finite")

    def test_tiny_ellipse_fill(self):
        # Squaring these finite ratios used to overflow in S20's fill measurement.
        root = figure_fixture(True)
        ellipse = ET.Element("ellipse", {"cx": "20", "cy": "20", "rx": "0." + "0" * 160 + "1",
                             "ry": "1", "fill": "#222222"})
        root.insert(1, ellipse)
        self.assertEqual(figure_findings(root, True), [])
        ellipse.set("rx", "0." + "0" * 309 + "1")
        self.assert_continued(figure_run(root, True), True, "non-finite")

    def test_encoding_failures_and_continuation(self):
        for idea in (False, True):
            for encoding in ("unknown-encoding", "shift_jis"):
                raw = f'<?xml version="1.0" encoding="{encoding}"?><svg/>'.encode("ascii")
                with self.subTest(idea=idea, encoding=encoding):
                    self.assert_continued(figure_run(raw, idea), idea, "not well-formed SVG",
                                          rule="S14" if idea else "S15")
        # The second parse site reads Euclid's figure while checking an idea's letters.
        for encoding in ("unknown-encoding", "shift_jis"):
            raw = f'<?xml version="1.0" encoding="{encoding}"?><svg/>'.encode("ascii")
            self.assert_continued(figure_run(figure_fixture(True), True, reference=raw), True,
                                  "not well-formed SVG", first_path="figures/I/01.svg", rule="S15")
        # Expat versions differ in which decoder failures they produce.
        parse = ET.parse
        for idea in (False, True):
            def decode_failure(path, *args, **kwargs):
                if Path(path).name == ("01-idea.svg" if idea else "01.svg"):
                    raise UnicodeDecodeError("utf-8", b"\xff", 0, 1, "invalid start byte")
                return parse(path, *args, **kwargs)
            with patch.object(ET, "parse", side_effect=decode_failure):
                self.assert_continued(figure_run(figure_fixture(idea), idea), idea,
                                      "not well-formed SVG", rule="S14" if idea else "S15")

    def test_stylesheet_processing_instructions_and_continuation(self):
        target = "xml-stylesheet"
        data = 'type="text/css" href="data:text/css,line{stroke-width:20}"'
        expected = pi_refusal(target, data)
        for idea in (False, True):
            with self.subTest(idea=idea):
                raw = (f'<?xml version="1.0"?>\n<?{target} {data}?>\n'.encode("ascii")
                       + ET.tostring(figure_fixture(idea)))
                found = figure_run(raw, idea)
                path = "figures/I/01" + ("-idea.svg" if idea else ".svg")
                self.assertEqual([f for f in found if f[1] == path], [("S26", path, 0, expected)])
                self.assert_continued(found, idea, expected)

    def test_dtd_refusal_and_continuation(self):
        for idea in (False, True):
            for declaration, family in DTD_CASES:
                for encoding in ("utf-8", "utf-16"):
                    with self.subTest(idea=idea, declaration=declaration, encoding=encoding):
                        raw = dtd_figure(idea, declaration, family).decode("ascii").encode(encoding)
                        found = figure_run(raw, idea)
                        path = "figures/I/01" + ("-idea.svg" if idea else ".svg")
                        self.assertEqual([f for f in found if f[1] == path],
                                         [("S26", path, 0, DTD_REFUSAL)])
                        self.assert_continued(found, idea, DTD_REFUSAL)

    def test_dtd_in_euclid_reference_is_reported_once_and_continues(self):
        for declaration, family in DTD_CASES:
            with self.subTest(declaration=declaration):
                raw = dtd_figure(False, declaration, family)
                found = figure_run(figure_fixture(True), True, reference=raw)
                path = "figures/I/01.svg"
                self.assertEqual([f for f in found if f[1] == path],
                                 [("S26", path, 0, DTD_REFUSAL)])
                self.assert_continued(found, True, DTD_REFUSAL, first_path=path)

    def test_drawn_letters_refuses_dtd(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "01.svg"
            for declaration, family in DTD_CASES:
                with self.subTest(declaration=declaration):
                    path.write_bytes(dtd_figure(False, declaration, family))
                    self.assertIsNone(style.drawn_letters(path))

    def test_dtd_refusal_precedes_internal_subset(self):
        # Refuse even before any declaration or reference in the subset is read.
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "01.svg"
            path.write_bytes(b"<!DOCTYPE svg [")
            with self.assertRaises(ET.ParseError) as raised:
                style.parse_svg(path)
            self.assertEqual(str(raised.exception), DTD_REFUSAL)

    def test_character_references_keep_the_resolved_value_gate(self):
        for idea in (False, True):
            for family in (b"&#71;eorgia", b"&#x47;eorgia", b"&#83;erif"):
                with self.subTest(idea=idea, family=family):
                    raw = ET.tostring(figure_fixture(idea)).replace(
                        b'font-family="Georgia"', b'font-family="' + family + b'"')
                    raw = raw.replace(b">A<", b">&#65;<")
                    found = figure_run(raw, idea)
                    path = "figures/I/01" + ("-idea.svg" if idea else ".svg")
                    expected = [("S26", path, 0, svg_refusal("svg", "font-family", "Serif"))] \
                        if family == b"&#83;erif" else []
                    self.assertEqual([f for f in found if f[1] == path], expected)

    def test_xml_declarations_and_comments_are_admitted(self):
        for idea in (False, True):
            with self.subTest(idea=idea):
                body = ET.tostring(figure_fixture(idea)).replace(b">", b"><!-- figure -->", 1)
                found = figure_run(b'<?xml version="1.0"?>\n' + body, idea)
                path = "figures/I/01" + ("-idea.svg" if idea else ".svg")
                self.assertFalse([f for f in found if f[1] == path], found)
                next_path = "figures/I/02" + ("-idea.svg" if idea else ".svg")
                self.assertTrue(any(r == "S26" and p == next_path and "canvas's edge" in msg
                                    for r, p, _, msg in found), found)

    def test_malformed_euclid_figure_is_reported_once(self):
        bad_figures = (
            b"<svg>",
            b'<?xml version="1.0" encoding="unknown-encoding"?><svg/>',
        )
        for raw in bad_figures:
            with self.subTest(raw=raw):
                found = figure_run(figure_fixture(True), True, reference=raw)
                first = [f for f in found if f[0] == "S15" and f[1] == "figures/I/01.svg"]
                self.assertEqual(len(first), 1, found)
                self.assertIn("not well-formed SVG", first[0][3])
                self.assert_continued(found, True, "not well-formed SVG",
                                      first_path="figures/I/01.svg", rule="S15")

    def test_checker_errors_are_not_decoder_failures(self):
        for idea in (False, True):
            for error in (LookupError("checker defect"), ValueError("checker defect"),
                          UnicodeDecodeError("utf-8", b"\xff", 0, 1, "checker defect")):
                for function in ("supported_svg", "glyph_hull"):
                    with self.subTest(idea=idea, error=type(error).__name__, function=function), \
                            patch.object(style, function, side_effect=error):
                        with self.assertRaises(type(error)):
                            figure_run(figure_fixture(idea), idea)
            # getroot runs after the parser's exception boundary, too.
            with patch.object(ET, "parse") as parse:
                parse.return_value.getroot.side_effect = ValueError("checker defect")
                with self.assertRaisesRegex(ValueError, "checker defect"):
                    figure_run(figure_fixture(idea), idea)

    def test_nested_svg(self):
        for idea in (False, True):
            root = figure_fixture(idea)
            ET.SubElement(root, "svg", {"viewBox": "0 0 400 300"})
            self.assert_refused(root, idea, "<svg>")

    def test_numeric_ranges(self):
        for idea in (False, True):
            for attr in ("r", "rx", "ry", "width", "height", "font-size", "stroke-width"):
                with self.subTest(idea=idea, attr=attr):
                    root = figure_fixture(idea)
                    ET.SubElement(root, "rect", {attr: "-0.1"})
                    self.assert_refused(root, idea, attr)
            for attr in ("fill-opacity", "stroke-opacity"):
                for value in ("-0.1", "1.1"):
                    with self.subTest(idea=idea, attr=attr, value=value):
                        root = figure_fixture(idea)
                        ET.SubElement(root, "g", {attr: value})
                        self.assert_refused(root, idea, attr)
            for attr, values in (
                    ("viewBox", ("0 0 400", "0 0 400 300 1", "0 0 0 300", "0 0 400 0",
                                 "0 0 -1 300", "0 0 400 -1")),
                    ("points", ("10 20 30",)),
                    ("stroke-dasharray", ("-1 2", "1 -2"))):
                for value in values:
                    with self.subTest(idea=idea, attr=attr, value=value):
                        root = figure_fixture(idea)
                        root.set(attr, value)
                        self.assert_refused(root, idea, attr)

    def test_exact_keywords_and_whitespace(self):
        for idea in (False, True):
            for attr, word in (("font-weight", "normal"), ("font-style", "normal"),
                               ("text-anchor", "start"), ("font-family", "Georgia"),
                               ("stroke-linecap", "butt"), ("stroke-linejoin", "miter"),
                               ("fill", "none"), ("stroke", "none"), ("stroke-dasharray", "none")):
                for value in (word.upper(), " " + word, word + " ", "\t" + word,
                              word + "\n", "\u00a0" + word):
                    with self.subTest(idea=idea, attr=attr, value=value):
                        root = figure_fixture(idea)
                        ET.SubElement(root, "g", {attr: value})
                        self.assert_refused(root, idea, attr)
            for space in ("\u00a0", "\u2003", "\v", "\f"):
                for attr, value in (("x1", space + "10"), ("x1", "10" + space),
                                    ("points", f"0{space}0"), ("viewBox", f"0 0{space}400 300"),
                                    ("stroke-dasharray", f"1{space}2"),
                                    ("transform", f"translate(0{space}0)"),
                                    ("d", f"M100{space}100 L200 100")):
                    with self.subTest(idea=idea, attr=attr, value=value):
                        root = figure_fixture(idea)
                        ET.SubElement(root, "g", {attr: value})
                        self.assert_refused(root, idea, attr)
            root = figure_fixture(idea)
            ET.SubElement(root, "line", {"x1": " \t\r\n10 \t\r\n",
                          "stroke-dasharray": "1,\t2\r\n3 4"})
            self.assertEqual(figure_findings(root, idea), [])

    def test_arc_flags_and_close_arguments(self):
        for idea in (False, True):
            paths = ["M100 100 Z 200 100", "M100 100 Z 0",
                     "M100 100 A10 -10 0 0 0 120 100"]
            for flag in ("2", "-1", "0.0", "1.0", "+1", "01"):
                paths += [f"M100 100 A10 10 0 {flag} 0 120 100",
                          f"M100 100 A10 10 0 0 {flag} 120 100"]
            for value in paths:
                with self.subTest(idea=idea, d=value):
                    root = figure_fixture(idea)
                    ET.SubElement(root, "path", {"d": value})
                    self.assert_refused(root, idea, "<path>", "d")

    def test_supported_spellings_and_continuation(self):
        for idea in (False, True):
            root = figure_fixture(idea)
            for transform in ("translate(+0,-0)", "translate(0 0)",
                              "rotate(0 150 100)", "rotate(0,150,100)"):
                group = ET.SubElement(root, "g", {"transform": transform, "font-style": "normal",
                                      "font-weight": "normal", "text-anchor": "start",
                                      "stroke-linecap": "butt", "stroke-linejoin": "miter"})
                ET.SubElement(group, "polyline", {"points": "10,20 30,40", "stroke-dasharray": "none"})
                ET.SubElement(group, "line", {"x1": "+10.00", "y1": "-0", "stroke-width": "0",
                              "stroke-dasharray": "1, 2   3,4"})
            self.assertEqual([f for f in figure_findings(root, idea) if f[0] == "S26"], [])
            ET.SubElement(root, "image")
            ET.SubElement(root, "g", {"style": "fill:none", "unknown": "bad"})
            self.assert_refused(root, idea, "<image>", "style", "unknown")
            self.assertEqual(figure_findings(figure_fixture(idea), idea), [])

    def test_elements_and_attributes(self):
        for idea in (False, True):
            for name in ("style", "use", "image", "foreignObject", "animate", "tspan",
                         "defs", "marker", "unknown", "{urn:other}line"):
                with self.subTest(idea=idea, element=name):
                    root = figure_fixture(idea)
                    ET.SubElement(root, name)
                    self.assert_refused(root, idea, f"<{name}>")
            for name in ("style", "class", "id", "onclick", "filter", "clip-path",
                         "mask", "vector-effect", "dx", "dy", "fill-rule",
                         "stroke-miterlimit", "unknown", "{urn:other}x"):
                with self.subTest(idea=idea, attribute=name):
                    root = figure_fixture(idea)
                    ET.SubElement(root, "g", {name: "none"})
                    self.assert_refused(root, idea, "<g>", name)

    def test_plain_decimals_and_lists(self):
        for idea in (False, True):
            for attr in ("x1", "stroke-width", "fill-opacity", "stroke-opacity", "font-size"):
                for value in ("0 px", "1px", "1e2", ".5", "1.", "1 2", "1,2",
                              "--1", "+", "", "NaN", "inf", "١", "9" * 400):
                    with self.subTest(idea=idea, attr=attr, value=value[:30]):
                        root = figure_fixture(idea)
                        ET.SubElement(root, "line", {attr: value})
                        self.assert_refused(root, idea, "<line>", attr)
            for attr in ("points", "viewBox", "stroke-dasharray"):
                for value in ("0 0 400x 300", "0 0 4e2 300", "0 0 .4 300", "0,,0",
                              ",0 0", "0 0,", "0 0px", "0;0", "0 0 inherit", ""):
                    with self.subTest(idea=idea, attr=attr, value=value):
                        root = figure_fixture(idea)
                        root.set(attr, value)
                        self.assert_refused(root, idea, "<svg>", attr)

    def test_transforms(self):
        for idea in (False, True):
            for value in ("translate(-80px,0)", "translate(-80,0,0)",
                          "translate(-80,0)junk", "translate(-80,0) rotate(0)",
                          "translate(-80)", "translate(-80,,0)", "translate(-8e1,0)",
                          "translate(-80 0", "translate(-80,0))", "translate(-80;0)",
                          "translate()", "rotate(0)", "rotate(0 1)", "rotate(0 1 2 3)",
                          "scale(1)", "scale(1,2)", "matrix(1 0 0 1 0 0)", "skewX(0)", ""):
                with self.subTest(idea=idea, transform=value):
                    root = figure_fixture(idea)
                    ET.SubElement(root, "line", {"x1": "352", "y1": "150.8", "x2": "364",
                                  "y2": "150.8", "stroke": "#222222" if idea else "#3b2f2f",
                                  "stroke-width": "1.6", "transform": value})
                    self.assert_refused(root, idea, "<line>", "transform")

    def test_css_coordinates_and_paths(self):
        for idea in (False, True):
            for kind, attrs in (
                    ("line", {"x1": "352", "y1": "150.8", "x2": "364", "y2": "150.8",
                              "style": "y1:210px;y2:210px"}),
                    ("path", {"d": "M352 150.8 L364 150.8",
                              "style": "d:path('M352 210 L364 210')"}),
                    ("text", {"style": "y:220px"})):
                with self.subTest(idea=idea, kind=kind):
                    root = figure_fixture(idea)
                    if kind == "text":
                        el = next(e for e in root.iter() if style.text_of(e) == "E")
                    else:
                        el = ET.SubElement(root, kind, {
                            "stroke": "#222222" if idea else "#3b2f2f", "stroke-width": "1.6"})
                    el.attrib.update(attrs)
                    self.assert_refused(root, idea, f"<{kind}>", "style")

    def test_whitespace_width(self):
        for idea in (False, True):
            for placement in ("attribute", "style", "inherited"):
                with self.subTest(idea=idea, placement=placement):
                    root = figure_fixture(idea)
                    parent = ET.SubElement(root, "g") if placement == "inherited" else root
                    line = ET.SubElement(parent, "line", {
                        "x1": "352", "y1": "150.8", "x2": "364", "y2": "150.8",
                        "stroke": "#222222" if idea else "#3b2f2f"})
                    target = parent if placement == "inherited" else line
                    attr = "style" if placement == "style" else "stroke-width"
                    target.set(attr, "stroke-width:0 px" if placement == "style" else "0 px")
                    self.assert_refused(root, idea, f"<{style.tag(target)}>", attr)

    def test_keywords(self):
        for idea in (False, True):
            for attr in ("text-anchor", "stroke-linecap", "stroke-linejoin", "font-style",
                         "font-weight", "font-family", "fill", "stroke", "stroke-dasharray"):
                for value in ("inherit", "initial", "unset", "revert", "revert-layer", "unknown"):
                    with self.subTest(idea=idea, attr=attr, value=value):
                        root = figure_fixture(idea)
                        ET.SubElement(root, "g", {attr: value})
                        self.assert_refused(root, idea, "<g>", attr)
            for attr, value in (("stroke-linecap", "square"), ("stroke-linejoin", "bevel"),
                                ("font-style", "oblique"), ("font-weight", "700")):
                with self.subTest(idea=idea, attr=attr, value=value):
                    root = figure_fixture(idea)
                    ET.SubElement(root, "g", {attr: value})
                    self.assert_refused(root, idea, attr)

    def test_explicit_inheritance(self):
        for idea in (False, True):
            for attr, value, shape in (
                    ("text-anchor", "middle", '<line x1="145" y1="85" x2="145" y2="105"/>'),
                    ("stroke-linejoin", "miter", '<polyline points="130,160 155,103 180,160"/>')):
                with self.subTest(idea=idea, attribute=attr):
                    root = figure_fixture(idea)
                    group = ET.SubElement(root, "g", {attr: value, "stroke-width": "1.6",
                                          "stroke": "#222222" if idea else "#3b2f2f"})
                    drawn = ET.fromstring(shape)
                    group.append(drawn)
                    e = next(el for el in root.iter() if style.tag(el) == "text"
                             and style.text_of(el) == "E")
                    e.attrib.update(x="150", y="100", **{"font-size": "17", "font-style": "normal",
                                                        "text-anchor": "start"})
                    if attr == "text-anchor":
                        next(el for el in root.iter() if e in list(el)).remove(e)
                        group.append(e)
                    target = e if attr == "text-anchor" else drawn
                    target.set(attr, "inherit")
                    self.assert_refused(root, idea, attr)
                    target.set(attr, value)
                    found = [f[3] for f in figure_findings(root, idea) if f[0] == "S26"]
                    self.assertTrue(any("letter E" in f for f in found), found)

    def test_paths(self):
        for idea in (False, True):
            for value in ("M100 100 Q150 50 200 100", "M100 100 S150 50 200 100",
                          "M100 100 T200 100", "m100 100 l100 0", "M100 100 a1 1 0 0 0 1 1",
                          "M100 100 R200 100", "M100 100 L200", "L100 100", "M100px 100",
                          "M1e2 100 L200 100", "M100 100 A10 10 0 2 0 120 100",
                          "M100 100 A-10 10 0 0 0 120 100", "M100 100 L200 100 junk"):
                with self.subTest(idea=idea, d=value):
                    root = figure_fixture(idea)
                    ET.SubElement(root, "path", {"d": value})
                    self.assert_refused(root, idea, "<path>", "d")

    def test_bezier_clearance(self):
        # The quadratic in the review, and its exact cubic degree elevation.
        paths = ("M100,182.5507421875 Q150,27.8632421875 200,173.1757421875",
                 "M100,182.5507421875 C133.33333333333334,79.4257421875 "
                 "166.66666666666666,76.3007421875 200,173.1757421875",
                 # Its minimum at t = 0.5173 falls between subdivision points;
                 # exact clearance 1.99999 requires subtracting the chord error.
                 "M100,183.079777 C133.33333333333334,79.619777 "
                 "166.66666666666666,76.159777 200,172.699777")
        for idea in (False, True):
            for d in paths:
                with self.subTest(idea=idea, d=d):
                    root = figure_fixture(idea)
                    ET.SubElement(root, "path", {"d": d, "fill": "none", "stroke-width": "1.6",
                                  "stroke": "#222222" if idea else "#3b2f2f"})
                    e = next(el for el in root.iter() if style.tag(el) == "text"
                             and style.text_of(el) == "E")
                    e.attrib.update(x="150", y="100", **{"font-size": "17", "font-style": "normal",
                                                        "text-anchor": "start"})
                    if "Q" in d:
                        self.assert_refused(root, idea, "<path>", "d")
                    else:
                        found = [f[3] for f in figure_findings(root, idea) if f[0] == "S26"]
                        self.assertTrue(any("letter E" in f and "from a path" in f for f in found), found)
                        root[-1].set("transform", "translate(0,0.1)")
                        self.assertEqual([f for f in figure_findings(root, idea) if f[0] == "S26"], [])

    def test_long_malformed_lists(self):
        # A subprocess bounds even the old parser's quadratic failure time.
        code = f"""
import runpy
ns = runpy.run_path({str(Path(__file__).resolve())!r})
for idea in (False, True):
    for attr in ('points', 'viewBox', 'stroke-dasharray'):
        root = ns['figure_fixture'](idea)
        root.set(attr, '0 0 ' + '9' * 32000 + 'x 300')
        found = ns['figure_findings'](root, idea)
        assert any(f[0] == 'S26' and attr in f[3] for f in found), found
"""
        subprocess.run([sys.executable, "-I", "-c", code], check=True, timeout=2,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)


class Clearance(unittest.TestCase):
    """The clearance cases, and a letter drawn more than once."""

    def test_curve_join_figure_entry_points(self):
        """True curve tangents put mitres near E; round joins clear it."""
        paths = (
            # The reviewer's cubic; its last control point is almost its endpoint.
            "M150 90 C150 95 149.9999 100 150 100 L141.339746 105",
            # Reversed, and with one or both endpoint controls coincident.
            "M141.339746 105 L150 100 C149.9999 100 150 95 150 90",
            "M150 90 C149.9999 100 150 100 150 100 L141.339746 105",
            "M141.339746 105 L150 100 C150 100 149.9999 100 150 90",
            "M140 100 C150 100 150 100 150 100 L141.339746 105",
            "M141.339746 105 L150 100 C150 100 150 100 140 100",
            # An arc with the same end tangent, reversed, rotated and enlarged.
            "M140 90 A10 10 0 0 0 150 100 L141.339746 105",
            "M141.339746 105 L150 100 A10 10 0 0 1 140 90",
            "M140 80 A20 10 90 0 0 150 100 L141.339746 105",
            "M150 98 A0.1 0.1 0 0 0 150 100 L141.339746 105",
            # The outgoing segment can itself be a curve.
            "M140 90 A10 10 0 0 0 150 100 C147 101.7320508 144 105 141.339746 105",
            # Z supplies a segment, and joins the last segment to the first.
            "M141.339746 105 L140 90 A10 10 0 0 0 150 100 Z",
            "M150 100 C150 100 149.9999 100 150 90 L141.339746 105 Z",
            # A directionless segment or an omitted arc does not break a join.
            "M150 90 C150 95 149.9999 100 150 100 L150 100 "
            "C150 100 150 100 150 100 A10 10 0 0 0 150 100 L141.339746 105",
        )
        for idea in (False, True):
            for d in paths:
                for join in (None, "miter", "round"):
                    with self.subTest(idea=idea, d=d, join=join):
                        root = figure_fixture(idea)
                        curve = ET.SubElement(root, "path", {
                            "d": d, "fill": "none",
                            "stroke": "#222222" if idea else "#3b2f2f",
                            "stroke-width": "1.6"})
                        if join is not None:
                            curve.set("stroke-linejoin", join)
                        e = next(el for el in root.iter()
                                 if style.tag(el) == "text" and style.text_of(el) == "E")
                        for label in root.iter():
                            if style.tag(label) == "text":
                                label.set("font-style", "normal")
                        e.attrib.update(x="154.3" if idea and "A" in d else "154.2", y="99.4",
                                        **{"text-anchor": "start", "font-family": "Georgia"})
                        found = figure_findings(root, idea)
                        if join == "round":
                            self.assertEqual(found, [])
                        else:
                            self.assertEqual(len(found), 1, found)
                            self.assertEqual(found[0][0], "S26")
                            self.assertIn("letter E", found[0][3])
                            self.assertIn("from a path, under 2", found[0][3])

    def test_curve_subdivisions_have_no_joins(self):
        """A single curve has no joins at its sampled chords, nor across a moveto."""
        shapes = (
            '<path d="M100 100 C100 50 150 50 150 100"/>',
            '<path d="M140 90 A10 10 0 0 0 150 100"/>',
            '<rect x="100" y="100" width="50" height="50" rx="10"/>',
            '<path d="M100 100 C100 50 150 50 150 100 M150 100 L140 110"/>',
        )
        for shape in shapes:
            with self.subTest(shape=shape):
                root = ET.fromstring(
                    '<svg stroke="#3b2f2f" stroke-width="1.6" fill="none">'
                    + shape + '</svg>')
                pieces = list(style.strokes(style.ROOT / "figures" / "case.svg", root))
                self.assertTrue(any(len(run) > 3 for _, run, _ in pieces), pieces)
                self.assertTrue(all(half is not None for _, _, half in pieces),
                                "flattening or moveto introduced a filled join")

    def test_width_spellings(self):
        """Plain widths keep their clearance; CSS, units and exponents are refused."""
        for width in ("3", "3e0", "+3", "3px", "+3e0px"):
            for placement in ("attribute", "style", "inherited"):
                with self.subTest(width=width, placement=placement):
                    attrs = f'stroke-width="{width}"'
                    if placement == "style":
                        attrs = f'style="stroke-width:{width}"'
                    drawn = (f'<line x1="145" y1="103" x2="165" y2="103" '
                             f'stroke="#222222" {attrs if placement != "inherited" else ""}/>')
                    if placement == "inherited":
                        drawn = f'<g {attrs}>{drawn}</g>'
                    want = ["letter A at (150, 100) stands 1.5 from a line, under 2: move it clear"]
                    if placement == "style":
                        want = [svg_refusal("line", "style", f"stroke-width:{width}")]
                    elif width not in ("3", "+3"):
                        want = [svg_refusal("g" if placement == "inherited" else "line",
                                            "stroke-width", width)]
                    self.assertEqual(s26_findings(drawn, letter("A", font_style="normal", size=14)),
                                     want)

    def test_text_offsets(self):
        """Coordinates and translations place the capital; unused offsets and scales fail."""
        drawn = '<line x1="150" y1="92" x2="160" y2="92" stroke="#222222" stroke-width="2"/>'
        for transform in ("", 'transform="translate(25,20)"',
                          'transform="translate(25,20) scale(2,1.5)"'):
            for position, want in (
                    ('x="150" y="100"', True),
                    ('x="150" y="120" dy="-20"', True),
                    ('x="130" y="100" dx="+2e1"', True),
                    ('x="130" y="120" dx="20" dy="-20"', True),
                    ('x="150" y="120"', False),
                    ('x="150" y="100" dy="20"', False),
                    ('x="170" y="100"', False),
                    ('x="150" y="100" dx="20"', False)):
                with self.subTest(transform=transform, position=position):
                    text = f'<text {position} font-size="14" font-style="normal">A</text>'
                    found = s26_findings(f'<g {transform}>{drawn}{text}</g>', "")
                    refused = []
                    if "scale" in transform:
                        refused.append(svg_refusal("g", "transform", "translate(25,20) scale(2,1.5)"))
                    for attr, value in ET.fromstring(text).attrib.items():
                        if attr in ("dx", "dy"):
                            refused.append(svg_refusal("text", attr, value))
                    if refused:
                        self.assertEqual(found, refused)
                    else:
                        self.assertEqual(bool(found), want, found)

    def test_stroke_joins(self):
        """A mitre reaches H and a round join clears it; unused join syntax is refused."""
        shapes = (
            '<polyline points="130,160 155,104 180,160" {attrs}/>',
            '<polyline points="180,160 155,104 130,160" {attrs}/>',
            '<polyline points="130,160 155,104 155,104 180,160" {attrs}/>',
            '<path d="M130 160 L155 104 L180 160" {attrs}/>',
            '<path d="M155 104 L180 160 L130 160 Z" {attrs}/>',
            '<polygon points="155,104 180,160 130,160" {attrs}/>',
        )
        for shape in shapes:
            for join, want in (("", True), ('stroke-linejoin="miter"', True),
                               ('stroke-linejoin="round"', False),
                               ('stroke-linejoin="bevel"', False),
                               ('stroke-miterlimit="2"', False),
                               ('stroke-miterlimit="+3e0"', True)):
                for inherited in (False, True):
                    with self.subTest(shape=shape, join=join, inherited=inherited):
                        attrs = f'stroke="#222222" stroke-width="3" fill="none" {join}'
                        drawn = (f'<g {attrs}>{shape.format(attrs="")}</g>' if inherited
                                 else shape.format(attrs=attrs))
                        found = s26_findings(drawn, letter("H", font_style="normal"))
                        refused = [svg_refusal("g" if inherited else style.tag(ET.fromstring(drawn)),
                                               k, v) for k, v in ET.fromstring(f"<g {join}/>").attrib.items()
                                   if k == "stroke-miterlimit" or v == "bevel"]
                        if refused:
                            self.assertEqual(found, refused)
                        else:
                            self.assertEqual(bool(found), want, found)
                            if want:
                                self.assertIn("stands 0.3 from", found[0])

    def test_square_caps(self):
        """Unused square caps, CSS and scales fail; supported round and butt caps clear H."""
        shapes = (
            '<line x1="163.2" y1="102.5" x2="183.2" y2="102.5" {attrs}/>',
            '<line x1="183.2" y1="102.5" x2="163.2" y2="102.5" {attrs}/>',
            '<polyline points="163.2,102.5 163.2,102.5 183.2,102.5" {attrs}/>',
            '<path d="M163.2 102.5 L183.2 102.5" {attrs}/>',
            '<line x1="163.2" y1="102.5" x2="163.2" y2="102.5" {attrs}/>',
            '<path d="M163.2 102.5 L163.2 102.5" {attrs}/>',
            '<path d="M163.2 102.5 Z" {attrs}/>',
            '<path d="M250 200 L260 200 M163.2 102.5 Z" {attrs}/>',
        )
        for shape in shapes:
            for cap in ("square", "round", "butt"):
                for placement in ("attribute", "style", "inherited"):
                    for transform in ("", "rotate(30,150,100)",
                                      "translate(10,10) scale(1.1,1.2)"):
                        with self.subTest(shape=shape, cap=cap, placement=placement,
                                          transform=transform):
                            caps = (f'style="stroke-linecap:{cap}"' if placement == "style"
                                    else f'stroke-linecap="{cap}"')
                            attrs = 'stroke="#222222" stroke-width="3" fill="none"'
                            drawn = (f'<g {caps}>{shape.format(attrs=attrs)}</g>'
                                     if placement == "inherited"
                                     else shape.format(attrs=f"{attrs} {caps}"))
                            group_transform = f' transform="{transform}"' if transform else ""
                            found = s26_findings(
                                f'<g{group_transform}>{drawn}'
                                + letter("H", font_style="normal", size=14) + '</g>', "")
                            refused = []
                            if "scale" in transform:
                                refused.append(svg_refusal("g", "transform", transform))
                            kind = "g" if placement == "inherited" else style.tag(ET.fromstring(drawn))
                            if placement == "style":
                                refused.append(svg_refusal(kind, "style", f"stroke-linecap:{cap}"))
                            elif cap == "square":
                                refused.append(svg_refusal(kind, "stroke-linecap", cap))
                            self.assertEqual(found, refused)

    def test_square_cap_boundaries(self):
        """Unused square caps are refused on open, closed and empty subpaths alike."""
        shape = ('<line x1="163.2" y1="102.5" x2="183.2" y2="102.5" '
                 'style="stroke-linecap:{cap}"/>')
        for drawn, want in (
                (shape.format(cap="round"), False),
                (shape.format(cap="butt"), False),
                ('<g stroke-linecap="butt">' + shape.format(cap="square") + '</g>', True),
                ('<path d="M163.2 102.5"/>', False),
                ('<path d="M163.2 102.5 L183.2 102.5 L183.2 122.5 Z"/>', False),
                ('<path d="M163.2 102.5 L183.2 102.5 L183.2 122.5 L163.2 102.5"/>', True),
                ('<polygon points="163.2,102.5 183.2,102.5 183.2,122.5"/>', False)):
            with self.subTest(drawn=drawn):
                found = s26_findings(
                    '<g stroke="#222222" stroke-width="3" stroke-linecap="square" '
                    f'stroke-linejoin="round" fill="none">{drawn}</g>',
                    letter("H", font_style="normal", size=14))
                refused = [svg_refusal("g", "stroke-linecap", "square")]
                for el in ET.fromstring(drawn).iter():
                    if "style" in el.attrib:
                        refused.append(svg_refusal(style.tag(el), "style", el.get("style")))
                self.assertEqual(found, refused)

    def test_square_caps_idea(self):
        """The reviewer's square cap is refused by the complete idea-figure check."""
        for cap in ("square", "round", "butt"):
            with self.subTest(cap=cap):
                root = ET.fromstring(
                    '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 300" '
                    'font-family="Georgia">'
                    '<title>I.1 at a glance</title><desc>A straight line [black].</desc>'
                    '<text x="150" y="100" font-size="14" font-style="normal" '
                    'fill="#222222">H</text>'
                    '<line x1="163.2" y1="102.5" x2="183.2" y2="102.5" '
                    f'stroke="#222222" stroke-width="3" stroke-linecap="{cap}"/></svg>')
                with patch.object(style, "svg_root", return_value=root), \
                        patch.object(style, "drawn_letters", return_value={"H"}), \
                        patch.object(style, "failures", []), \
                        patch.object(style, "reports", defaultdict(list)):
                    style.check_idea(style.ROOT / "figures" / "I" / "01-idea.svg", "I.1", True)
                    want = [("S26", svg_refusal("line", "stroke-linecap", "square"))] \
                        if cap == "square" else []
                    self.assertEqual([(r, m) for r, _, _, m in style.failures], want)

    def test_zero_length_subpaths(self):
        """A closed point with round caps is drawn like a zero-length line."""
        for cap in ("butt", "round"):
            for shape in (
                    '<line x1="156" y1="94" x2="156" y2="94" {attrs}/>',
                    '<path d="M156 94 Z" {attrs}/>',
                    '<path d="M156 94 L156 94" {attrs}/>',
                    '<path d="M156 94 Z M250 200 L260 200" {attrs}/>',
                    '<path d="M250 200 L260 200 M156 94 Z" {attrs}/>'):
                with self.subTest(cap=cap, shape=shape):
                    drawn = shape.format(attrs=f'stroke="#222222" stroke-width="3" '
                                         f'stroke-linecap="{cap}" fill="none"')
                    found = s26_findings(drawn, letter("A", font_style="normal", size=14))
                    self.assertEqual(bool(found), cap == "round", found)
        # A moveto alone has no drawing command, so even round caps paint nothing.
        self.assertEqual(s26_findings(
            '<path d="M156 94" stroke="#222222" stroke-width="3" stroke-linecap="round"/>',
            letter("A", font_style="normal", size=14)), [])

    def test_join_boundaries(self):
        """Joins respect open ends and a hull wholly inside; CSS and scales are refused."""
        shape = ('<polyline points="130,160 155,104 180,160" stroke="#222222" '
                 'stroke-width="3" fill="none" {attrs}/>')
        for drawn, want in (
                ('<path d="M155 104 L180 160 L130 160 L155 104" stroke="#222222" '
                 'stroke-width="3" fill="none"/>', False),
                ('<g stroke-linejoin="round">'
                 + shape.format(attrs='style="stroke-linejoin:miter"') + '</g>', True),
                ('<g stroke-linejoin="miter">'
                 + shape.format(attrs='style="stroke-linejoin:round"') + '</g>', False),
                ('<polyline points="-95,960 155,400 405,960" stroke="#222222" '
                 'stroke-width="300" fill="none"/>', True)):
            with self.subTest(drawn=drawn):
                found = s26_findings(drawn, letter("H", font_style="normal"))
                refused = [svg_refusal(style.tag(el), "style", el.get("style"))
                           for el in ET.fromstring(drawn).iter() if "style" in el.attrib]
                if refused:
                    self.assertEqual(found, refused)
                else:
                    self.assertEqual(bool(found), want, found)
        found = s26_findings('<g transform="translate(25,10) scale(2)">'
                             + shape.format(attrs="") + letter("H", font_style="normal")
                             + '</g>', "")
        self.assertEqual(found, [svg_refusal("g", "transform", "translate(25,10) scale(2)")])

    def test_figure_entry_points(self):
        """Both production figure checks require S26's clearance finding."""
        for idea in (True, False):
            with self.subTest(idea=idea):
                ink, size = ("#222222", 14) if idea else ("#3b2f2f", 17)
                title = "I.1 at a glance" if idea else "Euclid I.1: a triangle"
                desc = "<desc>A straight line [black].</desc>" if idea else ""
                root = ET.fromstring(
                    f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 300" '
                    f'font-family="Georgia">'
                    f'<title>{title}</title>{desc}'
                    f'<line x1="145" y1="103" x2="165" y2="103" '
                    f'stroke="{ink}" stroke-width="3"/>'
                    f'<g fill="{ink}">{letter("A", font_style="normal", size=size)}</g></svg>')
                with patch.object(style, "svg_root", return_value=root), \
                        patch.object(style, "drawn_letters", return_value={"A"}), \
                        patch.object(style, "heath_letters", return_value={"A"}), \
                        patch.object(style, "failures", []), \
                        patch.object(style, "reports", defaultdict(list)):
                    path = style.ROOT / "figures" / "I" / ("01-idea.svg" if idea else "01.svg")
                    if idea:
                        style.check_idea(path, "I.1", True)
                    else:
                        style.check_euclid(path, "I.1")
                    self.assertEqual(
                        [(rule, msg) for rule, _, _, msg in style.failures],
                        [("S26", "letter A at (150, 100) stands 1.5 from a line, "
                          "under 2: move it clear")])

    def test_use_figure_entry_points(self):
        """Both complete figure checks refuse references they do not follow."""
        for idea in (True, False):
            for use in ("", '<use href="#pointA" x="200"/>',
                        '<g><use xmlns:xlink="http://www.w3.org/1999/xlink" '
                        'xlink:href="#pointA" x="200"/></g>'):
                with self.subTest(idea=idea, use=use):
                    ink, size = ("#222222", 14) if idea else ("#3b2f2f", 17)
                    title = "I.1 at a glance" if idea else "Euclid I.1: a point"
                    desc = "<desc>A point [black].</desc>" if idea else ""
                    root = ET.fromstring(
                        '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 300">'
                        f'<title>{title}</title>{desc}'
                        f'<text id="pointA" x="60" y="100" font-size="{size}" '
                        f'font-style="normal" fill="{ink}">A</text>{use}</svg>')
                    with patch.object(ET, "parse", return_value=ET.ElementTree(root)), \
                            patch.object(Path, "read_text", return_value="A"), \
                            patch.object(style, "failures", []), \
                            patch.object(style, "reports", defaultdict(list)):
                        name = "01-idea.svg" if idea else "01.svg"
                        path = style.ROOT / "figures" / "I" / name
                        if idea:
                            style.check_idea(path, "I.1", True)
                        else:
                            style.check_euclid(path, "I.1")
                        messages = [svg_refusal("text", "id", "pointA")]
                        if use:
                            messages.append(svg_refusal("use"))
                        want = [("S26", f"figures/I/{name}", 0, msg) for msg in messages]
                        self.assertEqual(style.failures, want)

    def test_text_children_figure_entry_points(self):
        """Positioned descendants cannot borrow the parent's clear position."""
        for idea in (False, True):
            path = style.ROOT / "figures" / "I" / ("01-idea.svg" if idea else "01.svg")
            for child in ("", '<tspan x="150" y="155">A</tspan>',
                          '<tspan x="150" y="150">A</tspan>', '<tspan>A</tspan>',
                          '<a>A</a>'):
                with self.subTest(idea=idea, child=child):
                    root = figure_fixture(idea)
                    if child:
                        a = next(el for el in root.iter()
                                 if style.tag(el) == "text" and style.text_of(el) == "A")
                        a.text = None
                        a.append(ET.fromstring(child))
                    want = [("S26", str(path.relative_to(style.ROOT)), 0,
                             svg_refusal(style.tag(ET.fromstring(child))))] if child else []
                    self.assertEqual(figure_findings(root, idea), want)
            for y in ("150", "155"):
                with self.subTest(idea=idea, flat_y=y):
                    root = figure_fixture(idea)
                    a = next(el for el in root.iter()
                             if style.tag(el) == "text" and style.text_of(el) == "A")
                    a.attrib.update(x="150", y=y)
                    self.assertTrue(any(r == "S26" and "letter A" in msg
                                        for r, _, _, msg in figure_findings(root, idea)))

    def test_text_lists_figure_entry_points(self):
        """All four text coordinates must place one label, including dx and dy."""
        for idea in (False, True):
            path = style.ROOT / "figures" / "I" / ("01-idea.svg" if idea else "01.svg")
            for attr in ("x", "y", "dx", "dy"):
                for suffix in ("", " 270", ",270", " +2.7e2"):
                    with self.subTest(idea=idea, attr=attr, suffix=suffix):
                        root = figure_fixture(idea)
                        a = next(el for el in root.iter()
                                 if style.tag(el) == "text" and style.text_of(el) == "A")
                        a.set(attr, a.get(attr, "0") + suffix)
                        want = [("S26", str(path.relative_to(style.ROOT)), 0,
                                 svg_refusal("text", attr, a.get(attr)))] \
                            if suffix or attr in ("dx", "dy") else []
                        self.assertEqual(figure_findings(root, idea), want)

    def test_unmeasured_capitals_figure_entry_points(self):
        """Extra capital runs fail even while every required letter remains present."""
        for idea in (False, True):
            path = style.ROOT / "figures" / "I" / ("01-idea.svg" if idea else "01.svg")
            for text in ("AA", "A B", "A=2", "Angle A", "2", "lowercase"):
                for x in ("120", "120 270"):
                    with self.subTest(idea=idea, text=text, x=x):
                        root = figure_fixture(idea)
                        ink = "#222222" if idea else "#3b2f2f"
                        root.append(ET.fromstring(
                            f'<text x="{x}" y="220" fill="{ink}">{text}</text>'))
                        want = []
                        if " " in x:
                            want.append(svg_refusal("text", "x", x))
                        if " " not in x and text not in ("2", "lowercase"):
                            want.append(f"<text> {text!r} has unmeasured capitals: "
                                        "draw each label in a separate <text>")
                        expected = [("S26", str(path.relative_to(style.ROOT)), 0, msg)
                                    for msg in want]
                        if " " not in x and idea and text != "2":
                            expected.append(("S20", str(path.relative_to(style.ROOT)), 0,
                                             f"<text>{text}</text>: an idea figure's text is "
                                             "Heath's letters, one to a <text>, or numbers "
                                             "on a fill"))
                        self.assertEqual(figure_findings(root, idea), expected)

    def test_stroke_widths_figure_entry_points(self):
        """Unsupported widths fail explicitly; 3pt's equivalent 4 fails clearance."""
        for idea in (False, True):
            path = style.ROOT / "figures" / "I" / ("01-idea.svg" if idea else "01.svg")
            for width in (None, "1", "1px", "4", "4px", "3pt", "3em", "3%",
                          "bad", "", "1..5", "1e999"):
                for placement in ("attribute", "style", "inherited"):
                    with self.subTest(idea=idea, width=width, placement=placement):
                        root = figure_fixture(idea)
                        ink, y = ("#222222", 55.5) if idea else ("#3b2f2f", 57.5)
                        line = ET.SubElement(root, "line", x1="194", y1=str(y), x2="206",
                                             y2=str(y), stroke=ink)
                        if width is not None:
                            if placement == "inherited":
                                root.remove(line)
                                group = ET.SubElement(root, "g", {"stroke-width": width})
                                group.append(line)
                            else:
                                line.set("style" if placement == "style" else "stroke-width",
                                         f"stroke-width:{width}" if placement == "style" else width)
                        found = [f for f in figure_findings(root, idea) if f[0] == "S26"]
                        if width == "4" and placement != "style":
                            self.assertEqual(len(found), 1, found)
                            self.assertIn("letter C", found[0][3])
                            self.assertIn("from a line, under 2", found[0][3])
                        else:
                            messages = []
                            if width is not None and placement == "style":
                                messages.append(svg_refusal("line", "style", f"stroke-width:{width}"))
                            elif width not in (None, "1"):
                                messages.append(svg_refusal("g" if placement == "inherited" else "line",
                                                            "stroke-width", width))
                            want = [("S26", str(path.relative_to(style.ROOT)), 0, m) for m in messages]
                            self.assertEqual(found, want)

    def test_vector_effect_figure_entry_points(self):
        """A scaled non-scaling stroke is refused in either presentation spelling."""
        for idea in (False, True):
            path = style.ROOT / "figures" / "I" / ("01-idea.svg" if idea else "01.svg")
            for effect in (None, "non-scaling-stroke", "none"):
                for placement in ("attribute", "style"):
                    with self.subTest(idea=idea, effect=effect, placement=placement):
                        root = figure_fixture(idea)
                        ink, y = ("#222222", "111") if idea else ("#3b2f2f", "115")
                        line = ET.SubElement(root, "line", x1="388", y1=y, x2="412", y2=y,
                                             stroke=ink, transform="scale(.5)",
                                             attrib={"stroke-width": "4"})
                        if effect is not None:
                            line.set("style" if placement == "style" else "vector-effect",
                                     f"vector-effect:{effect}" if placement == "style" else effect)
                        found = [f for f in figure_findings(root, idea) if f[0] == "S26"]
                        messages = [svg_refusal("line", "transform", "scale(.5)")]
                        if effect is not None:
                            attr = "style" if placement == "style" else "vector-effect"
                            messages.append(svg_refusal("line", attr, line.get(attr)))
                        want = [("S26", str(path.relative_to(style.ROOT)), 0, m) for m in messages]
                        self.assertEqual(found, want)

    def test_sagitta_figure_entry_points(self):
        """Curved chords must not hide a clearance just below 2."""
        shapes = {
            "circle": '<circle cx="250" cy="150" r="100"/>',
            "ellipse": '<ellipse cx="250" cy="150" rx="100" ry="100"/>',
            "transformed ellipse":
                '<ellipse cx="500" cy="150" rx="200" ry="100" transform="scale(.5,1)"/>',
            "path": '<path d="M350 150 A100 100 0 1 0 150 150 A100 100 0 1 0 350 150"/>',
            "relative path": '<path d="M350 150 a100 100 0 1 0 -200 0 a100 100 0 1 0 200 0"/>',
            "grown path": '<path d="M350 150 A1 1 0 1 0 150 150 A1 1 0 1 0 350 150"/>',
            "transformed path": '<path transform="scale(.5,1)" '
                'd="M700 150 A200 100 0 1 0 300 150 A200 100 0 1 0 700 150"/>',
            "rect": '<rect x="150" y="50" width="200" height="200" rx="100"/>',
            "transformed rect": '<rect x="300" y="50" width="400" height="200" '
                'rx="200" ry="100" transform="scale(.5,1)"/>',
        }
        for idea in (False, True):
            path = style.ROOT / "figures" / "I" / ("01-idea.svg" if idea else "01.svg")
            for shape, markup in shapes.items():
                for near in (False, True):
                    with self.subTest(idea=idea, shape=shape, near=near):
                        root = figure_fixture(idea)
                        curve = ET.SubElement(root, "g", {
                            "fill": "none", "stroke": "#222222" if idea else "#8c7b62",
                            "stroke-width": "3" if idea else "1.3"})
                        curve.append(ET.fromstring(markup))
                        e = next(el for el in root.iter()
                                 if style.tag(el) == "text" and style.text_of(el) == "E")
                        e.attrib.update(x="268.13", y=("47.38" if idea else "48.93")
                                        if near else "47")
                        found = figure_findings(root, idea)
                        if shape.startswith("transformed") or shape == "relative path":
                            attr = "d" if shape == "relative path" else "transform"
                            self.assertEqual(found, [("S26", str(path.relative_to(style.ROOT)), 0,
                                svg_refusal(style.tag(curve[0]), attr, curve[0].get(attr)))])
                        elif near:
                            self.assertEqual(len(found), 1, found)
                            self.assertEqual(found[0][:3],
                                             ("S26", str(path.relative_to(style.ROOT)), 0))
                            self.assertIn("letter E", found[0][3])
                            kind = style.tag(curve[0])
                            self.assertIn(f"from {'an' if kind == 'ellipse' else 'a'} {kind}",
                                          found[0][3])
                            self.assertIn("under 2", found[0][3])
                        else:
                            self.assertEqual(found, [])

    def test_percentage_coordinates_figure_entry_points(self):
        """Percentages cannot conceal a line through E at either entry point."""
        for idea in (False, True):
            path = style.ROOT / "figures" / "I" / ("01-idea.svg" if idea else "01.svg")
            for percentage in (False, True):
                with self.subTest(idea=idea, percentage=percentage):
                    root = figure_fixture(idea)
                    line = ET.SubElement(root, "line", {
                        "x1": "88%" if percentage else "352",
                        "x2": "91%" if percentage else "364",
                        "y1": "50.2667%" if percentage else "150.8",
                        "y2": "50.2667%" if percentage else "150.8",
                        "stroke": "#222222" if idea else "#3b2f2f", "stroke-width": "1.6"})
                    found = [f for f in figure_findings(root, idea) if f[0] == "S26"]
                    if percentage:
                        self.assertEqual(found, [
                            ("S26", str(path.relative_to(style.ROOT)), 0,
                             svg_refusal("line", attr, line.get(attr))) for attr in ("x1", "x2", "y1", "y2")])
                    else:
                        self.assertEqual(len(found), 1, found)
                        self.assertIn("letter E", found[0][3])
                        self.assertIn("meets a line", found[0][3])

    def test_lengths_figure_entry_points(self):
        """Every measured scalar length rejects units and malformed numbers by file."""
        shapes = {
            "line": ("x1", "y1", "x2", "y2", "stroke-width"),
            "circle": ("cx", "cy", "r"),
            "ellipse": ("cx", "cy", "rx", "ry"),
            "rect": ("x", "y", "width", "height", "rx", "ry"),
            "text": ("x", "y", "dx", "dy", "font-size"),
        }
        invalid = ("88%", "3pt", "3em", "3ex", "3rem", "3cm", "3mm", "3in", "3pc",
                   "3vh", "3vw", "bad", "", "1..5", "1e", "px", "NaN", "inf", "1e999")
        for idea in (False, True):
            path = style.ROOT / "figures" / "I" / ("01-idea.svg" if idea else "01.svg")
            for kind, attrs in shapes.items():
                for attr in attrs:
                    for value in invalid:
                        for placement in ("attribute", "style", "inherited") \
                                if attr in ("stroke-width", "font-size") else ("attribute", "style"):
                            with self.subTest(idea=idea, kind=kind, attr=attr, value=value,
                                              placement=placement):
                                root = figure_fixture(idea)
                                el = ET.SubElement(root, kind, {
                                    "fill": "none",
                                    "stroke": "#222222" if idea else "#3b2f2f"})
                                if kind == "text":
                                    el.text = "A"
                                target = el
                                if placement == "inherited":
                                    root.remove(el)
                                    target = ET.SubElement(root, "g")
                                    target.append(el)
                                target.set("style" if placement == "style" else attr,
                                           f"{attr}:{value}" if placement == "style" else value)
                                found = [f for f in figure_findings(root, idea) if f[0] == "S26"]
                                self.assertIn(
                                    ("S26", str(path.relative_to(style.ROOT)), 0,
                                     svg_refusal(style.tag(target),
                                                 "style" if placement == "style" else attr,
                                                 f"{attr}:{value}" if placement == "style" else value)), found)

    def test_length_spellings_figure_entry_points(self):
        """Plain signed decimals agree; former unit and exponent spellings are refused."""
        for idea in (False, True):
            for spec, suffix in (("+.6f", ""), ("+.6e", ""), ("+.6e", "px"), ("+.6f", "px")):
                with self.subTest(idea=idea, spec=spec, suffix=suffix):
                    root = figure_fixture(idea)
                    messages = []
                    for el in root.iter():
                        for attr in ("x", "y", "x1", "y1", "x2", "y2", "width", "height",
                                     "rx", "font-size", "stroke-width"):
                            if attr in el.attrib:
                                value = format(float(el.get(attr)), spec) + suffix
                                el.set(attr, value)
                                if spec.endswith("e") or suffix:
                                    messages.append(svg_refusal(style.tag(el), attr, value))
                    self.assertCountEqual([m for _, _, _, m in figure_findings(root, idea)], messages)

    def test_coordinate_sequences_figure_entry_points(self):
        """Point lists and the canvas cannot hide units or drop malformed coordinates."""
        for idea in (False, True):
            path = style.ROOT / "figures" / "I" / ("01-idea.svg" if idea else "01.svg")
            for kind, attr in (("polyline", "points"), ("polygon", "points"), ("svg", "viewBox")):
                for value in ("0 0 400% 300", "0 0 3pt 300", "0 0 bad 300",
                              "0 0 1..5 300", "0 0 1e999 300", "0 0 400", ""):
                    with self.subTest(idea=idea, kind=kind, value=value):
                        root = figure_fixture(idea)
                        el = root if kind == "svg" else ET.SubElement(
                            root, kind, {"stroke": "#222222" if idea else "#3b2f2f"})
                        el.set(attr, value)
                        found = [f for f in figure_findings(root, idea) if f[0] == "S26"]
                        self.assertEqual(found, [
                            ("S26", str(path.relative_to(style.ROOT)), 0,
                             svg_refusal(kind, attr, value))])

    def test_clearance_cases(self):
        for drawn, s, font_style, anchor, want in CLEAR_CASES:
            with self.subTest(drawn=drawn, letter=s, style=font_style, anchor=anchor):
                found = s26_findings(drawn, letter(s, font_style=font_style, anchor=anchor))
                self.assertFalse(any("SVG allow-list" in message for message in found), found)
                self.assertEqual(bool(found), want,
                                 f"S26 {'misses' if want else 'wrongly finds'} a stroke "
                                 f"near {font_style} {s}, anchored at its {anchor}: "
                                 f"{drawn}: {found}")

    test_clearance_cases.__doc__ = (f"S26 reads {len(CLEAR_CASES)} strokes and dots beside "
                                    "a letter rightly")

    def test_clearance_refusal_cases(self):
        for drawn, kind, attr, value in CLEAR_REFUSAL_CASES:
            with self.subTest(drawn=drawn):
                self.assertEqual(s26_findings(drawn, letter("A")),
                                 [svg_refusal(kind, attr, value)])

    test_clearance_refusal_cases.__doc__ = (
        f"S26 refuses {len(CLEAR_REFUSAL_CASES)} excluded clearance spellings exactly")

    def test_edge_cases(self):
        for x, y, want in EDGE_CASES:
            with self.subTest(at=(x, y)):
                found = s26_findings("", letter("A", x=x, y=y))
                self.assertEqual(bool(found), want,
                                 f"S26 {'misses' if want else 'wrongly finds'} the canvas's "
                                 f"edge near a letter at ({x:g}, {y:g}): {found}")

    test_edge_cases.__doc__ = f"S26 reads {len(EDGE_CASES)} letters by the canvas's edge rightly"

    def test_place_cases(self):
        for drawn, letters, want in PLACE_CASES:
            with self.subTest(drawn=drawn, letters=letters):
                found = s26_findings(drawn, letters)
                self.assertEqual(bool(found), want,
                                 f"S26 {'misses' if want else 'wrongly finds'} a finding on "
                                 f"{letters} beside {drawn or 'nothing'}: {found}")

    test_place_cases.__doc__ = (f"S26 reads {len(PLACE_CASES)} letters by their size, their "
                                "transform and their primes rightly")

    def test_kind_cases(self):
        for drawn, kind in KIND_CASES:
            with self.subTest(drawn=drawn):
                found = s26_findings(drawn, letter("A"))
                self.assertEqual(found, [f"letter A at (150, 100) meets {kind}"],
                                 f"S26 does not call {drawn} {kind}: {found}")

    test_kind_cases.__doc__ = (f"S26 names {len(KIND_CASES)} lines through a letter, dashed "
                               "or not, rightly")

    def test_twice_cases(self):
        for xs, cuts, want in TWICE_CASES:
            with self.subTest(at=xs, cuts=cuts):
                found = s26_findings("", "".join(letter("A", x=x) for x in xs), cuts)
                self.assertEqual(bool(found), want,
                                 f"S26 {'misses' if want else 'wrongly finds'} a letter "
                                 f"drawn at x {xs}, cut at {cuts}: {found}")

    test_twice_cases.__doc__ = (f"S26 reads {len(TWICE_CASES)} figures drawing a letter "
                                "once or more rightly")


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
            "  ✗ S26 figures/I/10.svg: a letter meets a line",
        ])
        with ExitStack() as stack:
            stack.enter_context(patch.object(acceptance, "failures", {}))
            stack.enter_context(patch.object(acceptance, "run", return_value=SimpleNamespace(
                returncode=1, stdout=out, stderr="")))
            acceptance.check_style_rules()
            self.assertEqual(sorted(acceptance.failures),
                             [("I.10", "P8"), ("I.5", "P9"), ("I.6", "P9"),
                              ("I.7", "P7"), ("I.8", "P8"), ("I.9", "P9")])


if __name__ == "__main__":
    unittest.main(verbosity=2)
