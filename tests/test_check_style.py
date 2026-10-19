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
* the modern cases: S22 and S23 read a figure of the modern way against its Euclid's
  figure's letters and its paragraph's names, which `modern_names` takes from TeX and
  from plain words alike.

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
# The modern cases: a figure of the modern way, read as S22 and S23 read it, against the
# letters its Euclid's figure draws and the names its paragraph uses.

MODERN_PARAGRAPH = (style.MODERN_WAY + r" Put $\mathrm{A} = (0, 0)$, $\mathrm{B} = (c, 0)$ "
                    r"and $\mathrm{C} = (0, b)$, and write $a$ for BC. Then $\vec{u}$ "
                    r"turns through $\theta$, and $\tfrac{1}{2}bc$ is the area; with h a "
                    "height, (a + b)² is plain.")
NAMES_CASES = [   # (a paragraph, names it must give, names it must not)
    (MODERN_PARAGRAPH, {"a", "b", "c", "u", "θ", "h"}, {"v", "e", "r", "t", "f", "m"}),
    (style.MODERN_WAY + r" The point $\mathrm{A} + i\mathrm{(B - A)}$ is D.", {"i"}, {"m", "r"}),
    (style.MODERN_WAY + " With AC = a and CB = b, the square is (a + b)².", {"a", "b"}, {"c"}),
    (style.MODERN_WAY + r" Its breadth is $q/(a\sin\theta)$.", {"q", "a", "θ"}, {"s", "n"}),
    (style.MODERN_WAY + r" With $\nu$ and $\vartheta$ and ϕ.", {"ν", "θ", "φ"}, {"n", "u"}),
    (style.MODERN_WAY + r" Let $a_{\text{side {length}}}$ be given.", {"a"}, {"g", "s", "l"}),
]
SPAN_CASES = [   # (a mishnah, the paragraph modern_span finds, or None)
    ("Before.\n\n" + style.MODERN_WAY + " x.\n\nAfter.", style.MODERN_WAY + " x."),
    ("Before.\n \n" + style.MODERN_WAY + " x.\n \nAfter.", style.MODERN_WAY + " x."),
    ("Before.\n\n  " + style.MODERN_WAY + " x.", style.MODERN_WAY + " x."),
    (style.MODERN_WAY + " x.\n# A heading", style.MODERN_WAY + " x."),
    ("<!--\n\n" + style.MODERN_WAY + " x.\n\n-->", None),
    ("```\n" + style.MODERN_WAY + " x.\n```", None),
    ("**A lead.** No modern way here.", None),
]
HEATHS = {"A", "B", "C"}
NAMES = style.modern_names(MODERN_PARAGRAPH)
MODERN_GOOD = ('<title>I.47: the modern way</title>'
               '<rect width="400" height="300" rx="10" fill="#fbf7ee"/>'
               '<line x1="40" y1="250" x2="360" y2="250" stroke="#3b2f2f" stroke-width="1.6"/>'
               '<polygon points="60,250 300,250 60,60" fill="#e9dcc0" fill-opacity="0.55" '
               'stroke="#a0522d" stroke-width="2.4"/>'
               '<g font-family="Georgia, serif" font-size="17" fill="#3b2f2f">'
               '<text x="50" y="270">A</text><text x="300" y="270">B</text>'
               '<text x="50" y="55">C</text>'
               '<text x="180" y="270" font-style="italic">c</text>'
               '<text x="200" y="140" font-style="italic">a² = b² + c²</text>'
               '<text x="70" y="290">(0, 0)</text></g>')
MODERN_CASES = [   # (a figure's inside, the title's ref, the finding wanted: rule, or None)
    (MODERN_GOOD, "I.47", None),
    (MODERN_GOOD, "I.48", "S22"),
    (MODERN_GOOD.replace("</title>", "</title><desc>A caption.</desc>"), "I.47", "S22"),
    (MODERN_GOOD.replace('fill="#e9dcc0"', 'fill="#f2b705"'), "I.47", "S22"),
    (MODERN_GOOD.replace('stroke-width="1.6"', 'stroke-width="0.8"'), "I.47", "S22"),
    (MODERN_GOOD.replace(">C<", ">D<"), "I.47", "S23"),
    (MODERN_GOOD.replace('<text x="50" y="270">A', '<text x="50" y="270" font-style="italic">A'),
     "I.47", "S23"),
    (MODERN_GOOD.replace('font-style="italic">c<', '>c<'), "I.47", "S23"),
    (MODERN_GOOD.replace(">c<", ">x<"), "I.47", "S23"),
    (MODERN_GOOD.replace(">c<", ">BC<"), "I.47", "S23"),
    (MODERN_GOOD.replace(">c<", ">c<tspan>₁</tspan><"), "I.47", "S23"),
    (MODERN_GOOD.replace(">c<", ">c∫<"), "I.47", "S23"),
    (MODERN_GOOD.replace('font-size="17"', 'font-size="14"'), "I.47", "S23"),
    (MODERN_GOOD.replace(' fill="#3b2f2f">', '>'), "I.47", "S22"),
    (MODERN_GOOD + '<polyline points="1,1 9,9 1,9" stroke="#8c7b62" stroke-width="1.3"/>',
     "I.47", "S22"),
    (MODERN_GOOD.replace(">a² = b² + c²<", ">a² =\n   b² + c²<"), "I.47", None),
    (MODERN_GOOD.replace(">c<", ">ϑ<"), "I.47", None),
    (MODERN_GOOD.replace(">c<", ">ν<"), "I.47", "S23"),
]


def modern_rules(inside: str, ref: str, heaths=HEATHS, names=NAMES) -> set[str]:
    """The rules S22 and S23 find broken in a 400 × 300 figure of the modern way."""
    root = ET.fromstring('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 300">'
                         f"{inside}</svg>")
    return {rule for rule, _ in style.modern_findings(root, ref, heaths, names)}


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


class Modern(unittest.TestCase):
    """The modern cases: the names a paragraph gives, and a figure of the modern way read
    against them and against its Euclid's figure's letters."""

    def test_names(self):
        for text, given, not_given in NAMES_CASES:
            with self.subTest(text=text):
                names = style.modern_names(text)
                self.assertLessEqual(given, names, f"modern_names misses {given - names}")
                self.assertFalse(names & not_given, f"modern_names wrongly gives {names & not_given}")

    def test_modern_cases(self):
        for inside, ref, want in MODERN_CASES:
            with self.subTest(figure=inside, ref=ref):
                found = modern_rules(inside, ref)
                if want is None:
                    self.assertEqual(found, set(), f"S22 and S23 wrongly find {found}")
                else:
                    self.assertIn(want, found, f"{want} misses a fault in {inside!r}")

    def test_no_paragraph_and_no_figure(self):
        self.assertIn("S22", modern_rules(MODERN_GOOD, "I.47", names=None))
        self.assertIn("S22", modern_rules(MODERN_GOOD, "I.47", heaths=None))
        for text, want in SPAN_CASES:
            with self.subTest(text=text):
                self.assertEqual(style.modern_paragraph(text), want)

    test_modern_cases.__doc__ = (f"S22 and S23 read {len(MODERN_CASES)} figures of the "
                                 "modern way rightly")


if __name__ == "__main__":
    unittest.main(verbosity=2)
