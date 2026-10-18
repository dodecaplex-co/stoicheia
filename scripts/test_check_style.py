#!/usr/bin/env python3
"""Tests for S20's ink in scripts/check_style.py: a letter on an angle's wedge.

    python3 scripts/test_check_style.py        # a second or so; no Lean, no network

Each test draws a small figure at a glance in a temporary directory, with Euclid's figure
beside it to take Heath's letters from, runs `check_idea_letters` on it, and reads the S20
findings. An angle's wedge is a filled path, and a letter on one is judged by the wedge's
fill: black on a blue wedge is caught, the parchment's colour on it passes, and black on a
yellow wedge drawn over red passes. The wedge is spelled with an absolute arc, a relative
arc and a cubic curve, and moved by a transform, and each spelling is judged alike.
Standard library only.
"""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import check_style  # noqa: E402

RED, YELLOW, BLUE = "#d0312d", "#f2b705", "#1f5aa6"
BLACK, PARCHMENT = check_style.IDEA_INK, check_style.IDEA_INK_ON_DARK

# A quarter wedge of radius 34 at the vertex (200, 150), below and to the right of it.
WEDGES = {
    "an absolute arc": "M200,150 L234,150 A34,34 0 0,1 200,184 Z",
    "a relative arc": "m200,150 l34,0 a34,34 0 0,1 -34,34 z",
    "a cubic curve": "M200,150 H234 C234,168.78 218.78,184 200,184 Z",
}
ON_TRIANGLE = (215.0, 160.0)   # inside the triangle of the wedge's three ends
ON_ARC = (221.2, 171.2)        # 30 from the vertex: beyond the chord, inside the arc
BEYOND = (226.9, 176.9)        # 38 from the vertex: on the parchment


def letter(centre: tuple[float, float], ink: str) -> str:
    """Heath's A in the given ink, its glyph's middle at `centre` as check_style reckons it."""
    x, y = centre
    size = check_style.IDEA_LETTER_SIZE
    return (f'<text x="{x}" y="{y + 0.35 * size}" text-anchor="middle" font-size="{size}" '
            f'font-style="italic" fill="{ink}">A</text>')


class WedgeInk(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.saved_root = check_style.ROOT
        check_style.ROOT = self.root
        check_style.failures.clear()
        (self.root / "04.svg").write_text(
            '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 300">'
            '<text x="190" y="140">A</text></svg>')

    def tearDown(self):
        check_style.ROOT = self.saved_root
        check_style.failures.clear()
        self.tmp.cleanup()

    def s20(self, body: str) -> list[str]:
        path = self.root / "04-idea.svg"
        path.write_text('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 300">'
                        f'<rect width="400" height="300" fill="#fbf7ee"/>{body}</svg>')
        check_style.failures.clear()
        check_style.check_idea_letters(path, check_style.svg_root(path), False)
        return [msg for rule, _, _, msg in check_style.failures if rule == "S20"]

    def test_black_letter_on_blue_wedge_is_caught(self):
        for name, d in WEDGES.items():
            for where in (ON_TRIANGLE, ON_ARC):
                with self.subTest(wedge=name, at=where):
                    found = self.s20(f'<path d="{d}" fill="{BLUE}"/>{letter(where, BLACK)}')
                    self.assertEqual(len(found), 1, found)
                    self.assertIn(f"not {PARCHMENT}", found[0])

    def test_parchment_letter_on_blue_wedge_passes(self):
        for name, d in WEDGES.items():
            for where in (ON_TRIANGLE, ON_ARC):
                with self.subTest(wedge=name, at=where):
                    self.assertEqual(self.s20(f'<path d="{d}" fill="{BLUE}"/>'
                                              f'{letter(where, PARCHMENT)}'), [])

    def test_black_letter_on_yellow_wedge_over_red_passes(self):
        red = '<polygon points="150,100 300,100 300,250 150,250" fill="#d0312d"/>'
        for name, d in WEDGES.items():
            with self.subTest(wedge=name):
                wedge = f'<path d="{d}" fill="{YELLOW}"/>'
                self.assertEqual(self.s20(red + wedge + letter(ON_ARC, BLACK)), [])
                found = self.s20(red + wedge + letter(ON_ARC, PARCHMENT))
                self.assertEqual(len(found), 1, found)
                self.assertIn(f"not {BLACK}", found[0])

    def test_letter_beyond_the_arc_stands_on_the_parchment(self):
        for name, d in WEDGES.items():
            with self.subTest(wedge=name):
                wedge = f'<path d="{d}" fill="{BLUE}"/>'
                self.assertEqual(self.s20(wedge + letter(BEYOND, BLACK)), [])
                self.assertEqual(len(self.s20(wedge + letter(BEYOND, PARCHMENT))), 1)

    def test_a_transformed_wedge_is_read_where_it_is_drawn(self):
        moved = (ON_ARC[0] - 100, ON_ARC[1] + 20)
        for name, d in WEDGES.items():
            with self.subTest(wedge=name):
                wedge = f'<g transform="translate(-100,20)"><path d="{d}" fill="{BLUE}"/></g>'
                self.assertEqual(len(self.s20(wedge + letter(moved, BLACK))), 1)
                self.assertEqual(self.s20(wedge + letter(moved, PARCHMENT)), [])
                self.assertEqual(self.s20(wedge + letter(ON_ARC, BLACK)), [])


if __name__ == "__main__":
    unittest.main()
