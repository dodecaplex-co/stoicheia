#!/usr/bin/env python3
"""Decision entries assembled in filename order, with dates supplied by the renderer.

    python3 -I tests/test_render_decisions.py

Standard library only; no Lean or network.
"""

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import render  # noqa: E402


BEGIN = "<!-- decisions:entries begin -->\n"
END = "<!-- decisions:entries end -->\n"
HISTORY = "# Decisions\n\n## 19 October 2026\n\nAn existing decision.\n\n"
PAGE = HISTORY + BEGIN + END


class DecisionPages(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.folder = Path(self.temp.name)

    def entry(self, name, text):
        (self.folder / name).write_text(text, encoding="utf-8")

    def test_filename_order_and_one_heading_per_day(self):
        self.entry("2026-11-01-later.md", "- The next month.\n")
        self.entry("2026-10-20-z-last.md", "- The last entry that day.\n")
        self.entry("2026-10-20-a-first.md", "- The first entry that day.\n")
        expected = (HISTORY + BEGIN + "\n## 20 October 2026\n\n"
                    "- The first entry that day.\n\n- The last entry that day.\n\n"
                    "## 1 November 2026\n\n- The next month.\n\n" + END)
        self.assertEqual(render.decisions_page(PAGE, self.folder), expected)
        self.assertEqual(render.decisions_page(expected, self.folder), expected)

    def test_heading_before_the_markers_is_not_repeated(self):
        self.entry("2026-10-19-another.md", "- Another decision.\n")
        expected = HISTORY + BEGIN + "\n- Another decision.\n\n" + END
        self.assertEqual(render.decisions_page(PAGE, self.folder), expected)
        self.assertEqual(expected.count("## 19 October 2026"), 1)

    def test_empty_folder_leaves_the_page_byte_for_byte(self):
        self.assertEqual(render.decisions_page(PAGE, self.folder).encode(), PAGE.encode())
        self.entry("README.md", "# Decision entries\n")
        self.assertEqual(render.decisions_page(PAGE, self.folder).encode(), PAGE.encode())

    def test_removing_the_last_entry_clears_only_the_generated_region(self):
        stale = HISTORY + BEGIN + "\n- A removed entry.\n\n" + END
        self.assertEqual(render.decisions_page(stale, self.folder), PAGE)

    def test_bad_markers_refused(self):
        for text in (HISTORY, HISTORY + END + BEGIN, PAGE + BEGIN,
                     PAGE + END, PAGE + "\nLater text.\n", HISTORY + BEGIN):
            with self.subTest(text=text), self.assertRaisesRegex(SystemExit, "markers"):
                render.decisions_page(text, self.folder)

    def test_bad_filename_or_date_refused(self):
        for name in ("notes.md", "2026-10-20-.md", "2026-02-30-date.md"):
            with self.subTest(name=name):
                self.entry(name, "- A decision.\n")
                with self.assertRaisesRegex(SystemExit, "expected|invalid date"):
                    render.decisions_page(PAGE, self.folder)
                (self.folder / name).unlink()

    def test_empty_entry_or_date_heading_refused(self):
        name = "2026-10-20-test.md"
        for text in (" \n", "## 20 October 2026\n\n- A decision.\n",
                     "  ## 20 October 2026 ##\n\n- A decision.\n", BEGIN):
            with self.subTest(text=text):
                self.entry(name, text)
                with self.assertRaisesRegex(SystemExit, "entry text"):
                    render.decisions_page(PAGE, self.folder)

    def test_missing_folder_unreadable_entry_and_symlink_refused(self):
        with self.assertRaises(OSError):
            render.decisions_page(PAGE, self.folder / "missing")
        path = self.folder / "2026-10-20-test.md"
        path.write_bytes(b"\xff")
        with self.assertRaises(UnicodeError):
            render.decisions_page(PAGE, self.folder)
        path.unlink()
        path.symlink_to(self.folder / "missing")
        with self.assertRaisesRegex(SystemExit, "regular file"):
            render.decisions_page(PAGE, self.folder)


if __name__ == "__main__":
    unittest.main()
