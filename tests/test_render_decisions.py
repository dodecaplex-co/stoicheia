#!/usr/bin/env python3
"""Decision entries assembled in filename order, with dates supplied by the renderer.

    python3 -I tests/test_render_decisions.py

Standard library only; no Lean or network.
"""

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

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
        self.root = Path(self.temp.name).resolve()
        self.folder = self.root / "docs" / "decisions"
        self.folder.mkdir(parents=True)
        root = mock.patch.object(render, "ROOT", self.root)
        root.start()
        self.addCleanup(root.stop)

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

    def test_indented_and_closed_date_headings_are_not_repeated(self):
        self.entry("2026-10-19-another.md", "- Another decision.\n")
        for heading in ("  ## 19 October 2026", "## 19 October 2026 ##",
                        "   ##\t19 October 2026 ### \t"):
            with self.subTest(heading=heading):
                history = HISTORY.replace("## 19 October 2026", heading)
                expected = history + BEGIN + "\n- Another decision.\n\n" + END
                self.assertEqual(render.decisions_page(history + BEGIN + END, self.folder),
                                 expected)

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

    def test_missing_folder_is_no_entries(self):
        self.assertEqual(render.decisions_page(PAGE, self.folder / "missing"), PAGE)

    def test_a_file_or_link_in_the_folder_s_place_refused(self):
        (self.folder / "file").write_text("x\n")
        with self.assertRaisesRegex(SystemExit, "a folder of entry files"):
            render.decisions_page(PAGE, self.folder / "file")
        (self.folder / "link").symlink_to(self.folder)
        with self.assertRaisesRegex(SystemExit, "a folder of entry files"):
            render.decisions_page(PAGE, self.folder / "link")

    def test_folder_under_a_link_is_refused_even_when_missing(self):
        self.entry("2026-10-20-test.md", "- A decision.\n")
        link = self.root / "docs"
        link.rename(self.root / "real-docs")
        link.symlink_to(self.root / "real-docs", target_is_directory=True)
        for name in ("decisions", "missing"):
            with self.subTest(name=name), self.assertRaisesRegex(SystemExit, "symlink"):
                render.decisions_page(PAGE, link / name)

    def test_count_markers_in_entries_are_refused(self):
        for marker in ("<!-- count:vocabulary -->0<!-- /count -->",
                       "<!-- count:vocabulary:Word -->None<!-- /count -->",
                       "<!-- count:vocabulary -->", "<!-- /count -->",
                       "<!-- count: vocabulary -->0<!-- /count -->"):
            with self.subTest(marker=marker):
                self.entry("2026-10-20-test.md", f"- {marker} words.\n")
                with self.assertRaisesRegex(SystemExit, "count marker|count closing marker"):
                    render.decisions_page(PAGE, self.folder)

    def test_count_marker_refusal_precedes_all_renderer_writes(self):
        self.entry("2026-10-20-test.md", "- <!-- count:vocabulary -->0<!-- /count --> words.\n")
        decisions = self.root / "docs" / "briefs" / "0002-decisions.md"
        decisions.parent.mkdir()
        decisions.write_text(PAGE, encoding="utf-8")
        pending = self.root / "pending.md"
        pending.write_text("<!-- count:vocabulary -->0<!-- /count -->\n", encoding="utf-8")
        paths = [pending, decisions, self.folder / "2026-10-20-test.md"]
        before = {path: path.read_bytes() for path in paths}
        with (mock.patch.object(render, "DECISIONS", decisions),
              mock.patch.object(render, "DECISION_ENTRIES", self.folder),
              mock.patch.object(render.generated_counts, "tracked_markdown",
                                return_value=[p.relative_to(self.root) for p in paths]),
              mock.patch.dict(render.generated_counts.COUNTS, {"vocabulary": lambda root: 42}),
              mock.patch.object(render, "write_text") as write,
              mock.patch.object(render, "load_facts") as facts,
              contextlib.redirect_stdout(io.StringIO())):
            with self.assertRaisesRegex(SystemExit, "count markers.*dated history"):
                render.main()
            write.assert_not_called()
            facts.assert_not_called()
        self.assertEqual({path: path.read_bytes() for path in paths}, before)

    def test_relative_links_must_start_with_parent_folder(self):
        for target in ("README.md", "./README.md", "#decision", "?view=1", "",
                       "/docs/WORKFLOW.md", "./../../scripts/render.py"):
            for entry in (f"- [the rules]({target})\n",
                          f"- [the rules](\n  {target})\n",
                          f"- [the rules][rules]\n\n[rules]: <{target}>\n",
                          f"- [the rules][rules]\n\n[rules]:\n  <{target}>\n",
                          f'- <a href="{target}">the rules</a>\n'):
                with self.subTest(entry=entry):
                    self.entry("2026-10-20-test.md", entry)
                    with self.assertRaisesRegex(SystemExit, "relative links must start with"):
                        render.decisions_page(PAGE, self.folder)

    def test_parent_folder_and_external_links_are_kept(self):
        entry = ("- [the rules](../WORKFLOW.md#4-files-and-ownership), "
                 "[the renderer][render], [a site](https://example.invalid/), "
                 "[mail](mailto:reader@example.invalid), "
                 "[another site](//example.invalid/), "
                 "[wrapped](\n  ../WORKFLOW.md).\n\n"
                 "[render]:\n  ../../scripts/render.py\n")
        self.entry("2026-10-20-test.md", entry)
        expected = HISTORY + BEGIN + "\n## 20 October 2026\n\n" + entry + "\n" + END
        self.assertEqual(render.decisions_page(PAGE, self.folder), expected)

    def test_unreadable_entry_and_symlink_refused(self):
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
