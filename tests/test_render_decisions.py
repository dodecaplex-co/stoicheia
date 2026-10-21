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

    def test_heading_omitted_only_after_that_date_s_own_heading(self):
        self.entry("2026-10-19-another.md", "- Another decision.\n")
        for history in (HISTORY + "## Other notes\n\nA note.\n\n",
                         HISTORY + "- ### A heading in a list item\n\n",
                         HISTORY + "### 19 October 2026\n\n"):
            with self.subTest(history=history):
                expected = (history + BEGIN + "\n## 19 October 2026\n\n- Another decision.\n\n"
                            + END)
                self.assertEqual(render.decisions_page(history + BEGIN + END, self.folder),
                                 expected)
        setext = "# Decisions\n\n19 October 2026\n---------------\n\nAn existing decision.\n\n"
        self.assertEqual(render.decisions_page(setext + BEGIN + END, self.folder),
                         setext + BEGIN + "\n- Another decision.\n\n" + END)
        fenced = HISTORY + "```\n## 18 October 2026\n```\n\n"
        self.assertEqual(render.decisions_page(fenced + BEGIN + END, self.folder),
                         fenced + BEGIN + "\n- Another decision.\n\n" + END)

    def test_an_entry_s_own_heading_brings_back_the_date_heading(self):
        self.entry("2026-10-20-a-first.md", "- The first.\n\n### Its details\n\nMore.\n")
        self.entry("2026-10-20-b-second.md", "- The second.\n")
        self.assertEqual(render.decisions_page(PAGE, self.folder),
                         HISTORY + BEGIN + "\n## 20 October 2026\n\n- The first.\n\n"
                         "### Its details\n\nMore.\n\n## 20 October 2026\n\n- The second.\n\n"
                         + END)

    def test_text_after_the_end_marker_is_kept_after_the_entries(self):
        later = "\n- **A page entry written after the markers.** It stays here.\n"
        self.entry("2026-10-20-test.md", "- A decision.\n")
        expected = (HISTORY + BEGIN + "\n## 20 October 2026\n\n- A decision.\n\n" + END
                    + later)
        self.assertEqual(render.decisions_page(PAGE + later, self.folder), expected)
        self.assertEqual(render.decisions_page(expected, self.folder), expected)
        (self.folder / "2026-10-20-test.md").unlink()
        self.assertEqual(render.decisions_page(expected, self.folder), PAGE + later)

    def test_bad_markers_refused(self):
        for text in (HISTORY, HISTORY + END + BEGIN, PAGE + BEGIN, PAGE + END,
                     HISTORY + BEGIN, HISTORY + " " + BEGIN + END,
                     HISTORY + BEGIN + END.rstrip("\n") + " Later text.\n"):
            with self.subTest(text=text), self.assertRaisesRegex(SystemExit, "markers"):
                render.decisions_page(text, self.folder)

    def test_page_text_left_open_before_the_markers_refused(self):
        for opened in ("```\n", "~~~~\n", "<!-- an open comment\n"):
            with self.subTest(opened=opened):
                with self.assertRaisesRegex(SystemExit, "would hide the entries"):
                    render.decisions_page(HISTORY + opened + "\n" + BEGIN + END, self.folder)

    def test_entry_left_open_refused_before_later_entries(self):
        for text in ("- A decision.\n\n```\ncode\n", "- A decision.\n\n~~~~\ncode\n~~~\n",
                     "```python\ncode\n~~~\n", "````\ncode\n```\n",
                     "- A decision. <!-- an open comment\n", "- A decision. <!-->\n",
                     "<!--\n```\n-->\n```\n", "<!--\n\n```\n-->\n```\n",
                     "<div>\n```\n</div>\n\n```\n", "- ```\n  code\n```\n",
                     "> ```\n> code\n", "- x\n\n   ```\n   code\n   ```\n", "- x\n\n\t```\n",
                     "```a`b\n```\n", "<pre>\nkept\n</pre>\n", "<script>\n",
                     "<STYLE>x</STYLE>\n", "<textarea>\n", "<?php\n", "<!DOCTYPE html>\n",
                     "<![CDATA[\n", "<details>\n\n- A decision, folded.\n",
                     "- A <b>bold decision.\n", "- A decision.</div>\n",
                     "<div><details></div></details>\n",
                     "- The `<details>` in code is read too.\n"):
            with self.subTest(text=text):
                self.entry("2026-10-20-a-open.md", text)
                self.entry("2026-10-21-b-later.md", "- A later decision.\n")
                with self.assertRaisesRegex(SystemExit, "2026-10-20-a-open.md: the entry "
                                            "leaves .* which would hide what follows"):
                    render.decisions_page(PAGE, self.folder)

    def test_closed_blocks_are_kept(self):
        entry = ("- A decision with code.\n\n```\n## 20 October 2026\n~~~\n```\n\n"
                 "~~~~ text\n```\n~~~~\n\n<!-- a note\nover lines -->\n\n<div>\nA box.\n"
                 "</div>\n\n<details><summary>More</summary>\n\nText<br>, <br/> and "
                 "<img src=../a.png alt=x />.\n\n</details>\n")
        self.entry("2026-10-20-test.md", entry)
        self.entry("2026-10-21-later.md", "- A later decision.\n")
        expected = (HISTORY + BEGIN + "\n## 20 October 2026\n\n" + entry
                    + "\n## 21 October 2026\n\n- A later decision.\n\n" + END)
        self.assertEqual(render.decisions_page(PAGE, self.folder), expected)

    def test_entry_starts_at_the_margin(self):
        for text in ("  continued from the entry before\n", "    indented code\n",
                     "\tindented code\n"):
            with self.subTest(text=text):
                self.entry("2026-10-20-test.md", text)
                with self.assertRaisesRegex(SystemExit, "starts at the margin"):
                    render.decisions_page(PAGE, self.folder)

    def test_reference_and_footnote_definitions_refused(self):
        for text in ("- [the rules][rules]\n\n[rules]: ../WORKFLOW.md\n",
                     "- [rules]\n\n  [rules]: ../STYLE.md\n",
                     "- [the rules][rules]\n\n- [rules]: ../WORKFLOW.md\n",
                     "> [rules]: ../WORKFLOW.md\n",
                     "- [the rules][the\nrules]\n\n[the\nrules]: ../WORKFLOW.md\n",
                     "- A note.[^1]\n\n[^1]: The note.\n"):
            with self.subTest(text=text):
                self.entry("2026-10-20-test.md", text)
                with self.assertRaisesRegex(SystemExit, "reference or footnote definition"):
                    render.decisions_page(PAGE, self.folder)

    def test_definitions_in_two_entries_cannot_rebind_each_other(self):
        self.entry("2026-10-20-a-first.md", "- See [rules].\n\n[rules]: ../WORKFLOW.md\n")
        self.entry("2026-10-20-b-second.md", "- See [Rules].\n\n[RULES]: ../STYLE.md\n")
        with self.assertRaisesRegex(SystemExit, "2026-10-20-a-first.md:3: a reference"):
            render.decisions_page(PAGE, self.folder)
        self.entry("2026-10-20-a-first.md", "- See [rules].\n")
        with self.assertRaisesRegex(SystemExit, "2026-10-20-b-second.md:3: a reference"):
            render.decisions_page(PAGE, self.folder)

    def test_labels_the_page_defines_refused_in_entries(self):
        for page in (HISTORY + "[The  Rules]: ../WORKFLOW.md\n\n" + BEGIN + END,
                     PAGE + "\n[the rules]: ../WORKFLOW.md\n"):
            for text in ("- See [the rules].\n", "- See [them][the\nRULES].\n"):
                with self.subTest(page=page, text=text):
                    self.entry("2026-10-20-test.md", text)
                    with self.assertRaisesRegex(SystemExit, r"\[the rules\] is a label the "
                                                "decisions page's own text defines"):
                        render.decisions_page(page, self.folder)

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
                       "/docs/WORKFLOW.md", "./../../scripts/render.py",
                       "2026-10-19-another-entry.md"):
            for entry in (f"- [the rules]({target})\n",
                          f"- [the rules](\n  {target})\n",
                          f'- <a href="{target}">the rules</a>\n',
                          f"- <a href='{target}'>the rules</a>\n",
                          f"- <img alt=x src = '{target}'>\n",
                          f'- <A\n  HREF="{target}">the rules</A>\n',
                          f"- `<a href='{target}'>x</a>` in code is refused too\n"):
                with self.subTest(entry=entry):
                    self.entry("2026-10-20-test.md", entry)
                    with self.assertRaisesRegex(SystemExit, "relative links must start with"):
                        render.decisions_page(PAGE, self.folder)

    def test_unquoted_html_attributes_are_read(self):
        for entry in ("- <a href=README.md>the rules</a>\n",
                      "- <a href=2026-10-19-another-entry.md>the other entry</a>\n",
                      "- <a title=x href=#decision>an anchor</a>\n",
                      "- <img src=figure.svg>\n", "- <a href = README.md>spaced</a>\n",
                      "- <a href=&#46;/README.md>an escaped dot</a>\n",
                      "- <svg><a xlink:href=README.md>x</a></svg>\n",
                      "- <img srcset='../ok.png 1x, figure.png 2x'>\n",
                      "- <a ping='../ok.html README.md'>x</a>\n",
                      "- <a href=>empty</a>\n", "- <form action=README.md></form>\n"):
            with self.subTest(entry=entry):
                self.entry("2026-10-20-test.md", entry)
                with self.assertRaisesRegex(SystemExit, "relative links must start with"):
                    render.decisions_page(PAGE, self.folder)

    def test_parent_folder_and_external_links_are_kept(self):
        entry = ("- [the rules](../WORKFLOW.md#4-files-and-ownership), "
                 "[a site](https://example.invalid/), "
                 "[mail](mailto:reader@example.invalid), "
                 "[another site](//example.invalid/), "
                 "[wrapped](\n  ../WORKFLOW.md), "
                 "[another entry](../decisions/2026-10-19-another-entry.md), "
                 "<a href=../STYLE.md>bare</a>, <a href='../STYLE.md'>single</a>, "
                 '<a href="../STYLE.md">double</a>, <a href=https://example.invalid/>web</a>, '
                 "<img srcset='../a.png 1x, ../b.png 2x' alt=x>.\n")
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
