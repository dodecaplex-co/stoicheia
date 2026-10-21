#!/usr/bin/env python3
"""The checks render.py makes of docs/decisions/, the dated decision entries, each a page
of its own, before it writes anything; and that render.py, run whole on a copy of the
sources, assembles no entry into another page and leaves the decisions record as it was.

    python3 -I tests/test_decision_entries.py

Standard library only; no Lean or network. scripts/negative_tests.py runs it beside the
count regressions, so CI's `negative` job and the pre-flight run it on every pull request.
"""

import contextlib
import io
import os
import subprocess
import sys
import tempfile
import unittest
import uuid
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import render  # noqa: E402
import safe_push  # noqa: E402


class DecisionEntries(unittest.TestCase):
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
        path = self.folder / name
        if isinstance(text, bytes):
            path.write_bytes(text)
        else:
            path.write_text(text, encoding="utf-8", newline="")
        return path

    def refused(self, pattern):
        return self.assertRaisesRegex(SystemExit, pattern)

    def test_entries_are_pages_read_where_they_are(self):
        self.entry("README.md", "# Decision entries\n\nEach decision is a file.\n")
        self.entry("2026-11-01-later.md", "- **The next month.** A decision.\n")
        self.entry("2026-10-20-b-second.md", "- **The second.** A decision.\n")
        self.entry("2026-10-20-a-first.md",
                   "## 20 October 2026\n\n- **The first.** A decision.\n\n### Its details\n\n"
                   "More, with [a link](../WORKFLOW.md) and [another](README.md).\n")
        before = {path: path.read_bytes() for path in self.folder.iterdir()}
        self.assertEqual(render.decision_entries(), ["2026-10-20-a-first.md",
                                                     "2026-10-20-b-second.md",
                                                     "2026-11-01-later.md"])
        self.assertEqual({path: path.read_bytes() for path in self.folder.iterdir()}, before)

    def test_missing_or_empty_folder_is_no_entries(self):
        self.assertEqual(render.decision_entries(), [])
        self.folder.rmdir()
        self.assertEqual(render.decision_entries(), [])

    def test_bad_names_and_dates_refused(self):
        for name in ("notes.md", "2026-10-20-.md", "2026-10-20-Case.md", "2026-10-20-a_b.md",
                     "2026-10-20-test.txt", "26-10-20-test.md", "readme.md", "README.MD",
                     ".DS_Store", "2026-10-20-test.md~"):
            with self.subTest(name=name):
                self.entry(name, "- A decision.\n")
                with self.refused(f"docs/decisions/{name}: expected README.md or an entry"):
                    render.decision_entries()
                (self.folder / name).unlink()
        for name in ("2026-02-30-date.md", "2026-13-01-month.md", "0000-01-01-year.md"):
            with self.subTest(name=name):
                self.entry(name, "- A decision.\n")
                with self.refused(f"docs/decisions/{name}: invalid date"):
                    render.decision_entries()
                (self.folder / name).unlink()

    def test_only_regular_files_the_readme_included(self):
        target = self.root / "elsewhere.md"
        target.write_text("- A decision.\n")
        for name in ("README.md", "2026-10-20-test.md"):
            with self.subTest(name=name):
                (self.folder / name).symlink_to(target)
                with self.refused(f"docs/decisions/{name}: expected a regular file"):
                    render.decision_entries()
                (self.folder / name).unlink()
        (self.folder / "2026-10-20-folder.md").mkdir()
        with self.refused("docs/decisions/2026-10-20-folder.md: expected a regular file"):
            render.decision_entries()

    def test_a_file_or_link_in_the_folder_s_place_refused(self):
        self.folder.rmdir()
        self.folder.write_text("- A decision.\n")
        with self.refused("docs/decisions: expected a folder of entry files"):
            render.decision_entries()
        self.folder.unlink()
        (self.root / "real").mkdir()
        self.folder.symlink_to(self.root / "real", target_is_directory=True)
        with self.refused("docs/decisions: expected a folder of entry files: .*symlink"):
            render.decision_entries()

    def test_folder_under_a_link_refused_even_when_missing(self):
        self.entry("2026-10-20-test.md", "- A decision.\n")
        docs = self.root / "docs"
        docs.rename(self.root / "real-docs")
        docs.symlink_to(self.root / "real-docs", target_is_directory=True)
        with self.refused("symlink"):
            render.decision_entries()
        (self.root / "real-docs" / "decisions" / "2026-10-20-test.md").unlink()
        (self.root / "real-docs" / "decisions").rmdir()
        with self.refused("symlink"):
            render.decision_entries()

    def test_folder_spelled_otherwise_refused(self):
        # On a file system that ignores case, docs/decisions finds docs/Decisions/; where
        # case counts, docs/decisions is missing. Refused either way, as Git would hold it.
        other = self.root / "docs" / "Decisions"
        self.folder.rename(other)
        (other / "2026-10-21-case.md").write_text("- A decision.\n")
        with self.refused("spelled on disk as docs/Decisions;"):
            render.decision_entries()
        # Where case counts, a second spelling beside the folder is refused too.
        try:
            self.folder.mkdir()
        except FileExistsError:
            return
        with self.refused("spelled on disk as docs/Decisions, docs/decisions"):
            render.decision_entries()

    def test_entry_not_utf8_refused_naming_the_file(self):
        for name in ("2026-10-20-test.md", "README.md"):
            with self.subTest(name=name):
                path = self.entry(name, b"- A decision \xff.\n")
                with self.refused(f"^docs/decisions/{name}: not UTF-8 text \\(byte 13"):
                    render.decision_entries()
                path.unlink()

    def test_count_markers_refused_in_entries_and_the_readme(self):
        for name in ("2026-10-20-test.md", "README.md"):
            for marker in ("<!-- count:vocabulary -->0<!-- /count -->",
                           "<!-- count:vocabulary:Word -->None<!-- /count -->",
                           "<!-- count:vocabulary -->", "<!-- /count -->",
                           "<!-- count: vocabulary -->0<!-- /count -->"):
                with self.subTest(name=name, marker=marker):
                    path = self.entry(name, f"- A decision.\n- {marker} words.\n")
                    with self.refused(f"docs/decisions/{name}:2: .*count .*marker.*"
                                      "forbidden in dated history"):
                        render.decision_entries()
                    path.unlink()

    def test_count_marker_refusal_precedes_all_renderer_writes(self):
        entry = self.entry("2026-10-20-test.md",
                           "- <!-- count:vocabulary -->0<!-- /count --> words.\n")
        pending = self.root / "pending.md"
        pending.write_text("<!-- count:vocabulary -->0<!-- /count -->\n", encoding="utf-8")
        paths = [pending, entry]
        before = {path: path.read_bytes() for path in paths}
        with (mock.patch.object(render.generated_counts, "tracked_markdown",
                                return_value=[p.relative_to(self.root) for p in paths]),
              mock.patch.dict(render.generated_counts.COUNTS, {"vocabulary": lambda root: 42}),
              mock.patch.object(render, "write_text") as write,
              mock.patch.object(render, "load_facts") as facts,
              contextlib.redirect_stdout(io.StringIO())):
            with self.refused("count markers are forbidden in dated history"):
                render.main()
            write.assert_not_called()
            facts.assert_not_called()
        self.assertEqual({path: path.read_bytes() for path in paths}, before)

    def test_empty_entry_refused(self):
        for text in ("", "\n", " \n\t\n"):
            with self.subTest(text=text):
                self.entry("2026-10-20-test.md", text)
                with self.refused("docs/decisions/2026-10-20-test.md: expected the entry's"):
                    render.decision_entries()

    def test_invisible_characters_refused(self):
        line = "- **A decision.** It names `scripts/check_style.py`.\n"
        for char, name in (("\r", "U\\+000D"), ("\x0c", "U\\+000C"), ("\x00", "U\\+0000"),
                           ("\x85", "U\\+0085"), ("\u2028", "LINE SEPARATOR"),
                           ("\u2029", "PARAGRAPH SEPARATOR"), ("\u200b", "ZERO WIDTH SPACE"),
                           ("\ufeff", "ZERO WIDTH NO-BREAK SPACE"), ("\u00ad", "SOFT HYPHEN"),
                           ("\u2060", "WORD JOINER"), ("\u202e", "RIGHT-TO-LEFT OVERRIDE"),
                           ("\u034f", "COMBINING GRAPHEME JOINER"), ("\u3164", "HANGUL FILLER"),
                           ("\ufe0f", "VARIATION SELECTOR-16"),
                           ("\U000e0041", "TAG LATIN CAPITAL LETTER A")):
            for text in (char + line, line.replace(" ", char + " ", 1),
                         line + line.replace("\n", char + "\n")):
                with self.subTest(char=hex(ord(char)), text=text):
                    self.entry("2026-10-20-test.md", text)
                    number = 2 if text.startswith(line) else 1
                    with self.refused(f"docs/decisions/2026-10-20-test.md:{number}: "
                                      f".*{name}.*: an entry holds no control character"):
                        render.decision_entries()
        self.entry("2026-10-20-test.md", line.replace("\n", "\r\n"))
        with self.refused("2026-10-20-test.md:1: U\\+000D: an entry holds no control"):
            render.decision_entries()

    def test_ordinary_text_is_kept(self):
        # Spaces of other widths and the Braille pattern blank are kept: safe_push.py reads
        # each as a space when it compares an entry with the record (safe_push.skeleton).
        self.entry("2026-10-20-test.md",
                   "- **Στοιχεῖα, naïve and café.**\tA tab, a no-break\u00a0space, an "
                   "em space\u2003, a Braille blank\u2800and ✓ marks are text.\n")
        self.assertEqual(render.decision_entries(), ["2026-10-20-test.md"])
        self.assertEqual(safe_push.record_line("a\u00a0b\u2003c\u2800d"), "a b c d")

    def test_render_and_safe_push_refuse_the_same_characters(self):
        differ = [hex(n) for n in range(0x110000)
                  if render.invisible(chr(n)) != safe_push.invisible(chr(n))]
        self.assertEqual(differ, [])


class RenderLeavesTheRecord(unittest.TestCase):
    """render.py, run whole on a copy of the sources, reads the entries where they are:
    it assembles them into no page, and writes nothing into the decisions record."""

    def test_render_assembles_no_entry_and_leaves_the_record_as_it_was(self):
        from negative_tests import count_source_copy

        # Words found in no file of the sources, this one included, until they are planted.
        words = [f"entry-{uuid.uuid4().hex}" for _ in range(2)]
        with count_source_copy() as (root, env):
            folder = root / "docs" / "decisions"
            entries = {
                folder / "2026-10-22-render-first.md":
                    f"- **A first decision for the test ({words[0]}).** It links "
                    "[the renderer](../../scripts/render.py) and [the page]"
                    "(../briefs/0002-decisions.md).\n",
                folder / "2026-10-23-render-second.md":
                    "- **A second decision for the test.** It holds a heading.\n\n"
                    f"## {words[1]}\n\nAnd more words under it.\n",
            }
            for path, text in entries.items():
                path.write_text(text, encoding="utf-8")
            record = [root / "docs" / "briefs" / "0002-decisions.md", folder / "README.md",
                      *entries]
            self.assertTrue(all(path.is_file() for path in record))
            before = {path: path.read_bytes() for path in record}
            names = sorted(os.listdir(folder))
            result = subprocess.run([sys.executable, "scripts/render.py"], cwd=root, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn(f"decision entries: {len(entries)} checked in docs/decisions/",
                          result.stdout)
            self.assertIn("rendered book pages", result.stdout)
            self.assertEqual({path: path.read_bytes() for path in record}, before)
            self.assertEqual(sorted(os.listdir(folder)), names)
            holding = sorted(path.relative_to(root).as_posix() for path in root.rglob("*")
                             if path.is_file() and path not in entries
                             and any(word.encode() in path.read_bytes() for word in words))
            self.assertEqual(holding, [])


if __name__ == "__main__":
    unittest.main()
