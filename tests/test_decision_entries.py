#!/usr/bin/env python3
"""The checks render.py makes of docs/decisions/, the dated decision entries, each a page
of its own, before it writes anything, passing over the files Git ignores by a rule of the
root's .gitignore, .git/info/exclude or the user's excludes file, never a nested
.gitignore's; and that render.py, run whole on a copy of the sources, assembles no entry
without a header into another page and leaves the decisions record as it was. Then the
header line an entry may begin with, each of its refusals, and the notes regions of the
briefs and of PROGRAM.md that render.py fills from the headers: their lines, their markers'
refusals and the refusal of a region holding a line render.py does not write, which come
before any write, and a whole run on a copy, once rendered, that a headed entry changes in
no file, then, with markers planted, one brief, between its markers, and nothing else.

    python3 -I tests/test_decision_entries.py

Standard library and Git only; no Lean or network. Each case's folder is in a Git
repository of its own, read with no configuration or excludes file but its own.
scripts/negative_tests.py runs it beside the count regressions, so CI's `negative` job runs
it on every push to main and on a pull request of class R3 and above
(scripts/risk.py), the cadence every six hours on main, and the pre-flight on every pull
request of R3 and above.
"""

import contextlib
import io
import os
import re
import subprocess
import sys
import tempfile
import time
import unittest
import uuid
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import heath  # noqa: E402
import render  # noqa: E402
import safe_push  # noqa: E402


def git_environment(home):
    """The environment, for Git, of a repository of a test's own: none named by GIT_DIR or
    the like, and no configuration or excludes file but the repository's, so that what
    Git ignores is what the test says (`home` stands for the user's home)."""
    env = {name: value for name, value in os.environ.items() if not name.startswith("GIT_")}
    return {**env, "HOME": str(home), "XDG_CONFIG_HOME": str(home / ".config"),
            "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_CEILING_DIRECTORIES": str(home.parent)}


class EntryFolder(unittest.TestCase):
    """A repository of a test's own, with an empty docs/decisions/, as render.py's root."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve() / "repository"
        self.folder = self.root / "docs" / "decisions"
        self.folder.mkdir(parents=True)
        home = Path(self.temp.name).resolve() / "home"
        home.mkdir()
        environment = mock.patch.dict(os.environ, git_environment(home), clear=True)
        environment.start()
        self.addCleanup(environment.stop)
        self.git("init", "-q")
        root = mock.patch.object(render, "ROOT", self.root)
        root.start()
        self.addCleanup(root.stop)

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.root, check=True, capture_output=True)

    def entry(self, name, text):
        path = self.folder / name
        if isinstance(text, bytes):
            path.write_bytes(text)
        else:
            path.write_text(text, encoding="utf-8", newline="")
        return path

    def refused(self, pattern):
        return self.assertRaisesRegex(SystemExit, pattern)


class DecisionEntries(EntryFolder):
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

    def test_no_entry_dated_before_the_first(self):
        # The entries began on 20 October 2026. The working tree has no commit, so no date
        # is too late here: the pre-flight bounds it by the commit's (safe_push.py).
        self.assertEqual(render.FIRST_ENTRY, safe_push.FIRST_ENTRY)
        for name in ("2026-10-19-early.md", "1900-01-01-old.md", "0001-01-01-first-year.md"):
            with self.subTest(name=name):
                self.entry(name, "- A decision.\n")
                with self.refused(f"^docs/decisions/{name}: dated before 2026-10-20, the day "
                                  "the entries began$"):
                    render.decision_entries()
                (self.folder / name).unlink()
        for name in ("2026-10-20-first.md", "9999-12-31-last-word.md"):
            self.entry(name, "- A decision.\n")
        self.assertEqual(render.decision_entries(),
                         ["2026-10-20-first.md", "9999-12-31-last-word.md"])

    def test_files_git_ignores_are_passed_over(self):
        # Finder's .DS_Store and an editor's backup, ignored by the repository's rules, are
        # no part of the record: Git never commits them. A file the rules do not cover is
        # refused as before, and so is one they cover that is tracked, which Git commits.
        (self.root / ".gitignore").write_text(".DS_Store\n*~\n.idea/\n")
        self.entry("2026-10-20-test.md", "- A decision.\n")
        self.entry(".DS_Store", b"\x00\x00\x00\x01Bud1")
        self.entry("2026-10-20-test.md~", "- A decision, as it was.\r\n")
        (self.folder / ".idea").mkdir()
        self.assertEqual(render.decision_entries(), ["2026-10-20-test.md"])
        self.entry("notes.md", "- Notes.\n")
        with self.refused("^docs/decisions/notes.md: expected README.md or an entry"):
            render.decision_entries()
        (self.folder / "notes.md").unlink()
        self.git("add", "-f", "--", "docs/decisions/.DS_Store")
        with self.refused("^docs/decisions/.DS_Store: expected README.md or an entry"):
            render.decision_entries()

    def test_only_the_root_ignore_rules_and_the_users_pass_a_file_over(self):
        # A rule of a nested .gitignore, which a commit may add beside the folder or in it,
        # passes nothing over (the security re-review's case); nor does a negated rule. A
        # rule of the root's .gitignore, of .git/info/exclude, of core.excludesFile or of
        # Git's default excludes file does.
        self.entry("2026-10-20-test.md", "- A decision.\n")
        self.entry("notes.md", "- Notes.\n")
        nested = self.root / "docs" / ".gitignore"
        for rules in ("decisions/notes.md\n", "*.md\n"):
            with self.subTest(rules=rules):
                nested.write_text(rules)
                with self.refused("^docs/decisions/notes.md: expected README.md or an entry"):
                    render.decision_entries()
        nested.unlink()
        inside = self.entry(".gitignore", "*\n")
        with self.refused("^docs/decisions/.gitignore: expected README.md or an entry"):
            render.decision_entries()
        inside.unlink()
        (self.root / ".gitignore").write_text("notes.md\n")
        nested.write_text("!decisions/notes.md\n")
        with self.refused("^docs/decisions/notes.md: expected README.md or an entry"):
            render.decision_entries()
        nested.unlink()
        self.assertEqual(render.decision_entries(), ["2026-10-20-test.md"])
        (self.root / ".gitignore").unlink()
        home = Path(os.environ["HOME"])
        exclude = self.root / ".git" / "info" / "exclude"
        configured = home / "excludes"
        default = home / ".config" / "git" / "ignore"
        default.parent.mkdir(parents=True)
        for path, setting in ((exclude, None), (configured, str(configured)),
                              (home / "tilde", "~/tilde"), (default, None)):
            with self.subTest(path=path.name):
                path.write_text("notes.md\n")
                if setting:
                    self.git("config", "core.excludesFile", setting)
                self.assertEqual(render.decision_entries(), ["2026-10-20-test.md"])
                path.unlink()
                if setting:
                    self.git("config", "--unset", "core.excludesFile")
                with self.refused("^docs/decisions/notes.md: expected README.md or an entry"):
                    render.decision_entries()

    def test_git_must_say_what_it_ignores(self):
        # Where Git cannot be run, finds no repository, finds one whose work tree is not
        # the root, or cannot read its index, nothing is passed over: render.py stops.
        self.entry("2026-10-20-test.md", "- A decision.\n")
        with mock.patch.object(render.subprocess, "run", side_effect=FileNotFoundError("git")):
            with self.refused("^docs/decisions: cannot ask Git which files it ignores"):
                render.decision_entries()
        elsewhere = self.root.parent / "elsewhere"
        elsewhere.mkdir()
        with mock.patch.dict(os.environ, {"GIT_DIR": str(self.root / ".git"),
                                          "GIT_WORK_TREE": str(elsewhere)}):
            with self.refused("^docs/decisions: Git's work tree .*elsewhere is not the "
                              "repository root"):
                render.decision_entries()
        (self.root / ".git" / "index").write_bytes(b"not an index")
        with self.refused("^docs/decisions: git check-ignore failed: "):
            render.decision_entries()
        (self.root / ".git").rename(self.root / "git-metadata")
        with self.refused("^docs/decisions: cannot ask Git which files it ignores"):
            render.decision_entries()

    def test_git_naming_a_file_it_was_not_asked_about_stops_render(self):
        # Or answering otherwise than in fours: a rule's source, its line, its pattern and
        # the file.
        self.entry("2026-10-20-test.md", "- A decision.\n")
        run = subprocess.run
        for out, why in ((b".gitignore\x001\x00other\x00docs/decisions/other\x00",
                          "named a file it was not asked about"),
                         (b"docs/decisions/2026-10-20-test.md\x00",
                          "answered in a form it was not asked for"),
                         (b".gitignore\x001\x00x\x00docs/decisions/2026-10-20-test.md",
                          "answered in a form it was not asked for")):
            def answer(command, **kwargs):
                if "check-ignore" in command:
                    return subprocess.CompletedProcess(command, 0, out, b"")
                return run(command, **kwargs)

            with self.subTest(out=out):
                with mock.patch.object(render.subprocess, "run", side_effect=answer):
                    with self.refused(f"^docs/decisions: git check-ignore {why}$"):
                        render.decision_entries()

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
        # A long s (U+017F) casefolds to an s, so a Mac's file system finds docs/deciſions/
        # there too.
        long_s = self.root / "docs" / "deciſions"
        other.rename(long_s)
        with self.refused("spelled on disk as docs/deciſions;"):
            render.decision_entries()
        long_s.rename(other)
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
                           ("\U000e0041", "TAG LATIN CAPITAL LETTER A"),
                           ("\u2800", "BRAILLE PATTERN BLANK"),
                           ("\U0001d159", "MUSICAL SYMBOL NULL NOTEHEAD"),
                           ("\U00016fe4", "KHITAN SMALL SCRIPT FILLER"),
                           ("\ue000", "U\\+E000"), ("\u0378", "U\\+0378")):
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

    def test_readme_holds_no_hidden_character(self):
        # The README is held to an entry's characters, though it may be empty and is no
        # entry, as the pre-flight holds it (safe_push.entry_changes).
        for char, name in (("\u200b", "ZERO WIDTH SPACE"),
                           ("\U0001d159", "MUSICAL SYMBOL NULL NOTEHEAD"), ("\r", "U\\+000D")):
            with self.subTest(char=hex(ord(char))):
                self.entry("README.md", f"# Decision entries\n\nEach{char} decision.\n")
                with self.refused(f"^docs/decisions/README.md:3: .*{name}.*: the README holds "
                                  "no control character"):
                    render.decision_entries()
        self.entry("README.md", "")
        self.assertEqual(render.decision_entries(), [])

    def test_ordinary_text_is_kept(self):
        # Spaces of other widths are kept: safe_push.py reads each as a space when it
        # compares an entry with the record (safe_push.skeleton). The Braille pattern blank,
        # which it reads so too, renders blank and is no white space, so an entry may not
        # hold it (test_invisible_characters_refused); the decisions page may.
        self.entry("2026-10-20-test.md",
                   "- **Στοιχεῖα, naïve and café.**\tA tab, a no-break\u00a0space, an "
                   "em space\u2003, and ✓ marks are text.\n")
        self.assertEqual(render.decision_entries(), ["2026-10-20-test.md"])
        self.assertEqual(safe_push.record_line("a\u00a0b\u2003c\u2800d"), "a b c d")

    def test_refusals_print_names_with_escapes(self):
        # A name holding an escape sequence, a bell or a bidirectional mark is printed with
        # each written as an escape, so that a refusal gives a terminal nothing to act on.
        for name, shown in (("notes\x1b[31m.md", "notes\\\\x1b\\[31m\\.md"),
                            ("2026-10-20-\u202etest.md", "2026-10-20-\\\\u202etest\\.md"),
                            ("\x07bell.md", "\\\\x07bell\\.md")):
            with self.subTest(name=ascii(name)):
                path = self.entry(name, "- A decision.\n")
                with self.assertRaises(SystemExit) as caught:
                    render.decision_entries()
                message = str(caught.exception)
                self.assertRegex(message, f"^docs/decisions/{shown}: expected README.md or an "
                                          "entry")
                self.assertEqual([c for c in message if not c.isprintable()], [])
                path.unlink()

    def test_render_and_safe_push_refuse_the_same_characters(self):
        differ = [hex(n) for n in range(0x110000)
                  if render.invisible(chr(n)) != safe_push.invisible(chr(n))]
        self.assertEqual(differ, [])
        self.assertEqual(render.BLANK_GLYPHS, safe_push.BLANK_GLYPHS)


class RenderLeavesTheRecord(unittest.TestCase):
    """render.py, run whole on a copy of the sources, reads the entries where they are:
    it assembles them into no page, and writes nothing into the decisions record."""

    def test_render_assembles_no_entry_and_leaves_the_record_as_it_was(self):
        # Run as the folder stands, and with a real entry besides the two planted (#242):
        # render.py checks every entry in the folder, so the count it reports is the folder's
        # entries and the planted ones, read from the folder, never the planted ones alone.
        for besides in (False, True):
            with self.subTest(a_real_entry_besides=besides):
                self.render_leaves_the_record(besides)

    def render_leaves_the_record(self, besides):
        from negative_tests import count_source_copy

        # Words found in no file of the sources, this one included, until they are planted.
        words = [f"entry-{uuid.uuid4().hex}" for _ in range(2)]
        with count_source_copy() as (root, env):
            folder = root / "docs" / "decisions"
            if besides:
                self.assertFalse((folder / "2026-10-21-render-real.md").exists())
                (folder / "2026-10-21-render-real.md").write_text(
                    "- **A decision already in the folder, for the test.** It stands as an "
                    "entry main holds would.\n", encoding="utf-8")
            existing = sorted(path for path in folder.iterdir()
                              if path.suffix == ".md" and path.name != "README.md")
            if besides:
                self.assertIn(folder / "2026-10-21-render-real.md", existing)
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
                self.assertFalse(path.exists(), path)
                path.write_text(text, encoding="utf-8")
            record = [root / "docs" / "briefs" / "0002-decisions.md", folder / "README.md",
                      *existing, *entries]
            self.assertTrue(all(path.is_file() for path in record))
            before = {path: path.read_bytes() for path in record}
            names = sorted(os.listdir(folder))
            result = subprocess.run([sys.executable, "scripts/render.py"], cwd=root, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn(f"decision entries: {len(existing) + len(entries)} checked in "
                          "docs/decisions/", result.stdout)
            self.assertIn("rendered book pages", result.stdout)
            self.assertEqual({path: path.read_bytes() for path in record}, before)
            self.assertEqual(sorted(os.listdir(folder)), names)
            holding = sorted(path.relative_to(root).as_posix() for path in root.rglob("*")
                             if path.is_file() and path not in entries
                             and any(word.encode() in path.read_bytes() for word in words))
            self.assertEqual(holding, [])


ISSUE = "https://github.com/dodecaplex-co/stoicheia/issues/"


def header(*keys, line="News."):
    """An entry's header line: `keys` as written, then the line."""
    return "<!-- entry: " + " ".join(keys) + f' line="{line}" -->'


class HeaderFolder(EntryFolder):
    """An entry folder beside three briefs, the decisions page among them."""

    def setUp(self):
        super().setUp()
        briefs = self.root / "docs" / "briefs"
        briefs.mkdir()
        for stem in ("0002-decisions", "0008-centre", "book-I"):
            (briefs / f"{stem}.md").write_text(f"# {stem}\n", encoding="utf-8")

    def headed(self, name, first, rest="- **A decision.** Words.\n"):
        return self.entry(name, first + "\n" + rest)

    def headers(self):
        return render.entry_headers(render.decision_entries())


class EntryHeaders(HeaderFolder):
    def test_a_header_with_every_key(self):
        self.entry("2026-10-25-old.md", "- **An old decision.** Words.\n")
        self.headed("2026-10-26-older.md", header("id=older", "cards=5"))
        line = "x" * render.ENTRY_LINE_LIMIT
        self.headed("2026-10-27-full.md", header(
            "id=full-2", "cards=577,12", "briefs=0008-centre,book-I",
            "program=landed", "corrects=2026-10-25-old.md",
            "reverts=2026-10-26-older.md,2026-10-25-old.md",
            "removes=Elements.Tacit.area_congruent,Elements.Old.«term∠___»,Elements.«a.b»",
            line=line))
        self.assertEqual(self.headers()["2026-10-27-full.md"], {
            "id": "full-2", "cards": [577, 12], "briefs": ["0008-centre", "book-I"],
            "program": ["landed"], "corrects": ["2026-10-25-old.md"],
            "reverts": ["2026-10-26-older.md", "2026-10-25-old.md"],
            "removes": ["Elements.Tacit.area_congruent", "Elements.Old.«term∠___»",
                        "Elements.«a.b»"],
            "line": line})

    def test_a_header_of_the_longest_length_is_read(self):
        # A header of ENTRY_HEADER_LIMIT characters is read; one character more is refused
        # before it is parsed.
        base = len(header("id=", "cards=1"))
        longest = header("id=" + "a" * (render.ENTRY_HEADER_LIMIT - base), "cards=1")
        self.assertEqual(len(longest), render.ENTRY_HEADER_LIMIT)
        self.headed("2026-10-27-long.md", longest)
        self.assertEqual(self.headers()["2026-10-27-long.md"]["cards"], [1])
        self.headed("2026-10-27-long.md", longest.replace("id=a", "id=aa", 1))
        with self.refused("^docs/decisions/2026-10-27-long\\.md:1: a header is 2,000 "
                          "characters at most, not 2,001$"):
            self.headers()

    def test_only_the_required_keys_and_no_header(self):
        self.headed("2026-10-27-a.md", header("id=a", "cards=1", line="News, of a kind."))
        self.entry("2026-10-27-b.md", "- **No header.** An entry may have none.\n")
        self.assertEqual(self.headers(), {"2026-10-27-a.md": {
            "id": "a", "cards": [1], "briefs": [], "program": [], "corrects": [],
            "reverts": [], "removes": [], "line": "News, of a kind."}})

    def test_each_refusal(self):
        self.entry("2026-10-26-earlier.md", "- **Earlier.** Words.\n")
        good = 'id=a cards=1 line="x" -->'
        cases = (
            ('<!-- entry: id=a cards=1 colour=red line="x" -->', "unknown key 'colour'"),
            ('<!-- entry: cards=1 id=a line="x" -->', "the key 'id' is out of order"),
            ('<!-- entry: id=a cards=1 program=landed briefs=book-I line="x" -->',
             "the key 'briefs' is out of order"),
            ('<!-- entry: id=a cards=1 cards=2 line="x" -->', "the key 'cards' is given twice"),
            ('<!-- entry: id=a cards=1 line="x" line="y" -->', "the line holds no \""),
            ('<!-- entry: id=a  cards=1 line="x" -->', "single spaces separate"),
            ('<!-- entry:  id=a cards=1 line="x" -->', "single spaces separate"),
            ('<!-- entry:id=a cards=1 line="x" -->', "single spaces separate"),
            ('<!-- entry: id=a cards=1 line="x"  -->', "single spaces separate"),
            ('<!-- entry: id=a cards=1 line="x"-->', "single spaces separate"),
            ('<!-- entry: id=a cards=1 line="x"', "line 1 holds no --> to close the header"),
            ('<!-- entry: id=a cards=1 line="x"\n-->', "line 1 holds no --> to close"),
            ('<!-- entry: id=a cards=1 line="x" --> More.', "text after the header's -->"),
            ('<!-- entry: id=a cards=1 line="x" --> ', "text after the header's -->"),
            ("<!--entry: " + good, 'a header begins "<!-- entry:" exactly'),
            ("<!-- Entry: " + good, 'a header begins "<!-- entry:" exactly'),
            ("<!-- entry " + good, 'a header begins "<!-- entry:" exactly'),
            ("<!-- entry_typo: " + good, 'a header begins "<!-- entry:" exactly'),
            ('<!-- entry: id=a cards=1 news line="x" -->', "expected key=value, not 'news'"),
            ('<!-- entry: ID=a cards=1 line="x" -->', "unknown key 'ID'"),
            ('<!-- entry: cards=1 line="x" -->', "the key 'id' is required"),
            ('<!-- entry: id=a line="x" -->', "the key 'cards' is required"),
            ("<!-- entry: id=a cards=1 -->", "the key 'line' is required"),
            ("<!-- entry: -->", "the key 'id' is required"),
            ('<!-- entry: id=a cards=1 line="x" briefs=book-I -->', "the line comes last"),
            ("<!-- entry: id=a cards=1 line=x -->", "the line comes last"),
            ('<!-- entry: id=A cards=1 line="x" -->', "the id 'A' is not lower-case letters"),
            ('<!-- entry: id=a_b cards=1 line="x" -->', "the id 'a_b' is not lower-case"),
            ('<!-- entry: id=a- cards=1 line="x" -->', "the id 'a-' is not lower-case"),
            ('<!-- entry: id= cards=1 line="x" -->', "the id '' is not lower-case"),
            ('<!-- entry: id=a cards=0 line="x" -->', "the card '0' is not an issue number"),
            ('<!-- entry: id=a cards=07 line="x" -->', "the card '07' is not an issue"),
            ('<!-- entry: id=a cards=#5 line="x" -->', "the card '#5' is not an issue"),
            ('<!-- entry: id=a cards=5,5 line="x" -->', "cards names '5' twice"),
            ('<!-- entry: id=a cards= line="x" -->', "cards is a list joined by commas, "
                                                    "with no empty item"),
            ('<!-- entry: id=a cards=5, line="x" -->', "cards is a list joined by commas"),
            ('<!-- entry: id=a cards=1 briefs=0099-none line="x" -->',
             "no brief docs/briefs/0099-none.md"),
            ('<!-- entry: id=a cards=1 briefs=book-I.md line="x" -->',
             "no brief docs/briefs/book-I.md.md"),
            ('<!-- entry: id=a cards=1 briefs=0002-decisions line="x" -->',
             "the decisions page, 0002-decisions, is dated history and holds no notes"),
            ('<!-- entry: id=a cards=1 briefs=book-I,book-I line="x" -->',
             "briefs names 'book-I' twice"),
            ('<!-- entry: id=a cards=1 program=status line="x" -->',
             "unknown PROGRAM.md section 'status'; the sections that hold notes are "
             "landed"),
            ('<!-- entry: id=a cards=1 program=open-items line="x" -->',
             "unknown PROGRAM.md section 'open-items'; the sections that hold notes are "
             "landed"),
            ('<!-- entry: id=a cards=1 program=Landed line="x" -->',
             "unknown PROGRAM.md section 'Landed'"),
            ('<!-- entry: id=a cards=1 program=landed,landed line="x" -->',
             "program names 'landed' twice"),
            ('<!-- entry: id=a cards=1 corrects=2026-10-26-earlier.md,2026-10-26-earlier.md '
             'line="x" -->', "corrects names '2026-10-26-earlier.md' twice"),
            ('<!-- entry: id=a cards=1 removes=Elements.a reverts=2026-10-26-earlier.md '
             'line="x" -->', "the key 'reverts' is out of order"),
            ('<!-- entry: id=a cards=1 removes=Tacit.area_congruent line="x" -->',
             "removes 'Tacit.area_congruent': a removed name is a Lean name in full, under "
             "Elements"),
            ('<!-- entry: id=a cards=1 removes=Elements line="x" -->',
             "removes 'Elements': a removed name is a Lean name in full"),
            ('<!-- entry: id=a cards=1 removes=Elements..a line="x" -->',
             "removes 'Elements..a': a removed name is a Lean name in full"),
            ('<!-- entry: id=a cards=1 removes=Elements.a=b line="x" -->',
             "removes 'Elements.a=b': a removed name is a Lean name in full"),
            ('<!-- entry: id=a cards=1 removes=Elements.1a line="x" -->',
             "removes 'Elements.1a': a removed name is a Lean name in full"),
            ('<!-- entry: id=a cards=1 removes=Elements.«a«b» line="x" -->',
             "removes 'Elements.«a«b»': a removed name is a Lean name in full"),
            ('<!-- entry: id=a cards=1 removes=Elements.«» line="x" -->',
             "removes 'Elements.«»': a removed name is a Lean name in full"),
            ('<!-- entry: id=a cards=1 removes=Other.x line="x" -->',
             "removes 'Other.x': a removed name is a Lean name in full, under Elements"),
            ('<!-- entry: id=a cards=1 removes=Elements.a,Elements.a line="x" -->',
             "removes names 'Elements.a' twice"),
            ('<!-- entry: id=a cards=1 removes=Elements.a, line="x" -->',
             "removes is a list joined by commas, with no empty item"),
            ('<!-- entry: id=a cards=1 line="" -->', "the line is 1 to 300 characters, not 0"),
            (header("id=a", "cards=1", line="x" * 301), "the line is 1 to 300 characters, "
                                                         "not 301"),
            (header("id=a", "cards=1", line=" x"), "the line has no space at its start"),
            (header("id=a", "cards=1", line="x "), "the line has no space at its start"),
            (header("id=a", "cards=1", line='a "b" c'), 'the line holds no "'),
            (header("id=a", "cards=1", line="a <!-- b"), "the line holds no <!-- or -->"),
            (header("id=a", "cards=1", line="a --> b"), "the line holds no <!-- or -->"),
            (header("id=a", "cards=1", "removes=Elements.a", line="a --!> b"),
             "a header holds no comment terminator before its final -->"),
            (header("id=a", "cards=1", line="see [it](../x.md)"),
             "the line holds no Markdown link"),
            # Raw HTML, which could hide text or link to a file, and a bracket, which could
            # bind to a link the page it is copied into defines (PROGRAM.md defines [#1]).
            *((header("id=a", "cards=1", line=f"a {form} b"), "the line holds no <, [ or ]: "
               "raw HTML could hide text or link to a file")
              for form in ("<b>bold</b>", "<?hidden?>", "<!x hidden>",
                           "<a href=../../SECRET.md>here</a>", "<details>folded</details>",
                           "<https://example.com>", "[#1]", "[it][#1]", "[x", "x]")),
            ("<!-- entry: colour=" + "x" * render.ENTRY_HEADER_LIMIT + " -->",
             f"a header is 2,000 characters at most, not "
             f"{render.ENTRY_HEADER_LIMIT + len('<!-- entry: colour= -->'):,}"),
            (" " + header("id=a", "cards=1"), "an entry's header is its line 1"),
            (header("id=a", "cards=1") + header("id=b", "cards=2"),
             "an entry's header is its line 1, and it has one at most"),
            (header("id=a", "cards=1", line="see <!-- entry"), "an entry's header is its line"),
        )
        for first, message in cases:
            with self.subTest(header=first):
                self.headed("2026-10-27-test.md", first)
                with self.refused("^docs/decisions/2026-10-27-test\\.md:1: "
                                  + re.escape(message)):
                    self.headers()
        for text, number in ((header("id=a", "cards=1") + "\n\n" + header("id=b", "cards=2")
                              + "\n", 3),
                             ("- **A decision.**\n" + header("id=a", "cards=1") + "\n", 2),
                             ("- **A decision.** <!--  ENTRY: in passing -->\n", 1)):
            with self.subTest(text=text):
                self.entry("2026-10-27-test.md", text)
                with self.refused(f"^docs/decisions/2026-10-27-test\\.md:{number}: an "
                                  "entry's header is its line 1, and it has one at most$"):
                    self.headers()

    def test_refusals_print_what_they_quote_with_escapes(self):
        # A no-break space passes decision_entries, which keeps it as text; a refusal that
        # quotes it writes it as an escape (printable_text).
        self.headed("2026-10-27-test.md", header("id=a", "cards=1", "briefs=book I"))
        self.assertEqual(render.decision_entries(), ["2026-10-27-test.md"])
        with self.assertRaises(SystemExit) as caught:
            self.headers()
        self.assertEqual(str(caught.exception), "docs/decisions/2026-10-27-test.md:1: no brief "
                                                "docs/briefs/book\\xa0I.md")

    def test_removed_names_are_lean_names_as_the_released_names_check_reads_them(self):
        import check_released_names
        good = ("Elements.a", "Elements.Tacit.area_congruent", "Elements.«a.b»",
                "Elements.Old.«term∠___»", "Elements.x'", "Elements.get!", "Elements.α₁",
                "Elements.ℕ.x", "Elements._x", "Elements.é", "Elements.Ā", "Elements.aⱼ",
                "Elements.«a,b»", "Elements.«a b»")
        bad = ("Elements", "Other.x", "elements.x", "Elements..x", "Elements.x.",
               "Elements.a=b", "Elements.1a", "Elements.λ", "Elements.«»", "Elements.«a«b»",
               "Elements.«a\nb»", "Elements.a-b", "Elements.«a.b", "Elements.ⱼ",
               "Elements.×", "Elements.÷")
        first = header("id=a", "cards=1", "removes=" + ",".join(good))
        parsed = render.entry_header("2026-10-27-test.md", first + "\n", [], [])
        self.assertEqual(parsed["removes"], list(good))
        self.assertEqual(check_released_names.removes_of(first + "\n"), list(good))
        for name in bad:
            with self.subTest(name=name):
                first = header("id=a", "cards=1", f"removes={name}")
                with self.assertRaises(SystemExit):
                    render.entry_header("2026-10-27-test.md", first + "\n", [], [])
                self.assertEqual(check_released_names.removes_of(first + "\n"), [])

    def test_a_comment_unsafe_removed_name_has_an_exact_encoded_form(self):
        import check_released_names
        for name in ("Elements.«a-->b»", "Elements.«a--!>b»"):
            with self.subTest(name=name):
                encoded = "utf8hex:" + name.encode("utf-8").hex()
                first = header("id=a", "cards=1", f"removes={encoded}")
                parsed = render.entry_header("2026-10-27-test.md", first + "\n", [], [])
                self.assertEqual(parsed["removes"], [name])
                self.assertEqual(check_released_names.removes_of(first + "\n"), [name])

                unsafe = header("id=a", "cards=1", f"removes={name}")
                with self.assertRaises(SystemExit):
                    render.entry_header("2026-10-27-test.md", unsafe + "\n", [], [])
                self.assertEqual(check_released_names.removes_of(unsafe + "\n"), [])

    def test_malformed_removed_name_encodings_are_refused_by_both_readers(self):
        import check_released_names
        cases = ("utf8hex:", "utf8hex:0", "utf8hex:zz", "utf8hex:ff",
                 "utf8hex:" + "Other.x".encode("utf-8").hex())
        for encoded in cases:
            with self.subTest(encoded=encoded):
                first = header("id=a", "cards=1", f"removes={encoded}")
                with self.assertRaises(SystemExit):
                    render.entry_header("2026-10-27-test.md", first + "\n", [], [])
                self.assertEqual(check_released_names.removes_of(first + "\n"), [])

    def test_removed_name_duplicates_are_compared_after_decoding(self):
        name = "Elements.a"
        encoded = "utf8hex:" + name.encode("utf-8").hex()
        first = header("id=a", "cards=1", f"removes={name},{encoded}")
        with self.assertRaises(SystemExit) as caught:
            render.entry_header("2026-10-27-test.md", first + "\n", [], [])
        self.assertIn("removes names 'Elements.a' twice", str(caught.exception))

    def test_ids_are_unique(self):
        self.headed("2026-10-26-a.md", header("id=same", "cards=1"))
        self.headed("2026-10-27-b.md", header("id=other", "cards=2"))
        self.headed("2026-10-27-c.md", header("id=same", "cards=3"))
        with self.refused("^docs/decisions/2026-10-27-c\\.md:1: the id 'same' is the id of "
                          "docs/decisions/2026-10-26-a\\.md too; an id is unique$"):
            self.headers()

    def test_a_correction_or_revert_names_an_earlier_entry(self):
        self.entry("2026-10-26-a.md", "- **No header.** An old entry may be corrected.\n")
        self.headed("2026-10-27-b.md", header("id=b", "cards=2"))
        self.entry("README.md", "# Decision entries\n")
        for key in ("corrects", "reverts"):
            with self.subTest(key=key, named="earlier"):
                self.headed("2026-10-27-c.md", header(
                    "id=c", "cards=3", f"{key}=2026-10-26-a.md,2026-10-27-b.md"))
                self.assertEqual(self.headers()["2026-10-27-c.md"][key],
                                 ["2026-10-26-a.md", "2026-10-27-b.md"])
            self.headed("2026-10-28-d.md", header("id=d", "cards=4"))
            for named in ("2026-10-27-c.md", "2026-10-28-d.md", "2026-10-20-none.md",
                          "README.md", "2026-10-26-a", "../decisions/2026-10-26-a.md"):
                with self.subTest(key=key, named=named):
                    self.headed("2026-10-27-c.md", header("id=c", "cards=3", f"{key}={named}"))
                    with self.refused(f"^docs/decisions/2026-10-27-c\\.md:1: {key} "
                                      f"{re.escape(repr(named))}: a correction or revert "
                                      "must name an earlier entry$"):
                        self.headers()
            (self.folder / "2026-10-28-d.md").unlink()
        # Name order is date order, then slug: of two entries of one day, the first slug.
        self.headed("2026-10-27-c.md", header("id=c", "cards=3"))
        self.headed("2026-10-27-a.md", header("id=a", "cards=1", "corrects=2026-10-27-c.md"))
        with self.refused("a correction or revert must name an earlier entry"):
            self.headers()


class NotesRegions(HeaderFolder):
    """The notes regions render.py fills: their lines, and their markers' refusals."""

    def setUp(self):
        super().setUp()
        self.briefs = self.root / "docs" / "briefs"
        self.program = self.root / "docs" / "PROGRAM.md"
        self.program.write_text("# Programme\n\n<!-- status -->\n| table |\n<!-- /status -->\n",
                                encoding="utf-8")

    def brief(self, stem, text):
        path = self.briefs / f"{stem}.md"
        path.write_text(text, encoding="utf-8")
        return path

    def filled(self, headers=None, changes=None):
        headers = self.headers() if headers is None else headers
        return render.notes_updates(headers, changes or {})

    def test_lines_are_sorted_however_the_entries_are_written(self):
        path = self.brief("0008-centre", "# Centre\n\nBefore.\n\n<!-- notes -->\n"
                                         "<!-- /notes -->\n\nAfter.\n")
        written = [("2026-10-27-third.md", header("id=third", "cards=577",
                                                  "briefs=0008-centre", line="Third news.")),
                   ("2026-10-21-first.md", header("id=first", "cards=12",
                                                  "briefs=book-I,0008-centre",
                                                  line="First news.")),
                   ("2026-10-26-elsewhere.md", header("id=elsewhere", "cards=9",
                                                      "briefs=book-I", "program=landed")),
                   ("2026-10-26-second.md", header("id=second", "cards=100,20",
                                                   "briefs=0008-centre",
                                                   line="Second news, with `code`."))]
        for name, first in written:
            self.headed(name, first)
        self.entry("2026-10-25-plain.md", "- **No header.** Never in a region.\n")
        lines = [f"- 21 October 2026, [#12]({ISSUE}12): First news. "
                 "([the entry](../decisions/2026-10-21-first.md))",
                 f"- 26 October 2026, [#20]({ISSUE}20), [#100]({ISSUE}100): Second news, with "
                 "`code`. ([the entry](../decisions/2026-10-26-second.md))",
                 f"- 27 October 2026, [#577]({ISSUE}577): Third news. "
                 "([the entry](../decisions/2026-10-27-third.md))"]
        want = ("# Centre\n\nBefore.\n\n<!-- notes -->\n" + "\n".join(lines)
                + "\n<!-- /notes -->\n\nAfter.\n")
        headers = self.headers()
        shuffled = dict(reversed(list(headers.items())))
        self.assertNotEqual(list(shuffled), list(headers))
        for given in (headers, shuffled):
            with self.subTest(order=list(given)):
                self.assertEqual(self.filled(given), ({path: want}, 1, 1))
        # Filled again, the region is the same: nothing changes.
        path.write_text(want, encoding="utf-8")
        self.assertEqual(self.filled(), ({}, 1, 1))

    def test_entries_of_one_day_stand_in_name_order(self):
        # Two entries of one day in one region, written in the reverse of their names'
        # order: the line of the slug that sorts first stands first.
        path = self.brief("0008-centre", "# Centre\n\n<!-- notes -->\n<!-- /notes -->\n")
        self.headed("2026-10-27-third.md", header("id=third", "cards=577",
                                                  "briefs=0008-centre", line="Third news."))
        self.headed("2026-10-27-second.md", header("id=second", "cards=578",
                                                   "briefs=0008-centre", line="Second news."))
        want = ("# Centre\n\n<!-- notes -->\n"
                f"- 27 October 2026, [#578]({ISSUE}578): Second news. "
                "([the entry](../decisions/2026-10-27-second.md))\n"
                f"- 27 October 2026, [#577]({ISSUE}577): Third news. "
                "([the entry](../decisions/2026-10-27-third.md))\n<!-- /notes -->\n")
        headers = self.headers()
        shuffled = dict(reversed(list(headers.items())))
        self.assertEqual(list(shuffled), ["2026-10-27-third.md", "2026-10-27-second.md"])
        for given in (headers, shuffled):
            with self.subTest(order=list(given)):
                self.assertEqual(self.filled(given), ({path: want}, 1, 1))

    def test_a_page_without_markers_is_left_as_it_is(self):
        text = "# Book I\n\nNamed by an entry, but holding no markers.\n"
        path = self.brief("book-I", text)
        self.headed("2026-10-27-a.md", header("id=a", "cards=1", "briefs=book-I",
                                              "program=landed"))
        before = {p: p.read_bytes() for p in (path, self.program)}
        self.assertEqual(self.filled(), ({}, 0, 0))
        self.assertEqual({p: p.read_bytes() for p in before}, before)

    def test_the_program_regions(self):
        # PROGRAM.md's sections are `landed` alone, in the list render.py and the regions'
        # reader, heath.py, share.
        self.assertEqual(render.PROGRAM_NOTES, ("landed",))
        self.assertIs(render.PROGRAM_NOTES, heath.PROGRAM_NOTES)
        top = "# Programme\n\n<!-- status -->\n| table |\n<!-- /status -->\n\n### Landed\n\n"
        stale = (f"- 20 October 2026, [#6]({ISSUE}6): Stale news, replaced. "
                 "([the entry](decisions/2026-10-20-stale.md))")
        self.program.write_text(f"{top}<!-- notes:landed -->\n{stale}\n<!-- /notes:landed -->\n",
                                encoding="utf-8")
        self.headed("2026-10-20-stale.md", header("id=stale", "cards=6", "program=landed",
                                                  line="Stale news, replaced."))
        self.headed("2026-10-26-one.md", header("id=one", "cards=7", "program=landed",
                                                line="One news."))
        self.headed("2026-10-27-both.md", header("id=both", "cards=8", "briefs=book-I",
                                                 "program=landed", line="Both news."))
        one_line = (f"- 26 October 2026, [#7]({ISSUE}7): One news. "
                    "([the entry](decisions/2026-10-26-one.md))")
        both_line = (f"- 27 October 2026, [#8]({ISSUE}8): Both news. "
                     "([the entry](decisions/2026-10-27-both.md))")
        want = (f"{top}<!-- notes:landed -->\n{stale}\n{one_line}\n{both_line}\n"
                "<!-- /notes:landed -->\n")
        self.assertEqual(self.filled(), ({self.program: want}, 1, 1))
        # Two sections, each region filled with the entries that name it: `later` stands in
        # for a section a later card adds.
        self.program.write_text(
            f"{top}<!-- notes:landed -->\n{stale}\n<!-- /notes:landed -->\n\n### Later\n\n"
            "<!-- notes:later -->\n<!-- /notes:later -->\n", encoding="utf-8")
        with (mock.patch.object(render, "PROGRAM_NOTES", ("landed", "later")),
              mock.patch.object(heath, "PROGRAM_NOTES", ("landed", "later"))):
            self.headed("2026-10-26-one.md", header("id=one", "cards=7", "program=later",
                                                    line="One news."))
            self.headed("2026-10-27-both.md", header("id=both", "cards=8", "briefs=book-I",
                                                     "program=landed,later", line="Both news."))
            want = (f"{top}<!-- notes:landed -->\n{stale}\n{both_line}\n"
                    "<!-- /notes:landed -->\n\n"
                    f"### Later\n\n<!-- notes:later -->\n{one_line}\n{both_line}\n"
                    "<!-- /notes:later -->\n")
            self.assertEqual(self.filled(), ({self.program: want}, 2, 1))

    def test_program_page_writes_the_status_table_alone(self):
        # render.program_page writes the status table between the status markers, and gives
        # each notes region back byte for byte, for notes_updates to fill.
        text = ("# Programme\n\n<!-- status -->\n| old |\n<!-- /status -->\n\n### Landed\n\n"
                "<!-- notes:landed -->\n- A line.\n<!-- /notes:landed -->\n\nAfter.\n")
        with mock.patch.object(render, "status_table", return_value="| new |") as table:
            self.assertEqual(render.program_page(text, "facts", "records", "program"),
                             text.replace("| old |\n", "\n| new |\n\n"))
        table.assert_called_once_with("facts", "records", "program")

    def test_corrections_and_reverts_are_linked_both_ways(self):
        path = self.brief("book-I", "# Book I\n\n<!-- notes -->\n<!-- /notes -->\n")
        other = self.brief("0008-centre", "# Centre\n\n<!-- notes -->\n<!-- /notes -->\n")
        self.entry("2026-10-24-old.md", "- **No header.** An old entry.\n")
        self.headed("2026-10-25-a.md", header("id=a", "cards=1", "briefs=book-I", line="A."))
        self.headed("2026-10-26-b.md", header("id=b", "cards=2", "briefs=book-I",
                                              "corrects=2026-10-25-a.md", line="B."))
        self.headed("2026-10-27-c.md", header("id=c", "cards=3", "briefs=book-I",
                                              "reverts=2026-10-26-b.md", line="C."))
        self.headed("2026-10-27-d.md", header("id=d", "cards=4", "briefs=0008-centre",
                                              "corrects=2026-10-25-a.md,2026-10-24-old.md",
                                              "reverts=2026-10-26-b.md", line="D."))
        # A correction or revert is shown wherever the entry it names is, whatever region
        # the correcting entry names: D names another brief, and E names none.
        self.headed("2026-10-28-e.md", header("id=e", "cards=5", "reverts=2026-10-27-c.md",
                                              line="E."))

        def entry(name):
            return f"[the entry of {render.entry_day(name)}](../decisions/{name})"

        want = {
            path: "# Book I\n\n<!-- notes -->\n"
                  f"- 25 October 2026, [#1]({ISSUE}1): A. Corrected by "
                  f"{entry('2026-10-26-b.md')} and {entry('2026-10-27-d.md')}. "
                  "([the entry](../decisions/2026-10-25-a.md))\n"
                  f"- 26 October 2026, [#2]({ISSUE}2): B. Corrects {entry('2026-10-25-a.md')}."
                  f" Reverted by {entry('2026-10-27-c.md')} and {entry('2026-10-27-d.md')}. "
                  "([the entry](../decisions/2026-10-26-b.md))\n"
                  f"- 27 October 2026, [#3]({ISSUE}3): C. Reverts {entry('2026-10-26-b.md')}. "
                  f"Reverted by {entry('2026-10-28-e.md')}. "
                  "([the entry](../decisions/2026-10-27-c.md))\n<!-- /notes -->\n",
            other: "# Centre\n\n<!-- notes -->\n"
                   f"- 27 October 2026, [#4]({ISSUE}4): D. Corrects "
                   f"{entry('2026-10-24-old.md')} and {entry('2026-10-25-a.md')}. Reverts "
                   f"{entry('2026-10-26-b.md')}. ([the entry](../decisions/2026-10-27-d.md))\n"
                   "<!-- /notes -->\n"}
        self.assertEqual(entry("2026-10-24-old.md"),
                         "[the entry of 24 October 2026](../decisions/2026-10-24-old.md)")
        self.assertEqual(self.filled(), (want, 2, 2))

    def test_a_stale_line_may_lack_a_backlink_from_a_later_entry(self):
        path = self.brief("0008-centre", "# Centre\n\n<!-- notes -->\n"
                                         f"- 25 October 2026, [#1]({ISSUE}1): A. "
                                         "([the entry](../decisions/2026-10-25-a.md))\n"
                                         "<!-- /notes -->\n")
        self.headed("2026-10-25-a.md", header("id=a", "cards=1", "briefs=0008-centre",
                                              line="A."))
        self.headed("2026-10-26-b.md", header("id=b", "cards=2",
                                              "corrects=2026-10-25-a.md", line="B."))
        backlink = ("[the entry of 26 October 2026]"
                    "(../decisions/2026-10-26-b.md)")
        want = ("# Centre\n\n<!-- notes -->\n"
                f"- 25 October 2026, [#1]({ISSUE}1): A. Corrected by {backlink}. "
                "([the entry](../decisions/2026-10-25-a.md))\n<!-- /notes -->\n")
        self.assertEqual(self.filled(), ({path: want}, 1, 1))

    def test_a_region_no_header_names_stays_empty(self):
        self.headed("2026-10-27-a.md", header("id=a", "cards=1", "briefs=book-I"))
        path = self.brief("0008-centre", "# Centre\n\n<!-- notes -->\n<!-- /notes -->\n"
                                         "After.\n")
        self.assertEqual(self.filled(), ({}, 1, 1))

    def test_the_page_is_read_as_the_count_markers_leave_it(self):
        path = self.brief("book-I", "<!-- count:vocabulary -->0<!-- /count -->\n"
                                    "<!-- notes -->\n<!-- /notes -->\n")
        self.headed("2026-10-27-a.md", header("id=a", "cards=1", "briefs=book-I"))
        counted = "<!-- count:vocabulary -->42<!-- /count -->\n<!-- notes -->\n<!-- /notes -->\n"
        filled = self.filled(changes={path: counted})[0]
        self.assertTrue(filled[path].startswith("<!-- count:vocabulary -->42<!-- /count -->\n"
                                                "<!-- notes -->\n- 27 October 2026"))

    def test_marker_refusals(self):
        brief_cases = (
            ("<!--notes-->\n<!-- /notes -->\n", 1, "malformed notes marker"),
            ("<!-- NOTES -->\n<!-- /notes -->\n", 1, "malformed notes marker"),
            ("<!-- notes  -->\n<!-- /notes -->\n", 1, "malformed notes marker"),
            ("<!-- notes: -->\n<!-- /notes -->\n", 1, "malformed notes marker"),
            ("<!-- notes_typo -->\n<!-- /notes -->\n", 1, "malformed notes marker"),
            ("<!-- notes -->\n<!-- / notes -->\n", 2, "malformed notes marker"),
            ("<!-- notes, an ordinary comment -->\n", 1, "malformed notes marker"),
            ("<!-- notes\n-->\n<!-- /notes -->\n", 1, "malformed notes marker"),
            ("Text <!-- notes -->\n<!-- /notes -->\n", 1, "a notes marker stands on a line "
                                                         "of its own"),
            ("<!-- notes --> text\n<!-- /notes -->\n", 1, "a notes marker stands on a line "
                                                         "of its own"),
            ("<!-- notes -->\n<!-- /notes --> text\n", 2, "a notes marker stands on a line "
                                                         "of its own"),
            ("<!-- notes:landed -->\n<!-- /notes:landed -->\n", 1,
             "a brief's notes markers name no section"),
            ("<!-- /notes -->\n", 1, "notes closing marker has no opening marker"),
            ("x\n<!-- notes -->\n", 2, "unclosed notes marker"),
            ("<!-- notes -->\n<!-- notes -->\n<!-- /notes -->\n<!-- /notes -->\n", 2,
             "nested notes marker"),
            ("<!-- notes -->\n<!-- /notes -->\n\n<!-- notes -->\n<!-- /notes -->\n", 4,
             "repeated notes region; a brief holds one at most"),
        )
        status = "<!-- status -->\n| table |\n<!-- /status -->\n"
        program_cases = (
            ("<!-- notes -->\n<!-- /notes -->\n", 1,
             "a notes marker of docs/PROGRAM.md names its section"),
            ("<!-- notes:status -->\n<!-- /notes:status -->\n", 1,
             "unknown notes section 'status'; docs/PROGRAM.md's are landed"),
            ("<!-- notes:open-items -->\n<!-- /notes:open-items -->\n", 1,
             "unknown notes section 'open-items'; docs/PROGRAM.md's are landed"),
            ("<!-- notes:Landed -->\n<!-- /notes:Landed -->\n", 1, "malformed notes marker"),
            ("<!-- notes:landed -->\n<!-- /notes:open-items -->\n", 2,
             "unknown notes section 'open-items'; docs/PROGRAM.md's are landed"),
            ("<!-- notes:landed -->\n<!-- /notes:landed -->\n<!-- notes:landed -->\n"
             "<!-- /notes:landed -->\n", 3,
             "repeated notes region; section 'landed' has one at most"),
            ("<!-- notes:landed -->\n" + status + "<!-- /notes:landed -->\n", 1,
             "notes region 'landed' overlaps the status region"),
            ("<!-- status -->\n<!-- notes:landed -->\n<!-- /notes:landed -->\n"
             "<!-- /status -->\n", 2, "notes region 'landed' overlaps the status region"),
        )
        for rel, cases in (("docs/briefs/0008-centre.md", brief_cases),
                           ("docs/PROGRAM.md", program_cases)):
            path = self.root / rel
            for text, number, message in cases:
                with self.subTest(path=rel, text=text):
                    path.write_text(text, encoding="utf-8")
                    with self.refused("^notes regions: nothing was rendered:\n"
                                      f"{re.escape(rel)}:{number}: {re.escape(message)}$"):
                        self.filled()
            path.write_text("# Again as it was.\n", encoding="utf-8")
        # A region closed by another section's marker: `later` stands in for a section a
        # later card adds.
        with (mock.patch.object(heath, "PROGRAM_NOTES", ("landed", "later")),
              self.subTest(path="docs/PROGRAM.md", sections="landed, later")):
            self.program.write_text("<!-- notes:landed -->\n<!-- /notes:later -->\n",
                                    encoding="utf-8")
            with self.refused("^notes regions: nothing was rendered:\ndocs/PROGRAM.md:2: "
                              "notes closing marker does not close the region 'landed', "
                              "opened on line 1$"):
                self.filled()
        # A fault heath.fill finds past the notes markers, as a status region missing, is
        # named as render.py names it in the other generated pages.
        self.program.write_text("<!-- notes:landed -->\n<!-- /notes:landed -->\n",
                                encoding="utf-8")
        with self.refused("^notes regions: nothing was rendered:\ndocs/PROGRAM.md: no status "
                          "region: it must hold one status region; render.py writes between "
                          "these markers, so nothing was rendered$"):
            self.filled()
        self.program.write_text("# Again as it was.\n", encoding="utf-8")
        for text in ("<!-- notes -->\n<!-- /notes -->\n", "<!-- /notes -->\n"):
            with self.subTest(path="docs/briefs/0002-decisions.md", text=text):
                self.brief("0002-decisions", "# Decisions\n\n" + text)
                with self.refused("^notes regions: nothing was rendered:\n"
                                  "docs/briefs/0002-decisions.md:3: notes markers are "
                                  "forbidden in dated history$"):
                    self.filled()
        # Every page's fault is named, not the first alone.
        self.brief("book-I", "<!-- notes -->\n")
        self.program.write_text("<!-- notes -->\n<!-- /notes -->\n", encoding="utf-8")
        with self.assertRaises(SystemExit) as caught:
            self.filled()
        self.assertEqual(str(caught.exception).splitlines()[1:], [
            "docs/briefs/0002-decisions.md:3: notes markers are forbidden in dated history",
            "docs/briefs/book-I.md:1: unclosed notes marker",
            "docs/PROGRAM.md:1: a notes marker of docs/PROGRAM.md names its section"])

    def test_a_region_holds_only_the_lines_render_writes(self):
        # A misplaced marker never swallows text written by hand: a region whose body holds
        # a line render.py does not write is refused, naming its first such line, and the
        # page is left as it is.
        self.entry("2026-10-20-x.md", "- **X.** Earlier news.\n")
        self.entry("2026-10-21-y.md", "- **Y.** Other earlier news.\n")
        self.headed("2026-10-26-good.md", header(
            "id=good", "cards=5", "briefs=0008-centre", "program=landed",
            "corrects=2026-10-20-x.md", line="Good news."))
        good = (f"- 26 October 2026, [#5]({ISSUE}5): Good news. Corrects [the entry of 20 "
                "October 2026](../decisions/2026-10-20-x.md). "
                "([the entry](../decisions/2026-10-26-good.md))")
        authored = ("A paragraph written by hand, which the region would swallow.\n\n"
                    "Another, with [a link](../WORKFLOW.md).\n")
        cases = (
            ("authored paragraphs", authored, 4),
            ("a blank line", f"{good}\n\n", 5),
            ("a list item", f"{good}\n- An old status line.\n", 5),
            ("a space at the end", f"{good} \n", 4),
            ("a space after the colon", good.replace(": Good", ":  Good") + "\n", 4),
            ("a date not the entry's", good.replace("- 26 October", "- 27 October") + "\n", 4),
            ("a card linked elsewhere", good.replace("issues/5)", "issues/6)") + "\n", 4),
            ("cards out of order", good.replace(f"[#5]({ISSUE}5)",
                                                f"[#6]({ISSUE}6), [#5]({ISSUE}5)") + "\n", 4),
            ("a card twice", good.replace(f"[#5]({ISSUE}5)",
                                          f"[#5]({ISSUE}5), [#5]({ISSUE}5)") + "\n", 4),
            ("a link's day not its entry's", good.replace("of 20 October", "of 21 October")
             + "\n", 4),
            ("PROGRAM.md's links in a brief", good.replace("../decisions/", "decisions/")
             + "\n", 4),
            ("news holding <", good.replace("Good news.", "Good <b>news</b>.") + "\n", 4),
            ("news holding a quote", good.replace("Good news.", 'Good "news".') + "\n", 4),
            ("a day not in the calendar", good.replace("2026-10-26-good", "2026-02-30-good")
             + "\n", 4),
            ("an absent entry", good.replace("2026-10-26-good.md",
                                              "2026-10-26-absent.md") + "\n", 4),
            ("cards unlike the header", good.replace(f"[#5]({ISSUE}5)",
                                                       f"[#6]({ISSUE}6)") + "\n", 4),
            ("news unlike the header", good.replace("Good news.", "Other news.") + "\n", 4),
            ("an invented correction", good.replace("2026-10-20-x.md",
                                                      "2026-10-21-y.md") + "\n", 4),
            ("an invented backlink", good.replace("Corrects", "Corrected by") + "\n", 4),
        )
        self.assertEqual(render.notes_lines(self.headers(), ["2026-10-26-good.md"], "../"),
                         [good])
        for what, body, number in cases:
            with self.subTest(region=what):
                text = f"# Centre\n\n<!-- notes -->\n{body}<!-- /notes -->\nAfter.\n"
                path = self.brief("0008-centre", text)
                with self.refused("^notes regions: nothing was rendered:\n"
                                  f"docs/briefs/0008-centre\\.md:{number}: a notes region "
                                  "holds only the lines render\\.py writes, and this is not "
                                  "one; move the text written by hand, or the marker, so that "
                                  "the region does not swallow it$"):
                    self.filled()
                self.assertEqual(path.read_text(encoding="utf-8"), text)
        # In PROGRAM.md too, whose links lead to docs/ from docs/.
        self.brief("0008-centre", "# Centre\n\n<!-- notes -->\n<!-- /notes -->\n")
        top = "# Programme\n\n<!-- status -->\n| table |\n<!-- /status -->\n\n"
        for body, number in ((authored, 8), (good + "\n", 8),
                             (good.replace("../decisions/", "decisions/") + "\n- Old.\n", 9)):
            with self.subTest(page="docs/PROGRAM.md", body=body):
                text = f"{top}<!-- notes:landed -->\n{body}<!-- /notes:landed -->\n"
                self.program.write_text(text, encoding="utf-8")
                with self.refused(f"^notes regions: nothing was rendered:\ndocs/PROGRAM\\.md:"
                                  f"{number}: a notes region holds only the lines"):
                    self.filled()
                self.assertEqual(self.program.read_text(encoding="utf-8"), text)
        # A region that holds the lines a render wrote, or none, is filled.
        self.program.write_text(f"{top}<!-- notes:landed -->\n"
                                + good.replace("../decisions/", "decisions/")
                                + "\n<!-- /notes:landed -->\n", encoding="utf-8")
        self.brief("0008-centre", f"# Centre\n\n<!-- notes -->\n{good}\n<!-- /notes -->\n")
        filled, regions, pages = self.filled()
        self.assertEqual((len(filled), regions, pages), (0, 2, 2))

    def test_refusals_precede_all_renderer_writes(self):
        # A bad header, a bad notes marker, or a region around text written by hand, renders
        # nothing: no count is written, and no page is built.
        pending = self.root / "pending.md"
        pending.write_text("<!-- count:vocabulary -->0<!-- /count -->\n", encoding="utf-8")
        brief = self.brief("book-I", "# Book I\n\n<!-- notes -->\n<!-- /notes -->\n")
        for case in ("header", "marker", "authored", "canonical"):
            with self.subTest(case=case):
                if case == "header":
                    self.headed("2026-10-27-a.md", header("id=a", "cards=1", "briefs=book-II"))
                    message = "no brief docs/briefs/book-II.md"
                elif case == "marker":
                    self.headed("2026-10-27-a.md", header("id=a", "cards=1", "briefs=book-I"))
                    self.brief("0008-centre", "# Centre\n\n<!-- notes -->\n")
                    message = "docs/briefs/0008-centre.md:3: unclosed notes marker"
                elif case == "authored":
                    self.brief("0008-centre", "# Centre\n\n<!-- notes -->\nA paragraph written "
                                              "by hand.\n\nAnother.\n<!-- /notes -->\n")
                    message = ("docs/briefs/0008-centre.md:4: a notes region holds only the "
                               "lines render.py writes")
                else:
                    line = (f"- 27 October 2026, [#9]({ISSUE}9): Authored news. "
                            "([the entry](../decisions/2026-10-27-absent.md))")
                    self.brief("0008-centre", f"# Centre\n\n<!-- notes -->\n{line}\n"
                                              "<!-- /notes -->\n")
                    message = ("docs/briefs/0008-centre.md:4: a notes region holds only the "
                               "lines render.py writes")
                paths = [pending, brief, *self.briefs.iterdir(), self.program,
                         *self.folder.iterdir()]
                before = {path: path.read_bytes() for path in paths}
                with (mock.patch.object(render.generated_counts, "tracked_markdown",
                                        return_value=[pending.relative_to(self.root)]),
                      mock.patch.dict(render.generated_counts.COUNTS,
                                      {"vocabulary": lambda root: 42}),
                      mock.patch.object(render, "load_checks", return_value=[]),
                      mock.patch.object(render, "write_text") as write,
                      mock.patch.object(render, "load_facts") as facts,
                      contextlib.redirect_stdout(io.StringIO())):
                    with self.refused(re.escape(message)):
                        render.main()
                    write.assert_not_called()
                    facts.assert_not_called()
                self.assertEqual({path: path.read_bytes() for path in paths}, before)


class HeathReadsTheNotes(EntryFolder):
    """heath.py's one account of the generated regions reads the notes regions as it reads
    the others, in docs/PROGRAM.md beside its status region and in a brief: a hand edit
    inside a notes body is generated (heath.bodies) and leaves the part written by hand as
    it was (heath.outside); a marker deleted or bent is refused (heath.regions) and seen;
    and heath.fill names each region to its write and refuses a write that reaches outside
    a notes body. safe_push.py, which reads docs/PROGRAM.md through them, sees a changed
    notes body as a generated change, and reads a brief as written by hand whole."""

    PAGES = {
        "docs/PROGRAM.md": ("# Programme\n\n<!-- status -->\n| table |\n<!-- /status -->\n\n"
                            "### Landed\n\n<!-- notes:landed -->\n- One.\n- Two.\n"
                            "<!-- /notes:landed -->\n\nAfter.\n"),
        "docs/briefs/0008-centre.md": ("# Centre\n\nBefore.\n\n<!-- notes -->\n- One.\n- Two.\n"
                                       "<!-- /notes -->\n\nAfter.\n"),
    }
    NAMES = {"docs/PROGRAM.md": ["status", "notes:landed"],
             "docs/briefs/0008-centre.md": ["notes"]}

    def test_every_byte_is_generated_or_written_by_hand(self):
        for path, text in self.PAGES.items():
            with self.subTest(path=path):
                found = heath.regions(path, text)
                self.assertEqual([m["name"] for m in found], self.NAMES[path])
                bodies = heath.bodies(path, text)
                self.assertEqual([name for name, _ in bodies], self.NAMES[path])
                self.assertEqual(bodies[-1][1], "- One.\n- Two.\n")
                hand = text
                for m in reversed(found):
                    hand = hand[:m.start("body")] + hand[m.end("body"):]
                self.assertEqual(heath.outside(path, text), hand)
                self.assertEqual(len(hand) + sum(len(body) for _, body in bodies), len(text))
        # REGIONS is as it was: its keys the three files, none a folder, and PROGRAM.md's
        # pattern finds the status region alone.
        self.assertEqual(list(heath.REGIONS),
                         ["README.md", "docs/PROGRAM.md", "docs/WORKFLOW.md"])
        program = self.PAGES["docs/PROGRAM.md"]
        self.assertEqual([m.group(2) for m in heath.REGIONS["docs/PROGRAM.md"].finditer(program)],
                         ["| table |\n"])
        # The decisions page holds no region, and refuses any notes marker; a file that is
        # neither a brief nor a file of REGIONS has no region.
        brief = self.PAGES["docs/briefs/0008-centre.md"]
        for path in ("docs/briefs/0002-decisions.md", "docs/notes.md", "docs/briefs/a/b.md"):
            with self.subTest(path=path):
                self.assertEqual((heath.bodies(path, brief), heath.outside(path, brief)),
                                 ([], brief))
        with self.assertRaisesRegex(heath.RegionError, "^docs/briefs/0002-decisions.md:5: "
                                                       "notes markers are forbidden in dated "
                                                       "history$"):
            heath.regions("docs/briefs/0002-decisions.md", brief)
        self.assertEqual(heath.regions("docs/notes.md", brief), [])

    def test_a_hand_edit_inside_a_notes_body_is_generated(self):
        for path, text in self.PAGES.items():
            for edited in (text.replace("- Two.\n", ""),
                           text.replace("- One.", "- Changed by hand."),
                           text.replace("- One.\n- Two.\n", "")):
                with self.subTest(path=path, edited=edited):
                    self.assertEqual([m["name"] for m in heath.regions(path, edited)],
                                     self.NAMES[path])
                    self.assertEqual(heath.outside(path, edited), heath.outside(path, text))
                    self.assertNotEqual(heath.bodies(path, edited), heath.bodies(path, text))
                    # Written back with the bodies before the edit, the page is as it was.
                    before = dict(heath.bodies(path, text))
                    self.assertEqual(heath.fill(path, edited, lambda name, body: before[name]),
                                     text)

    def test_a_marker_deleted_or_bent_is_refused_and_seen(self):
        program, brief = self.PAGES["docs/PROGRAM.md"], self.PAGES["docs/briefs/0008-centre.md"]
        landed = "<!-- notes:landed -->\n- One.\n- Two.\n<!-- /notes:landed -->\n"
        opener, closer = "<!-- notes:landed -->", "<!-- /notes:landed -->"
        cases = {
            "docs/PROGRAM.md": (
                ("the opener deleted", program.replace(opener + "\n", "")),
                ("the closer deleted", program.replace(closer + "\n", "")),
                ("the opener bent", program.replace(opener, "<!-- notes:Landed -->")),
                ("the opener unspaced", program.replace(opener, "<!--notes:landed-->")),
                ("the opener indented", program.replace(opener, " " + opener)),
                ("a word after the closer", program.replace(closer, closer + " by hand")),
                ("the opener bare", program.replace("notes:landed", "notes")),
                ("a section not in the list", program.replace("notes:landed", "notes:later")),
                ("the region moved inside the status region",
                 program.replace(landed, "").replace("<!-- status -->\n",
                                                     "<!-- status -->\n" + landed)),
                ("a status closer's text after a line of the notes",
                 program.replace("- One.\n", "- One. <!-- /status -->\n")),
            ),
            "docs/briefs/0008-centre.md": (
                ("the opener deleted", brief.replace("<!-- notes -->\n", "")),
                ("the closer deleted", brief.replace("<!-- /notes -->\n", "")),
                ("the opener bent", brief.replace("<!-- notes -->", "<!-- Notes -->")),
                ("a near miss", brief.replace("<!-- notes -->", "<!-- notes_typo -->")),
                ("the opener named", brief.replace("notes -->", "notes:landed -->")),
                ("text before the opener",
                 brief.replace("<!-- notes -->", "Text <!-- notes -->")),
                ("the region doubled", brief + "<!-- notes -->\n<!-- /notes -->\n"),
                ("a marker's text after a line of the notes",
                 brief.replace("- One.\n", "- One. <!-- notes\n")),
            ),
        }
        for path, edits in cases.items():
            for what, edited in edits:
                with self.subTest(path=path, edit=what):
                    self.assertNotEqual(edited, self.PAGES[path])
                    with self.assertRaisesRegex(heath.RegionError, f"^{re.escape(path)}"):
                        heath.regions(path, edited)
                    self.assertNotEqual(heath.outside(path, edited),
                                        heath.outside(path, self.PAGES[path]))
                    written = []
                    with self.assertRaises(heath.RegionError):
                        heath.fill(path, edited, lambda name, body: written.append(name) or body)
                    self.assertEqual(written, [])

    def test_fill_names_each_region_and_refuses_a_write_reaching_outside_a_notes_body(self):
        for path, text in self.PAGES.items():
            with self.subTest(path=path):
                written = []
                self.assertEqual(heath.fill(path, text,
                                            lambda name, body: written.append(name) or body),
                                 text)
                self.assertEqual(written, self.NAMES[path])
                new = heath.fill(path, text, lambda name, body: (
                    "- New.\n" if name.startswith("notes") else body))
                self.assertEqual(new, text.replace("- One.\n- Two.\n", "- New.\n"))
                self.assertEqual(heath.outside(path, new), heath.outside(path, text))
                closer = ("<!-- /notes:landed -->" if path == "docs/PROGRAM.md"
                          else "<!-- /notes -->")
                # One closes the region early, with prose after it; one puts a marker's text
                # in the body, which `outside` keeps whole, as written by hand.
                for after in (f"{closer}\nProse.\n", "- A line. <!-- notes -->\n"):
                    with (self.subTest(after=after),
                          self.assertRaisesRegex(heath.RegionError, "reaches outside them")):
                        heath.fill(path, text, lambda name, body: (
                            body + after if name.startswith("notes") else body))

    def test_unclosed_openers_are_read_in_linear_time(self):
        # 8,000 openers with no closer are read in well under a second: by heath.outside and
        # heath.bodies, whose body stops at the next opener, and by heath.notes, which finds
        # the status region in two searches, with a notes region beside them or none.
        for path, line in (("docs/PROGRAM.md", "<!-- notes:landed -->\n"),
                           ("docs/PROGRAM.md", "<!-- status -->\n"),
                           ("docs/briefs/0008-centre.md", "<!-- notes -->\n")):
            with self.subTest(path=path, line=line):
                text = line * 8000
                started = time.perf_counter()
                self.assertEqual(heath.outside(path, text), text)
                self.assertEqual(heath.bodies(path, text), [])
                self.assertLess(time.perf_counter() - started, 1.0)
        for landed in ("", "<!-- notes:landed -->\n<!-- /notes:landed -->\n"):
            with self.subTest(landed=landed):
                text = landed + "<!-- status -->\n" * 8000
                started = time.perf_counter()
                self.assertEqual(len(heath.notes("docs/PROGRAM.md", text)), bool(landed))
                self.assertLess(time.perf_counter() - started, 1.0)

    def test_safe_push_reads_program_notes_bodies_as_generated(self):
        # safe_push.generated_parts reads docs/PROGRAM.md, a key of heath.REGIONS, through
        # heath.bodies and heath.outside: a changed notes body is a generated change and not
        # one written by hand; a marker bent or prose changed is written by hand.
        path, text = "docs/PROGRAM.md", self.PAGES["docs/PROGRAM.md"]
        commits = {}
        for name, version in (("base", text),
                              ("notes", text.replace("- Two.\n", "- Two.\n- Three.\n")),
                              ("marker", text.replace("<!-- /notes:landed -->",
                                                      "<!-- /notes:landed --> by hand")),
                              ("prose", text.replace("After.", "Later."))):
            (self.root / path).write_text(version, encoding="utf-8")
            self.git("add", path)
            self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                     "commit", "-q", "-m", name)
            commits[name] = self.git("rev-parse", "HEAD").stdout.decode().strip()
        base = commits["base"]
        self.assertEqual(safe_push.generated_parts(self.root, base, commits["notes"], path),
                         (True, False))
        self.assertTrue(safe_push.generated_parts(self.root, base, commits["marker"], path)[1])
        self.assertEqual(safe_push.generated_parts(self.root, base, commits["prose"], path),
                         (False, True))
        # A brief stays written by hand whole, until safe_push.py reads its notes regions:
        # no brief is under what safe_push.py takes for generated.
        self.assertIs(safe_push.heath, heath)
        self.assertFalse(safe_push.under("docs/briefs/0008-centre.md", safe_push.GENERATED))
        self.assertFalse(safe_push.under("docs/briefs/", safe_push.GENERATED))


class RenderFillsTheNotes(unittest.TestCase):
    """render.py, run whole on a copy of the sources it has rendered once, with a headed
    entry, changes no file; with a pair of notes markers planted in one brief besides, it
    changes that brief, between its markers, and nothing else."""

    def test_one_brief_changes_between_its_markers_alone(self):
        from negative_tests import count_source_copy

        word = uuid.uuid4().hex
        name = f"2026-10-27-render-notes-{word}.md"
        line = f"A note for the test ({word})."
        with count_source_copy() as (root, env):
            def run(expected):
                result = subprocess.run([sys.executable, "scripts/render.py"], cwd=root,
                                        env=env, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn(f"\nnotes regions: {expected}\n", result.stdout)
                self.assertIn("rendered book pages", result.stdout)

            def files():
                return {path: path.read_bytes() for path in root.rglob("*")
                        if path.is_file() and "__pycache__" not in path.parts}

            # Rendered once before the entry is written, so that what follows is compared
            # with the renderer's own output, not with the pages as committed: in the
            # pre-flight's pass with origin/main's checks, a renderer change finds its
            # regenerated pages stale, and that is freshness, not this test's verdict (#677).
            run("0 filled in 0 pages")
            entry = root / "docs" / "decisions" / name
            self.assertFalse(entry.exists())
            entry.write_text(header(f"id=render-notes-{word}", "cards=577",
                                    "briefs=0008-centre", line=line)
                             + "\n- **A decision for the test.** It names a brief.\n",
                             encoding="utf-8")

            # Then the entry beside the sources: no page has markers, so the header renders
            # nothing, and every file is byte for byte as the first run left it.
            before = files()
            run("0 filled in 0 pages")
            after = files()
            self.assertEqual(set(after), set(before))
            self.assertEqual(sorted(path.relative_to(root).as_posix() for path in after
                                    if before[path] != after[path]), [])
            brief = root / "docs" / "briefs" / "0008-centre.md"
            pair = "<!-- notes -->\n<!-- /notes -->\n"
            self.assertNotIn("<!-- notes", brief.read_text(encoding="utf-8"))
            planted = brief.read_text(encoding="utf-8") + "\n" + pair
            brief.write_text(planted, encoding="utf-8")
            before = files()
            run("1 filled in 1 page")
            after = files()
            self.assertEqual(sorted(path.relative_to(root).as_posix() for path in after
                                    if before.get(path) != after[path]),
                             ["docs/briefs/0008-centre.md"])
            self.assertEqual(set(after), set(before))
            self.assertEqual(brief.read_text(encoding="utf-8"), planted.replace(
                pair, f"<!-- notes -->\n- 27 October 2026, [#577]({ISSUE}577): {line} "
                      f"([the entry](../decisions/{name}))\n<!-- /notes -->\n"))


if __name__ == "__main__":
    unittest.main()
