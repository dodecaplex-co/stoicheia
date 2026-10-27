#!/usr/bin/env python3
"""File-only count and marker regressions: python3 -I tests/test_generated_counts.py."""

import io
import os
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))
import generated_counts as counts
import render


class CountTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory()))
        self.write("Certificate/axioms.lock", """
[axioms]
Postulate1 = "first"
Postulate2 = "second"
Postulate5 = "parallels"
"Definition1.15" = "definition"
"Tacit.first" = "rule"
"Tacit.second" = "rule"
"Other.rule" = "other"
[vocabulary]
Point = "word"
Centre = "word"
Circle = "word"
""")
        self.write("Elements/Companions.lean", """
/-! Example: (``Elements.BookIII.Prop9.example, "III.9 example") -/
def Elements.companions : List (Lean.Name × String) := [
  (``Elements.BookI.Prop1.general, "I.1 general"),
  /- Ignore (``Elements.BookIII.Prop9.fake, "III.9 fake").
     /- A nested comment. -/ -/
  (``Elements.BookI.Prop1.special, "I.1 special"),
  -- (``Elements.BookI.Prop2.fake, "I.2 fake"),
  (``Elements.BookII.Prop1.general, "II.1 general")]
""")
        for book, stages in {"I": ("full", "exceptions"), "II": ("exceptions",),
                             "III": ("full", "full", "full")}.items():
            for n, stage in enumerate(stages, 1):
                self.write(f"review/{book}/{n:02d}.toml",
                           f'[review]\nstage = "{stage}"\n')
        self.write("review/I/notes.toml", 'stage = "full"')
        self.report("**7 failing items**. 2 of the 6 propositions pass every item of their own.")
        self.write(counts.SCREEN, '''"""A small screen; its CIRCLE is named here only in prose."""

import itertools

RULES = """Postulate1 Postulate2 Postulate3""".split()

# Rules that speak of circles.
CIRCLE = """Definition15 Postulate3
Tacit.circles_meet""".split()

missing = [rule for rule in CIRCLE if rule not in RULES]
pairs = list(itertools.combinations(CIRCLE, 2))
''')
        self.write(counts.SUPERPOSITION, '''import Elements.Figure.Superposition

/-! The first two pins record their dependencies. -/

/-- info: 'Elements.first' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Elements.first

/-- info: 'Elements.second' does not depend on any axioms -/
#guard_msgs in
#print axioms Elements.second

#print Elements.Superposition.Placed

-- #print axioms Elements.lineComment
/- Outer /- #print axioms Elements.nestedComment -/ still a comment. -/
def note : String := "#print axioms Elements.inString"
''')
        self.tracked = [p.relative_to(self.root) for p in self.root.rglob("*") if p.is_file()]
        self.enterContext(patch.object(
            counts, "tracked_files",
            side_effect=lambda root, pattern: [p for p in self.tracked if p.match(pattern)]))

    def write(self, path, text):
        path = self.root / path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def report(self, summary):
        self.write(counts.ACCEPTANCE, "For each book, for each of the 6 propositions.\n\n"
                   "## Summary\n\n" + summary + "\n\nFailing propositions, item by item:\n"
                   "\n## The whole edition\n")

    def scan(self, files, *, check=False):
        with patch.object(counts, "tracked_markdown", return_value=list(map(Path, files))):
            return counts.updates(self.root, check=check)

    def test_every_count_on_small_files(self):
        self.assertEqual({name: fn(self.root) for name, fn in counts.COUNTS.items()}, {
            "axioms": 7, "tacit-rules": 2, "postulates": 3, "axioms-but-postulate-5": 6,
            "vocabulary": 3,
            "companions": 3, "companion-propositions": 2,
            "reviews:I": 2, "reviews:II": 1, "reviews:III": 3,
            "reviews:I:full": 1, "reviews:II:full": 0, "reviews:III:full": 3,
            "acceptance:failing": 7, "acceptance:passing": 2,
            "screen-circle-rules": 3, "superposition-dependency-checks": 2,
        })

    def test_screen_circle_rules_refuse_any_other_shape(self):
        path = self.root / counts.SCREEN
        original = path.read_text()
        assignment = 'CIRCLE = """Definition15 Postulate3\nTacit.circles_meet""".split()'
        for text in (original.replace("CIRCLE =", "CIRCLES ="),
                     original + 'CIRCLE = "Postulate1".split()\n',
                     original + "CIRCLE: list[str]\n",
                     original + 'CIRCLE += ["Postulate1"]\n',
                     original.replace("CIRCLE =", "CIRCLE: list[str] ="),
                     original.replace("CIRCLE =", "CIRCLE = OTHER ="),
                     original.replace(assignment, 'CIRCLE = ["Definition15", "Postulate3"]'),
                     original.replace(".split()\n\nmissing", '.split(" ")\n\nmissing'),
                     original.replace(".split()\n\nmissing", ".split(sep=None)\n\nmissing"),
                     original.replace(assignment, 'CIRCLE = f"{RULES[2]} Definition15".split()'),
                     original.replace(assignment, "CIRCLE = RULES"),
                     original.replace(assignment, 'CIRCLE = b"Definition15 Postulate3".split()'),
                     original.replace("Tacit.circles_meet", "Postulate3"),
                     original + "if RULES:\n    CIRCLE = []\n",
                     original + "def widen():\n    global CIRCLE\n    CIRCLE = RULES\n",
                     original + 'CIRCLE.append("Postulate1")\n',
                     original + "del CIRCLE[0]\n",
                     original + "from rules import CIRCLE\n",
                     original + "CIRCLE = (\n"):
            with self.subTest(text=text):
                path.write_text(text)
                with self.assertRaisesRegex(ValueError, counts.SCREEN):
                    counts.screen_circle_rules(self.root)
        path.unlink()
        with self.assertRaisesRegex(ValueError, counts.SCREEN):
            counts.screen_circle_rules(self.root)

    def test_screen_circle_rules_refuse_an_alias_that_is_mutated(self):
        path = self.root / counts.SCREEN
        path.write_text(path.read_text() + '\nalias = CIRCLE\nalias.append("Postulate1")\n')
        with self.assertRaisesRegex(ValueError, counts.SCREEN):
            counts.screen_circle_rules(self.root)

    def test_screen_circle_rules_refuse_argument_bindings(self):
        path = self.root / counts.SCREEN
        path.write_text(path.read_text() + "\ndef shadow(CIRCLE):\n    return None\n")
        with self.assertRaisesRegex(ValueError, counts.SCREEN):
            counts.screen_circle_rules(self.root)

    def test_screen_circle_rules_refuse_combinations_or_module_rebinding(self):
        path = self.root / counts.SCREEN
        original = path.read_text()
        call = "pairs = list(itertools.combinations(CIRCLE, 2))"
        replacements = (
            'itertools.combinations = lambda xs, n: (xs.append("Postulate1") or ())\n'
            + call,
            'class Mutating:\n'
            '    def combinations(self, xs, n):\n'
            '        xs.append("Postulate1")\n'
            '        return ()\n'
            'itertools = Mutating()\n' + call,
        )
        for replacement in replacements:
            with self.subTest(replacement=replacement):
                path.write_text(original.replace(call, replacement))
                with self.assertRaisesRegex(ValueError, counts.SCREEN):
                    counts.screen_circle_rules(self.root)

    def test_superposition_dependency_checks_refuse_an_unreadable_file(self):
        path = self.root / counts.SUPERPOSITION
        original = path.read_text()
        for text in (original + "/- A comment never closed.\n#print axioms Elements.third\n",
                     original + 'def unclosed : String := "never closed\n'
                     "#print axioms Elements.third\n",
                     original + 'def braces : String := "{ a hole or text?"\n'):
            with self.subTest(text=text):
                path.write_text(text)
                with self.assertRaisesRegex(ValueError, counts.SUPERPOSITION):
                    counts.superposition_dependency_checks(self.root)
        path.unlink()
        with self.assertRaisesRegex(ValueError, counts.SUPERPOSITION):
            counts.superposition_dependency_checks(self.root)

    def test_source_readers_name_decode_failures(self):
        for relative, reader in ((counts.SCREEN, counts.screen_circle_rules),
                                 (counts.SUPERPOSITION,
                                  counts.superposition_dependency_checks)):
            with self.subTest(path=relative):
                (self.root / relative).write_bytes(b"\xff")
                with self.assertRaises(ValueError) as raised:
                    reader(self.root)
                self.assertIn(relative, str(raised.exception))

    def test_superposition_dependency_checks_ignore_escaped_names(self):
        path = self.root / counts.SUPERPOSITION
        path.write_text(path.read_text() + '\ndef «#print axioms Elements.note» := 0\n')
        self.assertEqual(counts.superposition_dependency_checks(self.root), 2)

    def test_superposition_dependency_checks_require_a_subcommand_and_target(self):
        path = self.root / counts.SUPERPOSITION
        path.write_text(path.read_text() + "\n#print axioms.foo\n#print axioms\n")
        self.assertEqual(counts.superposition_dependency_checks(self.root), 2)

    def test_superposition_dependency_checks_preserve_source_line_endings(self):
        path = self.root / counts.SUPERPOSITION
        original = path.read_bytes()
        path.write_bytes(original.replace(b"\n", b"\r\n"))
        self.assertEqual(counts.superposition_dependency_checks(self.root), 2)
        path.write_bytes(b"-- comment\r#print axioms Elements.hidden\n")
        with self.assertRaisesRegex(ValueError, counts.SUPERPOSITION):
            counts.superposition_dependency_checks(self.root)

    def test_screen_and_superposition_words_fill_markers(self):
        text = ("<!-- count:screen-circle-rules:Word -->Ten<!-- /count --> rules about circles "
                "(<!-- count:screen-circle-rules -->10<!-- /count -->); "
                "<!-- count:superposition-dependency-checks -->28<!-- /count --> checks, "
                "<!-- count:superposition-dependency-checks:word -->twenty-eight"
                "<!-- /count --> in words.\n")
        path = self.write("docs/notes.md", text)
        changes, errors = self.scan(["docs/notes.md"])
        self.assertEqual(errors, [])
        self.assertEqual(changes[path], text.replace("-->Ten<!--", "-->Three<!--")
                         .replace("-->10<!--", "-->3<!--").replace("-->28<!--", "-->2<!--")
                         .replace("-->twenty-eight<!--", "-->two<!--"))
        self.assertEqual(counts.value(self.root, "screen-circle-rules:word", {}), "three")
        self.assertEqual(counts.value(self.root, "superposition-dependency-checks:Word", {}),
                         "Two")

    def test_real_screen_and_superposition_files_read(self):
        # Their values are left to the markers: asserting them here would retype the counts.
        self.assertGreater(counts.screen_circle_rules(REPO), 0)
        self.assertGreater(counts.superposition_dependency_checks(REPO), 0)

    def test_companions_refuse_unreadable_or_duplicate_entries(self):
        path = self.root / "Elements/Companions.lean"
        original = path.read_text()
        for text in (original.replace('"I.1 general"', '"I.2 general"'),
                     original.replace("Prop1.special", "Prop1.general")
                     .replace('"I.1 special"', '"I.1 general"'),
                     original.replace(":= [", ":= extra ++ ["),
                     original + " ++ []",
                     original.replace("Prop1.special", "unknown"),
                     original.replace('general")]', 'general")')):
            with self.subTest(text=text):
                path.write_text(text)
                with self.assertRaises(ValueError):
                    counts.companions(self.root)

    def test_empty_companions_list(self):
        self.write("Elements/Companions.lean",
                   "def Elements.companions : List (Lean.Name × String) := []")
        self.assertEqual(counts.companions(self.root), 0)
        self.assertEqual(counts.companion_propositions(self.root), 0)

    def test_bad_inputs_are_not_silently_counted(self):
        self.write("review/I/01.toml", '[review]\nstage = "complete"\n')
        with self.assertRaisesRegex(ValueError, "invalid.*stage"):
            counts.full_reviews(self.root, "I")
        self.write("Certificate/axioms.lock", "[axioms]\n")
        with self.assertRaises(ValueError):
            counts.axioms(self.root)
        self.write(counts.ACCEPTANCE, "303 failing items; no generated summary")
        with self.assertRaisesRegex(ValueError, "Summary"):
            counts.acceptance_failing(self.root)

    def test_report_all_pass_and_not_run_forms(self):
        self.report("**No failures.** Every item of the checklist passes.")
        self.assertEqual(counts.acceptance_summary(self.root), (0, 6))
        self.report("**1 failing item**, and 2 not run. "
                    "3 of the 6 propositions pass every item of their own.")
        self.assertEqual(counts.acceptance_summary(self.root), (1, 3))
        self.report("**7 failing items**. 8 of the 6 propositions pass every item of their own.")
        with self.assertRaises(ValueError):
            counts.acceptance_summary(self.root)

    def test_number_words_and_sentence_capital(self):
        cases = {0: "zero", 8: "eight", 19: "nineteen", 20: "twenty",
                 21: "twenty-one", 81: "eighty-one", 91: "ninety-one",
                 100: "one hundred", 303: "three hundred and three",
                 1001: "one thousand and one", 1234: "one thousand two hundred and thirty-four"}
        for number, expected in cases.items():
            self.assertEqual(counts.number_word(number), expected)
        self.assertEqual(counts.value(self.root, "companions:Word", {}), "Three")
        self.assertEqual(counts.value(self.root, "reviews:I:full:word", {}), "one")
        with self.assertRaisesRegex(ValueError, "unknown count name"):
            counts.value(self.root, "companions:WORD", {})

    def test_exact_freshness_diagnostic_and_repair(self):
        path = self.write("docs/PROGRAM.md", "# Programme\n\n"
                          "Vocabulary: <!-- count:vocabulary -->61<!-- /count --> words.\n")
        changes, errors = self.scan(["docs/PROGRAM.md"], check=True)
        self.assertEqual(errors, ["docs/PROGRAM.md:3: count 'vocabulary': stated '61', "
                                  "computed '3'; run python3 scripts/render.py"])
        self.assertIn("-->3<!--", changes[path])
        self.assertEqual(path.read_text().count("-->61<!--"), 1)
        path.write_text(changes[path])
        self.assertEqual(self.scan(["docs/PROGRAM.md"], check=True), ({}, []))

    def test_multiple_forms_outside_generated_regions_preserve_surrounding_prose(self):
        text = ("A <!-- count:companions:Word -->One<!-- /count --> theorem; "
                "<!-- count:companion-propositions:word -->one<!-- /count --> propositions.\n"
                "<!-- scope:I -->Generated summary.<!-- /scope:I -->\n"
                "<!-- status -->\nGenerated status.\n<!-- /status -->")
        path = self.write("README.md", text)
        changes, errors = self.scan(["README.md"])
        self.assertEqual(errors, [])
        self.assertEqual(changes[path], text.replace("-->One<!--", "-->Three<!--")
                         .replace("-->one<!--", "-->two<!--"))

    def test_markers_in_partial_renderer_regions_are_refused(self):
        marker = "<!-- count:vocabulary -->3<!-- /count -->"
        cases = (
            ("README.md", f"# Title\n<!-- scope:I -->\n{marker}\n<!-- /scope:I -->\n"),
            ("README.md", "# Title\n<!-- count:vocabulary -->3<!-- scope:I -->summary"
             "<!-- /count --><!-- /scope:I -->\n"),
            ("README.md", "# Title\n<!-- count:vocabulary -->3<!-- scope:I -->summary"
             "<!-- /scope:I --><!-- /count -->\n"),
            ("README.md", "# Title\n<!-- scope:I -->summary<!-- count:vocabulary -->3"
             "<!-- /scope:I --><!-- /count -->\n"),
            ("docs/PROGRAM.md",
             f"# Programme\n<!-- status -->\n{marker}\n<!-- /status -->\n"),
        )
        for path, text in cases:
            source = self.write(path, text)
            line = text.count("\n", 0, counts.START.search(text).start()) + 1
            for check in (False, True):
                with self.subTest(path=path, text=text, check=check):
                    changes, errors = self.scan([path], check=check)
                    self.assertEqual(changes, {})
                    self.assertEqual(len(errors), 1)
                    self.assertTrue(errors[0].startswith(f"{path}:{line}:"), errors)
                    self.assertIn("forbidden", errors[0])
                    self.assertIn("region", errors[0])
                    self.assertEqual(source.read_text(), text)

    def test_malformed_and_unknown_markers_name_the_line(self):
        bad = ("<!-- count:vocabulary -->3", "<!-- /count -->",
               "<!--count:vocabulary -->3<!-- /count -->",
               "<!-- count:vocabulary -->3<!-- /count:other -->",
               "<!-- count:vocabulary -->\n3<!-- /count -->",
               "<!-- count:vocabulary -->3<!-- count:axioms -->6<!-- /count -->",
               "<!-- count -->3<!-- /count -->", "<!-- COUNT:vocabulary -->",
               "<!-- count:vocabulary --", "<!-- count:unknown -->0<!-- /count -->")
        for marker in bad:
            with self.subTest(marker=marker):
                self.write("README.md", "# Title\n" + marker)
                for check in (True, False):
                    _, errors = self.scan(["README.md"], check=check)
                    self.assertEqual(len(errors), 1)
                    self.assertTrue(errors[0].startswith("README.md:2:"), errors)
        self.assertIn("unknown count name 'unknown'", errors[0])

    def test_whitespace_in_value_is_stale(self):
        self.write("README.md", "<!-- count:vocabulary --> 3 <!-- /count -->")
        self.assertIn("stated ' 3 '", self.scan(["README.md"], check=True)[1][0])

    def test_history_is_refused(self):
        history = ["docs/briefs/0002-decisions.md", "docs/reports/crew/new-log.md",
                   "docs/reports/read-through-01.md", counts.ACCEPTANCE]
        for path in history:
            self.write(path, "<!-- count:vocabulary -->3<!-- /count -->")
        changes, errors = self.scan(history)
        self.assertEqual(changes, {})
        self.assertEqual(len(errors), len(history))
        for path, error in zip(history, errors):
            self.assertIn(f"{path}:1:", error)
            self.assertIn("forbidden in dated history", error)

    def test_whole_outputs_refuse_every_marker_without_filling(self):
        outputs = ["book/I/index.md", "book/appendix.md", "CERTIFICATE.md", "GRAPH.md"]
        for marker in ("<!-- count:vocabulary -->3<!-- /count -->",
                       "<!-- count:vocabulary -->0<!-- /count -->",
                       "<!-- count:unknown -->0<!-- /count -->", "<!-- COUNT:broken"):
            for path in outputs:
                self.write(path, "# Output\n" + marker)
            for check in (False, True):
                with self.subTest(marker=marker, check=check):
                    changes, errors = self.scan(outputs, check=check)
                    self.assertEqual(changes, {})
                    self.assertEqual(len(errors), len(outputs))
                    for path, error in zip(outputs, errors):
                        self.assertIn(f"{path}:2:", error)
                        self.assertIn("forbidden in whole renderer outputs", error)
                        self.assertEqual((self.root / path).read_text(), "# Output\n" + marker)

    def test_tracked_review_numbers_must_belong_to_the_book(self):
        for book in counts.heath.BOOKS:
            for number in (0, counts.heath.BOOKS[book] + 1):
                rel = f"review/{book}/{number:02d}.toml"
                self.write(rel, '[review]\nstage = "full"\n')
                self.tracked.append(Path(rel))
                with self.subTest(path=rel), self.assertRaisesRegex(
                        ValueError, f"{rel}: proposition number is outside Book {book}"):
                    counts.review_stages(self.root, book)
                self.tracked.remove(Path(rel))

    def test_tracked_markdown_symlinks_are_refused_even_without_markers(self):
        for text in ("Plain prose.", "<!-- count:vocabulary -->0<!-- /count -->"):
            target = self.write("target.md", text)
            path = self.root / "README.md"
            path.symlink_to(target)
            try:
                for check in (False, True):
                    changes, errors = self.scan(["README.md"], check=check)
                    self.assertEqual(changes, {})
                    self.assertEqual(errors, ["README.md: symlink is forbidden"])
                self.assertEqual(target.read_text(), text)
            finally:
                path.unlink()

    def test_paths_resolving_outside_the_root_are_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            outside = Path(tmp)
            target = outside / "notes.md"
            text = "<!-- count:vocabulary -->0<!-- /count -->"
            target.write_text(text)
            (self.root / "linked").symlink_to(outside, target_is_directory=True)
            changes, errors = self.scan(["linked/notes.md"])
            self.assertEqual(changes, {})
            self.assertEqual(errors, ["linked: symlink is forbidden"])
            with patch.object(render, "ROOT", self.root):
                for path in (self.root / "linked/notes.md", target):
                    diagnostic = ("symlink is forbidden" if path.is_relative_to(self.root)
                                  else "outside repository root")
                    with self.assertRaisesRegex(ValueError, diagnostic):
                        render.read_text(path)
                    with self.assertRaisesRegex(ValueError, diagnostic):
                        render.write_text(path, "Changed.")
            self.assertEqual(target.read_text(), text)

    def test_in_repository_parent_symlinks_are_refused_for_reads_and_writes(self):
        target = self.write("actual/notes.md", "Original.")
        (self.root / "linked").symlink_to(self.root / "actual", target_is_directory=True)
        changes, errors = self.scan(["linked/notes.md"])
        self.assertEqual(changes, {})
        self.assertEqual(errors, ["linked: symlink is forbidden"])
        with patch.object(render, "ROOT", self.root):
            with self.assertRaisesRegex(ValueError, "linked: symlink is forbidden"):
                render.read_text(self.root / "linked/notes.md")
            with self.assertRaisesRegex(ValueError, "linked: symlink is forbidden"):
                render.write_text(self.root / "linked/notes.md", "Changed.")
        self.assertEqual(target.read_text(), "Original.")

    def test_render_rechecks_paths_before_writing(self):
        target = self.write("target.md", "Original.")
        path = self.write("README.md", "<!-- count:vocabulary -->0<!-- /count -->")
        changes, errors = self.scan(["README.md"])
        self.assertEqual(errors, [])
        path.unlink()
        path.symlink_to(target)
        with patch.object(render, "ROOT", self.root):
            with self.assertRaisesRegex(ValueError, "README.md: symlink is forbidden"):
                render.write_text(path, changes[path])
        self.assertEqual(target.read_text(), "Original.")

    def test_render_rechecks_parent_components_before_writing(self):
        path = self.write("docs/notes.md", "<!-- count:vocabulary -->0<!-- /count -->")
        changes, errors = self.scan(["docs/notes.md"])
        self.assertEqual(errors, [])
        target_dir = self.root / "actual"
        path.parent.rename(target_dir)
        (self.root / "docs").symlink_to(target_dir, target_is_directory=True)
        target = target_dir / "notes.md"
        with patch.object(render, "ROOT", self.root):
            with self.assertRaisesRegex(ValueError, "docs: symlink is forbidden"):
                render.write_text(path, changes[path])
        self.assertIn("-->0<!--", target.read_text())

    def test_symlinked_root_alias_is_supported(self):
        real_root = self.root / "real-root"
        real_root.mkdir()
        target = real_root / "notes.md"
        target.write_text("Original.")
        alias = self.root / "root-alias"
        alias.symlink_to(real_root, target_is_directory=True)
        with patch.object(render, "ROOT", alias):
            self.assertEqual(render.read_text(alias / "notes.md"), "Original.")
            render.write_text(alias / "notes.md", "Changed.")
        self.assertEqual(target.read_text(), "Changed.")

    def test_page_terms_reads_refuse_symlinks(self):
        target = self.write("review/terms-target.toml", "[tag.example]\n"
                            'kind = "representation"\nmeaning = "example"\n')
        terms = self.root / "review/terms.toml"
        terms.symlink_to(target)
        with patch.object(render, "ROOT", self.root), \
                patch.object(render.heath, "REVIEW", self.root / "review"):
            with self.assertRaisesRegex(ValueError, "review/terms.toml: symlink is forbidden"):
                render.representation_badge({"representation": {"tags": ["example"]}})
        self.assertEqual(target.read_text(), "[tag.example]\nkind = \"representation\"\n"
                         "meaning = \"example\"\n")

    def test_optional_paths_preserve_missing_fallbacks_and_refuse_escapes(self):
        with patch.object(render, "ROOT", self.root):
            self.assertEqual(render.load_facts(), {})
            self.assertEqual(render.book_intro("IV"), "")
            self.assertIsNone(render.optional_path(self.root / "missing.md"))
            with tempfile.TemporaryDirectory() as outside_dir:
                with self.assertRaisesRegex(ValueError, "path is outside repository root"):
                    render.optional_path(Path(outside_dir) / "outside.md")

    def test_names_page_refuses_dangling_lean_and_accepts_missing_lean(self):
        lean = self.root / "Elements/BookI/Prop01.lean"
        lean.parent.mkdir(parents=True, exist_ok=True)
        with patch.object(render, "ROOT", self.root), \
                patch.object(render, "BOOKS", {"I": (1, {1: "Test proposition"})}), \
                patch.object(render.heath, "lean_path", return_value=lean):
            page = render.names_page({}, {})
            self.assertIn("Test proposition", page)
            lean.symlink_to(self.root / "missing-lean.lean")
            with self.assertRaisesRegex(ValueError, "Elements/BookI/Prop01.lean: symlink"):
                render.names_page({}, {})

    def test_all_other_tracked_markdown_can_hold_counts(self):
        paths = ["docs/reports/gaps-book-I.md", "docs/reports/overlaps.md",
                 "Certificate/FIELDS.md", "tests/model/MODEL.md", "a folder/notes.md"]
        for path in paths + ["untracked.md"]:
            self.write(path, "<!-- count:vocabulary -->0<!-- /count -->")
        changes, errors = self.scan(paths)
        self.assertEqual(errors, [])
        self.assertEqual(set(changes), {self.root / path for path in paths})
        self.assertIn("-->0<!--", (self.root / "untracked.md").read_text())

    def test_literal_examples_must_escape_opening_angle(self):
        self.write("README.md", "&lt;!-- count:name -->value&lt;!-- /count -->")
        self.assertEqual(self.scan(["README.md"]), ({}, []))
        self.write("README.md", "`<!-- count:unknown -->0<!-- /count -->`")
        self.assertIn("unknown count", self.scan(["README.md"])[1][0])

    def test_intro_is_filled_before_copy_and_carries_no_count_comments(self):
        path = self.write("mishnah/intro/I.md", "There are <!-- count:vocabulary -->0"
                          "<!-- /count --> words. <!-- An ordinary comment stays. -->")
        changes, errors = self.scan(["mishnah/intro/I.md"])
        self.assertEqual(errors, [])
        path.write_text(changes[path])
        with patch.object(render, "ROOT", self.root):
            self.assertEqual(render.book_intro("I"),
                             "There are 3 words. <!-- An ordinary comment stays. -->")

    def test_negative_freshness_plant_saves_inline_outputs(self):
        import negative_tests

        marked = self.write("Certificate/FIELDS.md",
                            "<!-- count:vocabulary -->3<!-- /count -->")
        plain = self.write("notes.md", "Human prose.")
        with patch.object(negative_tests, "ROOT", self.root), patch.object(
                counts, "tracked_markdown",
                return_value=[Path("Certificate/FIELDS.md"), Path("notes.md")]):
            saved = negative_tests.generated_files()
        self.assertIn(marked, saved)
        self.assertNotIn(plain, saved)

    def test_render_refuses_all_updates_when_one_marker_is_bad(self):
        good = self.write("README.md", "<!-- count:vocabulary -->0<!-- /count -->")
        bad = self.write("bad.md", "<!-- count:unknown -->0<!-- /count -->")
        with patch.object(render, "ROOT", self.root), patch.object(
                counts, "tracked_markdown", return_value=[Path("README.md"), Path("bad.md")]):
            with self.assertRaisesRegex(SystemExit, "bad.md:1: unknown count"):
                render.main()
        self.assertIn("-->0<!--", good.read_text())
        self.assertIn("unknown", bad.read_text())


ABSENT_NOTE = ("note: tracked but absent from the work tree (under the check inputs, as a "
               "file the commit adds is in the pre-flight's pass with origin/main's "
               "checks): {!r}\n")
ABSENT_FAULT = "tracked but absent from the work tree, outside the check inputs: {!r}"


class AbsentTrackedMarkdownTests(unittest.TestCase):
    """The pre-flight's pass with origin/main's checks (scripts/safe_push.py, steps 3
    and 4, base_copies) takes the files a commit adds under the check inputs out of the
    work tree, while Git's index still lists them. A tracked Markdown file absent there
    is noted and passed over, and the rest is still checked; absent anywhere else, it is
    refused. Git runs only in a temporary repository, without user config."""

    files = {"Certificate/axioms.lock": '[axioms]\n[vocabulary]\nPoint = "word"\n',
             "Certificate/NEW.md": "Notes on a field a commit adds.\n",
             "docs/notes.md": "Words: <!-- count:vocabulary -->2<!-- /count -->.\n",
             "tests/new_check.md": "Notes on a check a commit adds.\n",
             "tests/folder/notes.md": "Notes in a folder.\n"}

    def setUp(self):
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        self.enterContext(patch.dict(os.environ, {**env, "GIT_CONFIG_GLOBAL": os.devnull,
                                                  "GIT_CONFIG_NOSYSTEM": "1"}, clear=True))
        for rel, text in self.files.items():
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.root / rel).write_text(text)
        for args in (("init", "-q"), ("add", "--", *self.files)):
            subprocess.run(["git", *args], cwd=self.root, capture_output=True, check=True)
        self.output = self.enterContext(redirect_stdout(io.StringIO()))

    def test_absent_check_inputs_are_noted_and_the_rest_still_checked(self):
        for rel in ("Certificate/NEW.md", "tests/new_check.md"):
            (self.root / rel).unlink()
        changes, errors = counts.updates(self.root, check=True)
        self.assertEqual(errors, ["docs/notes.md:1: count 'vocabulary': stated '2', "
                                  "computed '1'; run python3 scripts/render.py"])
        self.assertEqual(set(changes), {self.root / "docs/notes.md"})
        self.assertEqual(self.output.getvalue(), ABSENT_NOTE.format("Certificate/NEW.md")
                         + ABSENT_NOTE.format("tests/new_check.md"))

    def test_absent_markdown_outside_the_check_inputs_is_refused(self):
        for rel in ("docs/notes.md", "tests/new_check.md"):
            (self.root / rel).unlink()
        for check in (True, False):
            with self.subTest(check=check):
                self.assertEqual(counts.updates(self.root, check=check),
                                 ({}, [ABSENT_FAULT.format("docs/notes.md")]))
        self.assertEqual(self.output.getvalue(), 2 * ABSENT_NOTE.format("tests/new_check.md"))

    def test_names_are_escaped_in_the_note_and_the_fault(self):
        names = ("tests/a\x1b[2K\rok  forged\nline.md", "docs/b\x1b[2K\rok\n.md")
        for rel in names:
            (self.root / rel).write_text("Notes.\n")
        subprocess.run(["git", "add", "--", *names], cwd=self.root, capture_output=True,
                       check=True)
        for rel in names:
            (self.root / rel).unlink()
        note, fault = ABSENT_NOTE.format(names[0]), ABSENT_FAULT.format(names[1])
        self.assertTrue(note.endswith("checks): 'tests/a\\x1b[2K\\rok  forged\\nline.md'\n"))
        self.assertTrue(fault.endswith("inputs: 'docs/b\\x1b[2K\\rok\\n.md'"))
        changes, errors = counts.updates(self.root, check=True)
        self.assertEqual(errors, [fault, "docs/notes.md:1: count 'vocabulary': stated '2', "
                                         "computed '1'; run python3 scripts/render.py"])
        self.assertEqual(self.output.getvalue(), note)

    def test_an_unreadable_directory_is_not_absent(self):
        folder = self.root / "tests/folder"
        folder.chmod(0)
        self.addCleanup(folder.chmod, 0o755)
        denied = f"[Errno 13] Permission denied: {str(folder / 'notes.md')!r}"
        for check in (True, False):
            with self.subTest(check=check):
                self.assertEqual(counts.updates(self.root, check=check), ({}, [denied]))
        self.assertEqual(self.output.getvalue(), "")

    def test_symlinks_in_place_of_absent_check_inputs_are_still_refused(self):
        (self.root / "tests/new_check.md").unlink()
        (self.root / "tests/new_check.md").symlink_to(self.root / "missing.md")
        (self.root / "tests/folder/notes.md").unlink()
        (self.root / "tests/folder").rmdir()
        (self.root / "tests/folder").symlink_to(self.root / "missing",
                                                target_is_directory=True)
        changes, errors = counts.updates(self.root, check=True)
        self.assertEqual(errors, ["docs/notes.md:1: count 'vocabulary': stated '2', "
                                  "computed '1'; run python3 scripts/render.py",
                                  "tests/folder: symlink is forbidden",
                                  "tests/new_check.md: symlink is forbidden"])
        self.assertEqual(self.output.getvalue(), "")


class GitCountTests(unittest.TestCase):
    """Exercise real read-only Git calls, including the source copy's index."""

    def setUp(self):
        self.enterContext(patch.dict(
            os.environ, {k: v for k, v in os.environ.items() if not k.startswith("GIT_")},
            clear=True))

    def test_discovery_refuses_an_untracked_directory_inside_a_checkout(self):
        with tempfile.TemporaryDirectory(dir=REPO) as tmp:
            root = Path(tmp)
            with self.assertRaisesRegex(ValueError, "Git work tree .* does not match"):
                counts.tracked_markdown(root)
            changes, errors = counts.updates(root, check=True)
            self.assertEqual(changes, {})
            self.assertEqual(len(errors), 1)
            self.assertIn("does not match repository root", errors[0])

    def test_discovery_refuses_missing_git_metadata(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with self.assertRaisesRegex(ValueError, "cannot resolve Git work tree"):
                counts.tracked_markdown(root)
            self.assertIn("cannot resolve Git work tree", counts.updates(root, check=True)[1][0])

    def test_explicit_copy_work_tree_is_honoured_and_resolved(self):
        git_dir = subprocess.check_output(
            ["git", "rev-parse", "--absolute-git-dir"], cwd=REPO, text=True).strip()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "copy"
            root.mkdir()
            alias = Path(tmp) / "alias"
            alias.symlink_to(root, target_is_directory=True)
            with patch.dict(os.environ, {"GIT_DIR": git_dir, "GIT_WORK_TREE": str(alias)}):
                self.assertEqual(counts.tracked_markdown(root), counts.tracked_markdown(alias))
                self.assertIn(Path("README.md"), counts.tracked_markdown(root))
                with self.assertRaisesRegex(ValueError, "does not match repository root"):
                    counts.tracked_markdown(REPO)
                with self.assertRaisesRegex(ValueError, "does not match repository root"):
                    counts.review_stages(REPO, "I")

    def test_failed_git_listing_has_a_clear_error(self):
        real_run = subprocess.run

        def fail_listing(cmd, **kwargs):
            if cmd[1] == "ls-files":
                raise subprocess.CalledProcessError(128, cmd, stderr=b"index unavailable")
            return real_run(cmd, **kwargs)

        with patch.object(counts.subprocess, "run", side_effect=fail_listing):
            changes, errors = counts.updates(REPO, check=True)
        self.assertEqual(changes, {})
        self.assertEqual(errors, [f"{REPO}: cannot list tracked files with Git"])

    def test_untracked_review_records_cannot_move_counts(self):
        git_dir = subprocess.check_output(
            ["git", "rev-parse", "--absolute-git-dir"], cwd=REPO, text=True).strip()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with patch.dict(os.environ, {"GIT_DIR": git_dir, "GIT_WORK_TREE": str(root)}):
                paths = counts.tracked_files(root, "review/I/[0-9][0-9].toml")
                self.assertTrue(paths)
                for rel in paths:
                    path = root / rel
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text('[review]\nstage = "full"\n')
                before = (counts.reviews(root, "I"), counts.full_reviews(root, "I"))
                self.assertEqual(before, (len(paths), len(paths)))
                (root / "review/I/99.toml").write_text('[review]\nstage = "full"\n')
                self.assertEqual((counts.reviews(root, "I"), counts.full_reviews(root, "I")),
                                 before)

    def test_render_main_fills_intro_before_copying_without_count_comments(self):
        from negative_tests import count_source_copy

        with count_source_copy() as (root, env):
            path = root / "mishnah/intro/I.md"
            computed = counts.vocabulary(root)
            path.write_text("There are <!-- count:vocabulary -->0<!-- /count --> words. "
                            "<!-- An ordinary comment stays. -->\n")
            result = subprocess.run([sys.executable, "scripts/render.py"], cwd=root, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(path.read_text(),
                             f"There are <!-- count:vocabulary -->{computed}<!-- /count --> "
                             "words. <!-- An ordinary comment stays. -->\n")
            page = (root / "book/I/index.md").read_text()
            self.assertIn(f"There are {computed} words. <!-- An ordinary comment stays. -->",
                          page)
            self.assertIsNone(counts.START.search(page))

    def test_public_checks_refuse_counts_in_partial_outputs_before_writing(self):
        from negative_tests import count_source_copy

        cases = (("README.md", counts.README_SCOPE_MARKERS, 3, "README.md scope region"),
                 ("docs/PROGRAM.md", counts.PROGRAM_STATUS_MARKERS, 2,
                  "docs/PROGRAM.md status region"))
        marker = "<!-- count:vocabulary -->0<!-- /count -->"
        for rel, pattern, body_group, diagnostic in cases:
            with self.subTest(path=rel), count_source_copy() as (root, env):
                path = root / rel
                original = path.read_text()
                region = pattern.search(original)
                self.assertIsNotNone(region)
                insertion = region.start(body_group)
                prefix = "\n" if insertion and original[insertion - 1] != "\n" else ""
                planted = original[:insertion] + prefix + marker + "\n" + original[insertion:]
                marker_start = insertion + len(prefix)
                line = planted.count("\n", 0, marker_start) + 1
                path.write_text(planted)
                outputs = [root / name for name in
                           ("README.md", "docs/PROGRAM.md", "CERTIFICATE.md", "GRAPH.md")]
                outputs.extend((root / "book").rglob("*.md"))
                before = {output: output.read_bytes() for output in outputs}
                for script in ("check_fidelity.py", "render.py"):
                    result = subprocess.run([sys.executable, f"scripts/{script}"], cwd=root,
                                            env=env, capture_output=True, text=True)
                    message = result.stdout + result.stderr
                    self.assertNotEqual(result.returncode, 0, message)
                    self.assertIn(f"{rel}:{line}:", message)
                    self.assertIn(diagnostic, message)
                    self.assertEqual({output: output.read_bytes() for output in outputs}, before)

    def test_render_refuses_aliased_review_inputs_before_writing(self):
        from negative_tests import count_source_copy

        cases = (("review/I/01.toml", "inside-existing"),
                 ("review/I/01.toml", "outside-dangling"),
                 ("review/terms.toml", "outside-existing"),
                 ("review/terms.toml", "inside-dangling"))
        for rel, target_kind in cases:
            with self.subTest(path=rel, target=target_kind), count_source_copy() as (root, env), \
                    tempfile.TemporaryDirectory() as outside_dir:
                path = root / rel
                original = path.read_bytes()
                if target_kind == "inside-existing":
                    target = root / "review" / "alias-target.toml"
                    target.write_bytes(original)
                elif target_kind == "outside-existing":
                    target = Path(outside_dir) / "alias-target.toml"
                    target.write_bytes(original)
                elif target_kind == "inside-dangling":
                    target = root / "review" / "missing-target.toml"
                else:
                    target = Path(outside_dir) / "missing-target.toml"
                target_before = target.read_bytes() if target.exists() else None
                path.unlink()
                path.symlink_to(target)
                outputs = [root / name for name in
                           ("README.md", "docs/PROGRAM.md", "CERTIFICATE.md", "GRAPH.md")]
                outputs.extend((root / "book").rglob("*.md"))
                before = {output: output.read_bytes() for output in outputs}
                result = subprocess.run([sys.executable, "scripts/render.py"], cwd=root,
                                        env=env, capture_output=True, text=True)
                message = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, message)
                self.assertIn(rel, message)
                self.assertTrue("symlink is forbidden" in message
                                or "outside repository root" in message, message)
                self.assertEqual({output: output.read_bytes() for output in outputs}, before)
                self.assertEqual(target.read_bytes() if target.exists() else None, target_before)

    def test_public_checks_pass_over_only_an_absent_check_input(self):
        from negative_tests import count_source_copy
        from safe_push import CHECK_INPUTS, under

        tracked = [rel.as_posix() for rel in counts.tracked_markdown(REPO)
                   if (REPO / rel).is_file()]
        inside = next((rel for rel in tracked if rel.startswith("tests/")), None)
        outside = next((rel for rel in tracked if not under(rel, CHECK_INPUTS)), None)
        self.assertIsNotNone(inside, "no tracked Markdown file under tests/ to take out")
        self.assertIsNotNone(outside, "no tracked Markdown file outside the check inputs "
                                      "to take out")
        for rel, under_inputs in ((inside, True), (outside, False)):
            with self.subTest(path=rel), count_source_copy() as (root, env):
                (root / rel).unlink()       # as base_copies takes out a file the commit adds
                for script in ("check_fidelity.py", "render.py"):
                    result = subprocess.run([sys.executable, f"scripts/{script}"], cwd=root,
                                            env=env, capture_output=True, text=True)
                    message = result.stdout + result.stderr
                    self.assertNotIn("Traceback", message)
                    if under_inputs:
                        self.assertEqual(result.returncode, 0, message)
                        self.assertIn(ABSENT_NOTE.format(rel), result.stdout)
                    else:
                        self.assertNotEqual(result.returncode, 0, message)
                        self.assertIn(ABSENT_FAULT.format(rel), message)

    def test_render_refuses_dangling_optional_inputs(self):
        from negative_tests import count_source_copy

        paths = ("facts.json", "figures/I/01-idea.svg", "figures/I/01.svg",
                 "mishnah/I/01.md", "reading/I/01.md", "mishnah/intro/I.md",
                 "docs/reports/overlaps.md", "docs/reports/gaps-book-I.md")
        for rel in paths:
            with self.subTest(path=rel), count_source_copy() as (root, env), \
                    tempfile.TemporaryDirectory() as outside_dir:
                path = root / rel
                path.unlink()
                target = (Path(outside_dir) / "missing-input"
                          if rel == "facts.json" else root / "missing-input")
                path.symlink_to(target)
                outputs = [root / name for name in
                           ("README.md", "docs/PROGRAM.md", "CERTIFICATE.md", "GRAPH.md")]
                outputs.extend((root / "book").rglob("*.md"))
                before = {output: output.read_bytes() for output in outputs}
                result = subprocess.run([sys.executable, "scripts/render.py"], cwd=root,
                                        env=env, capture_output=True, text=True)
                message = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, message)
                self.assertIn(rel, message)
                self.assertTrue("symlink is forbidden" in message
                                or "outside repository root" in message, message)
                self.assertEqual({output: output.read_bytes() for output in outputs}, before)


if __name__ == "__main__":
    unittest.main()
