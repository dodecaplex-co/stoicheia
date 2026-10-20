#!/usr/bin/env python3
"""File-only count and marker regressions: python3 -I tests/test_generated_counts.py."""

import sys
import tempfile
import unittest
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
            "axioms": 6, "tacit-rules": 2, "postulates": 2, "vocabulary": 3,
            "companions": 3, "companion-propositions": 2,
            "reviews:I": 2, "reviews:II": 1, "reviews:III": 3,
            "reviews:I:full": 1, "reviews:II:full": 0, "reviews:III:full": 3,
            "acceptance:failing": 7, "acceptance:passing": 2,
        })

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

    def test_multiple_forms_preserve_surrounding_prose(self):
        text = ("<!-- scope:I -->A <!-- count:companions:Word -->One<!-- /count -->"
                " theorem; <!-- count:companion-propositions:word -->one<!-- /count -->"
                " propositions.<!-- /scope:I -->\n<!-- status -->\n<!-- /status -->")
        path = self.write("README.md", text)
        changes, errors = self.scan(["README.md"])
        self.assertEqual(errors, [])
        self.assertEqual(changes[path], text.replace("-->One<!--", "-->Three<!--")
                         .replace("-->one<!--", "-->two<!--"))

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

    def test_history_is_refused_and_whole_outputs_are_excluded(self):
        history = ["docs/briefs/0002-decisions.md", "docs/reports/crew/new-log.md",
                   "docs/reports/read-through-01.md", counts.ACCEPTANCE]
        outputs = ["book/I/index.md", "CERTIFICATE.md", "GRAPH.md"]
        for path in history + outputs:
            self.write(path, "<!-- count:vocabulary -->3<!-- /count -->")
        changes, errors = self.scan(history + outputs)
        self.assertEqual(changes, {})
        self.assertEqual(len(errors), len(history))
        for path, error in zip(history, errors):
            self.assertIn(f"{path}:1:", error)
            self.assertIn("forbidden in dated history", error)

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


if __name__ == "__main__":
    unittest.main()
