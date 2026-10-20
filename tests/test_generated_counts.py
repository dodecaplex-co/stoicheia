#!/usr/bin/env python3
"""File-only count and marker regressions: python3 -I tests/test_generated_counts.py."""

import os
import subprocess
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
            self.assertIn("linked/notes.md", errors[0])
            self.assertIn("outside repository root", errors[0])
            with patch.object(render, "ROOT", self.root):
                for path in (self.root / "linked/notes.md", target):
                    with self.assertRaisesRegex(ValueError, "outside repository root"):
                        render.read_text(path)
                    with self.assertRaisesRegex(ValueError, "outside repository root"):
                        render.write_text(path, "Changed.")
            self.assertEqual(target.read_text(), text)

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


if __name__ == "__main__":
    unittest.main()
