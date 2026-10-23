#!/usr/bin/env python3
"""The cases of scripts/check_acceptance.py's verdicts and its comparison of two runs.

    python3 -I tests/test_check_acceptance.py        # seconds; no Lean

CI's `acceptance` job holds a pull request to every item that passes on main: it runs the
checker on main and on the pull request, each writing its verdicts with --json, and then
`--compare MAIN PR`, which fails when an item that passes on main does not pass on the
pull request. The `acceptance` job in `.github/workflows/ci.yml` runs that comparison;
these cases put it to small files of verdicts, each with the outcome it should give:

* a pass that turns into a fail, into "not run" (a check not run is not a pass), or that
  the pull request's verdicts lack, is held; a fail that stays a fail, or turns into a
  pass, and an item main does not pass, is not; nor is a staging item's fail (P10, E6),
  which staging a statement before its proof brings, and which is listed;
* two files from different copies of the checker, which need not judge alike, or a file
  that --json did not write, cannot be compared, exit 2;
* --json writes a verdict for every item of every proposition, book and the edition, with
  each failure's messages and why an item was not run;
* the report, written by the generator in a small repository under several widths of
  Git's short hashes, gives one revision, which the style check's S12 reads as a commit,
  and no name for S12 to put to Lean; and the style check's findings on the report it
  replaces are quoted in E5 whole, each as one code span, which shows each message as
  the check printed it and in which neither S12 nor the report's other text rules find
  anything again (issue #178);
* CI copies the pull request's checks into main but keeps main's content pins, so an
  updated definition or expected count cannot hide a later E2 failure;
* P10 and E6 read a staged file's imports as check_fidelity's rule 3 reads Book Zero's
  (#200): in each spelling of an import that scripts/negative_tests.py's Book Zero plants
  use, a file that imports I.1 stages a declaration for it, an import the scan cannot
  read fails E6 on its line, and the same import only in a comment, a remark or a string
  ties the file to nothing.

CI runs this file before the checker. Python 3.11 or later; standard library, with sh and
rsync for scripts/copy_acceptance_checks.sh, the helper the workflow runs.
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import check_acceptance as ca  # noqa: E402
import negative_tests as negative  # noqa: E402


def run_file(verdicts: dict, checker: str = "sha256:same", revision: str = "abc1234",
             notes: dict | None = None) -> dict:
    return {"format": ca.VERDICTS_FORMAT, "checker": checker, "revision": revision,
            "run": "every item", "verdicts": verdicts, "notes": notes or {}}


class Comparison(unittest.TestCase):
    """--compare MAIN PR, as CI's `acceptance` job runs it."""

    def setUp(self):
        self.dir = Path(tempfile.mkdtemp(prefix="stoicheia-acceptance-test-"))

    def tearDown(self):
        for path in self.dir.iterdir():
            path.unlink()
        self.dir.rmdir()

    def write(self, name: str, data) -> Path:
        path = self.dir / name
        path.write_text(data if isinstance(data, str) else json.dumps(data), encoding="utf-8")
        return path

    def compare(self, main, pr) -> tuple[int, str]:
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = ca.main(["--compare", str(self.write("main.json", main)),
                            str(self.write("pr.json", pr))])
        return code, out.getvalue()

    def test_a_pass_may_not_turn_into_a_fail(self):
        main = run_file({"I.5": {"P1": "pass", "P9": "pass"}, "edition": {"E1": "pass"}})
        pr = run_file({"I.5": {"P1": "pass", "P9": "fail"}, "edition": {"E1": "pass"}},
                      notes={"I.5": {"P9": ["book/I/05.md is not as render.py writes it"]}})
        code, out = self.compare(main, pr)
        self.assertEqual(code, 1, out)
        self.assertIn("1 item that passes on main (abc1234) does not pass on the pull "
                      "request (abc1234)", out)
        self.assertIn("I.5, P9 style: fail: book/I/05.md is not as render.py writes it", out)
        self.assertNotIn("P1", out)

    def test_a_pass_may_not_turn_into_not_run_or_go_missing(self):
        main = run_file({"edition": {"E1": "pass", "E4": "pass"}, "III.1": {"P2": "pass"}})
        pr = run_file({"edition": {"E1": "not run"}},
                      notes={"edition": {"E1": ["not run (--quick)"]}})
        code, out = self.compare(main, pr)
        self.assertEqual(code, 1, out)
        self.assertIn("edition, E1 kernel: not run: not run (--quick)", out)
        self.assertIn("edition, E4 model: missing", out)
        self.assertIn("III.1, P2 record: missing", out)
        self.assertIn("3 items that pass on main", out)

    def test_the_failures_main_has_are_not_held(self):
        main = run_file({"I.1": {"P1": "fail", "P2": "fail", "P3": "not run", "P4": "pass"},
                         "Book II": {"B3": "fail"}})
        pr = run_file({"I.1": {"P1": "fail", "P2": "pass", "P3": "fail", "P4": "pass",
                               "P5": "fail"},
                       "Book II": {"B3": "fail"}, "edition": {"E6": "fail"}})
        code, out = self.compare(main, pr)
        self.assertEqual(code, 0, out)
        self.assertIn("no item that passes on main (abc1234) fails on the pull request", out)
        self.assertIn("1 pass on both, 1 more pass on the pull request, and 5 still fail or "
                      "were not run there", out)

    def test_what_a_pull_request_stages_is_listed_and_not_held(self):
        # A statement that a stage adds or changes is staged before its proof (WORKFLOW,
        # section 2), and P10 and E6 read Staging/ alone: their fail is listed, not held,
        # and the full gate holds it. Not run, or missing, it is held like any other.
        main = run_file({"I.1": {"P1": "pass", "P10": "pass"}, "edition": {"E6": "pass"}})
        staged = "Staging/Stage5/Prop01.lean still stages declarations for I.1: once proved"
        pr = run_file({"I.1": {"P1": "pass", "P10": "fail"}, "edition": {"E6": "fail"}},
                      notes={"I.1": {"P10": [staged]}})
        code, out = self.compare(main, pr)
        self.assertEqual(code, 0, out)
        self.assertIn("Not held: 2 staging items that pass on main", out)
        self.assertIn(f"I.1, P10 staging: fail: {staged}", out)
        self.assertIn("edition, E6 staging: fail", out)
        self.assertIn("fails on the pull request (abc1234), save the staging items above: 1 "
                      "pass on both", out)
        # Held with a fail of another item, and listed apart from it.
        pr = run_file({"I.1": {"P1": "fail", "P10": "fail"}, "edition": {"E6": "pass"}})
        code, out = self.compare(main, pr)
        self.assertEqual(code, 1, out)
        self.assertIn("1 item that passes on main", out)
        self.assertIn("Besides, not held: 1 staging item that passes on main (abc1234) and "
                      "fails on the pull request", out)
        self.assertLess(out.index("I.1, P1 proved: fail"), out.index("Besides"))
        self.assertLess(out.index("Besides"), out.index("I.1, P10 staging: fail"))
        # Not run, or gone missing: held.
        pr = run_file({"I.1": {"P1": "pass"}, "edition": {"E6": "not run"}})
        code, out = self.compare(main, pr)
        self.assertEqual(code, 1, out)
        self.assertIn("I.1, P10 staging: missing", out)
        self.assertIn("edition, E6 staging: not run", out)
        self.assertNotIn("Not held", out)

    def test_regressions_listed_in_the_reports_order(self):
        main = run_file({"I.10": {"P9": "pass"}, "I.2": {"P9": "pass", "P1": "pass"},
                         "Book I": {"B1": "pass"}, "edition": {"E5": "pass"}})
        pr = run_file({"I.10": {"P9": "fail"}, "I.2": {"P9": "fail", "P1": "fail"},
                       "Book I": {"B1": "fail"}, "edition": {"E5": "fail"}})
        lost = ca.regressions(ca.read_verdicts(self.write("m.json", main)),
                              ca.read_verdicts(self.write("p.json", pr)))
        self.assertEqual(lost, [("edition", "E5", "fail"), ("Book I", "B1", "fail"),
                                ("I.2", "P1", "fail"), ("I.2", "P9", "fail"),
                                ("I.10", "P9", "fail")])

    def test_different_checkers_cannot_be_compared(self):
        main = run_file({"I.1": {"P1": "pass"}}, checker="sha256:main")
        pr = run_file({"I.1": {"P1": "pass"}}, checker="sha256:pr")
        code, out = self.compare(main, pr)
        self.assertEqual(code, 2, out)
        self.assertIn("different copies of check_acceptance.py", out)

    def test_only_files_of_verdicts_are_compared(self):
        good = run_file({"I.1": {"P1": "pass"}})
        for bad in ("not JSON", [], {"verdicts": {}},
                    dict(good, format=2),
                    dict(good, checker=None),
                    dict(good, verdicts={"I.1": {"P1": "passed"}}),
                    dict(good, verdicts={"I.1": "pass"})):
            with self.subTest(bad=bad):
                code, out = self.compare(bad, good)
                self.assertEqual(code, 2, out)
                code, out = self.compare(good, bad)
                self.assertEqual(code, 2, out)
        missing = str(self.dir / "absent.json")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = ca.main(["--compare", missing, str(self.write("g.json", good))])
        self.assertEqual(code, 2, out.getvalue())

    def test_compare_takes_no_other_option(self):
        good = str(self.write("g.json", run_file({})))
        for extra in (["--quick"], ["--json", str(self.dir / "v.json")],
                      ["--output", str(self.dir / "r.md")]):
            with self.subTest(extra=extra), contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as e:
                    ca.main(["--compare", good, good, *extra])
                self.assertEqual(e.exception.code, 2)


class Verdicts(unittest.TestCase):
    """What --json writes, from the run's failures and the checks not run."""

    def setUp(self):
        ca.failures.clear()
        ca.not_run.clear()

    tearDown = setUp

    def test_every_item_has_a_verdict(self):
        ca.fail("I.5", "P9", "book/I/05.md is not as render.py writes it: regenerate it")
        ca.fail("Book III", "B2", "first\nsecond")
        ca.skip("edition", "E1", "--quick")
        data = ca.verdicts(ca.REPORT, quick=True)
        table = data["verdicts"]
        props = sum(ca.heath.BOOKS.values())
        self.assertEqual(sum(len(v) for v in table.values()),
                         props * len(ca.PROP_ITEMS) + len(ca.heath.BOOKS) * len(ca.BOOK_ITEMS)
                         + len(ca.EDITION_ITEMS))
        self.assertEqual(table["I.5"]["P9"], "fail")
        self.assertEqual(table["I.5"]["P1"], "pass")
        self.assertEqual(table["Book III"]["B2"], "fail")
        self.assertEqual(table["edition"]["E1"], "not run")
        self.assertEqual(data["notes"]["I.5"]["P9"],
                         ["book/I/05.md is not as render.py writes it: regenerate it"])
        self.assertEqual(data["notes"]["Book III"]["B2"], ["first\nsecond"])
        self.assertEqual(data["notes"]["edition"]["E1"], ["not run (--quick)"])
        self.assertNotIn("I.1", data["notes"])
        self.assertEqual(data["checker"], ca.checker_id())
        self.assertEqual(data["run"], "--quick")
        self.assertNotIn("`", data["revision"])

    def test_written_verdicts_read_back_and_compare_with_themselves(self):
        ca.fail("II.4", "P8", "the figure at a glance lacks the letter K")
        data = ca.verdicts(ca.REPORT, quick=False)
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "v.json"
            path.write_text(json.dumps(data), encoding="utf-8")
            self.assertEqual(ca.read_verdicts(path)["verdicts"], data["verdicts"])
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertEqual(ca.compare(path, path), 0, out.getvalue())


class Report(unittest.TestCase):
    """The report as the generator writes it, read by the style check's S12 and its other
    rules for a report (issue #178)."""

    def setUp(self):
        ca.failures.clear()
        ca.not_run.clear()

    tearDown = setUp

    @contextlib.contextmanager
    def repository(self):
        """A small repository, the generator's root while the context lasts, whose HEAD
        begins with a letter, so that a short form of it reads as a name; yields HEAD and
        a `git` that runs there."""
        where = ca.REPORT.relative_to(ca.ROOT)
        fixture = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        who, when = ("Fixture", "fixture@example.invalid"), "2026-10-21T00:00:00Z"
        fixture.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                       GIT_AUTHOR_NAME=who[0], GIT_AUTHOR_EMAIL=who[1], GIT_AUTHOR_DATE=when,
                       GIT_COMMITTER_NAME=who[0], GIT_COMMITTER_EMAIL=who[1],
                       GIT_COMMITTER_DATE=when)
        with tempfile.TemporaryDirectory() as d, patch.dict(os.environ, fixture, clear=True):
            root = Path(d).resolve()

            def git(*args: str) -> str:
                return subprocess.run(["git", *args], cwd=root, capture_output=True,
                                      text=True, check=True).stdout.strip()

            git("init", "-q")
            git("commit", "-q", "--allow-empty", "-m", "A fixture")
            for n in range(64):
                if not git("rev-parse", "HEAD")[0].isdigit():
                    break
                git("commit", "-q", "--amend", "--allow-empty", "-m", f"A fixture, {n}")
            head = git("rev-parse", "HEAD")
            self.assertFalse(head[0].isdigit(), head)
            with patch.object(ca, "ROOT", root), patch.object(ca, "REPORT", root / where):
                yield head, git

    @staticmethod
    def s12_asks(text: str) -> list[str]:
        """The names S12's plan puts to Lean in `text`, read as the report (call it
        outside `repository`, where ca.REPORT is the report's own path)."""
        import check_style as style
        named = style.NamedText(ca.REPORT, text, style.every_book_opens())
        _, asked, _, _ = style.s12_plan([named], True, (set(), set()))
        return sorted(n for group in asked.values() for n in group)

    @staticmethod
    def text_rules_find(text: str) -> list[str]:
        """What the style check's text rules for a report (S1, S7, S8 and S22) find in
        `text`, read as the report, each finding as the check prints it after its "✗"
        (call it outside `repository`)."""
        import check_style as style
        with patch.object(style, "failures", []):
            style.check_text(ca.REPORT, text, {"report"}, new=True)
            return [f"{rule} {path}{':' + str(line) if line else ''}: {msg}"
                    for rule, path, line, msg in style.failures]

    def regenerate(self, found: list[str]) -> str:
        """The report the generator writes in a small repository when the style check's
        findings are `found`, each as the check prints it after its "✗"."""
        with self.repository():
            style_check = subprocess.CompletedProcess(
                [], 1, "".join(f"  ✗ {finding}\n" for finding in found), "")
            with patch.object(ca, "run", return_value=style_check):
                ca.check_style_rules()
            return ca.report(ca.REPORT, {"lean_version": "4.35.0"}, quick=False)

    def test_a_regenerated_report_passes_s12(self):
        # Git's own width is seven digits in the small repository; under core.abbrev 4 it
        # is four, which is not a commit to S12 (heath.COMMIT) but a name it puts to Lean.
        # Whatever the width, the report gives one revision, in heath.COMMIT's form
        # beside the word "Revision", and S12 asks Lean about nothing in it.
        import check_style as style
        self.assertTrue(style.is_report(ca.REPORT), ca.REPORT)
        self.assertEqual(ca.REVISION_DIGITS, 12)
        texts = {}
        with self.repository() as (head, git):
            for abbrev in ("4", "9", None):
                if abbrev:
                    git("config", "core.abbrev", abbrev)
                else:
                    git("config", "--unset", "core.abbrev")
                texts[abbrev or "Git's own"] = ca.report(
                    ca.REPORT, {"lean_version": "4.35.0"}, quick=False)
        revisions = set()
        for abbrev, text in texts.items():
            with self.subTest(abbrev=abbrev):
                line = re.search(r"(?m)^- \*\*Revision:\*\* `([^`\n]*)`\.$", text)
                self.assertIsNotNone(line, text[:800])
                revision = line.group(1)
                revisions.add(revision)
                self.assertEqual(self.s12_asks(text), [], "names S12 would put to Lean")
                self.assertTrue(ca.heath.COMMIT.fullmatch(revision), revision)
                self.assertTrue(head.startswith(revision), (revision, head))
                self.assertEqual(revision, head[:ca.REVISION_DIGITS])
        self.assertEqual(len(revisions), 1, revisions)

    def test_a_finding_on_the_old_report_is_not_quoted_back_to_s12(self):
        # The style check reads the report a run replaces, and E5 quotes its findings in
        # the new one. Here S12 found names in the old report: its revision, of four
        # digits as the old generator wrote it under core.abbrev 4, or of twelve as the
        # generator writes it now, and a name Lean does not know, as B2 and E2 quote a
        # catalogue's on purpose. Quoted as they were, away from the word "Revision", each
        # is a name S12 puts to Lean in the new report, and every regeneration quotes the
        # last one's finding back. E5 fails with each whole finding as one code span, and
        # S12 asks Lean about nothing in the new report.
        where = ca.REPORT.relative_to(ca.ROOT).as_posix()
        with self.repository() as (head, _):
            names = [head[:4], head[:ca.REVISION_DIGITS], "Elements.BookI.no_such_lemma"]
            found = [f"S12 {where}:{line}: `{name}`: unknown identifier '{name}'"
                     for line, name in zip((6, 6, 120), names)]
            style_check = subprocess.CompletedProcess(
                [], 1, "".join(f"  ✗ {finding}\n" for finding in found), "")
            with patch.object(ca, "run", return_value=style_check):
                ca.check_style_rules()
            text = ca.report(ca.REPORT, {"lean_version": "4.35.0"}, quick=False)
        self.assertEqual(self.s12_asks(text), [], "names S12 would put to Lean")
        quoted = [f"`` {finding} ``" for finding in found]
        self.assertEqual(ca.failures, {("edition", "E5"): quoted})
        for message in quoted:
            self.assertIn(f"\n  - {message}\n", text)

    def test_quoted_code_is_shown_as_the_style_check_printed_it(self):
        # The texts the style check reads hold code (the report on the figures against
        # the scans gives `figures/<book>/NN.svg`), and a finding's excerpt quotes it.
        # With its backticks gone, GitHub would take `<book>` for an HTML tag and set
        # `2*a*b` in italic. Each finding is one code span, its fence one backtick longer
        # than any run of backticks in it (three for the double backticks of the last),
        # and reads, as CommonMark reads a span, exactly as the check printed it: in E5's
        # list, and as I.1's one P9 message.
        import check_style as style
        found = ['S22 docs/reports/figures-against-scans.md:3: "AB": …each of Euclid\'s '
                 'figures, `figures/<book>/NN.svg`, with its side `AB`…',
                 'S12 review/I/01.toml:9: `h : 2*a*b = c`: write the hypothesis in words, '
                 'not as a Lean binder (STYLE, section 1, "Hypotheses in words")',
                 'S22 docs/reports/figures-against-scans.md:9: "ABC": …the triangle `ABC` '
                 'of ``Elements.Book<book>.Prop<n>``…']
        text = self.regenerate(found)
        spans = [content for _, _, content in style.markdown_code_spans(text)]
        for finding in found:
            with self.subTest(finding=finding):
                self.assertIn(finding, spans)
        self.assertEqual(sorted(ca.failures), [("I.1", "P9"), ("edition", "E5")])
        self.assertIn(f"\n  - ``` {found[2]} ```\n", text)

    def test_a_finding_on_the_old_report_is_not_quoted_back_to_the_text_rules(self):
        # S1, S7 and S8 read the report outside code. An old report with an em dash, a
        # definition without its book and curly quotation marks fails each, and an S22
        # finding elsewhere holds an em dash only in code. Quoted outside code, each
        # would fail its rule again in the new report, and every regeneration would quote
        # it back. E5 quotes each finding in the new report, and none of the style
        # check's rules for a report finds anything there: S1, S7, S8 and S22 nothing,
        # and S12's plan no name.
        import check_style as style
        old = ("# The old report\n\nA line \u2014 with Definition 15 and "
               "\u201cquoted\u201d words.\n")
        found = self.text_rules_find(old)
        self.assertEqual(sorted({finding.split()[0] for finding in found}),
                         ["S1", "S7", "S8"], found)
        found.append('S22 docs/reports/figures-against-scans.md:5: "AB": …the side `AB` '
                     'and the step `A\u2014B`…')
        text = self.regenerate(found)
        self.assertEqual(self.text_rules_find(text), [], "the text rules on the new report")
        self.assertEqual(self.s12_asks(text), [], "names S12 would put to Lean")
        spans = [content for _, _, content in style.markdown_code_spans(text)]
        self.assertEqual([finding for finding in found if finding not in spans], [])
        self.assertEqual(len(ca.failures[("edition", "E5")]), len(found))


class BaselineCopy(unittest.TestCase):
    """Run the baseline-copy helper on small trees, without git or Lean."""

    # WORKFLOW section 10, step 4: values pinned to the edition, including the model's
    # account of its laws. model/ itself is outside the directories CI copies.
    pins = ("Certificate/axioms.lock", "tests/certificate_expectations.json",
            "tests/model/lock.sha256", "tests/model/laws.toml", "tests/model/MODEL.md",
            "tests/model/results/summary.txt", "tests/model/results/nested/run.txt")
    checks = ("scripts/check_acceptance.py", "scripts/check_fidelity.py",
              "scripts/copy_acceptance_checks.sh",
              "tests/test_check_acceptance.py", "tests/model/run.py",
              "tests/model/search.py", "tests/model/hyperbolic.py",
              "Certificate/Facts.lean", "review/SCHEMA.md", "review/terms.toml")
    # The lock must contain each forbidden circle rule, with the same type in the facts.
    axiom_types = {name: "fixture statement" for name in ca.cf.FORBIDDEN_CIRCLE_RULES}

    @staticmethod
    def write(root: Path, name: str, text: str) -> None:
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def trees(self, root: Path) -> tuple[Path, Path]:
        main, pr = root / "main tree", root / "pull request"
        for tree, version in ((main, "main"), (pr, "pull request")):
            for name in self.pins + self.checks + ("model/lock.sha256",):
                self.write(tree, name, f"{version}: {name}\n")
        helper = pr / "scripts/copy_acceptance_checks.sh"
        helper.write_bytes((ca.ROOT / "scripts/copy_acceptance_checks.sh").read_bytes())
        helper.chmod(0o755)
        return main, pr

    def copy_checks(self, main: Path, pr: Path) -> None:
        done = subprocess.run([str(pr / "scripts/copy_acceptance_checks.sh"),
                               str(pr), str(main)], cwd=pr, capture_output=True, text=True,
                              timeout=10)
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)

    def test_workflow_copies_checks_and_preserves_main_pins(self):
        with tempfile.TemporaryDirectory() as d:
            main, pr = self.trees(Path(d))
            self.write(main, "scripts/retired.py", "old checker\n")
            self.write(main, "tests/model/results/main-only.txt", "main result\n")
            self.write(pr, "tests/model/results/pr-only.txt", "pull request result\n")
            self.copy_checks(main, pr)
            for name in self.pins + ("model/lock.sha256",):
                with self.subTest(pin=name):
                    self.assertEqual((main / name).read_text(), f"main: {name}\n")
            for name in self.checks:
                with self.subTest(check=name):
                    self.assertEqual((main / name).read_bytes(), (pr / name).read_bytes())
            self.assertFalse((main / "scripts/retired.py").exists())
            self.assertEqual((main / "tests/model/results/main-only.txt").read_text(),
                             "main result\n")
            self.assertFalse((main / "tests/model/results/pr-only.txt").exists())

    def test_pin_absence_on_either_side_does_not_change_main(self):
        for absent in ("main", "pr"):
            with self.subTest(absent=absent), tempfile.TemporaryDirectory() as d:
                main, pr = self.trees(Path(d))
                for name in self.pins:
                    ((main if absent == "main" else pr) / name).unlink()
                self.copy_checks(main, pr)
                for name in self.pins:
                    self.assertEqual((main / name).exists(), absent != "main", name)

    def certificate(self, root: Path, word: str, count: int) -> dict:
        facts = {"axiom_types": self.axiom_types, "vocabulary": {"word": word}}
        entries = {"I.1": (None, {"axioms": [f"rule{i}" for i in range(count)]})}
        _, errors = ca.captured(ca.cf.check_lock, facts, root / "Certificate/axioms.lock")
        _, more = ca.captured(ca.cf.check_expectations, entries,
                              root / "tests/certificate_expectations.json")
        errors += more
        return run_file({"edition": {"E2": "fail" if errors else "pass"}},
                        notes={"edition": {"E2": errors}})

    def test_updated_pin_cannot_hide_a_pr_certificate_failure(self):
        for changed in ("definition", "expected count"):
            with self.subTest(changed=changed), tempfile.TemporaryDirectory() as d:
                root = Path(d)
                main, pr = self.trees(root)
                pr_word = "new definition" if changed == "definition" else "main definition"
                pr_count = 2 if changed == "expected count" else 1
                for tree, word, count in ((main, "main definition", 1),
                                          (pr, pr_word, pr_count)):
                    self.write(tree, "Certificate/axioms.lock",
                               ca.cf.render_lock(self.axiom_types, {"word": word}))
                    self.write(tree, "tests/certificate_expectations.json", json.dumps({
                        "expectations": [{"ref": "I.1", "field": "axioms",
                                          "count": {"prefix": "rule", "is": count},
                                          "why": "the edition's expected count"}]}))
                self.assertEqual(self.certificate(main, "main definition", 1)
                                 ["verdicts"]["edition"]["E2"], "pass")
                self.assertEqual(self.certificate(pr, pr_word, pr_count)
                                 ["verdicts"]["edition"]["E2"], "pass")
                self.copy_checks(main, pr)
                before = self.certificate(main, "main definition", 1)
                # A subsequent PR defect violates its own count. The updated pin must
                # not make unchanged main fail too, excusing this as pre-existing.
                after = self.certificate(pr, pr_word, pr_count + 1)
                self.assertEqual(after["verdicts"]["edition"]["E2"], "fail")
                self.write(root, "main.json", json.dumps(before))
                self.write(root, "pr.json", json.dumps(after))
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    code = ca.main(["--compare", str(root / "main.json"),
                                    str(root / "pr.json")])
                self.assertEqual(code, 1, out.getvalue())
                self.assertIn("edition, E2 certificate: fail", out.getvalue())
                self.assertEqual(before["verdicts"]["edition"]["E2"], "pass")


class StagedImports(unittest.TestCase):
    """P10 and E6 on a small tree, without Lean (#200): a staged file's imports read as
    check_fidelity's rule 3 reads Book Zero's, through whitespace, comments and «…» names,
    and never in a comment or a string."""

    rel = "Staging/Planted/Planted.lean"
    # `Prop1` with no book, in a folder that names none: only an import ties it to I.1.
    declaration = "\ntheorem Planted.Prop1.statement : True := trivial\n"

    def setUp(self):
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        self.enterContext(patch.object(ca, "ROOT", self.root))
        self.enterContext(patch.object(ca, "failures", {}))

    def verdicts(self, text: str) -> dict:
        """What P10 and E6 find with `text` and the declaration staged at `rel`."""
        path = self.root / self.rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text + self.declaration, encoding="utf-8")
        ca.failures.clear()
        ca.check_staging()
        return dict(ca.failures)

    def ties(self, ref: str) -> dict:
        return {(ref, "P10"): [f"{self.rel} still stages declarations for {ref}: once proved, "
                               "a statement moves to Elements/ and its staged copy is deleted"]}

    def no_one(self, count: int = 1) -> str:
        return (f"{self.rel} still stages {count} declaration(s), for no one proposition: "
                "move them to Elements/ or retire them")

    def test_each_spelling_of_the_book_zero_plants_ties_the_file_to_its_proposition(self):
        for what, text, *extra in negative.BOOK_ZERO_SPELLINGS:
            with self.subTest(what=what):
                found = self.verdicts(text)
                line = text.count("\n", 0, text.rindex("import")) + 1
                if "Elements.Companions" in text:
                    # P10 reads the module a file names, not what that module brings in.
                    self.assertEqual(found, {("edition", "E6"): [self.no_one()]})
                elif extra and "cannot read this import for certain" in extra[0]:
                    self.assertEqual(found, {("edition", "E6"): [
                        f"{self.rel}:{line}: an import the scan cannot read for certain, so "
                        "which propositions this file imports cannot be told: each part of the module's name must be a plain name, in «…» or not, "
                        "and whitespace must follow it",
                        self.no_one()]})
                else:
                    self.assertEqual(found, self.ties("I.1"))

    def test_the_same_import_in_a_comment_or_a_string_ties_the_file_to_nothing(self):
        _, text = negative.BOOK_ZERO_TEXT
        self.assertEqual(self.verdicts(text), {("edition", "E6"): [self.no_one(3)]})
        # Each holds the import at the start of a line, as a reading of the raw text found it.
        for text in ("/-\nimport Elements.BookI.Prop01\n-/\n",
                     "/- /- -/\nimport Elements.BookI.Prop01\n-/\n",
                     'def s := "\nimport Elements.BookI.Prop01"\n',
                     "def s := r#\"\nimport Elements.BookI.Prop01\"#\n"):
            with self.subTest(text=text):
                self.assertNotIn(("I.1", "P10"), self.verdicts(text))

    def test_the_file_is_read_from_its_bytes(self):
        # A lone carriage return ends no `--` comment for Lean, so the import on the next
        # line is real; read with universal newlines, it would end the comment and open a
        # string holding the import, which would then tie the file to nothing.
        self.assertEqual(self.verdicts('-- r\r"\nimport Elements.BookI.Prop01\n-- "\n'),
                         self.ties("I.1"))

    def test_an_import_of_one_book_alone_ties_the_file(self):
        self.assertEqual(self.verdicts("import «Elements».«BookIII».Prop01\n"),
                         self.ties("III.1"))
        self.assertEqual(self.verdicts("import Elements.BookII.Prop01.Aux\n"),
                         self.ties("II.1"))
        self.assertEqual(self.verdicts("import Elements.BookI.Prop01\n"
                                       "import  Elements.BookII.Prop01\n"),
                         {("edition", "E6"): [self.no_one()]})


if __name__ == "__main__":
    unittest.main(verbosity=2)
