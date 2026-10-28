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
  ties the file to nothing;
* a checking run asks Lake first whether Elements and Audit are built and current: Lake's
  `--no-build` exiting 3, a stale Audit build, stops it with exit 2, saying why on
  stdout, before any check runs and with no report or verdicts written; so do Lake's exit
  1, said to be Lake unable to answer and not a stale build, a `lake` that cannot be
  started, and Lake with no answer; exiting 0 lets it go on; with no `lake` to run it goes
  on as before; and --compare and --check-current never ask;
* --check-current, on a repository of its own: a report committed after the commit it
  names is current, and so it stays when a later commit changes the report alone, and
  when main, unmoved, merges the candidate with `--no-ff`; a later commit of any other
  file, or a merge after main moved, a rename onto the report's path or off it, a change
  not committed anywhere (the report's own too, or a file untracked), a file the index
  marks assume-unchanged or skip-worktree, a `--quick` run or a Run line of neither kind,
  a report of changes not committed, a revision that names no commit, or is no commit of
  HEAD's history, a branch or tag named as its digits included, or a revision that a
  `git replace` stands in for, is not, exit 1; and revision(), the generator's own walk,
  takes a rename onto the report as a change to another file; no git checkout, no report
  at HEAD, or one not UTF-8, or without its marker, its Revision line or its Run line,
  cannot begin, exit 2; and it takes no other option.

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


class StaleBuild(unittest.TestCase):
    """A checking run asks Lake, before any check and before it writes anything, whether
    Elements and Audit are built and current, with a stand-in for subprocess.run that
    answers for `lake`, as tests/test_screen.py's do: no Lean. Each check is stubbed, and
    records that it ran."""

    checks = ("check_certificate", "load_records", "check_propositions", "check_review_items",
              "check_books", "check_style_rules", "check_links", "check_runs")
    # Lake's exit 3, and lines in the form it prints them, on a tree whose Audit build is
    # older than its sources: it names the first modules it would build.
    stale = ("✖ [178/195] Building Audit.Overlaps\n"
             "error: target is out-of-date and needs to be rebuilt\n"
             "✖ [183/195] Building Audit.Crossing\n"
             "error: target is out-of-date and needs to be rebuilt\n"
             "✖ [190/195] Building Audit.Centre\n"
             "error: target is out-of-date and needs to be rebuilt\n"
             "Some required targets logged failures:\n"
             "- Audit.Overlaps\n"
             "- Audit.Crossing\n"
             "- Audit.Centre\n")
    # Lake's exit 1, and what it printed, with a lakefile it cannot read.
    unread = "error: lakefile.toml:3:0: error: unexpected end of input; expected ']'\n"

    def setUp(self):
        self.dir = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        self.enterContext(patch.object(ca, "failures", {}))
        self.enterContext(patch.object(ca, "not_run", {}))
        self.enterContext(patch.object(ca, "revision", return_value="`0123456789ab`"))
        self.ran: list[str] = []
        for name in self.checks:
            self.enterContext(patch.object(
                ca, name, side_effect=lambda *_, name=name: self.ran.append(name)))
        self.asked: list = []
        self.report, self.verdicts = self.dir / "report.md", self.dir / "verdicts.json"

    def lake(self, answer):
        """subprocess.run, with `lake` answering `answer`: its exit and what it printed, or
        an exception to raise (no `lake` to run, one that cannot be started, or no answer
        in time)."""
        real = subprocess.run

        def run(argv, **kw):
            if argv[:1] != ["lake"]:
                return real(argv, **kw)
            self.asked.append((list(argv), kw.get("cwd")))
            if isinstance(answer, BaseException):
                raise answer
            code, said = answer
            return subprocess.CompletedProcess(argv, code, said, "")
        return patch.object(ca.subprocess, "run", run)

    def check(self, *extra: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = ca.main(["--output", str(self.report), "--json", str(self.verdicts), *extra])
        return code, out.getvalue(), err.getvalue()

    def test_a_stale_build_stops_the_run_before_any_check(self):
        # Lake decides what is stale by its traces; the checker only asks it.
        self.assertEqual(ca.CURRENT_BUILD, ["lake", "build", "--no-build", "Elements", "Audit"])
        for extra in ((), ("--quick",)):
            with self.subTest(extra=extra), self.lake((3, self.stale)):
                self.asked.clear()
                code, out, err = self.check(*extra)
                self.assertEqual(code, 2, out + err)
                self.assertEqual(self.asked, [(ca.CURRENT_BUILD, ca.ROOT)])
                self.assertIn("cannot begin: `lake build --no-build Elements Audit` exits 3: "
                              "Lake does not find Elements and Audit built and current", out)
                for module in ("Audit.Overlaps", "Audit.Crossing", "Audit.Centre"):
                    self.assertIn(f"\n  - {module}\n", out)
                self.assertIn("`lake build`, `lake build Audit`, then `lake env lean "
                              "Certificate/Facts.lean`", out)
                self.assertEqual(err, "")
                self.assertEqual(self.ran, [])
                self.assertFalse(self.report.exists())
                self.assertFalse(self.verdicts.exists())

    def test_lake_unable_to_answer_stops_the_run(self):
        # An exit but 0 or 3 is Lake unable to answer, and not a stale build; a `lake`
        # that exists but cannot be started is no answer either, and not "no `lake`".
        cases = {
            "exit 1": ((1, self.unread),
                       "`lake build --no-build Elements Audit` exits 1: Lake could not answer "
                       "whether the build is current (a toolchain or lakefile problem, say)"),
            "cannot start": (PermissionError(13, "Permission denied", "lake"),
                             "`lake build --no-build Elements Audit` could not be started "
                             "([Errno 13] Permission denied: 'lake')"),
        }
        for what, (answer, said) in cases.items():
            with self.subTest(what=what), self.lake(answer):
                code, out, err = self.check()
                self.assertEqual(code, 2, out + err)
                self.assertIn(f"cannot begin: {said}", out)
                self.assertNotIn("does not find Elements and Audit built", out)
                self.assertEqual(err, "")
                self.assertEqual(self.ran, [])
                self.assertFalse(self.report.exists())
                self.assertFalse(self.verdicts.exists())
                if what == "exit 1":
                    self.assertIn(f"Lake printed:\n  {self.unread}", out)

    def test_a_current_build_lets_the_run_go_on(self):
        with self.lake((0, "")):
            code, out, err = self.check()
        self.assertEqual(code, 0, out + err)
        self.assertEqual(self.asked, [(ca.CURRENT_BUILD, ca.ROOT)])
        self.assertEqual(self.ran, list(self.checks))
        self.assertTrue(self.report.read_text(encoding="utf-8").startswith(ca.GENERATED))
        self.assertTrue(self.verdicts.exists())

    def test_no_lake_to_run_keeps_the_path_it_had(self):
        # With no `lake` at all, the run goes on as it did before Lake was asked, and the
        # checks that need Lean say that they could not ask it. So too with the real
        # subprocess.run, on a PATH that has no `lake`.
        empty = self.dir / "no-lake"
        empty.mkdir()
        with patch.dict(os.environ, {"PATH": str(empty)}):
            self.assertIsNone(ca.build_problem())
        with self.lake(FileNotFoundError(2, "No such file or directory", "lake")):
            code, out, err = self.check()
        self.assertEqual(code, 0, out + err)
        self.assertNotIn("cannot begin", out + err)
        self.assertEqual(self.ran, list(self.checks))
        self.assertTrue(self.report.exists())

    def test_lake_with_no_answer_stops_the_run(self):
        with self.lake(subprocess.TimeoutExpired(ca.CURRENT_BUILD, ca.BUILD_TIMEOUT)):
            code, out, err = self.check()
        self.assertEqual(code, 2, out + err)
        self.assertIn(f"did not answer in {ca.BUILD_TIMEOUT} seconds", out)
        self.assertEqual(self.ran, [])
        self.assertFalse(self.report.exists())

    def test_compare_and_check_current_do_not_ask_lake(self):
        good = self.dir / "v.json"
        good.write_text(json.dumps(run_file({"I.1": {"P1": "pass"}})), encoding="utf-8")
        with self.lake((3, self.stale)), patch.object(ca, "check_current", return_value=0), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(ca.main(["--compare", str(good), str(good)]), 0)
            self.assertEqual(ca.main(["--check-current"]), 0)
        self.assertEqual(self.asked, [])


class CheckCurrent(unittest.TestCase):
    """--check-current on a repository of its own, with git's environment cleared as
    Report's is: the report as HEAD holds it, read through git, against HEAD and the
    worktree."""

    def setUp(self):
        self.where = ca.REPORT.relative_to(ca.ROOT).as_posix()
        fixture = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        who, when = ("Fixture", "fixture@example.invalid"), "2026-10-25T00:00:00Z"
        fixture.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                       GIT_AUTHOR_NAME=who[0], GIT_AUTHOR_EMAIL=who[1], GIT_AUTHOR_DATE=when,
                       GIT_COMMITTER_NAME=who[0], GIT_COMMITTER_EMAIL=who[1],
                       GIT_COMMITTER_DATE=when)
        self.enterContext(patch.dict(os.environ, fixture, clear=True))
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        self.enterContext(patch.object(ca, "ROOT", self.root))
        self.enterContext(patch.object(ca, "REPORT", self.root / self.where))
        self.enterContext(patch.object(ca, "failures", {}))
        self.enterContext(patch.object(ca, "not_run", {}))
        self.git("init", "-q")
        self.library = self.commit("The library", "Elements.lean", "-- the library\n")

    def git(self, *args: str) -> str:
        return subprocess.run(["git", *args], cwd=self.root, capture_output=True, text=True,
                              check=True).stdout.strip()

    def write(self, name: str, text: str) -> None:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def commit(self, message: str, name: str, text: str) -> str:
        """`name` written and committed alone; the commit, in the report's digits."""
        self.write(name, text)
        self.git("add", "--", name)
        self.git("commit", "-q", "-m", message)
        return self.git("rev-parse", f"--short={ca.REVISION_DIGITS}", "HEAD")

    def regenerate(self, quick: bool = False) -> str:
        """The report the generator writes now, its revision read from git."""
        return ca.report(ca.REPORT, {"lean_version": "4.35.0"}, quick=quick)

    def check(self, *args: str) -> tuple[int, str]:
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = ca.main(["--check-current", *args])
        return code, out.getvalue()

    def test_a_report_committed_after_the_commit_it_names_is_current(self):
        text = self.regenerate()
        self.assertIn(f"- **Revision:** `{self.library}`.", text)
        self.commit("The report", self.where, text)
        code, out = self.check()
        self.assertEqual(code, 0, out)
        self.assertIn(f"a run of every item on `{self.library}`", out)
        # Regenerated, with a failure this time, and committed again: the files read are
        # still the library's.
        ca.fail("I.1", "P9", "book/I/01.md is not as render.py writes it: regenerate it")
        self.commit("The report again", self.where, self.regenerate())
        code, out = self.check()
        self.assertEqual(code, 0, out)

    def test_a_later_commit_of_any_other_file_is_not_current(self):
        self.commit("The report", self.where, self.regenerate())
        self.commit("More library", "Elements.lean", "-- the library, grown\n")
        self.commit("An audit", "Audit.lean", "-- an audit\n")
        code, out = self.check()
        self.assertEqual(code, 1, out)
        self.assertIn(f"HEAD differs from its revision `{self.library}` in more than the "
                      "report: Audit.lean, Elements.lean", out)
        self.assertIn("Regenerate it on a freshly built tree", out)

    def release(self) -> tuple[str, str]:
        """Main's branch, and the candidate: a branch `release` from it, with a change to
        the library and then its report, committed by itself."""
        main = self.git("branch", "--show-current")
        self.git("checkout", "-q", "-b", "release")
        candidate = self.commit("The release", "Elements.lean", "-- the library, released\n")
        self.commit("The report", self.where, self.regenerate())
        return main, candidate

    def test_a_merge_of_the_candidate_into_an_unmoved_main_is_current(self):
        # HEAD is compared with the report's revision tree to tree. revision()'s walk of
        # first parents names main's merge commit itself, for it differs from its first
        # parent in all that the release changed.
        main, candidate = self.release()
        code, out = self.check()
        self.assertEqual(code, 0, out)
        self.git("checkout", "-q", main)
        self.git("merge", "-q", "--no-ff", "-m", "Merge the release", "release")
        merged = self.git("rev-parse", f"--short={ca.REVISION_DIGITS}", "HEAD")
        self.assertEqual(ca.revision(ca.REPORT), f"`{merged}`")
        code, out = self.check()
        self.assertEqual(code, 0, out)
        self.assertIn(f"a run of every item on `{candidate}`", out)

    def test_a_merge_after_main_moved_first_is_not_current(self):
        main, candidate = self.release()
        self.git("checkout", "-q", main)
        self.commit("Main moves first", "Other.lean", "-- another file\n")
        self.git("merge", "-q", "--no-ff", "-m", "Merge the release", "release")
        code, out = self.check()
        self.assertEqual(code, 1, out)
        self.assertIn(f"HEAD differs from its revision `{candidate}` in more than the "
                      "report: Other.lean\n", out)

    def test_a_rename_onto_the_report_or_off_it_is_seen(self):
        # Git's rename detection shows a file moved onto the report's path as the report
        # alone; with --no-renames the file it left is seen too, here and in revision()'s
        # walk. A rename off the path, with a new report written there, adds a file.
        draft = self.commit("A draft of the report", "draft.md", self.regenerate())
        self.write(self.where, self.regenerate())
        self.git("rm", "-q", "draft.md")
        self.git("add", "--", self.where)
        self.git("commit", "-q", "-m", "The draft becomes the report")
        self.assertRegex(self.git("diff", "--name-status", "HEAD^", "HEAD"),
                         rf"^R\d+\tdraft\.md\t{re.escape(self.where)}$")
        moved = self.git("rev-parse", f"--short={ca.REVISION_DIGITS}", "HEAD")
        self.assertEqual(ca.revision(ca.REPORT), f"`{moved}`")
        code, out = self.check()
        self.assertEqual(code, 1, out)
        self.assertIn(f"HEAD differs from its revision `{draft}` in more than the report: "
                      "draft.md\n", out)
        self.git("reset", "-q", "--hard", self.library)
        self.commit("The report", self.where, self.regenerate())
        grown = self.commit("More library", "Elements.lean", "-- the library, grown\n")
        text = self.regenerate()
        self.git("mv", self.where, "docs/reports/old.md")
        self.write(self.where, text)
        self.git("add", "--", self.where)
        self.git("commit", "-q", "-m", "The report moved off, and a new one")
        code, out = self.check()
        self.assertEqual(code, 1, out)
        self.assertIn(f"HEAD differs from its revision `{grown}` in more than the report: "
                      "docs/reports/old.md\n", out)

    def test_a_change_not_committed_anywhere_is_not_current(self):
        # The report is read as HEAD holds it: changed or deleted in the working copy, it
        # is still read, and its change is one more change not committed.
        self.commit("The report", self.where, self.regenerate())
        self.assertEqual(self.check()[0], 0)
        cases = {
            "a change not staged": lambda: self.write("Elements.lean", "-- changed\n"),
            "a change staged": lambda: (self.write("Elements.lean", "-- changed\n"),
                                        self.git("add", "Elements.lean")),
            "the report's own change": lambda: self.write(self.where, "not a report\n"),
            "the report deleted": lambda: (self.root / self.where).unlink(),
            "a file untracked": lambda: self.write("notes/draft.md", "a draft\n"),
        }
        for what, change in cases.items():
            with self.subTest(what=what):
                change()
                code, out = self.check()
                self.assertEqual(code, 1, out)
                self.assertIn("the worktree has changes not committed", out)
                self.assertNotIn("HEAD differs", out)
                if what == "a file untracked":
                    self.assertIn("notes/draft.md (untracked)", out)
                self.git("reset", "-q", "--hard")
                self.git("clean", "-q", "-f", "-d")
                self.assertEqual(self.check()[0], 0)

    def test_a_file_the_index_marks_is_not_current(self):
        # A file marked assume-unchanged or skip-worktree is not compared with the
        # worktree, so `git status` shows no change in it, changed or not.
        self.commit("The report", self.where, self.regenerate())
        for mark in ("assume-unchanged", "skip-worktree"):
            with self.subTest(mark=mark):
                self.write("Elements.lean", "-- changed, and hidden\n")
                self.git("update-index", f"--{mark}", "--", "Elements.lean")
                self.assertEqual(self.git("status", "--porcelain"), "")
                code, out = self.check()
                self.assertEqual(code, 1, out)
                self.assertIn("the index marks files that git does not compare with the "
                              "worktree", out)
                self.assertIn("cannot be shown to have no change: Elements.lean;", out)
                self.assertNotIn("the worktree has changes", out)
                self.git("update-index", f"--no-{mark}", "--", "Elements.lean")
                self.git("checkout", "--", "Elements.lean")
                self.assertEqual(self.check()[0], 0)

    def test_a_quick_run_is_not_current(self):
        self.commit("The report", self.where, self.regenerate(quick=True))
        code, out = self.check()
        self.assertEqual(code, 1, out)
        self.assertIn("it is a `--quick` run", out)
        self.assertNotIn("HEAD differs", out)

    def test_a_report_of_changes_not_committed_is_not_current(self):
        self.write("Elements.lean", "-- changed, not committed\n")
        text = self.regenerate()
        self.assertIn(f"`{self.library}`, with changes not yet committed.", text)
        self.git("checkout", "--", "Elements.lean")
        self.commit("The report", self.where, text)
        code, out = self.check()
        self.assertEqual(code, 1, out)
        self.assertIn(f"it is a run on `{self.library}` with changes not yet committed", out)
        self.assertNotIn("the worktree has", out)

    def test_a_revision_that_is_no_commit_of_the_history_is_not_current(self):
        text = self.regenerate()
        self.git("checkout", "-q", "-b", "side")
        side = self.commit("A side", "Side.lean", "-- aside\n")
        self.git("checkout", "-q", "-")
        for digits, why in (("0123456789ab", "is not one commit of this repository"),
                            (side, "is not in the history of HEAD")):
            with self.subTest(digits=digits):
                self.commit(f"A report of {digits}", self.where,
                            text.replace(f"`{self.library}`", f"`{digits}`"))
                code, out = self.check()
                self.assertEqual(code, 1, out)
                self.assertIn(f"its revision `{digits}` {why}", out)

    def test_a_branch_or_tag_named_as_the_revision_is_not_its_commit(self):
        # Git reads a name as a branch or a tag before it reads it as a short hash: one
        # named as the report's digits, at a commit with the same files, is not the commit
        # the report names.
        digits = "a" * ca.REVISION_DIGITS
        self.commit("A report of no commit", self.where,
                    self.regenerate().replace(f"`{self.library}`", f"`{digits}`"))
        for kind in ("branch", "tag"):
            with self.subTest(kind=kind):
                self.git(kind, digits, self.library)
                self.assertEqual(self.git("rev-parse", f"{digits}^{{commit}}"),
                                 self.git("rev-parse", self.library))
                code, out = self.check()
                self.assertEqual(code, 1, out)
                self.assertIn(f"its revision `{digits}` is not one commit of this repository",
                              out)
                self.git(kind, "-d", digits)

    def test_a_replacement_of_the_revision_is_not_read(self):
        # `git replace` can make the revision read as a commit carrying HEAD's files; the
        # check runs git with GIT_NO_REPLACE_OBJECTS=1.
        self.commit("The report", self.where, self.regenerate())
        self.commit("More library", "Elements.lean", "-- the library, grown\n")
        self.assertEqual(self.check()[0], 1)
        stand_in = self.git("commit-tree", "HEAD^{tree}", "-m", "A stand-in")
        self.git("replace", self.git("rev-parse", self.library), stand_in)
        self.assertEqual(self.git("diff", "--name-only", self.library, "HEAD"), "")
        code, out = self.check()
        self.assertEqual(code, 1, out)
        self.assertIn(f"HEAD differs from its revision `{self.library}` in more than the "
                      "report: Elements.lean\n", out)

    def test_a_revision_or_a_run_line_it_cannot_take_is_not_current(self):
        text = self.regenerate()
        cases = {
            "no commit": (text.replace(f"`{self.library}`", "not a git checkout"),
                          "it names no commit: its revision is \"not a git checkout\""),
            "a run of neither kind": (text.replace("- **Run:** every item.",
                                                   "- **Run:** some of the items."),
                                      "it is not a run of every item: its Run line says "
                                      "\"some of the items.\""),
        }
        for what, (bad, why) in cases.items():
            with self.subTest(what=what):
                self.commit(f"A report of {what}", self.where, bad)
                code, out = self.check()
                self.assertEqual(code, 1, out)
                self.assertIn(why, out)
                self.assertNotIn("`--quick`", out)

    def test_what_it_cannot_read_cannot_begin(self):
        code, out = self.check()
        self.assertEqual(code, 2, out)
        self.assertIn(f"cannot begin: HEAD holds no {self.where}", out)
        text = self.regenerate()
        broken = {
            "the generated marker": (text.split("\n", 1)[1],
                                     "its first line is not the generated marker"),
            "the Revision line": (re.sub(r"(?m)^- \*\*Revision:\*\*.*\n", "", text),
                                  "it has no Revision line"),
            "the Run line": (re.sub(r"(?m)^- \*\*Run:\*\*.*\n", "", text),
                             "it has no Run line"),
        }
        for what, (bad, why) in broken.items():
            with self.subTest(without=what):
                self.commit(f"A report without {what}", self.where, bad)
                code, out = self.check()
                self.assertEqual(code, 2, out)
                self.assertIn(f"is not a report this script writes: {why}", out)
        with self.subTest(without="UTF-8"):
            (self.root / self.where).write_bytes(ca.GENERATED.encode() + b"\n\xff\xfe\n")
            self.git("add", "--", self.where)
            self.git("commit", "-q", "-m", "A report not UTF-8")
            code, out = self.check()
            self.assertEqual(code, 2, out)
            self.assertIn(f"cannot begin: HEAD's {self.where} is not UTF-8", out)
        # No git checkout, then a repository with no commit.
        elsewhere = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        with patch.object(ca, "ROOT", elsewhere), \
                patch.object(ca, "REPORT", elsewhere / self.where), \
                patch.dict(os.environ, {"GIT_CEILING_DIRECTORIES": str(elsewhere.parent)}):
            for made in (None, ["git", "init", "-q"]):
                with self.subTest(made=made):
                    if made:
                        subprocess.run(made, cwd=elsewhere, check=True)
                    code, out = self.check()
                    self.assertEqual(code, 2, out)
                    self.assertIn("cannot begin: this is not a git checkout with a commit", out)

    def test_check_current_takes_no_other_option(self):
        for extra in (["--compare", "main.json", "pr.json"], ["--quick"],
                      ["--json", "verdicts.json"], ["--output", "report.md"]):
            with self.subTest(extra=extra), contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as e:
                    ca.main(["--check-current", *extra])
                self.assertEqual(e.exception.code, 2)


if __name__ == "__main__":
    unittest.main(verbosity=2)
