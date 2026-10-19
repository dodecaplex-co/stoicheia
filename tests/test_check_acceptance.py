#!/usr/bin/env python3
"""The cases of scripts/check_acceptance.py's verdicts and its comparison of two runs.

    python3 -I tests/test_check_acceptance.py        # well under a second; no Lean

CI's `acceptance` job holds a pull request to every item that passes on main: it runs the
checker on main and on the pull request, each writing its verdicts with --json, and then
`--compare MAIN PR`, which fails when an item that passes on main does not pass on the
pull request (docs/ACCEPTANCE.md, "In CI"). These cases put that comparison to small
files of verdicts, each with the outcome it should give:

* a pass that turns into a fail, into "not run" (a check not run is not a pass), or that
  the pull request's verdicts lack, is held; a fail that stays a fail, or turns into a
  pass, and an item main does not pass, is not;
* two files from different copies of the checker, which need not judge alike, or a file
  that --json did not write, cannot be compared, exit 2;
* --json writes a verdict for every item of every proposition, book and the edition, with
  each failure's messages and why an item was not run.

CI runs this file before the checker. Python 3.11 or later; standard library.
"""

from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import check_acceptance as ca  # noqa: E402


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


if __name__ == "__main__":
    unittest.main(verbosity=2)
