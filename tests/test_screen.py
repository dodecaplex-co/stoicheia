#!/usr/bin/env python3
"""The cases of Audit/screen.py, the overlap screen: which tries it makes, and how it reads
what Lean says of them.

    python3 -I tests/test_screen.py        # well under a second; no Lean, no network

The screen has Lean's `grind` try every statement of facts.json from no rule, each rule,
each family of rules and each pair of them, and reports what closes
([docs/reports/overlaps.md](../docs/reports/overlaps.md), "How the rows were found"). A run
needs Lean and takes minutes. These cases need neither: they put the screen's own
functions to small inputs, each with the answer the screen should give.

* The attempts: for each statement a bare one with no rule, then each axiom, each family,
  each pair of the rules about circles and each pair of families; a rule about circles
  missing from facts.json stops the screen.
* The tries: each attempt with rules is two, one for each way of giving `grind` its rules,
  each without the rules `grind` refuses in that way, and none is made with no rule left;
  the bare attempt is one try, with no rule.
* Lean's log of a file of tries: a try closes only when nothing is reported from its
  `set_option` line to the next try's, neither an error nor a `sorry`; a timeout is told
  apart from any other error, and an error is read whether or not Lean names its kind
  after the word; an error on a try's `set_option` line is that try's, not the
  one before; a log that stops before the file's last line, or an error in the preamble,
  stops the screen.
* The pass over the rules: an error on a case's lines is a refusal of that case's rule in
  that case's way; any other error stops the screen.
* The pass over the definitions: a definition reached that no list provides for, a name
  that is not the edition's, a failed run or an empty one stops the screen.
* The known rows: III.2, III.5 and III.6 must close by a rule; closed only by the bare try,
  a row is lost.
* The lists: the definitions unfolded, chosen and left as they are do not overlap; every
  file of tries proves the controls, and unfolds every definition listed.

Nothing runs these in CI yet: whoever changes the screen runs this file. Python 3.11 or
later; standard library.
"""

from __future__ import annotations

import itertools
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "Audit"))
import screen  # noqa: E402

NAME = "Screen0.lean"


def file_of(tries: list[tuple[str, str, str]]) -> str:
    """A file of tries, as the screen writes it."""
    return (screen.HEAD + "".join(screen.theorem(n, d, g, 100) for n, d, g in tries)
            + f'#print "{screen.END}"\n')


def line_of(text: str, start: str) -> int:
    """The number of the first line of `text` that begins with `start`."""
    return next(i + 1 for i, line in enumerate(text.splitlines()) if line.startswith(start))


def given(line: str) -> list[str]:
    """The names a line of Lean gives `grind`, in its order."""
    return line.split("grind [", 1)[1].removesuffix("]").split(", ")


def unfolded() -> list[str]:
    """The names every try gives `grind` beyond its rules: each definition, then each lemma."""
    return [f"Elements.{d}" for d in screen.DEFS] + list(screen.CHOSEN.values())


def message(line: int, col: int, what: str, name: str = NAME) -> str:
    return f"/somewhere/{name}:{line}:{col}: {what}\n"


END_LINE = f"{screen.END}\n"
TIMEOUT = ("error: (deterministic) timeout at `whnf`, maximum number of heartbeats (100) "
           "has been reached")
SORRY = "warning: declaration uses `sorry`"


class Attempts(unittest.TestCase):
    def facts(self, extra: dict[str, str]) -> dict:
        modules = {c: "Elements.Foundations.Tacit.Circles" for c in screen.CIRCLE}
        modules.update(extra)
        return {"propositions": [{"name": "BookI.Prop1", "ref": "I.1"},
                                 {"name": "BookIII.Prop2", "ref": "III.2"}],
                "axiom_modules": modules}

    def test_each_statement_has_every_attempt_once(self):
        facts = self.facts({"Postulate1": "Elements.Foundations.Postulates",
                            "Tacit.len_symm": "Elements.Foundations.Tacit.Metric"})
        jobs = screen.attempts(facts)
        axioms, families = 2 + len(screen.CIRCLE), 3
        each = (1 + axioms + families + len(list(itertools.combinations(screen.CIRCLE, 2)))
                + 3)
        self.assertEqual(len(jobs), 2 * each)
        self.assertEqual(len({name for name, _, _ in jobs}), len(jobs))
        self.assertEqual(jobs[0], ("bare__BookI_Prop1", "BookI.Prop1", []))
        self.assertEqual(jobs[each], ("bare__BookIII_Prop2", "BookIII.Prop2", []))
        self.assertEqual(sum(1 for _, _, rules in jobs if not rules), 2)
        self.assertIn(("family__BookI_Prop1__Postulates", "BookI.Prop1", ["Postulate1"]),
                      jobs)
        self.assertIn(("fampair__BookI_Prop1__Metric__Postulates", "BookI.Prop1",
                       ["Postulate1", "Tacit.len_symm"]), jobs)
        for name, _, _ in jobs:
            self.assertIn(name.split("__")[0], screen.KINDS)

    def test_a_missing_rule_about_circles_stops_the_screen(self):
        facts = self.facts({})
        del facts["axiom_modules"]["Tacit.circle_eq"]
        with self.assertRaises(SystemExit):
            screen.attempts(facts)


class Tries(unittest.TestCase):
    REFUSE = {"": {"Postulate1"}, "__forward": {"Postulate1", "Tacit.len_symm"}}

    def test_refused_rules_are_left_out_in_their_way(self):
        jobs = [("bare__X", "X", []),
                ("single__X__Postulate1", "X", ["Postulate1"]),
                ("single__X__Tacit_len_symm", "X", ["Tacit.len_symm"]),
                ("pair__X__Postulate1__Tacit_circle_eq", "X",
                 ["Postulate1", "Tacit.circle_eq"])]
        self.assertEqual(screen.tries(jobs, self.REFUSE), {
            "bare__X": ("X", ""),
            "single__X__Tacit_len_symm": ("X", "Elements.Tacit.len_symm"),
            "pair__X__Postulate1__Tacit_circle_eq": ("X", "Elements.Tacit.circle_eq"),
            "pair__X__Postulate1__Tacit_circle_eq__forward":
                ("X", "→ Elements.Tacit.circle_eq"),
        })

    def test_the_bare_try_gives_grind_only_the_definitions(self):
        bare = screen.theorem("bare__X", "BookI.Prop1", "", 100)
        ruled = screen.theorem("single__X__P", "BookI.Prop1", "Elements.P", 100)
        for text, names in ((bare, unfolded()), (ruled, ["Elements.P"] + unfolded())):
            lines = text.splitlines()
            self.assertEqual(lines[0], "set_option maxHeartbeats 100 in")
            self.assertTrue(lines[1].startswith("theorem "))
            self.assertIn("type_of% @Elements.BookI.Prop1", lines[1])
            [grind] = [line for line in lines if line.startswith("  | grind [")]
            self.assertEqual(given(grind), names)
            self.assertIn("  | sorry", lines)


class Outcomes(unittest.TestCase):
    TRIES = [("bare__A", "BookI.Prop1", ""),
             ("single__A__P", "BookI.Prop1", "Elements.P"),
             ("single__A__Q", "BookI.Prop1", "Elements.Q"),
             ("pair__A__P__Q", "BookI.Prop1", "Elements.P, Elements.Q")]

    def setUp(self):
        self.text = file_of(self.TRIES)
        self.line = {n: line_of(self.text, f"theorem {n} :") for n, _, _ in self.TRIES}

    def read(self, log: str):
        return screen.outcomes(NAME, self.text, log)

    def test_a_clean_log_closes_every_try(self):
        self.assertEqual(self.read(END_LINE), (4, [n for n, _, _ in self.TRIES], [], []))

    def test_sorry_timeout_and_other_errors_are_told_apart(self):
        log = (message(self.line["bare__A"], 8, SORRY)
               + message(self.line["single__A__P"], 0, TIMEOUT)
               + message(self.line["single__A__Q"] + 4, 4,
                         "error: maximum recursion depth has been reached")
               + END_LINE)
        self.assertEqual(self.read(log), (4, ["pair__A__P__Q"], ["single__A__P"],
                                          ["single__A__Q"]))

    def test_an_error_that_names_its_kind_is_still_read(self):
        # Lean 4.35 prints some errors with their kind after the word, as here.
        log = (message(self.line["single__A__P"], 0, "error(lean.unknownConstant): Unknown "
                       "constant `Elements.BookI.Prop1`") + END_LINE)
        _, closed, slow, stopped = self.read(log)
        self.assertEqual((slow, stopped), ([], ["single__A__P"]))
        self.assertNotIn("single__A__P", closed)

    def test_a_grind_failure_without_sorry_still_does_not_close(self):
        log = message(self.line["single__A__Q"] + 4, 4, "error: `grind` failed") + END_LINE
        _, closed, _, stopped = self.read(log)
        self.assertNotIn("single__A__Q", closed)
        self.assertEqual(stopped, ["single__A__Q"])

    def test_an_error_on_the_set_option_line_is_its_own_trys(self):
        log = message(self.line["single__A__Q"] - 1, 0, TIMEOUT) + END_LINE
        _, closed, slow, _ = self.read(log)
        self.assertEqual(slow, ["single__A__Q"])
        self.assertIn("single__A__P", closed)

    def test_the_last_try_runs_to_the_end_of_the_file(self):
        last = len(self.text.splitlines())
        log = message(last, 0, "error: unexpected end of input") + END_LINE
        _, closed, _, stopped = self.read(log)
        self.assertEqual(stopped, ["pair__A__P__Q"])
        self.assertEqual(len(closed), 3)

    def test_another_files_messages_are_not_read(self):
        log = message(self.line["bare__A"], 8, SORRY, name="Screen10.lean") + END_LINE
        self.assertEqual(len(self.read(log)[1]), 4)

    def test_a_log_that_stops_early_stops_the_screen(self):
        with self.assertRaises(SystemExit):
            self.read("")

    def test_an_error_in_the_preamble_stops_the_screen(self):
        control = line_of(self.text, "example :")
        for line in (control, self.line["bare__A"] - 2):
            with self.subTest(line=line), self.assertRaises(SystemExit):
                self.read(message(line, 2, "error: `grind` failed") + END_LINE)


class Refusals(unittest.TestCase):
    def setUp(self):
        self.cases, self.text = screen.refusal_cases(["Tacit.len_symm", "Postulate1"])

    def test_each_case_starts_where_the_reading_says(self):
        lines = self.text.splitlines()
        self.assertEqual(len(self.cases), 2 * len(screen.MODES))
        for k, (mode, ax) in enumerate(self.cases):
            self.assertEqual(lines[3 + 3 * k - 1], "example (h : False) : False := by")
            self.assertEqual(lines[3 + 3 * k], f"  grind [{screen.MODES[mode]}Elements.{ax}]")
        self.assertEqual(lines[-1], f'#print "{screen.END}"')

    def test_a_refusal_is_read_as_its_cases_rule_in_its_way(self):
        where = {case: 3 + 3 * k + 1 for k, case in enumerate(self.cases)}
        log = (message(where[("", "Postulate1")], 2,
                       "error: invalid `grind` parameter, failed to find patterns",
                       name="Refused.lean")
               + message(where[("__forward", "Postulate1")], 2,
                         "error: invalid `grind` forward theorem", name="Refused.lean")
               + message(where[("__forward", "Tacit.len_symm")], 2,
                         "error: failed to find patterns in the hypotheses",
                         name="Refused.lean")
               + END_LINE)
        self.assertEqual(screen.refusals(self.cases, "Refused.lean", log),
                         {"": {"Postulate1"}, "__forward": {"Postulate1", "Tacit.len_symm"}})

    def test_any_other_error_stops_the_screen(self):
        for line, what in ((4, "error: unknown identifier 'Elements.Postulate1'"),
                           (4, "error(lean.unknownIdentifier): Unknown identifier "
                               "`Elements.Postulate1`"),
                           (1, "error: invalid `grind` parameter")):
            with self.subTest(line=line), self.assertRaises(SystemExit):
                screen.refusals(self.cases, "Refused.lean",
                                message(line, 2, what, name="Refused.lean") + END_LINE)

    def test_a_pass_that_stops_early_stops_the_screen(self):
        with self.assertRaises(SystemExit):
            screen.refusals(self.cases, "Refused.lean", "")


class Definitions(unittest.TestCase):
    def log(self, *names: str, unknown: tuple[str, ...] = ()) -> str:
        """A log of the pass, as Lean prints it: one bare line a message."""
        return ("".join(f"screen-def Elements.{n}\n" for n in names)
                + "".join(f"screen-unknown Elements.{n}\n" for n in unknown)
                + END_LINE)

    def test_every_listed_definition_is_accepted(self):
        names = ("Triangle", "Collinear", "circumference", "Magnitude", "Apart.area")
        self.assertEqual(screen.definitions(self.log(*names), True), set(names))

    def test_a_definition_in_no_list_stops_the_screen(self):
        with self.assertRaises(SystemExit) as stop:
            screen.definitions(self.log("Triangle", "NewWord"), True)
        self.assertIn("NewWord", str(stop.exception.code))

    def test_a_failed_empty_or_unknown_pass_stops_the_screen(self):
        for log, ok in ((self.log("Triangle"), False), (self.log(), True),
                        (self.log("Triangle", unknown=("Gone",)), True),
                        ("screen-def Elements.Triangle\n", True)):
            with self.subTest(log=log, ok=ok), self.assertRaises(SystemExit):
                screen.definitions(log, ok)

    def test_the_pass_names_every_root_and_every_listed_word(self):
        facts = {"propositions": [{"name": "BookI.Prop1"}],
                 "axiom_modules": {"Postulate1": "Elements.Foundations.Postulates"}}
        text = screen.reach_file(facts)
        for n in ["BookI.Prop1", "Postulate1"] + screen.DEFS + list(screen.CHOSEN):
            self.assertIn(f"`Elements.{n}", text)
        self.assertTrue(text.endswith(f'#print "{screen.END}"\n'))


class KnownRows(unittest.TestCase):
    RULED = ["single__BookIII_Prop2__Tacit_inside_of_between",
             "single__BookIII_Prop5__Tacit_circle_eq__forward",
             "pair__BookIII_Prop6__Tacit_centre_inside__Tacit_circle_eq"]

    def test_the_known_rows_closed_by_rules(self):
        self.assertEqual(screen.lost(self.RULED), [])

    def test_a_row_closed_only_by_its_bare_try_is_lost(self):
        closed = self.RULED + ["bare__BookIII_Prop2"]
        self.assertEqual(screen.by_rule(closed),
                         ({"BookIII_Prop2"}, {"BookIII_Prop5", "BookIII_Prop6"}))
        self.assertEqual(screen.lost(closed), ["BookIII.Prop2"])

    def test_a_row_not_closed_is_lost(self):
        self.assertEqual(screen.lost(self.RULED[1:]), ["BookIII.Prop2"])

    def test_tries_name_their_statements(self):
        facts = {"propositions": [{"name": "BookI.Prop40.general", "ref": "I.40 general"},
                                  {"name": "BookIII.Prop2", "ref": "III.2"}]}
        self.assertEqual(screen.statements(facts, ["bare__BookI_Prop40_general",
                                                   self.RULED[0]]),
                         ["I.40 general", "III.2"])


class Lists(unittest.TestCase):
    def test_the_lists_are_apart_and_without_repeats(self):
        lists = [screen.DEFS, list(screen.CHOSEN), screen.CARRIERS]
        everything = [n for names in lists for n in names]
        self.assertEqual(len(everything), len(set(everything)))

    def test_every_file_proves_the_controls_and_unfolds_every_listed_word(self):
        blocks = [block.splitlines() for block in screen.HEAD.split("\n\n")
                  if block.startswith("example : ")]
        goals = [lines[0].removeprefix("example : ").removesuffix(" := by")
                 for lines in blocks]
        self.assertEqual(goals, screen.CONTROLS)
        for lines in blocks:
            [grind] = [line for line in lines if line.lstrip().startswith("grind [")]
            self.assertEqual(set(given(grind)), set(unfolded()))


if __name__ == "__main__":
    unittest.main(verbosity=2)
