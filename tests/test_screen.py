#!/usr/bin/env python3
"""The cases of Audit/screen.py, the overlap screen: which tries it makes, and how it reads
what Lean says of them.

    python3 -I tests/test_screen.py        # about a second; no Lean, no network

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
* The record of a run (--write) and its check (--check-current), with a stand-in for git:
  each part of what decides the result is named when it changes (a statement added or
  restated, a rule, a word, a file of the library or the toolchain, the screen's code, on
  its docstring's last line too, or another module beside it), and nothing else is (the
  docstring, what the screen does not read); a record that is missing, does not read, is
  a symbolic link, disagrees with itself, or is of a run on inputs other than a commit's
  is refused; no record is written of such a run, through a symbolic link, or of inputs
  or a commit that moved while it ran; and the real inputs compute, which takes most of
  the time.
* Before any Lean: --check-current takes no OUTDIR and no --write; a stale build, --write
  on inputs that are not a commit's, or a move to another commit or other inputs after the
  build checks as current, stops a run. Before a successful --write, an unchanged build is
  checked again; a build left stale during the main or retry pass stops the run and leaves
  the existing record in place.

Nothing runs these in CI yet: whoever changes the screen runs this file. Python 3.11 or
later; standard library.
"""

from __future__ import annotations

import contextlib
import io
import itertools
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "Audit"))
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


COMMIT = "a" * 40


def git_at(commit: str | None = COMMIT, status: str | None = ""):
    """The screen's git, as a checkout at `commit` whose inputs show `status`."""
    def git(*args: str, root: Path = REPO) -> str | None:
        return {"rev-parse": commit, "status": status}.get(args[0])
    return mock.patch.object(screen, "git", git)


class Record(unittest.TestCase):
    """A run's record names what it read; --check-current names each part that changed. Each
    case builds a small copy of the inputs, records it as a run would, at a commit given by
    a stand-in for git, changes one thing, and reads what --check-current says."""

    def setUp(self):
        self.tmp = self.enterContext(tempfile.TemporaryDirectory())
        self.root = Path(self.tmp)
        self.facts = {"propositions": [
            {"name": "BookI.Prop1", "ref": "I.1", "kind": "proposition", "statement": "P1",
             "own_axioms": ["Postulate1"]},
            {"name": "BookI.Prop2", "ref": "I.2", "kind": "proposition", "statement": "P2"}],
            "axiom_modules": {"Postulate1": "Elements.Foundations.Postulates"},
            "axiom_types": {"Postulate1": "T1"},
            "vocabulary": {"Triangle": "def : X := Y"}}
        self.write("facts.json", json.dumps(self.facts))
        self.write("Elements.lean", "import Elements.Foundations.Words\n")
        self.write("Elements/Foundations/Words.lean", "def x := 1\n")
        self.write("Elements/Figure/Areas.lean", "instance : Foo := bar\n")
        self.write("lean-toolchain", "leanprover/lean4:v4.35.0\n")
        self.write("lakefile.toml", 'name = "stoicheia"\n')
        self.write("lake-manifest.json", "{}\n")
        (self.root / "Audit").mkdir()
        shutil.copyfile(REPO / screen.SCREEN, self.root / screen.SCREEN)
        self.path = self.root / "Audit" / "screen-run.toml"
        self.enterContext(git_at())
        self.assertEqual(self.record(),
                         f"recorded what this run read in Audit/screen-run.toml: commit "
                         f"{COMMIT[:12]} ({screen.COMMITTED}), 2 statements\n")

    def write(self, rel: str, text: str) -> None:
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")

    def record(self) -> str:
        """Record the inputs as a run would; what it prints."""
        facts = json.loads((self.root / "facts.json").read_text(encoding="utf-8"))
        read = screen.inputs(self.root, facts)
        with contextlib.redirect_stdout(io.StringIO()) as out:
            screen.write_record(self.root, read, len(facts["propositions"]), self.path,
                                at=screen.revision(self.root))
        return out.getvalue()

    def check(self) -> tuple[list[str], list[str]]:
        problems, _, changed = screen.check_current(self.root, self.path)
        return problems, changed

    def changed(self, rel: str, edit) -> list[str]:
        p = self.root / rel
        p.write_text(edit(p.read_text(encoding="utf-8")), encoding="utf-8")
        problems, changed = self.check()
        self.assertEqual(len(problems), len(changed))
        return changed

    def facts_changed(self, edit) -> list[str]:
        facts = json.loads((self.root / "facts.json").read_text(encoding="utf-8"))
        edit(facts)
        (self.root / "facts.json").write_text(json.dumps(facts), encoding="utf-8")
        return self.check()[1]

    def refused(self) -> str:
        """The one problem --check-current finds, with no part named as changed."""
        problems, changed = self.check()
        self.assertEqual((len(problems), changed), (1, []), problems)
        return problems[0]

    def test_a_fresh_record_is_current(self):
        self.assertEqual(self.check(), ([], []))
        text = self.path.read_text(encoding="utf-8")
        self.assertIn(f'commit = "{COMMIT}"\n', text)
        self.assertIn(f'state = "{screen.COMMITTED}"\n', text)
        self.assertIn("statements = 2\n", text)
        self.assertIn("[parts]\n", text)
        self.assertEqual(sorted(p.name for p in (self.root / "Audit").iterdir()),
                         ["screen-run.toml", "screen.py"])

    def test_a_missing_record_is_not_current(self):
        self.path.unlink()
        self.assertIn("no record of a run", self.refused())

    def test_an_unreadable_record_is_refused(self):
        self.path.write_text('commit = "\n[parts\n', encoding="utf-8")
        self.assertIn("does not read", self.refused())

    def test_a_record_that_raises_permission_error_is_refused(self):
        with mock.patch.object(Path, "read_text", side_effect=PermissionError("denied")):
            self.assertIn("does not read", self.refused())

    def test_a_record_whose_parts_and_total_disagree_is_refused(self):
        self.path.write_text(self.path.read_text(encoding="utf-8").replace(
            "statements = 2", "statements = 3"), encoding="utf-8")
        self.assertIn("not as a run writes it", self.refused())
        self.record()
        text = self.path.read_text(encoding="utf-8")
        self.path.write_text(text.replace('screen = "', 'screen = "0', 1), encoding="utf-8")
        self.assertIn("not as a run writes it", self.refused())

    def test_a_record_of_a_run_on_other_inputs_is_refused(self):
        text = self.path.read_text(encoding="utf-8")
        for old, new in ((screen.COMMITTED, "inputs differ from this commit"),
                         (screen.COMMITTED, "unknown"),
                         (COMMIT, "unknown"), (COMMIT, "0" * 39), (COMMIT, COMMIT.upper())):
            with self.subTest(new=new):
                self.path.write_text(text.replace(f'"{old}"', f'"{new}"', 1), encoding="utf-8")
                self.assertIn("records a run on inputs other than a commit's", self.refused())

    def test_no_record_is_written_of_a_run_on_other_inputs(self):
        for commit, status in ((COMMIT, " M facts.json"), (COMMIT, None), (None, None),
                               ("unknown", "")):
            with self.subTest(commit=commit, status=status):
                self.path.unlink()
                with git_at(commit, status), self.assertRaisesRegex(SystemExit, "not a commit's"):
                    self.record()
                self.assertFalse(self.path.exists())
                self.record()

    def test_a_record_that_is_a_symbolic_link_is_refused_and_not_written_through(self):
        elsewhere = self.root / "elsewhere.toml"
        self.path.rename(elsewhere)
        self.path.symlink_to(elsewhere)
        self.assertIn("is a symbolic link", self.refused())
        before = elsewhere.read_text(encoding="utf-8")
        self.write("Elements/Foundations/Words.lean", "def x := 2\n")
        with self.assertRaisesRegex(SystemExit, "is a symbolic link"):
            self.record()
        self.assertTrue(self.path.is_symlink())
        self.assertEqual(elsewhere.read_text(encoding="utf-8"), before)

    def test_a_statement_added_or_restated_is_named(self):
        changed = self.facts_changed(lambda f: f["propositions"].append(
            {"name": "BookI.Prop3", "ref": "I.3", "kind": "proposition", "statement": "P3"}))
        self.assertEqual(changed, ["statements"])
        self.assertIn("2 at the run, 3 now", self.check()[0][0])
        self.facts_changed(lambda f: f["propositions"].pop())
        self.assertEqual(self.check(), ([], []))
        self.assertEqual(self.facts_changed(
            lambda f: f["propositions"][0].update(statement="P1'")), ["statements"])

    def test_what_the_screen_does_not_read_is_not_an_input(self):
        """A proof's axioms, or the order of the entries, decide nothing the screen does."""
        self.assertEqual(self.facts_changed(
            lambda f: f["propositions"][0].update(own_axioms=["Postulate2"])), [])
        self.assertEqual(self.facts_changed(lambda f: f["propositions"].reverse()), [])

    def test_a_rule_or_a_word_changed_is_named(self):
        self.assertEqual(self.facts_changed(
            lambda f: f["axiom_types"].update(Postulate1="T1'")), ["rules"])
        self.record()
        self.assertEqual(self.facts_changed(
            lambda f: f["axiom_modules"].update(Postulate1="Elements.Foundations.Other")),
            ["rules"])
        self.record()
        self.assertEqual(self.facts_changed(
            lambda f: f["vocabulary"].update(Triangle="def : X := Z")), ["words"])

    def test_a_library_file_changed_added_or_removed_is_named(self):
        self.assertEqual(self.changed("Elements/Figure/Areas.lean", lambda t: t + "-- c\n"),
                         ["library"])
        self.record()
        self.write("Elements/Figure/New.lean", "def y := 2\n")
        self.assertEqual(self.check()[1], ["library"])
        self.record()
        (self.root / "Elements/Figure/New.lean").unlink()
        self.assertEqual(self.check()[1], ["library"])
        self.record()
        self.assertEqual(self.changed("Elements.lean", lambda t: t + "import X\n"),
                         ["library"])

    def test_the_toolchain_is_named_and_a_lakefile_lean_counts(self):
        self.assertEqual(self.changed("lean-toolchain",
                                      lambda t: t.replace("4.35.0", "4.36.0")), ["toolchain"])
        self.record()
        self.write("lakefile.lean", "import Lake\n")
        self.assertEqual(self.check()[1], ["toolchain"])

    def test_the_screen_counts_but_its_docstring_does_not(self):
        self.assertEqual(self.changed(screen.SCREEN, lambda t: t.replace(
            '"""A mechanical screen', '"""A mechanical screen, run again', 1)), [])
        self.assertEqual(self.changed(screen.SCREEN,
                                      lambda t: t.replace("BEATS = 30000", "BEATS = 30001")),
                         ["screen"])

    def test_code_on_the_docstrings_last_line_counts(self):
        self.assertEqual(self.changed(screen.SCREEN, lambda t: t.replace(
            '\n"""\n', '\n"""; KNOWN_EXTRA = 1\n', 1)), ["screen"])
        for text, kept in (('"""Doc."""; x = 1\ny = 2\n', '"""Doc."""; x = 1\ny = 2\n'),
                           ('"""Doc,\nlonger."""\nx = 1\n', "x = 1\n"),
                           ("x = 1\n", "x = 1\n")):
            self.assertEqual(screen.without_docstring(text), kept)

    def test_a_module_beside_the_screen_counts(self):
        """Run without -I, a module beside the screen can stand in for a standard one."""
        self.write("Audit/datetime.py", "print('planted')\n")
        self.assertEqual(self.check()[1], ["screen"])
        self.assertEqual(screen.screen_files(self.root), [screen.SCREEN, "Audit/datetime.py"])
        self.record()
        self.write("Audit/__pycache__/screen.cpython-311.pyc", "cache")
        self.write("Audit/Overlaps.lean", "-- the audit lemmas\n")
        self.assertEqual(self.check(), ([], []))
        self.write("Audit/helpers/__init__.py", "")
        self.assertEqual(self.check()[1], ["screen"])

    def test_inputs_moved_during_a_run_are_not_recorded(self):
        read = screen.inputs(self.root, self.facts)
        self.write("Elements/Foundations/Words.lean", "def x := 2\n")
        with self.assertRaisesRegex(SystemExit, "changed while it ran"):
            screen.write_record(self.root, read, 2, self.path, at=screen.revision(self.root))

    def test_a_commit_moved_during_a_run_is_not_recorded(self):
        """The inputs as they were, but another commit checked out: the record names the
        commit the run read its inputs at, or nothing."""
        before = self.path.read_text(encoding="utf-8")
        read = screen.inputs(self.root, self.facts)
        with git_at("b" * 40), self.assertRaisesRegex(SystemExit, "changed while it ran"):
            screen.write_record(self.root, read, 2, self.path, at=(COMMIT, screen.COMMITTED))
        self.assertEqual(self.path.read_text(encoding="utf-8"), before)

    def test_a_move_to_clean_b_after_as_build_checks_stops_the_run(self):
        """A's build checks as current, and then the checkout moves, clean, to commit B,
        with another library file or none: no Lean runs, and B is not recorded against A's
        build."""
        before = self.path.read_text(encoding="utf-8")
        for library in ("def x := 2\n", None):
            with self.subTest(library=library):
                head = {"commit": COMMIT}
                launched = []

                def git(*args: str, root: Path = REPO) -> str | None:
                    return {"rev-parse": head["commit"], "status": ""}.get(args[0])

                def lake(argv, **kw):
                    launched.append(argv)
                    if library:
                        self.write("Elements/Foundations/Words.lean", library)
                    head["commit"] = "b" * 40
                    return subprocess.CompletedProcess(argv, 0)
                with tempfile.TemporaryDirectory() as out, \
                        mock.patch.object(screen, "git", git), \
                        mock.patch.object(screen, "ROOT", self.root), \
                        mock.patch.object(screen, "RECORD", self.path), \
                        mock.patch.object(screen.subprocess, "run", lake), \
                        mock.patch.object(screen.subprocess, "Popen") as lean, \
                        mock.patch.object(sys, "argv", ["screen.py", out, "--write"]), \
                        contextlib.redirect_stdout(io.StringIO()), \
                        self.assertRaises(SystemExit) as stop:
                    screen.main()
                self.assertIn("changed while the build was checked", str(stop.exception.code))
                self.assertEqual(launched, [["lake", "build", "--no-build", "Elements"]])
                lean.assert_not_called()
                self.assertEqual(self.path.read_text(encoding="utf-8"), before)

    def run_with_build_change(self, during_retry: bool) -> tuple[list[list[str]], str]:
        self.path.write_text("existing record\n", encoding="utf-8")
        before = self.path.read_text(encoding="utf-8")
        stale = {"build": False}
        launched = []

        def lake(argv, **kw):
            launched.append(argv)
            return subprocess.CompletedProcess(argv, 3 if stale["build"] else 0)

        def lean(todo, beats, out, prefix, jobs):
            if during_retry and prefix == "Screen":
                return 1, [], list(todo), []
            stale["build"] = True
            return len(todo), list(todo), [], []

        jobs = [("bare__BookI_Prop1", "BookI.Prop1", [])]
        with tempfile.TemporaryDirectory() as out, \
                mock.patch.object(screen, "ROOT", self.root), \
                mock.patch.object(screen, "RECORD", self.path), \
                mock.patch.object(screen, "reached"), \
                mock.patch.object(screen, "attempts", return_value=jobs), \
                mock.patch.object(screen, "refused", return_value={}), \
                mock.patch.object(screen, "tries", return_value={
                    "bare__BookI_Prop1": ("BookI.Prop1", "")}), \
                mock.patch.object(screen, "run", side_effect=lean), \
                mock.patch.object(screen, "lost", return_value=[]), \
                mock.patch.object(screen.subprocess, "run", side_effect=lake), \
                mock.patch.object(sys, "argv", ["screen.py", out, "--write"]), \
                contextlib.redirect_stdout(io.StringIO()), \
                self.assertRaises(SystemExit) as stop:
            screen.main()
        self.assertEqual(self.path.read_text(encoding="utf-8"), before)
        return launched, str(stop.exception.code)

    def test_a_build_left_stale_during_the_main_pass_is_not_recorded(self):
        launched, stopped = self.run_with_build_change(False)
        self.assertEqual(launched, 2 * [["lake", "build", "--no-build", "Elements"]])
        self.assertIn("build of Elements changed while the screen ran", stopped)

    def test_a_build_left_stale_during_the_retry_pass_is_not_recorded(self):
        launched, stopped = self.run_with_build_change(True)
        self.assertEqual(launched, 2 * [["lake", "build", "--no-build", "Elements"]])
        self.assertIn("build of Elements changed while the screen ran", stopped)

    def test_an_unchanged_build_is_checked_again_and_recorded(self):
        self.path.write_text("existing record\n", encoding="utf-8")
        launched = []

        def lake(argv, **kw):
            launched.append(argv)
            return subprocess.CompletedProcess(argv, 0)

        jobs = [("bare__BookI_Prop1", "BookI.Prop1", [])]
        with tempfile.TemporaryDirectory() as out, \
                mock.patch.object(screen, "ROOT", self.root), \
                mock.patch.object(screen, "RECORD", self.path), \
                mock.patch.object(screen, "reached"), \
                mock.patch.object(screen, "attempts", return_value=jobs), \
                mock.patch.object(screen, "refused", return_value={}), \
                mock.patch.object(screen, "tries", return_value={
                    "bare__BookI_Prop1": ("BookI.Prop1", "")}), \
                mock.patch.object(screen, "run", return_value=(1, [jobs[0][0]], [], [])), \
                mock.patch.object(screen, "lost", return_value=[]), \
                mock.patch.object(screen.subprocess, "run", side_effect=lake), \
                mock.patch.object(sys, "argv", ["screen.py", out, "--write"]), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(screen.main(), 0)
        self.assertEqual(launched, 2 * [["lake", "build", "--no-build", "Elements"]])
        self.assertEqual(screen.check_current(self.root, self.path)[0], [])

    def test_the_repository_inputs_read(self):
        """The real inputs compute, and every part is present."""
        facts = json.loads((REPO / "facts.json").read_text(encoding="utf-8"))
        parts = screen.inputs(REPO, facts)
        self.assertEqual(set(parts), set(screen.PARTS))
        self.assertIn("Elements/Figure/Areas.lean", screen.library_files(REPO))
        self.assertEqual(screen.library_files(REPO)[0], "Elements.lean")
        self.assertEqual(screen.screen_files(REPO)[0], screen.SCREEN)


class Main(unittest.TestCase):
    """What the screen refuses before it runs any Lean."""

    def main(self, *args: str) -> tuple[int | str | None, str]:
        """The screen's exit and what it wrote to stderr, given these arguments."""
        err = io.StringIO()
        with mock.patch.object(sys, "argv", ["screen.py", *args]), \
                contextlib.redirect_stderr(err), self.assertRaises(SystemExit) as stop:
            screen.main()
        return stop.exception.code, err.getvalue()

    def test_check_current_takes_no_outdir_and_no_write(self):
        with tempfile.TemporaryDirectory() as out:
            for args in ((out, "--check-current"), ("--check-current", "--write")):
                code, err = self.main(*args)
                self.assertEqual(code, 2)
                self.assertIn("--check-current takes no OUTDIR and no --write", err)

    def test_a_stale_build_stops_the_run(self):
        built = []

        def lake(argv, **kw):
            built.append(argv)
            return subprocess.CompletedProcess(argv, 3)
        with tempfile.TemporaryDirectory() as out, git_at(), \
                mock.patch.object(screen.subprocess, "run", lake):
            code, _ = self.main(out)
        self.assertEqual(built, [["lake", "build", "--no-build", "Elements"]])
        self.assertIn("run `lake build` first", code)

    def test_write_on_inputs_that_are_not_a_commits_stops_the_run(self):
        with tempfile.TemporaryDirectory() as out, git_at(status=" M facts.json"), \
                mock.patch.object(screen.subprocess, "run") as lake:
            code, _ = self.main(out, "--write")
        lake.assert_not_called()
        self.assertIn("records only a run on a commit's inputs", code)


if __name__ == "__main__":
    unittest.main(verbosity=2)
