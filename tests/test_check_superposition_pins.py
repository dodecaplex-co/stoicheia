#!/usr/bin/env python3
"""The cases of scripts/check_superposition_pins.py, without Lean.

    python3 -I tests/test_check_superposition_pins.py

The real brief, audit file and Audit.lean must pass. In copies, an invented theorem name in
the restriction section must fail with its line and name, and so must a name pinned only by
its axioms, by a `#check` with no `#guard_msgs`, by a `#guard_msgs` with any option
(`substring := true` among them), or by a pin in a comment. A name is pinned only under its
full name, so a pin of `Rule.Figure.restrict` does not pin a bare `restrict`. The
exceptions (`Rule.infer`, `Metric`, `cite`, file names, Lean's axioms, single letters and
spans that are not one identifier) pass with no pin, a name outside the section is not
read, and a brief without the section, or whose section names no theorem, cannot be read.

The audit file holds only its leading imports, one module each, comments and pins. In
copies of the real file, `set_option pp.deepTerms false` with `pp.deepTerms.threshold 0`
and a docstring cut down to match, which Lean accepts, `pp.oneline`, `pp.maxSteps`, an
option for one pin, and a namespace whose theorem takes a pinned name are each refused
with their lines; the reader alone would have counted the pin under the namespace, and
refuses the cut-down docstring itself. So are any declaration or other command after a
pin, `#eval` and `#exit` among them, a guard with options even beside a bare one, a pin
with no docstring, and an import after a pin or between a pin's docstring and its guard.
Audit.lean must import the audit file in its leading imports, not in a comment and not
after a command. The reader of pins is tested on its own for pins Lean never runs (in a
comment, a doc comment opened by `/--/`, a string or after `#exit`) and for quotes that
hide nothing, since the file may no longer hold the `#eval`s that carry those cases.

A definition is pinned by `#print`. In copies of the real file, a `#check` pin of
`Interpretation.Embedding` or of `Rule.Figure`, the two the section names, is refused by
name with its line and does not count: with the docstring Lean prints for it, and, for
`Embedding` declared `: id Type`, with one that shows neither sign. `Embedding` must keep
its `#print` pin even with the section no longer naming it. A `#check` pin of a definition
the section might name later is refused by the signs. `Placed`, `Val.place` and
`Metric.names` must each have a `#print` pin: removed, or turned into a `#check`, each
fails, and each is read by a theorem the section names, as the script says. A statement
pin whose docstring holds `⋯` or `[...]`, as Lean prints a statement cut short, is
refused with no option in the file, as if set outside it, and so is a proof printed as
`⋯`. What shows a definition in Lean's print of a type is tested on the five
definitions' prints, on propositions that only look like definitions' types, and on types
that show neither sign, definitions' among them; every `#check` pin in the real file
shows nothing. Every docstring below said to be what Lean prints was printed by Lean 4.35.
"""

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))
import check_superposition_pins as pins  # noqa: E402

PIN = """/--
info: @Elements.Superposition.{name} : True
-/
#guard_msgs in
#check @Elements.Superposition.{name}
"""
AXIOMS = """/--
info: 'Elements.Superposition.{name}' does not depend on any axioms
-/
#guard_msgs in
#print axioms Elements.Superposition.{name}
"""
SOUND = "Elements.Superposition.Derives.sound"
RESTRICT = "Elements.Superposition.Rule.Figure.restrict"
RESTRICT_GUARD = f"#guard_msgs in\n#check @{RESTRICT}\n"
S = "Elements.Superposition"
# What Lean prints for `#check @name` of each definition pinned by `#print`.
CHECKED = {
    f"{S}.Rule.Figure":
        f"{S}.Rule.Figure : {S}.Interpretation → List {S}.Cited → Prop",
    f"{S}.Interpretation.Embedding":
        f"{S}.Interpretation.Embedding : {S}.Interpretation →\n  {S}.Interpretation → Type",
    f"{S}.Placed":
        f"{S}.Placed : (I : {S}.Interpretation) →\n  I.Point → I.Point → I.Point → I.Point → "
        "I.Point → I.Point → I.Line → I.Point → I.Point → Prop",
    f"{S}.Val.place":
        f"@{S}.Val.place : {{I : {S}.Interpretation}} →\n  {{P L : Type}} →\n    "
        f"{S}.Val I P L →\n      I.Point →\n        I.Point →\n          "
        f"I.Line → {S}.Val I ({S}.Name P) ({S}.LineName L)",
    f"{S}.Metric.names":
        f"@{S}.Metric.names : {{P : Type}} → {S}.Metric P → List P",
}
# What Lean prints for `#check @name` of `Interpretation.Embedding` declared `: id Type`,
# a sort spelt through a name: its print shows neither sign.
ID_EMBEDDING = (f"{S}.Interpretation.Embedding : {S}.Interpretation →\n  "
                f"{S}.Interpretation → id Type")
# What Lean prints for `Rule.Figure.restrict` and `Metric.names` cut short: under
# `pp.deepTerms false` with threshold 0, under `pp.oneline`, and under `pp.maxSteps 1`.
DEEP_RESTRICT = f"@{RESTRICT} : ∀ {{I J : {S}.Interpretation}}, ⋯"
ONELINE_RESTRICT = (f"@{RESTRICT} : ∀ {{I J : {S}.Interpretation}} (e : J.Embedding I) "
                    f"{{cites : List {S}.Cited}}, [...]")
STEPS_NAMES = f"def {S}.Metric.names : {{P : ⋯}} → ⋯ :=\nfun {{P}} x => ⋯"


def prints(names) -> str:
    """A `#print` pin of each of `names`, each printed as if it were `True`."""
    return "".join(f"\n/--\ninfo: def {name} : Prop :=\nTrue\n-/\n#guard_msgs in\n#print {name}\n"
                   for name in names)


# The five definitions the script requires `#print` pins of, for the cases that do not copy
# the real file.
HELD = (*pins.DEFINITIONS, *pins.PRINTED)
PRINTS = prints(HELD)


def check_pin(name: str, printed: str | None = None) -> str:
    """A `#check` pin of `name`, with what Lean prints for it, or with `printed`."""
    return f"/--\ninfo: {printed or CHECKED[name]}\n-/\n#guard_msgs in\n#check @{name}\n"


def pin_span(audit: str, command: str) -> tuple[int, int]:
    """Where the pin whose command is `command` starts, at its docstring, and ends, after
    the command's line, in `audit`."""
    tail = f"#guard_msgs in\n{command}\n"
    assert audit.count(tail) == 1, command
    end = audit.index(tail) + len(tail)
    return audit.rindex("/--\n", 0, end), end


def numbered(text: str, snippet: str) -> list[tuple[int, str]]:
    """The lines of `snippet`, found once in `text`, that hold something, with their
    numbers in `text`."""
    assert text.count(snippet) == 1, snippet
    first = text[:text.index(snippet)].count("\n") + 1
    return [(first + k, line.strip()) for k, line in enumerate(snippet.split("\n"))
            if line.strip()]


class PinTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory()))

    def run_check(self, brief: str, audit: str, library: str | None = None,
                  printed: bool = True) -> tuple[int, str]:
        """The script's exit code and output. When `printed`, the definitions in
        `pins.PRINTED` are printed at the end of the audit file, so that a case about
        something else does not fail for their lack; a copy of the real file prints them
        already, and passes False."""
        (self.root / "brief.md").write_text(brief)
        (self.root / "Audit.lean").write_text(audit + (PRINTS if printed else ""))
        argv = ["--brief", str(self.root / "brief.md"), "--audit", str(self.root / "Audit.lean")]
        if library is not None:
            (self.root / "Library.lean").write_text(library)
            argv += ["--library", str(self.root / "Library.lean")]
        out = io.StringIO()
        with redirect_stdout(out), redirect_stderr(out):
            code = pins.main(argv)
        return code, out.getvalue()

    def brief(self, body: str, after: str = "") -> str:
        return ("# Brief\n\n## Before\n\n`Before.only` is not read.\n\n"
                f"{pins.HEADING}\n\n{body}\n\n### A subsection, still read\n\n"
                f"## After\n\n{after}\n")

    def real_pin(self) -> tuple[str, int, int]:
        """The real audit file, and where `Rule.Figure.restrict`'s statement pin starts and
        ends in it."""
        audit = (REPO / pins.AUDIT).read_text()
        start = audit.index(f"/--\ninfo: @{RESTRICT} :")
        return audit, start, audit.index(RESTRICT_GUARD) + len(RESTRICT_GUARD)

    def assert_refused(self, out: str, refused: list[tuple[int, str]],
                       others: tuple[tuple[int, str, str], ...] = ()):
        """`refused` are the lines refused as neither an import, a comment nor a pin;
        `others`, the lines of pins refused, each with its text and the start of why."""
        for number, line in refused:
            self.assertIn(f"Audit.lean:{number}: `{pins.shorten(line)}` is not a leading "
                          "import, a comment or a pin", out)
        for number, line, why in others:
            self.assertIn(f"Audit.lean:{number}: `{pins.shorten(line)}` {why}", out)
        self.assertIn(f"✗ {len(refused) + len(others)} refused", out)

    def brief_line(self, name: str) -> int:
        """The line of the real brief's section where `name` is first named."""
        found = pins.names(pins.section((REPO / pins.BRIEF).read_text()))
        return next(number for number, span in found if span == name)

    def test_the_real_brief_passes(self):
        out = io.StringIO()
        with redirect_stdout(out), redirect_stderr(out):
            code = pins.main([])
        self.assertEqual(code, 0, out.getvalue())
        self.assertIn("has a statement pin", out.getvalue())
        self.assertEqual(pins.strays((REPO / pins.AUDIT).read_text()), [])
        self.assertEqual(pins.MODULE, "Audit.Superposition")
        self.assertIn(pins.MODULE, pins.imports((REPO / pins.LIBRARY).read_text()))

    def test_an_invented_name_in_the_real_brief_fails(self):
        text = (REPO / pins.BRIEF).read_text()
        heading = text.index(pins.HEADING)
        planted = text.index("\n\n", heading) + 2
        text = (text[:planted] + "A planted claim: `Derives.invented_theorem` proves it.\n\n"
                + text[planted:])
        line = text[:text.index("Derives.invented_theorem")].count("\n") + 1
        code, out = self.run_check(text, (REPO / pins.AUDIT).read_text(), printed=False)
        self.assertEqual(code, 1, out)
        self.assertIn(f"brief.md:{line}: `Derives.invented_theorem` has no statement pin", out)
        self.assertIn("✗ 1 of", out)

    def test_a_pinned_name_passes(self):
        code, out = self.run_check(self.brief("Part 1: `Derives.map` and `exportable_iff`."),
                                   PIN.format(name="Derives.map")
                                   + PIN.format(name="exportable_iff"))
        self.assertEqual(code, 0, out)

    def test_a_print_pin_counts_for_a_definition(self):
        audit = ("/--\ninfo: def Elements.Superposition.Rule.Figure : Prop :=\nTrue\n-/\n"
                 "#guard_msgs in\n#print Elements.Superposition.Rule.Figure\n")
        others = prints(name for name in HELD if name != f"{S}.Rule.Figure")
        code, out = self.run_check(self.brief("`Rule.Figure` is a definition."),
                                   audit + others, printed=False)
        self.assertEqual(code, 0, out)

    def test_an_axiom_pin_is_not_a_statement_pin(self):
        code, out = self.run_check(self.brief("`Derives.sound` holds."),
                                   AXIOMS.format(name="Derives.sound"))
        self.assertEqual(code, 1, out)
        self.assertIn("`Derives.sound` has no statement pin", out)

    def test_a_check_without_guard_msgs_is_not_a_pin(self):
        code, out = self.run_check(self.brief("`Derives.sound` holds."), f"#check @{SOUND}\n")
        self.assertEqual(code, 1, out)
        self.assertIn("`Derives.sound` has no statement pin", out)
        self.assert_refused(out, [(1, f"#check @{SOUND}")])

    def test_a_pin_of_another_name_does_not_count(self):
        audit = PIN.format(name="Derives.map").replace(
            "info: @Elements.Superposition.Derives.map", "info: @Elements.Superposition.Other")
        code, out = self.run_check(self.brief("`Derives.map` holds."), audit)
        self.assertEqual(code, 1, out)

    def test_the_exceptions_need_no_pin(self):
        body = ("`Rule.infer`, `Metric`, `cite`, [`Restriction.lean`](x), "
                "`Certificate/axioms.lock`, `scripts/check_superposition_pins.py`, `propext`, "
                "`Quot.sound`, `Classical.choice`, `Rule I`, `I`, `∀ c ∈ cites, c.Holds I`; "
                "and one theorem, `Derives.map`.")
        code, out = self.run_check(self.brief(body), PIN.format(name="Derives.map"))
        self.assertEqual(code, 0, out)
        self.assertIn("1 in all", out)

    def test_a_section_that_names_no_theorem_cannot_be_read(self):
        code, out = self.run_check(self.brief("Only `Rule.infer`, `Metric` and `cite`."), "")
        self.assertEqual(code, 2, out)
        self.assertIn("names no theorem", out)

    def test_names_outside_the_section_and_in_fences_are_not_read(self):
        body = "```lean\n`Fenced.name`\n```\nOnly `Derives.map`."
        code, out = self.run_check(self.brief(body, after="`After.name` here."),
                                   PIN.format(name="Derives.map"))
        self.assertEqual(code, 0, out)
        self.assertIn("1 in all", out)

    def test_a_bare_suffix_is_not_pinned_by_a_longer_name(self):
        code, out = self.run_check(self.brief("`restrict` holds."),
                                   PIN.format(name="Rule.Figure.restrict"))
        self.assertEqual(code, 1, out)
        self.assertIn("`restrict` has no statement pin", out)
        self.assertIn("#check @Elements.Superposition.restrict", out)

    def test_a_pin_under_another_namespace_does_not_count(self):
        audit = PIN.format(name="Derives.map").replace("Elements.Superposition.",
                                                       "Other.Superposition.")
        code, out = self.run_check(self.brief("`Derives.map` holds."), audit)
        self.assertEqual(code, 1, out)

    def test_a_guard_with_options_is_not_a_statement_pin(self):
        for options in ("(substring := true)", "(drop info)", "(whitespace := lax)",
                        "(info, drop all)", "(ordering := sorted)",
                        "(substring := true) (drop warning)"):
            with self.subTest(options):
                guard = f"#guard_msgs {options} in\n#check @{SOUND}\n"
                audit = "-- the pin\n\n" + PIN.format(name="Derives.sound").replace(
                    "#guard_msgs in\n", f"#guard_msgs {options} in\n")
                code, out = self.run_check(self.brief("`Derives.sound` holds."), audit)
                self.assertEqual(code, 1, out)
                self.assertIn("`Derives.sound` has no statement pin", out)
                self.assertIn(f"Audit.lean:6 is under `#guard_msgs {options} in`", out)
                self.assertIn("only a bare `#guard_msgs in` pins a statement", out)
                self.assert_refused(out, numbered(audit, guard))

    def test_a_weak_pin_is_refused_even_beside_a_bare_one(self):
        bare = PIN.format(name="Derives.sound")
        weak = bare.replace("#guard_msgs in", "#guard_msgs (substring := true) in")
        audit = weak + "\n" + bare
        # The reader counts the bare pin; the weak one is refused all the same.
        self.assertEqual(pins.statement_pins(audit), ({SOUND}, {}))
        code, out = self.run_check(self.brief("`Derives.sound` holds."), audit)
        self.assertEqual(code, 1, out)
        self.assertNotIn("has no statement pin", out)
        self.assert_refused(out, [(4, "#guard_msgs (substring := true) in"),
                                  (5, f"#check @{SOUND}")])

    def test_options_that_shorten_what_lean_prints_are_refused(self):
        audit, start, end = self.real_pin()
        # Under the first two options Lean prints `restrict`'s statement as its binders and
        # `⋯`; with the docstring cut down to match, `lake build Audit` passes.
        deep = "set_option pp.deepTerms false\nset_option pp.deepTerms.threshold 0\n\n"
        shortened = (f"/--\ninfo: @{RESTRICT} : ∀ {{I J : Elements.Superposition.Interpretation}}"
                     ", ⋯\n-/\n" + RESTRICT_GUARD)
        back = "\nset_option pp.deepTerms true\n"
        oneline, steps = "set_option pp.oneline true\n\n", "set_option pp.maxSteps 1\n\n"
        one_pin = f"#guard_msgs in\nset_option pp.maxSteps 1 in\n#check @{RESTRICT}\n"
        # (the copy, the snippets planted in it, whether the reader alone counts the pin,
        # and the pins refused besides); the reader refuses the cut-down docstring itself.
        cut = audit[:start] + deep + shortened + back + audit[end:]
        mark = numbered(cut, shortened)[1]
        cases = {
            "pp.deepTerms, threshold 0":
                (cut, (deep, back), False, ((*mark, "holds `⋯`, where Lean cut its print "
                                                    f"short, so the pin of `{RESTRICT}`"),)),
            "pp.oneline": (audit[:start] + oneline + audit[start:], (oneline,), True, ()),
            "pp.maxSteps": (audit[:start] + steps + audit[start:], (steps,), True, ()),
            "an option for one pin":
                (audit.replace(RESTRICT_GUARD, one_pin), (one_pin,), False, ()),
        }
        for label, (planted, snippets, read, others) in cases.items():
            with self.subTest(label):
                self.assertEqual(RESTRICT in pins.statement_pins(planted)[0], read)
                code, out = self.run_check((REPO / pins.BRIEF).read_text(), planted,
                                           printed=False)
                self.assertEqual(code, 1, out)
                self.assert_refused(out, [line for snippet in snippets
                                          for line in numbered(planted, snippet)], others)

    def test_a_namespace_whose_theorem_takes_a_pinned_name_is_refused(self):
        audit, start, end = self.real_pin()
        opening = f"namespace Shadow\ntheorem {RESTRICT} : True := trivial\n"
        closing = "end Shadow\n"
        planted = (audit[:start] + opening + f"\n/--\ninfo: {RESTRICT} : True\n-/\n"
                   + RESTRICT_GUARD + closing + audit[end:])
        # In the namespace, Lean's pin names the new theorem, and the reader alone counts it.
        self.assertIn(RESTRICT, pins.statement_pins(planted)[0])
        code, out = self.run_check((REPO / pins.BRIEF).read_text(), planted, printed=False)
        self.assertEqual(code, 1, out)
        self.assertNotIn("has no statement pin", out)
        self.assert_refused(out, numbered(planted, opening) + numbered(planted, closing))

    def test_a_check_pin_of_a_definition_the_section_names_is_refused(self):
        real = (REPO / pins.AUDIT).read_text()
        brief = (REPO / pins.BRIEF).read_text()
        section = {span for _, span in pins.names(pins.section(brief))}
        embedding = f"{S}.Interpretation.Embedding"
        # The two the section names, each with the print Lean gives its `#check`; and
        # `Embedding` declared `: id Type`, whose print shows neither sign, so that only
        # its name refuses it.
        self.assertIsNone(pins.definition_sign(ID_EMBEDDING.split(" : ", 1)[1]))
        cases = {"Interpretation.Embedding": (embedding, CHECKED[embedding]),
                 "Rule.Figure": (f"{S}.Rule.Figure", CHECKED[f"{S}.Rule.Figure"]),
                 "Interpretation.Embedding, : id Type": (embedding, ID_EMBEDDING)}
        self.assertEqual(set(pins.DEFINITIONS), {name for name, _ in cases.values()})
        for label, (name, printed) in cases.items():
            short = name.removeprefix(f"{S}.")
            with self.subTest(label):
                self.assertIn(short, section)
                start, end = pin_span(real, f"#print {name}")
                pin = check_pin(name, printed)
                planted = real[:start] + pin + real[end:]
                line = numbered(planted, pin)[-1][0]
                # The reader does not count the `#check`; it shows only the type.
                self.assertNotIn(name, pins.statement_pins(planted)[0])
                code, out = self.run_check(brief, planted, printed=False)
                self.assertEqual(code, 1, out)
                self.assert_refused(out, [], ((
                    line, f"#check @{name}",
                    f"pins a definition by `#check`, which shows only its type (`{name}` is "
                    "held to `#print` by name, whatever its print shows); only "
                    f"`#print {name}` pins a definition"),))
                self.assertIn(f"brief.md:{self.brief_line(short)}: `{short}` has no "
                              f"statement pin in {self.root / 'Audit.lean'}: its pin at "
                              f"{self.root / 'Audit.lean'}:{line} is a `#check` of a "
                              "definition held to `#print` by name, whatever its print "
                              "shows", out)
                # Reported once, as a name the section names.
                self.assertNotIn("no longer named", out)

    def test_a_definition_held_by_name_needs_its_print_though_the_section_drops_it(self):
        real = (REPO / pins.AUDIT).read_text()
        brief = (REPO / pins.BRIEF).read_text()
        name = f"{S}.Interpretation.Embedding"
        dropped = brief.replace("in I (`Interpretation.Embedding`), keeping",
                                "in I (an embedding), keeping")
        self.assertNotIn("Interpretation.Embedding",
                         {span for _, span in pins.names(pins.section(dropped))})
        code, out = self.run_check(dropped, real, printed=False)
        self.assertEqual(code, 0, out)
        start, end = pin_span(real, f"#print {name}")
        cases = {
            "removed": (real[:start] + real[end + 1:], " (an `info:` docstring"),
            "a #check": (real[:start] + check_pin(name, ID_EMBEDDING) + real[end:],
                         ": its pin at"),
        }
        for label, (planted, then) in cases.items():
            with self.subTest(label):
                code, out = self.run_check(dropped, planted, printed=False)
                self.assertEqual(code, 1, out)
                self.assertIn(f"Audit.lean: `{name}`, held to `#print` by name, though the "
                              f"section no longer names it, has no `#print` pin{then}", out)
                self.assertIn("✗ 1 of the 2 definitions held to `#print` by name have no "
                              "`#print` pin and are no longer named", out)
                self.assertNotIn("has no statement pin", out)

    def test_the_signs_refuse_a_definition_the_section_names_later(self):
        # A name not held by name, whose `#check` shows a sign in its type.
        name = f"{S}.Later.kind"
        for printed, sign in (
                (f"{name} : Nat → Type", "ending in the sort `Type`"),
                (f"@{name} : {{P : Type}} → P → List P",
                 "with `{P : Type} →`, where a proposition has `∀ {P : Type},`")):
            with self.subTest(printed):
                audit = f"/--\ninfo: {printed}\n-/\n#guard_msgs in\n#check @{name}\n"
                code, out = self.run_check(self.brief("`Later.kind` is a definition."), audit)
                self.assertEqual(code, 1, out)
                self.assert_refused(out, [], ((
                    5, f"#check @{name}", "pins a definition by `#check`, which shows only "
                                          f"its type (Lean prints the type {sign});"),))
                self.assertIn(f"`Later.kind` has no statement pin in {self.root / 'Audit.lean'}"
                              f": its pin at {self.root / 'Audit.lean'}:5 is a `#check`, but "
                              f"Lean prints the type {sign}", out)

    def test_the_definitions_pinned_theorems_read_must_be_printed(self):
        real = (REPO / pins.AUDIT).read_text()
        brief = (REPO / pins.BRIEF).read_text()
        self.assertEqual(set(pins.PRINTED), {f"{S}.Placed", f"{S}.Val.place",
                                             f"{S}.Metric.names"})
        section = {span for _, span in pins.names(pins.section(brief))}
        for name, readers in pins.PRINTED.items():
            # Each is read by theorems the section names, as the comment on it says: their
            # statement pins print its name.
            for reader in readers:
                with self.subTest(name, reader=reader):
                    self.assertIn(reader, section)
                    start, end = pin_span(real, f"#check @{S}.{reader}")
                    self.assertIn(f".{name.rsplit('.', 1)[1]}", real[start:end])
            start, end = pin_span(real, f"#print {name}")
            check = check_pin(name)
            no_sign = f"/--\ninfo: {name} : True\n-/\n#guard_msgs in\n#check @{name}\n"
            cases = {
                "removed": (real[:start] + real[end + 1:], None),
                "a #check": (real[:start] + check + real[end:], check),
                # Not what Lean prints, but a `#check` is no `#print` whatever it shows.
                "a #check whose type shows nothing": (real[:start] + no_sign + real[end:], None),
            }
            for label, (planted, refused) in cases.items():
                with self.subTest(name, case=label):
                    self.assertNotIn(name, pins.printed_pins(planted))
                    code, out = self.run_check(brief, planted, printed=False)
                    self.assertEqual(code, 1, out)
                    self.assertIn(f"Audit.lean: `{name}`, read by `{readers[0]}`", out)
                    self.assertIn("has no `#print` pin", out)
                    self.assertIn("✗ 1 of the 3 definitions that pinned theorems read have "
                                  "no `#print` pin", out)
                    self.assertNotIn("has no statement pin", out)
                    if refused:
                        line = numbered(planted, refused)[-1][0]
                        self.assertIn(f"Audit.lean:{line}: `#check @{name}` pins a definition "
                                      "by `#check`", out)
                        self.assertIn(f"its pin at {self.root / 'Audit.lean'}:{line} is a "
                                      "`#check`, but Lean prints the type", out)
                    elif label == "removed":
                        self.assertIn(f"then `#print {name}`)", out)
                        self.assertNotIn("refused", out)
                    else:
                        self.assertIn("is a `#check`, which shows only a definition's type",
                                      out)

    def test_a_statement_pin_cut_short_is_refused(self):
        real = (REPO / pins.AUDIT).read_text()
        brief = (REPO / pins.BRIEF).read_text()
        restrict = pin_span(real, f"#check @{RESTRICT}")
        names = pin_span(real, f"#print {S}.Metric.names")
        proof = f"{S}.Derives.map"
        # No option is in the file: as if set outside it, in the lakefile, or as Lean's
        # default `pp.maxSteps` on a long statement, or its default `pp.proofs` on a proof.
        # The last puts, under `Derives.map`'s name, the type Lean prints for a theorem
        # whose statement holds a proof, `(⟨0, by decide⟩ : Fin 3).val = 0`.
        cases = {
            "pp.deepTerms": (restrict, DEEP_RESTRICT, RESTRICT, "⋯"),
            "pp.oneline": (restrict, ONELINE_RESTRICT, RESTRICT, "[...]"),
            "pp.maxSteps on a #print": (names, STEPS_NAMES, f"{S}.Metric.names", "⋯"),
            "a proof under pp.proofs":
                (pin_span(real, f"#check @{proof}"), f"@{proof} : ↑⟨0, ⋯⟩ = 0", proof, "⋯"),
        }
        for label, ((start, end), printed, name, mark) in cases.items():
            with self.subTest(label):
                command = "#check @" if "#check" in real[start:end] else "#print "
                pin = f"/--\ninfo: {printed}\n-/\n#guard_msgs in\n{command}{name}\n"
                planted = real[:start] + pin + real[end:]
                number, line = numbered(planted, pin)[1]
                self.assertNotIn(name, pins.statement_pins(planted)[0])
                code, out = self.run_check(brief, planted, printed=False)
                self.assertEqual(code, 1, out)
                self.assert_refused(out, [], ((
                    number, line, f"holds `{mark}`, where Lean cut its print short, so the pin "
                                  f"of `{name}` matches only part of the statement"),))
                self.assertIn(f"its pin at {self.root / 'Audit.lean'}:{number} holds "
                              f"`{mark}`", out)

    def test_what_shows_a_definition_in_a_print(self):
        signs = {
            f"{S}.Rule.Figure": "ending in the sort `Prop`",
            f"{S}.Interpretation.Embedding": "ending in the sort `Type`",
            f"{S}.Placed": "ending in the sort `Prop`",
            f"{S}.Val.place": f"with `{{I : {S}.Interpretation}} →`, where a proposition has "
                              f"`∀ {{I : {S}.Interpretation}},`",
            f"{S}.Metric.names": "with `{P : Type} →`, where a proposition has "
                                 "`∀ {P : Type},`",
        }
        for name, sign in signs.items():
            with self.subTest(name):
                self.assertEqual(pins.definition_sign(CHECKED[name].split(" : ", 1)[1]), sign)
        # Other types as Lean prints them: definitions' types; propositions, some only
        # looking like definitions' (a sort after an arrow inside a `fun` or after `have`, an
        # equation of sorts, a function type in brackets); and types that show neither sign,
        # propositions and definitions alike (the last two are definitions' types).
        prints = {
            "{α : Type u_1} → [Inhabited α] → List α": "with `{α : Type u_1} →`",
            "Sort u_1 → Sort (max 1 u_1)": "ending in the sort `Sort (max 1 u_1)`",
            "Type → Type": "ending in the sort `Type`",
            "((fun n => Nat) = fun n => Nat → Prop) → (fun n => Nat) = fun n => Nat → Prop":
                None,
            "1 = 1 →\n  have T := Prop;\n  T = Prop": None,
            "Sort (max u_1 u_2) = Sort (max u_2 u_1)": None,
            "(∀ (x : Nat), x = x) → Nonempty Prop": None,
            "∀ (a : (x : Nat) → Fin (x + 1)), True": None,
            "1 = 1 → 2 = 2": None,
            "2 = 2": None,
            "((x : Nat) → Fin (x + 1)) → Nat": None,
            "Nat → Nat": None,
        }
        for printed, sign in prints.items():
            with self.subTest(printed):
                found = pins.definition_sign(printed)
                if sign is None:
                    self.assertIsNone(found)
                else:
                    self.assertIsNotNone(found)
                    self.assertTrue(found.startswith(sign), found)
        # Every `#check` pin in the real file pins a theorem, and shows nothing.
        found = [pin for pin in pins.read_pins((REPO / pins.AUDIT).read_text())
                 if pin.command == "check"]
        self.assertEqual(len(found), 17)
        self.assertEqual([pin.name for pin in found if pin.sign or pin.shortened], [])

    def test_any_other_command_after_a_pin_is_refused(self):
        pin = PIN.format(name="Derives.sound")
        commands = (
            "theorem extra : True := trivial", "private theorem extra : True := trivial",
            "@[simp] theorem extra : True := trivial", "def extra : Nat := 1",
            "abbrev extra : Nat := 1", "instance : Inhabited Nat := ⟨1⟩",
            "axiom extra : False", "attribute [simp] Nat.add_comm",
            'notation "pinned" => True', 'macro "pinned" : term => `(True)',
            "open Elements.Superposition", "section", "end", "variable (n : Nat)",
            "universe u", "set_option pp.all true", "#eval 1", "#exit", f"#print {SOUND}",
            f"#guard_msgs in #check @{SOUND}", "import Elements.BookI.Prop04",
        )
        for command in commands:
            with self.subTest(command):
                code, out = self.run_check(self.brief("`Derives.sound` holds."),
                                           f"{pin}\n{command}\n{pin}")
                self.assertEqual(code, 1, out)
                self.assertNotIn("has no statement pin", out)
                self.assert_refused(out, [(7, command)])

    def test_imports_lead_the_file_one_module_each(self):
        pin = PIN.format(name="Derives.sound")
        brief = self.brief("`Derives.sound` holds.")
        code, out = self.run_check(brief, "-- a note\nimport Elements.BookI.Prop04\n/- a note -/\n"
                                   "import Elements.BookI.Prop08\n\n/-! A module doc. -/\n\n" + pin)
        self.assertEqual(code, 0, out)
        two = "import Elements.BookI.Prop04 Elements.BookI.Prop08"
        code, out = self.run_check(brief, f"{two}\n\n{pin}")
        self.assertEqual(code, 1, out)
        self.assert_refused(out, [(1, two)])
        # An import between a pin's docstring and its guard leads nothing, and the guard
        # after it is not directly after the docstring.
        audit = pin.replace("#guard_msgs in", "import Elements.BookI.Prop04\n#guard_msgs in")
        code, out = self.run_check(brief, audit)
        self.assertEqual(code, 1, out)
        self.assert_refused(out, [(4, "import Elements.BookI.Prop04"), (5, "#guard_msgs in"),
                                  (6, f"#check @{SOUND}")])

    def test_a_pin_with_no_docstring_is_refused(self):
        bare = f"#guard_msgs in\n#check @{SOUND}\n"
        for label, audit, first in (
                ("first in the file", bare + "\n" + PIN.format(name="Derives.sound"), 1),
                ("after the imports", "import Elements.BookI.Prop04\n" + bare, 2)):
            with self.subTest(label):
                code, out = self.run_check(self.brief("`Derives.sound` holds."), audit)
                self.assertEqual(code, 1, out)
                self.assert_refused(out, [(first, "#guard_msgs in"),
                                          (first + 1, f"#check @{SOUND}")])

    def test_audit_lean_must_import_the_audit_file(self):
        brief, pin = self.brief("`Derives.sound` holds."), PIN.format(name="Derives.sound")
        cases = {
            "imported": ("import Audit.Overlaps\nimport Audit.Superposition\n", 0),
            "not imported": ("import Audit.Overlaps\n", 1),
            "imported in a line comment":
                ("import Audit.Overlaps\n-- import Audit.Superposition\n", 1),
            "imported in a block comment":
                ("/- import Audit.Superposition -/\nimport Audit.Overlaps\n", 1),
            "a longer module": ("import Audit.Superposition.Extra\n", 1),
            "imported after a command":
                ("import Audit.Overlaps\n#check Nat\nimport Audit.Superposition\n", 1),
        }
        for label, (library, expected) in cases.items():
            with self.subTest(label):
                code, out = self.run_check(brief, pin, library=library)
                self.assertEqual(code, expected, out)
                if expected:
                    self.assertIn("Library.lean: does not import Audit.Superposition", out)
                    self.assertIn("✗ 1 refused", out)

    def test_a_pin_in_a_comment_is_not_counted(self):
        pin = PIN.format(name="Derives.sound")
        cases = {
            "a block comment": f"/-\n{pin}-/\n",
            "a nested block comment": f"/- outer /- inner -/\n{pin}-/\n",
            "a module doc": f"/-!\n{pin}-/\n",
            "line comments": "".join(f"-- {line}\n" for line in pin.splitlines()),
        }
        for label, audit in cases.items():
            with self.subTest(label):
                code, out = self.run_check(self.brief("`Derives.sound` holds."), audit)
                self.assertEqual(code, 1, out)
                self.assertIn("`Derives.sound` has no statement pin", out)
                self.assertNotIn("refused", out)

    def test_the_reader_skips_a_pin_lean_never_runs(self):
        pin = PIN.format(name="Derives.sound")
        cases = {
            "a block comment": f"/-\n{pin}-/\n",
            "a nested block comment": f"/- outer /- inner -/\n{pin}-/\n",
            "a module doc": f"/-!\n{pin}-/\n",
            "line comments": "".join(f"-- {line}\n" for line in pin.splitlines()),
            "a doc comment opened by /--/": f"/--/\n{pin}-/\n",
            "a string": f'#eval "\n{pin}"\n',
            "a string with an escaped quote": f'#eval "\\"\n{pin}"\n',
            "a raw string": f'#eval r#"\n"\n{pin}"#\n',
            "after #exit": f"#exit\n{pin}",
        }
        for label, audit in cases.items():
            with self.subTest(label):
                self.assertEqual(pins.statement_pins(audit), (set(), {}))

    def test_the_reader_finds_a_pin_beside_quotes_that_hide_nothing(self):
        pin = PIN.format(name="Derives.sound")
        cases = {
            "a character literal of a quote": f"#eval '\"'\n{pin}#eval '\"'\n",
            "a primed name": f"#check fun B' => B'\n{pin}",
            "a dash in a string": f'#eval "--"\n{pin}',
            "a comment closed before it": f"/- a note -/\n{pin}",
            "a line comment before it": f"-- a note\n{pin}",
        }
        for label, audit in cases.items():
            with self.subTest(label):
                self.assertEqual(pins.statement_pins(audit), ({SOUND}, {}))
        # A comment is all of these the audit file may hold, so only these pass whole.
        for label in ("a comment closed before it", "a line comment before it"):
            with self.subTest(label, whole=True):
                code, out = self.run_check(self.brief("`Derives.sound` holds."), cases[label])
                self.assertEqual(code, 0, out)

    def test_an_unclosed_comment_cannot_be_read(self):
        code, out = self.run_check(self.brief("`Derives.sound` holds."),
                                   "/- never closed\n" + PIN.format(name="Derives.sound"))
        self.assertEqual(code, 2, out)
        self.assertIn("is never closed", out)

    def test_a_subsection_is_read(self):
        code, out = self.run_check(self.brief("Nothing here.").replace(
            "### A subsection, still read\n", "### A subsection, still read\n\n`Sub.name`\n"), "")
        self.assertEqual(code, 1, out)
        self.assertIn("`Sub.name` has no statement pin", out)

    def test_a_brief_without_the_section_cannot_be_read(self):
        code, out = self.run_check("# Brief\n\n## Another section\n", "")
        self.assertEqual(code, 2, out)
        self.assertIn("no heading", out)

    def test_a_missing_audit_file_or_audit_lean_cannot_be_read(self):
        (self.root / "brief.md").write_text(self.brief("`Derives.map`."))
        (self.root / "Audit.lean").write_text(PIN.format(name="Derives.map"))
        for flag in ("--audit", "--library"):
            with self.subTest(flag):
                argv = ["--brief", str(self.root / "brief.md"),
                        "--audit", str(self.root / "Audit.lean"),
                        flag, str(self.root / "missing.lean")]
                out = io.StringIO()
                with redirect_stdout(out), redirect_stderr(out):
                    code = pins.main(argv)
                self.assertEqual(code, 2, out.getvalue())
                self.assertIn("cannot read", out.getvalue())


if __name__ == "__main__":
    unittest.main()
