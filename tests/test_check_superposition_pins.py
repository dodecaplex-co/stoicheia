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
with their lines, and the reader alone would have counted the first and the last. So are
any declaration or other command after a pin, `#eval` and `#exit` among them, a guard with
options even beside a bare one, a pin with no docstring, and an import after a pin or
between a pin's docstring and its guard.
Audit.lean must import the audit file in its leading imports, not in a comment and not
after a command. The reader of pins is tested on its own for pins Lean never runs (in a
comment, a doc comment opened by `/--/`, a string or after `#exit`) and for quotes that
hide nothing, since the file may no longer hold the `#eval`s that carry those cases.
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

    def run_check(self, brief: str, audit: str, library: str | None = None) -> tuple[int, str]:
        (self.root / "brief.md").write_text(brief)
        (self.root / "Audit.lean").write_text(audit)
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

    def assert_refused(self, out: str, refused: list[tuple[int, str]]):
        for number, line in refused:
            self.assertIn(f"Audit.lean:{number}: `{pins.shorten(line)}` is not a leading "
                          "import, a comment or a pin", out)
        self.assertIn(f"✗ {len(refused)} refused", out)

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
        code, out = self.run_check(text, (REPO / pins.AUDIT).read_text())
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
        code, out = self.run_check(self.brief("`Rule.Figure` is a definition."), audit)
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
        # (the copy, the snippets planted in it, and whether the reader alone counts the pin)
        cases = {
            "pp.deepTerms, threshold 0":
                (audit[:start] + deep + shortened + back + audit[end:], (deep, back), True),
            "pp.oneline": (audit[:start] + oneline + audit[start:], (oneline,), True),
            "pp.maxSteps": (audit[:start] + steps + audit[start:], (steps,), True),
            "an option for one pin": (audit.replace(RESTRICT_GUARD, one_pin), (one_pin,), False),
        }
        for label, (planted, snippets, read) in cases.items():
            with self.subTest(label):
                self.assertEqual(RESTRICT in pins.statement_pins(planted)[0], read)
                code, out = self.run_check((REPO / pins.BRIEF).read_text(), planted)
                self.assertEqual(code, 1, out)
                self.assert_refused(out, [line for snippet in snippets
                                          for line in numbered(planted, snippet)])

    def test_a_namespace_whose_theorem_takes_a_pinned_name_is_refused(self):
        audit, start, end = self.real_pin()
        opening = f"namespace Shadow\ntheorem {RESTRICT} : True := trivial\n"
        closing = "end Shadow\n"
        planted = (audit[:start] + opening + f"\n/--\ninfo: {RESTRICT} : True\n-/\n"
                   + RESTRICT_GUARD + closing + audit[end:])
        # In the namespace, Lean's pin names the new theorem, and the reader alone counts it.
        self.assertIn(RESTRICT, pins.statement_pins(planted)[0])
        code, out = self.run_check((REPO / pins.BRIEF).read_text(), planted)
        self.assertEqual(code, 1, out)
        self.assertNotIn("has no statement pin", out)
        self.assert_refused(out, numbered(planted, opening) + numbered(planted, closing))

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
