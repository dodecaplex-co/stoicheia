#!/usr/bin/env python3
"""The cases of scripts/check_superposition_pins.py, without Lean.

    python3 -I tests/test_check_superposition_pins.py

The real brief and audit file must pass. In copies, an invented theorem name in the
restriction section must fail with its line and name, and so must a name pinned only by
its axioms, by a `#check` with no `#guard_msgs`, by a `#guard_msgs` with any option
(`substring := true` among them), or by a pin Lean never runs: one in a block comment, in
`--` comments, in a string or after `#exit`. A name is pinned only under its full name, so
a pin of `Rule.Figure.restrict` does not pin a bare `restrict`. The exceptions
(`Rule.infer`, `Metric`, `cite`, file names, Lean's axioms, single letters and spans that
are not one identifier) pass with no pin, a name outside the section is not read, and a
brief without the section, or whose section names no theorem, cannot be read.
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


class PinTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory()))

    def run_check(self, brief: str, audit: str) -> tuple[int, str]:
        (self.root / "brief.md").write_text(brief)
        (self.root / "Audit.lean").write_text(audit)
        out = io.StringIO()
        with redirect_stdout(out), redirect_stderr(out):
            code = pins.main(["--brief", str(self.root / "brief.md"),
                              "--audit", str(self.root / "Audit.lean")])
        return code, out.getvalue()

    def brief(self, body: str, after: str = "") -> str:
        return ("# Brief\n\n## Before\n\n`Before.only` is not read.\n\n"
                f"{pins.HEADING}\n\n{body}\n\n### A subsection, still read\n\n"
                f"## After\n\n{after}\n")

    def test_the_real_brief_passes(self):
        out = io.StringIO()
        with redirect_stdout(out), redirect_stderr(out):
            code = pins.main([])
        self.assertEqual(code, 0, out.getvalue())
        self.assertIn("has a statement pin", out.getvalue())

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
        code, out = self.run_check(self.brief("`Derives.sound` holds."),
                                   "#check @Elements.Superposition.Derives.sound\n")
        self.assertEqual(code, 1, out)

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
                audit = "-- the pin\n\n" + PIN.format(name="Derives.sound").replace(
                    "#guard_msgs in", f"#guard_msgs {options} in")
                code, out = self.run_check(self.brief("`Derives.sound` holds."), audit)
                self.assertEqual(code, 1, out)
                self.assertIn("`Derives.sound` has no statement pin", out)
                self.assertIn(f"Audit.lean:6 is under `#guard_msgs {options} in`", out)
                self.assertIn("only a bare `#guard_msgs in` pins a statement", out)

    def test_a_bare_pin_beside_a_weak_one_passes(self):
        bare = PIN.format(name="Derives.sound")
        weak = bare.replace("#guard_msgs in", "#guard_msgs (substring := true) in")
        code, out = self.run_check(self.brief("`Derives.sound` holds."), weak + "\n" + bare)
        self.assertEqual(code, 0, out)

    def test_a_pin_lean_never_runs_is_not_read(self):
        pin = PIN.format(name="Derives.sound")
        commented = "".join(f"-- {line}\n" for line in pin.splitlines())
        cases = {
            "a block comment": f"/-\n{pin}-/\n",
            "a nested block comment": f"/- outer /- inner -/\n{pin}-/\n",
            "a module doc": f"/-!\n{pin}-/\n",
            "line comments": commented,
            "a string": f'#eval "\n{pin}"\n',
            "a string with an escaped quote": f'#eval "\\"\n{pin}"\n',
            "a raw string": f'#eval r#"\n"\n{pin}"#\n',
            "after #exit": f"#exit\n{pin}",
        }
        for label, audit in cases.items():
            with self.subTest(label):
                code, out = self.run_check(self.brief("`Derives.sound` holds."), audit)
                self.assertEqual(code, 1, out)
                self.assertIn("`Derives.sound` has no statement pin", out)

    def test_quotes_lean_reads_otherwise_do_not_hide_a_pin(self):
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
                code, out = self.run_check(self.brief("`Derives.sound` holds."), audit)
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

    def test_a_missing_audit_file_cannot_be_read(self):
        (self.root / "brief.md").write_text(self.brief("`Derives.map`."))
        out = io.StringIO()
        with redirect_stdout(out), redirect_stderr(out):
            code = pins.main(["--brief", str(self.root / "brief.md"),
                              "--audit", str(self.root / "missing.lean")])
        self.assertEqual(code, 2, out.getvalue())


if __name__ == "__main__":
    unittest.main()
