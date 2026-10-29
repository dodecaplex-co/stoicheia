#!/usr/bin/env python3
"""Focused cases for Certificate/Facts.lean's restricted-calculus C.N. 4 detection, its
module boundary, its construction rules and cited laws, its shared steps and each entry's
proved rules; and for check_fidelity.py's reading of the expectations on them.

    export PATH=$HOME/.elan/bin:$PATH
    lake build
    python3 -I tests/test_certificate.py

Run an unmodified copy of the certificate source against a small Lean fixture compiled
as the temporary package's Elements module. The temporary module takes precedence over
the repository's Elements module while retaining access to its foundation modules. The
package keeps every output, including facts.json, away from the repository. The fixture
declares stand-ins with the exact marker and constructor names, so it can land before the
calculus it checks.

Each congruence constructor is tested directly, through a helper's value and through
map and sound. Reaching only the inductive type's constructor list (I.7), naming another
Derives constructor (I.8), transforming or eliminating a given derivation (I.9, I.10,
I.16), or passing a bound marker (I.14) reports no C.N. 4. A helper that names the step
counts even when that branch is not taken (I.15). Every case keeps the same axiom fields.

Separately compiled helpers in Staging.Hidden must be refused by their declaring module,
even when their names begin with Elements. They supply a step, a Common Notion or an
existing axiom, or appear only in an entry's type. So must a separately compiled
Lean.Hidden that supplies a Common Notion: its root is Lean's, but its .olean is not the
toolchain's. The temporary package's Lean root links every other entry to the toolchain's
own files, so a reached declaration of Lean.Data.Position still ends a walk.

A third fixture, tests/fixtures/CertificateCited.lean, imports the repository's compiled
foundations themselves. Its own axioms are the cases of a construction rule: existence
asserted directly, through a definition, through a projection of a structure that a
definition gives, through a projection reached through nested structures and through a
function's arguments, through an inherited instance's order, through a let-bound
structure, through a let at an application's head, twice negated, in an Iff and in an
Or, each counted; existence negated, outright or by a definition (Triangle), behind an
implication inside a definition, assumed in a hypothesis, absent, or only in a field the
statement does not read, none counted. Its entries cite laws through one shared theorem
that proves a list of laws by cases (I.1), whose proofs the walk finds, and law by law,
naming each law's proof (I.2), which is listed alone: each law with its proofs, where Lean
declares them, and the construction rules beneath them, in the order of the Cited type. A
proof reached only through another entry is not found (I.3); a named proof that leaves
another proof reached outside it lists every proof reached, with all their rules (I.6);
and a law named with no proof found fails the run (I.5).

A fourth class reads the forms of tests/certificate_expectations.json as
scripts/check_fidelity.py does, on small facts and without Lean: a cited law's
construction rules, a field of facts.json's top level, a field of every entry and an
entry's proved rules, apart from the top level's, are read; an entry's states, given with
`one_of`, hold when exactly one does, and fail once when none does, naming each state with
what sank it, or when two do, naming them; and an expectation that is malformed, unmet or
asks nothing fails.

A fifth class compiles a fixture written in the test, over the foundations' Common
Notions: a tacit rule proved from III.2, which III.3 calls itself and III.4 only through a
lemma outside its namespace. III.3's shared steps list the rule, bringing in III.2;
III.4's list the lemma and not the rule.

A sixth class checks each entry's proved rules against two stand-ins declared as theorems
in Elements.Tacit, the second proved from the first, on a fixture written in the test. An
entry must list those its proof reaches directly, through its own helper, through a lemma,
an entry it cites or a Common Notion, or its statement alone; both when it reaches the
second; and none when it reaches neither. The fixture declares its own stand-ins for the
Common Notions, under their names, the second proved from the first rule. A copy of the
certificate whose walk for the proved rules stops at each rule must fail the run, its
check against Lean naming every entry that rests on a rule.

The foundation modules must be built first. CI's check job and the pre-flight run this
immediately after Certificate/Facts.lean, as in docs/WORKFLOW.md, section 8.
Standard library only.
"""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import check_fidelity  # noqa: E402
AXIOM_FIELDS = ("axioms", "direct_axioms", "own_axioms", "inherited", "lean_foundations")


def prepare_package(work):
    (work / "lakefile.toml").write_text('name = "certificate_fixture"\n')
    (work / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())
    shutil.copyfile(ROOT / "Certificate/Facts.lean", work / "Facts.lean")
    env = os.environ.copy()
    repository_modules = str(ROOT / ".lake/build/lib/lean")
    if inherited_modules := env.get("LEAN_PATH"):
        repository_modules += os.pathsep + inherited_modules
    fixture_modules = work / ".lake/build/lib/lean"
    fixture_modules.mkdir(parents=True)
    shutil.copytree(
        ROOT / ".lake/build/lib/lean/Elements/Foundations",
        fixture_modules / "Elements/Foundations",
    )
    env["LEAN_PATH"] = str(fixture_modules) + os.pathsep + repository_modules
    return env, fixture_modules


def shadow_lean_root(work, env, modules):
    result = subprocess.run(
        ["lake", "env", "lean", "--print-libdir"],
        cwd=work, env=env, capture_output=True, text=True, timeout=120,
    )
    if result.returncode:
        raise AssertionError(
            f"lean --print-libdir exited {result.returncode}\n" + result.stdout + result.stderr
        )
    library = Path(result.stdout.strip())
    (modules / "Lean").mkdir()
    for entry in (library / "Lean").iterdir():
        (modules / "Lean" / entry.name).symlink_to(entry)
    for entry in library.glob("Lean.*"):
        (modules / entry.name).symlink_to(entry)


def compile_module(work, env, modules, name):
    source = Path(*name.split(".")).with_suffix(".lean")
    output = (modules / source).with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(
        ["lake", "env", "lean", str(source), "-o", str(output)],
        cwd=work, env=env, capture_output=True, text=True, timeout=120,
    )
    if result.returncode:
        raise AssertionError(
            f"fixture {name}: lake env lean exited {result.returncode}\n"
            + result.stdout + result.stderr
        )


class CommonNotion4Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with tempfile.TemporaryDirectory(prefix="stoicheia-cn4-") as tmp:
            work = Path(tmp)
            env, fixture_modules = prepare_package(work)
            shutil.copyfile(ROOT / "tests/fixtures/CertificateCN4.lean", work / "Elements.lean")
            compile_module(work, env, fixture_modules, "Elements")
            certificate_result = subprocess.run(
                ["lake", "env", "lean", "Facts.lean"],
                cwd=work, env=env, capture_output=True, text=True, timeout=120,
            )
            if certificate_result.returncode:
                raise AssertionError(
                    f"certificate: lake env lean exited {certificate_result.returncode}\n"
                    + certificate_result.stdout + certificate_result.stderr
                )
            facts = json.loads((work / "facts.json").read_text())
        cls.entries = {entry["ref"]: entry for entry in facts["propositions"]}
        if set(cls.entries) != {f"I.{i}" for i in range(1, 17)}:
            raise AssertionError(f"unexpected fixture subjects: {sorted(cls.entries)}")

    def test_direct_constructors(self):
        for number, name in enumerate(("len_congr", "angle_congr", "area_congr"), 1):
            with self.subTest(constructor=name):
                self.assertEqual(self.entries[f"I.{number}"]["common_notions"], ["C.N. 4"])

    def test_constructors_through_helper_values(self):
        for number, name in enumerate(("len_congr", "angle_congr", "area_congr"), 4):
            with self.subTest(constructor=name):
                self.assertEqual(self.entries[f"I.{number}"]["common_notions"], ["C.N. 4"])

    def test_constructor_metadata_does_not_count(self):
        for ref in ("I.7", "I.8"):
            with self.subTest(ref=ref):
                self.assertEqual(self.entries[ref]["common_notions"], [])

    def test_transformers_without_step_do_not_count(self):
        for ref in ("I.9", "I.10", "I.16"):
            with self.subTest(ref=ref):
                self.assertEqual(self.entries[ref]["common_notions"], [])

    def test_transformers_preserve_real_steps(self):
        for number, name in enumerate(("len_congr", "angle_congr", "area_congr"), 11):
            with self.subTest(constructor=name):
                self.assertEqual(self.entries[f"I.{number}"]["common_notions"], ["C.N. 4"])

    def test_bound_marker_does_not_count(self):
        self.assertEqual(self.entries["I.14"]["common_notions"], [])

    def test_helper_naming_step_counts_without_evaluation(self):
        self.assertEqual(self.entries["I.15"]["common_notions"], ["C.N. 4"])

    def test_axiom_fields_unchanged(self):
        control = self.entries["I.7"]
        self.assertEqual(control["axioms"], ["Tacit.add_comm", "Tacit.add_zero"])
        self.assertEqual(control["own_axioms"], ["Tacit.add_comm"])
        self.assertEqual(set(control["inherited"]), {"Tacit.add_zero"})
        self.assertEqual(
            [lemma["name"] for lemma in control["inherited"]["Tacit.add_zero"]],
            ["CertificateFixture.add_nothing"],
        )
        for ref, entry in self.entries.items():
            with self.subTest(ref=ref):
                self.assertEqual(entry["status"], "proved")
                self.assertEqual(entry["cites"], [])
                for field in AXIOM_FIELDS:
                    with self.subTest(field=field):
                        self.assertEqual(entry[field], control[field])


class ModuleBoundaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        tmp = tempfile.TemporaryDirectory(prefix="stoicheia-modules-")
        cls.addClassCleanup(tmp.cleanup)
        cls.work = Path(tmp.name)
        cls.env, cls.modules = prepare_package(cls.work)
        (cls.work / "Elements").mkdir()
        shutil.copyfile(
            ROOT / "tests/fixtures/CertificateCN4.lean",
            cls.work / "Elements/CertificateFixture.lean",
        )
        compile_module(cls.work, cls.env, cls.modules, "Elements.CertificateFixture")
        (cls.work / "Staging").mkdir()
        (cls.work / "Staging/Hidden.lean").write_text(
            "import Elements.CertificateFixture\n"
            "namespace Elements.Hidden\n"
            "theorem step : Superposition.Coincidence := .step\n"
            "theorem notion (a b c : Length) (h : a = c) (k : b = c) : a = b :=\n"
            "  CommonNotion1 h k\n"
            "theorem rule (a b : Length) : a + b = b + a := Tacit.add_comm a b\n"
            "end Elements.Hidden\n"
        )
        compile_module(cls.work, cls.env, cls.modules, "Staging.Hidden")
        shadow_lean_root(cls.work, cls.env, cls.modules)
        (cls.work / "Lean").mkdir()
        (cls.work / "Lean/Hidden.lean").write_text(
            "import Elements.CertificateFixture\n"
            "namespace Lean.Hidden\n"
            "theorem notion (a b c : Elements.Length) (h : a = c) (k : b = c) : a = b :=\n"
            "  Elements.CommonNotion1 h k\n"
            "end Lean.Hidden\n"
        )
        compile_module(cls.work, cls.env, cls.modules, "Lean.Hidden")

    def certificate(self, declaration):
        (self.work / "Elements.lean").write_text(
            "import Staging.Hidden\nimport Lean.Hidden\nimport Lean.Data.Position\n"
            + declaration + "\n"
        )
        compile_module(self.work, self.env, self.modules, "Elements")
        (self.work / "facts.json").unlink(missing_ok=True)
        return subprocess.run(
            ["lake", "env", "lean", "Facts.lean"],
            cwd=self.work, env=self.env, capture_output=True, text=True, timeout=120,
        )

    def test_foreign_helpers_are_rejected(self):
        cases = (
            ("step", "theorem Prop17 : Superposition.Coincidence := Hidden.step"),
            ("notion", "theorem Prop17 (a b c : Length) (h : a = c) (k : b = c) : "
             "a = b := Hidden.notion a b c h k"),
            ("rule", "theorem Prop17 (a b : Length) : a + b = b + a := Hidden.rule a b"),
            ("rule", "theorem Prop17 (a b : Length) : "
             "a + b = b + a ∧ a + b = b + a := ⟨Tacit.add_comm a b, Hidden.rule a b⟩"),
            ("step", "theorem Prop17 : (fun _ => True) Hidden.step := True.intro"),
        )
        for helper, declaration in cases:
            with self.subTest(helper=helper, declaration=declaration):
                result = self.certificate(
                    f"namespace Elements.BookI\n{declaration}\nend Elements.BookI"
                )
                output = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, output)
                self.assertIn(
                    f"certificate: declaration Elements.Hidden.{helper} is declared in "
                    "unsupported module Staging.Hidden; expected Elements, or Init, Std or "
                    "Lean from the running Lean toolchain",
                    output,
                )
                self.assertFalse((self.work / "facts.json").exists())

    def test_modules_from_outside_the_toolchain_are_rejected_under_its_roots(self):
        result = self.certificate(
            "namespace Elements.BookI\n"
            "theorem Prop17 (a b c : Length) (h : a = c) (k : b = c) : a = b :=\n"
            "  Lean.Hidden.notion a b c h k\n"
            "end Elements.BookI"
        )
        output = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, output)
        self.assertIn(
            "certificate: declaration Lean.Hidden.notion is declared in unsupported module "
            "Lean.Hidden; expected Elements, or Init, Std or Lean from the running Lean "
            "toolchain",
            output,
        )
        self.assertFalse((self.work / "facts.json").exists())

    def test_reached_toolchain_modules_end_walks(self):
        result = self.certificate(
            "namespace Elements.BookI\n"
            "theorem Prop17 : (Lean.Position.mk 1 2).line = 1 := rfl\n"
            "end Elements.BookI"
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        facts = json.loads((self.work / "facts.json").read_text())
        entry = next(entry for entry in facts["propositions"] if entry["ref"] == "I.17")
        self.assertEqual(entry["status"], "proved")
        self.assertEqual(entry["common_notions"], [])
        self.assertEqual(entry["axioms"], [])

    def test_unused_foreign_helpers_do_not_fail(self):
        result = self.certificate("")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue((self.work / "facts.json").is_file())


class ConstructionTests(unittest.TestCase):
    """The construction rules and the cited laws, on tests/fixtures/CertificateCited.lean
    over the repository's compiled foundations (#150, question 4)."""

    CONSTRUCTS = ("plain", "circles", "line_circle", "lines", "by_projection",
                  "by_nested_projection", "by_instance", "twice_negated", "in_iff", "in_or")
    DOES_NOT = ("triangle", "not_collinear", "empty", "assumed", "equal", "other_field",
                "prop7_law")

    @classmethod
    def setUpClass(cls):
        tmp = tempfile.TemporaryDirectory(prefix="stoicheia-cited-")
        cls.addClassCleanup(tmp.cleanup)
        cls.work = Path(tmp.name)
        cls.env, cls.modules = prepare_package(cls.work)
        cls.fixture = (ROOT / "tests/fixtures/CertificateCited.lean").read_text()
        result = cls.certificate("")
        if result.returncode:
            raise AssertionError(
                f"certificate: lake env lean exited {result.returncode}\n"
                + result.stdout + result.stderr
            )
        cls.facts = json.loads((cls.work / "facts.json").read_text())
        cls.entries = {entry["ref"]: entry for entry in cls.facts["propositions"]}

    @classmethod
    def certificate(cls, declarations):
        """Compile the fixture, with `declarations` added before its last line, as the
        package's Elements module, and run the certificate on it."""
        body, last = cls.fixture.rstrip("\n").rsplit("\n", 1)
        (cls.work / "Elements.lean").write_text(f"{body}\n{declarations}\n{last}\n")
        compile_module(cls.work, cls.env, cls.modules, "Elements")
        (cls.work / "facts.json").unlink(missing_ok=True)
        return subprocess.run(
            ["lake", "env", "lean", "Facts.lean"],
            cwd=cls.work, env=cls.env, capture_output=True, text=True, timeout=300,
        )

    def test_rules_asserting_existence_are_construction_rules(self):
        rules = self.facts["construction_rules"]
        for name in self.CONSTRUCTS:
            with self.subTest(axiom=name):
                self.assertIn(f"CitedFixture.{name}", rules)
        self.assertIn("Postulate1", rules)

    def test_rule_through_an_inherited_instance_projection(self):
        self.assertIn("CitedFixture.by_instance", self.facts["construction_rules"])

    def test_rule_through_a_projection_of_a_definitions_structure(self):
        self.assertIn("CitedFixture.by_projection", self.facts["construction_rules"])

    def test_rule_through_nested_structures_and_a_functions_arguments(self):
        # `(twoFamily.pick L).holds L α`: the second field of `twoFamily`, a function, is
        # applied to `L`, and the second field of what it gives is read. Its first field,
        # which asserts no existence, must not be read in its place.
        rules = self.facts["construction_rules"]
        self.assertIn("CitedFixture.by_nested_projection", rules)
        self.assertNotIn("CitedFixture.other_field", rules)

    def test_rule_through_a_let_bound_structure(self):
        self.assertIn("CitedFixture.circles", self.facts["construction_rules"])

    def test_rule_through_a_let_at_an_applications_head(self):
        self.assertIn("CitedFixture.lines", self.facts["construction_rules"])

    def test_rules_not_asserting_existence_are_not(self):
        rules = self.facts["construction_rules"]
        for name in self.DOES_NOT:
            with self.subTest(axiom=name):
                self.assertNotIn(f"CitedFixture.{name}", rules)
        for name in ("Postulate4", "Definition15", "Tacit.superposition"):
            with self.subTest(axiom=name):
                self.assertNotIn(name, rules)

    def test_construction_rules_are_sorted_axioms(self):
        rules = self.facts["construction_rules"]
        self.assertEqual(rules, sorted(set(rules)))
        for name in rules:
            with self.subTest(axiom=name):
                self.assertIn(name, self.facts["axiom_modules"])

    @classmethod
    def proof(cls, name):
        """A proof as `proofs` lists it: its name, and where Lean declares it, in the
        fixture compiled as the package's Elements module."""
        short = name.split(".", 1)[1]
        lines = cls.fixture.splitlines()
        line = next(i for i, text in enumerate(lines, 1)
                    if text.startswith(f"theorem {short} "))
        return {"name": name, "file": "Elements.lean", "line": line}

    def test_laws_through_one_shared_theorem(self):
        self.assertEqual(self.entries["I.1"]["cited_laws"], [
            {"law": "lenSymm", "proofs": [self.proof("CitedFixture.holds_lenSymm")],
             "construction_rules": []},
            {"law": "angleSymm", "proofs": [self.proof("CitedFixture.holds_angleSymm")],
             "construction_rules": ["Postulate1"]},
        ])

    def test_laws_one_by_one_in_the_type_order(self):
        # Metric 3's law is named through its second proof, which the first lies beneath,
        # so the second alone is listed.
        self.assertEqual(self.entries["I.2"]["cited_laws"], [
            {"law": "lenSymm", "proofs": [self.proof("CitedFixture.holds_lenSymm'")],
             "construction_rules": []},
            {"law": "prop7", "proofs": [self.proof("BookI.Prop2.holds_prop7")],
             "construction_rules": ["Tacit.circles_meet"]},
        ])

    def test_walk_stops_at_other_entries(self):
        self.assertEqual(self.entries["I.3"]["cited_laws"], [
            {"law": "lenSymm", "proofs": [self.proof("CitedFixture.holds_lenSymm")],
             "construction_rules": []},
        ])

    def test_a_proof_reached_outside_the_named_ones_lists_every_proof(self):
        # I.6 names the first proof of Metric 3's law, and reaches the drawn one only through
        # a lemma: every proof reached is listed, with the rules beneath them all.
        self.assertEqual(self.entries["I.6"]["cited_laws"], [
            {"law": "lenSymm", "proofs": [self.proof("CitedFixture.holds_lenSymm"),
                                          self.proof("CitedFixture.holds_lenSymm_drawn")],
             "construction_rules": ["Postulate2"]},
        ])

    def test_no_law_no_field(self):
        self.assertNotIn("cited_laws", self.entries["I.4"])

    def test_law_without_a_proof_fails(self):
        # I.5 names Metric 3's law, and proves it only through I.2, an entry. The other
        # tests read the facts setUpClass loaded, so this run changes none of them.
        result = self.certificate(
            "namespace BookI\n"
            "open Superposition in\n"
            "theorem Prop5 : Cited.lenSymm.Holds primitives ∧ True :=\n"
            "  ⟨Prop2 _ (by simp [Prop2.cites]), trivial⟩\n"
            "end BookI"
        )
        output = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, output)
        self.assertIn(
            "I.5: its own Lean names the law Elements.Superposition.Cited.lenSymm, but no "
            "theorem stating exactly `Cited.Holds primitives "
            "Elements.Superposition.Cited.lenSymm` is reached from it without passing "
            "through another entry",
            output,
        )


class ExpectationTests(unittest.TestCase):
    """check_fidelity.py's reading of tests/certificate_expectations.json, on small facts,
    without Lean (#150, question 4): a cited law's construction rules, read by its `law`; a
    field of facts.json's top level, read with no `ref`; a field of every entry, read with
    `"every": "entry"`, a shared step by its `name` (#429); an entry's `proved_rules`, read
    by its `ref` apart from the top level's (#168); an entry's states, read with `one_of`,
    of which exactly one must hold (#517): I.4 by Metric 9 or by Common Notion 4 for
    figures, each passing, and a tree between them failing once, naming both states, as
    do states that hold together; and each expectation that is malformed, unmet or asks
    nothing, failing with its own message, a malformed `one_of` among them."""

    def facts(self, **i4):
        return {
            "construction_rules": ["Postulate1", "Tacit.circles_meet"],
            "propositions": [
                dict({"ref": "I.4", "axioms": ["Tacit.len_symm"], "cited_laws": [
                    {"law": "lenSymm", "proofs": [], "construction_rules": []}]}, **i4),
                {"ref": "I.8", "axioms": ["Postulate1"], "cited_laws": [
                    {"law": "lenSymm", "proofs": [], "construction_rules": []},
                    {"law": "prop7", "proofs": [], "construction_rules": ["Postulate1"]}]},
            ],
        }

    def problems(self, *expectations, facts=None, top=True):
        """The problems check_expectations finds in `expectations`, each given a `why`
        unless it has one, against `facts` (and its top level unless `top` is False)."""
        facts = facts or self.facts()
        by_ref = {p["ref"]: (None, p) for p in facts["propositions"]}
        errors = []
        with tempfile.TemporaryDirectory() as tmp, \
                patch.object(check_fidelity, "errors", errors):
            path = Path(tmp) / "expectations.json"
            path.write_text(json.dumps({"expectations": [
                x if "why" in x else dict(x, why="for the test") for x in expectations]}))
            check_fidelity.check_expectations(by_ref, path, facts if top else None)
        return errors

    def assertFailsOnce(self, expectation, message, **kwargs):
        errors = self.problems(expectation, **kwargs)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn(message, errors[0])

    def test_kept_expectations_pass(self):
        self.assertEqual(self.problems(
            {"ref": "I.8", "field": "cited_laws", "includes": ["lenSymm", "prop7"],
             "count": {"prefix": "", "is": 2}},
            {"ref": "I.4", "field": "cited_laws", "excludes": ["prop7"]},
            {"ref": "I.8", "field": "cited_laws", "law": "prop7", "includes": ["Postulate1"]},
            {"ref": "I.4", "field": "cited_laws", "law": "lenSymm", "excludes": [],
             "equals": []},
            {"ref": "I.4", "field": "cited_laws", "law": "lenSymm", "includes": [],
             "count": {"prefix": "", "is": 0}},
            {"field": "construction_rules", "includes": ["Postulate1"],
             "excludes": ["Postulate4"]},
        ), [])

    def test_a_cited_law_is_read_by_its_law(self):
        self.assertFailsOnce(
            {"ref": "I.8", "field": "cited_laws", "law": "prop7", "equals": []},
            "I.8: its construction_rules for the cited law prop7 is ['Postulate1'], not []")
        self.assertFailsOnce(
            {"ref": "I.4", "field": "cited_laws", "includes": ["prop7"]},
            "I.4: its cited_laws should include prop7")
        self.assertFailsOnce(
            {"ref": "I.4", "field": "cited_laws", "law": "lenSymm", "includes": ["Postulate1"]},
            "I.4: its construction_rules for the cited law lenSymm should include Postulate1")

    def test_a_law_not_cited_once_fails(self):
        missing = {"ref": "I.4", "field": "cited_laws", "law": "prop7", "equals": []}
        self.assertFailsOnce(missing, "I.4: pinned by")
        self.assertFailsOnce(missing, "but its cited_laws has no law prop7 with "
                                      "construction_rules")
        twice = [{"law": "lenSymm", "proofs": [], "construction_rules": []}] * 2
        self.assertFailsOnce({"ref": "I.4", "field": "cited_laws", "law": "lenSymm",
                              "equals": []},
                             "has no law lenSymm with construction_rules",
                             facts=self.facts(cited_laws=twice))
        self.assertFailsOnce({"ref": "I.4", "field": "axioms", "law": "lenSymm", "equals": []},
                             "but its axioms has no law lenSymm with construction_rules")

    def test_a_law_needs_a_ref(self):
        self.assertFailsOnce({"field": "construction_rules", "law": "lenSymm", "equals": []},
                             "a `ref` unless it reads the top level of facts.json (and always "
                             "with a `law`)")

    def test_the_top_level_is_read_without_a_ref(self):
        self.assertFailsOnce({"field": "construction_rules", "includes": ["Postulate4"]},
                             "facts.json: its construction_rules should include Postulate4")
        self.assertFailsOnce({"field": "construction_rules", "excludes": ["Postulate1"]},
                             "facts.json: its construction_rules should not include Postulate1")
        self.assertFailsOnce({"field": "proved_rules", "excludes": ["Postulate1"]},
                             "facts.json: pinned by")
        self.assertFailsOnce({"field": "proved_rules", "excludes": ["Postulate1"]},
                             "but its top level has no field `proved_rules`")
        self.assertFailsOnce({"field": "construction_rules", "includes": ["Postulate1"]},
                             "reads the top level of facts.json, which was not given",
                             top=False)

    def test_a_missing_field_or_entry_fails(self):
        self.assertFailsOnce({"ref": "I.4", "field": "shared_steps", "excludes": ["x"]},
                             "I.4: pinned by")
        self.assertFailsOnce({"ref": "I.4", "field": "shared_steps", "excludes": ["x"]},
                             "but its entry has no field `shared_steps`")
        self.assertFailsOnce({"ref": "I.9", "field": "axioms", "excludes": ["x"]},
                             "I.9: pinned by")

    def test_an_expectation_that_asks_nothing_fails(self):
        # Before #150's review this passed: an expectation with none of the four asked
        # nothing, and so could never fail.
        for expectation in ({"ref": "I.4", "field": "axioms"},
                            {"ref": "I.4", "field": "axioms", "includes": []},
                            {"ref": "I.4", "field": "axioms", "excludes": []},
                            {"ref": "I.4", "field": "axioms", "includes": [],
                             "excludes": []},
                            {"ref": "I.4", "field": "cited_laws", "law": "lenSymm"},
                            {"field": "construction_rules"}):
            with self.subTest(expectation=expectation):
                self.assertFailsOnce(expectation, "and an effective predicate: nonempty "
                                                  "`includes` or `excludes`, or present "
                                                  "`equals` or `count`")

    def test_a_malformed_expectation_fails(self):
        for expectation in ({"ref": "I.4", "field": "axioms", "includes": [], "why": None,
                             "extra": 1},
                            {"ref": "I.4", "includes": ["Tacit.len_symm"]}):
            with self.subTest(expectation=expectation):
                self.assertFailsOnce(expectation, "needs `field` and `why`")

    def test_a_malformed_predicate_fails(self):
        # A string `excludes` was read letter by letter, and so could never fail.
        for expectation in ({"ref": "I.4", "field": "axioms", "excludes": "Tacit.len_symm"},
                            {"ref": "I.4", "field": "axioms", "includes": [1]},
                            {"ref": "I.4", "field": "axioms", "count": 1},
                            {"ref": "I.4", "field": "axioms", "count": {"is": "1"}},
                            {"ref": "I.4", "field": "axioms",
                             "count": {"pefix": "Tacit.", "is": 1}},
                            {"ref": "I.4", "field": "axioms",
                             "count": {"prefix": 1, "is": 1}}):
            with self.subTest(expectation=expectation):
                self.assertFailsOnce(expectation, "`includes` and `excludes` must be lists of "
                                                  "names, and `count` an object with an "
                                                  "integer `is`")

    def test_a_field_with_no_names_cannot_be_read_by_name(self):
        # Before #150's review these passed: `shared_steps` was read as its objects' missing
        # `law`s, and a scalar as no names, so an `excludes` on either could never fail.
        steps = [{"name": "Prop1.perpendicular", "brings_in": ["I.1"], "file": "f", "line": 1}]
        facts = self.facts(shared_steps=steps, statement="If two triangles …",
                           mixed=["Tacit.len_symm", {"law": "lenSymm"}])
        for expectation in ({"ref": "I.4", "field": "shared_steps",
                             "excludes": ["Prop1.perpendicular"]},
                            {"ref": "I.4", "field": "shared_steps",
                             "includes": ["Prop1.perpendicular"]},
                            {"ref": "I.4", "field": "statement", "excludes": ["If"]},
                            {"ref": "I.4", "field": "statement",
                             "count": {"prefix": "", "is": 0}},
                            {"ref": "I.4", "field": "mixed", "excludes": ["Tacit.len_symm"]}):
            with self.subTest(expectation=expectation):
                self.assertFailsOnce(expectation, "is not a list of names, an object or "
                                                  "cited_laws, so `includes`, `excludes` and "
                                                  "`count` cannot read it", facts=facts)
        self.assertFailsOnce({"ref": "I.4", "field": "statement", "excludes": [],
                              "equals": "If two triangles"},
                             "I.4: its statement is 'If two triangles …', not 'If two "
                             "triangles'", facts=facts)
        self.assertEqual(self.problems(
            {"ref": "I.4", "field": "shared_steps", "equals": steps},
            {"ref": "I.4", "field": "statement", "excludes": [],
             "equals": "If two triangles …"},
            {"ref": "I.4", "field": "inherited", "includes": ["Postulate3"],
             "excludes": ["Postulate1"], "count": {"prefix": "Post", "is": 1}},
            facts=self.facts(shared_steps=steps, statement="If two triangles …",
                             inherited={"Postulate3": steps})), [])

    def test_a_malformed_cited_law_fails(self):
        for cited in ([{"name": "lenSymm", "proofs": [], "construction_rules": []}],
                      [{"law": None, "proofs": [], "construction_rules": []}],
                      [{"law": "", "proofs": [], "construction_rules": []}],
                      ["lenSymm"],
                      {"lenSymm": []}):
            facts = self.facts(cited_laws=cited)
            for expectation in ({"ref": "I.4", "field": "cited_laws", "excludes": ["prop7"]},
                                {"ref": "I.4", "field": "cited_laws",
                                 "count": {"prefix": "", "is": 1}}):
                with self.subTest(cited=cited, expectation=expectation):
                    self.assertFailsOnce(expectation, "I.4: pinned by", facts=facts)
                    self.assertFailsOnce(expectation, "but its cited_laws is not a list of "
                                                      "objects each with a `law` name",
                                         facts=facts)
        beside = [{"law": "lenSymm", "proofs": [], "construction_rules": []},
                  {"proofs": [], "construction_rules": ["Postulate1"]}]
        self.assertFailsOnce({"ref": "I.4", "field": "cited_laws", "law": "lenSymm",
                              "equals": []},
                             "but its cited_laws is not a list of objects each with a `law` "
                             "name", facts=self.facts(cited_laws=beside))

    STEP = {"name": "Tacit.outside_of_between", "brings_in": ["III.2"], "file": "f", "line": 1}
    PIN = {"every": "entry", "field": "shared_steps", "excludes": ["Tacit.outside_of_between"]}

    def test_every_entry_is_read(self):
        # #429: no entry may list Circle 3 among its shared steps. The pin reads every
        # entry, and a shared step by its `name`.
        facts = self.facts(shared_steps=[self.STEP])
        facts["propositions"][1]["shared_steps"] = []
        self.assertFailsOnce(self.PIN, "I.4: its shared_steps should not include "
                                       "Tacit.outside_of_between", facts=facts)
        self.assertEqual(self.problems(
            dict(self.PIN, excludes=["Tacit.inside_of_between"]),
            {"every": "entry", "field": "axioms", "excludes": ["Postulate4"]},
            facts=facts), [])
        self.assertFailsOnce({"every": "entry", "field": "axioms", "excludes": ["Postulate1"]},
                             "I.8: its axioms should not include Postulate1", facts=facts)
        facts["propositions"][1]["shared_steps"] = [self.STEP]
        errors = self.problems(self.PIN, facts=facts)
        self.assertEqual(len(errors), 2, errors)
        for ref, error in zip(("I.4", "I.8"), errors):
            self.assertIn(f"{ref}: its shared_steps should not include", error)

    def test_every_entry_must_be_readable(self):
        # Read as empty, an entry with no field, or a step with no name, would let the pin
        # pass; and so would no entries at all.
        self.assertFailsOnce(self.PIN, "but its entry has no field `shared_steps`",
                             facts=self.facts(shared_steps=[]))
        nameless, mixed = [dict(self.STEP, name=None)], [self.STEP, "Tacit.inside_of_between"]
        for facts in (self.facts(shared_steps=nameless), self.facts(shared_steps=mixed)):
            facts["propositions"][1]["shared_steps"] = []
            with self.subTest(steps=facts["propositions"][0]["shared_steps"]):
                self.assertFailsOnce(self.PIN, "I.4: its shared_steps is not a list of names, "
                                               "an object or a list of objects each with a "
                                               "`name`", facts=facts)
        errors = self.problems(dict(self.PIN, field="cited_laws"))
        self.assertEqual(len(errors), 2, errors)
        self.assertTrue(all("is not a list of names" in e for e in errors), errors)
        self.assertFailsOnce(self.PIN, "reads every entry, but facts.json has none",
                             facts={"propositions": []})

    def test_a_malformed_every_fails(self):
        for expectation in (dict(self.PIN, every="entries"),
                            dict(self.PIN, every=True),
                            dict(self.PIN, ref="I.4"),
                            dict(self.PIN, includes=["Tacit.inside_of_between"]),
                            dict(self.PIN, equals=[]),
                            dict(self.PIN, count={"is": 0})):
            with self.subTest(expectation=expectation):
                self.assertFailsOnce(expectation, "an expectation over every entry is "
                                                  "`\"every\": \"entry\"`")
        self.assertFailsOnce(dict(self.PIN, excludes=[]), "and an effective predicate")
        self.assertFailsOnce(dict(self.PIN, law="lenSymm"), "needs `field` and `why`")

    def test_an_entrys_proved_rules_are_read_apart_from_the_top_levels(self):
        # #168: an entry's proved_rules, a list of names, is read by its `ref` or over
        # every entry; the top level's, an object, by its keys, the rules themselves.
        facts = self.facts(proved_rules=["Tacit.adjacent_eq_of_right"])
        facts["propositions"][1]["proved_rules"] = []
        facts["proved_rules"] = {"Tacit.adjacent_eq_of_right": ["Postulate1"],
                                 "Tacit.centre_unique": ["Postulate3"]}
        used = ["Tacit.adjacent_eq_of_right"]
        for expectation in ({"ref": "I.4", "field": "proved_rules", "excludes": used},
                            {"every": "entry", "field": "proved_rules", "excludes": used}):
            with self.subTest(expectation=expectation):
                self.assertFailsOnce(expectation, "I.4: its proved_rules should not include "
                                                  "Tacit.adjacent_eq_of_right", facts=facts)
        self.assertEqual(self.problems(
            {"ref": "I.4", "field": "proved_rules", "excludes": ["Tacit.centre_unique"],
             "equals": used},
            {"ref": "I.8", "field": "proved_rules", "excludes": used,
             "count": {"prefix": "Tacit.", "is": 0}},
            {"field": "proved_rules", "includes": ["Tacit.centre_unique"]},
            {"every": "entry", "field": "proved_rules", "excludes": ["Tacit.centre_unique"]},
            facts=facts), [])
        # Read as empty, an entry without the field would let every `excludes` pass.
        self.assertFailsOnce({"ref": "I.4", "field": "proved_rules", "excludes": used},
                             "but its entry has no field `proved_rules`")

    # #517: I.4 in one of two states, as tests/certificate_expectations.json holds it: its
    # area clause by Metric 9, through its law, or by Common Notion 4 for figures, and
    # nothing between.
    METRIC_9 = {"state": "Metric 9", "expectations": [
        {"ref": "I.4", "field": "cited_laws", "includes": ["lenSymm", "areaCongruent"],
         "count": {"prefix": "", "is": 2}, "why": "the seven laws"},
        {"ref": "I.4", "field": "cited_laws", "law": "areaCongruent", "equals": [],
         "why": "Metric 9's law"},
        {"ref": "I.4", "field": "own_axioms", "excludes": ["Tacit.figures_coincide"],
         "why": "not the new axiom"}]}
    CN_4 = {"state": "Common Notion 4 for figures", "expectations": [
        {"ref": "I.4", "field": "cited_laws", "includes": ["lenSymm"],
         "count": {"prefix": "", "is": 1}, "why": "the six laws"},
        {"ref": "I.4", "field": "own_axioms", "includes": ["Tacit.figures_coincide"],
         "why": "the new axiom"}]}
    STATES = {"ref": "I.4", "one_of": [METRIC_9, CN_4]}
    LEN_SYMM = {"law": "lenSymm", "proofs": [], "construction_rules": []}
    AREA = {"law": "areaCongruent", "proofs": [], "construction_rules": []}

    def i4(self, laws, own):
        return self.facts(cited_laws=laws, own_axioms=own)

    def test_one_state_of_two_holds(self):
        for name, facts in (("Metric 9", self.i4([self.LEN_SYMM, self.AREA], ["Postulate1"])),
                            ("Common Notion 4 for figures",
                             self.i4([self.LEN_SYMM], ["Postulate1", "Tacit.figures_coincide"]))):
            with self.subTest(state=name):
                self.assertEqual(self.problems(self.STATES, facts=facts), [])

    def test_a_tree_between_the_states_fails_once_naming_each(self):
        # The new axiom with the seven laws, or the six laws without it: in neither state.
        for between, facts, sunk in (
                ("the new axiom with Metric 9's law",
                 self.i4([self.LEN_SYMM, self.AREA], ["Tacit.figures_coincide"]),
                 ("its own_axioms should not include Tacit.figures_coincide",
                  "its cited_laws has 2 names beginning '', not 1")),
                ("neither", self.i4([self.LEN_SYMM], ["Postulate1"]),
                 ("its cited_laws should include areaCongruent",
                  "its cited_laws has no law areaCongruent with construction_rules",
                  "its own_axioms should include Tacit.figures_coincide"))):
            with self.subTest(between=between):
                errors = self.problems(self.STATES, facts=facts)
                self.assertEqual(len(errors), 1, errors)
                self.assertTrue(errors[0].startswith("I.4: "), errors[0])
                self.assertIn("expectations.json, expectation 1 asks that exactly one of its "
                              "states hold, and none does (for the test) The state ", errors[0])
                metric, cn = (errors[0].index('The state "Metric 9" fails: '),
                              errors[0].index('The state "Common Notion 4 for figures" fails: '))
                self.assertLess(metric, cn)
                for message in sunk:
                    self.assertIn(message, errors[0])
                # Each failure stands under the state it sank, with its own label.
                self.assertIn('expectation 1, state "Metric 9", expectation ', errors[0][:cn])
                self.assertIn('expectation 1, state "Common Notion 4 for figures", expectation ',
                              errors[0][cn:])

    def test_states_that_hold_together_fail(self):
        both = {"ref": "I.4", "one_of": [
            {"state": "one", "expectations": [
                {"ref": "I.4", "field": "cited_laws", "includes": ["lenSymm"], "why": "a"}]},
            {"state": "two", "expectations": [
                {"ref": "I.4", "field": "axioms", "includes": ["Tacit.len_symm"], "why": "b"}]},
            {"state": "three", "expectations": [
                {"ref": "I.4", "field": "axioms", "includes": ["Postulate5"], "why": "c"}]}]}
        self.assertFailsOnce(both, 'expectations.json, expectation 1 asks that exactly one of '
                                   'its states hold, but "one" and "two" hold at once, so the '
                                   'states are not exclusive (for the test)')
        self.assertTrue(self.problems(both)[0].startswith("I.4: "))

    def test_a_malformed_choice_of_states_fails(self):
        inner = self.CN_4["expectations"][1]
        def states(*one_of):
            return {"ref": "I.4", "one_of": list(one_of)}
        for shape, expectation, message in (
                ("one state", states(self.CN_4),
                 "expectation 1: its `one_of` must be a list of two states or more"),
                ("no list", dict(self.STATES, one_of={"Metric 9": self.METRIC_9}),
                 "expectation 1: its `one_of` must be a list of two states or more"),
                ("an empty state", states(self.METRIC_9, dict(self.CN_4, expectations=[])),
                 'expectation 1, state "Common Notion 4 for figures": its `expectations` must '
                 "be a nonempty list"),
                ("a nested one_of", states(self.METRIC_9, dict(self.CN_4, expectations=[
                    dict(self.STATES, why="nested")])),
                 'state "Common Notion 4 for figures", expectation 1: a state\'s expectations '
                 "are ordinary ones of its entry, with no `one_of` or `every`"),
                ("an inner every", states(self.METRIC_9, dict(self.CN_4, expectations=[
                    {"every": "entry", "field": "axioms", "excludes": ["Postulate5"],
                     "why": "every"}])),
                 'state "Common Notion 4 for figures", expectation 1: a state\'s expectations '
                 "are ordinary ones of its entry, with no `one_of` or `every`"),
                ("an inner ref that differs", states(self.METRIC_9, dict(self.CN_4, expectations=[
                    dict(inner, ref="I.8")])),
                 'state "Common Notion 4 for figures", expectation 1: its `ref` must be I.4, '
                 "the `ref` of the expectation with `one_of`"),
                ("an inner expectation with no ref", states(self.METRIC_9, dict(
                    self.CN_4, expectations=[{k: v for k, v in inner.items() if k != "ref"}])),
                 'state "Common Notion 4 for figures", expectation 1: its `ref` must be I.4'),
                ("an inner expectation with no why", states(self.METRIC_9, dict(
                    self.CN_4, expectations=[{k: v for k, v in inner.items() if k != "why"}])),
                 'state "Common Notion 4 for figures", expectation 1: needs `field` and `why`'),
                ("an unknown key outside", dict(self.STATES, field="cited_laws"),
                 "expectation 1: an expectation with `one_of` has a `ref`, the name of an "
                 "entry, `one_of`, its states, and a `why`, and nothing else"),
                ("no ref", {"one_of": [self.METRIC_9, self.CN_4]},
                 "expectation 1: an expectation with `one_of` has a `ref`"),
                ("an unknown key in a state", states(self.METRIC_9, dict(self.CN_4, why="w")),
                 "expectation 1, state 2: a state is an object with a `state`, its name, and "
                 "`expectations`, and nothing else"),
                ("an unknown key inside", states(self.METRIC_9, dict(self.CN_4, expectations=[
                    dict(inner, extra=1)])),
                 'state "Common Notion 4 for figures", expectation 1: needs `field` and `why`'),
                ("a state with no name", states(
                    self.METRIC_9, {"state": "", "expectations": self.CN_4["expectations"]}),
                 "expectation 1, state 2: its `state` must name it, with a nonempty string"),
                ("a state named by no string", states(
                    self.METRIC_9, {"state": 2, "expectations": self.CN_4["expectations"]}),
                 "expectation 1, state 2: its `state` must name it, with a nonempty string"),
                ("duplicate names", states(self.METRIC_9, dict(self.CN_4, state="Metric 9")),
                 'expectation 1: two of its states are named "Metric 9": each state needs a '
                 "name of its own")):
            with self.subTest(shape=shape):
                # Malformed, it fails by its shape alone, in a tree that holds a state.
                self.assertFailsOnce(expectation, message, facts=self.i4(
                    [self.LEN_SYMM, self.AREA], ["Postulate1"]))


class SharedStepTests(unittest.TestCase):
    """A proved tacit rule among an entry's shared steps, on a fixture written here
    (#429): the expectation over every entry's `shared_steps` can see a rule only where
    the walk lists it. A rule the entry's own Lean calls is listed, bringing in the
    proposition it is proved from, as Circle 2 brings in III.2; one it calls only through
    a lemma outside its namespace is not, and that lemma is listed instead."""

    @classmethod
    def setUpClass(cls):
        with tempfile.TemporaryDirectory(prefix="stoicheia-steps-") as tmp:
            work = Path(tmp)
            env, fixture_modules = prepare_package(work)
            (work / "Elements.lean").write_text(
                "import Elements.Foundations.CommonNotions\n"
                "namespace Elements\n"
                "def companions : List (Lean.Name × String) := []\n"
                "theorem BookIII.Prop2 (a : Length) : a + 0 = a := Tacit.add_zero a\n"
                "theorem Tacit.rule (a : Length) : a + 0 = a := BookIII.Prop2 a\n"
                "theorem CertificateFixture.via (a : Length) : a + 0 = a := Tacit.rule a\n"
                "theorem BookIII.Prop3 (a : Length) : a + 0 = a := Tacit.rule a\n"
                "theorem BookIII.Prop4 (a : Length) : a + 0 = a := CertificateFixture.via a\n"
                "end Elements\n"
            )
            compile_module(work, env, fixture_modules, "Elements")
            certificate_result = subprocess.run(
                ["lake", "env", "lean", "Facts.lean"],
                cwd=work, env=env, capture_output=True, text=True, timeout=120,
            )
            if certificate_result.returncode:
                raise AssertionError(
                    f"certificate: lake env lean exited {certificate_result.returncode}\n"
                    + certificate_result.stdout + certificate_result.stderr
                )
            facts = json.loads((work / "facts.json").read_text())
        cls.steps = {entry["ref"]: {step["name"]: step["brings_in"]
                                    for step in entry["shared_steps"]}
                     for entry in facts["propositions"]}
        if set(cls.steps) != {"III.2", "III.3", "III.4"}:
            raise AssertionError(f"unexpected fixture subjects: {sorted(cls.steps)}")

    def test_a_rule_called_directly_is_listed(self):
        self.assertEqual(self.steps["III.3"], {"Tacit.rule": ["III.2"]})

    def test_a_rule_called_through_a_lemma_is_not(self):
        self.assertEqual(self.steps["III.4"], {"CertificateFixture.via": ["III.2"]})


PROVED_RULES_FIXTURE = """\
import Elements.Foundations.Tacit.Magnitudes

namespace Elements

def companions : List (Lean.Name × String) := []

/- Stand-ins for retired rules: theorems in `Elements.Tacit`, the second proved from the
first. No axiom is declared here. -/
theorem Tacit.first_proved (a b : Length) : a + b = b + a := Tacit.add_comm a b
theorem Tacit.second_proved (a b : Length) : a + b = b + a := Tacit.first_proved a b

theorem CertificateFixture.swap (a b : Length) : a + b = b + a := Tacit.first_proved a b

/- Stand-ins for the Common Notions, under their names, which the certificate knows them
by; so this fixture imports the tacit rules of magnitudes rather than the foundations'
Common Notions. The second is proved from the first rule. -/
theorem CommonNotion1 : True := trivial
theorem CommonNotion2 (a b : Length) : a + b = b + a := Tacit.first_proved a b
theorem CommonNotion3 : True := trivial
theorem CommonNotion4 : True := trivial
theorem CommonNotion4.angle : True := trivial
theorem CommonNotion4.triangle : True := trivial
theorem CommonNotion5 : True := trivial

namespace BookI

variable (a b : Length)

theorem Prop1 : a + b = b + a := Tacit.add_comm a b
theorem Prop2 : a + b = b + a := Tacit.first_proved a b
theorem Prop3.step : a + b = b + a := Tacit.first_proved a b
theorem Prop3 : a + b = b + a := Prop3.step a b
theorem Prop4 : a + b = b + a := CertificateFixture.swap a b
theorem Prop5 : a + b = b + a := Prop2 a b
theorem Prop6 : (fun _ => True) @Tacit.first_proved := True.intro
theorem Prop7 : a + b = b + a := Tacit.second_proved a b
theorem Prop8 : a + b = b + a := CommonNotion2 a b

end BookI
end Elements
"""

# The line of `beneath` that goes on into what a declaration mentions, and the same line
# stopped at each proved rule, as a walk that lost the rules' axioms would be.
BENEATH_GOES_ON = ("      if rules.contains d then found := { found with rules := "
                   "found.rules.insert d }\n"
                   "      unless seen.contains d do todo := todo.push d\n")
BENEATH_STOPS = BENEATH_GOES_ON.replace("unless seen.contains d do",
                                        "unless seen.contains d || rules.contains d do")


class ProvedRulesTests(unittest.TestCase):
    """Each entry's `proved_rules`, on a fixture written here (#168): two stand-in proved
    rules, the second proved from the first, reached in every way the walk must follow;
    and the run's check of that walk against Lean, on a copy of the certificate whose walk
    stops at each proved rule."""

    @classmethod
    def setUpClass(cls):
        with tempfile.TemporaryDirectory(prefix="stoicheia-proved-") as tmp:
            work = Path(tmp)
            env, fixture_modules = prepare_package(work)
            (work / "Elements.lean").write_text(PROVED_RULES_FIXTURE)
            compile_module(work, env, fixture_modules, "Elements")
            result = subprocess.run(
                ["lake", "env", "lean", "Facts.lean"],
                cwd=work, env=env, capture_output=True, text=True, timeout=120,
            )
            if result.returncode:
                raise AssertionError(
                    f"certificate: lake env lean exited {result.returncode}\n"
                    + result.stdout + result.stderr
                )
            cls.facts = json.loads((work / "facts.json").read_text())
            source = (work / "Facts.lean").read_text()
            if source.count(BENEATH_GOES_ON) != 1:
                raise AssertionError("Certificate/Facts.lean: expected the walk `beneath` to "
                                     "go on from each mention once; update this test")
            (work / "Facts.lean").write_text(source.replace(BENEATH_GOES_ON, BENEATH_STOPS))
            cls.stopped = subprocess.run(
                ["lake", "env", "lean", "Facts.lean"],
                cwd=work, env=env, capture_output=True, text=True, timeout=120,
            )
        cls.entries = {entry["ref"]: entry for entry in cls.facts["propositions"]}
        if set(cls.entries) != {f"I.{i}" for i in range(1, 9)}:
            raise AssertionError(f"unexpected fixture subjects: {sorted(cls.entries)}")

    def test_the_rules_are_listed_with_their_axioms(self):
        self.assertEqual(self.facts["proved_rules"], {
            "Tacit.first_proved": ["Tacit.add_comm"],
            "Tacit.second_proved": ["Tacit.add_comm"],
        })

    def test_an_entry_reaching_no_rule_lists_none(self):
        self.assertEqual(self.entries["I.1"]["proved_rules"], [])
        self.assertEqual(self.entries["I.1"]["axioms"], ["Tacit.add_comm"])

    def test_every_way_to_a_rule_counts(self):
        for ref, way in (("I.2", "directly"), ("I.3", "through its own helper"),
                         ("I.4", "through a lemma"), ("I.5", "through I.2, which it cites"),
                         ("I.6", "through its statement alone"),
                         ("I.8", "through a Common Notion")):
            with self.subTest(ref=ref, way=way):
                self.assertEqual(self.entries[ref]["proved_rules"], ["Tacit.first_proved"])
                self.assertEqual(self.entries[ref]["axioms"], ["Tacit.add_comm"])
        self.assertEqual(self.entries["I.5"]["cites"], ["I.2"])
        self.assertEqual(self.entries["I.8"]["cites"], [])
        self.assertEqual(self.entries["I.8"]["common_notions"], ["C.N. 2"])

    def test_a_rule_proved_from_another_brings_in_both(self):
        self.assertEqual(self.entries["I.7"]["proved_rules"],
                         ["Tacit.first_proved", "Tacit.second_proved"])

    def test_a_walk_that_stops_at_a_rule_fails_the_run(self):
        # The run's check of `beneath` against collectAxioms (#168): stopped at each proved
        # rule, the walk misses the axioms beneath it, and the run fails, naming each entry
        # that rests on a rule, and no other.
        output = self.stopped.stdout + self.stopped.stderr
        self.assertEqual(self.stopped.returncode, 1, output)
        message = "the walk for its proved rules does not find Lean's axioms"
        for ref in sorted(self.entries):
            with self.subTest(ref=ref):
                if ref == "I.1":
                    self.assertNotIn(f"{ref}: {message}", output)
                else:
                    self.assertIn(f"{ref}: {message}", output)


if __name__ == "__main__":
    unittest.main(verbosity=2)
