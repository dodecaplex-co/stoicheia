#!/usr/bin/env python3
"""Restoration regressions for scripts/negative_tests.py, and without Git outside
temporary repositories.

    python3 -I tests/test_negative_tests.py

The negative suite runs these first without Lean. Temporary files stand in for Lake
outputs; simulated builds delete, replace and create them before failing or being
interrupted. A temporary repository stands in for the pre-flight's pass with origin/main's
checks, whose work tree lacks the files a commit adds under the check inputs while Git's
index still lists them.
"""

import io
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))
import negative_tests as negative  # noqa: E402


class RestorationTests(unittest.TestCase):
    def setUp(self):
        tmp = self.enterContext(tempfile.TemporaryDirectory())
        self.root = Path(tmp)
        self.build = self.root / ".lake/build"
        self.planted = self.root / "Elements/Foundations/Tacit/Planted.lean"
        self.planted.parent.mkdir(parents=True)
        self.enterContext(patch.multiple(negative, ROOT=self.root, PLANTED=self.planted,
                                        failures=[]))
        self.output = self.enterContext(redirect_stdout(io.StringIO()))

    def write(self, path, data):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)

    def files(self):
        return {p.relative_to(self.build): p.read_bytes()
                for p in self.build.rglob("*") if p.is_file()}

    def outputs(self, module):
        for kind, suffixes in (
                ("lib/lean", ("olean", "ilean", "trace", "olean.hash", "ilean.hash",
                              "olean.private")),
                ("ir", ("c", "c.hash", "setup.json")),
                ("native", ("c.o", "c.o.hash"))):
            for suffix in suffixes:
                self.write(self.build / kind / f"{module}.{suffix}",
                           b"olean\x00original " + suffix.encode())

    def damage_outputs(self):
        for path in self.build.rglob("*"):
            if path.is_file():
                if path.suffix in (".olean", ".ilean", ".c"):
                    path.unlink()
                else:
                    path.write_bytes(b"incomplete")
        self.write(self.build / "ir/New/Dependent.c", b"new output")

    def failed_rebuild(self, interrupt):
        self.damage_outputs()
        if interrupt:
            raise KeyboardInterrupt("restoration build interrupted")
        return subprocess.CompletedProcess([], 1, "", "restoration build failed")

    def test_snapshot_removes_outputs_when_build_tree_was_absent(self):
        saved = negative.BuildOutputs()
        self.outputs("Elements/BookI/Prop01")
        saved.restore()
        self.assertEqual(self.files(), {})

    def test_temporary_module_snapshot_keeps_neighbours(self):
        self.outputs("Elements/Foundations/Tacit/Planted")
        saved = self.files()
        snapshot = negative.BuildOutputs("**/Elements/Foundations/Tacit/Planted.*")
        self.damage_outputs()
        self.outputs("Elements/Foundations/Tacit/PlantedMore")
        self.outputs("Other/Planted")
        neighbours = {p: data for p, data in self.files().items() if p not in saved}
        snapshot.restore()
        self.assertEqual(self.files(), saved | neighbours)

    def test_successful_rebuild_keeps_new_outputs_and_replays(self):
        self.outputs("Elements/BookI/Prop01")
        path = self.build / "lib/lean/Elements/BookI/Prop01.olean"
        calls = []
        def run(*cmd):
            calls.append(cmd)
            if len(calls) == 1:
                self.assertTrue(path.read_bytes().startswith(b"broken"))
                return subprocess.CompletedProcess(cmd, 1, "", "failed to read file "
                    "Elements/BookI/Prop01.olean: invalid header")
            if cmd == ("lake", "build"):
                self.assertFalse(path.exists(), "restoration must force the rebuild")
                self.write(path, b"olean rebuilt")
            else:
                self.assertEqual(cmd, calls[0], "the restored environment must be replayed")
                self.assertEqual(path.read_bytes(), b"olean rebuilt")
            return subprocess.CompletedProcess(cmd, 0, "", "")
        with patch.object(negative, "run", side_effect=run), \
                patch.object(negative.check_kernel, "toolchain_bin",
                             return_value=Path("toolchain")):
            negative.corrupt_olean()
        self.assertEqual(len(calls), 3)
        self.assertEqual(path.read_bytes(), b"olean rebuilt")
        self.assertEqual(negative.failures, [])

    def test_corrupt_olean_restores_all_outputs(self):
        for interrupt in (False, True):
            with self.subTest(interrupt=interrupt):
                self.outputs("Elements/BookI/Prop01")
                self.outputs("Elements/BookI/Prop02")
                saved = self.files()
                def run(*cmd):
                    if cmd == ("lake", "build"):
                        return self.failed_rebuild(interrupt)
                    return subprocess.CompletedProcess(cmd, 1, "", "failed to read file "
                        "Elements/BookI/Prop01.olean: invalid header")
                with patch.object(negative, "run", side_effect=run) as commands, \
                        patch.object(negative.check_kernel, "toolchain_bin",
                                     return_value=Path("toolchain")):
                    if interrupt:
                        with self.assertRaises(KeyboardInterrupt):
                            negative.corrupt_olean()
                    else:
                        negative.corrupt_olean()
                        self.assertIn("the restored Elements build: exit 1", negative.failures)
                self.assertEqual(commands.call_count, 2)
                self.assertEqual(self.files(), saved)

    def ill_typed_commands(self, replay, rebuild):
        """Stand-ins for the ill-typed plant's commands: the compile must read a copy of I.1
        outside the tree, with the plant, and write I.1's `.olean`; `replay` answers
        leanchecker and `rebuild` the restoration build."""
        source = self.root / "Elements/BookI/Prop01.lean"
        self.write(source, b"import Elements.Figure.Basics\n")
        path = self.build / "lib/lean/Elements/BookI/Prop01.olean"
        def run(*cmd):
            if cmd[:3] == ("lake", "env", "lean"):
                copy = Path(cmd[-1])
                self.assertFalse(copy.is_relative_to(self.root), "the copy must be outside")
                self.assertEqual(copy, Path(cmd[cmd.index("-R") + 1])
                                 / "Elements/BookI/Prop01.lean")
                self.assertEqual(cmd[cmd.index("-o") + 1], str(path))
                self.assertEqual(copy.read_text(), "import Lean.Elab.Command\n"
                                 + source.read_text() + negative.ILL_TYPED_LEAN)
                self.write(path, b"olean planted")
                return subprocess.CompletedProcess(cmd, 0, "", "")
            if cmd == ("lake", "build"):
                return rebuild(cmd)
            self.assertEqual(cmd, ("lake", "env", "toolchain/leanchecker", "--fresh", "Elements"))
            return replay(cmd)
        return path, run

    def test_ill_typed_proof_rejected_then_rebuilt_and_replayed(self):
        name = negative.ILL_TYPED
        for message, caught in (
                (f"while replaying declaration '{name}':\n(kernel) declaration type "
                 f"mismatch, '{name}' has type\n  True\n", True),
                ("failed to read file Elements/BookI/Prop01.olean: invalid header", False)):
            with self.subTest(caught=caught):
                negative.failures.clear()
                self.outputs("Elements/BookI/Prop01")
                replays = []
                def replay(cmd):
                    replays.append(path.read_bytes())
                    return subprocess.CompletedProcess(cmd, 1 if len(replays) == 1 else 0,
                                                       "", message)
                def rebuild(cmd):
                    self.assertFalse(path.exists(), "restoration must force the rebuild")
                    self.write(path, b"olean rebuilt")
                    return subprocess.CompletedProcess(cmd, 0, "", "")
                path, run = self.ill_typed_commands(replay, rebuild)
                with patch.object(negative, "run", side_effect=run) as commands, \
                        patch.object(negative.check_kernel, "toolchain_bin",
                                     return_value=Path("toolchain")):
                    negative.ill_typed_proof()
                self.assertEqual(commands.call_count, 4)
                self.assertEqual(replays, [b"olean planted", b"olean rebuilt"])
                if caught:
                    self.assertEqual(negative.failures, [])
                else:
                    self.assertEqual(len(negative.failures), 1)
                    self.assertIn("not caught", negative.failures[0])

    def test_ill_typed_proof_restores_all_outputs(self):
        for interrupt in (False, True):
            with self.subTest(interrupt=interrupt):
                negative.failures.clear()
                self.outputs("Elements/BookI/Prop01")
                self.outputs("Elements/BookI/Prop02")
                saved = self.files()
                path, run = self.ill_typed_commands(
                    lambda cmd: subprocess.CompletedProcess(
                        cmd, 1, "", f"while replaying declaration '{negative.ILL_TYPED}'"),
                    lambda cmd: self.failed_rebuild(interrupt))
                with patch.object(negative, "run", side_effect=run) as commands, \
                        patch.object(negative.check_kernel, "toolchain_bin",
                                     return_value=Path("toolchain")):
                    if interrupt:
                        with self.assertRaises(KeyboardInterrupt):
                            negative.ill_typed_proof()
                    else:
                        negative.ill_typed_proof()
                        self.assertIn("the Elements build restored after the ill-typed "
                                      "proof: exit 1", negative.failures)
                self.assertEqual(commands.call_count, 3)
                self.assertEqual(self.files(), saved)

    def test_missing_files_restored_byte_for_byte(self):
        rels = ("figures/I/01.svg", "figures/I/01-idea.svg", "mishnah/I/01.md")
        originals = {rel: f"<{rel}>\r\nno newline at the end".encode() for rel in rels}
        for outcome in ("caught", "not caught", "interrupted"):
            with self.subTest(outcome=outcome):
                negative.failures.clear()
                for rel, data in originals.items():
                    self.write(self.root / rel, data)
                def fidelity(*args):
                    missing = [rel for rel in rels if not (self.root / rel).exists()]
                    self.assertEqual(len(missing), 1)
                    if outcome == "interrupted":
                        raise KeyboardInterrupt("fidelity check interrupted")
                    if outcome == "not caught":
                        return subprocess.CompletedProcess([], 0, "", "")
                    return subprocess.CompletedProcess(
                        [], 1, f"✗ I.1: {missing[0]} is missing\n", "")
                with patch.object(negative, "fidelity", side_effect=fidelity) as checks:
                    if outcome == "interrupted":
                        with self.assertRaises(KeyboardInterrupt):
                            negative.missing_files()
                    else:
                        negative.missing_files()
                self.assertEqual(checks.call_count, 1 if outcome == "interrupted" else 3)
                for rel, data in originals.items():
                    self.assertEqual((self.root / rel).read_bytes(), data)
                if outcome == "caught":
                    self.assertEqual(negative.failures, [])
                elif outcome == "not caught":
                    self.assertEqual(len(negative.failures), 3)

    def test_audit_restores_all_outputs(self):
        source = self.root / "Audit/Overlaps.lean"
        for multiline, interrupt in ((False, False), (False, True),
                                     (True, False), (True, True)):
            with self.subTest(multiline=multiline, interrupt=interrupt):
                dropped = ("Elements.Tacit.outside_of_between" if multiline
                           else "Elements.Tacit.inside_of_between")
                axioms = (f"propext,\n Classical.choice,\n Quot.sound,\n {dropped}"
                          if multiline else dropped)
                original = f"'Audit.III_2' depends on axioms: [{axioms}]".encode()
                self.write(source, original)
                self.outputs("Audit/Overlaps")
                self.outputs("Audit")
                saved = self.files()
                def run(*cmd):
                    self.assertEqual(cmd, ("lake", "build", "Audit"))
                    if source.read_bytes() == original:
                        return self.failed_rebuild(interrupt)
                    self.damage_outputs()
                    return subprocess.CompletedProcess(cmd, 1, "", "Audit/Overlaps.lean: "
                        "Docstring on `#guard_msgs` does not match generated message "
                        f"Audit.III_2 {dropped}")
                with patch.object(negative, "run", side_effect=run) as commands:
                    if interrupt:
                        with self.assertRaises(KeyboardInterrupt):
                            negative.changed_audit_pin()
                    else:
                        negative.changed_audit_pin()
                        self.assertIn("the restored audit build: exit 1", negative.failures)
                self.assertEqual(commands.call_count, 2)
                self.assertEqual(source.read_bytes(), original)
                self.assertEqual(self.files(), saved)

    def test_audit_drops_one_project_axiom_and_keeps_other_pins(self):
        source = self.root / "Audit/Overlaps.lean"
        for axioms in (
                "Elements.Tacit.inside_of_between",
                "propext, Classical.choice, Quot.sound, Elements.Tacit.outside_of_between",
                "propext,\n Classical.choice,\n Elements.Postulate1,\n Quot.sound,\n "
                "Elements.Tacit.outside_of_between"):
            with self.subTest(axioms=axioms):
                names = [a.strip() for a in axioms.split(",")]
                dropped = next(a for a in names if a.startswith("Elements."))
                remaining = names.copy()
                remaining.remove(dropped)
                prefix = "/-- info: 'Audit.I_2' depends on axioms: [Elements.Postulate1] -/\n"
                suffix = "\n-/\n#guard_msgs in\n#print axioms Audit.III_2\n"
                original = (prefix + "/--\ninfo: 'Audit.III_2' depends on axioms: ["
                            + axioms + "]" + suffix).encode()
                self.write(source, original)
                calls = []
                def run(*cmd):
                    calls.append(cmd)
                    self.assertEqual(cmd, ("lake", "build", "Audit"))
                    if len(calls) == 2:
                        self.assertEqual(source.read_bytes(), original)
                        return subprocess.CompletedProcess(cmd, 0, "", "")
                    changed = source.read_text()
                    self.assertTrue(changed.startswith(prefix))
                    self.assertTrue(changed.endswith(suffix))
                    pin = re.search(r"'Audit\.III_2' depends on axioms: \[([^\]]*)\]", changed)
                    self.assertEqual([a.strip() for a in pin[1].split(",") if a.strip()],
                                     remaining)
                    return subprocess.CompletedProcess(cmd, 1, "", "Audit/Overlaps.lean: "
                        "Docstring on `#guard_msgs` does not match generated message "
                        f"Audit.III_2 {dropped}")
                with patch.object(negative, "run", side_effect=run):
                    negative.changed_audit_pin()
                self.assertEqual(len(calls), 2)
                self.assertEqual(source.read_bytes(), original)
                self.assertEqual(negative.failures, [])

    def test_planted_outputs_cleaned_after_restoration(self):
        originals = {}
        for rel in ("Elements/BookI/Prop15.lean", "Elements/BookI/Prop16.lean", "facts.json"):
            originals[rel] = (REPO / rel).read_bytes()
            self.write(self.root / rel, originals[rel])
        for preexisting, outcome in ((False, "success"), (True, "success"),
                                     (False, "failed"), (True, "failed"),
                                     (False, "interrupted"), (True, "interrupted")):
            with self.subTest(preexisting=preexisting, outcome=outcome):
                for path in self.build.rglob("*"):
                    if path.is_file():
                        path.unlink()
                if preexisting:
                    self.outputs("Elements/Foundations/Tacit/Planted")
                saved = self.files()
                def run(*cmd):
                    self.assertEqual(cmd, ("lake", "build"))
                    self.outputs("Elements/Foundations/Tacit/Planted")
                    self.write(self.build / "ir/Elements/Foundations/Tacit/Planted.new",
                               b"new output")
                    if not self.planted.exists():
                        if outcome == "success":
                            return subprocess.CompletedProcess(cmd, 0, "", "")
                        return self.failed_rebuild(outcome == "interrupted")
                    return subprocess.CompletedProcess(cmd, 1, "", "planted build failed")
                with patch.object(negative, "run", side_effect=run) as commands:
                    if outcome == "interrupted":
                        with self.assertRaises(KeyboardInterrupt):
                            negative.planted_assumptions()
                    else:
                        negative.planted_assumptions()
                self.assertEqual(commands.call_count, 2)
                self.assertFalse(self.planted.exists())
                for rel, data in originals.items():
                    self.assertEqual((self.root / rel).read_bytes(), data)
                self.assertEqual(self.files(), saved)

    def test_law_plants_restore_sources_and_outputs(self):
        # The plant in two clean laws' proofs (#150), at each of its stages: whether the
        # planted build, the probe that prints the pins, the audit build or the certificate
        # run fails or is interrupted, or the run goes through to check_fidelity.py, and
        # whatever the restoration build does, the law proofs, the audit pins and
        # facts.json come back, and so do the outputs when the restoration build fails.
        rels = ("Elements/Figure/Superposition.lean", "Audit/Superposition.lean", "facts.json")
        originals = {rel: (REPO / rel).read_bytes() for rel in rels}
        names = [m[2] for m in negative.AUDIT_PIN.finditer(originals[rels[1]].decode())]
        self.assertTrue(names)
        steps = ("baseline", "planted", "probe", "audit", "certificate", "fidelity")
        caught = ("✗ I.4: its construction_rules for the cited law lenSymm is ['Postulate1'], "
                  "not []\n✗ I.8: its construction_rules for the cited law lenSymm is "
                  "['Postulate1'], not []\n✗ I.4: its construction_rules for the cited law "
                  "angleSymm is ['Tacit.circles_meet'], not []\n")
        cases = [(stage, outcome, restoring)
                 for stage in ("planted", "probe", "audit", "certificate")
                 for outcome in ("failed", "interrupted")
                 for restoring in ("success", "failed", "interrupted")]
        cases += [(None, "completed", restoring)
                  for restoring in ("success", "failed", "interrupted")]
        for stage, outcome, restoring in cases:
            with self.subTest(stage=stage, outcome=outcome, restoring=restoring):
                for rel, data in originals.items():
                    self.write(self.root / rel, data)
                for path in self.build.rglob("*"):
                    if path.is_file():
                        path.unlink()
                self.outputs("Elements/Figure/Superposition")
                saved = self.files()
                calls = []

                def ends(step, cmd, ok):
                    """The step's result: its failure or interruption at `stage`."""
                    if step != stage:
                        return ok
                    self.damage_outputs()
                    if outcome == "interrupted":
                        raise KeyboardInterrupt(f"{step} interrupted")
                    return subprocess.CompletedProcess(cmd, 1, "", f"{step} failed")

                def run(*cmd):
                    calls.append(cmd)
                    step = steps[len(calls) - 1] if len(calls) <= len(steps) else None
                    done = subprocess.CompletedProcess(cmd, 0, "", "")
                    if cmd == ("lake", "build", "Elements", "Audit"):
                        # The restoration build, with every source back.
                        for rel, data in originals.items():
                            self.assertEqual((self.root / rel).read_bytes(), data)
                        if restoring == "success":
                            return done
                        return self.failed_rebuild(restoring == "interrupted")
                    if step in ("baseline", "fidelity"):
                        self.assertEqual(cmd, (sys.executable, "scripts/check_fidelity.py"))
                        if step == "baseline":
                            # The unplanted tree's problems, read before anything is planted.
                            for rel, data in originals.items():
                                self.assertEqual((self.root / rel).read_bytes(), data)
                            return subprocess.CompletedProcess(cmd, 0, "✓ fidelity\n", "")
                        return subprocess.CompletedProcess(cmd, 1, caught, "")
                    if step == "planted":
                        self.assertEqual(cmd, ("lake", "build"))
                        laws = (self.root / rels[0]).read_text()
                        self.assertIn("have _planted := @Postulate1", laws)
                        self.assertIn("have _planted := @Tacit.circles_meet", laws)
                        return ends(step, cmd, done)
                    if step == "probe":
                        self.assertEqual(cmd[:3], ("lake", "env", "lean"))
                        probe = Path(cmd[3])
                        self.assertEqual(probe.name, "Pins.lean")
                        self.assertNotEqual(probe.parent, self.root)
                        printed = [line.split(" ", 2)[2]
                                   for line in probe.read_text().splitlines()
                                   if line.startswith("#print axioms ")]
                        self.assertEqual(printed, names)
                        out = "".join(f"{probe}:{i}:0: info: '{n}' depends on axioms: "
                                      f"[propext, Elements.Postulate1]\n"
                                      for i, n in enumerate(names, 2))
                        return ends(step, cmd, subprocess.CompletedProcess(cmd, 0, out, ""))
                    if step == "audit":
                        self.assertEqual(cmd, ("lake", "build", "Audit"))
                        audit = (self.root / rels[1]).read_text()
                        self.assertEqual(audit.count("[propext, Elements.Postulate1]"),
                                         len(names))
                        return ends(step, cmd, done)
                    self.assertEqual(step, "certificate")
                    self.assertEqual(cmd, ("lake", "env", "lean", "Certificate/Facts.lean"))
                    (self.root / "facts.json").write_text("{}\n")
                    return ends(step, cmd, done)

                interrupted = "interrupted" in (outcome, restoring)
                with patch.object(negative, "run", side_effect=run):
                    if interrupted:
                        with self.assertRaises(KeyboardInterrupt):
                            negative.construction_in_clean_laws()
                    else:
                        negative.construction_in_clean_laws()
                reached = len(steps) if stage is None else steps.index(stage) + 1
                self.assertEqual(len(calls), reached + 1)
                self.assertEqual(calls[-1], ("lake", "build", "Elements", "Audit"))
                for rel, data in originals.items():
                    self.assertEqual((self.root / rel).read_bytes(), data)
                if restoring != "success":
                    self.assertEqual(self.files(), saved)
                if stage is None and restoring == "success":
                    self.assertEqual(negative.failures, [])
                negative.failures.clear()

    @staticmethod
    def axiom_pin(name, axioms="[propext]"):
        return (f"/--\ninfo: '{name}' depends on axioms: {axioms}\n-/\n"
                f"#guard_msgs in\n#print axioms {name}\n")

    STATEMENT_PIN = ("/--\ninfo: Elements.law : ∀ c ∈ cites, c.Holds primitives\n-/\n"
                     "#guard_msgs in\n#check Elements.law\n")

    def test_audit_pins_never_run_across_a_statement_pin(self):
        # #150's review: a statement pin (`#guard_msgs in` over `#check`) before an axiom
        # pin must be neither read into its message nor rewritten.
        rel = "Audit/Pins.lean"
        text = ("import Elements\n\n" + self.STATEMENT_PIN + "\n" + self.axiom_pin("Elements.a")
                + "\n" + self.STATEMENT_PIN + "\n" + self.axiom_pin("Elements.b"))
        self.write(self.root / rel, text.encode())
        found = list(negative.AUDIT_PIN.finditer(text))
        self.assertEqual([m[2] for m in found], ["Elements.a", "Elements.b"])
        for m in found:
            self.assertNotIn("#check", m[0])

        def run(*cmd):
            self.assertEqual(cmd[:3], ("lake", "env", "lean"))
            return subprocess.CompletedProcess(cmd, 0, "".join(
                f"{cmd[3]}:{i}:0: info: '{n}' depends on axioms: [propext, Elements.P]\n"
                for i, n in enumerate(("Elements.a", "Elements.b"), 2)), "")
        with patch.object(negative, "run", side_effect=run):
            changed = negative.rewritten_pins(rel)
        self.assertEqual(negative.failures, [])
        self.assertEqual(changed, text.replace("[propext]", "[propext, Elements.P]"))
        self.assertEqual(changed.count(self.STATEMENT_PIN), 2)

    def test_every_print_axioms_must_be_read_as_a_pin(self):
        # A `#print axioms` the pattern does not read as a pin fails the plant, before Lean
        # is run, rather than being left as it was.
        rel = "Audit/Pins.lean"
        self.write(self.root / rel, ("import Elements\n\n" + self.axiom_pin("Elements.a")
                                     + "\n#print axioms Elements.b\n").encode())
        with patch.object(negative, "run", side_effect=AssertionError("Lean was run")):
            self.assertIsNone(negative.rewritten_pins(rel))
        self.assertEqual(negative.failures, [
            f"printing the pins of {rel}: 2 `#print axioms` commands, but 1 pins read; "
            "update this test"])
        negative.failures.clear()
        text = ("import Elements\n\n" + self.axiom_pin("Elements.a")
                + "\n" + self.axiom_pin("Elements.b"))
        self.write(self.root / rel, text.encode())

        def run(*cmd):
            self.assertEqual(cmd[:3], ("lake", "env", "lean"))
            self.assertEqual(Path(cmd[3]).read_text().splitlines(), [
                "import Elements", "#print axioms Elements.a", "#print axioms Elements.b"])
            return subprocess.CompletedProcess(cmd, 0, "".join(
                f"{cmd[3]}:{i}:0: info: '{name}' depends on axioms: [propext, Elements.P]\n"
                for i, name in enumerate(("Elements.a", "Elements.b"), 2)), "")

        with patch.object(negative, "run", side_effect=run):
            changed = negative.rewritten_pins(rel)
        self.assertEqual(negative.failures, [])
        self.assertEqual(changed, text.replace("[propext]", "[propext, Elements.P]"))

    def test_certificate_plant_restores_source_on_interruption(self):
        source = self.root / "Certificate/Facts.lean"
        original = (REPO / "Certificate/Facts.lean").read_bytes()
        self.write(source, original)
        def interrupted(*cmd):
            self.assertEqual(cmd, (sys.executable, "-I", "tests/test_certificate.py"))
            self.assertIn(b"Derives.len_congr", source.read_bytes())
            self.assertNotIn(b"used.contains coincidenceStep", source.read_bytes())
            raise KeyboardInterrupt("certificate test interrupted")
        with patch.object(negative, "run", side_effect=interrupted):
            with self.assertRaises(KeyboardInterrupt):
                negative.certificate_constructor_counting()
        self.assertEqual(source.read_bytes(), original)

    def test_certificate_plant_restores_source_when_mutation_fails(self):
        source = self.root / "Certificate/Facts.lean"
        original = (REPO / "Certificate/Facts.lean").read_bytes().replace(b"\n", b"\r\n")
        for error in (KeyboardInterrupt("mutation interrupted"), OSError("partial write")):
            with self.subTest(error=type(error).__name__):
                self.write(source, original)
                def damaged_write(path, text, *args, **kwargs):
                    self.assertEqual(path, source)
                    self.assertIn("Derives.len_congr", text)
                    path.write_bytes(text[:100].encode())
                    raise error
                with patch.object(Path, "write_text", damaged_write), \
                        patch.object(negative, "run") as commands:
                    with self.assertRaises(type(error)) as raised:
                        negative.certificate_constructor_counting()
                self.assertIs(raised.exception, error)
                commands.assert_not_called()
                self.assertEqual(source.read_bytes(), original)

    def test_cited_law_plant_restores_source_and_outputs(self):
        source = self.root / negative.SYNTAX
        original = (REPO / negative.SYNTAX).read_bytes()
        for interrupt in (False, True):
            with self.subTest(interrupt=interrupt):
                negative.failures.clear()
                self.write(source, original)
                self.outputs("Elements/Foundations/Superposition/Syntax")
                self.outputs("Elements/BookI/Prop08")
                saved = self.files()
                def run(*cmd):
                    self.assertEqual(cmd, ("lake", "build", "Elements.BookI.Prop08"))
                    if source.read_bytes() == original:
                        return self.failed_rebuild(interrupt)
                    self.assertIn(b"  | planted\n", source.read_bytes())
                    self.damage_outputs()
                    return subprocess.CompletedProcess(cmd, 1, "", f"error: {negative.HOLDS_ALL}"
                                                       ":84:2: Missing cases:\nCited.planted\n")
                with patch.object(negative, "run", side_effect=run) as commands:
                    if interrupt:
                        with self.assertRaises(KeyboardInterrupt):
                            negative.cited_law_unproved()
                    else:
                        negative.cited_law_unproved()
                        self.assertEqual(negative.failures, ["the restored I.8 build: exit 1"])
                self.assertEqual(commands.call_count, 2)
                self.assertEqual(source.read_bytes(), original)
                self.assertEqual(self.files(), saved)

    def test_cited_law_refused_elsewhere_is_not_holds_all(self):
        source = self.root / negative.SYNTAX
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_bytes((REPO / negative.SYNTAX).read_bytes())
        def run(*cmd):
            return subprocess.CompletedProcess(cmd, 1, "", (
                "error: Elements/Figure/Superposition.lean:109:2: Missing cases:\n"
                f"error: {negative.HOLDS_ALL}:84:2: Missing cases:\nCited.planted\n"))
        with patch.object(negative, "run", side_effect=run):
            negative.cited_law_unproved()
        self.assertTrue(any("also refused outside" in f and "Elements/Figure/Superposition.lean"
                            in f for f in negative.failures), negative.failures)

    def test_figure_guard_needs_the_control_to_compile_and_the_plant_to_fail(self):
        source = self.root / negative.RESTRICTION
        original = (REPO / negative.RESTRICTION).read_bytes()
        proved = (f"'{negative.RESTRICT_NAME}' depends on axioms: "
                  "[propext, Classical.choice, Quot.sound]\n")
        sorried = (f"'{negative.RESTRICT_NAME}' depends on axioms: "
                   "[propext, sorryAx, Classical.choice, Quot.sound]\n")
        # (label, the control's errors and axioms, the plant's, the failure expected); a
        # run exits 1 when it has an error, or when a fourth item says so.
        cases = (
            ("caught", ([], proved), (["restrict"], sorried), None),
            ("the control refused inside the theorem", (["restrict"], sorried),
             (["restrict"], sorried), "the control"),
            ("the control refused elsewhere", (["other"], proved), (["restrict"], sorried),
             "the control"),
            ("the control failing with no error read", ([], proved, 1),
             (["restrict"], sorried), "the control"),
            ("the control resting on sorry", ([], sorried), (["restrict"], sorried),
             "the control"),
            ("the control's axioms not printed", ([], ""), (["restrict"], sorried),
             "the control"),
            ("the plant refused outside the theorem", ([], proved), (["other"], proved),
             "not caught by Rule.Figure.restrict alone"),
            ("the plant refused inside and outside", ([], proved),
             (["restrict", "other"], sorried), "not caught by Rule.Figure.restrict alone"),
            ("the plant compiled", ([], proved), ([], proved),
             "not caught by Rule.Figure.restrict alone"),
            ("the plant refused but proved", ([], proved), (["restrict"], proved),
             "not caught by Rule.Figure.restrict alone"),
        )
        for label, control, plant, expected in cases:
            with self.subTest(label):
                negative.failures.clear()
                self.write(source, original)
                calls = []
                def run(*cmd):
                    self.assertEqual(cmd, ("lake", "env", "lean", negative.RESTRICTION))
                    text = source.read_text()
                    is_control = negative.OVER_THE_FIGURE in text
                    self.assertNotEqual(is_control, negative.OVER_ALL_POINTS in text)
                    self.assertNotIn(negative.IFF_FIGURE, text)
                    calls.append(is_control)
                    line = {"restrict": negative.declaration_lines(text, negative.RESTRICT)[2],
                            "other": 1}
                    errors, axioms, *code = control if is_control else plant
                    return subprocess.CompletedProcess(
                        cmd, code[0] if code else int(bool(errors)), axioms, "".join(
                            f"{negative.RESTRICTION}:{line[e]}:5: error: Type mismatch\n"
                            for e in errors))
                with patch.object(negative, "run", side_effect=run):
                    negative.figure_guard_over_all_points()
                self.assertEqual(source.read_bytes(), original)
                if expected is None:
                    self.assertEqual(negative.failures, [])
                    self.assertEqual(calls, [True, False])
                else:
                    self.assertEqual(len(negative.failures), 1, negative.failures)
                    self.assertIn(expected, negative.failures[0])
                    if expected == "the control":
                        self.assertEqual(calls, [True])

    def test_figure_guard_restores_the_source_when_interrupted(self):
        source = self.root / negative.RESTRICTION
        original = (REPO / negative.RESTRICTION).read_bytes()
        self.write(source, original)
        with patch.object(negative, "run", side_effect=KeyboardInterrupt), \
                self.assertRaises(KeyboardInterrupt):
            negative.figure_guard_over_all_points()
        self.assertEqual(source.read_bytes(), original)

    def test_failed_regressions_stop_before_any_plant(self):
        with patch.object(negative, "run", return_value=subprocess.CompletedProcess(
                [], 1, "", "regression failed")) as commands, \
                patch.object(negative, "heath_word") as plant:
            self.assertEqual(negative.main(), 1)
        self.assertEqual(commands.call_args.args,
                         (sys.executable, "-I", "tests/test_negative_tests.py",
                          "RestorationTests"))
        plant.assert_not_called()

    def test_counts_only_invokes_no_lake_or_lean_build(self):
        commands = []

        def run(*cmd):
            commands.append(cmd)
            return subprocess.CompletedProcess(cmd, 0, "", "")

        with patch.object(negative, "run", side_effect=run), \
                patch.object(negative, "count_markers") as counts:
            self.assertEqual(negative.main(("--counts-only",)), 0)
        self.assertEqual(commands, [
            (sys.executable, "-I", "tests/test_negative_tests.py", "RestorationTests"),
            (sys.executable, "-I", "tests/test_generated_counts.py"),
            (sys.executable, "-I", "tests/test_decision_entries.py"),
        ])
        self.assertFalse(any(part in {"lake", "lean"}
                             for command in commands for part in command))
        counts.assert_called_once_with()

    def test_final_status_checked_without_replacing_original_exception(self):
        for final in ("unchanged", "changed", "failed", "raised"):
            with self.subTest(final=final):
                negative.failures.clear()
                status_calls = []
                original = KeyboardInterrupt("plant interrupted")
                output = io.StringIO()
                def run(*cmd):
                    if cmd[:2] != ("git", "status"):
                        return subprocess.CompletedProcess(cmd, 0, "", "")
                    status_calls.append(cmd)
                    if len(status_calls) == 2:
                        if final == "raised":
                            raise OSError("final status unavailable")
                        if final == "failed":
                            return subprocess.CompletedProcess(cmd, 1, "", "status failed")
                        if final == "changed":
                            return subprocess.CompletedProcess(cmd, 0, " M unexpected\n", "")
                    return subprocess.CompletedProcess(cmd, 0, " M entry\n", "")
                with redirect_stdout(output), \
                        patch.object(negative, "run", side_effect=run), \
                        patch.object(negative, "heath_word", side_effect=original):
                    with self.assertRaises(KeyboardInterrupt) as raised:
                        negative.main()
                self.assertIs(raised.exception, original)
                self.assertEqual(len(status_calls), 2)
                if final == "changed":
                    self.assertIn("the working tree did not return to its entry Git status",
                                  negative.failures)
                    self.assertIn(
                        "✗ the working tree did not return to its entry Git status:\n",
                        output.getvalue())
                    self.assertIn(" M unexpected\n", output.getvalue())
                elif final == "failed":
                    self.assertIn("final Git status: exit 1", negative.failures)
                    self.assertIn("✗ final Git status: exit 1\n", output.getvalue())
                    self.assertIn("status failed\n", output.getvalue())
                elif final == "raised":
                    self.assertIn(
                        "Final Git status also failed: OSError: final status unavailable\n",
                        output.getvalue())
                else:
                    self.assertIn(
                        "✓ working tree restored to its entry Git status\n",
                        output.getvalue())


class CircleRuleTests(unittest.TestCase):
    inside = "Tacit.inside_of_between"
    outside = "Tacit.outside_of_between"

    def setUp(self):
        tmp = self.enterContext(tempfile.TemporaryDirectory())
        self.root = Path(tmp)
        self.lock = self.root / "Certificate/axioms.lock"
        self.lock.parent.mkdir()
        self.errors = []
        self.enterContext(patch.multiple(negative, ROOT=self.root, failures=[]))
        self.enterContext(patch.object(negative.check_fidelity, "errors", self.errors))
        self.enterContext(redirect_stdout(io.StringIO()))

    def fixture(self, locked, proved=None):
        types = {name: "fixture statement" for name in locked}
        self.lock.write_text(negative.check_fidelity.render_lock(types, {}))
        facts = {"axiom_types": types, "axiom_modules": {}, "vocabulary": {}}
        if proved is not None:
            facts["proved_rules"] = proved
        return facts

    def test_locked_rules_need_no_proved_rules_key(self):
        facts = self.fixture((self.inside, self.outside))
        self.assertEqual(negative.check_fidelity.check_lock(facts, self.lock), 2)
        self.assertEqual(self.errors, [])

    def test_either_proved_rule_needs_the_other_as_a_locked_axiom(self):
        for proved, locked in ((self.inside, self.outside), (self.outside, self.inside)):
            for dependencies in ([], ["Postulate1"], [proved], [locked], ["Postulate1", locked]):
                with self.subTest(proved=proved, dependencies=dependencies):
                    self.errors.clear()
                    facts = self.fixture((locked,), {proved: dependencies})
                    self.assertEqual(negative.check_fidelity.check_lock(facts, self.lock), 1)
                    if locked in dependencies:
                        self.assertEqual(self.errors, [])
                    else:
                        self.assertEqual(len(self.errors), 1)
                        self.assertIn(proved, self.errors[0])
                        self.assertIn("proved without another forbidden circle rule",
                                      self.errors[0])

    def test_missing_or_renamed_rule_is_refused_without_proof(self):
        for proved in (None, {}, {"Tacit.renamed": [self.outside]}):
            with self.subTest(proved=proved):
                self.errors.clear()
                facts = self.fixture((self.outside,), proved)
                negative.check_fidelity.check_lock(facts, self.lock)
                self.assertEqual(len(self.errors), 1)
                self.assertIn(f"{self.inside} (Circle 2): not an axiom", self.errors[0])
                self.assertIn("renamed", self.errors[0])

    def test_unlocked_dependency_and_circular_proofs_are_refused(self):
        facts = self.fixture((), {self.inside: [self.outside], self.outside: [self.inside]})
        negative.check_fidelity.check_lock(facts, self.lock)
        self.assertEqual(len(self.errors), 2)
        for rule, error in zip(negative.check_fidelity.FORBIDDEN_CIRCLE_RULES, self.errors):
            self.assertIn(rule, error)
            self.assertIn("proved without another forbidden circle rule", error)

    def test_circle_plant_checks_both_cases_and_restores_either_lock(self):
        for retired in (False, True):
            with self.subTest(retired=retired):
                facts = self.fixture((self.outside,) if retired else (self.inside, self.outside))
                (self.root / "facts.json").write_text(json.dumps(facts))
                saved = self.lock.read_bytes()
                saved_facts = (self.root / "facts.json").read_bytes()
                self.errors[:] = ["a previous finding"]
                with patch.object(negative.check_fidelity, "check_lock",
                                  wraps=negative.check_fidelity.check_lock) as check:
                    negative.circle_proved()
                self.assertEqual(check.call_count, 2)
                calls = [call.args[0] for call in check.call_args_list]
                self.assertEqual(calls[0]["proved_rules"][self.inside], [])
                self.assertEqual(calls[1]["proved_rules"][self.inside], [self.outside])
                self.assertEqual(negative.failures, [])
                self.assertEqual(self.errors, ["a previous finding"])
                self.assertEqual(self.lock.read_bytes(), saved)
                self.assertEqual((self.root / "facts.json").read_bytes(), saved_facts)

    def test_circle_plant_restores_on_failure_or_interrupt(self):
        for retired in (False, True):
            for exception in (RuntimeError, KeyboardInterrupt):
                with self.subTest(retired=retired, exception=exception):
                    facts = self.fixture((self.outside,) if retired
                                         else (self.inside, self.outside))
                    (self.root / "facts.json").write_text(json.dumps(facts))
                    saved = self.lock.read_bytes()
                    self.errors[:] = ["a previous finding"]
                    with patch.object(negative.check_fidelity, "check_lock",
                                      side_effect=exception("interrupted")):
                        with self.assertRaises(exception):
                            negative.circle_proved()
                    self.assertEqual(self.lock.read_bytes(), saved)
                    self.assertEqual(self.errors, ["a previous finding"])
                    self.assertEqual(json.loads((self.root / "facts.json").read_text()), facts)


class AbsentTrackedFileTests(unittest.TestCase):
    """A commit adds a check and its test (and a note beside them), and the pre-flight's
    pass with origin/main's checks (scripts/safe_push.py, step 4, base_copies) unlinks
    each from the work tree while Git's index still lists it. Every listing of tracked
    files names them and goes on with what is present; one absent outside the check
    inputs is a failure, and an error reading one, as in a directory of mode 000, is
    raised. Git runs only in a temporary repository, without user config."""

    present = {"scripts/check.py": "# the check\n", "tests/test_check.py": "# its test\n",
               "docs/notes.md": "Words: <!-- count:vocabulary -->3<!-- /count -->.\n"}
    added = ("scripts/new_check.py", "tests/test_new_check.py", "tests/new_check.md",
             "tests/a\x1b[2K\rforged\nline.py")

    def setUp(self):
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        self.enterContext(patch.dict(os.environ, {**env, "GIT_CONFIG_GLOBAL": os.devnull,
                                                  "GIT_CONFIG_NOSYSTEM": "1"}, clear=True))
        self.enterContext(patch.multiple(negative, ROOT=self.root, failures=[]))
        self.output = self.enterContext(redirect_stdout(io.StringIO()))
        files = {**self.present, **{rel: f"# added: {rel}\n" for rel in self.added}}
        for rel, text in files.items():
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.root / rel).write_text(text)
        self.git("init", "-q")
        self.git("add", "--", *files)
        self.git("-c", "user.name=test", "-c", "user.email=test@example.invalid",
                 "commit", "-q", "--no-verify", "-m", "add a check and its test")
        for rel in self.added:
            (self.root / rel).unlink()       # as base_copies takes out a file the commit adds
        self.assertEqual(self.git_names(), sorted(files))

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.root, capture_output=True, text=True,
                              check=True).stdout

    def git_names(self):
        result = subprocess.run(["git", "ls-files", "-z"], cwd=self.root,
                                capture_output=True, check=True)
        return [name.decode() for name in result.stdout.split(b"\0") if name]

    def note(self, rel):
        return ("note: tracked but absent from the work tree (under the check inputs, as a "
                "file the commit adds is in the pre-flight's pass with origin/main's "
                f"checks): {rel!r}\n")

    def assert_named(self, failures=()):
        for rel in self.added:
            self.assertIn(self.note(rel), self.output.getvalue())
        self.assertEqual(negative.failures, list(failures))

    def test_count_copy_names_absent_files_and_copies_the_rest(self):
        with negative.count_source_copy() as (copy, env):
            copied = {p.relative_to(copy).as_posix() for p in copy.rglob("*") if p.is_file()}
            self.assertEqual(copied, set(self.present))
            for rel in self.present:
                self.assertEqual((copy / rel).read_bytes(), (self.root / rel).read_bytes())
            self.assertEqual((env["GIT_DIR"], env["GIT_WORK_TREE"]),
                             (str(self.root / ".git"), str(copy)))
        self.assert_named()

    def test_marker_copy_names_absent_files(self):
        _, listing = negative.tracked_names()
        copy = Path(self.enterContext(tempfile.TemporaryDirectory()))
        negative.copy_marker_files(copy, listing)
        copied = {p.relative_to(copy).as_posix() for p in copy.rglob("*") if p.is_file()}
        self.assertEqual(copied, set(self.present))
        self.assert_named()

    def test_generated_outputs_pass_over_absent_markdown(self):
        self.assertEqual(negative.generated_files(), {self.root / "docs/notes.md"})
        self.assertIn(self.note("tests/new_check.md"), self.output.getvalue())
        self.assertEqual(negative.failures, [])

    def test_absent_file_outside_the_check_inputs_fails(self):
        (self.root / "docs/notes.md").unlink()
        message = ("tracked but absent from the work tree, outside the check inputs: "
                   "'docs/notes.md'")
        with negative.count_source_copy() as (copy, _):
            copied = {p.relative_to(copy).as_posix() for p in copy.rglob("*") if p.is_file()}
            self.assertEqual(copied, {"scripts/check.py", "tests/test_check.py"})
        _, listing = negative.tracked_names()
        negative.copy_marker_files(Path(self.enterContext(tempfile.TemporaryDirectory())),
                                   listing)
        self.assertEqual(self.output.getvalue().count(f"✗ {message}\n"), 2)
        self.assert_named([message])

    def test_an_unreadable_directory_is_not_absent(self):
        docs = self.root / "docs"
        docs.chmod(0)
        self.addCleanup(docs.chmod, 0o755)
        _, listing = negative.tracked_names()
        with self.assertRaises(PermissionError), negative.count_source_copy():
            pass
        with self.assertRaises(PermissionError):
            negative.copy_marker_files(Path(self.enterContext(tempfile.TemporaryDirectory())),
                                       listing)
        self.assertEqual(self.output.getvalue(), "")
        self.assertEqual(negative.failures, [])


if __name__ == "__main__":
    unittest.main()
