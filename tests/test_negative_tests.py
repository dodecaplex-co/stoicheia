#!/usr/bin/env python3
"""Restoration regressions for scripts/negative_tests.py, without Lean, and without Git
outside temporary repositories.

    python3 -I tests/test_negative_tests.py

The negative suite runs these first. Temporary files stand in for Lake outputs;
simulated builds delete, replace and create them before failing or being interrupted.
A temporary repository stands in for the pre-flight's pass with origin/main's checks,
whose work tree lacks the files a commit adds under the check inputs while Git's index
still lists them. The plants are reached as the suite reaches them, through its loader
of scripts/negative/, and the loader is tested on temporary folders of small plants; one
test runs the suite as a script, in a temporary copy, to see that its plants share the
running module and that no bytecode runs in place of the runner or a plant. The comment
reader the scripts share is fed the texts on which a reader could read a Lean comment
otherwise than Lean does, each with Lean's own reading. The workers of `--workers` are
run on a throwaway repository, as a script, with small plants that need no Lean.
"""

import ast
import errno
import importlib.util
import io
import json
import os
import py_compile
import re
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time
import unittest
import warnings
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import Mock, patch

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))
import negative_tests as negative  # noqa: E402

# The lane exports the number of workers for its runs; these tests choose their own.
os.environ.pop(negative.WORKERS, None)


def plant(name):
    """The plant() of scripts/negative/<name>.py, as the loader gives it."""
    plants, faults = negative.load_plants(REPO / "scripts" / "negative")
    assert not faults, faults
    return next(p for p in plants if p.name == name).plant


def stand_in(root, **kwargs):
    """One stand-in plant, its function a Mock given `kwargs`, as load_plants returns it."""
    function = Mock(**kwargs)
    return ([negative.Plant("heath_word", root / "scripts/negative/heath_word.py",
                            "A stand-in.", False, function)], []), function


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
            plant("corrupt_olean")()
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
                            plant("corrupt_olean")()
                    else:
                        plant("corrupt_olean")()
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
                    plant("ill_typed_proof")()
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
                            plant("ill_typed_proof")()
                    else:
                        plant("ill_typed_proof")()
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
                            plant("missing_files")()
                    else:
                        plant("missing_files")()
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
                            plant("changed_audit_pin")()
                    else:
                        plant("changed_audit_pin")()
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
                    plant("changed_audit_pin")()
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
                            plant("planted_assumptions")()
                    else:
                        plant("planted_assumptions")()
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
                            plant("construction_in_clean_laws")()
                    else:
                        plant("construction_in_clean_laws")()
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
            self.assertEqual(cmd, (sys.executable, "-I", "tests/test_certificate.py",
                                   "CommonNotion4Tests"))
            self.assertIn(b"Derives.len_congr", source.read_bytes())
            self.assertNotIn(b"used.contains coincidenceStep", source.read_bytes())
            raise KeyboardInterrupt("certificate test interrupted")
        with patch.object(negative, "run", side_effect=interrupted):
            with self.assertRaises(KeyboardInterrupt):
                plant("certificate_constructor_counting")()
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
                        plant("certificate_constructor_counting")()
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
                            plant("cited_law_unproved")()
                    else:
                        plant("cited_law_unproved")()
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
            plant("cited_law_unproved")()
        self.assertTrue(any("also refused outside" in f and "Elements/Figure/Superposition.lean"
                            in f for f in negative.failures), negative.failures)

    def test_figure_guard_runs_differ_in_the_guard_alone(self):
        original = (REPO / negative.RESTRICTION).read_text()
        control = negative.plant_figure_guard(original, negative.OVER_THE_FIGURE)
        plant = negative.plant_figure_guard(original, negative.OVER_ALL_POINTS)
        self.assertEqual(control.replace(negative.OVER_THE_FIGURE, "GUARD"),
                         plant.replace(negative.OVER_ALL_POINTS, "GUARD"))
        for text in (control, plant):
            proof = text[text.index(negative.RESTRICT):]
            self.assertIn("hh hX hΓ", proof)
            self.assertIn(negative.THROUGH_THE_EMBEDDING, proof)
            self.assertTrue(text.endswith(f"#print axioms {negative.RESTRICT_NAME}\n"))
            # Rule.iff_figure and its docstring are left out, and nothing else.
            self.assertNotIn(negative.IFF_FIGURE, text)
            self.assertNotIn("for laws that hold.**", text)
            self.assertNotIn("\n\n\n", text)
            self.assertIn("def Rule.Figure", text)
            self.assertIn("structure Interpretation.Embedding", text)
        start = original.index("/-- **The rule is its part about the figure")
        iff = original[start:original.index("\n\n", original.index(negative.IFF_FIGURE))]
        edited = ["      ¬ I.OnLine (v.pt h) (v.line l) → (∀ ℓ ∈ Γ, ℓ.Holds v) → φ.Holds v",
                  "  intro n m Γ a b c d g h l φ dφ v hT hd hg hdg hh hΓ"]
        removed = [line for line in original.splitlines() if line not in plant.splitlines()]
        self.assertEqual(sorted(removed), sorted(iff.splitlines() + edited))

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
        for label, control, planted, expected in cases:
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
                    errors, axioms, *code = control if is_control else planted
                    return subprocess.CompletedProcess(
                        cmd, code[0] if code else int(bool(errors)), axioms, "".join(
                            f"{negative.RESTRICTION}:{line[e]}:5: error: Type mismatch\n"
                            for e in errors))
                with patch.object(negative, "run", side_effect=run):
                    plant("figure_guard_over_all_points")()
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
            plant("figure_guard_over_all_points")()
        self.assertEqual(source.read_bytes(), original)

    def test_failed_regressions_stop_before_any_plant(self):
        loaded, first = stand_in(self.root)

        def run(*cmd):
            if cmd[:2] == ("git", "status"):
                return subprocess.CompletedProcess(cmd, 0, "", "")
            return subprocess.CompletedProcess(cmd, 1, "", "regression failed")
        with patch.object(negative, "run", side_effect=run) as commands, \
                patch.object(negative, "load_plants", return_value=loaded) as load:
            self.assertEqual(negative.main(), 1)
        # The bracket's entry status comes before the regressions, and its closing one after.
        self.assertEqual([call.args for call in commands.call_args_list],
                         [("git", "status", "--porcelain"),
                          (sys.executable, "-I", "tests/test_negative_tests.py"),
                          ("git", "status", "--porcelain")])
        first.assert_not_called()
        load.assert_not_called()

    def test_counts_only_invokes_no_lake_or_lean_build(self):
        commands = []

        def run(*cmd):
            commands.append(cmd)
            return subprocess.CompletedProcess(cmd, 0, "", "")

        # The real plants are loaded, from the repository, and the count plant's run is
        # stood in for.
        with patch.object(negative, "run", side_effect=run), \
                patch.object(negative, "ROOT", REPO), \
                patch.object(negative, "run_plant") as counts:
            self.assertEqual(negative.main(("--counts-only",)), 0)
        self.assertEqual(commands, [
            (sys.executable, "-I", "tests/test_negative_tests.py"),
            (sys.executable, "-I", "tests/test_generated_counts.py"),
            (sys.executable, "-I", "tests/test_decision_entries.py"),
            (sys.executable, "-I", "tests/test_risk.py"),
            (sys.executable, "-I", "tests/test_axiom_lock.py"),
        ])
        self.assertFalse(any(part in {"lake", "lean"}
                             for command in commands for part in command))
        counts.assert_called_once()
        self.assertEqual(counts.call_args.args[0].name, "count_markers")

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
                loaded, _ = stand_in(self.root, side_effect=original)
                with redirect_stdout(output), \
                        patch.object(negative, "run", side_effect=run), \
                        patch.object(negative, "load_plants", return_value=loaded):
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

    def fixture(self, locked, proved=None, cites=None, propositions=None):
        """facts.json's tables, the lock holding `locked`, and the entries `propositions`
        (III.1 and a sound III.2 when None)."""
        types = {name: "fixture statement" for name in locked}
        self.lock.write_text(negative.check_fidelity.render_lock(types, {}))
        facts = {"axiom_types": types, "axiom_modules": {}, "vocabulary": {},
                 "propositions": [self.entry("III.1"), self.entry("III.2")]
                 if propositions is None else propositions}
        if proved is not None:
            facts["proved_rules"] = proved
        if cites is not None:
            facts["proved_rule_cites"] = cites
        return facts

    @staticmethod
    def entry(ref, **fields):
        """An entry's fields that the circle guard reads, resting on no circle rule, with
        `fields` in their place."""
        lemma = {"name": "BookI.Prop5.base", "file": "Elements/BookI/Helpers.lean", "line": 27}
        return {"ref": ref, "kind": "proposition", "status": "proved", "cites": ["I.5"],
                "axioms": ["Postulate1", "Postulate2"],
                "shared_steps": [dict(lemma, brings_in=["I.5"])],
                "inherited": {"Postulate2": [lemma]}, **fields}

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

    def refuses_circle3(self, facts, *wanted):
        """check_lock finds one fault in `facts`, Circle 3's, saying each of `wanted`."""
        self.errors.clear()
        negative.check_fidelity.check_lock(facts, self.lock)
        self.assertEqual(len(self.errors), 1, self.errors)
        self.assertIn(f"{self.outside} (Circle 3): ", self.errors[0])
        for words in wanted:
            self.assertIn(words, self.errors[0])

    def refuses_as_unproved(self, facts):
        self.refuses_circle3(facts, "proved without another forbidden circle rule",
                             "or a proof that cites III.2")

    def test_rules_proved_from_a_sound_iii2_pass(self):
        facts = self.fixture((self.inside,), {self.outside: ["Postulate1"]},
                             {self.outside: ["I.5", "III.2"]})
        self.assertEqual(negative.check_fidelity.check_lock(facts, self.lock), 1)
        self.assertEqual(self.errors, [])
        # Then Circle 2, proved from Circle 3, cites III.2 through it, as the entries would.
        facts = self.fixture((), {self.inside: [], self.outside: ["Postulate1"]},
                             {self.inside: ["III.2"], self.outside: ["III.2"]})
        self.assertEqual(negative.check_fidelity.check_lock(facts, self.lock), 0)
        self.assertEqual(self.errors, [])

    def test_a_rule_proved_citing_nothing_is_refused(self):
        for cites in ({}, {self.outside: []}, {self.outside: ["I.5"]},
                      {self.inside: ["III.2"]}):
            with self.subTest(cites=cites):
                self.refuses_as_unproved(self.fixture((self.inside,), {self.outside: []}, cites))

    def test_a_rule_citing_other_propositions_but_not_iii2_is_refused(self):
        for cited in (["III.1"], ["III.3"], ["III.1", "III.3"], ["III.20"], ["II.2"]):
            with self.subTest(cited=cited):
                self.refuses_as_unproved(
                    self.fixture((self.inside,), {self.outside: []}, {self.outside: cited}))

    def test_a_rule_citing_a_missing_or_unproved_iii2_is_refused(self):
        for propositions, fault in (
                ([self.entry("III.1")], "III.2 has no entry in facts.json"),
                ([], "III.2 has no entry in facts.json"),
                ([self.entry("III.2", status="sketched")], "III.2 is 'sketched', not \"proved\""),
                ([self.entry("III.2", status="proved-pending")],
                 "III.2 is 'proved-pending', not \"proved\"")):
            with self.subTest(fault=fault, propositions=len(propositions)):
                facts = self.fixture((self.inside,), {self.outside: []},
                                     {self.outside: ["III.2"]}, propositions)
                self.refuses_circle3(facts, "proved by a proof that cites III.2, but " + fault)

    def test_a_rule_citing_an_iii2_that_rests_on_a_circle_rule_is_refused(self):
        def lemma(name):
            return {"name": name, "file": "Elements/Foundations/Tacit/Diagram.lean", "line": 152}
        for name, rule in negative.check_fidelity.FORBIDDEN_CIRCLE_RULES.items():
            for fields, fault in (
                    ({"axioms": ["Postulate1", name]},
                     f"rests on {name} ({rule}) among its axioms"),
                    ({"shared_steps": [dict(lemma(name), brings_in=["I.5"])]},
                     f"names {name} ({rule}) among its shared steps"),
                    ({"inherited": {"Postulate1": [lemma("len_pos"), lemma(name)]}},
                     f"names {name} ({rule}) among the lemmas it inherits through")):
                with self.subTest(rule=rule, fault=fault):
                    facts = self.fixture((self.inside,), {self.outside: []},
                                         {self.outside: ["III.2"]},
                                         [self.entry("III.1"), self.entry("III.2", **fields)])
                    self.refuses_circle3(facts, "proved by a proof that cites III.2, but "
                                         "III.2 itself " + fault)

    def test_missing_or_malformed_cites_count_as_citing_nothing(self):
        for cites in (None, ["III.2"], "III.2", {self.outside: "III.2"},
                      {self.outside: {"III.2": True}}, {self.outside: None},
                      {self.outside: 2}):
            with self.subTest(cites=cites):
                self.refuses_as_unproved(self.fixture((self.inside,), {self.outside: []}, cites))

    def test_a_malformed_iii2_entry_is_refused_without_a_crash(self):
        def facts(propositions):
            return self.fixture((self.inside,), {self.outside: []}, {self.outside: ["III.2"]},
                                propositions)
        absent = facts([])
        del absent["propositions"]
        for case, given, fault in (
                ("no propositions", absent, "III.2 has no entry"),
                ("propositions not a list", facts({"ref": "III.2"}), "III.2 has no entry"),
                ("entries not objects", facts([None, "III.2", ["III.2"]]), "III.2 has no entry"),
                ("no status", facts([{k: v for k, v in self.entry("III.2").items()
                                      if k != "status"}]), "III.2 is None, not \"proved\""),
                ("axioms a string", facts([self.entry("III.2", axioms=self.outside)]),
                 "III.2's `axioms` is not a list"),
                ("shared steps a string", facts([self.entry("III.2", shared_steps=self.outside)]),
                 "III.2's `shared_steps` is not a list of objects"),
                ("shared steps of names", facts([self.entry("III.2", shared_steps=[self.outside])]),
                 "III.2's `shared_steps` is not a list of objects"),
                ("inherited a list", facts([self.entry("III.2", inherited=[self.outside])]),
                 "III.2's `inherited` is not an object of lists of objects"),
                ("inherited of strings",
                 facts([self.entry("III.2", inherited={"Postulate1": self.outside})]),
                 "III.2's `inherited` is not an object of lists of objects"),
                ("inherited of names",
                 facts([self.entry("III.2", inherited={"Postulate1": [self.outside]})]),
                 "III.2's `inherited` is not an object of lists of objects")):
            with self.subTest(case=case):
                self.refuses_circle3(given, "proved by a proof that cites III.2, but " + fault)

    def test_a_rule_proved_from_a_locked_rule_needs_nothing_of_iii2(self):
        for propositions in ([], [self.entry("III.2", status="sketched")],
                             [self.entry("III.2", axioms=[self.outside])]):
            for cites in (None, {}, {self.inside: []}, {self.inside: ["III.2"]},
                          {self.inside: "III.2"}):
                with self.subTest(propositions=propositions, cites=cites):
                    self.errors.clear()
                    facts = self.fixture((self.outside,), {self.inside: [self.outside]}, cites,
                                         propositions)
                    self.assertEqual(negative.check_fidelity.check_lock(facts, self.lock), 1)
                    self.assertEqual(self.errors, [])

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
                    plant("circle_proved")()
                self.assertEqual(check.call_count, 2)
                calls = [call.args[0] for call in check.call_args_list]
                self.assertEqual(calls[0]["proved_rules"][self.inside], [])
                self.assertEqual(calls[1]["proved_rules"][self.inside], [self.outside])
                self.assertEqual(negative.failures, [])
                self.assertEqual(self.errors, ["a previous finding"])
                self.assertEqual(self.lock.read_bytes(), saved)
                self.assertEqual((self.root / "facts.json").read_bytes(), saved_facts)

    def test_circle_plant_locks_circle3_once_it_is_proved_from_iii2(self):
        # Circle 3 retired after III.2: neither rule in the lock, and facts.json giving
        # both as proved rules that cite III.2, as the walk finds them. The plant must
        # still make Circle 2 cite nothing, and put Circle 3 back in the lock and in the
        # tables of axioms for both cases.
        facts = self.fixture((), {self.inside: [], self.outside: []},
                             {self.inside: ["III.2"], self.outside: ["III.2"]})
        (self.root / "facts.json").write_text(json.dumps(facts))
        saved = self.lock.read_bytes()
        saved_facts = (self.root / "facts.json").read_bytes()
        self.errors[:] = ["a previous finding"]
        locks, original = [], negative.check_fidelity.check_lock

        def check_lock(facts, path):
            locks.append(negative.check_fidelity.read_lock(path)[0])
            return original(facts, path)
        with patch.object(negative.check_fidelity, "check_lock", side_effect=check_lock) as check:
            plant("circle_proved")()
        self.assertEqual(check.call_count, 2)
        calls = [call.args[0] for call in check.call_args_list]
        for call, dependencies, lock in zip(calls, ([], [self.outside]), locks):
            self.assertEqual(call["proved_rules"][self.inside], dependencies)
            self.assertEqual(call["proved_rule_cites"][self.inside], [])
            self.assertNotIn(self.outside, call["proved_rules"])
            self.assertNotIn(self.outside, call["proved_rule_cites"])
            self.assertIn(self.outside, call["axiom_types"])
            self.assertEqual(call["axiom_types"][self.outside], lock[self.outside])
            self.assertNotIn(self.inside, lock)
        self.assertEqual(negative.failures, [])
        self.assertEqual(self.errors, ["a previous finding"])
        self.assertEqual(self.lock.read_bytes(), saved)
        self.assertEqual((self.root / "facts.json").read_bytes(), saved_facts)

    def test_renamed_plant_renames_circle3_where_the_certificate_keeps_it(self):
        renamed = "Tacit.Circle.outside_of_between"
        for retired in (False, True):
            with self.subTest(retired=retired):
                facts = self.fixture(() if retired else (self.outside,),
                                     {self.outside: []} if retired else None,
                                     {self.outside: ["III.2"]} if retired else None)
                facts["axiom_modules"] = {name: "Elements.Foundations.Tacit.Diagram"
                                          for name in facts["axiom_types"]}
                (self.root / "facts.json").write_text(json.dumps(facts))
                saved = self.lock.read_bytes()
                seen = []

                def fidelity(*args):
                    self.assertEqual(args[0], "--facts")
                    seen.append((json.loads(Path(args[1]).read_text()),
                                 negative.check_fidelity.read_lock(self.lock)[0]))
                    return subprocess.CompletedProcess(
                        [], 1, f"✗ {self.outside} (Circle 3): not an axiom in "
                        "Certificate/axioms.lock\n", "")
                with patch.object(negative, "fidelity", side_effect=fidelity):
                    plant("circle_renamed")()
                (copy, lock), = seen
                tables = (("proved_rules", "proved_rule_cites") if retired
                          else ("axiom_types", "axiom_modules"))
                for table in tables:
                    self.assertIn(renamed, copy[table])
                    self.assertNotIn(self.outside, copy[table])
                self.assertEqual(renamed in lock, not retired)
                self.assertNotIn(self.outside, lock)
                self.assertEqual(negative.failures, [])
                self.assertEqual(self.lock.read_bytes(), saved)

    def test_circle_plant_restores_on_failure_or_interrupt(self):
        # Both rules locked; Circle 2 retired; and both proved from III.2, a lock into
        # which the plant writes Circle 3.
        both = {self.inside: ["III.2"], self.outside: ["III.2"]}
        for retired in (False, True, "both"):
            for exception in (RuntimeError, KeyboardInterrupt):
                with self.subTest(retired=retired, exception=exception):
                    facts = (self.fixture((), {self.inside: [], self.outside: []}, both)
                             if retired == "both" else
                             self.fixture((self.outside,) if retired
                                          else (self.inside, self.outside)))
                    (self.root / "facts.json").write_text(json.dumps(facts))
                    saved = self.lock.read_bytes()
                    self.errors[:] = ["a previous finding"]
                    with patch.object(negative.check_fidelity, "check_lock",
                                      side_effect=exception("interrupted")):
                        with self.assertRaises(exception):
                            plant("circle_proved")()
                    self.assertEqual(self.lock.read_bytes(), saved)
                    self.assertEqual(self.errors, ["a previous finding"])
                    self.assertEqual(json.loads((self.root / "facts.json").read_text()), facts)

    def test_iii2_plant_checks_three_cases_and_restores_any_lock(self):
        rules = (self.inside, self.outside)
        for locked in (rules, (self.outside,), ()):
            with self.subTest(locked=locked):
                facts = self.fixture(locked, {self.inside: [self.outside]} if locked else
                                     {self.inside: [], self.outside: []})
                (self.root / "facts.json").write_text(json.dumps(facts))
                saved = self.lock.read_bytes()
                saved_facts = (self.root / "facts.json").read_bytes()
                self.errors[:] = ["a previous finding"]
                refusals = []
                with patch.object(negative, "refusals", refusals), \
                        patch.object(negative.check_fidelity, "check_lock",
                                     wraps=negative.check_fidelity.check_lock) as check:
                    plant("circle_from_iii2")()
                self.assertEqual(check.call_count, 3)
                calls = [call.args[0] for call in check.call_args_list]
                for call, cited in zip(calls, ([], ["III.2"], ["III.2"])):
                    self.assertEqual(call["proved_rules"], {self.inside: [], self.outside: []})
                    self.assertEqual(call["proved_rule_cites"],
                                     {self.inside: cited, self.outside: cited})
                    self.assertFalse(set(rules) & set(call["axiom_types"]))
                self.assertEqual(calls[1]["propositions"], facts["propositions"])
                self.assertEqual(calls[2]["propositions"][1]["axioms"],
                                 facts["propositions"][1]["axioms"] + [self.outside])
                self.assertEqual(negative.failures, [])
                self.assertEqual(len(refusals), 2)
                self.assertEqual(self.errors, ["a previous finding"])
                self.assertEqual(self.lock.read_bytes(), saved)
                self.assertEqual((self.root / "facts.json").read_bytes(), saved_facts)

    def test_iii2_plant_restores_on_failure_or_interrupt(self):
        for locked in ((self.inside, self.outside), ()):
            for exception in (RuntimeError, KeyboardInterrupt):
                for calls in (1, 3):
                    with self.subTest(locked=locked, exception=exception, calls=calls):
                        facts = self.fixture(locked)
                        (self.root / "facts.json").write_text(json.dumps(facts))
                        saved = self.lock.read_bytes()
                        self.errors[:] = ["a previous finding"]
                        effects = [None] * (calls - 1) + [exception("interrupted")]
                        with patch.object(negative, "refusals", []), \
                                patch.object(negative.check_fidelity, "check_lock",
                                             side_effect=effects):
                            with self.assertRaises(exception):
                                plant("circle_from_iii2")()
                        self.assertEqual(self.lock.read_bytes(), saved)
                        self.assertEqual(self.errors, ["a previous finding"])
                        self.assertEqual(json.loads((self.root / "facts.json").read_text()),
                                         facts)


class RetiredRulePlantTests(unittest.TestCase):
    """scripts/negative/retired_rule_used.py in a temporary tree, with its build, its
    certificate and check_fidelity.py stood in for (#168): the plant passes only when the
    pin on III.2's proved_rules, and no pin on its axioms, refuses the use, and the source,
    facts.json and the build files come back however a step ends."""

    rule = "Tacit.centre_unique"
    head = "    ∀ E : Point, Between A E B → InsideCircle E ABC := by\n"
    name = f"{rule} in III.2's proof, its axioms unchanged"
    # What check_fidelity.py prints for the pin on III.2's proved_rules (expectation 4 here,
    # as setUp writes them), for the pin on III.1's (expectation 2) and for a pin on III.2's
    # axioms (expectation 3); only the first may speak.
    pin = (f"✗ III.2: its proved_rules should not include {rule} "
           "(tests/certificate_expectations.json, expectation 4: .)\n")
    other_pin = (f"✗ III.1: its proved_rules should not include {rule} "
                 "(tests/certificate_expectations.json, expectation 2: .)\n")
    axioms_pin = (f"✗ III.2: its axioms should not include {rule} "
                  "(tests/certificate_expectations.json, expectation 3: .)\n")
    commands = (("lake", "build"), ("lake", "env", "lean", "Certificate/Facts.lean"),
                (sys.executable, "scripts/check_fidelity.py"), ("lake", "build"))

    def setUp(self):
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory()))
        self.enterContext(patch.multiple(negative, ROOT=self.root, failures=[], refusals=[]))
        self.output = self.enterContext(redirect_stdout(io.StringIO()))
        self.source = self.root / "Elements/BookIII/Prop02.lean"
        self.facts = self.root / "facts.json"
        self.olean = self.root / ".lake/build/lib/lean/Elements/BookIII/Prop02.olean"
        self.pins = self.root / "tests/certificate_expectations.json"
        for path in (self.source, self.olean, self.pins):
            path.parent.mkdir(parents=True, exist_ok=True)
        self.source.write_text("theorem Prop2 :\n" + self.head + "  intro E hAEB\n")
        self.facts.write_text(self.certificate([]))
        self.olean.write_bytes(b"olean original")
        # The first reads facts.json's top level and has no `ref`, as the real file's do.
        self.pins.write_text(json.dumps({"expectations": [
            {"field": "construction_rules", "includes": ["Postulate1"], "why": "."},
            {"ref": "III.1", "field": "proved_rules", "excludes": [self.rule], "why": "."},
            {"ref": "III.2", "field": "axioms", "excludes": [self.rule], "why": "."},
            {"ref": "III.2", "field": "proved_rules", "excludes": [self.rule], "why": "."}]}))
        self.saved = {p: p.read_bytes() for p in (self.source, self.facts, self.olean)}

    def certificate(self, rules, axioms=("Postulate1",), cites=("I.5",)):
        return json.dumps({"propositions": [
            {"ref": "III.2", "axioms": list(axioms), "cites": list(cites),
             "proved_rules": rules}]})

    def fake(self, axioms=("Postulate1",), cites=("I.5",), verdict=None, stage=None,
             interrupt=None):
        """A run in which the planted III.2 builds, the certificate records the rule with
        `axioms` and `cites`, and check_fidelity.py gives `verdict`, its exit code and
        output (by default it fails, naming the pin on III.2's proved_rules alone). The
        planted build or the certificate, as `stage` names, fails or, when `interrupt`,
        is interrupted; with no `stage`, the build after restoration does so, when
        `interrupt` is not None."""
        returncode, stdout = verdict or (1, self.pin)
        calls = []

        def ends(cmd):
            self.olean.write_bytes(b"incomplete")
            if interrupt:
                raise KeyboardInterrupt(f"{cmd} interrupted")
            return subprocess.CompletedProcess(cmd, 1, "", f"{cmd} failed")

        def run(*cmd):
            calls.append(cmd)
            planted = self.source.read_bytes() != self.saved[self.source]
            if cmd == ("lake", "build") and not planted:
                # The restoration build, with the source and facts.json back.
                self.assertEqual(self.facts.read_bytes(), self.saved[self.facts])
                if stage is None and interrupt is not None:
                    return ends(cmd)
                self.olean.write_bytes(b"olean rebuilt")
                return subprocess.CompletedProcess(cmd, 0, "", "")
            self.assertTrue(planted)
            self.assertEqual(self.source.read_text(), self.saved[self.source].decode().replace(
                self.head, f"{self.head}  have _retired := @Elements.{self.rule}\n"))
            if cmd == ("lake", "build"):
                if stage == "build":
                    return ends(cmd)
                self.olean.write_bytes(b"olean planted")
                return subprocess.CompletedProcess(cmd, 0, "", "")
            if cmd == ("lake", "env", "lean", "Certificate/Facts.lean"):
                if stage == "certificate":
                    return ends(cmd)
                self.facts.write_text(self.certificate([self.rule], axioms, cites))
                return subprocess.CompletedProcess(cmd, 0, "", "")
            self.assertEqual(cmd, (sys.executable, "scripts/check_fidelity.py"))
            return subprocess.CompletedProcess(cmd, returncode, stdout, "")
        return calls, run

    def planted(self, run, interrupted=False):
        with patch.object(negative, "run", side_effect=run):
            if interrupted:
                with self.assertRaises(KeyboardInterrupt):
                    plant("retired_rule_used")()
            else:
                plant("retired_rule_used")()

    def assert_restored(self, olean=b"olean rebuilt"):
        self.assertEqual(self.source.read_bytes(), self.saved[self.source])
        self.assertEqual(self.facts.read_bytes(), self.saved[self.facts])
        self.assertEqual(self.olean.read_bytes(), olean)

    def test_the_pin_on_proved_rules_names_it_and_the_tree_is_restored(self):
        calls, run = self.fake()
        self.planted(run)
        self.assertEqual(tuple(calls), self.commands)
        self.assertEqual(negative.failures, [])
        self.assertEqual(negative.refusals, [f"{self.name}: caught"])
        self.assertIn(f"✓ {self.name}: caught", self.output.getvalue())
        self.assert_restored()

    def test_a_check_that_does_not_name_the_pin_alone_is_not_caught(self):
        """The plant reports one failure, "not caught", when check_fidelity.py passes or
        fails without naming the pin on III.2's proved_rules, names another entry's pin, or
        names a pin on III.2's axioms; the tree is restored each time."""
        for case, verdict, reason in (
                ("passes silently", (0, ""), "missing"),
                ("passes, naming the pin", (0, self.pin), None),
                ("fails silently", (1, ""), "missing"),
                ("names III.1's pin alone", (1, self.other_pin), "missing"),
                ("names the pin on its axioms alone", (1, self.axioms_pin), "missing"),
                ("names both pins", (1, self.pin + self.axioms_pin), "wrongly says"),
                ("names the rule under another expectation",
                 (1, self.pin.replace("expectation 4:", "expectation 5:")), "missing")):
            with self.subTest(case):
                negative.failures.clear()
                negative.refusals.clear()
                start = len(self.output.getvalue())
                calls, run = self.fake(verdict=verdict)
                self.planted(run)
                self.assertEqual(tuple(calls), self.commands)
                self.assertEqual(negative.refusals, [])
                self.assertEqual(len(negative.failures), 1, negative.failures)
                self.assertTrue(negative.failures[0].startswith(
                    f"{self.name}: not caught" + (f" ({reason} " if reason else "")),
                    negative.failures[0])
                self.assertNotIn(f"✓ {self.name}", self.output.getvalue()[start:])
                self.assert_restored()

    def test_a_plant_that_changes_the_axioms_or_cites_fails(self):
        for field, changed in (("axioms", {"axioms": ("Postulate1", "Tacit.circle_eq")}),
                               ("cites", {"cites": ("I.5", "I.7")})):
            with self.subTest(field=field):
                negative.failures.clear()
                calls, run = self.fake(**changed)
                self.planted(run)
                self.assertEqual(tuple(calls), self.commands)
                self.assertEqual(negative.failures, [
                    f"{self.name}: {self.rule} changed III.2's {field}, so the plant no longer "
                    "shows what only proved_rules can; update this test"])
                self.assert_restored()

    def test_a_failed_or_interrupted_step_restores_the_tree(self):
        # The planted build or the certificate ends early: nothing after it runs, and the
        # restoration build puts the build files back.
        for stage, reached, step in (
                ("build", 1, "III.2 built with a retired rule in its proof"),
                ("certificate", 2, "the certificate with a retired rule in III.2")):
            for interrupt in (False, True):
                with self.subTest(stage=stage, interrupt=interrupt):
                    negative.failures.clear()
                    self.olean.write_bytes(self.saved[self.olean])
                    calls, run = self.fake(stage=stage, interrupt=interrupt)
                    self.planted(run, interrupted=interrupt)
                    self.assertEqual(tuple(calls),
                                     self.commands[:reached] + (("lake", "build"),))
                    if not interrupt:
                        self.assertEqual(negative.failures, [f"{step}: exit 1"])
                    self.assert_restored()

    def test_a_failed_or_interrupted_restoration_build_restores_the_outputs(self):
        for interrupt in (False, True):
            with self.subTest(interrupt=interrupt):
                negative.failures.clear()
                self.olean.write_bytes(self.saved[self.olean])
                calls, run = self.fake(interrupt=interrupt)
                self.planted(run, interrupted=interrupt)
                self.assertEqual(tuple(calls), self.commands)
                if not interrupt:
                    self.assertEqual(negative.failures, ["the restored III.2 builds: exit 1"])
                self.assert_restored(olean=self.saved[self.olean])

    def test_without_one_pin_on_iii2_s_proved_rules_nothing_is_planted(self):
        for pins in ([], [{"ref": "III.2", "field": "proved_rules", "excludes": [self.rule],
                           "why": "."}] * 2):
            with self.subTest(pins=len(pins)):
                negative.failures.clear()
                self.pins.write_text(json.dumps({"expectations": pins}))
                with patch.object(negative, "run", side_effect=AssertionError("ran")):
                    plant("retired_rule_used")()
                self.assertEqual(negative.failures, [
                    f"{self.name}: expected one pin keeping {self.rule} from III.2's "
                    f"proved_rules, found {len(pins)}; update this test"])
                self.assertEqual(self.source.read_bytes(), self.saved[self.source])


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


class BookZeroImportTests(unittest.TestCase):
    """check_fidelity's rule 3 on a small tree, without Lean (#200): Book Zero's imports
    read as Lean 4.35 reads them, through comments, strings and «…» names, and through
    the edition's own files."""

    rel = "Elements/Figure/Planted.lean"
    tree = {"Elements/BookI/Prop01.lean": "theorem planted : True := trivial\n",
            "Elements/Companions.lean": "import Elements.BookI.Prop01\n",
            "Elements/Foundations/Words.lean": "import Init.Prelude\n",
            "Elements/Figure/Lines.lean": "import Elements.Foundations.Words\n"}

    def setUp(self):
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        for rel, text in self.tree.items():
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.root / rel).write_text(text)

    def findings(self, text, rel=None):
        (self.root / (rel or self.rel)).write_text(text, encoding="utf-8")
        return [line for line in negative.rules_in(self.root).stdout.split("\n") if line]

    def refused(self, line):
        return f"{self.rel}:{line}: Book Zero must not import a proposition"

    def test_each_spelling_of_the_negative_plants_is_refused_on_its_line(self):
        for what, text, *extra in negative.BOOK_ZERO_SPELLINGS:
            with self.subTest(what=what):
                found = self.findings(text)
                line = text.count("\n", 0, text.rindex("import")) + 1
                self.assertEqual(len(found), 1, found)
                self.assertTrue(found[0].startswith(self.refused(line)), found)
                for words in extra:
                    self.assertIn(words, found[0])

    def test_text_that_only_holds_an_import_is_not_refused(self):
        _, text = negative.BOOK_ZERO_TEXT
        self.assertEqual(self.findings(text), [])
        for text in ('def s := "\\" import Elements.BookI.Prop01"\n',
                     "def s := r#\"import Elements.BookI.Prop01\"#\n",
                     "def «import Elements.BookI.Prop01 » := 1\n",
                     "-- import Elements.BookI.Prop01\nimport Elements.Figure.Lines\n",
                     "/- /- -/ import Elements.BookI.Prop01 -/\n",
                     "theorem planted_import_ok : True := trivial\n",
                     "example := Lean.Parser.Module.import\n"):
            with self.subTest(text=text):
                self.assertEqual(self.findings(text), [])

    def test_a_comment_or_string_hides_no_import(self):
        for text, line in (("/- \" -/ import Elements.BookI.Prop01\n", 1),
                           ('def s := "/-"\nimport Elements.BookI.Prop01\n', 2),
                           ("-- a remark\n/-! A doc -/\nimport Elements.BookI.Prop01\n", 3),
                           ("import Elements.Figure.Lines -- a remark\n"
                            "import Elements.BookI.Prop01\n", 2),
                           # Lean reads these braces as text, but both readings end
                           # in one place, so read_lean keeps them as code (rule 4),
                           # failing closed.
                           ('def s := "{ import Elements.BookI.Prop01 }"\n', 1)):
            with self.subTest(text=text):
                self.assertEqual(self.findings(text), [self.refused(line)])

    def test_plain_imports_and_lean_s_own_pass(self):
        text = ("module\n\nprelude\npublic import Elements.Figure.Lines\n"
                "meta import  «Elements».«Foundations».Words\nimport all Init.Data.List.Basic\n")
        self.assertEqual(self.findings(text), [])

    def test_a_name_the_scan_cannot_read_is_refused(self):
        for text in ("import «Elements».«Book I».Prop01\n", "import «Elements.BookI».Prop01\n",
                     "import Elements.«».Prop01\n", "import Elements.Figure.Lines.\n",
                     "import Elements.«Figure»import Elements.BookI.Prop01\n", "import\n"):
            with self.subTest(text=text):
                found = self.findings(text)
                self.assertTrue(found and found[0].startswith(self.refused(1)), found)
                self.assertIn("cannot read this import for certain", found[0])

    def test_an_import_through_the_edition_s_files_is_refused(self):
        # Cycle.lean and Planted.lean import each other; Planted.lean brings in the rest.
        foundations = self.root / "Elements/Foundations"
        (foundations / "Cycle.lean").write_text("import Elements.Foundations.Planted\n")
        for planted, importer, brought in (
                ("import Elements.Companions\n", "Elements/Companions.lean",
                 "`Elements.BookI.Prop01`"),
                ("import «Elements/BookI».Prop01\n", "Elements/Foundations/Planted.lean",
                 "a module the scan cannot read for certain")):
            with self.subTest(planted=planted):
                (foundations / "Planted.lean").write_text(
                    "import Elements.Foundations.Cycle\n" + planted)
                self.assertEqual(self.findings("import Elements.Foundations.Cycle\n"),
                                 [f"{self.refused(1)}, and `Elements.Foundations.Cycle` brings "
                                  f"one in: {importer} imports {brought}"])

    def test_a_symlinked_module_directory_is_refused_without_reading_its_target(self):
        target = self.root / "Outside"
        target.mkdir()
        (target / "Bridge.lean").write_bytes(b"\xff")
        (self.root / "Elements/Alias").symlink_to(target, target_is_directory=True)
        self.assertEqual(self.findings("import Elements.Alias.Bridge\n"), [
            "Elements/Alias: a symbolic link, which the source scan does not follow; "
            "use a regular file or directory (docs/FORMALIZATION.md, section 7)",
            f"{self.refused(1)}, and `Elements.Alias.Bridge` reaches Elements/Alias, "
            "a symbolic link which the import scan does not follow",
        ])

    def test_a_root_module_symlink_is_refused_without_reading_its_target(self):
        target = self.root / "Outside.lean"
        target.write_bytes(b"\xff")
        (self.root / "Bridge.lean").symlink_to(target)
        self.assertEqual(self.findings("import Bridge\n"), [
            f"{self.refused(1)}, and `Bridge` reaches Bridge.lean, a symbolic link which "
            "the import scan does not follow",
        ])

    def test_a_transitive_symlinked_directory_outside_source_trees_is_refused(self):
        target = self.root / "Outside"
        target.mkdir()
        (target / "Hidden.lean").write_bytes(b"\xff")
        (self.root / "Support").symlink_to(target, target_is_directory=True)
        (self.root / "Bridge.lean").write_text("import Support.Hidden\n")
        self.assertEqual(self.findings("import Bridge\n"), [
            f"{self.refused(1)}, and `Bridge` reaches Support, a symbolic link which "
            "the import scan does not follow",
        ])

    def test_a_lone_carriage_return_in_a_followed_file_hides_no_import(self):
        # Bridge.lean, a root module the scan does not read for rule 4, read from its bytes
        # as Lean reads it: its `--` comment ends at the line feed, not at the lone `\r`, so
        # the quote after the `\r` opens no string, and the import on the next line is read.
        (self.root / "Bridge.lean").write_bytes(
            b'-- a remark\r"\nimport Elements.BookI.Prop01\n-- "\n')
        self.assertEqual(self.findings("import Bridge\n"), [
            f"{self.refused(1)}, and `Bridge` brings one in: Bridge.lean imports "
            "`Elements.BookI.Prop01`",
        ])

    def test_a_cycle_ends_and_files_outside_book_zero_may_import_propositions(self):
        (self.root / "Elements/Foundations/Words.lean").write_text(
            "import Elements.Figure.Lines\n")
        self.assertEqual(self.findings("import Elements.Figure.Lines\n"), [])
        self.assertEqual(self.findings("import Elements.BookI.Prop01\n",
                                       "Elements/BookI/Prop02.lean"), [])


class CommentReaderTests(unittest.TestCase):
    """The one reader of Lean comments that the scripts share, heath's `comment_end`
    (check_fidelity's until #349), read through `lean_comments` and `read_lean`, without Lean (#206): the
    texts on which a reader that began a block's body at its third character, or read no
    strings or character literals, could read otherwise than Lean 4.35. Each expected
    reading is Lean's: each text was elaborated in Lean 4.35 as written, alone in a scratch
    file outside the tree, where the names after its comments were defined, those within
    them unknown, and each of UNCLOSED refused as an unterminated comment. Then
    the three readers that call it, or a copy of it, check_fidelity's `_blank_remarks`,
    check_style's `lean_note_spans` and the Jev generator's `comment_end`, each read them
    so too."""

    # (a text, the comments Lean reads in it, in order, the names it defines and those it
    # does not, which stand within a comment)
    CASES = (
        ("/-/- -/ def after_slash_dash : Nat := 1\n", ["/-/- -/"], ["after_slash_dash"], []),
        ("/-/ x -/ def after_slash : Nat := 2\n", ["/-/ x -/"], ["after_slash"], []),
        ("/-/-/ def after_slash_dash_slash : Nat := 3\n", ["/-/-/"],
         ["after_slash_dash_slash"], []),
        ("/--/ def hidden_in_doc : Nat := 0 -/ def after_doc_slash : Nat := 4\n",
         ["/--/ def hidden_in_doc : Nat := 0 -/"], ["after_doc_slash"], ["hidden_in_doc"]),
        ("/-!/ x -/ def after_module_doc_slash : Nat := 5\n", ["/-!/ x -/"],
         ["after_module_doc_slash"], []),
        ("/- /- -/ def hidden_in_nested : Nat := 0 -/ def after_nested : Nat := 6\n",
         ["/- /- -/ def hidden_in_nested : Nat := 0 -/"], ["after_nested"],
         ["hidden_in_nested"]),
        ('def opener_in_string : String := "/-" def after_string : Nat := 7\n', [],
         ["opener_in_string", "after_string"], []),
        ('def closer_after_quote : Nat := 8 /- "-/ def after_quote : Nat := 9 -- "\n',
         ['/- "-/', '-- "'], ["closer_after_quote", "after_quote"], []),
        ("def dash_char : Char := '-'/- a remark -/ def after_dash_char : Nat := 10\n",
         ["/- a remark -/"], ["dash_char", "after_dash_char"], []),
        ("def slash_char : Char := '/'-- a remark\ndef after_slash_char : Nat := 11\n",
         ["-- a remark"], ["slash_char", "after_slash_char"], []),
        ("def quote_char : Char := '\"' /- \"-/ def after_quote_char : Nat := 12 -- \"\n",
         ['/- "-/', '-- "'], ["quote_char", "after_quote_char"], []),
        ("/- -- -/ def after_dashes_in_block : Nat := 13\n", ["/- -- -/"],
         ["after_dashes_in_block"], []),
        ("-- /-\ndef after_opener_in_line : Nat := 14\n", ["-- /-"],
         ["after_opener_in_line"], []),
        ('def in_hole : String := s!"{(1 : Nat) /- c -/}" def after_hole : Nat := 15\n',
         ["/- c -/"], ["in_hole", "after_hole"], []),
    )
    # Likewise, each with its last comment not closed, which runs to the end.
    UNCLOSED = (
        ("def before_unclosed : Nat := 1\n/- unclosed /- -/\ndef hidden_unclosed : Nat := 0\n",
         ["/- unclosed /- -/\ndef hidden_unclosed : Nat := 0\n"], ["before_unclosed"],
         ["hidden_unclosed"]),
        ("def before_bare : Nat := 1\n/-", ["/-"], ["before_bare"], []),
    )

    @classmethod
    def setUpClass(cls):
        import check_style
        cls.check_style = check_style
        spec = importlib.util.spec_from_file_location(
            "jev_questions_comment_reader", REPO / "scripts/audit/jev_questions.py")
        cls.questions = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = cls.questions
        cls.addClassCleanup(sys.modules.pop, spec.name, None)
        spec.loader.exec_module(cls.questions)

    def spans(self, text, comments):
        """Each of `comments`, read from `text` in order, as its offsets in it."""
        found, at = [], 0
        for comment in comments:
            at = text.index(comment, at)
            found.append((at, at + len(comment)))
            at += len(comment)
        return found

    def cases(self):
        """Each case, with its comments' offsets and whether its last comment is closed."""
        for (text, comments, defined, hidden), closed in (
                [(case, True) for case in self.CASES]
                + [(case, False) for case in self.UNCLOSED]):
            yield text, self.spans(text, comments), defined, hidden, closed

    def test_each_comment_ends_where_lean_ends_it(self):
        for text, spans, _, _, closed in self.cases():
            with self.subTest(text=text):
                self.assertEqual(negative.check_fidelity.lean_comments(text), spans)
                for start, end in spans[:None if closed else -1]:
                    self.assertEqual(negative.check_fidelity.comment_end(text, start), end)
                if not closed:
                    self.assertEqual(spans[-1][1], len(text))
                    self.assertIsNone(negative.check_fidelity.comment_end(text, spans[-1][0]))

    def test_read_lean_shows_the_names_lean_defines_and_no_other(self):
        for text, _, defined, hidden, _ in self.cases():
            with self.subTest(text=text):
                words = set(re.findall(r"\w+", negative.check_fidelity.read_lean(text)[0]))
                self.assertLessEqual(set(defined), words)
                self.assertFalse(set(hidden) & words)

    def test_plain_string_braces_create_no_speculative_comment(self):
        comment = "/- not_a_comment -/"
        text = f'def s : String := "{{ {comment} }}"\n'
        expected = text.replace(comment, " " * len(comment))
        strings = []
        self.assertEqual(negative.check_fidelity.lean_comments(text), [])
        self.assertEqual(negative.check_fidelity._blank_remarks(text), text)
        self.assertEqual(self.check_style.lean_note_spans(text), [])
        self.assertEqual(negative.check_fidelity.read_lean(text, strings), (expected, []))
        self.assertEqual(strings, [(text.index('"'), f"{{ {comment} }}")])

    def test_the_readers_that_call_it_read_each_case_so(self):
        for text, spans, _, _, closed in self.cases():
            blocks = [(i, j) for i, j in spans if text.startswith("/-", i)]
            remarks = list(text)
            for i, j in blocks:
                remarks[i:j] = ["\n" if ch == "\n" else " " for ch in text[i:j]]
            ended = spans if closed else spans[:-1]
            notes = [(i + (3 if text.startswith(("/--", "/-!"), i) else 2), j - 2)
                     for i, j in blocks if (i, j) in ended]
            with self.subTest(text=text):
                self.assertEqual(negative.check_fidelity._blank_remarks(text), "".join(remarks))
                self.assertEqual(self.check_style.lean_note_spans(text), notes)
                for i, j in ended:
                    self.assertEqual(self.questions.comment_end(text, i), j)
                if not closed:
                    with self.assertRaisesRegex(self.questions.Refusal, "unterminated"):
                        self.questions.comment_end(text, spans[-1][0])

    def test_the_jev_generator_s_reader_is_heath_s_word_for_word(self):
        # The generator reads the evidence commit's heath.py as a helper, which at an older
        # commit has no reader, so it holds a copy of heath.comment_end, word for word but
        # for the name (the coordinator's ruling of 23 October 05:20).
        def tree(path, name):
            module = ast.parse((REPO / path).read_text(encoding="utf-8"))
            found = [node for node in module.body
                     if isinstance(node, ast.FunctionDef) and node.name == name]
            self.assertEqual(len(found), 1, f"{path}: {name}")
            found[0].name = "comment_end"
            return ast.dump(found[0])
        self.assertEqual(tree("scripts/audit/jev_questions.py", "shared_comment_end"),
                         tree("scripts/heath.py", "comment_end"))

    def test_the_jev_generator_s_reader_reads_as_heath_s(self):
        # And it reads as heath's does, on a corpus of nested blocks, doc comments,
        # strings, character literals and «…» names.
        corpus = (
            "/-/- -/ import A", "/--/ x -/ y", "/-- doc -/ theorem t", "/-! module -/",
            "/- a /- nested /- deeper -/ -/ -/ after", "/- unclosed /- -/", "-- line\nnext",
            "-- last line", 'def s := "/- not a comment -/" -- but this is',
            "def c := '\"' /- after a character -/", "def c := '(' -- a bracket's character",
            "def «x /- y» := 1 /- -/", "/-/--/-/", "--/-\n/--\n-/", "/---/ -/", "",
        )
        heath = negative.check_fidelity.heath
        for text in corpus:
            for i in range(len(text)):
                if text.startswith(("--", "/-"), i):
                    with self.subTest(text=text, at=i):
                        self.assertEqual(self.questions.shared_comment_end(text, i),
                                         heath.comment_end(text, i))

    def test_the_jev_generator_delegates_to_heath_s_reader(self):
        source = "prefix /- comment -/ suffix"
        offset = source.index("/-")
        sentinel = object()
        with patch.object(self.questions, "shared_comment_end", return_value=sentinel) as shared:
            self.assertIs(self.questions.comment_end(source, offset), sentinel)
        shared.assert_called_once_with(source, offset)

        with patch.object(self.questions, "shared_comment_end", return_value=None) as shared:
            with self.assertRaisesRegex(self.questions.Refusal,
                                        r"^unterminated Lean comment$"):
                self.questions.comment_end(source, offset)
        shared.assert_called_once_with(source, offset)

    def test_check_fidelity_reads_lean_with_heath_s_reader_alone(self):
        # #349: the reader is heath's. check_fidelity imports it under the names it had,
        # the very objects, and defines none of them itself, so that no second reader can
        # drift apart from it; its own caller, _blank_remarks, reads comments through it.
        check_fidelity = negative.check_fidelity
        names = ("read_lean", "without_comments", "lean_comments", "comment_end", "_find",
                 "closed_up", "_read_code", "_read_string", "_read_interpolated",
                 "lean_string", "CHAR", "ESCAPE", "FIELD", "FIRST", "IDENT", "ID_FIRST",
                 "ID_REST", "INTERPOLATED", "LETTER_LIKE", "NAME_CHAR", "NAME_RUN",
                 "NON_ASCII", "NUMBER", "RAW", "REST", "SUBSCRIPT_ALNUM")
        for name in names:
            with self.subTest(name=name):
                self.assertIs(getattr(check_fidelity, name),
                              getattr(check_fidelity.heath, name))
        self.assertIs(check_fidelity.WORD, check_fidelity.heath.WORD_CHAR)
        # Nor does check_fidelity bind any of them itself, by a def or an assignment.
        source = (REPO / "scripts/check_fidelity.py").read_text(encoding="utf-8")
        defined = set()
        for node in ast.walk(ast.parse(source)):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                defined.add(node.name)
            elif isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                defined |= {n.id for target in targets for n in ast.walk(target)
                            if isinstance(n, ast.Name)}
        self.assertEqual(sorted(defined & set(names)), [])
        with patch.object(check_fidelity, "lean_comments",
                          wraps=check_fidelity.lean_comments) as read:
            check_fidelity._blank_remarks("theorem t : True := trivial -- a remark\n")
        read.assert_called_once()


PLANT = '''{doc}
import subprocess

import negative_tests as nt

{builds}


{plant}
'''
DOC = '"""A plant the loader\'s tests write."""'


def plant_source(name, *, doc=DOC, builds="BUILDS = False", body='nt.refused("{name}: caught")',
                 function=None, before=""):
    """A plant's file: it leaves planted-<name> in ROOT, so a test sees that it ran, and then
    does `body`; `before`, if given, is module-level code ahead of plant()."""
    if function is None:
        function = ("def plant() -> None:\n"
                    f'    (nt.ROOT / "planted-{name}").touch()\n'
                    f"    {body.format(name=name)}")
    if before:
        function = f"{before}\n\n\n{function}"
    return PLANT.format(doc=doc, builds=builds, plant=function)


def unchecked_bytecode(source, cfile):
    """Compile `source` to `cfile` as bytecode that Python's import never compares with the
    source beside it (an unchecked hash), the bytecode a plant's or the runner's could be."""
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "stand_in.py"
        path.write_text(source)
        Path(cfile).parent.mkdir(parents=True, exist_ok=True)
        py_compile.compile(str(path), cfile=str(cfile), doraise=True,
                           invalidation_mode=py_compile.PycInvalidationMode.UNCHECKED_HASH)


class LoaderTests(unittest.TestCase):
    """The loader of scripts/negative/, and main() around it, on temporary folders of small
    plants, without Lean or Git: `run` is a stand-in that passes, so the regressions, the
    Git bracket and the final check are calls it records."""

    def setUp(self):
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        self.folder = self.root / "scripts/negative"
        self.folder.mkdir(parents=True)
        self.enterContext(patch.multiple(negative, ROOT=self.root, failures=[]))
        self.calls = []
        self.fidelity = 0

        def run(*cmd):
            self.calls.append(cmd)
            code = self.fidelity if cmd[1:] == ("scripts/check_fidelity.py",) else 0
            return subprocess.CompletedProcess(cmd, code, "", "")
        self.enterContext(patch.object(negative, "run", side_effect=run))
        self.output = self.enterContext(redirect_stdout(io.StringIO()))

    def write(self, name, text):
        (self.folder / name).write_text(text)

    def reset(self):
        for path in (self.root / "scripts", self.folder):
            if path.is_symlink():
                path.unlink()
        if (self.root / "elsewhere").exists():
            shutil.rmtree(self.root / "elsewhere")
        if self.folder.is_dir():
            shutil.rmtree(self.folder)
        else:
            self.folder.unlink(missing_ok=True)
        self.folder.mkdir(parents=True)
        for path in self.root.glob("planted-*"):
            path.unlink()
        negative.failures.clear()
        self.calls.clear()
        self.output.truncate(0)
        self.output.seek(0)

    def planted(self):
        return sorted(p.name.removeprefix("planted-") for p in self.root.glob("planted-*"))

    def git_status(self):
        return [cmd for cmd in self.calls if cmd[:2] == ("git", "status")]

    def assert_refused_before_planting(self, *faults):
        """main() fails on `faults`, each the start of a failure, with nothing planted and no
        closing check of the unplanted tree; the entry Git status, taken before loading, is
        compared once more at the end."""
        self.assertEqual(negative.main(), 1)
        self.assertEqual(len(negative.failures), len(faults), negative.failures)
        for fault, failure in zip(faults, negative.failures):
            self.assertTrue(failure.startswith(fault), f"{failure!r} for {fault!r}")
            self.assertIn(f"✗ {failure}\n", self.output.getvalue())
        self.assertIn("loading the plants (scripts/negative/):\n  ✗ " + negative.failures[0],
                      self.output.getvalue())
        self.assertEqual(self.planted(), [])
        self.assertEqual(len(self.git_status()), 2)
        self.assertNotIn((sys.executable, "scripts/check_fidelity.py"), self.calls)

    def test_the_stable_order(self):
        for name, builds in (("zeta", False), ("alpha", True), ("beta", False),
                             ("gamma", True), ("a1_b", False)):
            self.write(f"{name}.py", plant_source(name, builds=f"BUILDS = {builds}"))
        plants, faults = negative.load_plants()
        self.assertEqual(faults, [])
        order = [("a1_b", False), ("beta", False), ("zeta", False), ("alpha", True),
                 ("gamma", True)]
        self.assertEqual([(p.name, p.builds) for p in plants], order)
        self.assertEqual(plants[0].path, self.folder / "a1_b.py")
        self.assertEqual(plants[0].description, "A plant the loader's tests write.")
        again, faults = negative.load_plants(self.folder)
        self.assertEqual([p[:4] for p in again], [p[:4] for p in plants])
        self.assertEqual(faults, [])
        self.assertEqual(negative.main(), 0)
        output = self.output.getvalue()
        headings = [output.index(f"\n{name} (scripts/negative/{name}.py)\n") for name, _ in order]
        self.assertEqual(headings, sorted(headings))
        for name, _ in order:
            self.assertRegex(output, rf"\n  {name}: \d+\.\d\ds \(including restoration\)\n")
        self.assertEqual(self.planted(), sorted(name for name, _ in order))
        self.assertEqual(len(self.git_status()), 2)

    def test_each_fault_fails_main_with_nothing_planted(self):
        def file(text=""):
            return lambda path: path.write_text(text)

        def link(target):
            return lambda path: path.symlink_to(target)

        def directory(path):
            path.mkdir()

        name = "not a plant's file name, which is [a-z][a-z0-9_]*.py"
        unloaded = "does not load: "
        cases = [
            ("Capital.py", file(plant_source("Capital")), name),
            ("1st.py", file(plant_source("1st")), name),
            ("with-dash.py", file(plant_source("dash")), name),
            ("_private.py", file(plant_source("private")), name),
            ("notes.txt", file("notes"), name),
            ("good.py.orig", file(plant_source("orig")), name),
            ("README", file("A folder of plants."), name),
            ("__pycache__", file(), name),
            (".good.py.swp", file("an editor's swap file"), name),
            (".DS_Store", directory, "a directory, not a plant's file"),
            (".DS_Store", link(self.folder / "good.py"), "a symbolic link, which is not read"),
            ("linked.py", link(self.folder / "good.py"), "a symbolic link, which is not read"),
            ("dangling.py", link(self.root / "missing.py"), "a symbolic link, which is not read"),
            ("cached", link(self.root), "a symbolic link, which is not read"),
            ("nested", directory, "a directory, not a plant's file"),
            ("nested.py", directory, "a directory, not a plant's file"),
            ("broken.py", file(plant_source("broken", function="def plant(:\n    pass")),
             unloaded + "SyntaxError: "),
            ("raises.py", file(DOC + '\nraise RuntimeError("raised on import")\n'),
             unloaded + "RuntimeError: raised on import"),
            ("exits.py", file(DOC + "\nimport sys\nsys.exit(3)\n"), unloaded + "SystemExit: 3"),
            ("imports.py", file(DOC + "\nimport no_such_module_for_a_plant\n"),
             unloaded + "ModuleNotFoundError: "),
            ("undescribed.py", file(plant_source("undescribed", doc="")), "no description"),
            ("blank.py", file(plant_source("blank", doc='"""  \n  """')), "no description"),
            ("unbuilt.py", file(plant_source("unbuilt", builds="")), "no BUILDS"),
            ("one.py", file(plant_source("one", builds="BUILDS = 1")),
             "BUILDS is 1, not True or False"),
            ("words.py", file(plant_source("words", builds='BUILDS = "False"')),
             "BUILDS is 'False', not True or False"),
            ("nothing.py", file(plant_source("nothing", builds="BUILDS = None")),
             "BUILDS is None, not True or False"),
            ("plantless.py", file(plant_source("plantless", function="")), "no plant()"),
            ("uncallable.py", file(plant_source("uncallable", function='plant = "plant"')),
             "plant is str, not a function"),
            ("argued.py", file(plant_source("argued", function="def plant(where):\n    pass")),
             "plant() must take no arguments"),
            ("keyword.py",
             file(plant_source("keyword", function="def plant(*, where):\n    pass")),
             "plant() must take no arguments"),
        ]
        for entry, make, reason in cases:
            with self.subTest(entry=entry, reason=reason):
                self.reset()
                self.write("good.py", plant_source("good"))
                make(self.folder / entry)
                self.assert_refused_before_planting(f"scripts/negative/{entry}: {reason}")
        with self.subTest(entry="several faults in one file"):
            self.reset()
            self.write("bare.py", plant_source("bare", doc="", builds="", function=""))
            self.assert_refused_before_planting(
                "scripts/negative/bare.py: no description", "scripts/negative/bare.py: no BUILDS",
                "scripts/negative/bare.py: no plant()")

    def test_a_missing_or_empty_folder_fails_main(self):
        cases = [("missing", lambda: self.folder.rmdir(),
                  "scripts/negative: the plants' folder cannot be listed (FileNotFoundError"),
                 ("a file", lambda: (self.folder.rmdir(), self.folder.write_text("")),
                  "scripts/negative: the plants' folder cannot be listed (NotADirectoryError"),
                 ("empty", lambda: None, "scripts/negative: no plants"),
                 ("only __pycache__", lambda: (self.folder / "__pycache__").mkdir(),
                  "scripts/negative: no plants"),
                 ("only .DS_Store", lambda: (self.folder / ".DS_Store").write_bytes(b"\0"),
                  "scripts/negative: no plants")]
        linked = ("scripts/negative: the plants' folder is, or passes through, a symbolic "
                  "link")

        def a_linked_folder():
            elsewhere = self.root / "elsewhere"
            elsewhere.mkdir()
            (elsewhere / "good.py").write_text(plant_source("good"))
            self.folder.rmdir()
            self.folder.symlink_to(elsewhere, target_is_directory=True)

        def a_linked_scripts_folder():
            scripts = self.root / "scripts"
            elsewhere = self.root / "elsewhere"
            scripts.rename(elsewhere)
            (elsewhere / "negative/good.py").write_text(plant_source("good"))
            scripts.symlink_to(elsewhere, target_is_directory=True)

        cases += [("a link", a_linked_folder, linked),
                  ("in a linked scripts/", a_linked_scripts_folder, linked)]
        for what, make, fault in cases:
            with self.subTest(folder=what):
                self.reset()
                make()
                self.assert_refused_before_planting(fault)
        with self.subTest(folder="an entry that resolves outside it"):
            # As if the entry became a link after it was looked at: the loader still reads
            # only a file directly in the folder.
            self.reset()
            (self.root / "elsewhere").mkdir()
            (self.root / "elsewhere/outside.py").write_text(plant_source("outside"))
            (self.folder / "outside.py").symlink_to(self.root / "elsewhere/outside.py")
            with patch.object(Path, "is_symlink", lambda path: False):
                self.assert_refused_before_planting(
                    f"scripts/negative/outside.py: resolves to {self.root}/elsewhere/outside.py, "
                    "which is not directly in the plants' folder")
        self.reset()

    def test_pycache_and_ds_store_are_passed_over(self):
        self.write("good.py", plant_source("good"))
        (self.folder / "__pycache__").mkdir()
        (self.folder / "__pycache__/stale.cpython-312.pyc").write_bytes(b"not a plant")
        (self.folder / ".DS_Store").write_bytes(b"\0\0\0\1Bud1")
        plants, faults = negative.load_plants()
        self.assertEqual(([p.name for p in plants], faults), (["good"], []))
        self.assertIn("note: scripts/negative/.DS_Store passed over: Finder's settings for "
                      "the folder, which Git ignores, not a plant\n", self.output.getvalue())

    def test_a_plant_is_compiled_from_its_text_never_from_bytecode(self):
        """Bytecode beside a plant, which Python's import would run without comparing it
        with the source, is not read: the plant is the file's text."""
        self.write("good.py", plant_source("good"))
        unchecked_bytecode(plant_source("good", doc='"""From bytecode."""',
                                        builds="BUILDS = True"),
                           importlib.util.cache_from_source(str(self.folder / "good.py")))
        plants, faults = negative.load_plants()
        self.assertEqual(faults, [])
        self.assertEqual([(p.name, p.description, p.builds) for p in plants],
                         [("good", "A plant the loader's tests write.", False)])

    def test_a_plant_that_exits_fails_and_the_run_goes_on(self):
        self.write("a_exits.py", plant_source("a_exits", before="import sys",
                                              body='nt.refused("{name}: caught"); sys.exit(0)'))
        self.write("b_later.py", plant_source("b_later"))
        self.assertEqual(negative.main(), 1)
        message = "a_exits: plant() exited (0) instead of returning"
        self.assertEqual(negative.failures, [message])
        self.assertIn(f"a_exits (scripts/negative/a_exits.py):\n  ✗ {message}\n",
                      self.output.getvalue())
        self.assertEqual(self.planted(), ["a_exits", "b_later"])
        self.assertIn((sys.executable, "scripts/check_fidelity.py"), self.calls)
        self.assertEqual(len(self.git_status()), 2)

    def test_a_run_that_stops_short_of_its_plants_fails(self):
        """A plant that empties the runner's list of chosen plants stops the loop early;
        the run counts the plants it ran against those chosen."""
        self.write("a_clears.py", plant_source("a_clears", before="import sys", body=(
            'nt.refused("{name}: caught"); sys._getframe(2).f_locals["chosen"].clear()')))
        self.write("b_never.py", plant_source("b_never"))
        self.assertEqual(negative.main(), 1)
        self.assertEqual(negative.failures, ["only 1 of the 2 plants chosen were run"])
        self.assertEqual(self.planted(), ["a_clears"])

    def test_a_file_that_changes_a_shared_name_fails_by_name(self):
        """A plant's file may not rebind or delete a name of the runner, nor of the modules
        it shares, nor add one to the runner, as it loads or as its plant() runs; the name is
        put back, so the plants after it are judged by the runner's own helpers."""
        expect_failure = negative.expect_failure
        check_lock = negative.check_fidelity.check_lock
        # Each name is put back by these too, should the guard fail, so no later test meets
        # a changed one.
        for module, name in ((negative, "expect_failure"), (negative, "PLANT_FILE"),
                             (negative.check_fidelity, "check_lock"), (negative.heath, "ROOT")):
            self.enterContext(patch.object(module, name, getattr(module, name)))
        self.addCleanup(lambda: vars(negative).pop("planted_name", None))
        fake = "lambda *args, **kwargs: nt.refused('faked')"
        later = plant_source("b_later", body=(
            'nt.expect_failure("a check that passes", subprocess.CompletedProcess('
            '[], 0, "", ""))'))
        put_back = ("(put back); a plant leaves the names it shares with the runner as it "
                    "finds them")
        with self.subTest(when="as it loads"):
            self.reset()
            self.write("good.py", plant_source("good"))
            self.write("rebinds.py", plant_source("rebinds", before=f"nt.expect_failure = {fake}"))
            self.assert_refused_before_planting(
                "scripts/negative/rebinds.py: rebinds negative_tests.expect_failure as it loads "
                + put_back)
            self.assertIs(negative.expect_failure, expect_failure)
        for change, reason in (
                (f"nt.expect_failure = {fake}", "rebinds negative_tests.expect_failure"),
                ("nt.check_fidelity.check_lock = lambda *args: 0",
                 "rebinds check_fidelity.check_lock"),
                ("nt.failures = []", "rebinds negative_tests.failures"),
                ("nt.planted_name = 1", "adds negative_tests.planted_name"),
                ("del nt.PLANT_FILE", "deletes negative_tests.PLANT_FILE"),
                ("del nt.heath.ROOT", "deletes heath.ROOT")):
            with self.subTest(when="as it runs", change=change):
                self.reset()
                failures = negative.failures
                self.write("a_changes.py", plant_source("a_changes", body=change))
                self.write("b_later.py", later)
                self.assertEqual(negative.main(), 1)
                message = (f"a_changes: scripts/negative/a_changes.py {reason} as it runs "
                           f"{put_back}")
                self.assertIs(negative.failures, failures)
                self.assertEqual(negative.failures,
                                 [message, "a check that passes: not caught"])
                self.assertIn(f"a_changes (scripts/negative/a_changes.py):\n  ✗ {message}\n",
                              self.output.getvalue())
                self.assertEqual(self.planted(), ["a_changes", "b_later"])
                self.assertIs(negative.expect_failure, expect_failure)
                self.assertIs(negative.check_fidelity.check_lock, check_lock)
                self.assertFalse(hasattr(negative, "planted_name"))
                self.assertTrue(hasattr(negative, "PLANT_FILE"))
                self.assertEqual(negative.heath.ROOT, REPO)
        with self.subTest(when="a name added to a shared module"):
            self.reset()
            self.addCleanup(lambda: vars(negative.check_fidelity).pop("planted_name", None))
            self.write("adds.py", plant_source("adds", body=(
                'nt.check_fidelity.planted_name = 1; nt.refused("{name}: caught")')))
            self.assertEqual(negative.main(), 0)
            self.assertEqual(negative.failures, [])

    def test_a_name_changed_by_the_closing_check_fails(self):
        """The names are looked at once more after the closing check of the unplanted tree,
        so a change made after the last plant's guard, as by a hook that a file left as it
        loaded, fails the run, and the name is put back."""
        check_lock = negative.check_fidelity.check_lock
        self.enterContext(patch.object(negative.check_fidelity, "check_lock", check_lock))

        def run(*cmd):
            self.calls.append(cmd)
            if cmd[1:] == ("scripts/check_fidelity.py",):
                negative.check_fidelity.check_lock = lambda *args: 0
            return subprocess.CompletedProcess(cmd, 0, "", "")
        self.write("good.py", plant_source("good"))
        with patch.object(negative, "run", side_effect=run):
            self.assertEqual(negative.main(), 1)
        message = ("rebinds check_fidelity.check_lock after the closing check (put back); a "
                   "plant leaves the names it shares with the runner as it finds them")
        self.assertEqual(negative.failures, [message])
        self.assertIn(f"outside any plant:\n  ✗ {message}\n", self.output.getvalue())
        self.assertIs(negative.check_fidelity.check_lock, check_lock)

    def test_a_plant_that_changes_earlier_failures_or_refusals_fails(self):
        """The failures and refusals recorded before a plant only grow: a plant() that
        clears the failures, or pops a refusal, fails by its name, and the earlier entries
        are put back, so the closing list still holds the earlier failure."""
        earlier = ('nt.refused("{name}: caught"); nt.expect_failure("a check that passes", '
                   'subprocess.CompletedProcess([], 0, "", ""))')
        message = "b_changes: changed the failures or refusals recorded before it"
        for change in ("nt.failures.clear()", "nt.refusals.pop()"):
            with self.subTest(change=change):
                self.reset()
                refusals = len(negative.refusals)
                self.write("a_earlier.py", plant_source("a_earlier", body=earlier))
                self.write("b_changes.py", plant_source("b_changes", body=(
                    change + '; nt.refused("{name}: caught")')))
                self.write("c_later.py", plant_source("c_later"))
                self.assertEqual(negative.main(), 1)
                self.assertEqual(negative.failures, ["a check that passes: not caught", message])
                self.assertEqual(negative.refusals[refusals], "a_earlier: caught")
                self.assertTrue(self.output.getvalue().endswith(
                    "2 negative-test failure(s):\n"
                    "a_earlier (scripts/negative/a_earlier.py):\n"
                    "  ✗ a check that passes: not caught\n"
                    f"b_changes (scripts/negative/b_changes.py):\n  ✗ {message}\n"))
                self.assertEqual(self.planted(), ["a_earlier", "b_changes", "c_later"])

    def test_a_warning_recorded_against_the_runner_is_passed_over(self):
        """Python's warnings machinery adds `__warningregistry__` to the module a warning is
        attributed to, ignored warnings too, so the guard passes over that one name
        (UNGUARDED): a plant whose helper raises a warning is not refused for it."""
        vars(negative).pop("__warningregistry__", None)
        self.addCleanup(lambda: vars(negative).pop("__warningregistry__", None))
        self.write("warns.py", plant_source("warns", before="import warnings", body=(
            'warnings.warn_explicit("probe", UserWarning, "negative_tests.py", 1, '
            'registry=vars(nt).setdefault("__warningregistry__", {{}})); '
            'nt.refused("{name}: caught")')))
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            self.assertEqual(negative.main(), 0)
        self.assertEqual(negative.failures, [])
        self.assertIn("__warningregistry__", vars(negative))

    def test_the_entry_git_status_comes_first_of_all(self):
        """The restoration regressions load the real plants' folder, so the entry Git status
        is taken before them, as main()'s first command."""
        self.write("good.py", plant_source("good"))
        self.assertEqual(negative.main(), 0)
        self.assertEqual(self.calls[0], ("git", "status", "--porcelain"))
        self.assertEqual(self.calls[1], (sys.executable, "-I", "tests/test_negative_tests.py"))

    def test_a_file_written_as_a_plant_loads_shows(self):
        """The entry Git status is taken before the plants' files are read, so a file that
        one writes as it loads is a change the closing comparison sees."""
        def run(*cmd):
            self.calls.append(cmd)
            written = sorted(p.name for p in self.root.glob("written-*"))
            status = cmd[:2] == ("git", "status")
            out = "".join(f"?? {name}\n" for name in written) if status else ""
            return subprocess.CompletedProcess(cmd, 0, out, "")
        self.write("writes.py", plant_source("writes", before=(
            '(nt.ROOT / "written-as-it-loads").touch()')))
        with patch.object(negative, "run", side_effect=run):
            self.assertEqual(negative.main(), 1)
        self.assertEqual(negative.failures,
                         ["the working tree did not return to its entry Git status"])
        self.assertIn("?? written-as-it-loads\n", self.output.getvalue())

    def test_a_plant_that_refuses_nothing_fails_by_name(self):
        self.write("quiet.py", plant_source("quiet", body='print("✓ a control, not a refusal")'))
        self.write("loud.py", plant_source("loud"))
        self.assertEqual(negative.main(), 1)
        message = "quiet: nothing refused what scripts/negative/quiet.py planted"
        self.assertEqual(negative.failures, [message])
        self.assertIn(f"✗ {message}\n", self.output.getvalue())
        self.assertIn(f"quiet (scripts/negative/quiet.py):\n  ✗ {message}\n",
                      self.output.getvalue())
        self.assertEqual(self.planted(), ["loud", "quiet"])
        self.assertEqual(len(self.git_status()), 2)

    def test_a_plant_whose_check_passes_fails(self):
        self.write("passes.py", plant_source("passes", body=(
            'nt.expect_failure("a check that passes", subprocess.CompletedProcess('
            '[], 0, "", ""), "refused")')))
        self.assertEqual(negative.main(), 1)
        message = "a check that passes: not caught (missing 'refused')"
        self.assertEqual(negative.failures, [message])
        self.assertIn(f"passes (scripts/negative/passes.py):\n  ✗ {message}\n",
                      self.output.getvalue())

    def test_a_plant_that_records_a_refusal_passes(self):
        self.write("caught.py", plant_source("caught", body=(
            'nt.expect_failure("a check that fails", subprocess.CompletedProcess('
            '[], 1, "refused here", ""), "refused")')))
        self.write("judged.py", plant_source("judged", body='nt.refused("judged by hand")'))
        refusals = len(negative.refusals)
        self.assertEqual(negative.main(), 0)
        self.assertEqual(negative.failures, [])
        self.assertEqual(negative.refusals[refusals:], ["a check that fails: caught",
                                                        "judged by hand"])
        for line in ("✓ a check that fails: caught\n", "✓ judged by hand\n",
                     "✓ the unplanted tree passes check_fidelity.py\n"):
            self.assertIn(line, self.output.getvalue())
        self.assertTrue(self.output.getvalue().endswith(
            "2 of 2 plants run\n✓ every planted change was caught\n"))

    def test_failures_outside_a_plant_have_a_heading_of_their_own(self):
        self.write("passes.py", plant_source("passes", body=(
            'nt.expect_failure("a check that passes", subprocess.CompletedProcess('
            '[], 0, "", ""))')))
        self.fidelity = 1
        self.assertEqual(negative.main(), 1)
        self.assertEqual(negative.failures, ["a check that passes: not caught",
                                             "the unplanted tree failed check_fidelity.py"])
        self.assertTrue(self.output.getvalue().endswith(
            "2 negative-test failure(s):\n"
            "passes (scripts/negative/passes.py):\n  ✗ a check that passes: not caught\n"
            "outside any plant:\n  ✗ the unplanted tree failed check_fidelity.py\n"))

    def test_plant_option(self):
        for name in ("one", "two", "three"):
            self.write(f"{name}.py", plant_source(name))
        self.assertEqual(negative.main(["--plant", "two", "--plant", "one"]), 0)
        self.assertEqual(self.planted(), ["one", "two"])
        self.assertEqual(len(self.git_status()), 2)
        self.assertEqual(self.calls[-2], (sys.executable, "scripts/check_fidelity.py"))
        output = self.output.getvalue()
        self.assertLess(output.index("\none (scripts/negative/one.py)\n"),
                        output.index("\ntwo (scripts/negative/two.py)\n"))
        self.assertTrue(output.endswith("✓ every change planted by 2 of the 3 plants was "
                                        "caught; the others were not run (--plant)\n"))
        self.assertNotIn("every planted change was caught", output)
        with self.subTest(names="all three"):
            self.reset()
            for name in ("one", "two", "three"):
                self.write(f"{name}.py", plant_source(name))
            self.assertEqual(negative.main(["--plant", "one", "--plant", "two",
                                            "--plant", "three"]), 0)
            self.assertTrue(self.output.getvalue().endswith(
                "3 of 3 plants run\n✓ every planted change was caught\n"))
        for known, unknown in ((["one", "nine"], "'nine'"), (["ten", "nine"], "'ten', 'nine'")):
            with self.subTest(names=known):
                for path in self.root.glob("planted-*"):
                    path.unlink()
                self.calls.clear()
                errors = io.StringIO()
                with redirect_stderr(errors), self.assertRaises(SystemExit) as raised:
                    negative.main([arg for name in known for arg in ("--plant", name)])
                self.assertEqual(raised.exception.code, 2)
                self.assertIn(f"no plant {unknown} in scripts/negative/; the plants are one, "
                              "three, two", errors.getvalue())
                self.assertEqual(self.planted(), [])
                # The entry status is taken before loading, and compared again on the exit.
                self.assertEqual(len(self.git_status()), 2)
                self.assertNotIn((sys.executable, "scripts/check_fidelity.py"), self.calls)
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
            negative.main(["--plant", "one", "--counts-only"])
        self.assertEqual(raised.exception.code, 2)
        self.assertEqual(self.planted(), [])

    def test_counts_only_runs_count_markers_alone_without_git(self):
        self.write("count_markers.py", plant_source("count_markers"))
        self.write("other.py", plant_source("other"))
        self.assertEqual(negative.main(["--counts-only"]), 0)
        self.assertEqual(self.planted(), ["count_markers"])
        self.assertEqual(self.git_status(), [])
        self.assertTrue(self.output.getvalue().endswith(
            "✓ count plants passed; other plants were not run (--counts-only)\n"))

    def test_the_real_plants_load(self):
        folder = REPO / "scripts" / "negative"
        plants, faults = negative.load_plants(folder)
        self.assertEqual(faults, [])
        names = [p.name for p in plants]
        self.assertEqual(len(names), len(set(names)))
        passed_over = {"__pycache__", ".DS_Store"}
        self.assertEqual(sorted(names), sorted(path.stem for path in folder.iterdir()
                                               if path.name not in passed_over))
        self.assertEqual(plants, sorted(plants, key=lambda p: (p.builds, p.name)))
        for p in plants:
            self.assertEqual(p.path, folder / f"{p.name}.py")
            self.assertTrue(p.description)


PROBE = '''"""A probe: is this plant's nt the module whose run_plant is running it?"""
import sys

import negative_tests as nt

BUILDS = False


def plant() -> None:
    frame = sys._getframe(1)
    while frame.f_code.co_name != "run_plant":
        frame = frame.f_back
    print(f"shared: {frame.f_globals is vars(nt)}; running: {nt is sys.modules['__main__']}")
    nt.refused("the probe: caught")
'''


class ScriptTests(unittest.TestCase):
    """The suite run as a script, as CI runs it, in a temporary copy of scripts/ whose
    regressions are empty stand-ins and whose one plant is a probe, named count_markers so
    that --counts-only runs it without Git or Lean."""

    def test_the_plants_share_the_running_module_and_no_bytecode_runs(self):
        root = Path(self.enterContext(tempfile.TemporaryDirectory()))
        (root / "scripts/negative").mkdir(parents=True)
        for path in (REPO / "scripts").glob("*.py"):
            shutil.copyfile(path, root / "scripts" / path.name)
        (root / "tests").mkdir()
        for _, rel in negative.REGRESSIONS:
            (root / rel).write_text("")
        probe = root / "scripts/negative/count_markers.py"
        probe.write_text(PROBE)
        # Bytecode that Python's import would run in place of the runner's source, were the
        # file imported a second time, or of the plant's, were it imported at all.
        stand_in = 'print("{}: a stand-in from bytecode")\nraise SystemExit(0)\n'
        unchecked_bytecode(stand_in.format("runner"), importlib.util.cache_from_source(
            str(root / "scripts/negative_tests.py")))
        unchecked_bytecode(stand_in.format("plant"),
                           importlib.util.cache_from_source(str(probe)))
        env = {k: v for k, v in os.environ.items() if not k.startswith("PYTHON")}
        result = subprocess.run([sys.executable, "scripts/negative_tests.py", "--counts-only"],
                                cwd=root, env=env, capture_output=True, text=True, timeout=300)
        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, 0, output)
        self.assertNotIn("a stand-in from bytecode", output)
        self.assertIn("shared: True; running: True\n✓ the probe: caught\n", result.stdout)
        self.assertTrue(result.stdout.endswith(
            "✓ count plants passed; other plants were not run (--counts-only)\n"), output)


class DealTests(unittest.TestCase):
    """The deal of the plants to the workers, longest first, and the record of their times,
    tests/negative_times.json, which `--times-from-log` writes."""

    def plants(self, *names, builds=()):
        """Stand-in plants, in the order given, which the caller gives as the stable one."""
        return [negative.Plant(name, Path(f"scripts/negative/{name}.py"), "A stand-in.",
                               name in builds, lambda: None) for name in names]

    def names(self, shares):
        return [[p.name for p in share] for share in shares]

    def test_longest_first(self):
        shares, loads = negative.deal(self.plants("a", "b", "c", "d"), 2,
                                      {"a": 1.0, "b": 10.0, "c": 5.0, "d": 4.0})
        self.assertEqual(self.names(shares), [["b"], ["a", "c", "d"]])
        self.assertEqual(loads, [10.0, 10.0])

    def test_a_plant_with_no_time_weighs_the_median(self):
        """x weighs 6, the median, and so goes beside b; weighing nothing, it would go with
        a beside c."""
        shares, loads = negative.deal(self.plants("a", "b", "c", "x"), 2,
                                      {"a": 1.0, "b": 6.0, "c": 8.0})
        self.assertEqual(self.names(shares), [["a", "c"], ["b", "x"]])
        self.assertEqual(loads, [9.0, 12.0])

    def test_with_no_record_every_plant_weighs_the_same(self):
        shares, loads = negative.deal(self.plants("a", "b", "c", "d", builds=("c", "d")), 2, {})
        self.assertEqual(self.names(shares), [["a", "c"], ["b", "d"]])
        self.assertEqual(loads, [2.0, 2.0])

    def test_a_plant_that_builds_goes_first_on_a_tie(self):
        shares, _ = negative.deal(self.plants("a", "b", "c", builds=("c",)), 3,
                                  {"a": 5.0, "b": 5.0, "c": 5.0})
        self.assertEqual(self.names(shares), [["c"], ["a"], ["b"]])

    def test_every_chosen_plant_is_dealt_exactly_once(self):
        plants, faults = negative.load_plants(REPO / "scripts" / "negative")
        self.assertEqual(faults, [])
        plants += self.plants("unrecorded_one", "unrecorded_two")
        recorded = json.loads((REPO / negative.TIMES).read_text())["seconds"]
        for seconds in (recorded, {}):
            for count in (1, 2, 4, 8, len(plants)):
                with self.subTest(count=count, record=bool(seconds)):
                    shares, loads = negative.deal(plants, count, seconds)
                    self.assertEqual(len(shares), count)
                    dealt = [p for share in shares for p in share]
                    self.assertEqual(sorted(p.name for p in dealt), sorted(p.name for p in plants))
                    for share in shares:
                        self.assertTrue(share)
                        self.assertEqual(share, [p for p in plants if p in share])
                    median = statistics.median(seconds.values()) if seconds else 1.0
                    self.assertAlmostEqual(sum(loads),
                                           sum(seconds.get(p.name, median) for p in plants))

    def test_the_record_reads(self):
        data = json.loads((REPO / negative.TIMES).read_text())
        self.assertEqual(list(data), ["about", "seconds"])
        self.assertIn("--times-from-log", data["about"])
        self.assertEqual(list(data["seconds"]), sorted(data["seconds"]))
        for name, seconds in data["seconds"].items():
            self.assertRegex(name, r"\A[a-z][a-z0-9_]*\Z")
            self.assertIsInstance(seconds, (int, float))
            self.assertGreaterEqual(seconds, 0)
            self.assertEqual(round(seconds, 1), seconds)

    def test_recorded_times_without_a_record_or_with_one_unread(self):
        root = Path(self.enterContext(tempfile.TemporaryDirectory()))
        self.enterContext(patch.object(negative, "ROOT", root))
        self.assertEqual(negative.recorded_times(), {})
        (root / "tests").mkdir()
        (root / negative.TIMES).write_text('{"about": "", "seconds": {"a": 1.5}}')
        self.assertEqual(negative.recorded_times(), {"a": 1.5})
        errors = io.StringIO()
        (root / negative.TIMES).write_text('{"about": "", "seconds": ["a"]}')
        with redirect_stderr(errors):
            self.assertEqual(negative.recorded_times(), {})
        self.assertIn("note: tests/negative_times.json cannot be read (AttributeError: ",
                      errors.getvalue())

    def test_times_from_log(self):
        root = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        self.enterContext(patch.object(negative, "ROOT", root))
        (root / "tests").mkdir()
        (root / "logs/20261028-run").mkdir(parents=True)
        log = root / "logs/20261028-run/negative.log"
        log.write_text("zeta (scripts/negative/zeta.py)\n"
                       "  zeta: 12.34s (including restoration)\n"
                       "alpha (scripts/negative/alpha.py)\n"
                       "✓ alpha: caught\n"
                       "  alpha: 0.04s (including restoration)\n"
                       "  not a plant: 1.00s (including restoration)\n"
                       "2 of 2 plants run\n")
        output = io.StringIO()
        with redirect_stdout(output):
            self.assertEqual(negative.main(["--times-from-log", str(log)]), 0)
        data = json.loads((root / negative.TIMES).read_text())
        self.assertEqual(data["seconds"], {"alpha": 0.0, "zeta": 12.3})
        self.assertEqual(list(data["seconds"]), ["alpha", "zeta"])
        self.assertIn("from the time lines of 2 plants in the log 20261028-run/negative.log.",
                      data["about"])
        self.assertEqual(output.getvalue(), "Wrote tests/negative_times.json: 2 plants.\n")
        for text, reason in (("  zeta: 1.00s (including restoration)\n" * 2,
                              "times zeta more than once"),
                             ("no time lines\n", "holds no plant's time line")):
            with self.subTest(reason=reason):
                (root / negative.TIMES).unlink(missing_ok=True)
                log.write_text(text)
                errors = io.StringIO()
                with redirect_stderr(errors):
                    self.assertEqual(negative.main(["--times-from-log", str(log)]), 1)
                self.assertIn(reason, errors.getvalue())
                self.assertFalse((root / negative.TIMES).exists())


class WorkerOptionTests(unittest.TestCase):
    """--workers and STOICHEIA_NEGATIVE_WORKERS, in process, on a temporary folder of three
    plants: `run` is a stand-in that passes, and run_workers one that records the workers it
    is asked for and reports every plant run."""

    def setUp(self):
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        folder = self.root / "scripts/negative"
        folder.mkdir(parents=True)
        for name in ("one", "two", "three"):
            (folder / f"{name}.py").write_text(plant_source(name))
        self.enterContext(patch.multiple(negative, ROOT=self.root, failures=[]))
        self.enterContext(patch.object(negative, "run", side_effect=lambda *cmd:
                                       subprocess.CompletedProcess(cmd, 0, "", "")))
        self.enterContext(patch.object(negative, "worker_status", side_effect=lambda tree:
                                       subprocess.CompletedProcess((), 0, "", "")))
        self.enterContext(patch.object(negative, "copied_state", return_value=()))
        self.workers = self.enterContext(patch.object(negative, "run_workers", return_value=3))
        self.enterContext(patch.dict(os.environ))
        self.output = self.enterContext(redirect_stdout(io.StringIO()))

    def workers_for(self, argv=(), variable=None):
        """The workers main() runs the plants in, with the variable set to `variable`."""
        os.environ.pop(negative.WORKERS, None)
        if variable is not None:
            os.environ[negative.WORKERS] = variable
        self.workers.reset_mock()
        for path in self.root.glob("planted-*"):
            path.unlink()
        self.assertEqual(negative.main(argv), 0)
        if not self.workers.called:
            return 1, sorted(p.name.removeprefix("planted-") for p in self.root.glob("planted-*"))
        self.assertEqual(list(self.root.glob("planted-*")), [])
        return self.workers.call_args.args[1], []

    def refused(self, argv=(), variable=None):
        """What main() says as it exits 2."""
        os.environ.pop(negative.WORKERS, None)
        if variable is not None:
            os.environ[negative.WORKERS] = variable
        errors = io.StringIO()
        with redirect_stderr(errors), self.assertRaises(SystemExit) as raised:
            negative.main(argv)
        self.assertEqual(raised.exception.code, 2)
        return errors.getvalue()

    def test_the_variable_is_read_only_when_the_option_is_absent(self):
        everything = ["one", "three", "two"]
        for argv, variable, expected in (
                ((), None, (1, everything)),
                ((), "", (1, everything)),
                ((), "1", (1, everything)),
                ((), "2", (2, [])),
                ((), "02", (2, [])),
                (("--workers", "3"), "2", (3, [])),
                (("--workers", "1"), "3", (1, everything)),
                (("--workers", "2"), "not a number", (2, [])),
                (("--workers", "9"), None, (3, [])),       # cut to the plants chosen
                (("--plant", "two", "--workers", "4"), None, (1, ["two"]))):
            with self.subTest(argv=argv, variable=variable):
                self.assertEqual(self.workers_for(list(argv), variable), expected)

    def test_anything_but_a_whole_number_from_1_is_refused(self):
        for value in ("0", "00", "-1", "+2", " 2", "2.5", "two", "٣"):
            with self.subTest(value=value):
                self.assertIn(f"STOICHEIA_NEGATIVE_WORKERS must be a whole number from 1, not "
                              f"{value!r}", self.refused(variable=value))
                self.assertIn(f"--workers must be a whole number from 1, not {value!r}",
                              self.refused(["--workers", value], variable="2"))
        self.workers.assert_not_called()

    def test_counts_only_takes_no_workers(self):
        self.assertIn("--workers is not for --counts-only, which takes no workers",
                      self.refused(["--counts-only", "--workers", "1"]))
        (self.root / "scripts/negative/count_markers.py").write_text(
            plant_source("count_markers"))
        # The variable, which the lane may set for every run, is passed over, even when it
        # would be refused elsewhere.
        for value in ("", "2", "none"):
            os.environ[negative.WORKERS] = value
            self.assertEqual(negative.main(["--counts-only"]), 0)
        self.workers.assert_not_called()

    def test_a_failed_entry_status_is_not_compared_at_the_close(self):
        """The workers' entry status fails, and their final status reads a change: the run
        fails on the entry status alone, makes no worker, and does not add that the tree
        did not return to it."""
        self.enterContext(patch.object(negative, "worker_status", side_effect=[
            subprocess.CompletedProcess((), 128, "", "fatal: planted\n"),
            subprocess.CompletedProcess((), 0, "?? planted\n", "")]))
        os.environ.pop(negative.WORKERS, None)
        self.assertEqual(negative.main(["--workers", "2"]), 1)
        self.workers.assert_not_called()
        self.assertEqual(negative.failures, ["entry Git status: exit 128",
                                             "only 0 of the 3 plants chosen were run"])
        self.assertNotIn("did not return", self.output.getvalue())

    def test_the_worker_report_is_hidden_and_a_worker_takes_no_workers(self):
        with self.assertRaises(SystemExit) as raised:
            negative.main(["--help"])
        self.assertEqual(raised.exception.code, 0)
        self.assertIn("--workers N", self.output.getvalue())
        self.assertNotIn("--worker-report", self.output.getvalue())
        self.assertIn("--worker-report is for a worker, which is given its plants by --plant",
                      self.refused(["--worker-report", "report.json"]))
        self.assertIn("--workers is for a run of the plants, not with --worker-report",
                      self.refused(["--plant", "one", "--worker-report", "report.json",
                                    "--workers", "2"]))


# check_fidelity.py in the throwaway repository: the plants there plant nothing it reads, so
# the closing check of each unplanted tree passes; check_kernel reads ROOT from it.
STAND_IN_FIDELITY = '''"""A stand-in for check_fidelity.py, which passes."""
import heath

ROOT = heath.ROOT

if __name__ == "__main__":
    raise SystemExit(0)
'''
# The bodies of the throwaway plants' plant(), "{name}" the plant's name.
PASSES = 'print("{name} plants its change")\n    nt.refused("{name}: caught")'
MISSES = 'nt.expect_failure("{name}", subprocess.CompletedProcess([], 0, "", ""))'
CRASHES = 'import os\n    os._exit(3)'
LEAVES = '(nt.ROOT / "left-by-{name}").write_text("")\n    nt.refused("{name}: caught")'
LEAVES_AND_EXITS = '(nt.ROOT / "left-by-{name}").write_text("")\n    import os\n    os._exit(0)'
CHANGES_MODE = ('(nt.ROOT / "tracked-mode").chmod(0o755)\n'
                '    nt.refused("{name}: caught")')
DELETES_TREE_AND_CRASHES = 'import shutil\n    shutil.rmtree(nt.ROOT)\n    import os\n    os._exit(3)'
SLEEPS = 'import time\n    print("{name} sleeps")\n    time.sleep(120)'
SLEEPS_WITH_ALARM = ('import os\n'
                     '    import signal\n'
                     '    import time\n'
                     '    signal.signal(signal.SIGALRM, lambda *_: os._exit(9))\n'
                     '    signal.alarm(3)\n'
                     '    print("{name} sleeps")\n'
                     '    time.sleep(120)')
# It refuses only when a changed tracked file and an untracked one hold the bytes they hold
# in the tree under test, which it finds through Git's common directory.
LOOKS = ('import os\n'
         '    from pathlib import Path\n'
         '    print("status:", repr(nt.run("git", "status", "--porcelain").stdout))\n'
         '    built = nt.ROOT / ".lake/build/Built.olean"\n'
         '    print("built:", built.read_text().strip(), built.is_symlink(), '
         'os.stat(built).st_nlink)\n'
         '    print("root:", nt.ROOT)\n'
         '    common = nt.run("git", "rev-parse", "--path-format=absolute", "--git-common-dir")\n'
         '    tested = Path(common.stdout.strip()).parent.resolve()\n'
         '    same = [(nt.ROOT / n).read_bytes() == (tested / n).read_bytes()\n'
         '            for n in ("notes/changed.txt", "notes/untracked.txt")\n'
         '            if (nt.ROOT / n).is_file()]\n'
         '    if tested != nt.ROOT.resolve() and same == [True, True]:\n'
         '        nt.refused("{name}: caught")\n'
         '    else:\n'
         '        print("{name}: its files are not the tree under test\'s")')
# It refuses only when its process has none of the variables a worker is started without.
SCRUBBED = ('import os\n'
            '    seen = [n for n in ("LEAN_PATH", "LAKE_HOME", "GIT_NAMESPACE", nt.WORKERS)\n'
            '            if n in os.environ]\n'
            '    if seen:\n'
            '        print("{name} sees", ", ".join(seen))\n'
            '    else:\n'
            '        nt.refused("{name}: caught")')
READS_NON_UTF8 = ('import os\n'
                  '    path = os.fsencode(nt.ROOT) + b"/notes/untracked-\\xff.txt"\n'
                  '    with open(path, "rb") as file:\n'
                  '        contents = file.read()\n'
                  '    if contents == b"untracked non-UTF-8 name\\x00contents":\n'
                  '        nt.refused("{name}: caught")\n'
                  '    else:\n'
                  '        print("{name}: wrong contents", repr(contents))')
# It refuses only when Git ignores notes.tmp in its tree, as render.py asks Git which files
# to pass over; and it prints the untracked files Git does not ignore there.
ASKS_GIT = ('print("not ignored:", repr(nt.run("git", "ls-files", "--others", '
            '"--exclude-standard").stdout))\n'
            '    if nt.run("git", "check-ignore", "-q", "notes.tmp").returncode == 0:\n'
            '        nt.refused("{name}: caught")\n'
            '    else:\n'
            '        print("{name}: notes.tmp is not ignored")')
CHECKS_BOUND_GIT = ('import os\n'
                    '    import sys\n'
                    '    import tempfile\n'
                    '    path = nt.ROOT / "tracked-by-git"\n'
                    '    saved = path.read_text()\n'
                    '    path.write_text("planted\\n")\n'
                    '    checked = nt.run(sys.executable, "scripts/git_tree_probe.py")\n'
                    '    path.write_text(saved)\n'
                    '    env = {{name: value for name, value in os.environ.items()\n'
                    '           if name not in ("GIT_CONFIG_GLOBAL", "GIT_CONFIG_SYSTEM",\n'
                    '                           "GIT_CONFIG_NOSYSTEM")}}\n'
                    '    with tempfile.TemporaryDirectory() as tmp:\n'
                    '        initialized = subprocess.run(["git", "init", "-q"], cwd=tmp,\n'
                    '                                     env=env, capture_output=True, text=True)\n'
                    '        top = subprocess.run(["git", "rev-parse", "--show-toplevel"],\n'
                    '                             cwd=tmp, env=env, capture_output=True, text=True)\n'
                    '    if (checked.returncode == 0\n'
                    '            and checked.stdout == " M tracked-by-git\\n"\n'
                    '            and initialized.returncode == 0 and top.returncode == 0\n'
                    '            and os.path.realpath(top.stdout.strip()) == os.path.realpath(tmp)):\n'
                    '        nt.refused("{name}: caught")\n'
                    '    else:\n'
                    '        print("{name}: Git read the wrong tree", repr(checked.stdout),\n'
                    '              repr(top.stdout), checked.stderr, top.stderr)')


def corrupts(change):
    """A plant that passes, and that changes its worker's report by `change`, a statement on
    `report`, as the worker exits, after its `finally` has written the report."""
    return ('import atexit\n'
            '    import json\n'
            '    import sys\n'
            '    path = sys.argv[sys.argv.index("--worker-report") + 1]\n'
            '\n'
            '    def corrupt():\n'
            '        with open(path, encoding="utf-8") as file:\n'
            '            report = json.load(file)\n'
            f'        {change}\n'
            '        with open(path, "w", encoding="utf-8") as file:\n'
            '            json.dump(report, file)\n'
            '    atexit.register(corrupt)\n'
            '    nt.refused("{name}: caught")')


# check_fidelity.py failing in a worker's tree alone: one in a run's directory for its
# workers. The run's own tree passes it.
FAILS_IN_A_WORKER = '''"""A stand-in for check_fidelity.py, failing in a worker's tree alone."""
import heath

ROOT = heath.ROOT

if __name__ == "__main__":
    if ROOT.parent.name.startswith("stoicheia-negative-"):
        print("the stand-in fails in", ROOT.name)
        raise SystemExit(1)
    raise SystemExit(0)
'''
TIME = re.compile(r"\d+\.\d\ds \(including restoration\)")


class WorkerTests(unittest.TestCase):
    """--workers on a throwaway repository, the suite run as CI runs it, as a script: the
    runner and the helpers it imports are copies, check_fidelity.py a stand-in that passes,
    the regressions empty, `.lake` one small file, and the plants small ones that need no
    Lean. Git runs without user config, and the workers' trees are made in a temporary
    directory of the test's own, where every run must leave none, nor Git a note of one."""

    def setUp(self):
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        self.tmp = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        self.enterContext(patch.object(negative, "failures", []))
        self.env = {k: v for k, v in os.environ.items()
                    if not k.startswith(("GIT_", "PYTHON", "LAKE")) and k != "LEAN_PATH"}
        self.env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                        TMPDIR=str(self.tmp))
        (self.root / "scripts/negative").mkdir(parents=True)
        for name in ("negative_tests", "check_kernel", "generated_counts", "heath"):
            shutil.copyfile(REPO / f"scripts/{name}.py", self.root / f"scripts/{name}.py")
        (self.root / "scripts/check_fidelity.py").write_text(STAND_IN_FIDELITY)
        (self.root / "tests").mkdir()
        for _, rel in negative.REGRESSIONS:
            (self.root / rel).write_text("")
        (self.root / ".gitignore").write_text("/.lake\n__pycache__/\n")
        (self.root / ".lake/build").mkdir(parents=True)
        (self.root / ".lake/build/Built.olean").write_text("built\n")
        self.git("init", "-q")

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.root, env=self.env, capture_output=True,
                              text=True, check=True).stdout

    def commit(self, before=None, **bodies):
        """Each plant's file, its plant() doing its body, and commit the tree. A plant whose
        name ends `_builds` builds; one named in `before` runs that code as it loads."""
        for path in (self.root / "scripts/negative").glob("*.py"):
            path.unlink()
        for name, body in bodies.items():
            (self.root / f"scripts/negative/{name}.py").write_text(plant_source(
                name, builds=f"BUILDS = {name.endswith('_builds')}",
                function="def plant() -> None:\n    " + body.format(name=name),
                before=(before or {}).get(name, "")))
        self.git("add", "--", ".")
        self.git("-c", "user.name=test", "-c", "user.email=test@example.invalid",
                 "commit", "-q", "--no-verify", "--allow-empty", "-m", "the plants")

    def suite(self, *args):
        """The suite run as a script; then no worker's tree is left."""
        result = subprocess.run([sys.executable, "scripts/negative_tests.py", *args],
                                cwd=self.root, env=self.env, capture_output=True, text=True,
                                timeout=300)
        self.assert_no_worker_left()
        return result

    def assert_no_worker_left(self):
        self.assertEqual(list(self.tmp.glob("stoicheia-negative-*")), [])
        self.assertEqual(self.git("worktree", "list", "--porcelain").count("worktree "), 1)

    def one_worker_s_verdict(self):
        """The suite in two workers, which plant nothing in the tree under test, then alone:
        the same exit status, and the same stdout but for the time lines. The exit status."""
        workers = self.suite("--workers", "2")
        alone = self.suite()
        self.assertEqual(workers.returncode, alone.returncode, workers.stdout + alone.stdout)
        self.assertEqual(TIME.sub("", workers.stdout), TIME.sub("", alone.stdout))
        return alone.returncode

    def test_workers_give_one_worker_s_verdicts_and_stdout(self):
        """Apart from the time lines, and from the plan on stderr, on a set that passes and
        on a set where a plant misses its change."""
        for missing in (False, True):
            with self.subTest(missing=missing):
                self.commit(a_one=PASSES, b_two=PASSES, c_three=MISSES if missing else PASSES,
                            d_four_builds=PASSES)
                alone = self.suite()
                self.assertEqual(alone.returncode, 1 if missing else 0, alone.stdout)
                self.assertEqual(alone.stderr, "")
                for workers in ("2", "3"):
                    result = self.suite("--workers", workers)
                    self.assertEqual(result.returncode, alone.returncode, result.stdout)
                    self.assertEqual(TIME.sub("", result.stdout), TIME.sub("", alone.stdout))
                    self.assertIn(f"The plants in {workers} workers, dealt in turn",
                                  result.stderr)
                self.assertTrue(alone.stdout.endswith(
                    "1 negative-test failure(s):\nc_three (scripts/negative/c_three.py):\n"
                    "  ✗ c_three: not caught\n" if missing else
                    "4 of 4 plants run\n✓ every planted change was caught\n"), alone.stdout)

    def test_a_plant_that_misses_its_change_fails_the_run_in_any_worker(self):
        """As the first plant of a worker's share and as the last."""
        for missing in ("a_one", "d_four"):
            with self.subTest(missing=missing):
                self.commit(**{name: MISSES if name == missing else PASSES
                               for name in ("a_one", "b_two", "c_three", "d_four")})
                result = self.suite("--workers", "2")
                self.assertIn("  worker 1: a_one, c_three\n  worker 2: b_two, d_four\n",
                              result.stderr)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertTrue(result.stdout.endswith(
                    f"1 negative-test failure(s):\n{missing} (scripts/negative/{missing}.py):\n"
                    f"  ✗ {missing}: not caught\n"), result.stdout)
                self.assertNotIn("worker", result.stdout)

    def test_a_worker_that_crashes_fails_the_run(self):
        """Its plant ends the process, so neither its `finally` nor its report is written;
        the plant after it in its share is not run, and the other worker's report."""
        self.commit(a_one=PASSES, b_two=CRASHES, c_three=PASSES, d_four=PASSES)
        result = self.suite("--workers", "2")
        self.assertEqual(result.returncode, 1, result.stdout)
        crashed = "worker 2 (b_two, d_four) crashed: exit 3; no report"
        self.assertIn(f"✗ {crashed}; its log ends:\n", result.stdout)
        self.assertIn("\nb_two (scripts/negative/b_two.py)\n", result.stdout)
        for name in ("a_one", "c_three"):
            self.assertIn(f"\n{name} (scripts/negative/{name}.py)\n{name} plants its change\n"
                          f"✓ {name}: caught\n", result.stdout)
        self.assertNotIn("d_four plants its change", result.stdout)
        self.assertTrue(result.stdout.endswith(
            f"2 negative-test failure(s):\noutside any plant:\n  ✗ {crashed}\n"
            "  ✗ only 2 of the 4 plants chosen were run\n"), result.stdout)

    def test_a_worker_s_dirty_tree_fails_the_run(self):
        """A plant that leaves a file behind fails its worker's closing comparison and the
        run's own of the worker's tree; one that then ends the process, which leaves no
        report, is caught by the run's own comparison, as well as by its crash."""
        own = ("worker 2 (b_two, d_four): the working tree did not return to its entry Git "
               "status")
        dirty = "worker 2's tree did not return to its entry Git status"
        for body, failures in ((LEAVES, [own, dirty]),
                               (LEAVES_AND_EXITS, ["worker 2 (b_two, d_four) crashed: no "
                                                   "report", dirty, "only 2 of the 4 plants "
                                                   "chosen were run"])):
            with self.subTest(body=body):
                self.commit(a_one=PASSES, b_two=body, c_three=PASSES, d_four=PASSES)
                result = self.suite("--workers", "2")
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn(f"✗ {dirty}:\n?? left-by-b_two\n", result.stdout)
                self.assertTrue(result.stdout.endswith(
                    f"{len(failures)} negative-test failure(s):\noutside any plant:\n"
                    + "".join(f"  ✗ {failure}\n" for failure in failures)), result.stdout)
                self.assertEqual(self.git("status", "--porcelain"), "")

    def test_git_configuration_cannot_redirect_worker_status(self):
        """Both inline Git configuration protocols point core.worktree at the clean source
        tree: clean workers pass, but a worker that leaves its own tree dirty still fails
        with that worker's diagnostic, and every worker is cleaned up."""
        settings = (
            ("parameters", {"GIT_CONFIG_PARAMETERS":
                            f"'core.worktree'='{self.root}'"}),
            ("count", {"GIT_CONFIG_COUNT": "1", "GIT_CONFIG_KEY_0": "core.worktree",
                       "GIT_CONFIG_VALUE_0": str(self.root)}))
        for mechanism, variables in settings:
            with self.subTest(mechanism=mechanism):
                self.commit(a_one=PASSES, b_two=PASSES)
                self.env.update(variables)
                try:
                    clean = self.suite("--workers", "2")
                    self.assertEqual(clean.returncode, 0, clean.stdout + clean.stderr)
                    self.commit(a_one=PASSES, b_two=LEAVES)
                    dirty = self.suite("--workers", "2")
                    self.assertEqual(dirty.returncode, 1, dirty.stdout + dirty.stderr)
                    message = "worker 2's tree did not return to its entry Git status"
                    self.assertIn(f"✗ {message}:\n?? left-by-b_two\n", dirty.stdout)
                    self.assertEqual(self.git("status", "--porcelain"), "")
                finally:
                    for name in variables:
                        self.env.pop(name, None)

    def test_git_config_files_cannot_redirect_worker_status(self):
        """A global or system config points core.worktree at the clean source tree: a
        worker that leaves its own tree dirty still fails, leaves the source unchanged,
        and is completely cleaned up."""
        for source in ("GIT_CONFIG_GLOBAL", "GIT_CONFIG_SYSTEM"):
            with self.subTest(source=source):
                config = self.tmp / f"{source.lower()}.config"
                config.write_text(f"[core]\n\tworktree = {self.root}\n")
                self.commit(a_one=PASSES, b_two=LEAVES)
                saved = self.env.copy()
                self.env[source] = str(config)
                if source == "GIT_CONFIG_SYSTEM":
                    self.env["GIT_CONFIG_NOSYSTEM"] = "0"
                try:
                    result = self.suite("--workers", "2")
                    self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                    message = "worker 2's tree did not return to its entry Git status"
                    self.assertIn(f"✗ {message}:\n?? left-by-b_two\n", result.stdout)
                    self.assertFalse((self.root / "left-by-b_two").exists())
                    self.assertEqual(self.git("status", "--porcelain"), "")
                finally:
                    self.env.clear()
                    self.env.update(saved)

    def test_git_config_files_cannot_redirect_plant_checks(self):
        """Global and system core.worktree settings point at the source, while a plant's
        child check sees its worker and Git in an independent temporary repository stays
        with that repository; one and multiple workers give the same verdict."""
        tracked = self.root / "tracked-by-git"
        tracked.write_text("clean\n")
        (self.root / "scripts/git_tree_probe.py").write_text(
            'import subprocess\n'
            'import sys\n'
            'result = subprocess.run(["git", "status", "--porcelain", "--", '
            '"tracked-by-git"], capture_output=True, text=True)\n'
            'sys.stdout.write(result.stdout)\n'
            'sys.stderr.write(result.stderr)\n'
            'raise SystemExit(result.returncode)\n')
        self.commit(a_checks=CHECKS_BOUND_GIT, b_checks=CHECKS_BOUND_GIT)
        for source in ("GIT_CONFIG_GLOBAL", "GIT_CONFIG_SYSTEM"):
            with self.subTest(source=source):
                config = self.tmp / f"{source.lower()}-plant.config"
                config.write_text(f"[core]\n\tworktree = {self.root}\n")
                saved = self.env.copy()
                self.env[source] = str(config)
                if source == "GIT_CONFIG_SYSTEM":
                    self.env["GIT_CONFIG_NOSYSTEM"] = "0"
                try:
                    self.assertEqual(self.one_worker_s_verdict(), 0)
                finally:
                    self.env.clear()
                    self.env.update(saved)

    def test_status_configuration_gives_one_worker_s_verdict(self):
        """The repository hides untracked files from its status, so one worker's bracket
        does not see a file a plant leaves, and two workers', which read the same
        configuration, do not either: both pass."""
        self.commit(a_one=PASSES, b_two=LEAVES)
        self.git("config", "status.showUntrackedFiles", "no")
        self.assertEqual(self.one_worker_s_verdict(), 0)

    def test_local_core_worktree_cannot_redirect_worker_status(self):
        """The shared repository config points core.worktree at the clean source tree, but
        a file left in the actual worker still fails the run and cleanup removes it."""
        self.commit(a_one=PASSES, b_two=LEAVES)
        self.git("config", "core.worktree", str(self.root))
        result = self.suite("--workers", "2")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        message = "worker 2's tree did not return to its entry Git status"
        self.assertIn(f"✗ {message}:\n?? left-by-b_two\n", result.stdout)
        self.assertFalse((self.root / "left-by-b_two").exists())
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_global_quote_configuration_does_not_change_worker_snapshot(self):
        """A global core.quotePath=false and an existing non-ASCII untracked filename do
        not make an identical worker tree differ from the source tree."""
        self.commit(a_one=PASSES, b_two=PASSES)
        notes = self.root / "notes"
        notes.mkdir()
        non_ascii = notes / "café.txt"
        non_ascii.write_text("unchanged\n")
        config = self.tmp / "quote.config"
        config.write_text("[core]\n\tquotePath = false\n")
        self.env["GIT_CONFIG_GLOBAL"] = str(config)
        result = self.suite("--workers", "2")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for name in ("a_one", "b_two"):
            self.assertIn(f"✓ {name}: caught\n", result.stdout)
        self.assertEqual(non_ascii.read_text(), "unchanged\n")

    def test_global_excludes_file_gives_one_worker_s_verdict(self):
        """The caller's global excludes file ignores an untracked file: Git does not list it
        in the tree under test, so it is not copied into a worker, and Git ignores it in a
        worker's tree as in that tree, so that a check that asks Git which files to pass
        over, as render.py does, gives one worker's verdict."""
        self.commit(a_asks=ASKS_GIT, b_asks=ASKS_GIT)
        notes = self.root / "notes.tmp"
        notes.write_text("untracked, and ignored globally\n")
        excludes = self.tmp / "global-ignore"
        excludes.write_text("notes.tmp\n")
        config = self.tmp / "excludes.config"
        config.write_text(f"[core]\n\texcludesFile = {excludes}\n")
        self.env["GIT_CONFIG_GLOBAL"] = str(config)
        self.assertNotIn("notes.tmp", self.git("ls-files", "--others", "--exclude-standard"))
        self.assertEqual(self.one_worker_s_verdict(), 0)
        base = self.tmp / "stoicheia-negative-excludes"
        base.mkdir()
        registered = []
        with patch.object(negative, "ROOT", self.root), \
                patch.dict(os.environ, self.env, clear=True):
            try:
                self.assertIsNone(negative.make_worker(
                    base / "worker-1", negative.worker_status(self.root).stdout, registered))
                self.assertTrue((base / "worker-1/scripts/negative_tests.py").is_file())
                self.assertFalse((base / "worker-1/notes.tmp").exists())
            finally:
                negative.remove(registered, base)
        self.assert_no_worker_left()
        self.assertEqual(notes.read_text(), "untracked, and ignored globally\n")

    def test_inherited_alternate_index_does_not_change_worker_snapshot(self):
        """An inherited alternate index does not replace the source index in workers."""
        self.commit(a_one=PASSES, b_two=PASSES)
        alternate = self.tmp / "alternate-index"
        alternate_env = self.env | {"GIT_INDEX_FILE": str(alternate)}
        subprocess.run(["git", "read-tree", "--empty"], cwd=self.root, env=alternate_env,
                       check=True)
        self.env["GIT_INDEX_FILE"] = str(alternate)
        try:
            result = self.suite("--workers", "2")
        finally:
            self.env.pop("GIT_INDEX_FILE")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for name in ("a_one", "b_two"):
            self.assertIn(f"✓ {name}: caught\n", result.stdout)
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_worktree_rename_configuration_does_not_change_worker_snapshot(self):
        """A staged rename in a linked source has its plain-status form and one-worker
        verdict preserved in every worker."""
        notes = self.root / "notes"
        notes.mkdir()
        old = notes / "old.txt"
        old.write_text("renamed contents\n")
        self.commit(a_one=PASSES, b_two=PASSES)
        self.git("config", "extensions.worktreeConfig", "true")
        source = self.tmp / "source"
        self.git("worktree", "add", "--detach", str(source), "HEAD")
        try:
            def source_git(*args):
                return subprocess.run(["git", *args], cwd=source, env=self.env,
                                      capture_output=True, text=True, check=True).stdout

            source_git("config", "--worktree", "status.renames", "false")
            source_git("mv", "notes/old.txt", "notes/new.txt")
            before = source_git("status", "--porcelain")
            self.assertEqual(before, "A  notes/new.txt\nD  notes/old.txt\n")
            alone = subprocess.run([sys.executable, "scripts/negative_tests.py"], cwd=source,
                                   env=self.env, capture_output=True, text=True, timeout=300)
            workers = subprocess.run([sys.executable, "scripts/negative_tests.py", "--workers",
                                      "2"], cwd=source, env=self.env, capture_output=True,
                                     text=True, timeout=300)
            self.assertEqual(workers.returncode, alone.returncode,
                             workers.stdout + workers.stderr + alone.stdout + alone.stderr)
            self.assertEqual(TIME.sub("", workers.stdout), TIME.sub("", alone.stdout))
            self.assertEqual(source_git("status", "--porcelain"), before)
            self.assertEqual((source / "notes/new.txt").read_text(), "renamed contents\n")
        finally:
            self.git("worktree", "remove", "--force", "--force", str(source))
        self.assert_no_worker_left()

    def test_filemode_configuration_gives_one_worker_s_verdict(self):
        """With core.fileMode false, one worker's bracket does not see a plant's change to a
        tracked file's executable bit, and two workers', which read the same configuration,
        do not either: both pass."""
        tracked = self.root / "tracked-mode"
        tracked.write_text("tracked\n")
        tracked.chmod(0o644)
        self.commit(a_mode=CHANGES_MODE, b_mode=CHANGES_MODE)
        self.git("config", "core.fileMode", "false")
        self.assertEqual(self.one_worker_s_verdict(), 0)

    def test_worktree_lifecycle_ignores_inherited_repository_variables(self):
        """Worker creation and removal stay in the source repository under foreign Git
        repository variables."""
        self.commit(a_one=PASSES, b_two=PASSES)
        other = self.tmp / "other-repository"
        other.mkdir()
        other_env = self.env.copy()
        subprocess.run(["git", "init", "-q"], cwd=other, env=other_env, check=True)
        sentinel = other / "sentinel"
        sentinel.write_text("unchanged\n")
        subprocess.run(["git", "add", "sentinel"], cwd=other, env=other_env, check=True)
        subprocess.run(["git", "-c", "user.name=test", "-c",
                        "user.email=test@example.invalid", "commit", "-q", "-m", "other"],
                       cwd=other, env=other_env, check=True)
        foreign_before = subprocess.run(["git", "worktree", "list", "--porcelain"],
                                        cwd=other, env=other_env, capture_output=True,
                                        text=True, check=True).stdout
        self.env.update(GIT_DIR=str(other / ".git"), GIT_WORK_TREE=str(other))
        try:
            result = self.suite("--workers", "2")
        finally:
            self.env.pop("GIT_DIR")
            self.env.pop("GIT_WORK_TREE")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assert_no_worker_left()
        foreign_after = subprocess.run(["git", "worktree", "list", "--porcelain"],
                                       cwd=other, env=other_env, capture_output=True,
                                       text=True, check=True).stdout
        self.assertEqual(foreign_after, foreign_before)
        self.assertEqual(sentinel.read_text(), "unchanged\n")

    def test_interrupt_after_worktree_registration_cleans_the_registration(self):
        """SIGINT after Git registers the first worker reaches cleanup with that ownership
        recorded, so neither its directory nor its repository record remains."""
        self.commit(a_one=PASSES, b_two=PASSES)
        chosen = [negative.Plant(name, self.root / f"scripts/negative/{name}.py", "", False,
                                 lambda: None)
                  for name in ("a_one", "b_two")]
        with patch.object(negative, "ROOT", self.root), \
                patch.dict(os.environ, self.env, clear=True):
            entry = negative.worker_status(self.root).stdout
            real = negative.root_git
            interrupted = False

            def interrupt_after_add(*cmd):
                nonlocal interrupted
                result = real(*cmd)
                if cmd[:2] == ("worktree", "add") and result.returncode == 0 and not interrupted:
                    interrupted = True
                    os.kill(os.getpid(), signal.SIGINT)
                return result

            with patch.object(negative, "root_git", side_effect=interrupt_after_add), \
                    redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()), \
                    self.assertRaises(KeyboardInterrupt):
                negative.run_workers(chosen, 2, entry, {})
        self.assertTrue(interrupted)
        self.assert_no_worker_left()

    def test_interrupt_after_process_creation_stops_it_before_removing_its_tree(self):
        """SIGINT after a child is created leaves cleanup owning it, with SIGINT unblocked;
        the child is stopped and reaped before either registered tree is removed."""
        self.commit(a_one=SLEEPS_WITH_ALARM, b_two=PASSES)
        chosen = [negative.Plant(name, self.root / f"scripts/negative/{name}.py", "", False,
                                 lambda: None)
                  for name in ("a_one", "b_two")]
        children = []
        reaped = []
        real_popen = subprocess.Popen
        before_mask = signal.pthread_sigmask(signal.SIG_BLOCK, set())
        with patch.object(negative, "ROOT", self.root), \
                patch.dict(os.environ, self.env, clear=True):
            entry = negative.worker_status(self.root).stdout
            real_root_git = negative.root_git

            def interrupt_after_spawn(*args, **kwargs):
                child = real_popen(*args, **kwargs)
                command = args[0] if args else kwargs["args"]
                if "--worker-report" in command:
                    children.append(child)
                    os.kill(os.getpid(), signal.SIGINT)
                return child

            def check_before_removal(*cmd):
                if cmd[:2] == ("worktree", "remove"):
                    reaped.append(bool(children) and children[0].poll() is not None)
                return real_root_git(*cmd)

            with patch.object(negative.subprocess, "Popen", side_effect=interrupt_after_spawn), \
                    patch.object(negative, "root_git", side_effect=check_before_removal), \
                    redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()), \
                    self.assertRaises(KeyboardInterrupt):
                negative.run_workers(chosen, 2, entry, {})
        self.assertEqual(signal.pthread_sigmask(signal.SIG_BLOCK, set()), before_mask)
        self.assertEqual(len(children), 1)
        self.assertIsNotNone(children[0].returncode)
        self.assertNotEqual(children[0].returncode, 9)
        self.assertEqual(reaped, [True, True])
        self.assert_no_worker_left()

    def test_split_index_state_is_cloned_into_workers(self):
        """A staged change in a valid split index has the same snapshot in every worker."""
        tracked = self.root / "split-index-state"
        tracked.write_text("committed\n")
        self.commit(a_one=PASSES, b_two=PASSES)
        tracked.write_text("staged\n")
        self.git("add", "split-index-state")
        self.git("update-index", "--split-index")
        git_dir = Path(self.git("rev-parse", "--absolute-git-dir").strip())
        self.assertTrue(list(git_dir.glob("sharedindex.*")))
        before = self.git("status", "--porcelain")
        result = self.suite("--workers", "2")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for name in ("a_one", "b_two"):
            self.assertIn(f"✓ {name}: caught\n", result.stdout)
        self.assertEqual(self.git("status", "--porcelain"), before)
        self.assertEqual(tracked.read_text(), "staged\n")

    def test_no_worker_s_tree_is_left(self):
        """After a run that passes, one that fails and one with a crash, as after every run
        of these tests; and after an interruption, which the run passes on to each worker
        still running before it removes the trees."""
        for body in (PASSES, MISSES, CRASHES):
            with self.subTest(body=body):
                self.commit(a_one=PASSES, b_two=body)
                self.assertEqual(self.suite("--workers", "2").returncode,
                                 0 if body == PASSES else 1)
        self.commit(a_one=PASSES, b_two=SLEEPS)
        run = subprocess.Popen([sys.executable, "scripts/negative_tests.py", "--workers", "2"],
                               cwd=self.root, env=self.env, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, text=True)
        self.addCleanup(run.kill)
        deadline = time.monotonic() + 120
        while not any("b_two sleeps" in log.read_text()
                      for log in self.tmp.glob("stoicheia-negative-*/worker-*.log")):
            if run.poll() is not None:
                self.fail(run.communicate())
            self.assertLess(time.monotonic(), deadline)
            time.sleep(0.05)
        run.send_signal(signal.SIGINT)
        out, err = run.communicate(timeout=120)
        self.assertNotEqual(run.returncode, 0, out + err)
        self.assertIn("KeyboardInterrupt", err)
        self.assert_no_worker_left()
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_a_missing_worker_tree_is_reported_and_later_workers_are_checked(self):
        """A worker deletes its tree and crashes, then a later worker leaves its tree dirty:
        both failures reach the normal summary, and cleanup removes every registration."""
        self.commit(a_one=PASSES, b_two=DELETES_TREE_AND_CRASHES,
                    c_three=LEAVES_AND_EXITS)
        result = self.suite("--workers", "3")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        prefix = "worker 2's tree did not return to its entry Git status (FileNotFoundError:"
        detail = next((line.removeprefix("✗ ") for line in result.stdout.splitlines()
                       if line.startswith(f"✗ {prefix}")), None)
        self.assertIsNotNone(detail, result.stdout)
        later = "worker 3's tree did not return to its entry Git status"
        self.assertIn(f"✗ {later}:\n?? left-by-c_three\n", result.stdout)
        self.assertNotIn("Traceback", result.stdout + result.stderr)
        failures = ["worker 2 (b_two) crashed: exit 3; no report", detail,
                    "worker 3 (c_three) crashed: no report", later,
                    "only 1 of the 3 plants chosen were run"]
        self.assertTrue(result.stdout.endswith(
            f"{len(failures)} negative-test failure(s):\noutside any plant:\n"
            + "".join(f"  ✗ {failure}\n" for failure in failures)), result.stdout)

    def test_an_untracked_non_utf8_filename_is_preserved(self):
        """Each worker receives an untracked filename that is not UTF-8, with its bytes and
        contents unchanged, and its plant observes that copy."""
        self.commit(a_reads=READS_NON_UTF8, b_reads=READS_NON_UTF8)
        notes = self.root / "notes"
        notes.mkdir()
        raw = os.fsencode(notes) + b"/untracked-\xff.txt"
        try:
            descriptor = os.open(raw, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        except OSError as error:
            if error.errno == errno.EILSEQ:
                self.skipTest("the filesystem refuses non-UTF-8 filenames")
            raise
        with os.fdopen(descriptor, "wb") as file:
            file.write(b"untracked non-UTF-8 name\x00contents")
        result = self.suite("--workers", "2")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for name in ("a_reads", "b_reads"):
            self.assertIn(f"✓ {name}: caught\n", result.stdout)

    def test_a_worker_s_tree_is_the_tree_under_test(self):
        """Not just its commit: a change staged, a change not, a tracked file deleted and an
        untracked one, a symbolic link and an executable file; and a clone of `.lake`, each
        file a regular file with one name. Each worker's Git status is the tree's, and the
        changed file and the untracked one hold the tree's bytes, or its plant refuses
        nothing. A tree that is not the one whose status was taken first fails the run
        before any plant."""
        notes = self.root / "notes"
        notes.mkdir()
        for name in ("staged", "changed", "gone"):
            (notes / f"{name}.txt").write_text(f"{name}\n")
        (notes / "link").symlink_to("staged.txt")
        (self.root / "scripts/tool.sh").write_text("#!/bin/sh\n")
        (self.root / "scripts/tool.sh").chmod(0o755)
        self.commit(a_looks=LOOKS, b_looks=LOOKS)
        (notes / "staged.txt").write_text("staged, changed\n")
        self.git("add", "--", "notes/staged.txt")
        (notes / "changed.txt").write_text("changed, not staged\n")
        (notes / "gone.txt").unlink()
        (notes / "untracked.txt").write_text("untracked\n")
        status = self.git("status", "--porcelain")
        self.assertEqual(status, " M notes/changed.txt\n D notes/gone.txt\nM  notes/staged.txt\n"
                                 "?? notes/untracked.txt\n")
        result = self.suite("--workers", "2")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.count(f"status: {status!r}\n"), 2, result.stdout)
        self.assertEqual(result.stdout.count("built: built False 1\n"), 2, result.stdout)
        roots = re.findall(r"^root: (.*)$", result.stdout, re.M)
        self.assertEqual(len(set(roots)), 2)
        self.assertNotIn(str(self.root), roots)
        self.assertEqual(self.git("status", "--porcelain"), status)
        with self.subTest("a file written as a plant loads"):
            self.commit(before={"b_writes": '(nt.ROOT / "written-as-it-loads").touch()'},
                        a_one=PASSES, b_writes=PASSES)
            alone = self.suite()
            (self.root / "written-as-it-loads").unlink()
            workers = self.suite("--workers", "2")
            self.assertEqual(workers.returncode, alone.returncode, workers.stdout + alone.stdout)
            self.assertEqual(TIME.sub("", workers.stdout), TIME.sub("", alone.stdout))
            first = workers.stdout.index("a_one (scripts/negative/a_one.py)")
            second = workers.stdout.index("b_writes (scripts/negative/b_writes.py)")
            self.assertLess(first, second)
            self.assertNotIn("tree does not match the tree under test", workers.stdout)
            self.assertIn("the working tree did not return to its entry Git status",
                          workers.stdout)

    def test_same_status_import_mutations_use_the_serial_path(self):
        """An import-time append to an already-untracked or already-modified file leaves
        its porcelain label unchanged, but multiple requested workers still give the
        already-loaded one-worker verdict from the same initial bytes."""
        target = self.root / "notes.txt"
        before = ('(nt.ROOT / "notes.txt").write_text('
                  '(nt.ROOT / "notes.txt").read_text() + "loaded\\n")')
        for tracked, initial, label in ((False, "untracked\n", "?? notes.txt\n"),
                                        (True, "modified\n", " M notes.txt\n")):
            with self.subTest(tracked=tracked):
                target.unlink(missing_ok=True)
                if tracked:
                    target.write_text("committed\n")
                expected = initial + "loaded\n"
                body = ('contents = (nt.ROOT / "notes.txt").read_text()\n'
                        f'    if contents == {expected!r}:\n'
                        '        nt.refused("{name}: caught")\n'
                        '    else:\n'
                        '        print("{name}: imported more than once", repr(contents))')
                self.commit(before={"b_reads": before}, a_reads=body, b_reads=body)
                target.write_text(initial)
                self.assertEqual(self.git("status", "--porcelain", "--", "notes.txt"),
                                 label)
                alone = self.suite()
                target.write_text(initial)
                self.assertEqual(self.git("status", "--porcelain", "--", "notes.txt"),
                                 label)
                workers = self.suite("--workers", "2")
                self.assertEqual(workers.returncode, alone.returncode,
                                 workers.stdout + workers.stderr + alone.stdout + alone.stderr)
                self.assertEqual(TIME.sub("", workers.stdout), TIME.sub("", alone.stdout))
                self.assertEqual(workers.stderr, alone.stderr)
                self.assertEqual(target.read_text(), expected)

    def test_a_run_s_directory_inside_a_work_tree_fails_the_run(self):
        """TMPDIR inside another repository's work tree, where a fixture meant to have no
        repository above it would find one: even when GIT_CEILING_DIRECTORIES would hide
        that repository, the run fails before it makes any worker, naming its directory
        and TMPDIR, and no plant runs."""
        inside = self.tmp / "checkout/tmp"
        inside.mkdir(parents=True)
        subprocess.run(["git", "init", "-q"], cwd=inside.parent, env=self.env, check=True)
        self.commit(a_one=PASSES, b_two=PASSES)
        self.env["TMPDIR"] = str(inside)
        self.env["GIT_CEILING_DIRECTORIES"] = str(inside.parent)
        result = self.suite("--workers", "2")
        self.assertEqual(result.returncode, 1, result.stdout)
        message = (rf"the run's directory {re.escape(str(inside))}/stoicheia-negative-\w+ is "
                   r"inside a Git work tree, where a plant's fixture would find a repository "
                   r"above it; no worker was made: set TMPDIR elsewhere \(it is "
                   rf"{re.escape(repr(str(inside)))}\)")
        self.assertRegex(result.stdout, rf"\n✗ {message}\n")
        self.assertRegex(result.stdout, rf"\noutside any plant:\n  ✗ {message}\n"
                                        r"  ✗ only 0 of the 2 plants chosen were run\n\Z")
        self.assertNotIn("(scripts/negative/", result.stdout)
        self.assertEqual(list(inside.iterdir()), [])

    def test_a_report_out_of_form_is_a_crash_and_the_others_are_read(self):
        """Each of seven workers' reports lacks a field the run reads, or has one of the
        wrong type, once the worker has written it: each worker crashed, and the eighth
        worker's verdicts are read all the same."""
        changes = {"a_no_plants": 'del report["plants"]',
                   "b_no_failures": 'del report["failures"]',
                   "c_no_status": 'del report["status"]',
                   "d_no_name": 'del report["plants"][0]["name"]',
                   "e_no_output": 'del report["plants"][0]["output"]',
                   "f_no_plant_failures": 'del report["plants"][0]["failures"]',
                   "g_status_as_text": 'report["status"] = str(report["status"])'}
        self.commit(h_whole=PASSES, **{name: corrupts(change) for name, change in changes.items()})
        result = self.suite("--workers", "8")
        self.assertEqual(result.returncode, 1, result.stdout)
        crashed = [f"worker {k} ({name}) crashed: its report is not in the form a worker writes"
                   for k, name in enumerate(changes, 1)]
        for message in crashed:
            self.assertIn(f"✗ {message}; its log ends:\n", result.stdout)
        self.assertIn("\nh_whole (scripts/negative/h_whole.py)\nh_whole plants its change\n"
                      "✓ h_whole: caught\n", result.stdout)
        self.assertTrue(result.stdout.endswith(
            "8 negative-test failure(s):\noutside any plant:\n"
            + "".join(f"  ✗ {message}\n" for message in crashed)
            + "  ✗ only 1 of the 8 plants chosen were run\n"), result.stdout)

    def test_a_worker_runs_without_the_variables_of_a_repository_or_a_build(self):
        """LEAN_PATH, a LAKE variable, GIT_NAMESPACE and the variable that gives the number
        of workers are in the run's environment and in no worker's: its plants refuse only
        then."""
        self.commit(a_one=SCRUBBED, b_two=SCRUBBED)
        self.env.update({"LEAN_PATH": str(self.tmp / "lean"), "LAKE_HOME": str(self.tmp / "lake"),
                         "GIT_NAMESPACE": "planted", negative.WORKERS: "2"})
        result = self.suite()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("The plants in 2 workers", result.stderr)
        for name in ("a_one", "b_two"):
            self.assertIn(f"✓ {name}: caught\n", result.stdout)

    def test_a_worker_s_closing_check_fails_the_run_under_its_name(self):
        """check_fidelity.py fails in a worker's tree alone: the run's own closing check
        passes, and each worker's fails the run under the worker's name."""
        (self.root / "scripts/check_fidelity.py").write_text(FAILS_IN_A_WORKER)
        self.commit(a_one=PASSES, b_two=PASSES)
        result = self.suite("--workers", "2")
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("\n✓ the unplanted tree passes check_fidelity.py\n", result.stdout)
        failed = [f"worker {k} ({name}): the unplanted tree failed check_fidelity.py"
                  for k, name in ((1, "a_one"), (2, "b_two"))]
        self.assertTrue(result.stdout.endswith(
            "2 negative-test failure(s):\noutside any plant:\n"
            + "".join(f"  ✗ {message}\n" for message in failed)), result.stdout)

    def trees(self, label):
        """Two workers' trees made as a run makes them, in a run's directory with their
        reports, `label` naming it; the runner in process, as a run with this repository's
        environment."""
        self.commit(a_one=PASSES)
        base = self.tmp / f"stoicheia-negative-{label}"
        base.mkdir()
        trees = [base / f"worker-{k}" for k in (1, 2)]
        for k, tree in enumerate(trees, 1):
            self.git("worktree", "add", "--detach", str(tree), "HEAD")
            (base / f"worker-{k}.json").write_text("{}")
        self.enterContext(patch.object(negative, "ROOT", self.root))
        self.enterContext(patch.dict(os.environ, self.env, clear=True))
        return base, trees

    def test_an_interrupt_during_the_first_removal_leaves_no_tree(self):
        """SIGINT while Git removes the first tree is ignored until both trees and the run's
        directory are gone, and the handler before it is put back."""
        base, trees = self.trees("interrupted")
        previous = signal.signal(signal.SIGINT, signal.default_int_handler)
        self.addCleanup(signal.signal, signal.SIGINT, previous)
        real, calls = negative.root_git, []

        def interrupted(*cmd):
            calls.append(cmd)
            if len(calls) == 1:
                os.kill(os.getpid(), signal.SIGINT)
            return real(*cmd)
        with patch.object(negative, "root_git", interrupted):
            try:
                negative.remove(trees, base)
            except KeyboardInterrupt:
                pass  # what it left is asserted below
        self.assertEqual(len(calls), 2)
        self.assert_no_worker_left()
        self.assertIs(signal.getsignal(signal.SIGINT), signal.default_int_handler)

    def test_a_tree_git_cannot_remove_fails_after_its_directory_is_deleted(self):
        """Git fails to remove the first tree, or the command raises: its directory is
        deleted but the run fails because Git's record stays, and the second tree is
        removed all the same. No record is pruned, not even one outside the run."""
        elsewhere = self.tmp / "elsewhere"
        self.commit(a_one=PASSES)
        self.git("worktree", "add", "--detach", str(elsewhere), "HEAD")
        shutil.rmtree(elsewhere)    # a stale record, which only `git worktree prune` drops
        for label, effect, why in (
                ("exit", subprocess.CompletedProcess((), 128, "", "fatal: planted\n"),
                 "exit 128: fatal: planted"),
                ("raise", OSError("planted"), "OSError: planted")):
            with self.subTest(label):
                negative.failures.clear()
                base, trees = self.trees(label)
                real = negative.root_git

                def fails(*cmd):
                    if str(trees[0]) not in cmd:
                        return real(*cmd)
                    if isinstance(effect, BaseException):
                        raise effect
                    return effect
                output = io.StringIO()
                with patch.object(negative, "root_git", fails), redirect_stdout(output):
                    negative.remove(trees, base)
                message = (f"worker 1's tree {trees[0]} could not be removed ({why}); its "
                           "directory was deleted, but its record remains in the repository's "
                           "worktree list")
                self.assertEqual(negative.failures, [message])
                self.assertEqual(output.getvalue(), f"✗ {message}\n")
                self.assertFalse(base.exists())
                listed = self.git("worktree", "list", "--porcelain")
                self.assertIn(f"worktree {trees[0]}\n", listed)
                self.assertNotIn(f"worktree {trees[1]}\n", listed)
                self.assertIn(f"worktree {elsewhere}\n", listed)

    def test_a_tree_neither_git_nor_deletion_removes_fails_the_run(self):
        """Git fails to remove the first tree and deleting it fails too, as for a folder
        that may not be written: the run fails, naming the tree, not claiming it deleted;
        the second tree is removed all the same, and the run's directory, which still
        holds the first, fails too."""
        self.commit(a_one=PASSES)
        base, trees = self.trees("kept")
        real, delete = negative.root_git, shutil.rmtree

        def fails(*cmd):
            if str(trees[0]) in cmd:
                return subprocess.CompletedProcess((), 128, "", "fatal: planted\n")
            return real(*cmd)

        def keeps(path, *args, **kwargs):
            if Path(path) not in (trees[0], base):
                delete(path, *args, **kwargs)
        output = io.StringIO()
        try:
            with patch.object(negative, "root_git", fails), \
                    patch.object(negative.shutil, "rmtree", keeps), redirect_stdout(output):
                negative.remove(trees, base)
            self.assertEqual(negative.failures, [
                f"worker 1's tree {trees[0]} could not be removed (exit 128: fatal: planted) "
                "nor deleted; remove it, and then its record (git worktree remove)",
                f"the workers' directory {base} could not be deleted; remove it"])
            self.assertNotIn("was deleted", output.getvalue())
            self.assertTrue(trees[0].exists())
            self.assertFalse(trees[1].exists())
        finally:
            self.git("worktree", "remove", "--force", "--force", str(trees[0]))
            delete(base, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
