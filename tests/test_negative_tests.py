#!/usr/bin/env python3
"""Restoration regressions for scripts/negative_tests.py, without Lean, and without Git
outside temporary repositories.

    python3 -I tests/test_negative_tests.py

The negative suite runs these first. Temporary files stand in for Lake outputs;
simulated builds delete, replace and create them before failing or being interrupted.
A temporary repository stands in for the pre-flight's pass with origin/main's checks,
whose work tree lacks the files a commit adds under the check inputs while Git's index
still lists them. The plants are reached as the suite reaches them, through its loader
of scripts/negative/, and the loader is tested on temporary folders of small plants.
"""

import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import Mock, patch

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))
import negative_tests as negative  # noqa: E402


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

    def test_failed_regressions_stop_before_any_plant(self):
        loaded, first = stand_in(self.root)
        with patch.object(negative, "run", return_value=subprocess.CompletedProcess(
                [], 1, "", "regression failed")) as commands, \
                patch.object(negative, "load_plants", return_value=loaded) as load:
            self.assertEqual(negative.main(), 1)
        self.assertEqual(commands.call_args.args,
                         (sys.executable, "-I", "tests/test_negative_tests.py"))
        first.assert_not_called()
        load.assert_not_called()

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
                    plant("circle_proved")()
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
                            plant("circle_proved")()
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


PLANT = '''{doc}
import subprocess

import negative_tests as nt

{builds}


{plant}
'''
DOC = '"""A plant the loader\'s tests write."""'


def plant_source(name, *, doc=DOC, builds="BUILDS = False", body='nt.refused("{name}: caught")',
                 function=None):
    """A plant's file: it leaves planted-<name> in ROOT, so a test sees that it ran, and then
    does `body`."""
    if function is None:
        function = ("def plant() -> None:\n"
                    f'    (nt.ROOT / "planted-{name}").touch()\n'
                    f"    {body.format(name=name)}")
    return PLANT.format(doc=doc, builds=builds, plant=function)


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
        if self.folder.is_dir():
            shutil.rmtree(self.folder)
        else:
            self.folder.unlink(missing_ok=True)
        self.folder.mkdir()
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
        self.assertEqual(negative.main(), 1)
        self.assertEqual(len(negative.failures), len(faults), negative.failures)
        for fault, failure in zip(faults, negative.failures):
            self.assertTrue(failure.startswith(fault), f"{failure!r} for {fault!r}")
            self.assertIn(f"✗ {failure}\n", self.output.getvalue())
        self.assertIn("loading the plants (scripts/negative/):\n  ✗ " + negative.failures[0],
                      self.output.getvalue())
        self.assertEqual(self.planted(), [])
        self.assertEqual(self.git_status(), [])

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
            with self.subTest(entry=entry):
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
                  "scripts/negative: no plants")]
        for what, make, fault in cases:
            with self.subTest(folder=what):
                self.reset()
                make()
                self.assert_refused_before_planting(fault)

    def test_pycache_is_passed_over(self):
        self.write("good.py", plant_source("good"))
        (self.folder / "__pycache__").mkdir()
        (self.folder / "__pycache__/stale.cpython-312.pyc").write_bytes(b"not a plant")
        plants, faults = negative.load_plants()
        self.assertEqual(([p.name for p in plants], faults), (["good"], []))

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
                     "✓ the unplanted tree passes check_fidelity.py\n",
                     "✓ every planted change was caught\n"):
            self.assertIn(line, self.output.getvalue())

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
                self.assertEqual(self.git_status(), [])
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
        self.assertEqual(sorted(names), sorted(path.stem for path in folder.iterdir()
                                               if path.name != "__pycache__"))
        self.assertEqual(plants, sorted(plants, key=lambda p: (p.builds, p.name)))
        for p in plants:
            self.assertEqual(p.path, folder / f"{p.name}.py")
            self.assertTrue(p.description)


if __name__ == "__main__":
    unittest.main()
