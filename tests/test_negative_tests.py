#!/usr/bin/env python3
"""Restoration regressions for scripts/negative_tests.py, without Lean, and without Git
outside temporary repositories.

    python3 -I tests/test_negative_tests.py

The negative suite runs these first. Temporary files stand in for Lake outputs;
simulated builds delete, replace and create them before failing or being interrupted.
A temporary repository stands in for the pre-flight's pass with origin/main's checks,
whose work tree lacks the files a commit adds under the check inputs while Git's index
still lists them. The comment reader the scripts share is fed the texts on which a reader
could read a Lean comment otherwise than Lean does, each with Lean's own reading.
"""

import importlib.util
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

    def test_failed_regressions_stop_before_any_plant(self):
        with patch.object(negative, "run", return_value=subprocess.CompletedProcess(
                [], 1, "", "regression failed")) as commands, \
                patch.object(negative, "heath_word") as plant:
            self.assertEqual(negative.main(), 1)
        self.assertEqual(commands.call_args.args,
                         (sys.executable, "-I", "tests/test_negative_tests.py"))
        plant.assert_not_called()

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
    """The one reader of Lean comments that the scripts share, check_fidelity's
    `comment_end`, read through `lean_comments` and `read_lean`, without Lean (#206): the
    texts on which a reader that began a block's body at its third character, or read no
    strings or character literals, could read otherwise than Lean 4.35. Each expected
    reading is Lean's: each text was elaborated in Lean 4.35 as written, alone in a scratch
    file outside the tree, where the names after its comments were defined, those within
    them unknown, and each of UNCLOSED refused as an unterminated comment. Then
    the three readers that call it, check_fidelity's `_blank_remarks`, check_style's
    `lean_note_spans` and the Jev generator's `comment_end`, each read them so too."""

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

    def test_the_jev_generator_runs_check_fidelity_s_own_reader(self):
        source = b'''raise AssertionError("unrelated top-level code ran")

def comment_end(src, i):
    return ("controlled reader", src, i)
'''
        checked = (REPO / "scripts/check_fidelity.py").resolve()
        with patch.object(self.questions, "read_no_follow", return_value=source) as read:
            reader = self.questions.shared_function(*self.questions.READER)
        read.assert_called_once_with(checked)
        self.assertEqual(reader("prefix /- comment -/ suffix", 7),
                         ("controlled reader", "prefix /- comment -/ suffix", 7))

    def test_the_jev_generator_delegates_to_check_fidelity_s_reader(self):
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


if __name__ == "__main__":
    unittest.main()
