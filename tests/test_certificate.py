#!/usr/bin/env python3
"""Focused cases for Certificate/Facts.lean's restricted-calculus C.N. 4 detection.

    export PATH=$HOME/.elan/bin:$PATH
    lake build
    python3 -I tests/test_certificate.py

Run an unmodified copy of the certificate source against a small Lean fixture compiled
as the temporary package's Elements module. The temporary module takes precedence over
the repository's Elements module while retaining access to its foundation modules. The
package keeps every output, including facts.json, away from the repository. The fixture
declares stand-ins with the exact constructor names, so this test can land before the
calculus it checks.

Each coincidence constructor is tested directly and through a helper's value. Reaching
only the inductive type's constructor list (I.7), or naming another Derives constructor
in a value (I.8), reports no C.N. 4. Every case must keep the same axiom fields.

The foundation modules must be built first. CI does not yet run this file: whoever
changes Certificate/Facts.lean, and the integrator, run it explicitly on the revision
delivered, as recorded in docs/WORKFLOW.md, section 8. Standard library only.
"""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
AXIOM_FIELDS = ("axioms", "direct_axioms", "own_axioms", "inherited", "lean_foundations")


class CommonNotion4Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with tempfile.TemporaryDirectory(prefix="stoicheia-cn4-") as tmp:
            work = Path(tmp)
            (work / "lakefile.toml").write_text('name = "certificate_fixture"\n')
            (work / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())
            shutil.copyfile(ROOT / "tests/fixtures/CertificateCN4.lean", work / "Elements.lean")
            shutil.copyfile(ROOT / "Certificate/Facts.lean", work / "Facts.lean")
            env = os.environ.copy()
            repository_modules = str(ROOT / ".lake/build/lib/lean")
            if inherited_modules := env.get("LEAN_PATH"):
                repository_modules += os.pathsep + inherited_modules
            env["LEAN_PATH"] = repository_modules
            fixture_modules = work / ".lake/build/lib/lean"
            fixture_modules.mkdir(parents=True)
            shutil.copytree(
                ROOT / ".lake/build/lib/lean/Elements/Foundations",
                fixture_modules / "Elements/Foundations",
            )
            fixture_result = subprocess.run(
                [
                    "lake", "env", "lean", "Elements.lean",
                    "-o", str(fixture_modules / "Elements.olean"),
                ],
                cwd=work, env=env, capture_output=True, text=True, timeout=120,
            )
            if fixture_result.returncode:
                raise AssertionError(
                    f"fixture: lake env lean exited {fixture_result.returncode}\n"
                    + fixture_result.stdout + fixture_result.stderr
                )
            env["LEAN_PATH"] = str(fixture_modules) + os.pathsep + repository_modules
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
        if set(cls.entries) != {f"I.{i}" for i in range(1, 9)}:
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


if __name__ == "__main__":
    unittest.main(verbosity=2)
