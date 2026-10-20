#!/usr/bin/env python3
"""Focused cases for Certificate/Facts.lean's restricted-calculus C.N. 4 detection.

    export PATH=$HOME/.elan/bin:$PATH
    lake build
    python3 -I tests/test_certificate.py

Run the actual certificate source against a small Lean fixture, substituting only its
Elements import. A temporary Lake package keeps every output, including facts.json,
away from the repository. The fixture declares stand-ins with the exact constructor
names, so this test can land before the calculus it checks.

CI does not currently run this file. The tooling writer and the integrator run it
explicitly, as recorded in docs/briefs/0002-decisions.md. Standard library only.
"""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
AXIOM_FIELDS = ("axioms", "direct_axioms", "own_axioms", "inherited", "lean_foundations")


class CommonNotion4Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        source = (ROOT / "Certificate/Facts.lean").read_text()
        fixture = (ROOT / "tests/fixtures/CertificateCN4.lean").read_text()
        if source.count("\nimport Elements\n") != 1:
            raise AssertionError("expected exactly one Elements import in Facts.lean")
        source = source.replace("\nimport Elements\n", "\n" + fixture + "\n", 1)
        with tempfile.TemporaryDirectory(prefix="stoicheia-cn4-") as tmp:
            work = Path(tmp)
            (work / "lakefile.toml").write_text('name = "certificate_fixture"\n')
            (work / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())
            (work / "FactsFixture.lean").write_text(source)
            env = os.environ.copy()
            env["LEAN_PATH"] = str(ROOT / ".lake/build/lib/lean")
            result = subprocess.run(
                ["lake", "env", "lean", "FactsFixture.lean"],
                cwd=work, env=env, capture_output=True, text=True, timeout=120,
            )
            if result.returncode:
                raise AssertionError(
                    f"fixture: lake env lean exited {result.returncode}\n"
                    + result.stdout + result.stderr
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
