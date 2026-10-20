"""Cases for the limitations allowed by acceptance item P3.

Run with: python3 -I tests/test_acceptance_limits.py
The records are varied in memory; no repository file is changed and no Lean build runs.
"""

import json
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import check_acceptance as acceptance  # noqa: E402


class AllowedLimits(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.facts = json.loads((ROOT / "facts.json").read_text(encoding="utf-8"))

    def p3_failures(self, ref, scope, tags, route="euclid"):
        book, number = ref.split(".")
        record = acceptance.heath.load_review(book, int(number), require_stamp=False)
        record["statement"]["scope"] = scope
        record["representation"]["tags"] = tags
        record["route"]["kind"] = route
        with patch.object(acceptance, "refs", return_value=[(book, int(number), ref)]), \
                patch.object(acceptance, "failures", {}):
            acceptance.check_propositions(self.facts, {ref: record})
            return acceptance.failures.get((ref, "P3"), [])

    def test_allowed_limits_and_table(self):
        expected = {
            "I.45": ("restricted", "figure-with-dissection"),
            "II.14": ("restricted", "figure-with-dissection"),
            "III.16": ("partial", "mixed-angles-omitted"),
            "III.31": ("partial", "mixed-angles-omitted"),
        }
        self.assertEqual(acceptance.ALLOWED_LIMITS, expected)
        text = (ROOT / "docs/ACCEPTANCE.md").read_text(encoding="utf-8")
        section = text.split("## The limitations allowed\n", 1)[1].split("\n## ", 1)[0]
        rows = [line.split("|")[1:-1] for line in section.splitlines()
                if line.startswith("| I")]
        self.assertEqual(
            [(ref.strip(), scope.strip(), tag.strip().strip("`"))
             for ref, scope, tag, why in rows],
            [(ref, scope, tag) for ref, (scope, tag) in expected.items()],
        )

    def test_restricted_figures_with_tag_pass(self):
        for ref in ("I.45", "II.14"):
            with self.subTest(ref=ref):
                self.assertEqual(
                    self.p3_failures(ref, "restricted", ["figure-with-dissection"]), [])

    def test_restricted_figures_without_tag_fail(self):
        for ref in ("I.45", "II.14"):
            for tags in ([], ["side-not-square"]):
                with self.subTest(ref=ref, tags=tags):
                    self.assertEqual(self.p3_failures(ref, "restricted", tags), [
                        "a restricted statement allowed only as `figure-with-dissection`, "
                        "and the record does not carry that tag",
                    ])

    def test_partial_figures_still_fail(self):
        for ref in ("I.45", "II.14"):
            with self.subTest(ref=ref):
                self.assertEqual(
                    self.p3_failures(ref, "partial", ["figure-with-dissection"]), [
                        "the statement is partial: every statement of Books I-III is full "
                        "but for the limitations docs/ACCEPTANCE.md names",
                    ])

    def test_alternative_route_still_fails(self):
        for ref in ("I.45", "II.14"):
            with self.subTest(ref=ref):
                self.assertEqual(self.p3_failures(
                    ref, "restricted", ["figure-with-dissection"], route="alternative"), [
                        "the route is an alternative argument, which is no deliberate "
                        "limitation of Books I-III: Euclid's own argument is due",
                    ])


if __name__ == "__main__":
    unittest.main(verbosity=2)
