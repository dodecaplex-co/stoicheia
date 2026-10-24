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

    @staticmethod
    def unlisted(scope):
        return [f"the statement is {scope}: every statement of Books I-III is full "
                "but for the limitations docs/ACCEPTANCE.md names"]

    def test_allowed_limits_and_table(self):
        expected = {
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

    def test_figures_short_of_full_fail_whatever_tags(self):
        # #116: the allowance for I.45 and II.14 is withdrawn, so a restricted or partial
        # statement of either fails as any limitation the table does not name.
        for ref in ("I.45", "II.14"):
            for scope in ("restricted", "partial"):
                for tags in ([], ["figure-with-dissection"], ["side-not-square"],
                             ["figure-with-dissection", "side-not-square"]):
                    with self.subTest(ref=ref, scope=scope, tags=tags):
                        self.assertEqual(self.p3_failures(ref, scope, tags),
                                         self.unlisted(scope))

    def test_full_statements_pass_with_or_without_tag(self):
        for ref in ("I.45", "II.14", "III.16", "III.31"):
            for tags in ([], ["figure-with-dissection"], ["mixed-angles-omitted"]):
                with self.subTest(ref=ref, tags=tags):
                    self.assertEqual(self.p3_failures(ref, "full", tags), [])

    def test_partial_mixed_angles_with_tag_pass(self):
        for ref in ("III.16", "III.31"):
            with self.subTest(ref=ref):
                self.assertEqual(
                    self.p3_failures(ref, "partial", ["mixed-angles-omitted"]), [])

    def test_partial_mixed_angles_without_tag_fail(self):
        for ref in ("III.16", "III.31"):
            for tags in ([], ["mixed-angles-local"], ["figure-with-dissection"]):
                with self.subTest(ref=ref, tags=tags):
                    self.assertEqual(self.p3_failures(ref, "partial", tags), [
                        "a partial statement allowed only as `mixed-angles-omitted`, "
                        "and the record does not carry that tag",
                    ])

    def test_restricted_mixed_angles_fail(self):
        for ref in ("III.16", "III.31"):
            for tags in ([], ["mixed-angles-omitted"]):
                with self.subTest(ref=ref, tags=tags):
                    self.assertEqual(self.p3_failures(ref, "restricted", tags),
                                     self.unlisted("restricted"))

    def test_alternative_route_still_fails(self):
        alternative = ["the route is an alternative argument, which is no deliberate "
                       "limitation of Books I-III: Euclid's own argument is due"]
        for ref, scope, tag in (("I.45", "full", "figure-with-dissection"),
                                ("II.14", "full", "figure-with-dissection"),
                                ("III.16", "partial", "mixed-angles-omitted"),
                                ("III.31", "partial", "mixed-angles-omitted")):
            with self.subTest(ref=ref):
                self.assertEqual(
                    self.p3_failures(ref, scope, [tag], route="alternative"), alternative)
        for ref in ("I.45", "II.14"):
            with self.subTest(ref=ref, scope="restricted"):
                self.assertEqual(self.p3_failures(
                    ref, "restricted", ["figure-with-dissection"], route="alternative"),
                    self.unlisted("restricted") + alternative)


if __name__ == "__main__":
    unittest.main(verbosity=2)
