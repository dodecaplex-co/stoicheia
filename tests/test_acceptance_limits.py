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
        # Every allowance has gone (#116, #162): the script and the table name none.
        expected = {}
        self.assertEqual(acceptance.ALLOWED_LIMITS, expected)
        text = (ROOT / "docs/ACCEPTANCE.md").read_text(encoding="utf-8")
        section = text.split("## The limitations allowed\n", 1)[1].split("\n## ", 1)[0]
        # Every line of the section that holds a | is read (#421): the header and its
        # delimiter row as the table has them today, then each row, however compact or
        # indented; a | anywhere else fails, so that no row written with a | is passed over.
        lines = [line.strip() for line in section.splitlines() if "|" in line]
        self.assertEqual([line for line in lines if not line.startswith("|")], [],
                         "a line of the section holds a | but begins no row of the table")
        header = ["| Proposition | Scope | Tag | Why |", "|---|---|---|---|"]
        self.assertEqual(lines[:2], header,
                         "the table's header has changed: read its rows by the new one")
        rows = [line.split("|")[1:-1] for line in lines[2:]]
        self.assertEqual(
            [(ref.strip(), scope.strip(), tag.strip().strip("`"))
             for ref, scope, tag, why in rows],
            [(ref, scope, tag) for ref, (scope, tag) in expected.items()],
        )

    def test_an_allowed_row_asks_its_scope_and_tag(self):
        # The table is empty, so a made-up row keeps P3's two refusals for a listed
        # proposition tested: the scope not allowed, and the allowed scope without its tag;
        # and the row does not allow III.31, given the same tag (#421).
        with patch.object(acceptance, "ALLOWED_LIMITS",
                          {"III.16": ("partial", "mixed-angles-omitted")}):
            self.assertEqual(
                self.p3_failures("III.16", "partial", ["mixed-angles-omitted"]), [])
            for tags in ([], ["mixed-angles-local"]):
                with self.subTest(tags=tags):
                    self.assertEqual(self.p3_failures("III.16", "partial", tags), [
                        "a partial statement allowed only as `mixed-angles-omitted`, "
                        "and the record does not carry that tag",
                    ])
            self.assertEqual(self.p3_failures("III.16", "restricted", ["mixed-angles-omitted"]),
                             self.unlisted("restricted"))
            self.assertEqual(self.p3_failures("III.31", "partial", ["mixed-angles-omitted"]),
                             self.unlisted("partial"))

    def test_a_row_for_a_full_record_fails(self):
        # An allowance that outlives its need is stale (#162, item 3): with made-up rows for
        # III.16 and I.45, each full record fails P3 with its own row's scope and tag,
        # whether it carries III.16's row tag, none, or the tag III.16's record carries; and
        # III.31, a full record no row names, still passes.
        def stale(scope, tag):
            return [f"the statement is full, so its allowance as a {scope} statement with "
                    f"`{tag}` is stale: its row in ALLOWED_LIMITS and in "
                    "docs/ACCEPTANCE.md's table is to go"]
        with patch.object(acceptance, "ALLOWED_LIMITS",
                          {"III.16": ("partial", "mixed-angles-omitted"),
                           "I.45": ("restricted", "figure-with-dissection")}):
            for ref, expected in (("III.16", stale("partial", "mixed-angles-omitted")),
                                  ("I.45", stale("restricted", "figure-with-dissection")),
                                  ("III.31", [])):
                for tags in ([], ["mixed-angles-omitted"], ["mixed-angles-local"]):
                    with self.subTest(ref=ref, tags=tags):
                        self.assertEqual(self.p3_failures(ref, "full", tags), expected)

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
        # The list as it is, empty, names no proposition, so a full statement passes whatever
        # its tags; one that a row names fails, as stale (test_a_row_for_a_full_record_fails).
        for ref in ("I.45", "II.14", "III.16", "III.31"):
            for tags in ([], ["figure-with-dissection"], ["mixed-angles-omitted"]):
                with self.subTest(ref=ref, tags=tags):
                    self.assertEqual(self.p3_failures(ref, "full", tags), [])

    def test_mixed_angles_full_pass(self):
        # III.16 and III.31 state their mixed angles, so their records are full.
        for ref in ("III.16", "III.31"):
            with self.subTest(ref=ref):
                book, number = ref.split(".")
                record = acceptance.heath.load_review(book, int(number), require_stamp=False)
                self.assertEqual(record["statement"]["scope"], "full")
                self.assertEqual(self.p3_failures(
                    ref, "full", record["representation"]["tags"],
                    route=record["route"]["kind"]), [])

    def test_mixed_angles_short_of_full_fail_whatever_tags(self):
        # #162: their allowance has gone, so a partial or restricted statement of either
        # fails as any limitation the table does not name, with the old tag or another.
        for ref in ("III.16", "III.31"):
            for scope in ("restricted", "partial"):
                for tags in ([], ["mixed-angles-omitted"], ["mixed-angles-local"],
                             ["figure-with-dissection"]):
                    with self.subTest(ref=ref, scope=scope, tags=tags):
                        self.assertEqual(self.p3_failures(ref, scope, tags),
                                         self.unlisted(scope))

    def test_alternative_route_still_fails(self):
        alternative = ["the route is an alternative argument, which is no deliberate "
                       "limitation of Books I-III: Euclid's own argument is due"]
        cases = (("I.45", "figure-with-dissection"), ("II.14", "figure-with-dissection"),
                 ("III.16", "mixed-angles-omitted"), ("III.31", "mixed-angles-omitted"))
        for ref, tag in cases:
            with self.subTest(ref=ref):
                self.assertEqual(
                    self.p3_failures(ref, "full", [tag], route="alternative"), alternative)
        for ref, tag in cases:
            with self.subTest(ref=ref, scope="restricted"):
                self.assertEqual(self.p3_failures(
                    ref, "restricted", [tag], route="alternative"),
                    self.unlisted("restricted") + alternative)


if __name__ == "__main__":
    unittest.main(verbosity=2)
