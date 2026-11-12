<!-- entry: id=proved-rule-foundations cards=629 line="The certificate records Lean's foundations beneath each proved tacit rule." -->

- **Foundations beneath proved rules (certificate).** The owner approved the table
  `proved_rule_foundations` for [#629](https://github.com/dodecaplex-co/stoicheia/issues/629).
  On 10 November 2026 the owner wrote: "questions through 48 - yes".
  The approval covers one new table of the public certificate; every other
  certificate field is unchanged.

  `Certificate/Facts.lean` computes that table from Lean's axiom collection for the
  theorems it lists as proved tacit rules. `Certificate/FIELDS.md` defines its keys,
  values and ordering. These lists show whether a proved tacit rule depends on Lean's
  foundations or `sorryAx`; `proved_rules` lists its Euclidean axioms.
  `facts.json` is the build machine's generated certificate, including that table.

  `scripts/negative/proved_rule_foundations.py` exercises the producer in an isolated
  test package: a proof without foundations, a proof using `Classical.choice`, and a
  proof using `sorry`. Its literal verifier refuses either required name lost from
  the emitted table. It runs in the edition's negative suite.

  This decision approves no change to a statement, no axiom and no Lean under
  `Elements/`. `Certificate/axioms.lock` has 48 assumptions and is unchanged.
