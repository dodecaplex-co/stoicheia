- **A forbidden circle rule may be proved from III.2 (certificate and checks,
  [#294](https://github.com/jackChallis/stoicheia/issues/294)).** Circle 2
  (`Tacit.inside_of_between`) and Circle 3 (`Tacit.outside_of_between`) say what III.2
  proves, and no certificate entry may rest on either. Until now the guard in
  `check_lock` accepted a forbidden rule missing from the axiom lock only as a theorem
  with the other forbidden rule beneath it, still an axiom in the lock: every entry using
  the theorem then rests on that axiom, and is refused by its axioms. Circle 2 is proved
  in that way, from Circle 3. Circle 3 can now be proved after III.2, from
  `Prop2.within`, but so proved it has no forbidden axiom beneath it, and the guard would
  refuse it, and with it the retirement of the last of the two axioms. Under the
  coordinator's ruling of 23 October, recorded on #294, the guard now also accepts a
  forbidden rule missing from the lock as a theorem whose proof cites III.2, while III.2's
  own entry is proved and rests on neither rule. The certificate records what each proved
  rule cites, in a new field, `proved_rule_cites`, found by the walk that finds the
  entries' own citations.

  This is no weaker. Every refusal stands. A rule missing from the lock and from
  `proved_rules` is refused as before, in the same words. A proved rule with neither a
  locked forbidden rule beneath it nor a proof that cites III.2 is refused, in words that
  now name both routes. An entry whose axioms hold a forbidden rule that is still an axiom
  is refused exactly as before. The new route has three refusals of its own, each naming
  the rule and III.2: III.2 has no entry in the certificate; III.2 is not proved; or III.2
  itself rests on either rule, among its axioms, its shared steps or the lemmas it
  inherits an axiom through, the circular case. A missing or malformed
  `proved_rule_cites` counts as citing nothing. And an entry using a rule proved from
  III.2 still cannot come before III.2. The walk that finds an entry's citations passes
  through the Tacit theorems, so the entry cites III.2 through the rule, and the check on
  later citations refuses it in Books I and II and in III.1, porisms and companions
  included; III.2 itself cannot use it, for Lean admits no circular proof. After III.2
  the use is an honest citation of the proposition that proves the rule.

  Circle 3 stays in the axiom lock for now: neither the lock nor anything under
  `Elements/` changes, and the certificate gains the new field alone. Retiring the axiom
  is the next train of #294. This is part of #294 and #152.

  This entry approves the change to `Certificate/Facts.lean`, which now writes
  `proved_rule_cites` beside `proved_rules`, for the same theorems, by the entries' walk.

  This entry approves the change to `scripts/check_fidelity.py`, whose `check_lock` takes
  a forbidden circle rule proved from a sound III.2 and refuses each other case by name.

  This entry approves the change to `Certificate/FIELDS.md`, which gives the new field
  `proved_rule_cites` its row among the fields of the top level.

  This entry approves the new plant `scripts/negative/circle_from_iii2.py`, which refuses
  both rules proved citing nothing or an III.2 resting on Circle 3, and passes them proved
  from III.2's real entry.

  This entry approves the change to `tests/test_negative_tests.py`, whose circle tests
  plant each case of the new route and test the new plant's three cases and restoration.
