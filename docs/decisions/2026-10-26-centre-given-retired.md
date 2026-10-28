- **The tag `centre-given` retired, and III.1's certificate pinned to the centre rule
  (checks, [#59](https://github.com/jackChallis/stoicheia/issues/59)).** The coordinator
  assigned this change on 26 October 2026, from ship C7's check of #59 against main at
  560da15a (the issue's comment of 25 October). It carries out step 7 of
  [brief 0008](../briefs/0008-centre.md), under the owner's decision of 18 October that
  `centre-given` "is retired where it only explained the missing rule"
  ([decisions record](../briefs/0002-decisions.md)). No Lean file, lock, statement,
  definition, record or `--` line changes.

  The tag. `[tag.centre-given]` said that a statement gave the circle its centre, named or
  as `∃ G, Centre G α`, as a hypothesis. Where the hypothesis asked only that some centre
  exist, the centre rule, once locked, gives it for every circle, and those statements now
  take a centre inside their proofs (step 6). By brief 0008's rule for each statement, a
  named centre that appears elsewhere in the statement is kept, since the existence of
  some centre does not identify it, and one that appears nowhere else is dropped, as an
  existence hypothesis in substance. Since step 6 no record carries the tag: before this
  change `grep -rl centre-given review` found only `review/terms.toml`, and after it
  finds nothing. No script or test names it. Brief 0008's step 7 takes it out of
  `review/terms.toml` in a pull request of its own, since that file is protected; this is
  that pull request. The record schema now refuses the tag, as it refuses any tag that
  `review/terms.toml` does not define.

  The pin. III.1 takes a centre from the rule in two places, inside its construction to
  prove that D is within and in its reductio for the supposed centre G, so its
  certificate carries `Tacit.exists_centre`, and `facts.json` gives it 39 tacit rules.
  Its expectation in `tests/certificate_expectations.json` counted those 39 but did not
  name the rule, so a certificate in which another tacit rule took its place would pass.
  The expectation now also `includes` `Tacit.exists_centre`, its `why` says so, and the
  count stays at 39. The check is only stricter: main passes it as it is, and a plant that
  replaces the rule in III.1's certificate by another tacit rule, the count unchanged,
  passes the old expectation and fails the new.

  The protected files. This entry approves the change to `review/terms.toml`.
  This entry approves the change to `tests/certificate_expectations.json`.
