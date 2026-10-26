- **The worked example of III.16 is its current record, and `mixed-angles-omitted` goes
  (tooling, [#162](https://github.com/jackChallis/stoicheia/issues/162), item 5).** The
  coordinator's orders of 25 October 2026 assign item 5 of card #162 to this change, a
  check train of its own. Since III.16 and III.31 state their mixed angles, no record
  carries the tag `mixed-angles-omitted`. It stayed in `review/terms.toml` only because the
  worked example of III.16 in `review/SCHEMA.md` carried it, as III.16 stood at commit
  d040117, and the contracts' self-test in `scripts/heath.py` checks each example against
  the tags. The entry
  [Check inputs after C6a](2026-10-23-check-inputs-after-c6a.md) said so, and proposed
  this change without making it.

  The first worked example is now III.16's record whole, copied from `review/III/16.toml`
  as it stands at commit 560da15a2: full, with its three companions, its modified route,
  `mixed-angles-local`, fourteen passages of five kinds, its figure and its review. Its
  stamps are the record's own, since comments do not count towards `heath.text_hash`; the
  prose before it gives the fingerprint `heath.review_fingerprint` computes for III.16 at
  that commit, `sha256:bbe980064221ec4c`, of its statement, its porism's and its three
  companions'. The paragraph after it, which told how III.16 had changed since d040117, goes,
  since the example is now the record as it stands. The example of I.40 stays as it was,
  the fixture from commit d040117. The self-test still checks two examples, and both hold.

  The tag `mixed-angles-omitted` leaves `review/terms.toml`. The
  [decisions record](../briefs/0002-decisions.md) kept it "while a record uses it", and none
  does. `docs/FORMALIZATION.md` no longer names it, so it does not change. The cases in
  `tests/test_acceptance_limits.py` that give a record the tag in memory, to show that P3
  refuses III.16 and III.31 short of full whatever their tags and fails a stale allowance,
  pass unchanged: P3 compares a record's tags with an allowance's, and never looks a tag up
  in the terms.

  Nothing is loosened: no check, test, expected value or lock changes, and no record,
  Lean file, mishnah, figure or generated page.

  This entry approves the first worked example in `review/SCHEMA.md`, III.16's record at
  commit 560da15a2, with the prose before it and without the paragraph that followed it.

  This entry approves the removal of `[tag.mixed-angles-omitted]` from `review/terms.toml`.
