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
  stamps are the record's own, since the block is the record byte for byte, its first
  line, `# review/III/16.toml`, included; the prose before it gives the fingerprint
  `heath.review_fingerprint` computes for III.16 at that commit,
  `sha256:bbe980064221ec4c`, of its statement, its porism's and its three companions'. The
  paragraph after it, which told how III.16 had changed since d040117, goes, since the
  example is now the record as it stands. The example of I.40 stays as it was, the fixture
  from commit d040117. The self-test still checks two examples, and both hold.

  The tag `mixed-angles-omitted` leaves `review/terms.toml`. The [decisions
  record](../briefs/0002-decisions.md) kept it "while a record uses it", and none does.
  `docs/FORMALIZATION.md` no longer names it, so it does not change. Every case in
  `tests/test_acceptance_limits.py` that gives a record the tag in memory passes,
  unchanged by item 5's commits: those that show what P3 does with a made-up allowance and
  with a stale one, that it refuses III.16 and III.31 short of full and passes them full
  whatever their tags, and that it refuses an alternative route. P3 compares a record's
  tags with an allowance's, and never looks a tag up in the terms.

  Item 5 loosens nothing: its commits change no check, test or lock (item 3's change to
  P3, on the same branch, has its own entry), and no record, Lean file, mishnah, figure or
  generated page. The example's stamps change with it, to the record's own: its `text`,
  which the self-test reads as a test value of `heath.text_hash`, and its fingerprint. The
  old example was the only partial record the self-test read, with `omitted`, a
  `[coverage]` map and an `unformalized` passage, and no record on main is partial now; so
  the self-test no longer runs those branches of `heath.validate_review`, and restoring
  them is left to a change of its own.

  This entry approves the first worked example in `review/SCHEMA.md`, III.16's record at
  commit 560da15a2, with the prose before it and without the paragraph that followed it.

  This entry approves the removal of `[tag.mixed-angles-omitted]` from `review/terms.toml`.
