- **The check inputs follow train C6a: III.16 and III.31 allowed only full, and contact
  within read with its point (checks,
  [#214](https://github.com/jackChallis/stoicheia/issues/214)).** Train C6a states and
  proves the mixed-angle clauses of III.16 and III.31, as companions in
  `Elements/BookIII/Prop16.lean` and `Elements/BookIII/Prop31.lean` on the shared steps of
  `Elements/BookIII/MixedAngles.lean`, and its records of both propositions have the scope
  `full`. It also gives contact within the definition that
  [brief 0008](../briefs/0008-centre.md) chose in its question 16: `TouchesInternally` now
  asks for a point of the inner circle within the outer, beside no point of it outside.
  Three check inputs still described the edition as it stood before that train. This
  change brings each up to date and carries no content, so it lands in a pull request of
  its own, after the train, as a check change must. This closes #214.

  First, the tag `touching-whole-circles` said of touching within only that no point of
  the inner circle is outside the outer. Its meaning now says what the definition says: a
  point of the inner is within the outer, and no point of the inner is outside it. The
  rest of the meaning, the tag's kind and its name stay. The decisions page's entries of
  19 and 21 October left this wording to a later check change, and this is that change.
  No page shows the meaning: the records of III.6, III.11, III.12 and III.13 each carry a
  representation note of their own, which their pages show in its place.

  Second, acceptance item P3 allowed III.16 and III.31 to be partial, with the tag
  `mixed-angles-omitted`, and
  [#162](https://github.com/jackChallis/stoicheia/issues/162) asked for those allowances
  to go once both records were full. Their rows leave `ALLOWED_LIMITS`, the expected table
  of the limitations' test module, and the table "The limitations allowed" in
  [ACCEPTANCE](../ACCEPTANCE.md), whose paragraph after the table now says that they have
  gone. P3 passes a full record whatever the table holds, so both records pass as they
  did, and a partial III.16 or III.31 is now refused, whatever its tags. Two new cases
  pin that: each record is full and passes P3, and each, made partial in memory with
  `mixed-angles-omitted` or with `mixed-angles-local`, is refused. Since
  [#249](https://github.com/jackChallis/stoicheia/issues/249) ACCEPTANCE is a check input
  and a protected path, so its table, `ALLOWED_LIMITS` and their test change together in
  this one check change.

  Third, the worked example for III.16 said that III.16 "is partial". Its prose now says
  that III.16 was partial at `d040117`, and a new paragraph after the example says what
  III.16's current record holds, as the paragraph after I.40's example already does for
  I.40. No value the tests read changes: the TOML block, its stamps, its fingerprint
  `sha256:9fd59073303dbcdc` and the commit `d040117` stay as they were, and the
  contracts' self-test still checks two examples.

  The tag `mixed-angles-omitted` stays, though no record carries it after the train: the
  contracts' self-test checks the worked example against the tags, and the example
  carries it. Its meaning named III.16 and III.31 as its users, and gave as its reason
  that our angles are made by two straight lines, which stopped being true when the
  edition gained its mixed angles. The meaning now keeps what the tag records, a clause
  about such an angle left out, with the rectilineal facts Euclid proves it by stated;
  and it says that no record carries the tag, and that the worked example shows it, as
  III.16 stood at `d040117`. Removing the tag would take the example with it, or need an
  example of another partial statement; that is proposed here, not done.

  The change tightens P3 and makes four descriptions true. It loosens nothing: no check,
  test, expected value or lock is weakened, and no record, Lean file, mishnah, figure or
  generated page changes.

  This entry approves the new meanings of two tags in `review/terms.toml`.
  It approves the past tense and the new paragraph of the worked
  example in `review/SCHEMA.md`.
  It approves the two rows taken out of `ALLOWED_LIMITS` in `scripts/check_acceptance.py`.
  It approves the two rows taken out of the table "The limitations allowed" in
  `docs/ACCEPTANCE.md`, and the paragraph after that table which says they have gone.
  It approves the shorter expected table and the two new
  cases of `tests/test_acceptance_limits.py`.
