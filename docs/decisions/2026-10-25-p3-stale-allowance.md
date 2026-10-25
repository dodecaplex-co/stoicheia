- **P3 refuses an allowance whose record is already full (tooling,
  [#162](https://github.com/jackChallis/stoicheia/issues/162), item 3).** The
  coordinator's orders of 25 October 2026, at 13:40, assign item 3 of card #162 to this
  change, a check train of its own. P3 of the acceptance checklist allows a statement
  short of full only when `ALLOWED_LIMITS` in `scripts/check_acceptance.py` names it, with
  the tag that says why, and the table of
  [ACCEPTANCE, "The limitations allowed"](../ACCEPTANCE.md#the-limitations-allowed) gives
  the same row. But the check looked a proposition up in that list only when its record's
  scope was not full, and `test_full_statements_pass_with_or_without_tag` in
  `tests/test_acceptance_limits.py` held that a full record passes whatever the list
  holds. So an allowance that had outlived its need, its record made full while its row
  stayed in the list and in the table, was never caught, and the checklist went on
  allowing a limitation that no record kept.

  Now P3 fails a full record whose proposition the list names, with the message that its
  allowance is stale and that its row in `ALLOWED_LIMITS` and in the table is to go. A
  comment over `ALLOWED_LIMITS` says so, and the section that holds the table says it in a
  sentence of its own. Nothing else in P3 changes: a statement short of full is judged as
  before, and so is the route. The list and the table have been empty since pull request
  #414, so no record fails for it; the change only makes P3 stricter. The P3 row of the
  checklist's item table stays as it is, since it is still true, and the section under it
  now says the rest.

  The test file gains `test_a_row_for_a_full_record_fails`. It patches the list with two
  made-up rows, one allowing III.16 partial with the tag `mixed-angles-omitted` and one
  allowing I.45 restricted with `figure-with-dissection`, and asks that each, made full,
  fail P3 with exactly the new message for its own row's scope and tag, with the tag
  `mixed-angles-omitted`, with none, and with `mixed-angles-local`, the tag III.16's
  record carries; and that III.31, full with the same tags, still pass, since no row
  names it. The case of full statements runs with the real list, which is empty, so it
  holds as before: a comment now says so and points to the new case, and none of its
  assertions goes.

  Each part was checked by mutation, with `scripts/check_acceptance.py` changed in place
  and restored after each run. With the new branch of P3 taken out, the new case failed on
  its six subtests for III.16 and I.45, and the other seven cases passed. With the message
  written for III.16's row alone, it failed on its three subtests for I.45. With the
  branch made to refuse every full record whenever the list holds any row, it failed on
  its three subtests for III.31. Unmutated, all eight pass. On the records of
  `230b92bd4574`, which the change does not touch,
  `python3 scripts/check_acceptance.py --quick` gave the same P3 verdicts with the check
  as it was and as it is now: none of the 99 propositions fails P3.

  This entry approves the change to `scripts/check_acceptance.py`: P3's refusal of an
  allowance for a full statement, with its message, and the comment over `ALLOWED_LIMITS`.

  This entry approves `tests/test_acceptance_limits.py` with its new case for a row that
  names a full record, and the comment on the case of full statements.

  This entry approves the sentence added to `docs/ACCEPTANCE.md`, under "The limitations
  allowed", that P3 fails a full record that the table still names.
