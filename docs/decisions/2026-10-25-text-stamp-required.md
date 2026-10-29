- **A review record without its `text` stamp fails, as one without any other stamp does
  (tooling, [#77](https://github.com/jackChallis/stoicheia/issues/77), item 2).** Item 2
  of card #77 asks that `scripts/check_fidelity.py` fail a record with no `text` stamp,
  which a note alone does not satisfy. The entry of 21 October 2026 on
  [the decisions page](../briefs/0002-decisions.md), "The `text` stamps' migration, and
  what it does not do", set this out as a check change of its own, after a records pull
  request: until every record had the stamp, failing on those without it would have
  stopped main, so the check named them in a note. That records train is the branch
  text/stamps-migrate, at d66e8bfc. There `scripts/review_stamp.py --migrate-text`, run on
  main at bedbba23, wrote `text` in the 63 records that lacked it, listed none for a
  reader and met no problem, so all 99 records carry `text`. It lands first, and this
  train follows it. This train changes no review record, no Lean file, statement,
  definition or lock, nor any `--` line, and `facts.json` stays as it was.

  `text` is now a stamp in `heath.FIELDS`, as `fingerprint`, `commit` and `lean` are.
  `heath.load_review` refuses a record without it unless an unstamped record is asked
  for: `review_stamp.py` asks so before it stamps, and `render.py`, `sweep_citations.py`
  and `check_acceptance.py` ask so to read a record whatever its stamps. So
  `check_fidelity.py`, which reads every record with its stamps required, fails a record
  with no `text`, naming the file, and `python3 scripts/heath.py`, which reads every
  record the same way, fails it too. The message for a missing stamp, whichever of the
  four, now says what to do: a reader reads the record and stamps it with
  `scripts/review_stamp.py --commit`, which writes it (WORKFLOW, section 6). For a record
  from an older branch that lacks only `text`, and whose text is as it was at its stamp
  commit, `review_stamp.py` run without `--commit` already points to `--migrate-text`,
  whose code this train leaves alone. The check's list of the records without `text`,
  the function that wrote its note, the note's printing and the clause of its docstring
  about the note are gone.
  `render.record_current`, by which the status table counts a record as current, no
  longer counts one with no `text` as current.

  `scripts/check_acceptance.py` and its tests are not changed. Its P2 takes each failure
  that the review checks of `check_fidelity.py` report of a record, save the three that
  P6 takes (a passage's `at` that begins no sentence, its `helper` not declared, and a run
  of `--` lines that no passage declares), and its P11 to P16 are assessed only for a
  record that `render.record_current` counts as current. So a record
  with no `text` now fails P2, with the message above, and each of its six items reads
  "not yet assessed: the record's stamps are not current (P2)". That was seen in a scratch
  copy of this tree, outside the repository, by calling the checklist's
  `check_certificate` and `check_review_items` in memory with I.1's `text` line taken
  away; with `heath.py` and `check_fidelity.py` as on the base, P2 said nothing of it.
  The copy holds no history, so I.1's items were not assessed there with the line in
  place either, for its commit, which the copy lacks. On the base every record carries
  `text`, so no verdict of the acceptance job changes.

  A new plant, `scripts/negative/missing_text.py`, takes I.1's `text` line out of its
  `[review]` table. It requires `check_fidelity.py` to fail, saying that the record's
  `text` is missing and what a reader does, and saying neither that the record's words
  have changed since it was reviewed nor a traceback. It then makes I.1's other stamps
  current in memory, so that on any branch only `text` decides, and requires
  `render.record_current` not to count the record current without it. The docstring of
  the plant in `scripts/negative/edited_note.py` said that I.1's record is given its
  `text` stamp "if it has none yet", so that the test held before and after the
  migration. Its code writes a current `text` over the one the record carries, which
  keeps the plant true on a branch that has edited the record, and the docstring now
  says that; the code is unchanged.

  Each mutant ran in a scratch copy of this tree, outside the repository, with a Git index
  of its own and no commit, through the copy's own `negative_tests` module, by calling
  the plant's `plant()` directly, since the runner's regressions need a commit. As
  written, both cases were refused. With `heath.py` and `check_fidelity.py` as on the
  base, `check_fidelity.py` passed and printed its note naming I.1, and the first case
  was not caught. With `heath.FIELDS` alone giving `text` as optional again,
  `check_fidelity.py` stopped on a `KeyError`, and the first case was not caught, its
  message missing and a traceback found. With `render.py` as on the base, the second case
  failed, since `render.record_current` counted the record current. With
  `check_fidelity.py` alone as on the base, the first case was still refused, by
  `heath.load_review`: the refusal is the schema's, and `check_fidelity.py` reports it. In
  the tree itself, the runner's `--plant missing_text --plant edited_note` passes both.

  Section 6 of [WORKFLOW](../WORKFLOW.md) and [CONTRIBUTING](../../CONTRIBUTING.md) lose
  their words for the time before every record carried `text`, and
  [review/SCHEMA.md](../../review/SCHEMA.md) its own, and the docstring of
  `scripts/sweep_citations.py` says that the records' `text` stamp covers `unused`, where
  it said that it would once #77 landed.

  Three things the plan names are not done here. The words for the migration in
  [`.github/pull_request_template.md`](../../.github/pull_request_template.md), its
  required box on the review records and the comment under "Review records", stay as they
  are: a record on an older branch may still gain only its `text` stamp from
  `--migrate-text`, so they stay true, and `scripts/safe_push.py` holds an open pull
  request's body to the box's words. PROGRAM.md's "where a record carries a `text` stamp"
  is the coordinator's to change. This change leaves open whether a stamp should also
  cover `[review]`'s `stage` and `items`, which the plan asks it to consider: that would
  be a check change of its own, with a migration.

  This entry approves the change to `scripts/heath.py`: `text` a stamp in `FIELDS`, a
  message for a missing stamp that says what a reader does, and the comment above
  `FIELDS` and the docstring of `validate_review` without their words for the migration.

  This entry approves the change to `scripts/check_fidelity.py`, which fails a record
  with no `text` through `heath.load_review`, compares a record's `text` with its text
  without asking first whether it has one, and keeps, writes and prints no note of the
  records without it.

  This entry approves the change to `scripts/render.py`, whose `record_current` holds a
  record with no `text` stamp to be not current, and whose docstring says so.

  This entry approves the change to `scripts/review_stamp.py`, whose docstring says that
  `--migrate-text` is for a record stamped before `text` was introduced, as one may be on
  an older branch; its code is as it was.

  This entry approves the change to `scripts/sweep_citations.py`, in its docstring alone,
  which says that the records' `text` stamp hashes a record as TOML reads it and covers
  `unused`.

  This entry approves the new file `scripts/negative/missing_text.py`, the plant of a
  record with no `text` stamp, with its two cases.

  This entry approves the change to `scripts/negative/edited_note.py`, in the docstring of
  its `plant` alone.

  This entry approves the change to `review/SCHEMA.md`: its `text` row without "for
  now"; its paragraph on the records stamped before `text`, which now says that `text` is
  required like the other stamps; and its sentence on `unused`, which says that the
  records' `text` stamp covers that key.

  This entry approves the change to `docs/ACCEPTANCE.md`, whose row for P2 asks for a
  current `text` with no "once it carries one".
