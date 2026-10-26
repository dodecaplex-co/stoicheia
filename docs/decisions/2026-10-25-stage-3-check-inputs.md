- **Two check inputs follow stage 3: the review schema's example of an alternative route,
  and the style check's hold on the overlap catalogue (checks,
  [#23](https://github.com/jackChallis/stoicheia/issues/23),
  [#25](https://github.com/jackChallis/stoicheia/issues/25)).** The coordinator's orders of
  25 October 2026 assign this change. Stage 3 moved into `Elements/` with train C6a
  ([#240](https://github.com/jackChallis/stoicheia/pull/240), 21 October): III.24 now
  applies one segment to the other, as Euclid does, and its record has the scope `full` and
  the route `modified`, with the proof by the radii kept as the companion
  `Prop24.equalCircles` and shown on the page as the alternative. Two check inputs still
  spoke of stage 3 as to come. Both are brought up to date here, apart from the prose and
  the report that stage 3 also left behind, which are content and land separately. No
  Lean file, lock, statement, definition, record or `--` line changes.

  The review schema's bullet for the route `alternative` gave as its example III.24's
  proof by the radii, "once stage 3 gives Euclid's own". Stage 3 has given it, and no
  record has that route now; item P3 of [ACCEPTANCE](../ACCEPTANCE.md) refuses it in Books
  I to III. The example now says so, and says how such a proof is kept there instead: as a
  companion beside Euclid's route, as `Prop24.equalCircles` is beside III.24's `modified`
  route. The bullet's definition of the route is unchanged.

  The style check held the overlap catalogue, `docs/reports/overlaps.md`, from S7 until
  stage 3's overlap entries were written (`REACH_PENDING`, naming #25). At commit 56f85f3
  on a built tree, `python3 scripts/check_style.py` reports that entry done (D16): no
  finding of S7 is left in the catalogue. The entry comes out, so a new S7 finding there
  fails as it would in any file; the change is only stricter, and the catalogue passes
  as it is. The two other entries that name #25 stay, since each file still has a
  finding of S12: the gap catalogue of Book III (`BookI.PropN` and `BookII.PropN`, at
  its line 48) and Book I's front page (`Circumference.semicircle`, a theorem of Book III,
  at its line 30).

  This entry approves the change to `review/SCHEMA.md`, where the example of the route
  `alternative` no longer waits for stage 3.

  This entry approves the change to `scripts/check_style.py`, where the entry of
  `REACH_PENDING` for `docs/reports/overlaps.md` is taken out and nothing else changes.
