- **III.25's kind passages are carried, where two dated texts call them helpers (docs,
  [#153](https://github.com/jackChallis/stoicheia/issues/153)).** The coordinator's orders
  of 25 October 2026 ask for this note. Two texts of 19 October 2026 describe the record
  of III.25 as it stood that day. The entry on III.25's segment kinds in
  [the decisions record](../briefs/0002-decisions.md) says that "The three passages in
  `review/III/25.toml` are helpers naming `Prop25.kind`", and the addition of 19 October to
  [brief 0006](../briefs/0006-statements.md#addition-19-october-2026-iii25s-segment-kinds)
  says that the record "makes all three existing kind passages `kind = "helper"`,
  `helper = "Prop25.kind"`". Both were true when written: commit 61e60553, that day, made
  the three kind passages `helper` passages naming `Prop25.kind`, and the record was stamped
  so at 58612ec. [review/SCHEMA.md](../../review/SCHEMA.md) then gave one case for a
  `carried` passage, "a porism proved as its own theorem", and admitted a companion beside
  it on 21 October ([#163](https://github.com/jackChallis/stoicheia/issues/163), commit
  ca0acb38).

  The record now does otherwise, as SCHEMA asks: a step proved as its own theorem, the
  proposition's porism or one of its companions, is declared as a `carried` passage that
  names it, and nothing else is carried this way: a lemma or another proposition that does
  a step makes a `helper` passage. `Prop25.kind` is the companion "III.25 kind", so when
  the records of Book III were drawn up at the stage full, on 22 October
  ([#29](https://github.com/jackChallis/stoicheia/issues/29)), the passages at "And it is
  manifest that the segment ABC is less than a semicircle" and "and ABC will clearly be a
  semicircle" became `carried`, naming `Prop25.kind`, as they are now. The third case's
  classification, the segment greater than a semicircle, is told in the note of the
  passage at "and if we construct, on the straight line BA", a `helper` naming
  `BookI.Prop23`, the step that passage does. `scripts/render.py` refuses a carried passage
  whose helper is not a porism or companion, so the page cannot show a lemma as proved
  separately.

  Both dated texts stand as they were written. This entry records the difference; it
  changes no record, statement, check or page.
