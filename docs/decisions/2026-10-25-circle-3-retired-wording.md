- **Three corrections to the entry on Circle 3's retirement, and a note on its wrap
  (docs, [#436](https://github.com/jackChallis/stoicheia/issues/436), item 2).** The last
  review of #294's retirement, C7-c294b-rev4, found four points of wording in the entry of
  24 October, [Circle 3 retired after III.2](2026-10-24-circle-3-retired.md). The train had
  used its two rounds of fixes by then, and an entry on main is history, never edited; so
  this entry corrects it instead.

  Its paragraph on the model says that the numerical harness keeps checking Circle 3's
  predicate "as the preparation of 24 October arranged". Three preparations of the
  retirement bear that date, and the next sentence names another of them. The one meant
  is the preparation that kept the predicate as a derived property,
  `derived.outside_of_between`, which has
  [an entry of its own](2026-10-24-circle-3-derived.md).

  The same paragraph says that the kind `'out'` of `gs_cm` "goes later, in a change of its
  own", and that the examples of Circle 3 as an axiom in `Certificate/FIELDS.md` and
  `review/SCHEMA.md` follow in another, naming no issue for either. The kind is item 1 of
  #436, and the examples are
  [#428](https://github.com/jackChallis/stoicheia/issues/428).

  It says the kind had to stay because, in that train, a harness could change "only in
  the laws" that moved with their axioms. The rule is narrower: `laws_move_with_axioms` in
  `scripts/safe_push.py` compares each harness's code outside its laws with main's,
  leaving out comments and the file's own docstring. So the kind's code had to stay in
  that train, but its comment, which named a law the file no longer had, could have gone
  with the law.

  Last, the words "The counts" stand alone on a line of that paragraph, left by a rewrap
  during a merge. That changes no meaning, and the line stays as it is.

  The coordinator filed these points as item 2 of #436, for a later entry, and its orders
  of 24 October give that entry to this change. This entry claims no approval of the owner.
