- **A planted kind that cannot make a genuine fault on its base does not apply to it (#36).**
  [The bar's entry](2026-10-25-jev-calibration-bar.md) gives each question's plants its
  kinds of fault in turn, each kind with a test the generator runs on the row, and
  [the rulings entry](2026-10-26-jev-calibration-rulings.md) restates P13's list for Book
  III, so that its tenth plant is III.36, due P13's fifth kind, "the one bridge that a
  needed connection rests on removed, the others kept". The kind's test, that the row
  supplies two bridges or more, passes on III.36. But the independent review of the
  generator found that no change within the kind makes a genuine fault there, and the
  Lean bears it out: III.36's bridges overlap in pairs. `Rectangle.eq_rect` is
  `Rectangle.contained` composed with `rect_congr`, so that each gives `rect` of a drawn
  rectangle, and `Square.eq_sq` and `Square.described` each give `sq`; no single supplied
  bridge carries a needed connection alone, so that with any one removed a careful reader
  could fairly answer "bridge stated". The entries did not say what happens when a kind's
  test passes and no change within the kind makes its fault. This question arose before
  any request of the calibration, or of the audit it gates, had been sent, and on 26
  October 2026 the coordinator ruled on it. This is the coordinator's ruling, not the
  owner's; the coordinator's record of it is
  [#36](https://github.com/jackChallis/stoicheia/issues/36). The ruling: "a planted kind
  that cannot make a genuine fault on its base does not apply to that base. The base takes
  the next kind in the entry's order (for III.36, kind 1), with the reason recorded. If no
  kind applies, the next base by the same hash rule replaces it, also recorded." Where this
  ruling and the bar's entry or the rulings entry differ, this ruling governs the
  calibration.

  So III.36's plant for P13 passes over the fifth kind, with the reason above recorded in
  the manifest beside the kinds a test passes over, and takes the first, every supplied
  bridge removed, the change of I.37's and II.6's plants.

  The ruling applies as well to II.8, P13's other plant of the fifth kind, as the
  independent re-check of this change found. II.8's row supplies the same five bridges as
  III.36's, and its plant removed `Square.described`. II.8 does draw its square by I.46 and
  takes the square's parallelogram from `Square.described`, but P13 does not ask whether a
  bridge's premises are met where it is used, and `Square.eq_sq`, which the plant kept,
  still states the connection of a square that is a parallelogram with `sq`; so a careful
  reader could fairly answer "bridge stated" there too. II.8's plant passes over the fifth
  kind for the same reason and takes the first, every supplied bridge removed. No plant of
  P13 now has the fifth kind. A kind passed over by this
  ruling is named, with its reason, in the generator's own table, read with it; the kinds'
  tests are unchanged. When no kind applies to a base, the generator still writes nothing:
  the replacing base, and the lists it changes, are recorded in a dated entry and in the
  generator before anything is sent. The bar's four conditions, the questions, the lists
  and every other plant's kind are as the bar's entry and the rulings entry give them.

  This entry approves, in `scripts/audit/jev_questions.py`, the table of kinds that do not
  apply by this ruling, its guards, the words of the refusal when no kind applies, and
  III.36's and II.8's plants for P13.

  This entry approves, in `tests/test_jev_questions.py`, the cases for those changes.
