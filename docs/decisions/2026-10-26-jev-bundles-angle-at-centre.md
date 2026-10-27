- **The Jev audit's question generator learns the angle at the centre of any size (#36).**
  The theorems on the angle at the centre of any size moved into Elements, and the records
  of III.20 and III.21, read in full again, now give their representations item `pass`,
  where they gave `n/a` (#129). The generator on main
  ([its entry](2026-10-26-jev-questions-book-iii.md)) gave neither record a bridge, so it
  refused to write the calibration set or the audit. This entry records the repair. It
  sends nothing: the generator reads no key and makes no request.

  `scripts/audit/jev_questions.py` now knows the word `angleAtCentre` among Book III's
  definitions, and gives three records the declarations their representation verdicts rest
  on. III.20 gets the angle at the centre; that it is the angle BEC where Euclid's angles at
  the centre are (`angleAtCentre.within`); that it depends on neither the diameter nor the
  point naming the side (`angleAtCentre.diameter`, `angleAtCentre.congr`); and that our
  measure of a circumference is its angle at the centre (`Prop20.circumference`), all of
  which its representation note gives. III.21 gets the angle at the centre,
  `angleAtCentre.congr` and `angleAtCentre.within`, read from its route and passage notes,
  since its record has no representation note. III.26 gets the angle at the centre, which
  its representation note names. `tests/test_jev_questions.py` pins the three bundles and
  the guard that refuses a row leaving out what its record names.

  **One planted fault moves.** The same work rewrote III.20's commentary, and the sentence
  that P14's planted fault on III.20 changed is gone, so the generator refused that plant.
  The plant keeps its kind, the third (a claim about what the statement covers), on a
  sentence present both on main and at the calibration's commit: "Our III.20 reaches
  Heron's case all the same." becomes "Our III.20 keeps E on A's side of BC, as Euclid
  does.", which `Prop20`, naming no centre, does not. As the bar's entry asks, the
  calibration is run on the evidence of one commit of main, and the plant changes only the
  generated row.

  **The calibration's lists are unchanged.** III.20, III.21 and III.26 rank by the bar's
  hash rule as before; recomputed at the calibration's commit, every list equals the
  bar's, with P13's list for Book III as
  [the rulings](2026-10-26-jev-calibration-rulings.md) restate it. Of the calibration's
  rows, P13's control III.26 now carries the angle at the centre among its definitions, and
  P14's control III.28 and plant III.20 carry its definition among theirs.
