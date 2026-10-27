- **The Jev audit's question generator learns the angle at the centre of any size (#36).**
  The theorems on the angle at the centre of any size moved into Elements, and the records
  of III.20 and III.21, read in full again, now give their representations item `pass`,
  where they gave `n/a` (#129). The generator on main
  ([its entry](2026-10-26-jev-questions-book-iii.md)) gave neither record a bridge, so it
  refused to write the calibration set or the audit. This entry records the repair. It
  sends nothing: the generator reads no key and makes no request.

  `scripts/audit/jev_questions.py` now knows the word `angleAtCentre` among Book III's
  definitions, and gives three records the declarations their representation verdicts rest
  on. III.20 and III.21 get the angle at the centre; that it is the angle BEC where
  Euclid's angles at the centre are (`angleAtCentre.within`); that it is the angles BEF and
  FEC of any diameter AEF with A across BC from the named circumference and F on its side,
  wherever the centre lies,
  on BC or beyond it too, as for the semicircle and the less segment
  (`angleAtCentre.diameter`); and that it reads only the side of BC that the point naming
  the circumference lies on (`angleAtCentre.congr`). III.20's representation note names
  the first and says the other two in words; III.21's record has no representation note,
  its route reads Euclid's argument in a segment of any size, the semicircle and the less
  segment among them, and its passages name `angleAtCentre.congr`. III.20 and III.26 also
  get that our measure of a circumference is its angle at the centre
  (`Prop20.circumference`): III.20's note names it, and for III.26 it connects the reading
  of equal circumferences as equal in measure with the angles at the centres that its note
  names, and, with `Circumference.centre`, already in its bundle, makes the angle at the
  centre the angle BGC where G lies across BC from K. The guard that refuses a row leaving
  out what its record names reads, besides the names a representation note gives in
  backticks, what these three records say in words: III.20's row must supply
  `angleAtCentre.diameter` and `angleAtCentre.congr`; III.21's the angle at the centre,
  `angleAtCentre.within`, `angleAtCentre.congr` and `angleAtCentre.diameter`; III.26's
  `Prop20.circumference`. `tests/test_jev_questions.py` pins the three bundles, and shows
  that a row leaving out any one of these is refused.

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
  rows, P13's control III.26 now carries the angle at the centre among its definitions and
  `Prop20.circumference` among its bridges, and P14's control III.28 and plant III.20 carry
  the angle's definition among theirs.
