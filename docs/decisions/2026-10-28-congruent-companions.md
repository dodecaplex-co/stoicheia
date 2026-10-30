- **III.27 and III.29 from congruent circumferences, two companions (Book III,
  [#474](https://github.com/jackChallis/stoicheia/issues/474)).** The owner's decision of
  26 October 2026, about 07:54 Pacific, which the coordinator has recorded on #474, reads in
  full: "yes on both, let's wait for the WIP trial." Those words are the owner's whole part
  here. The coordinator's record on #474 takes them as the approval of both statements
  below, as they were drafted for #474 that day (WORKFLOW, section 2); everything else in
  this entry is the coordinator's, and the entry claims no further approval of the owner's.

  This entry approves the statement of `Prop27.of_congruent`, the companion "III.27
  of_congruent", in `Elements/BookIII/Prop27.lean`: III.27's statement, with Q across BC
  from A and R across EF from D, which give the triangles BAC, EDF that `Prop27` assumes,
  and the circumferences BC, EF on the sides of Q and R congruent (`Arc.Congruent`) in
  place of the equal measures of the circumferences on which the angles at A and D stand;
  its conclusion is III.27's, unchanged.
  This entry approves the statement of `Prop29.of_congruent`, the companion "III.29
  of_congruent", in `Elements/BookIII/Prop29.lean`: III.29's statement, with the
  circumferences BGC, EHF congruent in place of equal in measure.

  ```lean
  theorem Prop27.of_congruent {A B C D E F G H Q R : Point} {ABC DEF : Circle}
      (hcircles : EqualCircles ABC DEF) (hG : Centre G ABC) (hH : Centre H DEF)
      (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hC : OnCircle C ABC)
      (hD : OnCircle D DEF) (hE : OnCircle E DEF) (hF : OnCircle F DEF)
      (hAQ : OppositeSidesOf A Q B C) (hDR : OppositeSidesOf D R E F)
      (hcong : Arc.Congruent ⟨ABC, B, C, Q⟩ ⟨DEF, E, F, R⟩) :
      ∠ B A C = ∠ E D F ∧
        (SameSideOf G A B C → SameSideOf H D E F → ∠ B G C = ∠ E H F)

  theorem Prop29.of_congruent {B C E F G H : Point} {ABC DEF : Circle}
      (hcircles : EqualCircles ABC DEF)
      (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hE : OnCircle E DEF) (hF : OnCircle F DEF)
      (hG : ¬ Collinear B C G) (hH : ¬ Collinear E F H)
      (hcong : Arc.Congruent ⟨ABC, B, C, G⟩ ⟨DEF, E, F, H⟩) :
      ‖B C‖ = ‖E F‖
  ```

  What the companions add. III.26 and III.28 conclude their equal circumferences congruent
  as well as equal in measure, reading Euclid's "equal" through Common Notion 4, but III.27
  and III.29 assume equal measures alone. The earlier companion `Prop24.equalMeasure`
  already turns congruence into equal measures. The companions take the congruence as their hypothesis, so that III.27 and III.29
  run from what III.26 and III.28 conclude. Each is proved in its proposition's file, after
  the proposition: III.24's companion `Prop24.equalMeasure` makes the congruent
  circumferences equal in measure, and the proposition then gives the conclusion by its own
  route. Neither cites anything after its proposition, nor `Arc.measure_eq_iff`,
  `Arc.congruent_iff` or anything else in that file, and neither adds a rule or an axiom.

  What they do not add. "In equal circles" stays redundant. For III.27 it was so already,
  since our measure of a circumference carries no radius, and its record keeps the tag
  `redundant-hypothesis`. In both companions the congruent circumferences already lie in
  equal circles (`Prop24.image`, `Prop24.equalCircles`), and in III.29's the congruence
  already gives the equal straight lines (`Prop24.image`); the hypothesis is kept as
  Euclid's setting and is used along each proposition's route. III.29's record gains the
  tag `redundant-hypothesis`, and its note says that the redundancy is the companion's
  alone, for `Prop29` itself needs the equal circles, which give I.4 its equal radii.

  This entry approves the change to `Elements/Companions.lean`, the companions list, which
  the integrator owns and [the risk table](../../scripts/risk.py) classes with the
  foundations: it gains the entries "III.27 of_congruent" and "III.29 of_congruent", after
  "III.25 of_circle", and the imports `Elements.BookIII.Prop27` and
  `Elements.BookIII.Prop29` that their names need. `Elements/BookIII/Prop29.lean` now
  imports `Elements.BookIII.Prop24`, as every proposition cited is imported. No other
  statement changes, nor any porism, definition, axiom, lock or `--` line. The records of
  III.27 and III.29 name their companions, and wait for an independent reader's stamp.
