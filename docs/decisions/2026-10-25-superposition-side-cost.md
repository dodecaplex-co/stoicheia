- **The side laid down: its cost made a theorem, and named beside System E (foundations,
  [#150](https://github.com/jackChallis/stoicheia/issues/150), question 5).** The
  coordinator's orders of 25 October 2026 finish two of the optional items of question 5
  of #150, "Pin the side's cost" and "The side in the System E comparison". The kept side
  itself, the side AC laid down as a straight line through D and C′, was approved as
  prototyped under question 5 on 20 October 2026, as
  [brief 0009](../briefs/0009-superposition.md) records; this entry adds no decision on
  it, only a theorem that states its cost and a sentence that names it. No axiom, no
  statement, no definition and no `--` line changes, and no entry of
  `Certificate/axioms.lock`.

  Until now the side's cost was checked by reading the model's proof of superposition:
  D is not C′, since C′ is on H's side of L and D is on L, and the model's Postulate 1
  then gives the straight line through them. The new theorem `Rule.of_placement_of_join`,
  in `Elements/Foundations/Superposition/Soundness.lean` beside `Rule.of_placement`,
  states that cost for any interpretation of the primitive words. From a placement that
  keeps the triangle's sides and angles but draws no side, from Same side 3's form (a
  point on one side of a straight line is off it) and from Postulate 1's (a straight line
  through any two distinct points), the restricted rule `Rule I` follows, through
  `Rule.of_placement`. Lean reports that it depends on `propext` and `Quot.sound` alone,
  as `Rule.of_placement` does.

  The model's proof of `superposition`, in `model/Model/Euclidean/Superposition.lean`,
  now applies the new theorem to `superposition_placement`, to the model's Same side 3,
  `not_on_line_of_same_side`, whose module the file now imports, and to the model's
  Postulate 1, in place of its own proof that D is not C′ and its own call of Postulate 1;
  its module docstring says so. Its axioms are what they were, `propext`,
  `Classical.choice` and `Quot.sound`, and the model's pin of them is unchanged.

  System E's superposition, as Avigad, Dean and Mumma state it (§3.7, p. 725), lists the
  facts of the triangle laid down in two sets, Π₁ for SAS and Π₂ for SSS, and neither
  names a line through d and c′. The paper's text does not settle whether a derivation
  inside the branch may draw one, and nothing here claims that it may or may not. The
  module docstring of `Elements/Foundations/Tacit/Superposition.lean` now says that our
  placement also keeps the side AC, which neither set lists, and what that side costs, by
  the new theorem; no declaration there changes, and no other sentence's claim.

  No protected path changes. A pin of the new theorem in the audit, and brief 0009's
  passages on the side's cost and on System E, are left to trains of their own.
