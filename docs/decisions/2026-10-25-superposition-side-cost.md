- **The side laid down: its cost made a theorem, and named beside System E (foundations,
  [#150](https://github.com/jackChallis/stoicheia/issues/150), question 5).** Under the
  coordinator's orders of 25 October 2026, this change takes up two of the optional items
  of question 5 of #150, "Pin the side's cost" and "The side in the System E comparison",
  and does the part of each that touches neither the audit nor the brief; neither item is
  finished here, and the last paragraph names what is left of each. The kept side is AC,
  laid down as a straight line through D and C′. This entry records no decision on it,
  and, on the side itself, the change adds only a theorem that states its cost, two
  sentences that name the side and that cost, and the model's descriptions of its proof
  by that theorem, named below. No axiom, no statement, no definition and no `--` line
  changes, and no entry of `Certificate/axioms.lock`.

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
  The model's pages name the new theorem where they described the side by Postulate 1 and
  `Rule.of_placement`: `model/README.md`, the docstring of
  `model/Model/Laws/superposition.lean`, and `tests/model/MODEL.md`, in the superposition
  row of its table of why each rule holds and in its account of the formal model.

  This entry approves the change to `tests/model/MODEL.md` that, in that row and in that
  account, names the new theorem and describes the proof of `superposition` by it, by
  Same side 3 and by Postulate 1.

  System E's superposition, as Avigad, Dean and Mumma state it (§3.7, p. 725), lists the
  facts of the triangle laid down in two sets, Π₁ for SAS and Π₂ for SSS, and neither
  names a line through d and c′. The paper's text does not settle whether a derivation
  inside the branch may draw one, and nothing here claims that it may or may not. The
  module docstring of `Elements/Foundations/Tacit/Superposition.lean` now says that our
  placement also keeps the side AC, which neither set lists, and a bound on what that side costs, by
  the new theorem; no declaration there changes, and no other sentence's claim.

  No other protected path changes. What is left of the two items goes to trains of their own:
  the pin of `Rule.of_placement_of_join` in `Audit/Superposition.lean`, a protected path,
  at `[propext, Quot.sound]`; and, in brief 0009, a citation of the theorem where the brief
  still says that the side's cost is checked by reading the model's proof (its round-4
  correction, its account of what the placement keeps, its account of the model obligation
  and its answer to question 5), and
  the kept side, with its cost and a p. 725 citation, in its comparison "Against System E".
