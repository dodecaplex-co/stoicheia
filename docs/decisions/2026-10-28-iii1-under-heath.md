- **III.1's construction set out under Euclid's sentences (Book III,
  [#547](https://github.com/jackChallis/stoicheia/issues/547)).** The coordinator's, under
  the owner's decision of 26 October 2026 that the coordinator has recorded on #547: "Yes -
  follow Euclid when possible." This entry claims no further approval of the owner's.

  `Prop1` now takes each step of Euclid's construction under his own sentence: I.10 bisects
  AB at D, `Prop1.perpendicular_chord` draws DC through to E, and I.10 bisects CE at F. Its
  reductio supposes that the constructed F is not the centre, as Euclid's does. The rule
  `Tacit.exists_centre` still supplies two steps and no point the construction returns: the
  supposed centre G, which Definitions I.15 and I.16 presuppose, and a centre for the proof
  that D is within the circle (`Prop1.midpoint_inside`, by III.2's argument in
  `Prop1.within`). No statement, porism, companion, definition, axiom or `--` line changes,
  and `Prop1.construction` keeps its type and its axioms.

  This entry approves the change to `Audit/Centre.lean`, a protected path, in its module
  comment alone: the comment names the steps that `Prop1` now calls in place of
  `Prop1.construction`. The pin, its fixture and its axiom list are unchanged.
