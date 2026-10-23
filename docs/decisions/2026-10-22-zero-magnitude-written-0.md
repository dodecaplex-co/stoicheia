- **The zero magnitude is written `0`, and FORMALIZATION says so
  ([#336](https://github.com/jackChallis/stoicheia/issues/336)).** Section 2 of
  [FORMALIZATION](../FORMALIZATION.md) said that no numbers, coordinates or real numbers
  appear in a statement or a proof. In Books I to III the zero magnitude is written `0`,
  in helpers' statements, as `0 < ∠ A C B` in `Prop7.figure`, and in proofs, as
  `‖A B‖ ≠ 0` in `Prop1.figure`'s; the foundations write it in some laws and definitions
  too (`len_self`, `Magnitude.sum`). Read literally, the sentence was false there.

  The coordinator's call, on #336, is to disclose the zero rather than remove it. It is
  not Euclid's, but it is how the foundations say whether a magnitude is nothing, and
  [Magnitudes.lean](../../Elements/Foundations/Magnitudes.lean) already says that there
  are no numbers there and that the zero is only a convenience. So the bullet now says, in
  a sentence of its own, that the zero magnitude is written `0`, in some laws,
  definitions, helpers and proofs, and stands for no magnitude (no length, no angle, no
  area), never for a number Euclid uses.

  The sentence was checked against every numeral in the Lean of Books I to III, outside
  comments and strings, by two scans that agree: 55 numerals. Of them, 36 are the zero
  magnitude, of length, angle, area or any kind, and none is in a proposition's own
  statement. The other 19 are the counts by which I.4's and I.8's superposition numbers
  its symbols; [#312](https://github.com/jackChallis/stoicheia/issues/312) is to take them
  out. The scans were run again after the figures' promotion landed (#342), which rewrote
  the sentence as "No coordinates or real numbers appear in a statement or a proof, and
  no number measures a length, an angle or an area" and added a paragraph on counts of a
  figure's corners: the scans' totals are the same.

  The sentence also names its scope now
  ([#338](https://github.com/jackChallis/stoicheia/issues/338)): it is a proposition's
  statement and the geometric steps of its proof in which no coordinates or real numbers
  appear and no number measures a magnitude. Beneath those steps numbers serve the
  machinery, and the bullet names them: the superposition rule numbers its symbols
  (`Symbols`), so I.4 and I.8 number the points and straight lines of their figures
  beside their proofs (the 19 counts above), as `valuation_encodes` writes a literal over
  two numbered symbols (`Fin 2`, in `Elements/Foundations/Superposition/Restriction.lean`);
  and Book Zero's proofs pass a count to a tactic (`congr 1`, in
  `Elements/Figure/OnCircles.lean`). Read literally, the sentence as it stood before #342,
  "No numbers, coordinates or real numbers appear in a statement or a proof", was false
  there too; and #342's form of it, read without a scope, was false of the model in
  [`model/`](../../model/README.md), which reads the words in Mathlib's plane,
  `EuclideanSpace ℝ (Fin 2)`, with real coordinates. This entry claims no approval of the
  owner.
