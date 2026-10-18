import Elements.Figure.Basics
import Elements.BookIII.Prop29
import Staging.Stage3.Definitions
import Staging.Stage3.Placement
import Staging.Stage3.Prop24
import Staging.Stage3.Prop28

/-!
# Stage 3, staged: what equal measures mean

Statements before proofs (brief 0006, stage 3). Destined for `Elements/BookIII/Arcs.lean`,
placed after III.29 so that the argument cannot go round in a circle: these bridge theorems
justify the measure of a circumference (`circumference`, an angle carrying no radius) and the
congruence of segments, and III.26–III.29 must not rest on them. Outside the placement files,
this file and III.24 are the only places that may cite `placement` or any lemma of the
`Placement` namespace.
-/

namespace Elements.BookIII

open Tacit

/-- **In equal circles, equal measure is equal chord and same kind.** For two drawn arcs in equal
circles, the measures are equal exactly when the straight lines joining their ends are equal and
the arcs are of the same kind (both less than semicircles, both semicircles, or both greater).

To be proved by III.28 (equal chords, kind decided by the centre's side), III.29 (equal
circumferences, equal chords), and the comparison of each kind with a semicircle
(`Circumference.lt_semicircle`, `.semicircle`, `.gt_semicircle`).

A bridge theorem for the measure that III.26–III.29 compare. -/
theorem Arc.measure_eq_iff {a b : Arc} (ha : a.Drawn) (hb : b.Drawn)
    (hcircles : EqualCircles a.circle b.circle) :
    a.measure = b.measure ↔ ‖a.B a.C‖ = ‖b.B b.C‖ ∧ Arc.SameKind a b := by
  sorry

/-- **Congruent is equal circles and equal measure.** Two drawn arcs are congruent exactly when
their circles are equal and their measures are equal.

To be proved: one way, the measures are equal by `Prop24.equalMeasure`, and the circles by
`Prop24.equalCircles`, the congruence keeping the chord and, at a point of the arc and its
image, the angle in the segment [I. 8]; neither is proved again here. The other way, by
`Arc.measure_eq_iff` the chords are equal and the kinds the same, so the angles in the segments
are equal, and III.24 (restated) makes the segments congruent.

A bridge theorem for the congruence that III.24, III.26 and III.28 conclude. -/
theorem Arc.congruent_iff {a b : Arc} (ha : a.Drawn) (hb : b.Drawn) :
    Arc.Congruent a b ↔ EqualCircles a.circle b.circle ∧ a.measure = b.measure := by
  sorry

end Elements.BookIII
