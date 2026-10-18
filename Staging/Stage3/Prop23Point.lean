import Elements.Figure.Basics
import Elements.BookI.Prop21
import Elements.BookIII.Prop21

/-!
# Stage 3, staged: III.23, point by point

Statements before proofs (brief 0006, stage 3). A companion of III.23, destined for
`Elements/BookIII/Prop23.lean`, after III.23, and certified as "III.23 point" (brief 0006).

III.23 says that on one straight line, on one side, there cannot be two similar and unequal
segments. Point by point: on one side of a chord, a point is on the circle exactly when the
chord subtends at it the angle in the segment, and within the circle exactly when it subtends
a greater angle.

III.24 cites it for the cases Euclid leaves to III.23: a segment that would fall within the
other, or outside it, is disposed of by a tacit reference to III.23, as Heath notes in his
commentary on III.24 (vol. 2, p. 54). As III.23's companion, the dependency shows in III.24's
certificate.
-/

namespace Elements.BookIII

open Tacit

/-- **On the circle, by the angle.** Let A, B, E be points of a circle with a centre, and P a
point on E's side of AB. Then P is on the circle exactly when the angle APB is equal to the
angle AEB, and P is within the circle exactly when the angle APB is greater than the angle
AEB.

To be proved through a point M between A and B, which is within the circle. On the circle,
the angles in the same segment are equal [III. 21]. Outside it, the finite straight line PM
meets the arc at a point Q, which is within the triangle ABP, so the angle AQB is greater
than the angle APB [I. 21]. Within it, MP produced beyond P meets the circle at a point Q,
and P is within the triangle ABQ, so the angle APB is greater than the angle AQB [I. 21]. In
both, Q is on E's side of AB, and the angle AQB is equal to the angle AEB [III. 21]. (A plan
that draws AP on fails when AP touches the circle at A.)

A companion of III.23 ("III.23 point"): its content, point by point. III.24 cites it. -/
theorem Prop23.point {A B E P : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hA : OnCircle A α) (hB : OnCircle B α) (hE : OnCircle E α) (hPE : SameSideOf P E A B) :
    (OnCircle P α ↔ ∠ A P B = ∠ A E B) ∧ (InsideCircle P α ↔ ∠ A E B < ∠ A P B) := by
  sorry

end Elements.BookIII
