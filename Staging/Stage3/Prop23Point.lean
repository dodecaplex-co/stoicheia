import Elements.Figure.Basics
import Elements.BookI.Prop16
import Elements.BookI.Prop21
import Elements.BookIII.Prop21

/-!
# Stage 3, staged: III.23, point by point

Statements before proofs (brief 0006, stage 3). A shared step of Book III, destined for a
file after III.21 (proposed: `Elements/BookIII/Circumferences.lean`, or a file of its own
beside it). III.24 uses it in place of Euclid's appeal to III.10.

III.23 says that on one straight line, on one side, there cannot be two similar and unequal
segments. Point by point: on one side of a chord, a point is on the circle exactly when the
chord subtends at it the angle in the segment, and within the circle exactly when it subtends
a greater angle.
-/

namespace Elements.BookIII

open Tacit

/-- **On the circle, by the angle.** Let A, B, E be points of a circle with a centre, and P a
point on E's side of AB. Then P is on the circle exactly when the angle APB is equal to the
angle AEB, and P is within the circle exactly when the angle APB is greater than the angle
AEB.

To be proved: one way is the angles in the same segment [III. 21]; the other draws AP on to
meet the circle at Q (or meets it between A and P) and compares the angles at P and Q, the
exterior angle of a triangle being greater [I. 16], or the angle within the triangle being
greater [I. 21].

Accompanies III.23 (its content, point by point); III.24 cites it. -/
theorem Prop23.point {A B E P : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hA : OnCircle A α) (hB : OnCircle B α) (hE : OnCircle E α) (hPE : SameSideOf P E A B) :
    (OnCircle P α ↔ ∠ A P B = ∠ A E B) ∧ (InsideCircle P α ↔ ∠ A E B < ∠ A P B) := by
  sorry

end Elements.BookIII
