import Elements.Figure.Basics
import Elements.BookI.Prop05

/-!
# Book I, Proposition 7

Euclid's text, in Heath's translation: [`heath/I/07.md`](../../heath/I/07.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- Given two straight lines constructed on a straight line (from its extremities) and meeting in a
point, there cannot be constructed on the same straight line (from its extremities), and on the
same side of it, two other straight lines meeting in another point and equal to the former two
respectively, namely each to that which has the same extremity with it. -/
theorem Prop7 {A B C D : Point} (hCD : SameSideOf C D A B) (hCA : ‖C A‖ = ‖D A‖)
    (hCB : ‖C B‖ = ‖D B‖) :
    C = D := by
  -- For, if possible, given two straight lines AC, CB constructed on the straight line AB and
  -- meeting at the point C, let two other straight lines AD, DB be constructed on the same
  -- straight line AB, on the same side of it, meeting in another point D and equal to the
  -- former two respectively, namely each to that which has the same extremity with it, so that
  -- CA is equal to DA which has the same extremity A with it, and CB to DB which has the same
  -- extremity B with it; and let CD be joined.
  -- Then, since AC is equal to AD,
  -- the angle ACD is also equal to the angle ADC; [I. 5]
  -- therefore the angle ADC is greater than the angle DCB;
  -- therefore the angle CDB is much greater than the angle DCB.
  -- Again, since CB is equal to DB,
  -- the angle CDB is also equal to the angle DCB.
  -- But it was also proved much greater than it:
  -- which is impossible.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
