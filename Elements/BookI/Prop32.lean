import Elements.Figure.Basics
import Elements.BookI.Prop13
import Elements.BookI.Prop29
import Elements.BookI.Prop31

/-!
# Book I, Proposition 32

Euclid's text, in Heath's translation: [`heath/I/32.md`](../../heath/I/32.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- In any triangle, if one of the sides be produced, the exterior angle is equal to the two
interior and opposite angles, and the three interior angles of the triangle are equal to two
right angles. -/
theorem Prop32 {A B C D : Point} (hABC : Triangle A B C) (hBCD : Between B C D) :
    ∠ A C D = ∠ C A B + ∠ A B C ∧ ∠ A B C + ∠ B C A + ∠ C A B = ∟ + ∟ := by
  -- Let ABC be a triangle, and let one side of it BC be produced to D;
  -- I say that the exterior angle ACD is equal to the two interior and opposite angles CAB,
  -- ABC, and the three interior angles of the triangle ABC, BCA, CAB are equal to two right
  -- angles.
  -- For let CE be drawn through the point C parallel to the straight line AB. [I. 31]
  -- Then, since AB is parallel to CE,
  -- and AC has fallen upon them,
  -- the alternate angles BAC, ACE are equal to one another. [I. 29]
  -- Again, since AB is parallel to CE,
  -- and the straight line BD has fallen upon them,
  -- the exterior angle ECD is equal to the interior and opposite angle ABC. [I. 29]
  -- But the angle ACE was also proved equal to the angle BAC;
  -- therefore the whole angle ACD is equal to the two interior and opposite angles BAC, ABC.
  -- Let the angle ACB be added to each;
  -- therefore the angles ACD, ACB are equal to the three angles ABC, BCA, CAB.
  -- But the angles ACD, ACB are equal to two right angles; [I. 13]
  -- therefore the angles ABC, BCA, CAB are also equal to two right angles.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
