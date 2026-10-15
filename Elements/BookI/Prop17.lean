import Elements.Figure.Basics
import Elements.BookI.Prop13
import Elements.BookI.Prop16

/-!
# Book I, Proposition 17

Euclid's text, in Heath's translation: [`heath/I/17.md`](../../heath/I/17.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- In any triangle two angles taken together in any manner are less than two right angles. -/
theorem Prop17 {A B C : Point} (hABC : Triangle A B C) :
    ∠ A B C + ∠ B C A < ∟ + ∟ ∧ ∠ B A C + ∠ A C B < ∟ + ∟ ∧ ∠ C A B + ∠ A B C < ∟ + ∟ := by
  -- Let ABC be a triangle;
  -- I say that two angles of the triangle ABC taken together in any manner are less than two
  -- right angles.
  -- For let BC be produced to D. [Post. 2]
  -- Then, since the angle ACD is an exterior angle of the triangle ABC,
  -- it is greater than the interior and opposite angle ABC. [I. 16]
  -- Let the angle ACB be added to each;
  -- therefore the angles ACD, ACB are greater than the angles ABC, BCA.
  -- But the angles ACD, ACB are equal to two right angles. [I. 13]
  -- Therefore the angles ABC, BCA are less than two right angles.
  -- Similarly we can prove that the angles BAC, ACB are also less than two right angles, and
  -- so are the angles CAB, ABC as well.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
