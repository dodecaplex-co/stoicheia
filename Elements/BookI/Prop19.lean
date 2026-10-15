import Elements.Figure.Basics
import Elements.BookI.Prop05
import Elements.BookI.Prop18

/-!
# Book I, Proposition 19

Euclid's text, in Heath's translation: [`heath/I/19.md`](../../heath/I/19.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- In any triangle the greater angle is subtended by the greater side. -/
theorem Prop19 {A B C : Point} (hABC : Triangle A B C) (h : ∠ B C A < ∠ A B C) :
    ‖A B‖ < ‖A C‖ := by
  -- Let ABC be a triangle having the angle ABC greater than the angle BCA;
  -- I say that the side AC is also greater than the side AB.
  -- For, if not, AC is either equal to AB or less.
  -- Now AC is not equal to AB;
  -- for then the angle ABC would also have been equal to the angle ACB; [I. 5]
  -- but it is not;
  -- therefore AC is not equal to AB.
  -- Neither is AC less than AB,
  -- for then the angle ABC would also have been less than the angle ACB; [I. 18]
  -- but it is not;
  -- therefore AC is not less than AB.
  -- And it was proved that it is not equal either.
  -- Therefore AC is greater than AB.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
