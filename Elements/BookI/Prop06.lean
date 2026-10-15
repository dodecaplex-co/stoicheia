import Elements.Figure.Basics

/-!
# Book I, Proposition 6

Euclid's text, in Heath's translation: [`heath/I/06.md`](../../heath/I/06.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- If in a triangle two angles be equal to one another, the sides which subtend the equal angles
will also be equal to one another. -/
theorem Prop6 {A B C : Point} (hABC : Triangle A B C) (h : ∠ A B C = ∠ A C B) :
    ‖A B‖ = ‖A C‖ := by
  -- Let ABC be a triangle having the angle ABC equal to the angle ACB;
  -- I say that the side AB is also equal to the side AC.
  -- For, if AB is unequal to AC, one of them is greater.
  -- Let AB be greater; and from AB the greater let DB be cut off equal to AC the less;
  -- let DC be joined.
  -- Then, since DB is equal to AC,
  -- and BC is common,
  -- the two sides DB, BC are equal to the two sides AC, CB respectively;
  -- and the angle DBC is equal to the angle ACB;
  -- therefore the base DC is equal to the base AB,
  -- and the triangle DBC will be equal to the triangle ACB,
  -- the less to the greater:
  -- which is absurd.
  -- Therefore AB is not unequal to AC;
  -- it is therefore equal to it.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
