import Elements.Figure.Basics
import Elements.BookI.Prop03
import Elements.BookI.Prop08

/-!
# Book I, Proposition 9

Euclid's text, in Heath's translation: [`heath/I/09.md`](../../heath/I/09.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- To bisect a given rectilineal angle. -/
theorem Prop9 {A B C : Point} (hBAC : Triangle B A C) :
    ∃ F : Point, ∠ B A F = ∠ F A C ∧ ∠ B A F + ∠ F A C = ∠ B A C := by
  -- Let the angle BAC be the given rectilineal angle.
  -- It is then required to bisect it.
  -- Let a point D be taken at random on AB;
  -- let AE be cut off from AC equal to AD; [I. 3]
  -- let DE be joined, and on DE let the equilateral triangle DEF be constructed;
  -- let AF be joined.
  -- I say that the angle BAC has been bisected by the straight line AF.
  -- For, since AD is equal to AE,
  -- and AF is common,
  -- the two sides DA, AF are equal to the two sides EA, AF respectively.
  -- And the base DF is equal to the base EF;
  -- therefore the angle DAF is equal to the angle EAF. [I. 8]
  -- Therefore the given rectilineal angle BAC has been bisected by the straight line AF.
  -- Q. E. F.
  sorry

end Elements.BookI
