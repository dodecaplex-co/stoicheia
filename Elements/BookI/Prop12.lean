import Elements.Figure.Basics
import Elements.BookI.Prop08
import Elements.BookI.Prop10

/-!
# Book I, Proposition 12

Euclid's text, in Heath's translation: [`heath/I/12.md`](../../heath/I/12.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- To a given infinite straight line, from a given point which is not on it, to draw a
perpendicular straight line. -/
theorem Prop12 {A B C : Point} (hAB : A ≠ B) (hC : ¬ Collinear A B C) :
    ∃ H : Point, Collinear A B H ∧ ∀ P : Point, Collinear A B P → P ≠ H → ∠ C H P = ∟ := by
  -- Let AB be the given infinite straight line, and C the given point which is not on it;
  -- thus it is required to draw to the given infinite straight line AB, from the given point C
  -- which is not on it, a perpendicular straight line.
  -- For let a point D be taken at random on the other side of the straight line AB, and with
  -- centre C and distance CD let the circle EFG be described; [Post. 3]
  -- let the straight line EG be bisected at H, [I. 10]
  -- and let the straight lines CG, CH, CE be joined. [Post. 1]
  -- I say that CH has been drawn perpendicular to the given infinite straight line AB from the
  -- given point C which is not on it.
  -- For, since GH is equal to HE,
  -- and HC is common,
  -- the two sides GH, HC are equal to the two sides EH, HC respectively;
  -- and the base CG is equal to the base CE;
  -- therefore the angle CHG is equal to the angle EHC. [I. 8]
  -- And they are adjacent angles.
  -- But, when a straight line set up on a straight line makes the adjacent angles equal to one
  -- another, each of the equal angles is right, and the straight line standing on the other is
  -- called a perpendicular to that on which it stands. [Def. 10]
  -- Therefore CH has been drawn perpendicular to the given infinite straight line AB from the
  -- given point C which is not on it.
  -- Q. E. F.
  sorry

end Elements.BookI
