import Elements.Figure.Basics
import Elements.BookI.Prop01
import Elements.BookI.Prop03
import Elements.BookI.Prop08

/-!
# Book I, Proposition 11

Euclid's text, in Heath's translation: [`heath/I/11.md`](../../heath/I/11.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- To draw a straight line at right angles to a given straight line from a given point on it. -/
theorem Prop11 {A B C Q : Point} (hAB : A ≠ B) (hC : Collinear A B C) (hQ : ¬ Collinear A B Q) :
    ∃ F : Point, SameSideOf F Q A B ∧ ∀ P : Point, Collinear A B P → P ≠ C → ∠ P C F = ∟ := by
  -- Let AB be the given straight line, and C the given point on it.
  -- Thus it is required to draw from the point C a straight line at right angles to the
  -- straight line AB.
  -- Let a point D be taken at random on AC;
  -- let CE be made equal to CD; [I. 3]
  -- on DE let the equilateral triangle FDE be constructed, [I. 1]
  -- and let FC be joined;
  -- I say that the straight line FC has been drawn at right angles to the given straight line
  -- AB from C the given point on it.
  -- For, since DC is equal to CE,
  -- and CF is common,
  -- the two sides DC, CF are equal to the two sides EC, CF respectively;
  -- and the base DF is equal to the base FE;
  -- therefore the angle DCF is equal to the angle ECF; [I. 8]
  -- and they are adjacent angles.
  -- But, when a straight line set up on a straight line makes the adjacent angles equal to one
  -- another, each of the equal angles is right; [Def. 10]
  -- therefore each of the angles DCF, FCE is right.
  -- Therefore the straight line CF has been drawn at right angles to the given straight line
  -- AB from the given point C on it.
  -- Q. E. F.
  sorry

end Elements.BookI
