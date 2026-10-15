import Elements.Figure.Basics
import Elements.BookI.Prop11
import Elements.BookI.Prop29
import Elements.BookI.Prop31
import Elements.BookI.Prop34

/-!
# Book I, Proposition 46

Euclid's text, in Heath's translation: [`heath/I/46.md`](../../heath/I/46.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- On a given straight line to describe a square. -/
theorem Prop46 {A B P : Point} (hAB : A ≠ B) (hP : ¬ Collinear A B P) :
    ∃ D E : Point, Square A D E B ∧ SameSideOf D P A B ∧ SameSideOf E P A B := by
  -- Let AB be the given straight line; thus it is required to describe a square on the
  -- straight line AB.
  -- Let AC be drawn at right angles to the straight line AB from the point A on it [I. 11],
  -- and let AD be made equal to AB; through the point D let DE be drawn parallel to AB, and
  -- through the point B let BE be drawn parallel to AD. [I. 31]
  -- Therefore ADEB is a parallelogram; therefore AB is equal to DE, and AD to BE. [I. 34]
  -- But AB is equal to AD; therefore the four straight lines BA, AD, DE, EB are equal to one
  -- another; therefore the parallelogram ADEB is equilateral.
  -- I say next that it is also right-angled.
  -- For, since the straight line AD falls upon the parallels AB, DE, the angles BAD, ADE are
  -- equal to two right angles. [I. 29]
  -- But the angle BAD is right; therefore the angle ADE is also right.
  -- And in parallelogrammic areas the opposite sides and angles are equal to one
  -- another; [I. 34] therefore each of the opposite angles ABE, BED is also right.
  -- Therefore ADEB is right-angled.
  -- And it was also proved equilateral.
  -- Therefore it is a square; and it is described on the straight line AB.
  -- Q. E. F.
  sorry

end Elements.BookI
