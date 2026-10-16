import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Prop20

/-!
# Book III, Proposition 21

Euclid's text, in Heath's translation: [`heath/III/21.md`](../../heath/III/21.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- In a circle the angles in the same segment are equal to one another. -/
theorem Prop21 {A B D E : Point} {ABCD : Circle} (hABCD : ∃ F : Point, Centre F ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hD : OnCircle D ABCD)
    (hE : OnCircle E ABCD) (hAE : SameSideOf A E B D) :
    ∠ B A D = ∠ B E D := by
  -- Let ABCD be a circle, and let the angles BAD, BED be angles in the same segment BAED;
  -- I say that the angles BAD, BED are equal to one another.
  -- For let the centre of the circle ABCD be taken, and let it be F; let BF, FD be joined.
  -- Now, since the angle BFD is at the centre,
  -- and the angle BAD at the circumference,
  -- and they have the same circumference BCD as base,
  -- therefore the angle BFD is double of the angle BAD. [III. 20]
  -- For the same reason
  -- the angle BFD is also double of the angle BED;
  -- therefore the angle BAD is equal to the angle BED.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
