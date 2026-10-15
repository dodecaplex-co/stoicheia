import Elements.Figure.Basics
import Elements.BookI.Prop13
import Elements.BookI.Prop15
import Elements.BookI.Prop27

/-!
# Book I, Proposition 28

Euclid's text, in Heath's translation: [`heath/I/28.md`](../../heath/I/28.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- If a straight line falling on two straight lines make the exterior angle equal to the interior
and opposite angle on the same side, or the interior angles on the same side equal to two right
angles, the straight lines will be parallel to one another. -/
theorem Prop28 {A B C D E F G H : Point} (hAGB : Between A G B) (hCHD : Between C H D)
    (hEGH : Between E G H) (hGHF : Between G H F) (hBD : SameSideOf B D E F)
    (h : ∠ E G B = ∠ G H D ∨ ∠ B G H + ∠ G H D = ∟ + ∟) :
    AreParallel A B C D := by
  -- For let the straight line EF falling on the two straight lines AB, CD make the exterior
  -- angle EGB equal to the interior and opposite angle GHD, or the interior angles on the same
  -- side, namely BGH, GHD, equal to two right angles;
  -- I say that AB is parallel to CD.
  -- For, since the angle EGB is equal to the angle GHD,
  -- while the angle EGB is equal to the angle AGH, [I. 15]
  -- the angle AGH is also equal to the angle GHD;
  -- and they are alternate;
  -- therefore AB is parallel to CD. [I. 27]
  -- Again, since the angles BGH, GHD are equal to two right angles, and the angles AGH, BGH
  -- are also equal to two right angles, [I. 13]
  -- the angles AGH, BGH are equal to the angles BGH, GHD.
  -- Let the angle BGH be subtracted from each;
  -- therefore the remaining angle AGH is equal to the remaining angle GHD;
  -- and they are alternate;
  -- therefore AB is parallel to CD. [I. 27]
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
