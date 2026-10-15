import Elements.Figure.Basics
import Elements.BookI.Prop13
import Elements.BookI.Prop15

/-!
# Book I, Proposition 29

Euclid's text, in Heath's translation: [`heath/I/29.md`](../../heath/I/29.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- A straight line falling on parallel straight lines makes the alternate angles equal to one
another, the exterior angle equal to the interior and opposite angle, and the interior angles on
the same side equal to two right angles. -/
theorem Prop29 {A B C D E F G H : Point} (hpar : AreParallel A B C D) (hAGB : Between A G B)
    (hCHD : Between C H D) (hEGH : Between E G H) (hGHF : Between G H F)
    (hBD : SameSideOf B D E F) :
    ∠ A G H = ∠ G H D ∧ ∠ E G B = ∠ G H D ∧ ∠ B G H + ∠ G H D = ∟ + ∟ := by
  -- For let the straight line EF fall on the parallel straight lines AB, CD;
  -- I say that it makes the alternate angles AGH, GHD equal, the exterior angle EGB equal to
  -- the interior and opposite angle GHD, and the interior angles on the same side, namely BGH,
  -- GHD, equal to two right angles.
  -- For, if the angle AGH is unequal to the angle GHD, one of them is greater.
  -- Let the angle AGH be greater.
  -- Let the angle BGH be added to each;
  -- therefore the angles AGH, BGH are greater than the angles BGH, GHD.
  -- But the angles AGH, BGH are equal to two right angles; [I. 13]
  -- therefore the angles BGH, GHD are less than two right angles.
  -- But straight lines produced indefinitely from angles less than two right angles
  -- meet; [Post. 5]
  -- therefore AB, CD, if produced indefinitely, will meet;
  -- but they do not meet, because they are by hypothesis parallel.
  -- Therefore the angle AGH is not unequal to the angle GHD,
  -- and is therefore equal to it.
  -- Again, the angle AGH is equal to the angle EGB; [I. 15]
  -- therefore the angle EGB is also equal to the angle GHD. [C.N. 1]
  -- Let the angle BGH be added to each;
  -- therefore the angles EGB, BGH are equal to the angles BGH, GHD. [C.N. 2]
  -- But the angles EGB, BGH are equal to two right angles; [I. 13]
  -- therefore the angles BGH, GHD are also equal to two right angles.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
