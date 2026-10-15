import Elements.Figure.Basics
import Elements.BookI.Prop16

/-!
# Book I, Proposition 27

Euclid's text, in Heath's translation: [`heath/I/27.md`](../../heath/I/27.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- If a straight line falling on two straight lines make the alternate angles equal to one another,
the straight lines will be parallel to one another. -/
theorem Prop27 {A B C D E F : Point} (hAEB : Between A E B) (hCFD : Between C F D)
    (hAD : OppositeSidesOf A D E F) (h : ∠ A E F = ∠ E F D) :
    AreParallel A B C D := by
  -- For let the straight line EF falling on the two straight lines AB, CD make the alternate
  -- angles AEF, EFD equal to one another;
  -- I say that AB is parallel to CD.
  -- For, if not, AB, CD when produced will meet either in the direction of B, D or towards A,
  -- C.
  -- Let them be produced and meet, in the direction of B, D, at G.
  -- Then, in the triangle GEF,
  -- the exterior angle AEF is equal to the interior and opposite angle EFG:
  -- which is impossible. [I. 16]
  -- Therefore AB, CD when produced will not meet in the direction of B, D.
  -- Similarly it can be proved that neither will they meet towards A, C.
  -- But straight lines which do not meet in either direction are parallel; [Def. 23]
  -- therefore AB is parallel to CD.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
