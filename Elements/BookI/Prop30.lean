import Elements.Figure.Basics
import Elements.BookI.Prop27
import Elements.BookI.Prop29

/-!
# Book I, Proposition 30

Euclid's text, in Heath's translation: [`heath/I/30.md`](../../heath/I/30.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid's last step, "and they are alternate. Therefore AB is parallel to CD", is
I.27, though he gives no bracket there; so this file imports it.
-/

namespace Elements.BookI

open Tacit

/-- Straight lines parallel to the same straight line are also parallel to one another. -/
theorem Prop30 {A B C D E F : Point} (h₁ : AreParallel A B E F) (h₂ : AreParallel C D E F)
    (hC : ¬ Collinear A B C) :
    AreParallel A B C D := by
  -- Let each of the straight lines AB, CD be parallel to EF;
  -- I say that AB is also parallel to CD.
  -- For let the straight line GK fall upon them.
  -- Then, since the straight line GK has fallen on the parallel straight lines AB, EF,
  -- the angle AGK is equal to the angle GHF. [I. 29]
  -- Again, since the straight line GK has fallen on the parallel straight lines EF, CD,
  -- the angle GHF is equal to the angle GKD. [I. 29]
  -- But the angle AGK was also proved equal to the angle GHF;
  -- therefore the angle AGK is also equal to the angle GKD; [C.N. 1]
  -- and they are alternate.
  -- Therefore AB is parallel to CD.
  -- Q. E. D.
  sorry

end Elements.BookI
