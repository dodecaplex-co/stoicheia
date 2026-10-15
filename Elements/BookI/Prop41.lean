import Elements.Figure.Basics
import Elements.BookI.Prop34
import Elements.BookI.Prop37

/-!
# Book I, Proposition 41

Euclid's text, in Heath's translation: [`heath/I/41.md`](../../heath/I/41.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- If a parallelogram have the same base with a triangle and be in the same parallels, the
parallelogram is double of the triangle. -/
theorem Prop41 {A B C D E : Point} (hABCD : Parallelogram A B C D) (hE : Collinear A D E) :
    quadArea A B C D = △ B E C + △ B E C := by
  -- For let the parallelogram ABCD have the same base BC with the triangle EBC, and let it be
  -- in the same parallels BC, AE;
  -- I say that the parallelogram ABCD is double of the triangle BEC.
  -- For let AC be joined.
  -- Then the triangle ABC is equal to the triangle EBC; for it is on the same base BC with it
  -- and in the same parallels BC, AE. [I. 37]
  -- But the parallelogram ABCD is double of the triangle ABC; for the diameter AC bisects
  -- it; [I. 34] so that the parallelogram ABCD is also double of the triangle EBC.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
