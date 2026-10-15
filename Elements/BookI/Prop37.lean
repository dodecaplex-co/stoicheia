import Elements.Figure.Basics
import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.Prop35

/-!
# Book I, Proposition 37

Euclid's text, in Heath's translation: [`heath/I/37.md`](../../heath/I/37.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- Triangles which are on the same base and in the same parallels are equal to one another. -/
theorem Prop37 {A B C D : Point} (hABC : Triangle A B C) (hDBC : Triangle D B C)
    (hpar : AreParallel A D B C) :
    △ A B C = △ D B C := by
  -- Let ABC, DBC be triangles on the same base BC and in the same parallels AD, BC;
  -- I say that the triangle ABC is equal to the triangle DBC.
  -- Let AD be produced in both directions to E, F; through B let BE be drawn parallel to
  -- CA, [I. 31] and through C let CF be drawn parallel to BD. [I. 31]
  -- Then each of the figures EBCA, DBCF is a parallelogram; and they are equal, for they are
  -- on the same base BC and in the same parallels BC, EF. [I. 35]
  -- Moreover the triangle ABC is half of the parallelogram EBCA; for the diameter AB bisects
  -- it. [I. 34]
  -- And the triangle DBC is half of the parallelogram DBCF; for the diameter DC bisects
  -- it. [I. 34]
  -- [But the halves of equal things are equal to one another.]
  -- Therefore the triangle ABC is equal to the triangle DBC.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
