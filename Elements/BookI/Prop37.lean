import Elements.Figure.Basics
import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.Prop35

/-!
# Book I, Proposition 37

Euclid's text, in Heath's translation: [`heath/I/37.md`](../../heath/I/37.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

"In the same parallels AD, BC": two parallel straight lines, one through the
vertices `A` and `D`, the other through the base `BC`, as in I.38. The two vertices
may be one point, and then the two triangles are one. So under "let AD be produced
in both directions to E, F", "AD" is the parallel through the vertices itself, and
`E` and `F` are taken on it.
-/

namespace Elements.BookI

open Tacit

/-- Triangles which are on the same base and in the same parallels are equal to one another. -/
theorem Prop37 {A B C D : Point} (hABC : Triangle A B C) (hDBC : Triangle D B C)
    (hpar : ∃ L M : Line, Parallel L M ∧ OnLine A L ∧ OnLine D L ∧ OnLine B M ∧ OnLine C M) :
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
