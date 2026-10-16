import Elements.Figure.Basics
import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.Prop36

/-!
# Book I, Proposition 38

Euclid's text, in Heath's translation: [`heath/I/38.md`](../../heath/I/38.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

"In the same parallels BF, AD": two parallel straight lines, one through the
vertices `A` and `D`, the other through the bases `BC` and `EF`. The two vertices
may be one point, as when I.42 cites this for the triangles `ABE` and `AEC`. So
under "let AD be produced in both directions to G, H", "AD" is the parallel
through the vertices itself, and `G` and `H` are taken on it.
-/

namespace Elements.BookI

open Tacit

/-- Triangles which are on equal bases and in the same parallels are equal to one another. -/
theorem Prop38 {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
    (hbase : ‖B C‖ = ‖E F‖)
    (hpar : ∃ L M : Line, Parallel L M ∧ OnLine A L ∧ OnLine D L ∧
      OnLine B M ∧ OnLine C M ∧ OnLine E M ∧ OnLine F M) :
    △ A B C = △ D E F := by
  -- Let ABC, DEF be triangles on equal bases BC, EF and in the same parallels BF, AD;
  -- I say that the triangle ABC is equal to the triangle DEF.
  -- For let AD be produced in both directions to G, H; through B let BG be drawn parallel to
  -- CA, [I. 31] and through F let FH be drawn parallel to DE.
  -- Then each of the figures GBCA, DEFH is a parallelogram; and GBCA is equal to DEFH; for
  -- they are on equal bases BC, EF and in the same parallels BF, GH. [I. 36]
  -- Moreover the triangle ABC is half of the parallelogram GBCA; for the diameter AB bisects
  -- it. [I. 34]
  -- And the triangle FED is half of the parallelogram DEFH; for the diameter DF bisects
  -- it. [I. 34]
  -- [But the halves of equal things are equal to one another.]
  -- Therefore the triangle ABC is equal to the triangle DEF.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
