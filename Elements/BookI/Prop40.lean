import Elements.Figure.Basics
import Elements.BookI.Prop31
import Elements.BookI.Prop38

/-!
# Book I, Proposition 40

Euclid's text, in Heath's translation: [`heath/I/40.md`](../../heath/I/40.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- Equal triangles which are on equal bases and on the same side are also in the same parallels. -/
theorem Prop40 {A B C D E : Point} (hABC : Triangle A B C) (hCDE : Triangle C D E)
    (hBCE : Between B C E) (hbase : ‖B C‖ = ‖C E‖) (heq : △ A B C = △ C D E)
    (hside : SameSideOf A D B E) (hAD : A ≠ D) :
    AreParallel A D B E := by
  -- Let ABC, CDE be equal triangles on equal bases BC, CE and on the same side.
  -- I say that they are also in the same parallels.
  -- For let AD be joined;
  -- I say that AD is parallel to BE.
  -- For, if not, let AF be drawn through A parallel to BE [I. 31], and let FE be joined.
  -- Therefore the triangle ABC is equal to the triangle FCE; for they are on equal bases BC,
  -- CE and in the same parallels BE, AF. [I. 38]
  -- But the triangle ABC is equal to the triangle DCE; therefore the triangle DCE is also
  -- equal to the triangle FCE, [C.N. 1] the greater to the less: which is impossible.
  -- Therefore AF is not parallel to BE.
  -- Similarly we can prove that neither is any other straight line except AD; therefore AD is
  -- parallel to BE.
  -- Therefore etc.
  -- Q. E. D.]
  sorry

end Elements.BookI
