import Elements.Figure.Basics
import Elements.BookI.Prop31
import Elements.BookI.Prop37

/-!
# Book I, Proposition 39

Euclid's text, in Heath's translation: [`heath/I/39.md`](../../heath/I/39.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- Equal triangles which are on the same base and on the same side are also in the same parallels. -/
theorem Prop39 {A B C D : Point} (hABC : Triangle A B C) (hDBC : Triangle D B C)
    (heq : △ A B C = △ D B C) (hside : SameSideOf A D B C) (hAD : A ≠ D) :
    AreParallel A D B C := by
  -- Let ABC, DBC be equal triangles which are on the same base BC and on the same side of it;
  -- [I say that they are also in the same parallels.]
  -- And [For] let AD be joined;
  -- I say that AD is parallel to BC.
  -- For, if not, let AE be drawn through the point A parallel to the straight line BC, [I. 31]
  -- and let EC be joined.
  -- Therefore the triangle ABC is equal to the triangle EBC; for it is on the same base BC
  -- with it and in the same parallels. [I. 37]
  -- But ABC is equal to DBC; therefore DBC is also equal to EBC, [C.N. 1] the greater to the
  -- less: which is impossible.
  -- Therefore AE is not parallel to BC.
  -- Similarly we can prove that neither is any other straight line except AD; therefore AD is
  -- parallel to BC.
  -- Therefore etc.
  sorry

end Elements.BookI
