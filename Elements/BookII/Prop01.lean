import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop03
import Elements.BookI.Prop11
import Elements.BookI.Prop31
import Elements.BookI.Prop34

/-!
# Book II, Proposition 1

Euclid's text, in Heath's translation: [`heath/II/01.md`](../../heath/II/01.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If there be two straight lines, and one of them be cut into any number of segments whatever, the
rectangle contained by the two straight lines is equal to the rectangles contained by the uncut
straight line and each of the segments. -/
theorem Prop1 {A₁ A₂ B C D E : Point} (hA : A₁ ≠ A₂) (hBDE : Between B D E) (hDEC : Between D E C) :
    rect A₁ A₂ B C = rect A₁ A₂ B D + rect A₁ A₂ D E + rect A₁ A₂ E C := by
  -- Let A, BC be two straight lines, and let BC be cut at random at the points D, E;
  -- I say that the rectangle contained by A, BC is equal to the rectangle contained by A, BD,
  -- that contained by A, DE and that contained by A, EC.
  -- For let BF be drawn from B at right angles to BC; [I. 11]
  -- let BG be made equal to A, [I. 3]
  -- through G let GH be drawn parallel to BC, [I. 31]
  -- and through D, E, C let DK, EL, CH be drawn parallel to BG.
  -- Then BH is equal to BK, DL, EH.
  -- Now BH is the rectangle A, BC, for it is contained by GB, BC, and BG is equal to A;
  -- BK is the rectangle A, BD, for it is contained by GB, BD, and BG is equal to A;
  -- and DL is the rectangle A, DE, for DK, that is BG [I. 34], is equal to A.
  -- Similarly also EH is the rectangle A, EC.
  -- Therefore the rectangle A, BC is equal to the rectangle A, BD, the rectangle A, DE and the
  -- rectangle A, EC.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookII
