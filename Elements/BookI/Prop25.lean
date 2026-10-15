import Elements.Figure.Basics
import Elements.BookI.Prop04
import Elements.BookI.Prop24

/-!
# Book I, Proposition 25

Euclid's text, in Heath's translation: [`heath/I/25.md`](../../heath/I/25.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- If two triangles have the two sides equal to two sides respectively, but have the base greater
than the base, they will also have the one of the angles contained by the equal straight lines
greater than the other. -/
theorem Prop25 {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
    (hAB : ‖A B‖ = ‖D E‖) (hAC : ‖A C‖ = ‖D F‖) (h : ‖E F‖ < ‖B C‖) :
    ∠ E D F < ∠ B A C := by
  -- Let ABC, DEF be two triangles having the two sides AB, AC equal to the two sides DE, DF
  -- respectively, namely AB to DE, and AC to DF; and let the base BC be greater than the base
  -- EF;
  -- I say that the angle BAC is also greater than the angle EDF.
  -- For, if not, it is either equal to it or less.
  -- Now the angle BAC is not equal to the angle EDF;
  -- for then the base BC would also have been equal to the base EF, [I. 4]
  -- but it is not;
  -- therefore the angle BAC is not equal to the angle EDF.
  -- Neither again is the angle BAC less than the angle EDF;
  -- for then the base BC would also have been less than the base EF, [I. 24]
  -- but it is not;
  -- therefore the angle BAC is not less than the angle EDF.
  -- But it was proved that it is not equal either;
  -- therefore the angle BAC is greater than the angle EDF.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
