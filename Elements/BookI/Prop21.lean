import Elements.Figure.Basics
import Elements.BookI.Prop16
import Elements.BookI.Prop20

/-!
# Book I, Proposition 21

Euclid's text, in Heath's translation: [`heath/I/21.md`](../../heath/I/21.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- If on one of the sides of a triangle, from its extremities, there be constructed two straight
lines meeting within the triangle, the straight lines so constructed will be less than the
remaining two sides of the triangle, but will contain a greater angle. -/
theorem Prop21 {A B C D : Point} (hABC : Triangle A B C) (hD : InsideTriangle D A B C) :
    ‖B D‖ + ‖D C‖ < ‖B A‖ + ‖A C‖ ∧ ∠ B A C < ∠ B D C := by
  -- On BC, one of the sides of the triangle ABC, from its extremities B, C, let the two
  -- straight lines BD, DC be constructed meeting within the triangle;
  -- I say that BD, DC are less than the remaining two sides of the triangle BA, AC, but
  -- contain an angle BDC greater than the angle BAC.
  -- For let BD be drawn through to E.
  -- Then, since in any triangle two sides are greater than the remaining one, [I. 20]
  -- therefore, in the triangle ABE, the two sides AB, AE are greater than BE.
  -- Let EC be added to each;
  -- therefore BA, AC are greater than BE, EC.
  -- Again, since, in the triangle CED,
  -- the two sides CE, ED are greater than CD,
  -- let DB be added to each;
  -- therefore CE, EB are greater than CD, DB.
  -- But BA, AC were proved greater than BE, EC;
  -- therefore BA, AC are much greater than BD, DC.
  -- Again, since in any triangle the exterior angle is greater than the interior and opposite
  -- angle, [I. 16]
  -- therefore, in the triangle CDE,
  -- the exterior angle BDC is greater than the angle CED.
  -- For the same reason, moreover, in the triangle ABE also,
  -- the exterior angle CEB is greater than the angle BAC.
  -- But the angle BDC was proved greater than the angle CEB;
  -- therefore the angle BDC is much greater than the angle BAC.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
