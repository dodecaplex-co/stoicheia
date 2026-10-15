import Elements.Figure.Basics
import Elements.BookI.Prop03
import Elements.BookI.Prop04
import Elements.BookI.Prop10
import Elements.BookI.Prop15

/-!
# Book I, Proposition 16

Euclid's text, in Heath's translation: [`heath/I/16.md`](../../heath/I/16.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- In any triangle, if one of the sides be produced, the exterior angle is greater than either of
the interior and opposite angles. -/
theorem Prop16 {A B C D : Point} (hABC : Triangle A B C) (hBCD : Between B C D) :
    ∠ C B A < ∠ A C D ∧ ∠ B A C < ∠ A C D := by
  -- Let ABC be a triangle, and let one side of it BC be produced to D;
  -- I say that the exterior angle ACD is greater than either of the interior and opposite
  -- angles CBA, BAC.
  -- Let AC be bisected at E [I. 10], and let BE be joined and produced in a straight line to
  -- F;
  -- let EF be made equal to BE [I. 3], let FC be joined [Post. 1], and let AC be drawn through
  -- to G [Post. 2].
  -- Then, since AE is equal to EC, and BE to EF,
  -- the two sides AE, EB are equal to the two sides CE, EF respectively;
  -- and the angle AEB is equal to the angle FEC,
  -- for they are vertical angles. [I. 15]
  -- Therefore the base AB is equal to the base FC,
  -- and the triangle ABE is equal to the triangle CFE,
  -- and the remaining angles are equal to the remaining angles respectively, namely those
  -- which the equal sides subtend; [I. 4]
  -- therefore the angle BAE is equal to the angle ECF.
  -- But the angle ECD is greater than the angle ECF; [C.N. 5]
  -- therefore the angle ACD is greater than the angle BAE.
  -- Similarly also, if BC be bisected, the angle BCG, that is, the angle ACD [I. 15], can be
  -- proved greater than the angle ABC as well.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
