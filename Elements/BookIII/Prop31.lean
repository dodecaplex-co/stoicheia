import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop05
import Elements.BookI.Prop17
import Elements.BookI.Prop32
import Elements.BookIII.Prop22

/-!
# Book III, Proposition 31

Euclid's text, in Heath's translation: [`heath/III/31.md`](../../heath/III/31.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- In a circle the angle in the semicircle is right, that in a greater segment less than a right
angle, and that in a less segment greater than a right angle; and further the angle of the
greater segment is greater than a right angle, and the angle of the less segment less than a
right angle. -/
theorem Prop31 {A B C E : Point} {ABCD : Circle} (hE : Centre E ABCD) (hA : OnCircle A ABCD)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hBEC : Between B E C) (hAB : A ≠ B)
    (hAC : A ≠ C) :
    ∠ B A C = ∟ ∧
      (∀ X : Point, OnCircle X ABCD → SameSideOf X B A C → ∠ A X C < ∟) ∧
      ∀ D : Point, OnCircle D ABCD → OppositeSidesOf B D A C → ∟ < ∠ A D C := by
  -- Let ABCD be a circle, let BC be its diameter, and E its centre, and let BA, AC, AD, DC be
  -- joined;
  -- I say that the angle BAC in the semicircle BAC is right,
  -- the angle ABC in the segment ABC greater than the semicircle is less than a right angle,
  -- and the angle ADC in the segment ADC less than the semicircle is greater than a right
  -- angle.
  -- Let AE be joined, and let BA be carried through to F.
  -- Then, since BE is equal to EA,
  -- the angle ABE is also equal to the angle BAE. [I. 5]
  -- Again, since CE is equal to EA,
  -- the angle ACE is also equal to the angle CAE. [I. 5]
  -- Therefore the whole angle BAC is equal to the two angles ABC, ACB.
  -- But the angle FAC exterior to the triangle ABC is also equal to the two angles ABC,
  -- ACB; [I. 32]
  -- therefore the angle BAC is also equal to the angle FAC;
  -- therefore each is right; [I. Def. 10]
  -- therefore the angle BAC in the semicircle BAC is right.
  -- Next, since in the triangle ABC the two angles ABC, BAC are less than two right
  -- angles, [I. 17]
  -- and the angle BAC is a right angle,
  -- the angle ABC is less than a right angle;
  -- and it is the angle in the segment ABC greater than the semicircle.
  -- Next, since ABCD is a quadrilateral in a circle,
  -- and the opposite angles of quadrilaterals in circles are equal to two right
  -- angles, [III. 22]
  -- while the angle ABC is less than a right angle,
  -- therefore the angle ADC which remains is greater than a right angle;
  -- and it is the angle in the segment ADC less than the semicircle.
  -- I say further that the angle of the greater segment, namely that contained by the
  -- circumference ABC and the straight line AC, is greater than a right angle;
  -- and the angle of the less segment, namely that contained by the circumference ADC and the
  -- straight line AC, is less than a right angle.
  -- This is at once manifest.
  -- For, since the angle contained by the straight lines BA, AC is right,
  -- the angle contained by the circumference ABC and the straight line AC is greater than a
  -- right angle.
  -- Again, since the angle contained by the straight lines AC, AF is right,
  -- the angle contained by the straight line CA and the circumference ADC is less than a right
  -- angle.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
