import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop32
import Elements.BookIII.Prop21

/-!
# Book III, Proposition 22

Euclid's text, in Heath's translation: [`heath/III/22.md`](../../heath/III/22.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- The opposite angles of quadrilaterals in circles are equal to two right angles. -/
theorem Prop22 {A B C D : Point} {ABCD : Circle} (hABCD : ∃ O : Point, Centre O ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hD : OnCircle D ABCD) (hAC : OppositeSidesOf A C B D) :
    ∠ A B C + ∠ A D C = ∟ + ∟ ∧ ∠ B A D + ∠ D C B = ∟ + ∟ := by
  -- Let ABCD be a circle, and let ABCD be a quadrilateral in it;
  -- I say that the opposite angles are equal to two right angles.
  -- Let AC, BD be joined.
  -- Then, since in any triangle the three angles are equal to two right angles, [I. 32]
  -- the three angles CAB, ABC, BCA of the triangle ABC are equal to two right angles.
  -- But the angle CAB is equal to the angle BDC, for they are in the same segment
  -- BADC; [III. 21]
  -- and the angle ACB is equal to the angle ADB, for they are in the same segment ADCB;
  -- therefore the whole angle ADC is equal to the angles BAC, ACB.
  -- Let the angle ABC be added to each;
  -- therefore the angles ABC, BAC, ACB are equal to the angles ABC, ADC.
  -- But the angles ABC, BAC, ACB are equal to two right angles;
  -- therefore the angles ABC, ADC are also equal to two right angles.
  -- Similarly we can prove that the angles BAD, DCB are also equal to two right angles.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
