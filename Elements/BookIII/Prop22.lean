import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop32
import Elements.BookIII.Prop02
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
theorem Prop22 {A B C D : Point} {ABCD : Circle}
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hD : OnCircle D ABCD) (hAC : OppositeSidesOf A C B D) :
    ∠ A B C + ∠ A D C = ∟ + ∟ ∧ ∠ B A D + ∠ D C B = ∟ + ∟ := by
  -- Let ABCD be a circle, and let ABCD be a quadrilateral in it;
  have hBDA : Triangle B D A := hAC.triangle
  have hBDC : Triangle B D C := hAC.symm.triangle
  -- I say that the opposite angles are equal to two right angles.
  -- Let AC, BD be joined.
  /- BD separates A from C, so AC crosses the straight line BD at a point X. X is within
     the circle (III.2), so it lies between B and D (System E, Circle 1), as in III.20:
     AC and BD cut one another. -/
  have hBD : B ≠ D := hAC.1
  obtain ⟨L, hB_L, hD_L⟩ := Postulate1 B D hBD
  obtain ⟨X, hX_L, hAXC⟩ := (hAC.2 L hB_L hD_L).exists_between
  have hBXD : Between B X D := between_of_inside_chord hX_L hB_L hD_L
    (Prop2 hA hC X hAXC) hB hD hBD
  have hAC' : A ≠ C := ne_of_between_ends hAXC
  /- Euclid proves it for the angles at B and D and says "similarly" for those at A and C,
     so we write his argument once, for any quadrilateral in the circle whose straight lines
     AC, BD cut one another, and use it twice. -/
  have half : ∀ {A B C D X : Point}, OnCircle A ABCD → OnCircle B ABCD → OnCircle C ABCD →
      OnCircle D ABCD → Between A X C → Between B X D → Triangle A B C → Triangle B C D →
      Triangle A C D → ∠ A B C + ∠ A D C = ∟ + ∟ := by
    intro A B C D X hA hB hC hD hAXC hBXD hABC hBCD hACD
    -- Then, since in any triangle the three angles are equal to two right angles, [I. 32]
    -- the three angles CAB, ABC, BCA of the triangle ABC are equal to two right angles.
    obtain ⟨E, hBCE⟩ := produce hABC.ne₂₃
    have h32 : ∠ A B C + ∠ B C A + ∠ C A B = ∟ + ∟ := (BookI.Prop32 hABC hBCE).2
    -- But the angle CAB is equal to the angle BDC, for they are in the same segment
    -- BADC; [III. 21]
    have h₁ : ∠ C A B = ∠ B D C := by
      rw [angle_symm hABC.ne₁₃.symm hABC.ne₁₂.symm]
      exact Prop21 hA hB hC hD (SameSideOf.of_cross hBXD (between_symm hAXC) hBCD).symm
    -- and the angle ACB is equal to the angle ADB, for they are in the same segment ADCB;
    have h₂ : ∠ A C B = ∠ A D B := Prop21 hC hA hB hD (SameSideOf.of_cross hAXC hBXD hABC)
    -- therefore the whole angle ADC is equal to the angles BAC, ACB.
    have hX : OnRay X D B := OnRay.of_between (between_symm hBXD)
    have h₃ : ∠ A D C = ∠ B A C + ∠ A C B := by
      rw [angle_add_of_between hACD hAXC, angle_onRay_right hX hACD.ne₁₃,
        angle_onRay_left hX hACD.ne₂₃, ← h₁, ← h₂, angle_symm hABC.ne₁₃.symm hABC.ne₁₂.symm]
      ac_rfl
    -- Let the angle ABC be added to each;
    -- therefore the angles ABC, BAC, ACB are equal to the angles ABC, ADC.
    have h₄ : ∠ A B C + ∠ B A C + ∠ A C B = ∠ A B C + ∠ A D C := by
      rw [h₃]; ac_rfl
    -- But the angles ABC, BAC, ACB are equal to two right angles;
    have h₅ : ∠ A B C + ∠ B A C + ∠ A C B = ∟ + ∟ := by
      rw [← h32, angle_symm hABC.ne₁₃.symm hABC.ne₁₂.symm,
        angle_symm hABC.ne₂₃ hABC.ne₁₃]
      ac_rfl
    -- therefore the angles ABC, ADC are also equal to two right angles.
    exact h₄ ▸ h₅
  /- The argument serves first in Euclid's own figure, for the angles ABC, ADC. Three
     points of the circle make a triangle (`Prop2.triangle`). -/
  have hB_D : ∠ A B C + ∠ A D C = ∟ + ∟ := half hA hB hC hD hAXC hBXD
    (Prop2.triangle hA hB hC hBDA.ne₁₃.symm hBDC.ne₁₃ hAC')
    (Prop2.triangle hB hC hD hBDC.ne₁₃ hBDC.ne₂₃.symm hBD)
    (Prop2.triangle hA hC hD hAC' hBDC.ne₂₃.symm hBDA.ne₂₃.symm)
  -- Similarly we can prove that the angles BAD, DCB are also equal to two right angles.
  /- The same argument serves in the quadrilateral BCDA, whose straight lines BD, CA cut
     one another at the same point, for its angles BCD, BAD. -/
  have hA_C : ∠ B A D + ∠ D C B = ∟ + ∟ := by
    rw [add_comm, angle_symm hBDC.ne₂₃ hBDC.ne₁₃]
    exact half hB hC hD hA hBXD (between_symm hAXC)
      (Prop2.triangle hB hC hD hBDC.ne₁₃ hBDC.ne₂₃.symm hBD)
      (Prop2.triangle hC hD hA hBDC.ne₂₃.symm hBDA.ne₂₃ hAC'.symm)
      (Prop2.triangle hB hD hA hBD hBDA.ne₂₃ hBDA.ne₁₃)
  -- Therefore etc.
  exact ⟨hB_D, hA_C⟩
  -- Q. E. D.

end Elements.BookIII
