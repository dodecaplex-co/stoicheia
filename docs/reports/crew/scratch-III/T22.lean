import Elements
open Elements Elements.Tacit

namespace Scratch

/-- The angles at `B` and `D` of a quadrilateral `ABCD` in a circle, its diameters
crossing at `X`. [I. 32, III. 21] -/
theorem T22.half {A B C D X : Point} {ABCD : Circle} (hABCD : ∃ O : Point, Centre O ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hD : OnCircle D ABCD)
    (hAXC : Between A X C) (hBXD : Between B X D) (hABC : Triangle A B C) (hBCD : Triangle B C D)
    (hACD : Triangle A C D) :
    ∠ A B C + ∠ A D C = ∟ + ∟ := by
  /- In the segments `BADC` and `ADCB`. [III. 21] -/
  have h₁ : ∠ B A C = ∠ B D C :=
    BookIII.Prop21 hABCD hA hB hC hD (SameSideOf.of_cross hBXD (between_symm hAXC) hBCD).symm
  have h₂ : ∠ A C B = ∠ A D B :=
    BookIII.Prop21 hABCD hC hA hB hD (SameSideOf.of_cross hAXC hBXD hABC)
  /- The whole angle `ADC` is the angles `ADB`, `BDC`. -/
  have hX : OnRay X D B := OnRay.of_between (between_symm hBXD)
  have hsplit : ∠ A D C = ∠ A D B + ∠ B D C := by
    rw [angle_add_of_between hACD hAXC, angle_onRay_right hX hACD.ne₁₃,
      angle_onRay_left hX hACD.ne₂₃]
  /- The angles of the triangle `ABC`. [I. 32] -/
  obtain ⟨E, hBCE⟩ := produce hABC.ne₂₃
  obtain ⟨-, h32⟩ := BookI.Prop32 hABC hBCE
  rw [hsplit, ← h₁, ← h₂, ← h32, angle_symm hABC.ne₁₃ hABC.ne₂₃,
    angle_symm hABC.ne₁₃.symm hABC.ne₁₂.symm]
  ac_rfl

theorem T22 {A B C D : Point} {ABCD : Circle} (hABCD : ∃ O : Point, Centre O ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hD : OnCircle D ABCD) (hAC : OppositeSidesOf A C B D) :
    ∠ A B C + ∠ A D C = ∟ + ∟ ∧ ∠ B A D + ∠ D C B = ∟ + ∟ := by
  have hBD : B ≠ D := hAC.1
  obtain ⟨L, hB_L, hD_L⟩ := Postulate1 B D hBD
  obtain ⟨X, hX_L, hAXC⟩ := (hAC.2 L hB_L hD_L).exists_between
  have hBXD : Between B X D :=
    between_of_inside_chord hX_L hB_L hD_L (inside_of_between (Or.inr hA) (Or.inr hC) hAXC) hB hD hBD
  have hBDA : Triangle B D A := hAC.triangle
  have hBDC : Triangle B D C := hAC.symm.triangle
  have hAB : A ≠ B := hBDA.ne₁₃.symm
  have hAD : A ≠ D := hBDA.ne₂₃.symm
  have hCB : C ≠ B := hBDC.ne₁₃.symm
  have hCD : C ≠ D := hBDC.ne₂₃.symm
  have hAC' : A ≠ C := ne_of_between_ends hAXC
  have tri : ∀ {P Q R : Point}, OnCircle P ABCD → OnCircle Q ABCD → OnCircle R ABCD → P ≠ Q →
      Q ≠ R → P ≠ R → Triangle P Q R := fun hP hQ hR h₁ h₂ h₃ => Triangle.of_onCircle hP hQ hR h₁ h₂ h₃
  refine ⟨T22.half hABCD hA hB hC hD hAXC hBXD (tri hA hB hC hAB hCB.symm hAC')
      (tri hB hC hD hCB.symm hCD hBD) (tri hA hC hD hAC' hCD hAD), ?_⟩
  /- Similarly for the quadrilateral `BCDA`. -/
  have := T22.half hABCD hB hC hD hA hBXD (between_symm hAXC) (tri hB hC hD hCB.symm hCD hBD)
    (tri hC hD hA hCD hAD.symm hAC'.symm) (tri hB hD hA hBD hAD.symm hAB.symm)
  rw [add_comm, angle_symm hCD.symm hCB.symm]
  exact this

end Scratch
