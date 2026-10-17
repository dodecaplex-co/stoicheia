import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Helpers
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
  have hABC : Triangle A B C :=
    Triangle.of_onCircle hA hB hC hAB (ne_of_between_ends hBEC) hAC
  -- I say that the angle BAC in the semicircle BAC is right,
  -- the angle ABC in the segment ABC greater than the semicircle is less than a right angle,
  -- and the angle ADC in the segment ADC less than the semicircle is greater than a right
  -- angle.
  -- Let AE be joined, and let BA be carried through to F.
  obtain ⟨F, hBAF⟩ := produce hAB.symm
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hABC.ne₂₃
  have hE_L : OnLine E L := on_line_of_between_ends hBEC hB_L hC_L
  have hA_L : ¬ OnLine A L := hABC.bca.off_line hB_L hC_L
  have hEBA : Triangle E B A := Triangle.of_line hE_L hB_L (ne_of_between hBEC).symm hA_L
  have hECA : Triangle E C A :=
    Triangle.of_line hE_L hC_L (ne_of_between (between_symm hBEC)).symm hA_L
  -- Then, since BE is equal to EA,
  have hBE : ‖E B‖ = ‖E A‖ := Definition15 hE hB hA
  -- the angle ABE is also equal to the angle BAE. [I. 5]
  have h₁ : ∠ A B E = ∠ B A E := by
    rw [angle_symm hAB hEBA.ne₁₂, BookI.Prop5.base hEBA hBE, angle_symm hEBA.ne₁₃ hAB.symm]
  -- Again, since CE is equal to EA,
  have hCE : ‖E C‖ = ‖E A‖ := Definition15 hE hC hA
  -- the angle ACE is also equal to the angle CAE. [I. 5]
  have h₂ : ∠ A C E = ∠ C A E := by
    rw [angle_symm hAC hECA.ne₁₂, BookI.Prop5.base hECA hCE, angle_symm hECA.ne₁₃ hAC.symm]
  -- Therefore the whole angle BAC is equal to the two angles ABC, ACB.
  have hwhole : ∠ B A C = ∠ A B C + ∠ A C B := by
    rw [angle_add_of_between hABC.bca hBEC, ← angle_onRay_right (OnRay.of_between hBEC) hAB,
      ← angle_onRay_right (OnRay.of_between (between_symm hBEC)) hAC, h₁, h₂,
      angle_symm hECA.ne₁₃ hAC.symm]
  -- But the angle FAC exterior to the triangle ABC is also equal to the two angles ABC,
  -- ACB; [I. 32]
  have hext : ∠ F A C = ∠ A B C + ∠ A C B := by
    obtain ⟨h32, -⟩ := BookI.Prop32 hABC.cba hBAF
    rw [angle_symm (ne_of_between (between_symm hBAF)) hAC.symm, h32, add_comm,
      angle_symm hABC.ne₂₃.symm hAB]
  -- therefore the angle BAC is also equal to the angle FAC;
  have heq : ∠ B A C = ∠ F A C := hwhole.trans hext.symm
  -- therefore each is right; [I. Def. 10]
  /- Definition I.10 says each is right, for they are equal adjacent angles on the
     straight line BF, and each is then `∟` (Post. 4, as in I.11). -/
  obtain ⟨M, hB_M, hA_M⟩ := Postulate1 B A hAB.symm
  have hF_M : OnLine F M := on_line_of_between hBAF hB_M hA_M
  have hC_M : ¬ OnLine C M := fun h => hABC ⟨M, hA_M, hB_M, h⟩
  have hFAC : Triangle F A C :=
    Triangle.of_line hF_M hA_M (ne_of_between (between_symm hBAF)) hC_M
  have hright : ∠ B A C = ∟ ∧ ∠ F A C = ∟ :=
    ⟨Postulate4 ⟨F, hBAF, hABC.bac, heq.trans (angle_symm hFAC.ne₁₂ hFAC.ne₂₃.symm)⟩,
     Postulate4 ⟨B, between_symm hBAF, hFAC,
       heq.symm.trans (angle_symm hAB.symm hAC.symm)⟩⟩
  -- therefore the angle BAC in the semicircle BAC is right.
  have hBAC : ∠ B A C = ∟ := hright.1
  -- Next, since in the triangle ABC the two angles ABC, BAC are less than two right
  -- angles, [I. 17]
  have h17 : ∠ C A B + ∠ A B C < ∟ + ∟ := (BookI.Prop17 hABC).2.2
  -- and the angle BAC is a right angle,
  rw [angle_symm hAC.symm hAB.symm, hBAC] at h17
  -- the angle ABC is less than a right angle;
  have hABC' : ∠ A B C < ∟ := Magnitude.lt_of_add_lt_add_left h17
  -- and it is the angle in the segment ABC greater than the semicircle.
  -- Next, since ABCD is a quadrilateral in a circle,
  -- and the opposite angles of quadrilaterals in circles are equal to two right
  -- angles, [III. 22]
  have hless : ∀ D : Point, OnCircle D ABCD → OppositeSidesOf B D A C → ∟ < ∠ A D C := by
    intro D hD hBD
    have h22 := (Prop22 ⟨E, hE⟩ hB hC hD hA hBD.swap).2
    rw [angle_symm hABC.ne₂₃.symm hAB] at h22
    -- while the angle ABC is less than a right angle,
    -- therefore the angle ADC which remains is greater than a right angle;
    rcases lt_trichotomy ∟ (∠ A D C) with h | h | h
    · exact h
    · rw [← h] at h22
      exact absurd (CommonNotion3 h22 rfl) (Magnitude.ne_of_lt hABC')
    · have := add_lt_add_right (∠ A D C) hABC'
      rw [h22] at this
      have h' := add_lt_add_right ∟ h
      rw [add_comm (∠ A D C) ∟] at h'
      exact absurd (lt_trans this h') (lt_irrefl _)
  -- and it is the angle in the segment ADC less than the semicircle.
  /- The statement covers every point X of the greater segment. With a point D of the
     less segment, III.22 makes the angle at X less than a right angle. -/
  have hgreater : ∀ X : Point, OnCircle X ABCD → SameSideOf X B A C → ∠ A X C < ∟ := by
    intro X hX hXB
    obtain ⟨D, hD, hDB⟩ := exists_onCircle_oppositeSidesOf hA hC hABC.acb
    have hXD : OppositeSidesOf X D A C := hXB.trans_opposite hDB.symm
    have h22 := (Prop22 ⟨E, hE⟩ hX hA hD hC hXD).2
    have hDAC : Triangle A D C := hXD.symm.triangle.acb
    rw [angle_symm hDAC.ne₂₃.symm hDAC.ne₁₂] at h22
    have hobtuse : ∟ < ∠ A D C := hless D hD hDB.symm
    rcases lt_trichotomy (∠ A X C) ∟ with h | h | h
    · exact h
    · rw [h, add_comm] at h22
      exact absurd (CommonNotion3 h22 rfl).symm (Magnitude.ne_of_lt hobtuse)
    · /- Were the angle at X greater than a right angle too, the two angles together
         would be greater than two right angles. -/
      have h₁ : ∟ + ∟ < ∠ A X C + ∟ := add_lt_add_right ∟ h
      have h₂ : ∠ A X C + ∟ < ∠ A X C + ∠ A D C := by
        rw [add_comm (∠ A X C) ∟, add_comm (∠ A X C) (∠ A D C)]
        exact add_lt_add_right (∠ A X C) hobtuse
      exact absurd (h22 ▸ lt_trans h₁ h₂) (lt_irrefl _)
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
  exact ⟨hBAC, hgreater, hless⟩
  -- Q. E. D.

end Elements.BookIII
