import Elements.BookI.Prop08
import Elements.BookI.Prop11
import Elements.BookI.Prop46
import Elements.BookI.Prop47

namespace Elements.BookI
open Tacit

/-- Throwaway: I.48 as restated, along Euclid's route. -/
theorem T48 {A B C P Q R S T U : Point} (hABC : Triangle A B C)
    (hBC : Square B P Q C) (hPQ : SameSideOf P Q B C)
    (hBA : Square A B R S) (hRS : SameSideOf R S A B)
    (hAC : Square A C T U) (hTU : SameSideOf T U A C)
    (h : quadArea B P Q C = quadArea A B R S + quadArea A C T U) :
    ∠ B A C = ∟ := by
  obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hABC.ne₁₃
  -- For let AD be drawn from the point A at right angles to the straight line AC,
  /- on the other side of `AC` from `B`, as in Euclid's figure. -/
  obtain ⟨X, hXB, -⟩ := exists_oppositeSidesOf hABC.acb []
  obtain ⟨D₀, hD₀X, hright⟩ := Prop11 hABC.ne₁₃ ⟨AC, hA_AC, hC_AC, hA_AC⟩ hXB.triangle
  -- let AD be made equal to BA,
  obtain ⟨D, hD, hAD⟩ := OnRay.exists_len_eq hABC.ne₁₂ hD₀X.triangle.ne₁₃
  have hDB : OppositeSidesOf D B A C := (SameSideOf.of_onRay hD hD₀X).trans_opposite hXB
  have hADC : Triangle A D C := hDB.triangle.acb
  have hDAC : ∠ D A C = ∟ := by
    rw [angle_symm hADC.ne₁₂.symm hADC.ne₁₃.symm, angle_onRay_right hD hABC.ne₁₃.symm]
    exact hright C ⟨AC, hA_AC, hC_AC, hC_AC⟩ hABC.ne₁₃.symm
  -- The squares on DC, DA and AC, described outwards [I. 46].
  obtain ⟨Y₁, hY₁A, -⟩ := exists_oppositeSidesOf hADC.bca []
  obtain ⟨d, e, hsq₁, hd, he⟩ := Prop46 hADC.ne₂₃ hY₁A.triangle
  obtain ⟨Y₂, hY₂C, -⟩ := exists_oppositeSidesOf hADC.bac []
  obtain ⟨f, g, hsq₂, hf, hg⟩ := Prop46 hADC.ne₁₂.symm hY₂C.triangle
  obtain ⟨Y₃, hY₃D, -⟩ := exists_oppositeSidesOf hADC.cab []
  obtain ⟨k, l, hsq₃, hk, hl⟩ := Prop46 hADC.ne₁₃.symm hY₃D.triangle
  -- I.47 on the triangle DAC
  have hDdeC_side : SameSideOf d e D C := hd.trans he.symm
  have h47 : quadArea D d e C = quadArea A D f g + quadArea A C k l :=
    Prop47 hADC hDAC hsq₁ (hd.trans_opposite hY₁A) (he.trans_opposite hY₁A)
      hsq₂.rotate.rotate.rotate (hf.trans_opposite hY₂C).swap (hg.trans_opposite hY₂C).swap
      hsq₃.rotate.rotate.rotate (hk.trans_opposite hY₃D).swap (hl.trans_opposite hY₃D).swap
  -- Since DA is equal to AB, the square on DA is also equal to the square on AB.
  have hfg : SameSideOf f g A D := (hf.trans hg.symm).swap
  have hsqDA : quadArea A D f g = quadArea A B R S :=
    Prop46.square_eq hsq₂.rotate.rotate.rotate hfg hBA hRS hAD
  -- (the square on AC, described either way, is one square)
  have hkl : SameSideOf k l A C := (hk.trans hl.symm).swap
  have hsqAC : quadArea A C k l = quadArea A C T U :=
    Prop46.square_eq hsq₃.rotate.rotate.rotate hkl hAC hTU rfl
  -- therefore the square on DC is equal to the square on BC,
  have hsq : quadArea C D d e = quadArea C B P Q := by
    have hp₁ : Parallelogram C D d e :=
      Prop28.square hsq₁.rotate.rotate.rotate hDdeC_side.swap
    have hp₂ : Parallelogram C B P Q := Prop28.square hBC.rotate.rotate.rotate hPQ.swap
    rw [← hp₁.quadArea_rotate, ← hp₂.quadArea_rotate, h47, hsqDA, hsqAC]
    exact h.symm
  -- so that the side DC is also equal to BC.
  have hDC : ‖C D‖ = ‖C B‖ :=
    Prop46.side_eq hsq₁.rotate.rotate.rotate hDdeC_side.swap hBC.rotate.rotate.rotate hPQ.swap hsq
  -- therefore the angle DAC is equal to the angle BAC. [I. 8]
  have h8 : ∠ D A C = ∠ B A C :=
    Prop8 hADC hABC hAD rfl (by rw [len_symm D C, hDC, len_symm C B])
  exact h8.symm.trans hDAC

end Elements.BookI
