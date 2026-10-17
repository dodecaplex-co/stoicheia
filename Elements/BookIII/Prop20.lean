import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Helpers
import Elements.BookI.Prop05
import Elements.BookI.Prop32

/-!
# Book III, Proposition 20

Euclid's text, in Heath's translation: [`heath/III/20.md`](../../heath/III/20.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- In a circle the angle at the centre is double of the angle at the circumference, when the angles
have the same circumference as base. -/
theorem Prop20 {A B C E : Point} {ABC : Circle} (hE : Centre E ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hEA : SameSideOf E A B C) :
    ∠ B E C = ∠ B A C + ∠ B A C := by
  -- Let ABC be a circle, let the angle BEC be an angle at its centre, and the angle BAC an
  -- angle at the circumference, and let them have the same circumference BC as base;
  -- I say that the angle BEC is double of the angle BAC.
  have hBCA : Triangle B C A := hEA.symm.triangle
  have hBCE : Triangle B C E := hEA.triangle
  have hAE : A ≠ E := ne_of_centre_of_on hE hA
  have hAB : A ≠ B := hBCA.ne₁₃.symm
  have hAC : A ≠ C := hBCA.ne₂₃.symm
  -- For let AE be joined and drawn through to F.
  obtain ⟨AE, hA_AE, hE_AE⟩ := Postulate1 A E hAE
  obtain ⟨F, -, -, hFEA⟩ := line_circle_beyond (centre_inside hE) hE_AE hA_AE hAE
  have hAEF : Between A E F := between_symm hFEA
  /- The isosceles-triangle argument is used again at `C` and at `D`. -/
  have double : ∀ {A B F : Point}, OnCircle A ABC → OnCircle B ABC → Between A E F →
      Triangle A E B → ∠ B E F = ∠ E A B + ∠ E A B := by
    intro A B F hA hB hAEF hAEB
    -- Then, since EA is equal to EB,
    have hEAEB : ‖E A‖ = ‖E B‖ := Definition15 hE hA hB
    -- the angle EAB is also equal to the angle EBA; [I. 5]
    have h5 : ∠ E A B = ∠ E B A := BookI.Prop5.base hAEB.bac hEAEB
    -- therefore the angles EAB, EBA are double of the angle EAB.
    have hdouble : ∠ E A B + ∠ E B A = ∠ E A B + ∠ E A B := by rw [← h5]
    -- But the angle BEF is equal to the angles EAB, EBA; [I. 32]
    have h32 : ∠ B E F = ∠ E A B + ∠ E B A := by
      rw [(BookI.Prop32 hAEB.cab hAEF).1, angle_symm hAEB.ne₁₃.symm hAEB.ne₁₂.symm]
      ac_rfl
    -- therefore the angle BEF is also double of the angle EAB.
    exact h32.trans hdouble
  have within : SameSideOf E C A B → SameSideOf E B A C → ∠ B E C = ∠ B A C + ∠ B A C := by
    intro hEC hEB
    have hAEB : Triangle A E B := hEC.triangle.acb
    have hAEC : Triangle A E C := hEB.triangle.acb
    have hFEB : ∠ B E F = ∠ E A B + ∠ E A B := double hA hB hAEF hAEB
    -- For the same reason
    -- the angle FEC is also double of the angle EAC.
    have hFEC : ∠ C E F = ∠ E A C + ∠ E A C := double hA hC hAEF hAEC
    -- Therefore the whole angle BEC is double of the whole angle BAC.
    obtain ⟨X, hBXC, hX⟩ := crossbar hEC hEB
    obtain ⟨N, hB_N, hC_N⟩ := Postulate1 B C hBCA.ne₁₂
    have hX_N : OnLine X N := on_line_of_between_ends hBXC hB_N hC_N
    have hAEX : Between A E X := by
      obtain ⟨-, hXA, ⟨K, hA_K, hE_K, hX_K⟩, hXAE⟩ := hX
      have hEX : E ≠ X := fun e => hBCE.off_line hB_N hC_N (e ▸ hX_N)
      rcases between_cases hAE hEX hXA.symm hA_K hE_K hX_K with h | h | h
      · exact h
      · exact absurd (between_symm h) hXAE
      · exact absurd (hEA.symm.sameSide hB_N hC_N) (pasch3 h hX_N)
    have hXray : OnRay X E F := OnRay.of_between_between hAEF hAEX
    rw [angle_add_of_between hBCE hBXC, angle_onRay_right hXray hBCE.ne₁₃,
      angle_onRay_left hXray hBCE.ne₂₃, angle_symm (ne_of_between (between_symm hAEF))
      hBCE.ne₂₃, hFEB, hFEC, angle_add_of_within hEC hEB, angle_symm hAB.symm hAE.symm]
    ac_rfl
  -- Again let another straight line be inflected, and let there be another angle BDC; let DE
  -- be joined and produced to G.
  have across : ∀ {B C D : Point}, OnCircle B ABC → OnCircle C ABC → OnCircle D ABC →
      OppositeSidesOf E C D B → ∠ B E C = ∠ B D C + ∠ B D C := by
    intro B C D hB hC hD hEC
    have hDE : D ≠ E := ne_of_centre_of_on hE hD
    obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hDE
    obtain ⟨G, -, -, hGED⟩ := line_circle_beyond (centre_inside hE) hE_DE hD_DE hDE
    have hDEG : Between D E G := between_symm hGED
    have hDB : D ≠ B := hEC.1
    obtain ⟨L, hD_L, hB_L⟩ := Postulate1 D B hDB
    obtain ⟨Y, hY_L, hEYC⟩ := (hEC.2 L hD_L hB_L).exists_between
    have hY_in : InsideCircle Y ABC :=
      inside_of_between (Or.inl (centre_inside hE)) (Or.inr hC) hEYC
    have hDYB : Between D Y B := between_of_inside_chord hY_L hD_L hB_L hY_in hD hB hDB
    have hDBE : Triangle D B E := hEC.triangle
    have hDBC : Triangle D B C := hEC.symm.triangle
    have hDY : D ≠ Y := ne_of_between hDYB
    have hECD : Triangle E C D := by
      rintro ⟨K, hE_K, hC_K, hD_K⟩
      have hY_K : OnLine Y K := on_line_of_between_ends hEYC hE_K hC_K
      exact hDBC.off_line hD_L hB_L ((line_unique hDY hD_K hY_K hD_L hY_L) ▸ hC_K)
    have hDEC : Triangle D E C := hECD.cab
    have hDEB : Triangle D E B := hDBE.acb
    -- Similarly then we can prove that the angle GEC is double of the angle EDC,
    have hGEC : ∠ C E G = ∠ E D C + ∠ E D C := double hD hC hDEG hDEC
    -- of which the angle GEB is double of the angle EDB;
    have hGEB : ∠ B E G = ∠ E D B + ∠ E D B := double hD hB hDEG hDEB
    -- therefore the angle BEC which remains is double of the angle BDC.
    /- `B` lies within the angle `EDC`, and within the angle `GEC`. -/
    have hsplitD : ∠ E D C = ∠ E D B + ∠ B D C := by
      rw [angle_add_of_between hECD hEYC, angle_onRay_right (OnRay.of_between hDYB) hDEC.ne₁₂.symm,
        angle_onRay_left (OnRay.of_between hDYB) hDBC.ne₁₃.symm]
    obtain ⟨K, hE_K, hG_K⟩ := Postulate1 E G (ne_of_between (between_symm hDEG)).symm
    have hD_K : OnLine D K := on_line_of_between (between_symm hDEG) hG_K hE_K
    have hY_K : ¬ OnLine Y K := fun hY_K =>
      hDBE.off_line hD_L hB_L ((line_unique hDY hD_K hY_K hD_L hY_L) ▸ hE_K)
    have hBC_EG : SameSideOf B C E G :=
      SameSideOf.of_line (ne_of_between (between_symm hDEG)).symm hE_K hG_K
        (same_side_trans (pasch2 hDYB hD_K hY_K) (pasch2 hEYC hE_K hY_K))
    have hBG_EC : SameSideOf B G E C := by
      have hDG : OppositeSidesOf D G E C := (OppositeSidesOf.of_between hECD.bac hDEG).swap
      obtain ⟨P, hE_P, hC_P⟩ := Postulate1 E C hECD.ne₁₂
      have hY_P : OnLine Y P := on_line_of_between_ends hEYC hE_P hC_P
      have hD_P : ¬ OnLine D P := hECD.off_line hE_P hC_P
      have hB_P : ¬ OnLine B P := fun hB_P =>
        hD_P (on_line_of_between (between_symm hDYB) hB_P hY_P)
      have hDB : OppositeSidesOf D B E C :=
        OppositeSidesOf.of_line hECD.ne₁₂ hE_P hC_P ⟨hD_P, hB_P, pasch3 hDYB hY_P⟩
      exact OppositeSidesOf.sameSideOf hDB hDG
    have hsplitE : ∠ G E C = ∠ G E B + ∠ B E C := angle_add_of_within hBC_EG hBG_EC
    have h := hsplitE
    rw [angle_symm (ne_of_between (between_symm hDEG)) hDEC.ne₂₃.symm, hGEC,
      angle_symm (ne_of_between (between_symm hDEG)) hDEB.ne₂₃.symm, hGEB, hsplitD] at h
    apply CommonNotion3 (c := ∠ E D B + ∠ E D B) (d := ∠ E D B + ∠ E D B) _ rfl
    rw [add_comm, ← h]
    ac_rfl
  -- Therefore etc.
  /- Which of Euclid's figures we are in: `E` on an arm of the angle `BAC`, within it,
     or outside it. -/
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  obtain ⟨M, hA_M, hC_M⟩ := Postulate1 A C hAC
  have hC_L : ¬ OnLine C L := hBCA.cab.off_line hA_L hB_L
  have hB_M : ¬ OnLine B M := hBCA.cab.acb.off_line hA_M hC_M
  by_cases hE_L : OnLine E L
  · /- `E` on `AB`, the case Euclid leaves out: `BEC` is the angle `FEC`. -/
    have hAEB : Between A E B := between_of_inside_chord hE_L hA_L hB_L (centre_inside hE) hA hB hAB
    have hAEC : Triangle A E C := Triangle.of_line hA_L hE_L hAE hC_L
    rw [angle_onRay_left (OnRay.of_between_between hAEF hAEB) hAEC.ne₂₃.symm,
      angle_symm (ne_of_between (between_symm hAEF)) hAEC.ne₂₃.symm, double hA hC hAEF hAEC,
      angle_onRay_left (OnRay.of_between hAEB) hAC.symm]
  by_cases hE_M : OnLine E M
  · have hAEC : Between A E C := between_of_inside_chord hE_M hA_M hC_M (centre_inside hE) hA hC hAC
    have hAEB : Triangle A E B := Triangle.of_line hA_M hE_M hAE hB_M
    rw [angle_symm hBCE.ne₁₃ hBCE.ne₂₃,
      angle_onRay_left (OnRay.of_between_between hAEF hAEC) hAEB.ne₂₃.symm,
      angle_symm (ne_of_between (between_symm hAEF)) hAEB.ne₂₃.symm, double hA hB hAEF hAEB,
      angle_onRay_left (OnRay.of_between hAEC) hAB.symm, angle_symm hAC.symm hAB.symm]
  by_cases hs1 : SameSide E C L
  · by_cases hs2 : SameSide E B M
    · exact within (SameSideOf.of_line hAB hA_L hB_L hs1) (SameSideOf.of_line hAC hA_M hC_M hs2)
    · rw [angle_symm hBCE.ne₁₃ hBCE.ne₂₃,
        across hC hB hA (OppositeSidesOf.of_line hAC hA_M hC_M ⟨hE_M, hB_M, hs2⟩),
        angle_symm hAC.symm hAB.symm]
  · exact across hB hC hA (OppositeSidesOf.of_line hAB hA_L hB_L ⟨hE_L, hC_L, hs1⟩)
  -- Q. E. D.

end Elements.BookIII
