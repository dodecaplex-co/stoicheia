import Elements.BookI.Prop44

namespace Elements.BookI
open Tacit

/-- Throwaway: the body of I.44, to test that I.43's hypotheses can be met. -/
theorem T44 {A B C₁ C₂ C₃ D₁ D D₂ P : Point} (hAB : A ≠ B) (hC : Triangle C₁ C₂ C₃)
    (hD : Triangle D₁ D D₂) (hP : ¬ Collinear A B P) :
    ∃ L M : Point, SameSideOf M P A B ∧ Parallelogram A B M L ∧
      ∠ A B M = ∠ D₁ D D₂ ∧ quadArea A B M L = △ C₁ C₂ C₃ := by
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  have hP_AB : ¬ OnLine P AB := fun h => hP ⟨AB, hA_AB, hB_AB, h⟩
  -- [I. 42], and placed
  obtain ⟨E₀, F₀, G₀, -, -, h42, hang42, harea42⟩ := Prop42 hC hD
  obtain ⟨X, hXP, -⟩ := exists_oppositeSidesOf (fun ⟨K, hA_K, hB_K, hP_K⟩ =>
    hP ⟨K, hA_K, hB_K, hP_K⟩ : Triangle A B P) []
  obtain ⟨E, F, G, hABE, hGX, hBEFG, hEBG, harea⟩ := Prop44.place hAB hXP.triangle h42
  have hE_AB : OnLine E AB := on_line_of_between hABE hA_AB hB_AB
  have hBE : B ≠ E := (ne_of_between (between_symm hABE)).symm
  -- the straight lines of the parallelogram BEFG
  have hBG : B ≠ G := hBEFG.2.2.1.symm
  obtain ⟨BG, hB_BG, hG_BG⟩ := Postulate1 B G hBG
  obtain ⟨EF, hE_EF, hF_EF⟩ := Postulate1 E F hBEFG.2.1
  obtain ⟨FG, hF_FG, hG_FG⟩ := Postulate1 F G hBEFG.1.2.1
  have hAB_FG : Parallel AB FG := hBEFG.1.parallel hB_AB hE_AB hF_FG hG_FG
  have hEF_BG : Parallel EF BG := hBEFG.2.parallel hE_EF hF_EF hG_BG hB_BG
  have hG_AB : ¬ OnLine G AB := hAB_FG.symm.not_onLine hG_FG
  -- AH through A parallel to BG [I. 31]; H where it meets FG produced
  have hA_BG : ¬ OnLine A BG := fun h =>
    hG_AB ((line_unique hAB.symm hB_BG h hB_AB hA_AB) ▸ hG_BG)
  obtain ⟨U, V, hUAV, hUV⟩ := Prop31 hBG (fun ⟨K, hB_K, hG_K, hA_K⟩ =>
    hA_BG ((line_unique hBG hB_K hG_K hB_BG hG_BG) ▸ hA_K))
  obtain ⟨LA, hU_LA, hV_LA⟩ := Postulate1 U V hUV.1
  have hA_LA : OnLine A LA := on_line_of_between_ends hUAV hU_LA hV_LA
  have hLA_BG : Parallel LA BG := hUV.parallel hU_LA hV_LA hB_BG hG_BG
  have hFG_BG : FG ≠ BG := fun e => hAB_FG.not_onLine hB_AB (e ▸ hB_BG)
  obtain ⟨H, hH_FG, hH_LA⟩ := Prop30.meet hLA_BG hG_BG hG_FG hFG_BG
  have hAE : A ≠ E := ne_of_between_ends hABE
  have hLA_EF_ne : LA ≠ EF := fun e =>
    hAB_FG.not_onLine ((line_unique hAE hA_AB hE_AB (e ▸ hA_LA) hE_EF) ▸ hF_EF) hF_FG
  have hLA_EF : Parallel LA EF := Prop30.parallel hLA_BG hEF_BG hLA_EF_ne
  have hAH : A ≠ H := fun e => hAB_FG.not_onLine hA_AB (e ▸ hH_FG)
  have hHF : H ≠ F := fun e => hLA_EF.not_onLine hH_LA (e ▸ hF_EF)
  -- Let HB be joined.
  have hHB : H ≠ B := fun e => hAB_FG.not_onLine hB_AB (e ▸ hH_FG)
  obtain ⟨HB, hH_HB, hB_HB⟩ := Postulate1 H B hHB
  -- AHF, HFE are equal to two right angles [I. 29]
  have hAE_FG : SameSide A E FG := hAB_FG.sameSide hA_AB hE_AB
  have hAHFE : AreParallel H A F E :=
    AreParallel.of_parallel hAH.symm hBEFG.2.1.symm hH_LA hA_LA hF_EF hE_EF hLA_EF
  have h29 : ∠ A H F + ∠ H F E = ∟ + ∟ :=
    Prop29.interior hAHFE (SameSideOf.of_line hHF hH_FG hF_FG hAE_FG)
  -- Therefore BHG, GFE are less than two right angles
  have hBE_LA : SameSide B E LA := pasch2 hABE hA_LA (fun h => hLA_BG.not_onLine h hB_BG)
  have hEF_LA : SameSide E F LA := hLA_EF.symm.sameSide hE_EF hF_EF
  have hBF_HA : SameSideOf B F H A :=
    SameSideOf.of_line hAH.symm hH_LA hA_LA (same_side_trans (same_side_symm hBE_LA) hEF_LA)
  have hBA_HF : SameSideOf B A H F :=
    SameSideOf.of_line hHF hH_FG hF_FG (hAB_FG.sameSide hB_AB hA_AB)
  have hAHF : ∠ A H F = ∠ A H B + ∠ B H F := angle_add_of_within hBF_HA hBA_HF
  have hlt : ∠ B H F + ∠ H F E < ∟ + ∟ :=
    calc ∠ B H F + ∠ H F E < (∠ B H F + ∠ H F E) + ∠ A H B :=
          CommonNotion5 hBF_HA.triangle.bac.angle_pos
      _ = ∟ + ∟ := by rw [← h29, hAHF]; ac_rfl
  -- HB, FE, when produced, will meet [Post. 5]
  have hBE_FG' : SameSide B E FG := hAB_FG.sameSide hB_AB hE_AB
  obtain ⟨K, hK_HB, hK_EF, hKB⟩ :=
    Postulate5 hB_HB hH_HB hH_FG hF_FG hF_EF hE_EF hHF hBE_FG' hlt
  have hH_AB : ¬ OnLine H AB := hAB_FG.symm.not_onLine hH_FG
  have hH_BG : ¬ OnLine H BG := hLA_BG.not_onLine hH_LA
  have hK_BG : ¬ OnLine K BG := hEF_BG.not_onLine hK_EF
  have hK_FG : ¬ OnLine K FG := not_on_line_of_same_side hKB
  have hK_AB : ¬ OnLine K AB := fun hK => by
    by_cases hKE : K = E
    · subst hKE
      exact hH_AB ((line_unique hBE hB_HB hK_HB hB_AB hK) ▸ hH_HB)
    · exact hAB_FG.not_onLine ((line_unique hKE hK_EF hE_EF hK hE_AB) ▸ hF_EF) hF_FG
  -- through K let KL be drawn parallel to FH [I. 31]
  obtain ⟨U', V', hU'KV', hU'V'⟩ := Prop31 hHF.symm (fun ⟨K', hF', hH', hK'⟩ =>
    hK_FG ((line_unique hHF.symm hF' hH' hF_FG hH_FG) ▸ hK'))
  obtain ⟨LK, hU'_LK, hV'_LK⟩ := Postulate1 U' V' hU'V'.1
  have hK_LK : OnLine K LK := on_line_of_between_ends hU'KV' hU'_LK hV'_LK
  have hLK_FG : Parallel LK FG := hU'V'.parallel hU'_LK hV'_LK hF_FG hH_FG
  have hLK_AB : Parallel LK AB :=
    Prop30.parallel hLK_FG hAB_FG (fun e => hK_AB (e ▸ hK_LK))
  -- let HA, GB be produced to the points L, M
  have hLA_FG : LA ≠ FG := fun e => hLA_BG.not_onLine (e ▸ hG_FG) hG_BG
  obtain ⟨L, hL_LA, hL_LK⟩ := Prop30.meet hLK_FG hH_FG hH_LA hLA_FG
  obtain ⟨M, hM_BG, hM_LK⟩ := Prop30.meet hLK_FG hG_FG hG_BG hFG_BG.symm
  -- where the points fall: parallels keep order
  have hHGF : Between H G F := hABE.of_sameSide hB_BG (hLA_BG.sameSide hH_LA hA_LA)
    (hEF_BG.sameSide hF_EF hE_EF) hG_BG ⟨FG, hH_FG, hG_FG, hF_FG⟩
  have hHBK : Between H B K := hHGF.of_sameSide hG_BG (same_side_refl hH_BG)
    (hEF_BG.sameSide hK_EF hF_EF) hB_BG ⟨HB, hH_HB, hB_HB, hK_HB⟩
  have hFEK : Between F E K := hHBK.of_sameSide hB_AB (hAB_FG.symm.sameSide hF_FG hH_FG)
    (same_side_refl hK_AB) hE_AB ⟨EF, hF_EF, hE_EF, hK_EF⟩
  have hKML : Between K M L := (between_symm hHBK).of_sameSide hB_BG (same_side_refl hK_BG)
    (hLA_BG.sameSide hL_LA hH_LA) hM_BG ⟨LK, hK_LK, hM_LK, hL_LK⟩
  have hLAH : Between L A H := (between_symm hHBK).of_sameSide hB_AB
    (hLK_AB.sameSide hL_LK hK_LK) (same_side_refl hH_AB) hA_AB ⟨LA, hL_LA, hA_LA, hH_LA⟩
  have hGBM : Between G B M := hHBK.of_sameSide hB_AB (hAB_FG.symm.sameSide hG_FG hH_FG)
    (hLK_AB.sameSide hM_LK hK_LK) hB_AB ⟨BG, hG_BG, hB_BG, hM_BG⟩
  -- the parallelograms about HK
  have hKL : K ≠ L := fun e => hLA_EF.not_onLine (e ▸ hL_LA) hK_EF
  have hLH : L ≠ H := fun e => hLK_FG.not_onLine hL_LK (e ▸ hH_FG)
  have hHG : H ≠ G := fun e => hLA_BG.not_onLine hH_LA (e ▸ hG_BG)
  have hKM : K ≠ M := fun e => hK_BG (e ▸ hM_BG)
  have hMB : M ≠ B := fun e => hLK_AB.not_onLine hM_LK (e ▸ hB_AB)
  have hML : M ≠ L := fun e => hLA_BG.not_onLine (e ▸ hL_LA) hM_BG
  have hLA' : L ≠ A := fun e => hLK_AB.not_onLine hL_LK (e ▸ hA_AB)
  have P₁ : Parallelogram H F K L :=
    ⟨AreParallel.of_parallel hHF hKL hH_FG hF_FG hK_LK hL_LK hLK_FG.symm,
      AreParallel.of_parallel (ne_of_between_ends hFEK) hLH hF_EF hK_EF hL_LA hH_LA
        hLA_EF.symm⟩
  have P₂ : Parallelogram H G B A :=
    ⟨AreParallel.of_parallel hHG hAB.symm hH_FG hG_FG hB_AB hA_AB hAB_FG.symm,
      AreParallel.of_parallel hBG.symm hAH hG_BG hB_BG hA_LA hH_LA hLA_BG.symm⟩
  have P₃ : Parallelogram B E K M :=
    ⟨AreParallel.of_parallel hBE hKM hB_AB hE_AB hK_LK hM_LK hLK_AB.symm,
      AreParallel.of_parallel (ne_of_between (between_symm hFEK)).symm hMB hE_EF hK_EF hM_BG
        hB_BG hEF_BG⟩
  -- therefore LB is equal to BF [I. 43]
  have h43 : quadArea G F E B = quadArea A B M L := Prop43 P₁ hHBK hHGF hFEK hKML hLAH P₂ P₃
  -- the angle GBE is equal to the angle ABM [I. 15]
  have h15 : ∠ G B E = ∠ A B M := (Prop15 hABE hGBM fun ⟨K', hA', hE', hG'⟩ =>
    hG_AB ((line_unique hAE hA' hE' hA_AB hE_AB) ▸ hG')).2
  have hGP : OppositeSidesOf G P A B := hGX.trans_opposite hXP
  have hGM : OppositeSidesOf G M A B :=
    OppositeSidesOf.of_between (Triangle.of_line hA_AB hB_AB hAB hG_AB) hGBM
  refine ⟨L, M, OppositeSidesOf.sameSideOf hGM hGP,
    ⟨AreParallel.of_parallel hAB hML hA_AB hB_AB hM_LK hL_LK hLK_AB.symm,
      AreParallel.of_parallel hMB.symm hLA' hB_BG hM_BG hL_LA hA_LA hLA_BG.symm⟩, ?_, ?_⟩
  · rw [← h15, angle_symm hBG.symm hBE.symm, hEBG, hang42]
  · rw [← h43, quadArea_reverse G B E F, quadArea_rotate₂ E F G B, hBEFG.quadArea_rotate,
      harea, harea42]

end Elements.BookI
