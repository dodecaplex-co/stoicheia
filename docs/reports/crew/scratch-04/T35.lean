import Elements.BookI.Prop04
import Elements.BookI.Prop34
import Elements.BookI.HelpersParallels

namespace Elements.BookI
open Tacit

/-- Throwaway: Euclid's case of I.35, where `D` lies between `A` and `E`. -/
theorem T35euclid {A B C D E F : Point} (h₁ : Parallelogram A B C D) (h₂ : Parallelogram E B C F)
    {L : Line} (hA : OnLine A L) (hD : OnLine D L) (hE : OnLine E L) (hF : OnLine F L)
    (hADE : Between A D E) :
    quadArea A B C D = quadArea E B C F := by
  obtain ⟨M, hB, hC⟩ := Postulate1 B C h₁.2.1
  have hLM : Parallel L M := (h₁.2.parallel hB hC hD hA).symm
  -- AD is equal to BC [I. 34], and AB to DC
  obtain ⟨hAD, hAB, -, -, -⟩ := Prop34 (A := A) (B := D) (C := B) (D := C) h₁
  -- EF is equal to BC
  obtain ⟨hEF, -, -, -, -⟩ := Prop34 (A := E) (B := F) (C := B) (D := C) h₂
  -- Euclid's G: EB and DC cross (his figure), for EC and BD cannot.
  have hED : E ≠ D := (ne_of_between (between_symm hADE))
  have hEDBC : AreParallel E D B C := AreParallel.of_parallel hED h₁.2.1 hE hD hB hC hLM
  obtain ⟨DC, hD_DC, hC_DC⟩ := Postulate1 D C h₁.1.2.1.symm
  have hAB_DC : SameSide A B DC := h₁.1.sameSideOf.sameSide hC_DC hD_DC
  have hA_DC : ¬ OnLine A DC := not_on_line_of_same_side hAB_DC
  have hE_DC : ¬ OnLine E DC := fun hE' => hA_DC (on_line_of_between (between_symm hADE) hE' hD_DC)
  have hEB : ¬ SameSide E B DC := fun hs =>
    pasch3 hADE hD_DC (same_side_trans (same_side_symm hAB_DC) (same_side_symm hs))
  obtain ⟨G, hEGB, hDGC⟩ : ∃ G : Point, Between E G B ∧ Between D G C := by
    rcases hEDBC.cross_or with ⟨X, hEXC, hBXD⟩ | hG
    · have hX : ¬ OnLine X DC := fun hX => hE_DC (on_line_of_between (between_symm hEXC) hC_DC hX)
      exact absurd (same_side_trans (pasch2 (between_symm hEXC) hC_DC hX)
        (pasch2 (between_symm hBXD) hD_DC hX)) hEB
    · exact hG
  /- Then `D` and `C` lie on either side of `EB`, and so do `D` and `F`: `E` lies between
     `D` and `F`. -/
  obtain ⟨EB, hE_EB, hB_EB⟩ := Postulate1 E B h₂.1.1
  have hG_EB : OnLine G EB := on_line_of_between_ends hEGB hE_EB hB_EB
  have hD_EB : ¬ OnLine D EB := fun hD' =>
    hLM.symm.not_onLine hB ((line_unique hED hE_EB hD' hE hD) ▸ hB_EB)
  have hC_EB : ¬ OnLine C EB := fun hC' =>
    hD_EB (on_line_of_between (between_symm hDGC) hC' hG_EB)
  have hCF : SameSide C F EB := h₂.sameSideOf.sameSide hE_EB hB_EB
  have hDF : ¬ SameSide D F EB := fun hs =>
    pasch3 hDGC hG_EB (same_side_trans (same_side_symm hs) (same_side_symm hCF))
  have hDEF : Between D E F := by
    obtain ⟨Y, hY_EB, hDYF⟩ := OppositeSides.exists_between
      ⟨hD_EB, not_on_line_of_same_side (same_side_symm hCF), hDF⟩
    have hY_L : OnLine Y L := on_line_of_between_ends hDYF hD hF
    have hLEB : L ≠ EB := fun e => hLM.not_onLine (e ▸ hB_EB) hB
    have : Y = E := Classical.byContradiction fun hYE =>
      hLEB (line_unique hYE hY_L hE hY_EB hE_EB)
    exact this ▸ hDYF
  -- AE is equal to DF [C.N. 2]
  have hAE_DF : ‖A E‖ = ‖D F‖ := by
    rw [← len_add_of_between hADE, ← len_add_of_between hDEF, hAD, ← hEF, add_comm]
  -- the angle FDC is equal to the angle EAB, the exterior to the interior [I. 29]
  have hADF : Between A D F := between_of_between_right hADE hDEF
  have hFDC : ∠ F D C = ∠ E A B := by
    rw [Prop29.exterior h₁.1.symm.swap_left h₁.2.sameSideOf.symm (between_symm hADF),
      angle_onRay_left (OnRay.of_beyond hADE) h₁.triangle.ne₁₂.symm]
  -- the triangle EAB is equal to the triangle FDC [I. 4]
  have hB_L : ¬ OnLine B L := hLM.symm.not_onLine hB
  have hC_L : ¬ OnLine C L := hLM.symm.not_onLine hC
  have hAEB : Triangle A E B := Triangle.of_line hA hE (ne_of_between_ends hADE) hB_L
  have hDFC : Triangle D F C := Triangle.of_line hD hF (ne_of_between_ends hDEF) hC_L
  have h4 : △ A E B = △ D F C := (Prop4 hAEB hDFC hAE_DF hAB hFDC.symm).2.1
  -- Let DGE be subtracted from each [C.N. 3]
  have trap : △ B A D + △ D G B = △ E G C + △ C E F := by
    have e₁ : △ A E B = △ B A D + △ D G B + △ E D G := by
      rw [area_cab A E B, ← area_cut (A := B) hADE, area_bca B D E, ← area_cut (A := D) hEGB,
        area_bac D E G]
      ac_rfl
    have e₂ : △ D F C = △ E G C + △ C E F + △ E D G := by
      rw [area_cab D F C, ← area_cut (A := C) hDEF, area_cba C D E, ← area_cut (A := E) hDGC]
      ac_rfl
    exact CommonNotion3 (e₁.symm.trans (h4.trans e₂)) rfl
  -- Let the triangle GBC be added to each [C.N. 2]
  have hL : quadArea A B C D = (△ B A D + △ D G B) + △ B G C := by
    rw [← h₁.quadArea_rotate]
    unfold quadArea
    rw [area_acb B C D, ← area_cut (A := B) hDGC, area_acb B D A, area_bca B D G]
    ac_rfl
  have hR : quadArea E B C F = (△ E G C + △ C E F) + △ B G C := by
    unfold quadArea
    rw [area_cab E B C, ← area_cut (A := C) hEGB, area_bca C E G, area_cba C G B, area_bac E C F]
    ac_rfl
  rw [hL, hR, trap]

end Elements.BookI

namespace Elements.BookI
open Tacit

/-- Throwaway: Proclus' case of I.35 where `E` lies between `A` and `D`. -/
theorem T35between {A B C D E F : Point} (h₁ : Parallelogram A B C D) (h₂ : Parallelogram E B C F)
    {L : Line} (hA : OnLine A L) (hD : OnLine D L) (hE : OnLine E L) (hF : OnLine F L)
    (hAED : Between A E D) :
    quadArea A B C D = quadArea E B C F := by
  obtain ⟨M, hB, hC⟩ := Postulate1 B C h₁.2.1
  have hLM : Parallel L M := (h₁.2.parallel hB hC hD hA).symm
  obtain ⟨hAD, hAB, -, -, -⟩ := Prop34 (A := A) (B := D) (C := B) (D := C) h₁
  obtain ⟨hEF, -, -, -, -⟩ := Prop34 (A := E) (B := F) (C := B) (D := C) h₂
  obtain ⟨DC, hD_DC, hC_DC⟩ := Postulate1 D C h₁.1.2.1.symm
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B h₁.1.1
  have hED : E ≠ D := (ne_of_between (between_symm hAED)).symm
  have hAE : A ≠ E := ne_of_between hAED
  have hB_L : ¬ OnLine B L := hLM.symm.not_onLine hB
  have hC_L : ¬ OnLine C L := hLM.symm.not_onLine hC
  -- E and C lie on one side of AB, so the diameters AC, BE of ABCE cross
  have hCD_AB : SameSide C D AB := h₁.sameSideOf.sameSide hA_AB hB_AB
  have hE_AB : ¬ OnLine E AB := fun h =>
    hB_L ((line_unique hAE hA_AB h hA hE) ▸ hB_AB)
  have hED_AB : SameSide E D AB := pasch2 hAED hA_AB hE_AB
  have hEC_AB : SameSide E C AB := same_side_trans (same_side_symm hED_AB) (same_side_symm hCD_AB)
  have hAEBC : AreParallel A E B C := AreParallel.of_parallel hAE h₁.2.1 hA hE hB hC hLM
  obtain ⟨Y, hAYC, hBYE⟩ : ∃ Y : Point, Between A Y C ∧ Between B Y E := by
    rcases hAEBC.cross_or with hY | ⟨Y, hAYB, hEYC⟩
    · exact hY
    · exact absurd hEC_AB (pasch3 hEYC (on_line_of_between_ends hAYB hA_AB hB_AB))
  -- E and B lie on one side of DC, so the diameters EC, BD of EBCD cross
  have hAB_DC : SameSide A B DC := h₁.1.sameSideOf.sameSide hC_DC hD_DC
  have hE_DC : ¬ OnLine E DC := fun h =>
    hC_L (by rw [line_unique hED hE hD h hD_DC]; exact hC_DC)
  have hEA_DC : SameSide E A DC := pasch2 (between_symm hAED) hD_DC hE_DC
  have hEB_DC : SameSide E B DC := same_side_trans (same_side_symm hEA_DC) hAB_DC
  have hEDBC : AreParallel E D B C := AreParallel.of_parallel hED h₁.2.1 hE hD hB hC hLM
  obtain ⟨X, hEXC, hBXD⟩ : ∃ X : Point, Between E X C ∧ Between B X D := by
    rcases hEDBC.cross_or with hX | ⟨X, hEXB, hDXC⟩
    · exact hX
    · exact absurd hEB_DC (pasch3 hEXB (on_line_of_between_ends hDXC hD_DC hC_DC))
  -- so D lies on C's side of EB, as F does, and D lies between E and F
  have hEBC : Triangle E B C := Triangle.of_line hB hC h₁.2.1 (hLM.not_onLine hE) |>.cab
  have hCD_EB : SameSideOf C D E B := SameSideOf.of_cross hEXC hBXD hEBC
  have hFray : OnRay F E D :=
    OnRay.of_sameSideOf (h₂.sameSideOf.symm.trans hCD_EB) ⟨L, hE, hD, hF⟩
      (ne_of_len_eq hEF h₁.2.1).symm
  have hED_lt : ‖E D‖ < ‖E F‖ := by
    rw [hEF, ← hAD, len_symm A D, len_symm E D]
    exact len_lt_of_between (between_symm hAED)
  have hEDF : Between E D F := (OnRay.self hED).between_of_len_lt hFray hED_lt
  have hADF : Between A D F :=
    between_symm (between_of_between_right (between_symm hEDF) (between_symm hAED))
  -- AE is equal to DF, and the triangles EAB, FDC are equal [I. 4]
  have hAE_DF : ‖A E‖ = ‖D F‖ := by
    refine CommonNotion3 (c := ‖E D‖) (d := ‖E D‖) ?_ rfl
    rw [len_add_of_between hAED, add_comm, len_add_of_between hEDF, hAD, hEF]
  have hFDC : ∠ F D C = ∠ E A B := by
    rw [Prop29.exterior h₁.1.symm.swap_left h₁.2.sameSideOf.symm (between_symm hADF),
      angle_onRay_left (OnRay.of_between hAED) h₁.triangle.ne₁₂.symm]
  have hAEB : Triangle A E B := Triangle.of_line hA hE hAE hB_L
  have hDFC : Triangle D F C := Triangle.of_line hD hF (ne_of_between_ends hEDF |> fun _ =>
    (ne_of_between (between_symm hEDF)).symm |> fun h => (ne_of_between_ends hADF |> fun _ => h)) hC_L
  have h4 : △ A E B = △ D F C := (Prop4 hAEB hDFC hAE_DF hAB hFDC.symm).2.1
  -- Proclus: the triangles added to the trapezium EBCD
  have hL₁ : quadArea A B C D = △ B C E + △ A E B + △ C E D := by
    have hq : quadArea B C E A = quadArea A B C E := quadArea_rotate_of_cross hAYC hBYE
    unfold quadArea at hq ⊢
    rw [area_bac A C D, ← area_cut (A := C) hAED, area_bac C A E, ← add_assoc, ← hq,
      area_cba B E A]
  have hR₁ : quadArea E B C F = △ B C E + △ D F C + △ C E D := by
    unfold quadArea
    rw [area_bac E C F, ← area_cut (A := C) hEDF, area_bca E B C, area_bca C D F]
    ac_rfl
  rw [hL₁, hR₁, h4]


end Elements.BookI

namespace Elements.BookI
open Tacit

/-- Throwaway: the case of I.35 where `E` falls on `D`. -/
theorem T35same {A B C D F : Point} (h₁ : Parallelogram A B C D) (h₂ : Parallelogram D B C F)
    {L : Line} (hA : OnLine A L) (hD : OnLine D L) (hF : OnLine F L) :
    quadArea A B C D = quadArea D B C F := by
  obtain ⟨M, hB, hC⟩ := Postulate1 B C h₁.2.1
  have hLM : Parallel L M := (h₁.2.parallel hB hC hD hA).symm
  obtain ⟨hAD, hAB, -, -, -⟩ := Prop34 (A := A) (B := D) (C := B) (D := C) h₁
  obtain ⟨hDF, -, -, -, -⟩ := Prop34 (A := D) (B := F) (C := B) (D := C) h₂
  -- A and F lie on either side of DB, so D lies between them
  obtain ⟨DB, hD_DB, hB_DB⟩ := Postulate1 D B h₂.1.1
  obtain ⟨X, hAXC, hBXD⟩ := h₁.cross
  have hX_DB : OnLine X DB := on_line_of_between_ends hBXD hB_DB hD_DB
  have hDA : D ≠ A := (ne_of_len_eq hAD h₁.2.1).symm
  have hA_DB : ¬ OnLine A DB := fun h =>
    hLM.symm.not_onLine hB (by rw [line_unique hDA hD hA hD_DB h]; exact hB_DB)
  have hC_DB : ¬ OnLine C DB := fun h =>
    hA_DB (on_line_of_between (between_symm hAXC) h hX_DB)
  have hCF : SameSide C F DB := h₂.sameSideOf.sameSide hD_DB hB_DB
  have hAF : ¬ SameSide A F DB := fun hs =>
    pasch3 hAXC hX_DB (same_side_trans (same_side_symm hs) (same_side_symm hCF))
  have hADF : Between A D F := by
    obtain ⟨Y, hY_DB, hAYF⟩ := OppositeSides.exists_between
      ⟨hA_DB, not_on_line_of_same_side (same_side_symm hCF), hAF⟩
    have hY_L : OnLine Y L := on_line_of_between_ends hAYF hA hF
    have hLDB : L ≠ DB := fun e => hLM.symm.not_onLine hB (e ▸ hB_DB)
    have : Y = D := Classical.byContradiction fun hYD =>
      hLDB (line_unique hYD hY_L hD hY_DB hD_DB)
    exact this ▸ hAYF
  have hFDC : ∠ F D C = ∠ D A B :=
    Prop29.exterior h₁.1.symm.swap_left h₁.2.sameSideOf.symm (between_symm hADF)
  have hB_L : ¬ OnLine B L := hLM.symm.not_onLine hB
  have hC_L : ¬ OnLine C L := hLM.symm.not_onLine hC
  have h4 : △ A D B = △ D F C :=
    (Prop4 (Triangle.of_line hA hD hDA.symm hB_L) (Triangle.of_line hD hF
      (ne_of_between (between_symm hADF)).symm hC_L) (hAD.trans hDF.symm) hAB hFDC.symm).2.1
  rw [← h₁.quadArea_rotate]
  unfold quadArea
  rw [area_cab B D A, area_acb A B D, h4, area_cab B C D, area_acb D C F]

/-- Throwaway: I.35 in general. -/
theorem T35 {A B C D E F : Point} (h₁ : Parallelogram A B C D) (h₂ : Parallelogram E B C F)
    (hAF : ∃ L : Line, OnLine A L ∧ OnLine D L ∧ OnLine E L ∧ OnLine F L) :
    quadArea A B C D = quadArea E B C F := by
  obtain ⟨L, hA, hD, hE, hF⟩ := hAF
  have oneway : ∀ {A D E F : Point}, Parallelogram A B C D → Parallelogram E B C F →
      OnLine A L → OnLine D L → OnLine E L → OnLine F L → (E = A ∨ SameSideOf C E A B) →
      quadArea A B C D = quadArea E B C F := by
    intro A D E F h₁ h₂ hA hD hE hF hdir
    obtain ⟨hAD, -, -, -, -⟩ := Prop34 (A := A) (B := D) (C := B) (D := C) h₁
    obtain ⟨hEF, -, -, -, -⟩ := Prop34 (A := E) (B := F) (C := B) (D := C) h₂
    rcases hdir with rfl | hCE
    · /- `E` is `A`: then `F` is `D`. -/
      have hFray : OnRay F E D :=
        OnRay.of_sameSideOf (h₂.sameSideOf.symm.trans h₁.sameSideOf) ⟨L, hE, hD, hF⟩
          (h₂.sameSideOf.symm.triangle.ne₁₃.symm)
      rw [hFray.eq_of_len_eq (hEF.trans hAD.symm)]
    · have hEA : E ≠ A := hCE.symm.triangle.ne₁₃.symm
      have hEray : OnRay E A D :=
        OnRay.of_sameSideOf (hCE.symm.trans h₁.sameSideOf) ⟨L, hA, hD, hE⟩ hEA
      by_cases hED : E = D
      · subst hED
        exact T35same h₁ h₂ hA hE hF
      · rcases between_cases hEray.1 (Ne.symm hED) hEA.symm hA hD hE with h | h | h
        · exact T35euclid h₁ h₂ hA hD hE hF h
        · exact absurd (between_symm h) hEray.2.2.2
        · exact T35between h₁ h₂ hA hD hE hF h
  by_cases hEA : E = A
  · exact oneway h₁ h₂ hA hD hE hF (Or.inl hEA)
  · obtain ⟨M, hB, hC⟩ := Postulate1 B C h₁.2.1
    have hLM : Parallel L M := (h₁.2.parallel hB hC hD hA).symm
    rcases (AreParallel.of_parallel (Ne.symm hEA) h₁.2.1 hA hE hB hC hLM).sameSideOf_or with h | h
    · exact oneway h₁ h₂ hA hD hE hF (Or.inr h)
    · exact (oneway h₂ h₁ hE hF hA hD (Or.inr h)).symm

end Elements.BookI
