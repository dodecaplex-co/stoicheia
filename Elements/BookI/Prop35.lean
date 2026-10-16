import Elements.Figure.Basics
import Elements.BookI.Prop04
import Elements.BookI.Prop29
import Elements.BookI.Prop34
import Elements.BookI.HelpersParallels

/-!
# Book I, Proposition 35

Euclid's text, in Heath's translation: [`heath/I/35.md`](../../heath/I/35.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- Euclid's figure: with `D` between `A` and `E`, `EB` crosses `DC` at a point `G`
between the parallels, and `E` lies between `D` and `F`. -/
theorem Prop35.figure {A B C D E F : Point} (h₁ : Parallelogram A B C D)
    (h₂ : Parallelogram E B C F) {AF : Line} (hA : OnLine A AF) (hD : OnLine D AF)
    (hF : OnLine F AF) (hADE : Between A D E) :
    ∃ G : Point, Between E G B ∧ Between D G C ∧ Between D E F := by
  have hE : OnLine E AF := on_line_of_between hADE hA hD
  obtain ⟨BC, hB, hC⟩ := Postulate1 B C h₁.2.1
  have hAF_BC : Parallel AF BC := (h₁.2.parallel hB hC hD hA).symm
  have hED : E ≠ D := (ne_of_between (between_symm hADE))
  have hEDBC : AreParallel E D B C := AreParallel.of_parallel hED h₁.2.1 hE hD hB hC hAF_BC
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
  obtain ⟨EB, hE_EB, hB_EB⟩ := Postulate1 E B h₂.1.1
  have hG_EB : OnLine G EB := on_line_of_between_ends hEGB hE_EB hB_EB
  have hD_EB : ¬ OnLine D EB := fun hD' =>
    hAF_BC.symm.not_onLine hB ((line_unique hED hE_EB hD' hE hD) ▸ hB_EB)
  have hCF : SameSide C F EB := h₂.sameSideOf.sameSide hE_EB hB_EB
  have hDF : ¬ SameSide D F EB := fun hs =>
    pasch3 hDGC hG_EB (same_side_trans (same_side_symm hs) (same_side_symm hCF))
  refine ⟨G, hEGB, hDGC, ?_⟩
  obtain ⟨Y, hY_EB, hDYF⟩ := OppositeSides.exists_between
    ⟨hD_EB, not_on_line_of_same_side (same_side_symm hCF), hDF⟩
  have hY_AF : OnLine Y AF := on_line_of_between_ends hDYF hD hF
  have hAF_EB : AF ≠ EB := fun e => hAF_BC.not_onLine (e ▸ hB_EB) hB
  have : Y = E := Classical.byContradiction fun hYE =>
    hAF_EB (line_unique hYE hY_AF hE hY_EB hE_EB)
  exact this ▸ hDYF

/-- One case Euclid leaves out, which Proclus supplies, as Heath reports under I.35:
when `E` lies between `A` and `D`, `D` lies between `E` and `F`. The triangles
`EAB`, `FDC` are equal by I.34, I.29 and I.4; adding each to the trapezium `EBCD`
gives the two parallelograms. -/
theorem Prop35.between {A B C D E F : Point} (h₁ : Parallelogram A B C D) (h₂ : Parallelogram E B C F)
    {AF : Line} (hA : OnLine A AF) (hD : OnLine D AF) (hE : OnLine E AF) (hF : OnLine F AF)
    (hAED : Between A E D) :
    quadArea A B C D = quadArea E B C F := by
  obtain ⟨BC, hB, hC⟩ := Postulate1 B C h₁.2.1
  have hAF_BC : Parallel AF BC := (h₁.2.parallel hB hC hD hA).symm
  obtain ⟨hAD, hAB, -, -, -⟩ := Prop34 (A := A) (B := D) (C := B) (D := C) h₁
  obtain ⟨hEF, -, -, -, -⟩ := Prop34 (A := E) (B := F) (C := B) (D := C) h₂
  obtain ⟨DC, hD_DC, hC_DC⟩ := Postulate1 D C h₁.1.2.1.symm
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B h₁.1.1
  have hED : E ≠ D := (ne_of_between (between_symm hAED)).symm
  have hAE : A ≠ E := ne_of_between hAED
  have hB_AF : ¬ OnLine B AF := hAF_BC.symm.not_onLine hB
  have hC_AF : ¬ OnLine C AF := hAF_BC.symm.not_onLine hC
  /- E and C lie on one side of AB, so the diameters AC, BE of ABCE cross. -/
  have hCD_AB : SameSide C D AB := h₁.sameSideOf.sameSide hA_AB hB_AB
  have hE_AB : ¬ OnLine E AB := fun h =>
    hB_AF ((line_unique hAE hA_AB h hA hE) ▸ hB_AB)
  have hED_AB : SameSide E D AB := pasch2 hAED hA_AB hE_AB
  have hEC_AB : SameSide E C AB := same_side_trans (same_side_symm hED_AB) (same_side_symm hCD_AB)
  have hAEBC : AreParallel A E B C := AreParallel.of_parallel hAE h₁.2.1 hA hE hB hC hAF_BC
  obtain ⟨Y, hAYC, hBYE⟩ : ∃ Y : Point, Between A Y C ∧ Between B Y E := by
    rcases hAEBC.cross_or with hY | ⟨Y, hAYB, hEYC⟩
    · exact hY
    · exact absurd hEC_AB (pasch3 hEYC (on_line_of_between_ends hAYB hA_AB hB_AB))
  /- E and B lie on one side of DC, so the diameters EC, BD of EBCD cross. -/
  have hAB_DC : SameSide A B DC := h₁.1.sameSideOf.sameSide hC_DC hD_DC
  have hE_DC : ¬ OnLine E DC := fun h =>
    hC_AF (by rw [line_unique hED hE hD h hD_DC]; exact hC_DC)
  have hEA_DC : SameSide E A DC := pasch2 (between_symm hAED) hD_DC hE_DC
  have hEB_DC : SameSide E B DC := same_side_trans (same_side_symm hEA_DC) hAB_DC
  have hEDBC : AreParallel E D B C := AreParallel.of_parallel hED h₁.2.1 hE hD hB hC hAF_BC
  obtain ⟨X, hEXC, hBXD⟩ : ∃ X : Point, Between E X C ∧ Between B X D := by
    rcases hEDBC.cross_or with hX | ⟨X, hEXB, hDXC⟩
    · exact hX
    · exact absurd hEB_DC (pasch3 hEXB (on_line_of_between_ends hDXC hD_DC hC_DC))
  /- So D lies on C's side of EB, as F does, and D lies between E and F. -/
  have hEBC : Triangle E B C := Triangle.of_line hB hC h₁.2.1 (hAF_BC.not_onLine hE) |>.cab
  have hCD_EB : SameSideOf C D E B := SameSideOf.of_cross hEXC hBXD hEBC
  have hFray : OnRay F E D :=
    OnRay.of_sameSideOf (h₂.sameSideOf.symm.trans hCD_EB) ⟨AF, hE, hD, hF⟩
      (ne_of_len_eq hEF h₁.2.1).symm
  have hED_lt : ‖E D‖ < ‖E F‖ := by
    rw [hEF, ← hAD, len_symm A D, len_symm E D]
    exact len_lt_of_between (between_symm hAED)
  have hEDF : Between E D F := (OnRay.self hED).between_of_len_lt hFray hED_lt
  have hADF : Between A D F :=
    between_symm (between_of_between_right (between_symm hEDF) (between_symm hAED))
  /- AE is equal to DF; I.4 then makes the triangles EAB, FDC equal. -/
  have hAE_DF : ‖A E‖ = ‖D F‖ := by
    refine CommonNotion3 (c := ‖E D‖) (d := ‖E D‖) ?_ rfl
    rw [len_add_of_between hAED, add_comm, len_add_of_between hEDF, hAD, hEF]
  have hFDC : ∠ F D C = ∠ E A B := by
    rw [Prop29.exterior h₁.1.symm.swap_left h₁.2.sameSideOf.symm (between_symm hADF),
      angle_onRay_left (OnRay.of_between hAED) h₁.triangle.ne₁₂.symm]
  have hAEB : Triangle A E B := Triangle.of_line hA hE hAE hB_AF
  have hDFC : Triangle D F C := Triangle.of_line hD hF (ne_of_between (between_symm hEDF)).symm hC_AF
  have h4 : △ A E B = △ D F C := (Prop4 hAEB hDFC hAE_DF hAB hFDC.symm).2.1
  /- Proclus: the triangles added to the trapezium EBCD. -/
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

/-- The other case Euclid leaves out, which Proclus also supplies: when `E` is `D`,
that point lies between `A` and `F`. The triangles `ADB`, `DFC` are equal by I.34,
I.29 and I.4; adding the common triangle `DBC` to each gives the two
parallelograms. -/
theorem Prop35.same {A B C D F : Point} (h₁ : Parallelogram A B C D) (h₂ : Parallelogram D B C F)
    {AF : Line} (hA : OnLine A AF) (hD : OnLine D AF) (hF : OnLine F AF) :
    quadArea A B C D = quadArea D B C F := by
  obtain ⟨BC, hB, hC⟩ := Postulate1 B C h₁.2.1
  have hAF_BC : Parallel AF BC := (h₁.2.parallel hB hC hD hA).symm
  obtain ⟨hAD, hAB, -, -, -⟩ := Prop34 (A := A) (B := D) (C := B) (D := C) h₁
  obtain ⟨hDF, -, -, -, -⟩ := Prop34 (A := D) (B := F) (C := B) (D := C) h₂
  /- A and F lie on either side of DB, so D lies between them. -/
  obtain ⟨DB, hD_DB, hB_DB⟩ := Postulate1 D B h₂.1.1
  obtain ⟨X, hAXC, hBXD⟩ := h₁.cross
  have hX_DB : OnLine X DB := on_line_of_between_ends hBXD hB_DB hD_DB
  have hDA : D ≠ A := (ne_of_len_eq hAD h₁.2.1).symm
  have hA_DB : ¬ OnLine A DB := fun h =>
    hAF_BC.symm.not_onLine hB (by rw [line_unique hDA hD hA hD_DB h]; exact hB_DB)
  have hC_DB : ¬ OnLine C DB := fun h =>
    hA_DB (on_line_of_between (between_symm hAXC) h hX_DB)
  have hCF : SameSide C F DB := h₂.sameSideOf.sameSide hD_DB hB_DB
  have hAF : ¬ SameSide A F DB := fun hs =>
    pasch3 hAXC hX_DB (same_side_trans (same_side_symm hs) (same_side_symm hCF))
  have hADF : Between A D F := by
    obtain ⟨Y, hY_DB, hAYF⟩ := OppositeSides.exists_between
      ⟨hA_DB, not_on_line_of_same_side (same_side_symm hCF), hAF⟩
    have hY_AF : OnLine Y AF := on_line_of_between_ends hAYF hA hF
    have hAF_DB : AF ≠ DB := fun e => hAF_BC.symm.not_onLine hB (e ▸ hB_DB)
    have : Y = D := Classical.byContradiction fun hYD =>
      hAF_DB (line_unique hYD hY_AF hD hY_DB hD_DB)
    exact this ▸ hAYF
  have hFDC : ∠ F D C = ∠ D A B :=
    Prop29.exterior h₁.1.symm.swap_left h₁.2.sameSideOf.symm (between_symm hADF)
  have hB_AF : ¬ OnLine B AF := hAF_BC.symm.not_onLine hB
  have hC_AF : ¬ OnLine C AF := hAF_BC.symm.not_onLine hC
  have h4 : △ A D B = △ D F C :=
    (Prop4 (Triangle.of_line hA hD hDA.symm hB_AF) (Triangle.of_line hD hF
      (ne_of_between (between_symm hADF)).symm hC_AF) (hAD.trans hDF.symm) hAB hFDC.symm).2.1
  rw [← h₁.quadArea_rotate]
  unfold quadArea
  rw [area_cab B D A, area_acb A B D, h4, area_cab B C D, area_acb D C F]

/-- Parallelograms which are on the same base and in the same parallels are equal to one another. -/
theorem Prop35 {A B C D E F : Point} (h₁ : Parallelogram A B C D) (h₂ : Parallelogram E B C F)
    (hAF : ∃ L : Line, OnLine A L ∧ OnLine D L ∧ OnLine E L ∧ OnLine F L) :
    quadArea A B C D = quadArea E B C F := by
  -- Let ABCD, EBCF be parallelograms on the same base BC and in the same parallels AF, BC;
  obtain ⟨AF, hA, hD, hE, hF⟩ := hAF
  obtain ⟨BC, hB, hC⟩ := Postulate1 B C h₁.2.1
  -- I say that ABCD is equal to the parallelogram EBCF.
  /- Euclid takes the case where AD and EF have no point in common, with D between
     A and E. We give his argument in his letters, then cover the other orders. -/
  have euclid : ∀ {A D E F : Point}, Parallelogram A B C D → Parallelogram E B C F →
      OnLine A AF → OnLine D AF → OnLine F AF → Between A D E →
      quadArea A B C D = quadArea E B C F := by
    intro A D E F h₁ h₂ hA hD hF hADE
    have hE : OnLine E AF := on_line_of_between hADE hA hD
    -- For, since ABCD is a parallelogram,
    have hAF_BC : Parallel AF BC := (h₁.2.parallel hB hC hD hA).symm
    -- AD is equal to BC. [I. 34]
    have hAD : ‖A D‖ = ‖B C‖ := (Prop34 (A := A) (B := D) (C := B) (D := C) h₁).1
    -- For the same reason also
    -- EF is equal to BC,
    have hEF : ‖E F‖ = ‖B C‖ := (Prop34 (A := E) (B := F) (C := B) (D := C) h₂).1
    -- so that AD is also equal to EF; [C.N. 1]
    have hAD_EF : ‖A D‖ = ‖E F‖ := CommonNotion1 hAD hEF
    -- and DE is common;
    /- G lies between E and B and between D and C; E lies between D and F.
       These are the orders Euclid reads from his figure. -/
    obtain ⟨G, hEGB, hDGC, hDEF⟩ := Prop35.figure h₁ h₂ hA hD hF hADE
    -- therefore the whole AE is equal to the whole DF. [C.N. 2]
    have hAE_DF : ‖A E‖ = ‖D F‖ := by
      have := CommonNotion2 hAD_EF (rfl : ‖D E‖ = ‖D E‖)
      rw [len_add_of_between hADE, add_comm, len_add_of_between hDEF] at this
      exact this
    -- But AB is also equal to DC; [I. 34]
    have hAB : ‖A B‖ = ‖D C‖ := (Prop34 (A := A) (B := D) (C := B) (D := C) h₁).2.1
    -- therefore the two sides EA, AB are equal to the two sides FD, DC respectively,
    have hB_AF : ¬ OnLine B AF := hAF_BC.symm.not_onLine hB
    have hC_AF : ¬ OnLine C AF := hAF_BC.symm.not_onLine hC
    have hAEB : Triangle A E B := Triangle.of_line hA hE (ne_of_between_ends hADE) hB_AF
    have hDFC : Triangle D F C := Triangle.of_line hD hF (ne_of_between_ends hDEF) hC_AF
    -- and the angle FDC is equal to the angle EAB, the exterior to the interior; [I. 29]
    have hADF : Between A D F := between_of_between_right hADE hDEF
    have hFDC : ∠ F D C = ∠ E A B := by
      rw [Prop29.exterior h₁.1.symm.swap_left h₁.2.sameSideOf.symm (between_symm hADF),
        angle_onRay_left (OnRay.of_beyond hADE) h₁.triangle.ne₁₂.symm]
    -- therefore the base EB is equal to the base FC,
    have h4 := Prop4 hAEB hDFC hAE_DF hAB hFDC.symm
    have hEB_FC : ‖E B‖ = ‖F C‖ := h4.1
    -- and the triangle EAB will be equal to the triangle FDC. [I. 4]
    have htri : △ A E B = △ D F C := h4.2.1
    -- Let DGE be subtracted from each;
    /- ABGD is named from B, so that its diameter is BD. Each subtraction is
       expressed by cutting the larger triangle into the trapezium and DGE. -/
    have e₁ : △ A E B = quadArea B G D A + △ D G E := by
      unfold quadArea
      rw [area_cab A E B, ← area_cut (A := B) hADE, area_bca B D E, ← area_cut (A := D) hEGB,
        area_cba B G D, area_acb B D A, area_acb D G E]
      ac_rfl
    have e₂ : △ D F C = quadArea E G C F + △ D G E := by
      unfold quadArea
      rw [area_cab D F C, ← area_cut (A := C) hDEF, area_cba C D E, ← area_cut (A := E) hDGC,
        area_bac E C F, area_cab D G E]
      ac_rfl
    -- therefore the trapezium ABGD which remains is equal to the trapezium EGCF which
    -- remains. [C.N. 3]
    have trap : quadArea B G D A = quadArea E G C F :=
      CommonNotion3 (e₁.symm.trans (htri.trans e₂)) rfl
    -- Let the triangle GBC be added to each;
    have hsum := CommonNotion2 trap (rfl : △ G B C = △ G B C)
    -- therefore the whole parallelogram ABCD is equal to the whole parallelogram EBCF. [C.N. 2]
    have hL : quadArea A B C D = quadArea B G D A + △ G B C := by
      rw [← h₁.quadArea_rotate]
      unfold quadArea
      rw [area_acb B C D, ← area_cut (A := B) hDGC, area_acb B G D, area_bac G B C]
      ac_rfl
    have hR : quadArea E B C F = quadArea E G C F + △ G B C := by
      unfold quadArea
      rw [area_cab E B C, ← area_cut (A := C) hEGB, area_cab E G C, area_cab G B C]
      ac_rfl
    rw [hL, hR, hsum]
  /- E may also fall between A and D, or at either end. The helpers add equal
     triangles to the common part, as Proclus does in the cases Heath reports.
     When E is A, equal lengths on the same ray make F equal to D. -/
  have oneway : ∀ {A D E F : Point}, Parallelogram A B C D → Parallelogram E B C F →
      OnLine A AF → OnLine D AF → OnLine E AF → OnLine F AF → (E = A ∨ SameSideOf C E A B) →
      quadArea A B C D = quadArea E B C F := by
    intro A D E F h₁ h₂ hA hD hE hF hdir
    obtain ⟨hAD, -, -, -, -⟩ := Prop34 (A := A) (B := D) (C := B) (D := C) h₁
    obtain ⟨hEF, -, -, -, -⟩ := Prop34 (A := E) (B := F) (C := B) (D := C) h₂
    rcases hdir with rfl | hCE
    · /- `E` is `A`: then `F` is `D`. -/
      have hFray : OnRay F E D :=
        OnRay.of_sameSideOf (h₂.sameSideOf.symm.trans h₁.sameSideOf) ⟨AF, hE, hD, hF⟩
          (h₂.sameSideOf.symm.triangle.ne₁₃.symm)
      rw [hFray.eq_of_len_eq (hEF.trans hAD.symm)]
    · have hEA : E ≠ A := hCE.symm.triangle.ne₁₃.symm
      have hEray : OnRay E A D :=
        OnRay.of_sameSideOf (hCE.symm.trans h₁.sameSideOf) ⟨AF, hA, hD, hE⟩ hEA
      by_cases hED : E = D
      · subst hED
        exact Prop35.same h₁ h₂ hA hE hF
      · rcases between_cases hEray.1 (Ne.symm hED) hEA.symm hA hD hE with h | h | h
        · exact euclid h₁ h₂ hA hD hF h
        · exact absurd (between_symm h) hEray.2.2.2
        · exact Prop35.between h₁ h₂ hA hD hE hF h
  /- Exchanging the parallelograms covers the other direction along AF. -/
  have harea : quadArea A B C D = quadArea E B C F := by
    by_cases hEA : E = A
    · exact oneway h₁ h₂ hA hD hE hF (Or.inl hEA)
    · have hAF_BC : Parallel AF BC := (h₁.2.parallel hB hC hD hA).symm
      rcases (AreParallel.of_parallel (Ne.symm hEA) h₁.2.1 hA hE hB hC hAF_BC).sameSideOf_or with h | h
      · exact oneway h₁ h₂ hA hD hE hF (Or.inr h)
      · exact (oneway h₂ h₁ hE hF hA hD (Or.inr h)).symm
  -- Therefore etc.
  exact harea
  -- Q. E. D.

end Elements.BookI
