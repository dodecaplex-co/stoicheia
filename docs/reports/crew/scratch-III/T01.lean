import Elements
open Elements Elements.Tacit

namespace Scratch

/-- A straight line has one middle point. -/
theorem mid_unique {A B D G : Point} (hADB : Between A D B) (hAD : ‖A D‖ = ‖D B‖)
    (hAGB : Between A G B) (hAG : ‖A G‖ = ‖G B‖) : G = D := by
  have e₁ := len_add_of_between hAGB
  have e₂ := len_add_of_between hADB
  rw [← hAG] at e₁
  rw [← hAD] at e₂
  have hlen : ‖A G‖ = ‖A D‖ := Magnitude.eq_of_add_self_eq (e₁.trans e₂.symm)
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B (ne_of_between_ends hADB)
  have hray : OnRay G A D := ⟨ne_of_between hADB, (ne_of_between hAGB).symm,
    ⟨L, hA_L, on_line_of_between_ends hADB hA_L hB_L, on_line_of_between_ends hAGB hA_L hB_L⟩,
    fun hb => not_between_of_between hAGB (between_of_between_right hb hADB)⟩
  exact OnRay.eq_of_len_eq hray hlen

/-- At a point `A`, only one straight line is at right angles to `AD`. -/
theorem one_perp {A D E F : Point} (hE : Triangle D A E) (hF : Triangle D A F)
    (hDAE : ∠ D A E = ∟) (hDAF : ∠ D A F = ∟) : Collinear A E F := by
  have hAD : A ≠ D := hE.ne₁₂.symm
  obtain ⟨L, hA_L, hD_L⟩ := Postulate1 A D hAD
  have hE_L : ¬ OnLine E L := hE.bac.off_line hA_L hD_L
  have hF_L : ¬ OnLine F L := hF.bac.off_line hA_L hD_L
  by_cases hs : SameSide F E L
  · exact (onRay_of_angle_eq (SameSideOf.of_line hAD hA_L hD_L hs) (hDAF.trans hDAE.symm)).2.2.1
  · obtain ⟨M, hE_M, hA_M⟩ := Postulate1 E A hE.ne₂₃.symm
    obtain ⟨E', hE'_M, hEAE', -⟩ := Postulate2 hE_M hA_M hE.ne₂₃.symm []
    have hD_M : ¬ OnLine D M := fun hD => hE ⟨M, hD, hA_M, hE_M⟩
    have hEAD : ∠ E A D = ∟ := by rw [angle_symm hE.ne₂₃.symm hE.ne₁₂]; exact hDAE
    have hDAE' : ∠ D A E' = ∟ := (adjacent_eq_of_right hE_M hE'_M hEAE' hD_M hEAD).symm.trans hEAD
    have hE'_L : ¬ OnLine E' L := fun h => hE_L (on_line_of_between (between_symm hEAE') h hA_L)
    have hFE' : SameSide F E' L := same_side_of_opposite_sides
      ⟨hE_L, hF_L, fun h => hs (same_side_symm h)⟩ ⟨hE_L, hE'_L, pasch3 hEAE' hA_L⟩
    obtain ⟨-, -, ⟨N, hA_N, hE'_N, hF_N⟩, -⟩ :=
      onRay_of_angle_eq (SameSideOf.of_line hAD hA_L hD_L hFE') (hDAF.trans hDAE'.symm)
    have hNM : N = M := line_unique (ne_of_between (between_symm hEAE')).symm hA_N hE'_N hA_M hE'_M
    subst hNM
    exact ⟨N, hA_N, hE_M, hF_N⟩

/-- **The Porism to III.1**: Euclid's reductio, said of the centre `G`. [I. 8] -/
theorem T01por {A B C D G : Point} {ABC : Circle} (hG : Centre G ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hADB : Between A D B) (hAD : ‖A D‖ = ‖D B‖)
    (hC : ¬ Collinear A B C) (hADC : ∠ A D C = ∟) : Collinear D C G := by
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B (ne_of_between_ends hADB)
  have hD_L := on_line_of_between_ends hADB hA_L hB_L
  have hC_L : ¬ OnLine C L := (show Triangle A B C from hC).off_line hA_L hB_L
  by_cases hGD : G = D
  · subst hGD
    obtain ⟨N, h1, h2⟩ := Postulate1 G C (fun e => hC_L (e ▸ hD_L))
    exact ⟨N, h1, h2, h1⟩
  /- `G` is off `AB`: else it would be the middle point `D`. -/
  have hG_L : ¬ OnLine G L := by
    intro hG_L
    have hAGB := between_of_inside_chord hG_L hA_L hB_L (centre_inside hG) hA hB
      (ne_of_between_ends hADB)
    exact hGD (mid_unique hADB hAD hAGB (by rw [len_symm A G, Definition15 hG hA hB]))
  have hDA : D ≠ A := (ne_of_between hADB).symm
  have hDAG : Triangle D A G := Triangle.of_line hD_L hA_L hDA hG_L
  have hDBG : Triangle D B G :=
    Triangle.of_line hD_L hB_L (ne_of_between (between_symm hADB)).symm hG_L
  /- The angles `ADG`, `GDB` are equal [I. 8], and so right [I. Def. 10]. -/
  have h8 : ∠ A D G = ∠ B D G := BookI.Prop8 hDAG hDBG (by rw [len_symm D A, hAD]) rfl
    (by rw [len_symm A G, len_symm B G, Definition15 hG hA hB])
  have hright : ∠ A D G = ∟ := Postulate4
    ⟨B, hADB, hDAG.bac, h8.trans (angle_symm hDBG.ne₁₂.symm hDBG.ne₁₃.symm)⟩
  exact one_perp (show Triangle A D C from fun ⟨N, h1, h2, h3⟩ => hC_L (by
      have := line_unique hDA.symm h1 h2 hA_L hD_L; exact this ▸ h3)) hDAG.bac hADC hright

/-- **III.1**: Euclid's construction finds the centre. -/
theorem T01 {A B : Point} {ABC : Circle} (hABC : ∃ G : Point, Centre G ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hAB : A ≠ B) :
    ∃ F C D E : Point, Centre F ABC ∧ Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧
      OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ Between C F E ∧ ‖C F‖ = ‖F E‖ := by
  obtain ⟨G, hG⟩ := hABC
  obtain ⟨D, hADB, hAD⟩ := BookI.Prop10 hAB
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hD_L := on_line_of_between_ends hADB hA_L hB_L
  obtain ⟨Q, hQ, -⟩ := exists_off_line hAB []
  obtain ⟨X, hXQ, hX⟩ := BookI.Prop11 hAB ⟨L, hA_L, hB_L, hD_L⟩ hQ
  have hD_in : InsideCircle D ABC := inside_of_between (Or.inr hA) (Or.inr hB) hADB
  have hX_L : ¬ OnLine X L := hXQ.triangle.off_line hA_L hB_L
  have hDX : D ≠ X := fun e => hX_L (e ▸ hD_L)
  obtain ⟨N, hD_N, hX_N⟩ := Postulate1 D X hDX
  /- `DC` drawn through to `E`. -/
  obtain ⟨E, hE, hE_N, hEDX⟩ := line_circle_beyond hD_in hD_N hX_N hDX.symm
  obtain ⟨C, hC, hC_N, hCDE⟩ := line_circle_beyond hD_in hD_N hE_N (ne_of_between hEDX)
  have hCray : OnRay C D X := OnRay.of_between_between hEDX (between_symm hCDE)
  have hADC : ∠ A D C = ∟ := by
    rw [angle_onRay_right hCray (ne_of_between hADB)]
    exact hX A ⟨L, hA_L, hB_L, hA_L⟩ (ne_of_between hADB)
  have hCD : C ≠ D := ne_of_between hCDE
  have hC_L : ¬ OnLine C L := fun h => hX_L ((line_unique hCD hC_N hD_N h hD_L) ▸ hX_N)
  /- `CE` bisected at `F`; the centre `G` is on `CE`, and is its middle point. -/
  obtain ⟨F, hCFE, hCF⟩ := BookI.Prop10 (ne_of_between_ends hCDE)
  obtain ⟨M, hD_M, hC_M, hG_M⟩ :=
    T01por hG hA hB hADB hAD (fun ⟨K, h1, h2, h3⟩ => hC_L (by
      have := line_unique hAB h1 h2 hA_L hB_L; exact this ▸ h3)) hADC
  have hMN : M = N := line_unique hCD hC_M hD_M hC_N hD_N
  subst hMN
  have hCGE := between_of_inside_chord hG_M hC_M hE_N (centre_inside hG) hC hE
    (ne_of_between_ends hCDE)
  have hGF : G = F := mid_unique hCFE hCF hCGE (by
    rw [len_symm C G, Definition15 hG hC hE])
  subst hGF
  exact ⟨G, C, D, E, hG, hADB, hAD, hC, hE, hCDE, hADC, hCFE, hCF⟩

end Scratch
