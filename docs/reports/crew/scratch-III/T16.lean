import Elements
open Elements Elements.Tacit

namespace Scratch

/-- In a triangle right-angled at `A`, the side `DP` opposite the right angle is greater
than `DA` [I. 17, I. 19]. -/
theorem right_hyp {A D P : Point} (h : Triangle D A P) (hA : ∠ D A P = ∟) : ‖D A‖ < ‖D P‖ := by
  have h17 := (BookI.Prop17 h).1
  rw [hA] at h17
  have hP : ∠ A P D < ∟ := Magnitude.lt_of_add_lt_add_left h17
  exact BookI.Prop19 h (hA ▸ hP)

/-- A point of a straight line `AE` other than `A`, where `AE` is at right angles to the
radius `DA`, is outside the circle. -/
theorem off_tangent {A D E P : Point} {ABC : Circle} (hD : Centre D ABC) (hA : OnCircle A ABC)
    (hE : ¬ Collinear D A E) (hDAE : ∠ D A E = ∟) (hP : Collinear A E P) (hPA : P ≠ A) :
    OutsideCircle P ABC := by
  have hDAE' : Triangle D A E := hE
  obtain ⟨L, hA_L, hE_L, hP_L⟩ := hP
  have hD_L : ¬ OnLine D L := hDAE'.bca.off_line hA_L hE_L |> fun h => by
    intro hD; exact hDAE' ⟨L, hD, hA_L, hE_L⟩
  have hDAP : Triangle D A P := Triangle.of_line hA_L hP_L hPA.symm hD_L |>.bca |>.bca
  /- The angle `DAP` is right: `P` is on the ray `AE`, or on the other side of `A`. -/
  have hright : ∠ D A P = ∟ := by
    by_cases hb : Between P A E
    · have hEAD : ∠ E A D = ∟ := by
        rw [angle_symm hDAE'.ne₂₃.symm hDAE'.ne₁₂]; exact hDAE
      rw [← adjacent_eq_of_right hE_L hP_L (between_symm hb) hD_L hEAD, hEAD]
    · rw [angle_onRay_right ⟨hDAE'.ne₂₃, hPA, ⟨L, hA_L, hE_L, hP_L⟩, hb⟩ hDAE'.ne₁₂]
      exact hDAE
  have := right_hyp hDAP hright
  rw [Definition15 hD hA hA] at this
  exact outside_of_len_gt hD hA this

/-- At a point `A`, only one straight line is at right angles to `AD`: if `AE` and `AF`
both are, `F` is on the straight line `AE` (one ray for one angle on each side). -/
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

/-- **III.16**: the straight line at right angles to the diameter at its end falls
outside, and every other straight line through `A` falls within. -/
theorem T16 {A B D E : Point} {ABC : Circle} (hD : Centre D ABC) (hA : OnCircle A ABC)
    (hADB : Between A D B) (hE : ¬ Collinear A B E) (hBAE : ∠ B A E = ∟) :
    (∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC) ∧
    (∀ F : Point, ¬ Collinear A E F → ∃ G : Point, Collinear A F G ∧ InsideCircle G ABC) := by
  have hABE : Triangle A B E := hE
  have hDAE : ∠ D A E = ∟ := by
    rw [angle_onRay_left (OnRay.of_between hADB) hABE.ne₁₃.symm]; exact hBAE
  have hDAE' : Triangle D A E := by
    obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hABE.ne₁₂
    have hD_L : OnLine D L := on_line_of_between_ends hADB hA_L hB_L
    exact (Triangle.of_line hA_L hD_L (ne_of_between hADB) (hABE.off_line hA_L hB_L)).bac
  refine ⟨fun P hP hPA => off_tangent hD hA hDAE' hDAE hP hPA, fun F hF => ?_⟩
  have hAF : A ≠ F := by
    rintro rfl
    obtain ⟨L, h1, h2⟩ := Postulate1 A E hDAE'.ne₂₃
    exact hF ⟨L, h1, h2, h1⟩
  by_cases hDF : Collinear A F D
  · exact ⟨D, hDF, centre_inside hD⟩
  obtain ⟨G, hG, hDG⟩ := BookI.Prop12 hAF hDF
  have hDAF : Triangle D A F := fun ⟨L, h1, h2, h3⟩ => hDF ⟨L, h2, h3, h1⟩
  have hGA : G ≠ A := by
    rintro rfl
    obtain ⟨L, h1, h2⟩ := Postulate1 G F hAF
    exact hF (one_perp hDAE' hDAF hDAE (hDG F ⟨L, h1, h2, h2⟩ hAF.symm))
  obtain ⟨L, hA_L, hF_L, hG_L⟩ := hG
  have hD_L : ¬ OnLine D L := fun hD => hDF ⟨L, hA_L, hF_L, hD⟩
  have hDGA : Triangle D G A := (Triangle.of_line hG_L hA_L hGA hD_L).bca.bca
  have := right_hyp hDGA (hDG A ⟨L, hA_L, hF_L, hA_L⟩ hGA.symm)
  exact ⟨G, ⟨L, hA_L, hF_L, hG_L⟩, inside_of_len_lt hD hA this⟩

/-- The Porism to III.16. -/
theorem T16por {A D E : Point} {ABC : Circle} (hD : Centre D ABC) (hA : OnCircle A ABC)
    (hE : ¬ Collinear D A E) (hDAE : ∠ D A E = ∟) : Touches A E ABC := by
  have hDAE' : Triangle D A E := hE
  refine ⟨hDAE'.ne₂₃, fun L hA_L hE_L => ⟨⟨A, hA_L, hA⟩, ?_⟩⟩
  rintro ⟨X, Y, hXY, hX_L, hX, hY_L, hY⟩
  have hcol : ∀ {P : Point}, OnLine P L → Collinear A E P := fun h => ⟨L, hA_L, hE_L, h⟩
  by_cases hXA : X = A
  · subst hXA
    exact (off_tangent hD hA hE hDAE (hcol hY_L) (Ne.symm hXY)).2 hY
  · exact (off_tangent hD hA hE hDAE (hcol hX_L) hXA).2 hX

/-- **III.18**. -/
theorem T18 {C D E F : Point} {ABC : Circle} (hF : Centre F ABC) (hC : OnCircle C ABC)
    (hDE : Touches D E ABC) (hCDE : Collinear D E C) :
    ∀ P : Point, Collinear D E P → P ≠ C → ∠ F C P = ∟ := by
  have hF_DE : ¬ Collinear D E F := fun h => hDE.not_inside h (centre_inside hF)
  obtain ⟨G, hG, hFG⟩ := BookI.Prop12 hDE.1 hF_DE
  by_cases hGC : G = C
  · subst hGC; exact hFG
  · /- Otherwise `FG` is less than `FC`, and `G`, on the tangent, falls within. -/
    exfalso
    obtain ⟨L, hD_L, hE_L, hG_L⟩ := hG
    have hC_L : OnLine C L := by
      obtain ⟨M, h1, h2, h3⟩ := hCDE
      exact (line_unique hDE.1 h1 h2 hD_L hE_L) ▸ h3
    have hF_L : ¬ OnLine F L := fun h => hF_DE ⟨L, hD_L, hE_L, h⟩
    have hFGC : Triangle F G C := (Triangle.of_line hG_L hC_L hGC hF_L).bca.bca
    have := right_hyp hFGC (hFG C ⟨L, hD_L, hE_L, hC_L⟩ (Ne.symm hGC))
    exact hDE.not_inside ⟨L, hD_L, hE_L, hG_L⟩ (inside_of_len_lt hF hC this)

end Scratch
