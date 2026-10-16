import Elements
open Elements Elements.Tacit

namespace Scratch

/-- **III.21** in full. Euclid's case, the segment greater than a semicircle (the centre
`F` on `A`'s side of `BD`), is III.20 twice. Otherwise Simson's: `AF` drawn through to
`C`, the point of the circle opposite `A`, falls between `B` and `D`, and the segments
on `BC` and `CD` both hold the centre, so Euclid's case applies to each. -/
theorem T21 {A B D E : Point} {ABCD : Circle} (hABCD : ∃ F : Point, Centre F ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hD : OnCircle D ABCD)
    (hE : OnCircle E ABCD) (hAE : SameSideOf A E B D) :
    ∠ B A D = ∠ B E D := by
  obtain ⟨F, hF⟩ := hABCD
  /- Euclid's case: the centre on the side of the angles. [III. 20] -/
  have greater : ∀ {P Q X Y : Point}, OnCircle P ABCD → OnCircle Q ABCD → OnCircle X ABCD →
      OnCircle Y ABCD → SameSideOf F X P Q → SameSideOf F Y P Q → ∠ P X Q = ∠ P Y Q := by
    intro P Q X Y hP hQ hX hY hFX hFY
    exact Magnitude.eq_of_add_self_eq
      ((BookIII.Prop20 hF hX hP hQ hFX).symm.trans (BookIII.Prop20 hF hY hP hQ hFY))
  have hBD : B ≠ D := hAE.1
  obtain ⟨L, hB_L, hD_L⟩ := Postulate1 B D hBD
  have hA_L : ¬ OnLine A L := hAE.triangle.off_line hB_L hD_L
  by_cases hFA : SameSide F A L
  · have hFA' : SameSideOf F A B D := SameSideOf.of_line hBD hB_L hD_L hFA
    exact greater hB hD hA hE hFA' (hFA'.trans hAE)
  /- Simson's case. `C`, the point of the circle opposite `A`. -/
  have hAF : A ≠ F := ne_of_centre_of_on hF hA
  obtain ⟨N, hA_N, hF_N⟩ := Postulate1 A F hAF
  obtain ⟨C, hC, hC_N, hCFA⟩ := line_circle_beyond (centre_inside hF) hF_N hA_N hAF
  /- `C` is on the other side of `BD` from `A`. -/
  have hAC_L : OppositeSides A C L := by
    by_cases hF_L : OnLine F L
    · have hC_L : ¬ OnLine C L := fun hC_L =>
        hA_L ((line_unique (ne_of_between hCFA) hC_N hF_N hC_L hF_L) ▸ hA_N)
      exact ⟨hA_L, hC_L, pasch3 (between_symm hCFA) hF_L⟩
    · obtain ⟨X, hX_L, hAXF⟩ := (show OppositeSides A F L from
        ⟨hA_L, hF_L, fun h => hFA (same_side_symm h)⟩).exists_between
      have hXFC : Between X F C := between_inner hAXF (between_symm hCFA)
      have hFC : SameSide F C L := pasch2 hXFC hX_L hF_L
      exact ⟨hA_L, not_on_line_of_same_side (same_side_symm hFC),
        fun h => hFA (same_side_trans (same_side_symm hFC) (same_side_symm h))⟩
  have hEC_L : OppositeSides E C L := by
    have hAE_L : SameSide A E L := hAE.sameSide hB_L hD_L
    exact ⟨not_on_line_of_same_side (same_side_symm hAE_L), hAC_L.2.1,
      fun h => hAC_L.2.2 (same_side_trans (same_side_symm hAE_L) h)⟩
  /- `AC` and `EC` cross `BD` within the circle, between `B` and `D`. -/
  obtain ⟨Y, hY_L, hAYC⟩ := hAC_L.exists_between
  obtain ⟨Z, hZ_L, hEZC⟩ := hEC_L.exists_between
  have hBYD : Between B Y D :=
    between_of_inside_chord hY_L hB_L hD_L (inside_of_between (Or.inr hA) (Or.inr hC) hAYC) hB hD hBD
  have hBZD : Between B Z D :=
    between_of_inside_chord hZ_L hB_L hD_L (inside_of_between (Or.inr hE) (Or.inr hC) hEZC) hB hD hBD
  have hBDA : Triangle B D A := Triangle.of_line hB_L hD_L hBD hA_L
  have hBDE : Triangle B D E := Triangle.of_line hB_L hD_L hBD hEC_L.1
  have hBDC : Triangle B D C := Triangle.of_line hB_L hD_L hBD hAC_L.2.1
  /- The angle `BAD` is the angles `BAC`, `CAD`; and `BED` is `BEC`, `CED`. -/
  have hsplitA : ∠ B A D = ∠ B A C + ∠ C A D := by
    rw [angle_add_of_between hBDA hBYD, angle_onRay_right (OnRay.of_between hAYC) hBDA.ne₁₃,
      angle_onRay_left (OnRay.of_between hAYC) hBDA.ne₂₃]
  have hsplitE : ∠ B E D = ∠ B E C + ∠ C E D := by
    rw [angle_add_of_between hBDE hBZD, angle_onRay_right (OnRay.of_between hEZC) hBDE.ne₁₃,
      angle_onRay_left (OnRay.of_between hEZC) hBDE.ne₂₃]
  /- `A` and `E` are on one side of `BC`, as `D` is, and on one side of `CD`, as `B` is. -/
  have hBC : B ≠ C := hBDC.ne₁₃
  have hDC : D ≠ C := hBDC.ne₂₃
  have hA_BC : SameSideOf D A B C :=
    SameSideOf.of_cross hBYD (between_symm hAYC) (hBDC.acb)
  have hE_BC : SameSideOf D E B C :=
    SameSideOf.of_cross hBZD (between_symm hEZC) (hBDC.acb)
  have hA_DC : SameSideOf B A D C :=
    SameSideOf.of_cross (between_symm hBYD) (between_symm hAYC) (hBDC.bac.acb)
  have hE_DC : SameSideOf B E D C :=
    SameSideOf.of_cross (between_symm hBZD) (between_symm hEZC) (hBDC.bac.acb)
  /- `F`, between `A` and `C`, is on `A`'s side of each. -/
  have hF_side : ∀ {P : Point}, P ≠ C → Triangle P C A → SameSideOf F A P C := by
    intro P hPC hPCA
    obtain ⟨K, hP_K, hC_K⟩ := Postulate1 P C hPC
    have hA_K : ¬ OnLine A K := hPCA.off_line hP_K hC_K
    have hF_K : ¬ OnLine F K := fun hF_K =>
      hA_K ((line_unique (ne_of_between hCFA) hC_N hF_N hC_K hF_K) ▸ hA_N)
    exact SameSideOf.of_line hPC hP_K hC_K (pasch2 hCFA hC_K hF_K)
  have hFA_BC : SameSideOf F A B C := hF_side hBC hA_BC.symm.triangle
  have hFA_DC : SameSideOf F A D C := hF_side hDC hA_DC.symm.triangle
  have h₁ : ∠ B A C = ∠ B E C :=
    greater hB hC hA hE hFA_BC (hFA_BC.trans (hA_BC.symm.trans hE_BC))
  have h₂ : ∠ D A C = ∠ D E C :=
    greater hD hC hA hE hFA_DC (hFA_DC.trans (hA_DC.symm.trans hE_DC))
  have hCA : C ≠ A := by
    intro e; subst e; exact hAC_L.2.2 (same_side_refl hA_L)
  have hCE : C ≠ E := by
    intro e; subst e; exact hEC_L.2.2 (same_side_refl hEC_L.1)
  rw [hsplitA, hsplitE, h₁, angle_symm hCA hBDA.ne₂₃, h₂, angle_symm hBDE.ne₂₃ hCE]

end Scratch
