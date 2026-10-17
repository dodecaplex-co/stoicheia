import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Prop20

/-!
# Book III, Proposition 21

Euclid's text, in Heath's translation: [`heath/III/21.md`](../../heath/III/21.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- In a circle the angles in the same segment are equal to one another. -/
theorem Prop21 {A B D E : Point} {ABCD : Circle} (hABCD : ∃ F : Point, Centre F ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hD : OnCircle D ABCD)
    (hE : OnCircle E ABCD) (hAE : SameSideOf A E B D) :
    ∠ B A D = ∠ B E D := by
  -- Let ABCD be a circle, and let the angles BAD, BED be angles in the same segment BAED;
  -- I say that the angles BAD, BED are equal to one another.
  -- For let the centre of the circle ABCD be taken, and let it be F; let BF, FD be joined.
  obtain ⟨F, hF⟩ := hABCD
  have greater : ∀ {A B D E : Point}, OnCircle A ABCD → OnCircle B ABCD → OnCircle D ABCD →
      OnCircle E ABCD → SameSideOf F A B D → SameSideOf A E B D → ∠ B A D = ∠ B E D := by
    intro A B D E hA hB hD hE hFA hAE
    -- Now, since the angle BFD is at the centre,
    -- and the angle BAD at the circumference,
    -- and they have the same circumference BCD as base,
    -- therefore the angle BFD is double of the angle BAD. [III. 20]
    have h₁ : ∠ B F D = ∠ B A D + ∠ B A D := Prop20 hF hA hB hD hFA
    -- For the same reason
    -- the angle BFD is also double of the angle BED;
    have h₂ : ∠ B F D = ∠ B E D + ∠ B E D := Prop20 hF hE hB hD (hFA.trans hAE)
    -- therefore the angle BAD is equal to the angle BED.
    exact Magnitude.eq_of_add_self_eq (h₁.symm.trans h₂)
  -- Therefore etc.
  have hBD : B ≠ D := hAE.1
  obtain ⟨L, hB_L, hD_L⟩ := Postulate1 B D hBD
  have hA_L : ¬ OnLine A L := hAE.triangle.off_line hB_L hD_L
  by_cases hFA : SameSide F A L
  · exact greater hA hB hD hE (SameSideOf.of_line hBD hB_L hD_L hFA) hAE
  /- Robert Simson's completion (Heath, vol. 2, pp. 49–50), for a segment equal
     to or less than a semicircle. Produce AF to C on the circle and join CE;
     the segments on BC and CD contain the centre, so Euclid's case applies to
     each. -/
  have hAF : A ≠ F := ne_of_centre_of_on hF hA
  obtain ⟨N, hA_N, hF_N⟩ := Postulate1 A F hAF
  obtain ⟨C, hC, hC_N, hCFA⟩ := line_circle_beyond (centre_inside hF) hF_N hA_N hAF
  /- C is on the other side of BD from A, whether F is on BD or beyond it. -/
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
  /- AC and EC cross BD within the circle, hence between B and D. The
     intersections Y and Z have no letters in Heath. -/
  obtain ⟨Y, hY_L, hAYC⟩ := hAC_L.exists_between
  obtain ⟨Z, hZ_L, hEZC⟩ := hEC_L.exists_between
  have hBYD : Between B Y D :=
    between_of_inside_chord hY_L hB_L hD_L
      (inside_of_between (Or.inr hA) (Or.inr hC) hAYC) hB hD hBD
  have hBZD : Between B Z D :=
    between_of_inside_chord hZ_L hB_L hD_L
      (inside_of_between (Or.inr hE) (Or.inr hC) hEZC) hB hD hBD
  have hBDA : Triangle B D A := Triangle.of_line hB_L hD_L hBD hA_L
  have hBDE : Triangle B D E := Triangle.of_line hB_L hD_L hBD hEC_L.1
  have hBDC : Triangle B D C := Triangle.of_line hB_L hD_L hBD hAC_L.2.1
  /- AC and EC divide the two angles into the pairs BAC, CAD and BEC, CED. -/
  have hsplitA : ∠ B A D = ∠ B A C + ∠ C A D := by
    rw [angle_add_of_between hBDA hBYD, angle_onRay_right (OnRay.of_between hAYC) hBDA.ne₁₃,
      angle_onRay_left (OnRay.of_between hAYC) hBDA.ne₂₃]
  have hsplitE : ∠ B E D = ∠ B E C + ∠ C E D := by
    rw [angle_add_of_between hBDE hBZD, angle_onRay_right (OnRay.of_between hEZC) hBDE.ne₁₃,
      angle_onRay_left (OnRay.of_between hEZC) hBDE.ne₂₃]
  /- A and E lie on one side of BC, as D does, and on one side of DC, as B does. -/
  have hBC : B ≠ C := hBDC.ne₁₃
  have hDC : D ≠ C := hBDC.ne₂₃
  have hA_BC : SameSideOf D A B C :=
    SameSideOf.of_cross hBYD (between_symm hAYC) hBDC.acb
  have hE_BC : SameSideOf D E B C :=
    SameSideOf.of_cross hBZD (between_symm hEZC) hBDC.acb
  have hA_DC : SameSideOf B A D C :=
    SameSideOf.of_cross (between_symm hBYD) (between_symm hAYC) hBDC.bac.acb
  have hE_DC : SameSideOf B E D C :=
    SameSideOf.of_cross (between_symm hBZD) (between_symm hEZC) hBDC.bac.acb
  /- F, between C and A, lies on A's side of both straight lines. -/
  have hF_side : ∀ {P : Point}, P ≠ C → Triangle P C A → SameSideOf F A P C := by
    intro P hPC hPCA
    obtain ⟨K, hP_K, hC_K⟩ := Postulate1 P C hPC
    have hA_K : ¬ OnLine A K := hPCA.off_line hP_K hC_K
    have hF_K : ¬ OnLine F K := fun hF_K =>
      hA_K ((line_unique (ne_of_between hCFA) hC_N hF_N hC_K hF_K) ▸ hA_N)
    exact SameSideOf.of_line hPC hP_K hC_K (pasch2 hCFA hC_K hF_K)
  /- The two pairs are equal by Euclid's case, and their sums are equal. -/
  have h₁ : ∠ B A C = ∠ B E C :=
    greater hA hB hC hE (hF_side hBC hA_BC.symm.triangle) (hA_BC.symm.trans hE_BC)
  have h₂ : ∠ D A C = ∠ D E C :=
    greater hA hD hC hE (hF_side hDC hA_DC.symm.triangle) (hA_DC.symm.trans hE_DC)
  have hCA : C ≠ A := by
    intro e; subst e; exact hAC_L.2.2 (same_side_refl hA_L)
  have hCE : C ≠ E := by
    intro e; subst e; exact hEC_L.2.2 (same_side_refl hEC_L.1)
  rw [hsplitA, hsplitE, h₁, angle_symm hCA hBDA.ne₂₃, h₂, angle_symm hBDE.ne₂₃ hCE]
  -- Q. E. D.

end Elements.BookIII
