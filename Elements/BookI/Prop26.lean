import Elements.Figure.Basics
import Elements.BookI.Prop03
import Elements.BookI.Prop04
import Elements.BookI.Prop16

/-!
# Book I, Proposition 26

Euclid's text, in Heath's translation: [`heath/I/26.md`](../../heath/I/26.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- If two triangles have the two angles equal to two angles respectively, and one side equal to one
side, namely, either the side adjoining the equal angles, or that subtending one of the equal
angles, they will also have the remaining sides equal to the remaining sides and the remaining
angle to the remaining angle. -/
theorem Prop26 {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
    (hB : ∠ A B C = ∠ D E F) (hC : ∠ B C A = ∠ E F D)
    (hside : ‖B C‖ = ‖E F‖ ∨ ‖A B‖ = ‖D E‖) :
    ‖A B‖ = ‖D E‖ ∧ ‖A C‖ = ‖D F‖ ∧ ‖B C‖ = ‖E F‖ ∧ ∠ B A C = ∠ E D F := by
  -- Let ABC, DEF be two triangles having the two angles ABC, BCA equal to the two angles DEF,
  -- EFD respectively, namely the angle ABC to the angle DEF, and the angle BCA to the angle
  -- EFD; and let them also have one side equal to one side, first that adjoining the equal
  -- angles, namely BC to EF;
  rcases hside with hBC | hAB
    -- I say that they will also have the remaining sides equal to the remaining sides
    -- respectively, namely AB to DE and AC to DF, and the remaining angle to the remaining
    -- angle, namely the angle BAC to the angle EDF.
    -- For, if AB is unequal to DE, one of them is greater.
  · /- The argument for the greater side works with the triangles named either
       way round. We write it once and exchange them below. -/
    have greater : ∀ {A B C D E F : Point}, Triangle A B C → Triangle D E F →
        ∠ A B C = ∠ D E F → ∠ B C A = ∠ E F D → ‖B C‖ = ‖E F‖ →
        ‖D E‖ < ‖A B‖ → False := by
      intro A B C D E F hABC hDEF hB hC hBC hlt
      -- Let AB be greater, and let BG be made equal to DE; and let GC be joined.
      /- I.3 supplies the cut and says explicitly that G is between B and A. GC is
         named by its ends, as a side of the triangle GBC, so nothing is drawn for the
         join. -/
      obtain ⟨G, hBGA, hBG⟩ := Prop3 hDEF.ne₁₂ (by rwa [len_symm B A])
      obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hABC.ne₁₂
      have hG_AB := on_line_of_between_ends hBGA hB_AB hA_AB
      have hBGC : Triangle B G C := Triangle.of_line hB_AB hG_AB
        (ne_of_between hBGA) (hABC.off_line hA_AB hB_AB)
      -- Then, since BG is equal to DE, and BC to EF,
      -- the two sides GB, BC are equal to the two sides DE, EF respectively;
      have hBG_ED : ‖B G‖ = ‖E D‖ := hBG.trans (len_symm D E)
      -- and the angle GBC is equal to the angle DEF;
      have hGBC : ∠ G B C = ∠ D E F :=
        (angle_onRay_left (OnRay.of_between hBGA) hABC.ne₂₃.symm).trans hB
      -- therefore the base GC is equal to the base DF,
      obtain ⟨hGC, harea, -, hC'⟩ := Prop4 hBGC hDEF.bac hBG_ED hBC hGBC
      -- and the triangle GBC is equal to the triangle DEF,
      have : △ G B C = △ D E F := by
        rw [area_swap G B C, area_rotate G C B, area_swap D E F, area_rotate D F E]
        exact harea
      -- and the remaining angles will be equal to the remaining angles, namely those which the
      -- equal sides subtend; [I. 4]
      -- therefore the angle GCB is equal to the angle DFE.
      have hGCB : ∠ G C B = ∠ D F E :=
        (angle_symm hBGC.ne₂₃ hBGC.ne₁₃).trans
          (hC'.trans (angle_symm hDEF.ne₂₃ hDEF.ne₁₃))
      -- But the angle DFE is by hypothesis equal to the angle BCA;
      have hDFE : ∠ D F E = ∠ B C A :=
        (angle_symm hDEF.ne₁₃ hDEF.ne₂₃).trans hC.symm
      -- therefore the angle BCG is equal to the angle BCA,
      have hBCG : ∠ B C G = ∠ B C A :=
        (angle_symm hBGC.ne₁₃ hBGC.ne₂₃).trans (hGCB.trans hDFE)
      -- the less to the greater: which is impossible.
      have hless := angle_lt_of_between hABC (between_symm hBGA)
      rw [← angle_symm hBGC.ne₁₃ hBGC.ne₂₃,
        ← angle_symm hABC.ne₂₃ hABC.ne₁₃, hBCG] at hless
      exact lt_irrefl _ hless
    -- Therefore AB is not unequal to DE,
    -- and is therefore equal to it.
    have hAB : ‖A B‖ = ‖D E‖ := by
      rcases lt_trichotomy ‖A B‖ ‖D E‖ with hlt | heq | hgt
      · exact False.elim (greater hDEF hABC hB.symm hC.symm hBC.symm hlt)
      · exact heq
      · exact False.elim (greater hABC hDEF hB hC hBC hgt)
    -- But BC is also equal to EF;
    -- therefore the two sides AB, BC are equal to the two sides DE, EF respectively,
    -- and the angle ABC is equal to the angle DEF;
    have hBA_ED : ‖B A‖ = ‖E D‖ :=
      (len_symm B A).trans (hAB.trans (len_symm D E))
    -- therefore the base AC is equal to the base DF,
    obtain ⟨hAC, -, hA, -⟩ := Prop4 hABC.bac hDEF.bac hBA_ED hBC hB
    -- and the remaining angle BAC is equal to the remaining angle EDF. [I. 4]
    exact ⟨hAB, hAC, hBC, hA⟩
    -- Again, let sides subtending equal angles be equal, as AB to DE;
    -- I say again that the remaining sides will be equal to the remaining sides, namely AC to DF
    -- and BC to EF, and further the remaining angle BAC is equal to the remaining angle EDF.
    -- For, if BC is unequal to EF, one of them is greater.
  · /- Again either triangle may have the greater side. -/
    have greater : ∀ {A B C D E F : Point}, Triangle A B C → Triangle D E F →
        ∠ A B C = ∠ D E F → ∠ B C A = ∠ E F D → ‖A B‖ = ‖D E‖ →
        ‖E F‖ < ‖B C‖ → False := by
      intro A B C D E F hABC hDEF hB hC hAB hlt
      -- Let BC be greater, if possible, and let BH be made equal to EF; let AH be joined.
      /- AH is named by its ends, as a side of the triangle ABH, so nothing is drawn
         for the join. -/
      obtain ⟨H, hBHC, hBH⟩ := Prop3 hDEF.ne₂₃ hlt
      obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABC.ne₂₃
      have hH_BC := on_line_of_between_ends hBHC hB_BC hC_BC
      have hBHA : Triangle B H A := Triangle.of_line hB_BC hH_BC
        (ne_of_between hBHC) (hABC.bca.off_line hB_BC hC_BC)
      have hCHA : Triangle C H A := Triangle.of_line hC_BC hH_BC
        (ne_of_between (between_symm hBHC)) (hABC.bca.off_line hB_BC hC_BC)
      -- Then, since BH is equal to EF, and AB to DE,
      -- the two sides AB, BH are equal to the two sides DE, EF respectively, and they contain
      -- equal angles;
      have hBA_ED : ‖B A‖ = ‖E D‖ :=
        (len_symm B A).trans (hAB.trans (len_symm D E))
      have hABH : ∠ A B H = ∠ D E F :=
        (angle_onRay_right (OnRay.of_between hBHC) hABC.ne₁₂).trans hB
      -- therefore the base AH is equal to the base DF,
      obtain ⟨hAH, harea, -, hH⟩ := Prop4 hBHA.acb hDEF.bac hBA_ED hBH hABH
      -- and the triangle ABH is equal to the triangle DEF,
      have : △ A B H = △ D E F := by
        rw [area_swap A B H, area_rotate A H B, area_swap D E F, area_rotate D F E]
        exact harea
      -- and the remaining angles will be equal to the remaining angles, namely those which the
      -- equal sides subtend; [I. 4]
      -- therefore the angle BHA is equal to the angle EFD.
      have hBHA_EFD : ∠ B H A = ∠ E F D := hH
      -- But the angle EFD is equal to the angle BCA;
      have hEFD : ∠ E F D = ∠ B C A := hC.symm
      -- therefore, in the triangle AHC, the exterior angle BHA is equal to the interior and
      -- opposite angle BCA:
      have hBHA_BCA : ∠ B H A = ∠ B C A := hBHA_EFD.trans hEFD
      -- which is impossible. [I. 16]
      have hless := (Prop16 hCHA.cab (between_symm hBHC)).1
      rw [angle_onRay_left (OnRay.of_between (between_symm hBHC)) hABC.ne₁₃,
        angle_symm hBHA.ne₂₃.symm hBHA.ne₁₂, hBHA_BCA] at hless
      exact lt_irrefl _ hless
    -- Therefore BC is not unequal to EF,
    -- and is therefore equal to it.
    have hBC : ‖B C‖ = ‖E F‖ := by
      rcases lt_trichotomy ‖B C‖ ‖E F‖ with hlt | heq | hgt
      · exact False.elim (greater hDEF hABC hB.symm hC.symm hAB.symm hlt)
      · exact heq
      · exact False.elim (greater hABC hDEF hB hC hAB hgt)
    -- But AB is also equal to DE;
    -- therefore the two sides AB, BC are equal to the two sides DE, EF respectively, and they
    -- contain equal angles;
    have hBA_ED : ‖B A‖ = ‖E D‖ :=
      (len_symm B A).trans (hAB.trans (len_symm D E))
    -- therefore the base AC is equal to the base DF,
    obtain ⟨hAC, harea, hA, -⟩ := Prop4 hABC.bac hDEF.bac hBA_ED hBC hB
    -- the triangle ABC equal to the triangle DEF,
    have : △ A B C = △ D E F := by
      rw [area_swap A B C, area_rotate A C B, area_swap D E F, area_rotate D F E]
      exact harea
    -- and the remaining angle BAC equal to the remaining angle EDF. [I. 4]
    have hBAC : ∠ B A C = ∠ E D F := hA
    -- Therefore etc.
    exact ⟨hAB, hAC, hBC, hBAC⟩
  -- Q. E. D.

end Elements.BookI
