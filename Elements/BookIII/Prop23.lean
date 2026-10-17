import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop16
import Elements.BookIII.Prop10
import Elements.BookIII.Prop21

/-!
# Book III, Proposition 23

Euclid's text, in Heath's translation: [`heath/III/23.md`](../../heath/III/23.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- On the same straight line there cannot be constructed two similar and unequal segments of
circles on the same side. -/
theorem Prop23 {A B C D : Point} {ACB ADB : Circle} (hACB : ∃ O : Point, Centre O ACB)
    (hADB : ∃ O : Point, Centre O ADB) (hA₁ : OnCircle A ACB) (hB₁ : OnCircle B ACB)
    (hC : OnCircle C ACB) (hA₂ : OnCircle A ADB) (hB₂ : OnCircle B ADB)
    (hD : OnCircle D ADB) (hCD : SameSideOf C D A B) (hsim : ∠ A C B = ∠ A D B) :
    ACB = ADB := by
  -- For, if possible, on the same straight line AB let two similar and unequal segments of
  -- circles ACB, ADB be constructed on the same side;
  refine Classical.byContradiction fun hne => ?_
  have hABC : Triangle A B C := hCD.triangle
  have hAB : A ≠ B := hCD.1
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  have hC_AB : ¬ OnLine C AB := hABC.off_line hA_AB hB_AB
  -- let ACD be drawn through, and let CB, DB be joined.
  /- Euclid draws the segment ACB within ADB. The circles meet at `A` and `B`, so not at
     `C` as well [III. 10]: `C` is within the circle ADB, or outside it. Within, `AC`
     drawn through meets ADB at `D₀` beyond `C` (System E, Intersections 5), and the angle
     `ADB` is the angle `AD₀B`, in the same segment [III. 21]. Outside, the segments are
     the other way about: a point `M` between `A` and `B` is within both circles, so `MC`
     meets ADB at a point `D₁` within ACB (Intersections 4, Circle 2), and `AD₁` drawn
     through meets ACB at `C₀`. Either way a point `P` of one segment lies within the other,
     and `AP` drawn through meets it at `Q`. -/
  have hC₂ : ¬ OnCircle C ADB := fun hC₂ =>
    hne (Prop10 hACB hADB hA₁ hA₂ hB₁ hB₂ hC hC₂ hAB hABC.ne₁₃ hABC.ne₂₃)
  obtain ⟨P, Q, hAPQ, hP_AB, hangles⟩ : ∃ P Q : Point, Between A P Q ∧ ¬ OnLine P AB ∧
      ((∠ A P B = ∠ A C B ∧ ∠ A Q B = ∠ A D B) ∨
        (∠ A P B = ∠ A D B ∧ ∠ A Q B = ∠ A C B)) := by
    by_cases hin : InsideCircle C ADB
    · obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hABC.ne₁₃
      obtain ⟨D₀, hD₀, -, hD₀CA⟩ := line_circle_beyond hin hC_AC hA_AC hABC.ne₁₃
      have hD₀C : SameSideOf D₀ C A B :=
        SameSideOf.of_onRay (OnRay.of_beyond (between_symm hD₀CA))
          (SameSideOf.of_line hAB hA_AB hB_AB (same_side_refl hC_AB))
      exact ⟨C, D₀, between_symm hD₀CA, hC_AB,
        Or.inl ⟨rfl, (Prop21 hADB hD hA₂ hB₂ hD₀ (hCD.symm.trans hD₀C.symm)).symm⟩⟩
    · obtain ⟨M, hM_AB, hAMB, -⟩ := exists_point_between hA_AB hB_AB hAB []
      have hM₁ : InsideCircle M ACB := inside_of_between (Or.inr hA₁) (Or.inr hB₁) hAMB
      have hM₂ : InsideCircle M ADB := inside_of_between (Or.inr hA₂) (Or.inr hB₂) hAMB
      have hMC : M ≠ C := fun h => hC_AB (h ▸ hM_AB)
      obtain ⟨MC, hM_MC, hC_MC⟩ := Postulate1 M C hMC
      obtain ⟨D₁, hD₁, hD₁_MC, hMD₁C⟩ := line_circle_between hM₂ hM_MC ⟨hin, hC₂⟩ hC_MC
      have hD₁_in : InsideCircle D₁ ACB := inside_of_between (Or.inl hM₁) (Or.inr hC) hMD₁C
      have hD₁_AB : ¬ OnLine D₁ AB := fun h =>
        hC_AB (line_unique (ne_of_between hMD₁C) hM_MC hD₁_MC hM_AB h ▸ hC_MC)
      have hD₁C : SameSideOf D₁ C A B :=
        SameSideOf.of_line hAB hA_AB hB_AB (pasch2 hMD₁C hM_AB hD₁_AB)
      have hAD₁ : A ≠ D₁ := fun h => hD₁_AB (h ▸ hA_AB)
      obtain ⟨AD₁, hA_AD₁, hD₁_AD₁⟩ := Postulate1 A D₁ hAD₁
      obtain ⟨C₀, hC₀, -, hC₀D₁A⟩ := line_circle_beyond hD₁_in hD₁_AD₁ hA_AD₁ hAD₁
      have hC₀D₁ : SameSideOf C₀ D₁ A B :=
        SameSideOf.of_onRay (OnRay.of_beyond (between_symm hC₀D₁A))
          (SameSideOf.of_line hAB hA_AB hB_AB (same_side_refl hD₁_AB))
      exact ⟨D₁, C₀, between_symm hC₀D₁A, hD₁_AB, Or.inr
        ⟨(Prop21 hADB hD hA₂ hB₂ hD₁ (hCD.symm.trans hD₁C.symm)).symm,
         (Prop21 hACB hC hA₁ hB₁ hC₀ (hD₁C.symm.trans hC₀D₁.symm)).symm⟩⟩
  -- Then, since the segment ACB is similar to the segment ADB,
  -- and similar segments of circles are those which admit equal angles, [III. Def. 11]
  have hPQ : ∠ A P B = ∠ A Q B := by
    rcases hangles with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]; exact hsim
    · rw [h₁, h₂]; exact hsim.symm
  -- the angle ACB is equal to the angle ADB, the exterior to the interior: which is
  -- impossible. [I. 16]
  obtain ⟨AP, hA_AP, hP_AP⟩ := Postulate1 A P (ne_of_between hAPQ)
  have hQ_AP : OnLine Q AP := on_line_of_between hAPQ hA_AP hP_AP
  have hB_AP : ¬ OnLine B AP := fun h =>
    hP_AB (line_unique hAB hA_AP h hA_AB hB_AB ▸ hP_AP)
  have hQPB : Triangle Q P B :=
    Triangle.of_line hQ_AP hP_AP (ne_of_between (between_symm hAPQ)) hB_AP
  have h16 := (BookI.Prop16 hQPB.cab (between_symm hAPQ)).1
  rw [angle_onRay_left (OnRay.of_between (between_symm hAPQ)) hQPB.ne₁₃.symm,
    angle_symm hQPB.ne₂₃.symm (ne_of_between hAPQ), ← hPQ] at h16
  exact lt_irrefl _ h16
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
