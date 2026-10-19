module

public import Model.Euclidean
public import Model.Laws.intersections
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Where a straight line cuts a circle, in the plane

A line through a point inside a circle crosses the circle twice, once in each direction.
Parametrize the line from the inside point B by a nonzero vector v. The squared distance
to the centre, minus the squared radius, is a quadratic in the parameter. Its leading
coefficient is positive and its value at zero is negative, so its two roots lie on
opposite sides of zero. The points inside the circle are exactly those between the roots.

This calculation proves Intersection 3, the two line and circle constructions, and
Circle 1. The constructions select the root on the required side of B. For Circle 1,
the two ends of the chord must be the two roots, so the inside point lies between them.
The argument includes a line through the centre and every placement allowed by the laws.

Mathlib's affine subspaces, betweenness and spheres are the work of Joseph Myers. Its
inner-product identities are due to Zhouhang Zhou, Sébastien Gouëzel and Frédéric Dupuis,
and its finite-dimensional linear algebra to Chris Hughes, as their files record.
Our thanks to them all.
-/

@[expose] public section

namespace Model.Euclidean

open scoped RealInnerProductSpace

/-- From a point B inside a circle, every nonzero direction reaches its circumference at
exactly two parameters, one negative and one positive. A parameter gives an inside point
exactly when it lies strictly between these two roots. -/
theorem exists_roots_of_inside {B c v : Plane} {r : ℝ}
    (hB : dist B c < r) (hv : v ≠ 0) :
    ∃ t₁ t₂ : ℝ, t₁ < 0 ∧ 0 < t₂ ∧ ∀ t : ℝ,
      (dist (t • v +ᵥ B) c = r ↔ t = t₁ ∨ t = t₂) ∧
      (dist (t • v +ᵥ B) c < r ↔ t₁ < t ∧ t < t₂) := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hB
  set a := ‖v‖ ^ 2 with ha_def
  set b := ⟪B -ᵥ c, v⟫ with hb_def
  set d := dist B c ^ 2 - r ^ 2 with hd_def
  have ha : 0 < a := sq_pos_of_pos (norm_pos_iff.2 hv)
  have hd : d < 0 := by
    have := (sq_lt_sq₀ dist_nonneg hr.le).2 hB
    dsimp [d]
    linarith
  have hdisc : 0 < b ^ 2 - a * d := by
    have := mul_neg_of_pos_of_neg ha hd
    nlinarith [sq_nonneg b]
  set k := Real.sqrt (b ^ 2 - a * d) with hk_def
  have hk : 0 < k := Real.sqrt_pos.2 hdisc
  have hkk : k ^ 2 = b ^ 2 - a * d := Real.sq_sqrt hdisc.le
  have hbk : b < k := by
    have := mul_neg_of_pos_of_neg ha hd
    nlinarith
  have hnbk : -b < k := by
    have := mul_neg_of_pos_of_neg ha hd
    nlinarith
  set t₁ := (-b - k) / a with ht₁_def
  set t₂ := (-b + k) / a with ht₂_def
  have ht₁ : t₁ < 0 := div_neg_of_neg_of_pos (by linarith) ha
  have ht₂ : 0 < t₂ := div_pos (by linarith) ha
  have hnorm : ∀ t : ℝ, dist (t • v +ᵥ B) c ^ 2 - r ^ 2 =
      a * t ^ 2 + 2 * b * t + d := by
    intro t
    rw [dist_eq_norm_vsub, vadd_vsub_assoc]
    rw [add_comm (t • v), norm_add_sq_real, inner_smul_right, norm_smul]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    rw [← dist_eq_norm_vsub Plane B c]
    dsimp [a, b, d]
    ring
  have hfactor : ∀ t : ℝ, dist (t • v +ᵥ B) c ^ 2 - r ^ 2 =
      a * ((t - t₁) * (t - t₂)) := by
    intro t
    rw [hnorm]
    dsimp [t₁, t₂]
    field_simp
    nlinarith [hkk]
  refine ⟨t₁, t₂, ht₁, ht₂, fun t => ⟨?_, ?_⟩⟩
  · rw [← pow_left_inj₀ dist_nonneg hr.le two_ne_zero, ← sub_eq_zero, hfactor,
      mul_eq_zero, or_iff_right ha.ne', mul_eq_zero, sub_eq_zero, sub_eq_zero]
  · rw [← sq_lt_sq₀ dist_nonneg hr.le, ← sub_neg, hfactor, mul_neg_iff]
    simp only [ha, not_lt_of_ge ha.le, true_and, false_and, or_false]
    rw [mul_neg_iff]
    constructor
    · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
      · exact ⟨by linarith, by linarith⟩
      · exfalso
        linarith
    · rintro ⟨h₁, h₂⟩
      exact Or.inl ⟨by linarith, by linarith⟩

/-! ## The laws -/

/-- **Intersection 3 holds in the plane.** A line through a point inside a circle
meets its circumference at two distinct points. -/
theorem line_meets_circle_of_inside : Hand.line_meets_circle_of_inside plane := by
  intro A L α hA hAL
  have : Nontrivial L.1.direction :=
    Module.nontrivial_of_finrank_pos (by rw [L.2]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : L.1.direction)
  have hv' : (v : Plane) ≠ 0 := fun h => hv (Subtype.ext h)
  obtain ⟨t₁, t₂, ht₁, ht₂, hroots⟩ := exists_roots_of_inside hA hv'
  refine ⟨t₁ • (v : Plane) +ᵥ A, t₂ • (v : Plane) +ᵥ A, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := smul_left_injective ℝ hv' (vadd_right_cancel A h)
    linarith
  · exact AffineSubspace.vadd_mem_of_mem_direction (L.1.direction.smul_mem t₁ v.2) hAL
  · exact onCircle_iff.2 ((hroots t₁).1.2 (Or.inl rfl))
  · exact AffineSubspace.vadd_mem_of_mem_direction (L.1.direction.smul_mem t₂ v.2) hAL
  · exact onCircle_iff.2 ((hroots t₂).1.2 (Or.inr rfl))

/-- **Intersections 5 of the constructions holds in the plane.** From an inside point B,
the line reaches the circle in the direction away from any other point C on it. -/
theorem line_circle_beyond : Hand.line_circle_beyond plane := by
  intro B C L α hB hBL hCL hCB
  have hv : C -ᵥ B ≠ 0 := vsub_ne_zero.2 hCB
  obtain ⟨t₁, t₂, ht₁, _, hroots⟩ := exists_roots_of_inside hB hv
  have hroot := (hroots t₁).1.2 (Or.inl rfl)
  refine ⟨t₁ • (C -ᵥ B) +ᵥ B, onCircle_iff.2 hroot, ?_, ?_⟩
  · exact AffineSubspace.vadd_mem_of_mem_direction
      (L.1.direction.smul_mem t₁ (AffineSubspace.vsub_mem_direction hCL hBL)) hBL
  · change Sbtw ℝ (t₁ • (C -ᵥ B) +ᵥ B) B C
    refine ⟨?_, ?_, hCB.symm⟩
    · simpa only [one_smul, vsub_vadd] using
        wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg B (C -ᵥ B) ht₁.le
          (show (0 : ℝ) ≤ 1 by norm_num)
    · intro h
      rw [← h] at hroot
      exact (ne_of_lt hB) hroot

/-- **Intersections 4 of the constructions holds in the plane.** The segment from an
inside point B to an outside point C crosses the circle strictly between them. -/
theorem line_circle_between : Hand.line_circle_between plane := by
  intro B C L α hB hBL hC hCL
  obtain ⟨hCinside, hCon⟩ := hC
  have hCB : C ≠ B := by
    rintro rfl
    exact hCinside hB
  obtain ⟨t₁, t₂, ht₁, ht₂, hroots⟩ :=
    exists_roots_of_inside hB (vsub_ne_zero.2 hCB)
  have hone := hroots 1
  simp only [one_smul, vsub_vadd] at hone
  have ht₂_one : t₂ < 1 := by
    have hle : t₂ ≤ 1 := le_of_not_gt fun h =>
      hCinside (hone.2.2 ⟨by linarith, h⟩)
    exact lt_of_le_of_ne hle fun h => hCon (onCircle_iff.2 (hone.1.2 (Or.inr h.symm)))
  refine ⟨t₂ • (C -ᵥ B) +ᵥ B, onCircle_iff.2 ((hroots t₂).1.2 (Or.inr rfl)), ?_, ?_⟩
  · exact AffineSubspace.vadd_mem_of_mem_direction
      (L.1.direction.smul_mem t₂ (AffineSubspace.vsub_mem_direction hCL hBL)) hBL
  · exact sbtw_lineMap_iff.2 ⟨hCB.symm, ht₂, ht₂_one⟩

/-- **Circle 1 holds in the plane.** A point inside the circle on the line of a chord
lies strictly between its two distinct ends. -/
theorem between_of_inside_chord : Hand.between_of_inside_chord plane := by
  intro A B C L α hAL hBL hCL hA hB hC hBC
  rw [onCircle_iff] at hB hC
  have hBA : B ≠ A := by
    rintro rfl
    exact (ne_of_lt hA) hB
  have hAC : A ≠ C := by
    rintro rfl
    exact (ne_of_lt hA) hC
  have hv : B -ᵥ A ≠ 0 := vsub_ne_zero.2 hBA
  have hdir : L.1.direction = ℝ ∙ (B -ᵥ A) :=
    eq_span_singleton_of_mem_of_finrank_eq_one L.2
      (AffineSubspace.vsub_mem_direction hBL hAL) hv
  have hCdir := AffineSubspace.vsub_mem_direction hCL hAL
  rw [hdir] at hCdir
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hCdir
  have hCs : s • (B -ᵥ A) +ᵥ A = C := by rw [hs, vsub_vadd]
  obtain ⟨t₁, t₂, ht₁, _, hroots⟩ := exists_roots_of_inside hA hv
  have hone : 1 = t₁ ∨ 1 = t₂ := (hroots 1).1.1 (by simpa only [one_smul, vsub_vadd] using hB)
  have ht₂ : 1 = t₂ := hone.resolve_left (by linarith)
  have hsroot : s = t₁ ∨ s = t₂ := (hroots s).1.1 (by rwa [hCs])
  have hsne : s ≠ t₂ := by
    intro h
    rw [h, ← ht₂, one_smul, vsub_vadd] at hCs
    exact hBC hCs
  have hsneg : s < 0 := by rw [hsroot.resolve_right hsne]; exact ht₁
  have hbetween : Sbtw ℝ C A B := by
    refine ⟨?_, hAC, hBA.symm⟩
    simpa only [hCs, one_smul, vsub_vadd] using
      wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg A (B -ᵥ A) hsneg.le
        (show (0 : ℝ) ≤ 1 by norm_num)
  exact hbetween.symm

end Model.Euclidean
