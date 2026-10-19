module

public import Model.Euclidean
public import Model.Laws.«areas-p5»
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The area laws in the ordinary plane

We read a triangle's area as half the absolute value of its determinant. Swapping
corners changes the sign, and cycling them preserves it. The three squared side lengths
determine the squared determinant, including when corners coincide or lie on a line.

A line through distinct A and B consists of the points A + t (B - A). The determinant
vanishes exactly on this line. Cutting a triangle at such a point scales its two areas
by |t| and |1 - t|. For a vertex off the line their sum equals the whole precisely when
0 ≤ t ≤ 1; excluding the endpoints gives strict betweenness.

The area laws are proved here as the coordinate calculation they are, and the
calculation reaches the plane's geometric words through Mathlib: its Euclidean plane,
`EuclideanSpace`, the work of Joseph Myers, Sébastien Gouëzel and Heather Macbeth, and its
betweenness and affine subspaces, the work of Joseph Myers and many others. Our thanks to
them all.
-/

@[expose] public section

namespace Model.Euclidean

namespace Areas

/-- Interchanging the vectors reverses the determinant's sign. -/
lemma det_swap (u v : Plane) : det u v = -det v u := by
  unfold det
  ring

/-- Cycling a triangle's corners preserves its signed determinant. -/
lemma det_rotate (A B C : Plane) : det (B - A) (C - A) = det (A - C) (B - C) := by
  simp only [det, PiLp.sub_apply]
  ring

/-- A nonzero vector has zero determinant with exactly its scalar multiples. -/
lemma det_eq_zero_iff {u v : Plane} (hu : u ≠ 0) :
    det u v = 0 ↔ ∃ t : ℝ, t • u = v := by
  constructor
  · intro h
    by_cases h0 : u 0 = 0
    · have h1 : u 1 ≠ 0 := by
        intro h1
        apply hu
        ext i
        fin_cases i <;> simp [h0, h1]
      refine ⟨v 1 / u 1, ?_⟩
      have hv0 : v 0 = 0 := by
        have hm : u 1 * v 0 = 0 := by simpa [det, h0] using h
        exact (mul_eq_zero.mp hm).resolve_left h1
      ext i
      fin_cases i <;> simp [PiLp.smul_apply, h0, hv0, h1]
    · refine ⟨v 0 / u 0, ?_⟩
      ext i
      fin_cases i
      · simp [PiLp.smul_apply, h0]
      · simp only [PiLp.smul_apply, smul_eq_mul]
        rw [div_mul_eq_mul_div, div_eq_iff h0]
        have hd : u 0 * v 1 = u 1 * v 0 := sub_eq_zero.mp h
        exact (mul_comm _ _).trans (hd.symm.trans (mul_comm _ _))
  · rintro ⟨t, rfl⟩
    simp only [det, PiLp.smul_apply, smul_eq_mul]
    ring

/-- A line through distinct points has their difference as a spanning direction. -/
lemma mem_line_iff {L : Line} {A B C : Plane}
    (hA : A ∈ L.1) (hB : B ∈ L.1) (hAB : A ≠ B) :
    C ∈ L.1 ↔ ∃ t : ℝ, t • (B - A) = C - A := by
  have hdir : L.1.direction = ℝ ∙ (B -ᵥ A) :=
    eq_span_singleton_of_mem_of_finrank_eq_one L.2
      (AffineSubspace.vsub_mem_direction hB hA) (vsub_ne_zero.2 hAB.symm)
  rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hA C, hdir]
  exact Submodule.mem_span_singleton

/-- Zero determinant is the test for membership in a line through distinct points. -/
lemma mem_line_iff_det_eq_zero {L : Line} {A B C : Plane}
    (hA : A ∈ L.1) (hB : B ∈ L.1) (hAB : A ≠ B) :
    C ∈ L.1 ↔ det (B - A) (C - A) = 0 := by
  rw [mem_line_iff hA hB hAB, det_eq_zero_iff (sub_ne_zero.mpr hAB.symm)]

/-- The area vanishes exactly when its signed determinant vanishes. -/
lemma triArea_eq_zero_iff (A B C : Plane) :
    triArea A B C = 0 ↔ det (B - A) (C - A) = 0 := by
  rw [← NNReal.coe_inj]
  change |det (B - A) (C - A)| / 2 = (0 : ℝ) ↔ det (B - A) (C - A) = 0
  simp

/-- The three squared side lengths determine four times the squared determinant. -/
lemma four_det_sq (A B C : Plane) :
    4 * det (B - A) (C - A) ^ 2 =
      4 * dist A B ^ 2 * dist C A ^ 2 -
        (dist A B ^ 2 + dist C A ^ 2 - dist B C ^ 2) ^ 2 := by
  simp only [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
    det, PiLp.sub_apply]
  ring

/-- Moving the first base endpoint a fraction t along the base scales its determinant
by t. -/
lemma det_lineMap_left (A B D : Plane) (t : ℝ) :
    det (AffineMap.lineMap A B t - A) (D - A) = t * det (B - A) (D - A) := by
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, det,
    PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The other piece of the base contributes the factor 1 - t. -/
lemma det_lineMap_right (A B D : Plane) (t : ℝ) :
    det (AffineMap.lineMap A B t - D) (B - D) = (1 - t) * det (B - A) (D - A) := by
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, det,
    PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

end Areas

/-- **`area_degenerate` holds in the plane.** A repeated corner gives a zero vector. -/
theorem area_degenerate : Hand.area_degenerate plane := by
  intro A B
  apply (Areas.triArea_eq_zero_iff A A B).2
  simp [det]

/-- **`area_rotate` holds in the plane.** Cycling the corners preserves the determinant. -/
theorem area_rotate : Hand.area_rotate plane := by
  intro A B C
  apply Subtype.ext
  change |det (B - A) (C - A)| / 2 = |det (A - C) (B - C)| / 2
  rw [Areas.det_rotate]

/-- **`area_swap` holds in the plane.** Absolute value removes the change of sign. -/
theorem area_swap : Hand.area_swap plane := by
  intro A B C
  apply Subtype.ext
  change |det (B - A) (C - A)| / 2 = |det (C - A) (B - A)| / 2
  rw [Areas.det_swap, abs_neg]

/-- **`area_congruent` holds in the plane.** The three side equalities already determine
the area, even for degenerate triangles, so the angle hypotheses are not needed. -/
theorem area_congruent : Hand.area_congruent plane := by
  intro A B C D E F hAB hBC hCA _ _ _
  have hAB' : dist A B = dist D E := congrArg NNReal.toReal hAB
  have hBC' : dist B C = dist E F := congrArg NNReal.toReal hBC
  have hCA' : dist C A = dist F D := congrArg NNReal.toReal hCA
  have hsq : det (B - A) (C - A) ^ 2 = det (E - D) (F - D) ^ 2 := by
    have h₁ := Areas.four_det_sq A B C
    have h₂ := Areas.four_det_sq D E F
    rw [hAB', hBC', hCA'] at h₁
    linarith
  apply Subtype.ext
  change |det (B - A) (C - A)| / 2 = |det (E - D) (F - D)| / 2
  congr 1
  nlinarith only [hsq, sq_abs (det (B - A) (C - A)),
    sq_abs (det (E - D) (F - D)), abs_nonneg (det (B - A) (C - A)),
    abs_nonneg (det (E - D) (F - D))]

/-- **`area_eq_zero_of_on_line` holds in the plane.** Points of the line have dependent
side vectors, hence zero determinant. -/
theorem area_eq_zero_of_on_line : Hand.area_eq_zero_of_on_line plane := by
  intro A B C L hA hB hAB hC
  exact (Areas.triArea_eq_zero_iff A B C).2
    ((Areas.mem_line_iff_det_eq_zero hA hB hAB).1 hC)

/-- **`on_line_of_area_eq_zero` holds in the plane.** The distinct first two corners fix
the line on which the determinant vanishes. -/
theorem on_line_of_area_eq_zero : Hand.on_line_of_area_eq_zero plane := by
  intro A B C L hA hB hAB harea
  exact (Areas.mem_line_iff_det_eq_zero hA hB hAB).2
    ((Areas.triArea_eq_zero_iff A B C).1 harea)

/-- **`area_add_of_between` holds in the plane.** A point strictly between the base
endpoints divides the determinant in the positive proportions t and 1 - t. -/
theorem area_add_of_between : Hand.area_add_of_between plane := by
  intro A B C D L _ _ _ _ _ _ _ hbetween
  obtain ⟨t, ht, rfl⟩ := hbetween.mem_image_Ioo
  apply Subtype.ext
  change |det (AffineMap.lineMap A B t - A) (D - A)| / 2 +
    |det (AffineMap.lineMap A B t - D) (B - D)| / 2 =
      |det (D - A) (B - A)| / 2
  rw [Areas.det_lineMap_left, Areas.det_lineMap_right,
    Areas.det_swap (D - A) (B - A), abs_neg, abs_mul, abs_mul,
    abs_of_pos ht.1, abs_of_pos (sub_pos.mpr ht.2)]
  ring

/-- **`between_of_area_add` holds in the plane.** The vertex off the line makes the
whole area positive; additivity forces the base parameter into the unit interval.
The distinctness hypotheses exclude its endpoints. -/
theorem between_of_area_add : Hand.between_of_area_add plane := by
  intro A B C D L hA hB hC hAB hAC hBC hD harea
  obtain ⟨t, ht⟩ := (Areas.mem_line_iff hA hB hAB).1 hC
  have hparam : AffineMap.lineMap A B t = C := by
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, ht, sub_add_cancel]
  have hk : det (B - A) (D - A) ≠ 0 := by
    intro h
    exact hD ((Areas.mem_line_iff_det_eq_zero hA hB hAB).2 h)
  have heq := congrArg NNReal.toReal harea
  change |det (C - A) (D - A)| / 2 + |det (C - D) (B - D)| / 2 =
    |det (D - A) (B - A)| / 2 at heq
  rw [← hparam, Areas.det_lineMap_left, Areas.det_lineMap_right,
    Areas.det_swap (D - A) (B - A), abs_neg, abs_mul, abs_mul] at heq
  have hsum : |t| + |1 - t| = 1 := by
    have hprod : (|t| + |1 - t| - 1) * |det (B - A) (D - A)| = 0 := by
      nlinarith [heq]
    have := (mul_eq_zero.mp hprod).resolve_right (abs_ne_zero.mpr hk)
    linarith
  have ht0 : 0 ≤ t := by
    linarith [le_abs_self (1 - t), neg_le_abs t]
  have ht1 : t ≤ 1 := by
    linarith [le_abs_self t, neg_le_abs (1 - t)]
  have htne0 : t ≠ 0 := by
    intro h
    apply hAC
    rw [← hparam, h, AffineMap.lineMap_apply_zero]
  have htne1 : t ≠ 1 := by
    intro h
    apply hBC
    rw [← hparam, h, AffineMap.lineMap_apply_one]
  exact sbtw_iff_mem_image_Ioo_and_ne.mpr
    ⟨⟨t, ⟨lt_of_le_of_ne ht0 htne0.symm, lt_of_le_of_ne ht1 htne1⟩, hparam⟩, hAB⟩

end Model.Euclidean
