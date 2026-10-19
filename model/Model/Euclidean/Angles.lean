module

public import Model.Euclidean.AngleBasics
public import Model.Laws.angles

/-!
# Radii and angle laws in the plane

These proofs use Mathlib's unoriented angle, the work of Joseph Myers and Manuel Candales,
and its spheres, betweenness and affine lines, the work of Joseph Myers. The bridge to our
angle keeps its value at 0 when either arm has a repeated point; with both arms nonzero,
we can use Mathlib's angle and its descriptions of a straight angle and a common ray.
-/

@[expose] public section

namespace Model.Euclidean

open scoped NNReal Real

/-- Our angle is at most π, including its value 0 when either arm is repeated. -/
theorem coe_angle_le_pi (A B C : Plane) : (angle A B C : ℝ) ≤ π := by
  by_cases hA : A = B
  · subst A
    simpa using Real.pi_nonneg
  by_cases hC : C = B
  · subst C
    simpa using Real.pi_nonneg
  rw [coe_angle_of_ne hA hC]
  exact EuclideanGeometry.angle_le_pi A B C

/-- With nonzero arms, our angle is zero exactly when Mathlib's angle is zero. -/
theorem angle_eq_zero_iff_of_ne {A B C : Plane} (hA : A ≠ B) (hC : C ≠ B) :
    angle A B C = 0 ↔ EuclideanGeometry.angle A B C = 0 := by
  rw [← NNReal.coe_inj, coe_angle_of_ne hA hC, NNReal.coe_zero]

/-- **`Definition15` holds in the plane.** Both distances from the centre are the
circle's radius, even if the two points on the circle coincide. -/
theorem Definition15_angles : Hand.Definition15_angles plane := by
  intro A B C α hA hB hC
  rw [centre_iff] at hA
  rw [onCircle_iff] at hB hC
  change nndist A B = nndist A C
  apply NNReal.eq
  change dist A B = dist A C
  rw [hA, dist_comm α.1.center B, dist_comm α.1.center C, hB, hC]

/-- **`angle_symm` holds in the plane.** Mathlib's unoriented angle is symmetric in
its arms; the hypotheses exclude an arm repeated at the vertex. -/
theorem angle_symm : Hand.angle_symm plane := by
  intro A B C hA hC
  exact (angle_eq_angle_iff hA hC hC hA).2 (EuclideanGeometry.angle_comm A B C)

/-- **`angle_le_two_right` holds in the plane.** Mathlib bounds an angle by π, the sum
of two right angles, and our value 0 at a repeated point satisfies the same bound. -/
theorem angle_le_two_right : Hand.angle_le_two_right plane := by
  intro A B C
  change ¬ (⟨π / 2, by positivity⟩ + ⟨π / 2, by positivity⟩ : ℝ≥0) < angle A B C
  apply not_lt_of_ge
  apply NNReal.coe_le_coe.mp
  change (angle A B C : ℝ) ≤ π / 2 + π / 2
  linarith [coe_angle_le_pi A B C]

/-- **`angle_eq_zero_of_same_ray` holds in the plane.** Collinear nonzero arms make
an angle of 0 or π, and the excluded betweenness rules out π; the two outer points may coincide. -/
theorem angle_eq_zero_of_same_ray : Hand.angle_eq_zero_of_same_ray plane := by
  intro A B C L hAB hAC hA hB hC hbtw
  apply (angle_eq_zero_iff_of_ne hAB.symm hAC.symm).2
  have hline := line_eq_affineSpan hAB hA hB
  have hcol : Collinear ℝ ({B, A, C} : Set Plane) := by
    change A ∈ L.1 at hA
    change B ∈ L.1 at hB
    change C ∈ L.1 at hC
    rw [hline] at hA hB hC
    exact collinear_triple_of_mem_affineSpan_pair hB hA hC
  rcases EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.1 hcol
      with h | h | h | h
  · exact False.elim (hAB h.symm)
  · exact False.elim (hAC h.symm)
  · exact h
  · exact False.elim (hbtw (EuclideanGeometry.angle_eq_pi_iff_sbtw.1 h))

/-- **`same_ray_of_angle_eq_zero` holds in the plane.** With the vertex distinct
from both outer points, a zero angle gives collinearity and cannot be a straight angle,
even when the outer points coincide. -/
theorem same_ray_of_angle_eq_zero : Hand.same_ray_of_angle_eq_zero plane := by
  intro A B C L hAB hAC hA hB hzero
  have hzero' := (angle_eq_zero_iff_of_ne hAB.symm hAC.symm).1 hzero
  have hcol := EuclideanGeometry.collinear_of_angle_eq_zero hzero'
  constructor
  · change C ∈ L.1
    rw [line_eq_affineSpan hAB hA hB]
    exact hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAB
  · intro hbtw
    have hpi := hbtw.angle₁₂₃_eq_pi
    rw [hzero'] at hpi
    exact Real.pi_ne_zero hpi.symm

/-- **`adjacent_eq_of_right` holds in the plane.** The two adjacent angles sum to π,
so if one is π/2 the other is too; strict betweenness and the point off the line keep
every arm nonzero. -/
theorem adjacent_eq_of_right : Hand.adjacent_eq_of_right plane := by
  intro A B C D L hA hB hbtw hD hright
  have hC : C ∈ L.1 :=
    (affineSpan_pair_le_of_mem_of_mem hA hB) hbtw.wbtw.mem_affineSpan
  have hDC : D ≠ C := by
    rintro rfl
    exact hD hC
  have hsum := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi D hbtw.angle₁₂₃_eq_pi
  rw [EuclideanGeometry.angle_comm D C A] at hsum
  have hright' : EuclideanGeometry.angle A C D = π / 2 := by
    have h := congrArg (fun x : ℝ≥0 => (x : ℝ)) hright
    change (angle A C D : ℝ) = π / 2 at h
    rwa [coe_angle_of_ne hbtw.left_ne hDC] at h
  apply (angle_eq_angle_iff hbtw.left_ne hDC hDC hbtw.right_ne).2
  linarith

/-- **`angle_eq_of_same_rays` holds in the plane.** Moving either arm by a positive
scale leaves its angle unchanged; the hypotheses exclude zero arms but allow the lines
and the points on each ray to coincide. -/
theorem angle_eq_of_same_rays : Hand.angle_eq_of_same_rays plane := by
  intro A B C L M B' C' hAL hBL hB'L hAM hCM hC'M hB hB' hC hC' hBB' hCC'
  have hleft := angle_eq_zero_of_same_ray hB.symm hB'.symm hAL hBL hB'L hBB'
  have hright := angle_eq_zero_of_same_ray hC.symm hC'.symm hAM hCM hC'M hCC'
  have hleft' := (angle_eq_zero_iff_of_ne hB hB').1 hleft
  have hright' := (angle_eq_zero_iff_of_ne hC hC').1 hright
  obtain ⟨_, r, hr, hBr⟩ := InnerProductGeometry.angle_eq_zero_iff.1 hleft'
  obtain ⟨_, s, hs, hCs⟩ := InnerProductGeometry.angle_eq_zero_iff.1 hright'
  apply (angle_eq_angle_iff hB hC hB' hC').2
  change InnerProductGeometry.angle (B -ᵥ A) (C -ᵥ A) =
    InnerProductGeometry.angle (B' -ᵥ A) (C' -ᵥ A)
  rw [hBr, hCs, InnerProductGeometry.angle_smul_left_of_pos _ _ hr,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hs]

/-- **`Postulate4` holds in the plane.** Equal adjacent angles on a straight line
sum to π and hence each equal π/2; strict betweenness and noncollinearity exclude
repeated points at the vertex, where our angle would be 0. -/
theorem Postulate4 : Hand.Postulate4 plane := by
  intro A B C hright
  obtain ⟨D, hbtw, hnoncol, heq⟩ := hright
  have hCB : C ≠ B := by
    rintro rfl
    exact hnoncol ⟨lineThrough hbtw.left_ne, mem_lineThrough_left hbtw.left_ne,
      mem_lineThrough_right hbtw.left_ne, mem_lineThrough_right hbtw.left_ne⟩
  have heq' := (angle_eq_angle_iff hbtw.left_ne hCB hCB hbtw.right_ne).1 heq
  have hsum := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi C hbtw.angle₁₂₃_eq_pi
  rw [EuclideanGeometry.angle_comm C B A] at hsum
  apply NNReal.eq
  change (angle A B C : ℝ) = π / 2
  rw [coe_angle_of_ne hbtw.left_ne hCB]
  linarith

end Model.Euclidean
