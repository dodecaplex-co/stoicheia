module

public import Model.Euclidean
public import Model.Laws.«areas-p5»
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Postulate 5, with the meeting on the stated side

The two interior angles sum to less than two right angles. We prove that the lines meet
on the side of the transversal containing A and D, as the postulate asks.

Write u = A - B, v = C - B and w = D - C. Strict same-side geometry gives
w = t • u + k • v with t positive. If k were nonnegative, w would lie in the cone
spanned by u and v. Mathlib's angle-addition theorem would then make the two interior
angles sum to at least pi. Thus k is negative. Taking r = -1 / k gives the meeting
B + (r * t) • u = C + r • w. Its positive coefficient on u puts it on A's side.

The strict side hypothesis also keeps both angle arms nonzero, so the reading's
repeated-point convention causes no exception here. The proof stands on Mathlib:
its sides of a line, the work of Joseph Myers; its unoriented angle, of Joseph Myers and
Manuel Candales; and the angle-addition theorem for a vector inside the cone of two
others, `angle_eq_angle_add_add_angle_add_of_mem_span`, of Ilmārs Cīrulis, Alex Meiburg
and Jovan Gerbscheid. Our warm thanks to them.
-/

@[expose] public section

namespace Model.Euclidean

open scoped NNReal Real

namespace P5

/-- Points on the same strict side give a positive coefficient transverse to the line.
The remaining displacement is a multiple of the line's direction. -/
theorem sameSide_decomposition {A B C D : Plane} {M : Line}
    (hB : B ∈ M.1) (hC : C ∈ M.1) (hBC : B ≠ C) (hAD : M.1.SSameSide A D) :
    ∃ t k : ℝ, 0 < t ∧ D - C = t • (A - B) + k • (C - B) := by
  have hD : D ∈ {y | M.1.SSameSide A y} := hAD
  rw [AffineSubspace.setOfPred_sSameSide_eq_image2 hAD.left_notMem hB] at hD
  obtain ⟨t, ht, P, hP, hDP⟩ := hD
  have hdir : M.1.direction = ℝ ∙ (C - B) :=
    eq_span_singleton_of_mem_of_finrank_eq_one M.2
      (AffineSubspace.vsub_mem_direction hC hB) (sub_ne_zero.2 hBC.symm)
  have hPC : P - C ∈ ℝ ∙ (C - B) := by
    rw [← hdir]
    exact AffineSubspace.vsub_mem_direction hP hC
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.1 hPC
  refine ⟨t, k, ht, ?_⟩
  change t • (A - B) + P = D at hDP
  rw [← hDP, hk]
  abel

/-- A nonnegative coefficient along the transversal would make the interior angles
sum to at least pi. The strict angle bound therefore makes that coefficient negative. -/
theorem coefficient_neg {u v w : Plane} {t k : ℝ} (ht : 0 < t) (hw : w ≠ 0)
    (hdecomp : w = t • u + k • v)
    (hang : InnerProductGeometry.angle u v + InnerProductGeometry.angle (-v) w < π) :
    k < 0 := by
  by_contra hk
  have hk0 : 0 ≤ k := le_of_not_gt hk
  have hmem : w ∈ Submodule.span ℝ≥0 {u, v} := by
    rw [Submodule.mem_span_pair]
    exact ⟨⟨t, ht.le⟩, ⟨k, hk0⟩, hdecomp.symm⟩
  have hadd := InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span hw hmem
  rw [InnerProductGeometry.angle_neg_left] at hang
  have hnonneg := InnerProductGeometry.angle_nonneg u w
  rw [InnerProductGeometry.angle_comm w v] at hadd
  linarith

end P5

/-- **`Postulate5` holds in the plane.** The angle bound gives a positive parameter on
the ray from B through A, and its intersection with CD lies strictly on A's side of BC. -/
theorem Postulate5 : Hand.Postulate5 plane := by
  intro A B C D L M N hAL hBL hBM hCM hCN hDN hBC hAD hang
  have hAB : A ≠ B := fun h => hAD.left_notMem (h ▸ hBM)
  have hDC : D ≠ C := fun h => hAD.right_notMem (h ▸ hCM)
  have hang' : EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C D < π := by
    change angle A B C + angle B C D <
      (⟨π / 2, by positivity⟩ : ℝ≥0) + (⟨π / 2, by positivity⟩ : ℝ≥0) at hang
    simp only [angle, hAB, hBC.symm, hBC, hDC, or_self, ↓reduceIte] at hang
    have hreal := NNReal.coe_lt_coe.2 hang
    change EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C D <
      π / 2 + π / 2 at hreal
    linarith
  obtain ⟨t, k, ht, hdecomp⟩ := P5.sameSide_decomposition hBM hCM hBC hAD
  have hk : k < 0 := by
    apply P5.coefficient_neg ht (sub_ne_zero.2 hDC) hdecomp
    simpa only [EuclideanGeometry.angle, vsub_eq_sub, neg_sub] using hang'
  let r : ℝ := -1 / k
  have hr : 0 < r := div_pos_of_neg_of_neg (by norm_num) hk
  have hrk : r * k = -1 := div_mul_cancel₀ _ hk.ne
  let E : Plane := (r * t) • (A - B) +ᵥ B
  have hEN : E = r • (D - C) +ᵥ C := by
    dsimp [E]
    change (r * t) • (A - B) + B = r • (D - C) + C
    rw [hdecomp, smul_add, ← mul_smul, ← mul_smul, hrk, neg_one_smul]
    abel
  refine ⟨E, ?_, ?_, ?_⟩
  · exact AffineSubspace.vadd_mem_of_mem_direction
      (L.1.direction.smul_mem (r * t) (AffineSubspace.vsub_mem_direction hAL hBL)) hBL
  · rw [hEN]
    exact AffineSubspace.vadd_mem_of_mem_direction
      (N.1.direction.smul_mem r (AffineSubspace.vsub_mem_direction hDN hCN)) hCN
  · exact AffineSubspace.sSameSide_smul_vsub_vadd_left hAD.left_notMem hBM hBM
      (mul_pos hr ht)

end Model.Euclidean
