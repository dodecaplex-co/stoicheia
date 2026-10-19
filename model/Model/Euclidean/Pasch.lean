module

public import Model.Euclidean.Sides

/-!
# Pasch's four rules, in the plane

Pasch 4 finds a point of L between A and C. It also lies on M, so the uniqueness of
the intersection of two distinct lines identifies it with B.

The proofs use Mathlib's sides and betweenness, the work of Joseph Myers, with thanks.
-/

@[expose] public section

namespace Model.Euclidean

/-- Two lines sharing two distinct points are equal. -/
private theorem line_eq_of_common_points {L M : Line} {A B : Plane}
    (hAB : A ≠ B) (hAL : A ∈ L.1) (hBL : B ∈ L.1)
    (hAM : A ∈ M.1) (hBM : B ∈ M.1) : L = M := by
  have hL : L.1.direction = ℝ ∙ (B -ᵥ A) :=
    eq_span_singleton_of_mem_of_finrank_eq_one L.2
      (AffineSubspace.vsub_mem_direction hBL hAL) (vsub_ne_zero.2 hAB.symm)
  have hM : M.1.direction = ℝ ∙ (B -ᵥ A) :=
    eq_span_singleton_of_mem_of_finrank_eq_one M.2
      (AffineSubspace.vsub_mem_direction hBM hAM) (vsub_ne_zero.2 hAB.symm)
  exact Subtype.ext (AffineSubspace.ext_of_direction_eq (hL.trans hM.symm) ⟨A, hAL, hAM⟩)

/-- **Pasch 1 holds in the plane.**
A crossing between A and B would also be a crossing between A and C. -/
theorem pasch1 : Hand.pasch1 plane := by
  intro A B C L hABC hAC
  rw [between_iff] at hABC
  rw [sameSide_iff] at hAC ⊢
  have hB : B ∉ L.1 := fun hBL => hAC.not_wOppSide (hABC.wbtw.wOppSide₁₃ hBL)
  rcases sSameSide_or_sOppSide L.2 hAC.left_notMem hB with hAB | hAB
  · exact hAB
  · obtain ⟨X, hXL, hAXB⟩ := AffineSubspace.wOppSide_iff_exists_wbtw.1 hAB.wOppSide
    exact (hAC.not_wOppSide ((hABC.wbtw.trans_left hAXB).wOppSide₁₃ hXL)).elim

/-- **Pasch 2 holds in the plane.**
Betweenness gives weak same-sidedness; if C lay on L, B would lie on L too. -/
theorem pasch2 : Hand.pasch2 plane := by
  intro A B C L hABC hA hB
  rw [between_iff] at hABC
  rw [onLine_iff] at hA hB
  rw [sameSide_iff]
  refine ⟨hABC.wbtw.wSameSide₂₃ hA, hB, ?_⟩
  intro hC
  exact hB ((affineSpan_pair_le_of_mem_of_mem hA hC) hABC.wbtw.mem_affineSpan)

/-- **Pasch 3 holds in the plane.**
A point of L between A and C puts them weakly on opposite sides, even if A lies on L. -/
theorem pasch3 : Hand.pasch3 plane := by
  intro A B C L hABC hB
  rw [between_iff] at hABC
  rw [onLine_iff] at hB
  rw [sameSide_iff]
  exact (hABC.wbtw.wOppSide₁₃ hB).not_sSameSide

/-- **Pasch 4 holds in the plane.**
A and C lie off L and on opposite sides of it. Their segment meets L at B, since
two distinct lines cannot share another point. -/
theorem pasch4 : Hand.pasch4 plane := by
  intro A B C L M hLM hBL hBM hAM hCM _hAC hAB hCB hside
  rw [onLine_iff] at hBL hBM hAM hCM
  rw [sameSide_iff] at hside
  rw [between_iff]
  have hAL : A ∉ L.1 := fun hAL =>
    hLM (line_eq_of_common_points hAB hAL hBL hAM hBM)
  have hCL : C ∉ L.1 := fun hCL =>
    hLM (line_eq_of_common_points hCB hCL hBL hCM hBM)
  have hopp : L.1.SOppSide A C :=
    (sSameSide_or_sOppSide L.2 hAL hCL).resolve_left hside
  obtain ⟨X, hXL, hAXC⟩ := AffineSubspace.wOppSide_iff_exists_wbtw.1 hopp.wOppSide
  have hXM : X ∈ M.1 :=
    (affineSpan_pair_le_of_mem_of_mem hAM hCM) hAXC.mem_affineSpan
  have hXB : X = B := by
    by_contra hXB
    exact hLM (line_eq_of_common_points hXB hXL hBL hXM hBM)
  subst X
  exact ⟨hAXC, hAB.symm, hCB.symm⟩

end Model.Euclidean
