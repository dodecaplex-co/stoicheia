module

public import Model.Euclidean
public import Model.Laws.order

/-!
# Betweenness and straight lines, in the plane

A line is a one-dimensional affine subspace and `Between A B C` is Mathlib's `Sbtw ℝ A B C`.
Betweenness puts each point in the affine span of the other two, so membership passes
to any line containing them. For the extension from A and B to C, strictness excludes
A = B, where weak betweenness alone would not suffice. Three points on a line are
collinear; their three given inequalities make the weak betweenness alternatives strict.
We thank Joseph Myers for Mathlib's betweenness lemmas, which supply these steps.
-/

@[expose] public section

namespace Model.Euclidean

/-- **`on_line_of_between` holds in the plane** (Between 2). -/
theorem on_line_of_between : Hand.on_line_of_between plane := by
  intro A B C L h hA hB
  change Sbtw ℝ A B C at h
  change A ∈ L.1 at hA
  change B ∈ L.1 at hB
  change C ∈ L.1
  exact affineSpan_pair_le_of_mem_of_mem hA hB h.right_mem_affineSpan

/-- **`on_line_of_between_ends` holds in the plane** (Between 3). -/
theorem on_line_of_between_ends : Hand.on_line_of_between_ends plane := by
  intro A B C L h hA hC
  change Sbtw ℝ A B C at h
  change A ∈ L.1 at hA
  change C ∈ L.1 at hC
  change B ∈ L.1
  exact affineSpan_pair_le_of_mem_of_mem hA hC h.wbtw.mem_affineSpan

/-- **`between_cases` holds in the plane** (Between 6). -/
theorem between_cases : Hand.between_cases plane := by
  intro A B C L hAB hBC hAC hA hB hC
  change A ∈ L.1 at hA
  change B ∈ L.1 at hB
  change C ∈ L.1 at hC
  change Sbtw ℝ A B C ∨ Sbtw ℝ B A C ∨ Sbtw ℝ A C B
  have hL : Collinear ℝ (L.1 : Set Plane) := by
    rw [collinear_iff_finrank_le_one, ← direction_affineSpan,
      AffineSubspace.affineSpan_coe, L.2]
  have hABC : Collinear ℝ ({A, B, C} : Set Plane) := hL.subset (by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hA, hB, hC⟩)
  rcases hABC.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact Or.inl ⟨h, hAB.symm, hBC⟩
  · exact Or.inr (Or.inr ⟨h.symm, hAC.symm, hBC.symm⟩)
  · exact Or.inr (Or.inl ⟨h.symm, hAB, hAC⟩)

end Model.Euclidean
