module

public import Model.Euclidean
public import Model.Laws.order

/-!
# Betweenness, in the plane

`Between A B C` reads as Mathlib's strict betweenness, `Sbtw ℝ A B C`: B lies on the
segment from A to C and is neither end. Joseph Myers's betweenness lemmas in Mathlib,
with our thanks, give symmetry, distinctness and Between 4 and 5 directly. Between 7 takes
one step more. C and D both lie on the ray from A through B, beyond B, so one of them, say
C, is weakly between A and the other; then B is between A and C, and C between B and D,
so B cannot also be strictly between C and D. That the ray has a direction at all needs
A and B to differ, which strict betweenness gives, and the weak comparison of C and D
covers the case C = D, where `Sbtw ℝ C B C` is false because its ends coincide.
-/

@[expose] public section

namespace Model.Euclidean

/-- **`between_symm` holds in the plane** (Between 1). -/
theorem between_symm : Hand.between_symm plane := by
  intro A B C
  change Sbtw ℝ A B C → Sbtw ℝ C B A
  exact Sbtw.symm

/-- **`ne_of_between` holds in the plane** (Between 1). -/
theorem ne_of_between : Hand.ne_of_between plane := by
  intro A B C
  change Sbtw ℝ A B C → A ≠ B
  exact Sbtw.left_ne

/-- **`ne_of_between_ends` holds in the plane** (Between 1). -/
theorem ne_of_between_ends : Hand.ne_of_between_ends plane := by
  intro A B C
  change Sbtw ℝ A B C → A ≠ C
  exact Sbtw.left_ne_right

/-- **`not_between_of_between` holds in the plane** (Between 1). -/
theorem not_between_of_between : Hand.not_between_of_between plane := by
  intro A B C
  change Sbtw ℝ A B C → ¬ Sbtw ℝ B A C
  intro hABC hBAC
  exact hABC.not_swap_left hBAC.wbtw

/-- **`between_of_between_left` holds in the plane** (Between 4). -/
theorem between_of_between_left : Hand.between_of_between_left plane := by
  intro A B C D
  change Sbtw ℝ A B C → Sbtw ℝ A D B → Sbtw ℝ A D C
  exact Sbtw.trans_left

/-- **`between_of_between_right` holds in the plane** (Between 5). -/
theorem between_of_between_right : Hand.between_of_between_right plane := by
  intro A B C D
  change Sbtw ℝ A B C → Sbtw ℝ B C D → Sbtw ℝ A B D
  exact Sbtw.trans_expand_left

/-- **`not_between_of_between_between` holds in the plane** (Between 7). -/
theorem not_between_of_between_between : Hand.not_between_of_between_between plane := by
  intro A B C D
  change Sbtw ℝ A B C → Sbtw ℝ A B D → ¬ Sbtw ℝ C B D
  intro hABC hABD hCBD
  have hAB : B -ᵥ A ≠ 0 := vsub_ne_zero.2 hABC.ne_left
  have hCD : SameRay ℝ (C -ᵥ A) (D -ᵥ A) :=
    hABC.wbtw.sameRay_vsub_left.symm.trans hABD.wbtw.sameRay_vsub_left
      (fun h => (hAB h).elim)
  rcases wbtw_total_of_sameRay_vsub_left hCD with hACD | hADC
  · exact hCBD.not_swap_left (hACD.trans_left_right hABC.wbtw)
  · exact hCBD.symm.not_swap_left (hADC.trans_left_right hABD.wbtw)

end Model.Euclidean
