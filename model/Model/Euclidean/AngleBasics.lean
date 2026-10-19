module

public import Model.Euclidean
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# The angle and the line, as the angle laws use them

The plane reads `ang A B C` as Mathlib's unoriented angle when `A` and `C` both differ from
`B`, and as 0 when either is `B` (`Model/Euclidean.lean`). These lemmas are the bridge: the
reading at a repeated point, the reading as Mathlib's angle when both arms are nonzero, and
the line through two points as the line of Mathlib's `line[ℝ, A, B]`.
-/

@[expose] public section

namespace Model.Euclidean

open scoped NNReal Real

/-- At a repeated point, `A = B`, the angle is 0. -/
@[simp] theorem angle_self_left (A C : Plane) : angle A A C = 0 := by
  simp [angle]

/-- At a repeated point, `C = B`, the angle is 0. -/
@[simp] theorem angle_self_right (A B : Plane) : angle A B B = 0 := by
  simp [angle]

/-- With both arms nonzero, the angle is Mathlib's unoriented angle. -/
theorem coe_angle_of_ne {A B C : Plane} (hA : A ≠ B) (hC : C ≠ B) :
    (angle A B C : ℝ) = EuclideanGeometry.angle A B C := by
  simp [angle, hA, hC]
  rfl

/-- Two angles with nonzero arms are equal exactly when Mathlib's angles are. -/
theorem angle_eq_angle_iff {A B C D E F : Plane} (hA : A ≠ B) (hC : C ≠ B) (hD : D ≠ E)
    (hF : F ≠ E) :
    angle A B C = angle D E F ↔ EuclideanGeometry.angle A B C = EuclideanGeometry.angle D E F := by
  rw [← NNReal.coe_inj, coe_angle_of_ne hA hC, coe_angle_of_ne hD hF]

/-- The line through two distinct points. -/
noncomputable def lineThrough {A B : Plane} (h : A ≠ B) : Line :=
  ⟨line[ℝ, A, B], by
    rw [direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (vsub_ne_zero.2 h)⟩

theorem mem_lineThrough_left {A B : Plane} (h : A ≠ B) : A ∈ (lineThrough h).1 :=
  left_mem_affineSpan_pair ℝ A B

theorem mem_lineThrough_right {A B : Plane} (h : A ≠ B) : B ∈ (lineThrough h).1 :=
  right_mem_affineSpan_pair ℝ A B

/-- A line through two distinct points is Mathlib's line through them. -/
theorem line_eq_affineSpan {L : Line} {A B : Plane} (h : A ≠ B) (hA : A ∈ L.1) (hB : B ∈ L.1) :
    L.1 = line[ℝ, A, B] := by
  have hle : line[ℝ, A, B] ≤ L.1 := affineSpan_pair_le_of_mem_of_mem hA hB
  have hdir : (line[ℝ, A, B]).direction = L.1.direction := by
    apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
    rw [L.2]
    exact (lineThrough h).2
  exact (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir
    ⟨A, left_mem_affineSpan_pair ℝ A B⟩ hle).symm

end Model.Euclidean
