module

public import Model.Euclidean.CircleSides
public import Model.Laws.circles
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finitely many points leave room in the plane

Each proof gives an injective family indexed by the natural numbers, so its range is
infinite. A finite list, even one with repetitions, cannot contain that range. This
single argument covers empty lists and lists containing any of the first points chosen.

For the plane, take the non-negative integer multiples of the horizontal unit vector.
For a side of a line, first choose a point P on the line. The vectors from P to B,
scaled by n + 1, stay on B's side; scaled by -(n + 1), they reach the opposite side.
The line has a point because its direction has dimension one. Since B is off the line,
its vector from P is nonzero, which makes both families injective. The strict opposite
side relation supplies both exclusions from the line and the failure of same side.

For a circle of radius r and centre O, the points at distances r / (n + 2) along the
horizontal ray from O lie inside, and those at distances r + n + 1 lie outside. The
positive radius makes the first family injective and places every point of it strictly
inside. The second family is strictly farther than the radius, hence neither inside
nor on the circle.

For the circumference, scale each vector (1, n) to length r and translate it to O.
Every vector has first coordinate one and is nonzero. If two resulting points agree,
their first coordinates give equal scale factors, and their second coordinates give
equal indices. The factors are positive because r is positive. Thus even a very small
circle has infinitely many points; a radius of zero is excluded by the type of circles.

Our thanks to Joseph Myers for Mathlib's sides and spheres, to Joseph Myers, Sébastien
Gouëzel and Heather Macbeth for its Euclidean spaces, and to Johannes Hölzl, Mario
Carneiro and Kyle Miller for the finite-set development used to escape the list.
-/

@[expose] public section

namespace Model.Euclidean

/-- An injective sequence has a member outside any finite list. Its range is infinite,
so Mathlib's infinite-set lemma applies to the list's finite set of entries. -/
theorem exists_not_mem_of_injective {X : Type*} (f : ℕ → X)
    (hf : Function.Injective f) (avoid : List X) : ∃ n, f n ∉ avoid := by
  classical
  obtain ⟨A, ⟨n, rfl⟩, hA⟩ :=
    (Set.infinite_range_of_injective hf).exists_notMem_finset avoid.toFinset
  exact ⟨n, by simpa using hA⟩

/-- A line contains a point: the empty affine subspace has direction of dimension zero. -/
theorem line_nonempty (L : Line) : (L.1 : Set Plane).Nonempty := by
  apply L.1.nonempty_iff_ne_bot.mpr
  intro h
  have hdim := L.2
  rw [h, AffineSubspace.direction_bot] at hdim
  simp at hdim

/-- Distinct scalars give distinct points along a nonzero vector from a fixed point. -/
theorem scaled_point_injective {f : ℕ → ℝ} (hf : Function.Injective f)
    {v : Plane} (hv : v ≠ 0) (P : Plane) :
    Function.Injective (fun n => f n • v +ᵥ P) := by
  intro n m h
  exact hf (smul_left_injective ℝ hv (vadd_right_cancel P h))

/-- The horizontal unit vector, used to place points at specified distances. -/
noncomputable def horizontalUnit : Plane := !₂[1, 0]

/-- The horizontal unit vector has length one. -/
theorem norm_horizontalUnit : ‖horizontalUnit‖ = 1 := by
  simp [horizontalUnit, EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- A vector of length one is nonzero. -/
theorem horizontalUnit_ne_zero : horizontalUnit ≠ 0 := by
  intro h
  have hn := norm_horizontalUnit
  simp [h] at hn

/-- **The plane has a point outside any finite list.** Integer multiples of a unit
vector form an injective sequence. -/
theorem exists_point : Hand.exists_point plane := by
  intro avoid
  let f : ℕ → Plane := fun n => (n : ℝ) • horizontalUnit +ᵥ (0 : Plane)
  have hf : Function.Injective f :=
    scaled_point_injective Nat.cast_injective horizontalUnit_ne_zero 0
  obtain ⟨n, hn⟩ := exists_not_mem_of_injective f hf avoid
  exact ⟨f n, hn⟩

/-- **A given side of a line has a point outside any finite list.** Positive multiples
of the vector from a point of the line to B remain strictly on B's side. Our thanks to
Joseph Myers for Mathlib's lemmas on sides of affine subspaces. -/
theorem exists_point_same_side : Hand.exists_point_same_side plane := by
  intro B L hB avoid
  obtain ⟨P, hP⟩ := line_nonempty L
  have hv : B -ᵥ P ≠ 0 := vsub_ne_zero.mpr (fun h => hB (h ▸ hP))
  let f : ℕ → Plane := fun n => ((n : ℝ) + 1) • (B -ᵥ P) +ᵥ P
  have ht : Function.Injective (fun n : ℕ => (n : ℝ) + 1) := by
    intro n m h
    exact Nat.cast_injective (add_right_cancel h)
  have hf : Function.Injective f := scaled_point_injective ht hv P
  obtain ⟨n, hn⟩ := exists_not_mem_of_injective f hf avoid
  refine ⟨f n, ?_, hn⟩
  exact AffineSubspace.sSameSide_smul_vsub_vadd_left hB hP hP (by positivity)

/-- **The opposite side has a point outside any finite list.** Negative multiples
of the vector from a point of the line to B lie off the line and not on B's side.
Our thanks to Joseph Myers for Mathlib's strict opposite-side relation and its lemmas. -/
theorem exists_point_opposite_side : Hand.exists_point_opposite_side plane := by
  intro B L hB avoid
  obtain ⟨P, hP⟩ := line_nonempty L
  have hv : B -ᵥ P ≠ 0 := vsub_ne_zero.mpr (fun h => hB (h ▸ hP))
  let f : ℕ → Plane := fun n => (-((n : ℝ) + 1)) • (B -ᵥ P) +ᵥ P
  have ht : Function.Injective (fun n : ℕ => -((n : ℝ) + 1)) := by
    intro n m h
    exact Nat.cast_injective (add_right_cancel (neg_injective h))
  have hf : Function.Injective f := scaled_point_injective ht hv P
  obtain ⟨n, hn⟩ := exists_not_mem_of_injective f hf avoid
  have hs : L.1.SOppSide (f n) B :=
    AffineSubspace.sOppSide_smul_vsub_vadd_left hB hP hP (neg_neg_of_pos (by positivity))
  exact ⟨f n, ⟨hs.left_notMem, hs.right_notMem, hs.not_sSameSide⟩, hn⟩

/-- **The interior has a point outside any finite list.** The distinct distances
r / (n + 2) from the centre are positive and strictly less than the radius r. -/
theorem exists_point_inside_circle : Hand.exists_point_inside_circle plane := by
  intro α avoid
  let f : ℕ → Plane := fun n => (α.1.radius / ((n : ℝ) + 2)) • horizontalUnit
    +ᵥ α.1.center
  have ht : Function.Injective (fun n : ℕ => α.1.radius / ((n : ℝ) + 2)) := by
    intro n m h
    have hcross := (div_eq_div_iff (by positivity : (n : ℝ) + 2 ≠ 0)
      (by positivity : (m : ℝ) + 2 ≠ 0)).mp h
    have hnm : (n : ℝ) + 2 = (m : ℝ) + 2 :=
      (mul_left_cancel₀ α.2.ne' hcross).symm
    exact Nat.cast_injective (add_right_cancel hnm)
  have hf : Function.Injective f :=
    scaled_point_injective ht horizontalUnit_ne_zero α.1.center
  obtain ⟨n, hn⟩ := exists_not_mem_of_injective f hf avoid
  refine ⟨f n, ?_, hn⟩
  rw [insideCircle_iff]
  dsimp only [f]
  rw [dist_eq_norm_vsub, vadd_vsub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos α.2 (by positivity)), norm_horizontalUnit, mul_one]
  apply div_lt_self α.2
  have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- **The exterior has a point outside any finite list.** The distances r + n + 1
from the centre are distinct and strictly greater than the radius r. -/
theorem exists_point_outside_circle : Hand.exists_point_outside_circle plane := by
  intro α avoid
  let f : ℕ → Plane := fun n => (α.1.radius + (n : ℝ) + 1) • horizontalUnit
    +ᵥ α.1.center
  have ht : Function.Injective (fun n : ℕ => α.1.radius + (n : ℝ) + 1) := by
    intro n m h
    exact Nat.cast_injective (add_left_cancel (add_right_cancel h))
  have hf : Function.Injective f :=
    scaled_point_injective ht horizontalUnit_ne_zero α.1.center
  obtain ⟨n, hn⟩ := exists_not_mem_of_injective f hf avoid
  have hd : α.1.radius < dist (f n) α.1.center := by
    dsimp only [f]
    rw [dist_eq_norm_vsub, vadd_vsub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by have hr := α.2; positivity), norm_horizontalUnit, mul_one]
    have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  refine ⟨f n, ⟨?_, ?_⟩, hn⟩
  · exact not_lt.mpr hd.le
  · exact fun h => hd.ne' (onCircle_iff.mp h)

/-- The vectors (1, n), whose distinct directions give distinct points on a circle. -/
noncomputable def circleDirection (n : ℕ) : Plane := !₂[1, (n : ℝ)]

/-- The first coordinate of each direction is one, so none is the zero vector. -/
theorem circleDirection_ne_zero (n : ℕ) : circleDirection n ≠ 0 := by
  intro h
  have := congrArg (fun v : Plane => v 0) h
  simp [circleDirection] at this

/-- Normalizing (1, n) to a positive radius preserves distinctness. Equality of first
coordinates fixes the scale factor; equality of second coordinates then fixes n. -/
theorem circle_family_injective (α : Circle) :
    Function.Injective (fun n : ℕ =>
      (α.1.radius / ‖circleDirection n‖) • circleDirection n +ᵥ α.1.center) := by
  intro n m h
  have hv := vadd_right_cancel α.1.center h
  have h0 := congrArg (fun v : Plane => v 0) hv
  have h1 := congrArg (fun v : Plane => v 1) hv
  simp only [PiLp.smul_apply, smul_eq_mul, circleDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one] at h0 h1
  have hn : 0 < α.1.radius / ‖circleDirection n‖ :=
    div_pos α.2 (norm_pos_iff.mpr (circleDirection_ne_zero n))
  have hnm : (n : ℝ) = (m : ℝ) := by
    rw [← h0] at h1
    exact mul_left_cancel₀ hn.ne' h1
  exact Nat.cast_injective hnm

/-- **The circumference has a point outside any finite list.** The vectors (1, n),
scaled to the radius and based at the centre, give infinitely many distinct points.
Our thanks to Joseph Myers, Sébastien Gouëzel and Heather Macbeth for Mathlib's Euclidean
spaces, and to Joseph Myers for its spheres. -/
theorem exists_point_on_circle : Hand.exists_point_on_circle plane := by
  intro α avoid
  let f : ℕ → Plane := fun n =>
    (α.1.radius / ‖circleDirection n‖) • circleDirection n +ᵥ α.1.center
  obtain ⟨n, hn⟩ := exists_not_mem_of_injective f (circle_family_injective α) avoid
  exact ⟨f n, onCircle_radius_smul (circleDirection_ne_zero n), hn⟩

end Model.Euclidean
