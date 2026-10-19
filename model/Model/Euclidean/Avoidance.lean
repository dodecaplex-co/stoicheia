module

public import Model.Euclidean.Incidence
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Points avoiding a finite list, in the plane

Each rule chooses a point from an infinite set, so any finite list can be avoided.
The plane is infinite. A line has a point and a nonzero direction vector, since its
direction has dimension one; the real multiples of that vector give infinitely many
points on the line. Two distinct lines share at most one point, by `line_unique`
(`Model/Euclidean/Incidence.lean`). Removing their
intersection therefore still leaves infinitely many points on the first line, whether
the lines meet or are disjoint.

For points between B and C, use the line map with a real parameter strictly between
zero and one. For Postulate 2, use parameters greater than one, beyond C. These real
intervals are infinite, and the hypothesis that B and C differ makes the line map
injective. The strict parameter inequalities exclude the endpoints in both arguments.

We are grateful to Joseph Myers for Mathlib's affine maps and betweenness, to Chris
Hughes for its finite-dimensional linear algebra, to Johannes Hölzl, Mario Carneiro and
Kyle Miller for its finite and infinite sets, and to Reid Barton for its infinitude of
intervals. Their results carry these arguments.
-/

@[expose] public section

namespace Model.Euclidean

/-- An infinite set of points contains a point outside any finite list. -/
theorem avoidance_exists_mem_notMem {s : Set Plane} (hs : s.Infinite)
    (avoid : List Plane) : ∃ A ∈ s, A ∉ avoid := by
  classical
  obtain ⟨A, hA, havoid⟩ := hs.exists_notMem_finset avoid.toFinset
  exact ⟨A, hA, by simpa using havoid⟩

/-- A line contains an injective image of the real numbers along a nonzero direction. -/
theorem avoidance_line_infinite (L : Line) : (L.1 : Set Plane).Infinite := by
  have hL : L.1 ≠ ⊥ := by
    intro h
    have hdim := L.2
    rw [h, AffineSubspace.direction_bot] at hdim
    simp at hdim
  obtain ⟨P, hP⟩ := L.1.nonempty_iff_ne_bot.mpr hL
  have : Nontrivial L.1.direction := Module.nontrivial_of_finrank_eq_succ L.2
  obtain ⟨v, hv⟩ := exists_ne (0 : L.1.direction)
  have hv0 : (v : Plane) ≠ 0 := by
    intro h
    exact hv (Subtype.ext h)
  have hQ : (v : Plane) +ᵥ P ∈ L.1 :=
    AffineSubspace.vadd_mem_of_mem_direction v.property hP
  have hPQ : P ≠ (v : Plane) +ᵥ P := by
    intro h
    apply hv0
    simpa using congrArg (fun Q => Q -ᵥ P) h.symm
  exact Set.infinite_of_injective_forall_mem (AffineMap.lineMap_injective ℝ hPQ)
    (fun t => AffineMap.lineMap_mem t hP hQ)

/-- **Points 1 (`exists_point`) holds in the plane.** -/
theorem exists_point : Hand.exists_point plane := by
  intro avoid
  obtain ⟨A, _, hA⟩ := avoidance_exists_mem_notMem (Set.infinite_univ :
    (Set.univ : Set Plane).Infinite) avoid
  exact ⟨A, hA⟩

/-- **Points 2 (`exists_point_on_line`) holds in the plane.** -/
theorem exists_point_on_line : Hand.exists_point_on_line plane := by
  intro L avoid
  exact avoidance_exists_mem_notMem (avoidance_line_infinite L) avoid

/-- **`exists_point_on_line_off_line` holds in the plane.** -/
theorem exists_point_on_line_off_line : Hand.exists_point_on_line_off_line plane := by
  intro L M hLM avoid
  have hcommon : ((L.1 : Set Plane) ∩ M.1).Finite := by
    apply Set.Subsingleton.finite
    intro P hP Q hQ
    by_contra hPQ
    exact hLM (line_unique hPQ hP.1 hQ.1 hP.2 hQ.2)
  obtain ⟨A, ⟨hAL, hnot⟩, havoid⟩ :=
    avoidance_exists_mem_notMem ((avoidance_line_infinite L).sdiff hcommon) avoid
  exact ⟨A, hAL, fun hAM => hnot ⟨hAL, hAM⟩, havoid⟩

/-- **Points 3 (`exists_point_between`) holds in the plane.** -/
theorem exists_point_between : Hand.exists_point_between plane := by
  intro B C L hB hC hBC avoid
  have hinf := (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).image
    (AffineMap.lineMap_injective ℝ hBC).injOn
  obtain ⟨A, ⟨t, ht, rfl⟩, havoid⟩ := avoidance_exists_mem_notMem hinf avoid
  exact ⟨_, AffineMap.lineMap_mem t hB hC, sbtw_lineMap_iff.mpr ⟨hBC, ht⟩, havoid⟩

/-- **Postulate 2 holds in the plane.** -/
theorem Postulate2 : Hand.Postulate2 plane := by
  intro B C L hB hC hBC avoid
  have hinf := (Set.Ioi_infinite (1 : ℝ)).image
    (AffineMap.lineMap_injective ℝ hBC).injOn
  obtain ⟨A, hA, havoid⟩ := avoidance_exists_mem_notMem hinf avoid
  have hbetween : Sbtw ℝ B C A :=
    sbtw_iff_left_ne_and_right_mem_image_Ioi.mpr ⟨hBC, hA⟩
  obtain ⟨t, _, rfl⟩ := hA
  exact ⟨_, AffineMap.lineMap_mem t hB hC, hbetween, havoid⟩

end Model.Euclidean
