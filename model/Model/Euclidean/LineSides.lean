module

public import Model.Euclidean
public import Model.Euclidean.CircleSides
public import Model.Euclidean.LineCircle
public import Model.Laws.intersections
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Lines separating points on or inside a circle, in the plane

When A and B lie on opposite sides of a line L, the straight segment joining them
crosses L strictly between them. Any line through A and B contains that crossing point,
and differs from L because A is not on L. This proves Intersection 1.

A point strictly between two points on or inside a circle is strictly inside it:
its distance from the centre is less than the greater of the endpoints' distances.
This is Circle 2, the strict convexity of the Euclidean disk. It also proves Circle 3:
if A is on or inside and C, between A and B, is not inside, then B must be outside.
For Intersection 2, a line separating two points on or inside the circle therefore
passes through an inside point, and Intersection 3 (`Model/Euclidean/LineCircle.lean`)
then gives two distinct points where the line cuts the circle.

For Circle 4, two distinct circles with two distinct common points have distinct
centres: equal centres and a common point would fix the same radius. The line of
centres is the perpendicular bisector of the common points, so those points lie on
opposite sides of it, and cannot lie on the same side.

Mathlib's betweenness, sides, spheres and strict-convexity distance lemma are the work
of Joseph Myers. Its convexity of inner product spaces is due to Zhouhang Zhou,
Sébastien Gouëzel and Frédéric Dupuis; its perpendicular bisector, to Yury Kudryashov
and Joseph Myers. Our thanks to them.
-/

@[expose] public section

namespace Model.Euclidean

/-- **Intersection 1 holds in the plane.** A line through points on opposite sides of
another line differs from that line and meets it between the two points. -/
theorem lines_meet_of_opposite_sides : Hand.lines_meet_of_opposite_sides plane := by
  intro A B L M h hAM hBM
  have hside : L.1.SOppSide A B :=
    (sSameSide_or_sOppSide L.2 h.1 h.2.1).resolve_left h.2.2
  obtain ⟨X, hXL, hAXB⟩ := hside.exists_sbtw
  refine ⟨?_, X, hXL, ?_⟩
  · rintro rfl
    exact h.1 hAM
  · exact (affineSpan_pair_le_of_mem_of_mem hAM hBM) hAXB.wbtw.mem_affineSpan

/-- **Circle 2 holds in the plane.** Every point strictly between two points on or
inside a circle is strictly inside it, by the strict convexity of the Euclidean disk. -/
theorem inside_of_between : Hand.inside_of_between plane := by
  intro A B C α hA hB hACB
  rw [insideCircle_iff, onCircle_iff] at hA hB
  change Sbtw ℝ A C B at hACB
  exact (hACB.dist_lt_max_dist α.1.center).trans_le
    (max_le (le_of_lt_or_eq hA) (le_of_lt_or_eq hB))

/-- A line separating two points on or inside a circle contains a point strictly
inside the circle, at its crossing with the segment joining the two points. -/
theorem exists_inside_of_opposite_sides {A B : Plane} {L : Line} {α : Circle}
    (hA : plane.InsideCircle A α ∨ plane.OnCircle A α)
    (hB : plane.InsideCircle B α ∨ plane.OnCircle B α)
    (h : plane.OppositeSides A B L) :
    ∃ X : Plane, X ∈ L.1 ∧ plane.InsideCircle X α := by
  have hside : L.1.SOppSide A B :=
    (sSameSide_or_sOppSide L.2 h.1 h.2.1).resolve_left h.2.2
  obtain ⟨X, hXL, hAXB⟩ := hside.exists_sbtw
  exact ⟨X, hXL, inside_of_between hA hB hAXB⟩

/-- **Intersection 2 follows from Intersection 3 in the plane.** The separating line
passes through an inside point, so the supplied law gives two distinct circle points. -/
theorem line_meets_circle_of_opposite_sides_of_inside
    (h3 : Hand.line_meets_circle_of_inside plane) :
    Hand.line_meets_circle_of_opposite_sides plane := by
  intro A B L α hA hB h
  obtain ⟨X, hXL, hXα⟩ := exists_inside_of_opposite_sides hA hB h
  exact h3 hXα hXL

/-- **Intersection 2 holds in the plane.** A line separating two points on or inside a
circle cuts it in two points: it passes through a point inside, and Intersection 3 does
the rest. -/
theorem line_meets_circle_of_opposite_sides : Hand.line_meets_circle_of_opposite_sides plane :=
  line_meets_circle_of_opposite_sides_of_inside line_meets_circle_of_inside

/-- **Circle 3 holds in the plane.** If A is on or inside a circle and C, strictly
between A and B, is not inside, then B is outside: either other position for B would
put C strictly inside by Circle 2. -/
theorem outside_of_between : Hand.outside_of_between plane := by
  intro A B C α hA hC hACB
  constructor
  · intro hB
    exact hC (inside_of_between hA (Or.inl hB) hACB)
  · intro hB
    exact hC (inside_of_between hA (Or.inr hB) hACB)

/-- **Circle 4 holds in the plane.** Two distinct common points of distinct circles
cannot lie on the same side of the line through their centres: that line is the
perpendicular bisector of the common points. -/
theorem not_same_side_of_circles_meet : Hand.not_same_side_of_circles_meet plane := by
  intro A B C D L α β hαβ hCα hCβ hDα hDβ hCD hA hB hAL hBL
  rw [centre_iff] at hA hB
  subst A
  subst B
  have hc : α.1.center ≠ β.1.center := by
    intro hc
    exact hαβ (circle_eq_of_center_eq_of_common_point hc hCα hCβ)
  have hL := line_eq_perpBisector L.2 hc hCD hAL hBL
    ((onCircle_iff.1 hCα).trans (onCircle_iff.1 hDα).symm)
    ((onCircle_iff.1 hCβ).trans (onCircle_iff.1 hDβ).symm)
  have hCDside : L.1.SOppSide C D := by
    rw [hL]
    exact (sbtw_midpoint_of_ne ℝ hCD).sOppSide_of_notMem_of_mem
      (by simpa only [AffineSubspace.left_mem_perpBisector] using hCD)
      (AffineSubspace.midpoint_mem_perpBisector C D)
  exact hCDside.not_sSameSide

end Model.Euclidean
