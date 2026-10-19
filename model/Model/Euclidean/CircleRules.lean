module

public import Model.Laws.circles
public import Model.Euclidean.CircleSides
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Geometry.Euclidean.Sphere.Basic

/-!
# Inside, outside and between, in the plane

System E's Circle 1 to 3 follow from strict convexity of the disc. A point strictly
between two distinct points of a closed disc lies in its interior. On a line through
two points of the circumference, an interior point must therefore lie between them:
either other ordering would put a circumference point inside the disc. Mathlib proves
this implication for collinear points. Membership in our one-dimensional line supplies
collinearity, and the strict distance inequality excludes either endpoint. Circle 3
then follows by contradiction from Circle 2, including when the first point is on the
circumference. Strict betweenness excludes repeated endpoints throughout.

For Circle 4, a common point and coincident centres would force equal radii and equal
circles, contrary to the hypothesis. With distinct centres, the line through them is the
perpendicular bisector of the two common points, as proved in `CircleSides`. Their
midpoint lies on that line, and the points lie strictly on opposite sides of it.

A circle does meet itself in the sense of `CirclesMeet`: `circlesMeet_self` takes a point
of its circumference and reflects it in the centre. Positive radius makes the two ends
of this diameter distinct. Circle 4 explicitly excludes equal circles; its conclusion
does not extend to arbitrary pairs of common points on a circle equal to itself.
-/

@[expose] public section

namespace Model.Euclidean

/-- **Circle 1 holds in the plane.** The one-dimensional line makes the three points
collinear, and strict convexity puts the interior point between the circumference points.
We thank Joseph Myers for Mathlib's collinearity and betweenness results, and Yaël Dillies
and Yury Kudryashov for its strict convexity theory. -/
theorem between_of_inside_chord : Hand.between_of_inside_chord plane := by
  intro A B C L α hA hB hC hAα hBα hCα hBC
  have hL : Collinear ℝ (L.1 : Set Plane) := by
    rw [collinear_iff_finrank_le_one, ← AffineSubspace.direction_eq_vectorSpan, L.2]
  have hcol : Collinear ℝ ({B, A, C} : Set Plane) := by
    apply hL.subset
    intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl | rfl
    · exact hB
    · exact hA
    · exact hC
  exact hcol.sbtw_of_dist_eq_of_dist_lt (onCircle_iff.1 hBα) hAα
    (onCircle_iff.1 hCα) hBC

/-- **Circle 2 holds in the plane.** Strict betweenness gives a distance from the centre
less than the larger endpoint distance. We thank Joseph Myers for this betweenness
lemma, Yaël Dillies and Yury Kudryashov for Mathlib's strict convexity theory, and
Zhouhang Zhou, Sébastien Gouëzel and Frédéric Dupuis for its inner product space instance. -/
theorem inside_of_between : Hand.inside_of_between plane := by
  intro A B C α hA hB hACB
  have hA' : dist A α.1.center ≤ α.1.radius := by
    rcases hA with hA | hA
    · exact hA.le
    · exact (onCircle_iff.1 hA).le
  have hB' : dist B α.1.center ≤ α.1.radius := by
    rcases hB with hB | hB
    · exact hB.le
    · exact (onCircle_iff.1 hB).le
  exact (hACB.dist_lt_max_dist α.1.center).trans_le (max_le hA' hB')

/-- **Circle 3 holds in the plane.** If the far endpoint were inside or on the circle,
Circle 2 would put the intervening point inside it, contrary to the hypothesis. -/
theorem outside_of_between : Hand.outside_of_between plane := by
  intro A B C α hA hC hACB
  exact ⟨fun hB => hC (inside_of_between hA (Or.inl hB) hACB),
    fun hB => hC (inside_of_between hA (Or.inr hB) hACB)⟩

/-- **Circle 4 holds in the plane.** Distinct circles sharing two distinct points have
distinct centres; their line is the perpendicular bisector of those points. We thank
Yury Kudryashov and Joseph Myers for Mathlib's perpendicular bisector theory, and Joseph
Myers for its betweenness and side relations, used through `CircleSides`. -/
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
  have hside : L.1.SOppSide C D := by
    rw [hL]
    exact (sbtw_midpoint_of_ne ℝ hCD).sOppSide_of_notMem_of_mem
      (by simpa only [AffineSubspace.left_mem_perpBisector] using hCD)
      (AffineSubspace.midpoint_mem_perpBisector C D)
  exact hside.not_sSameSide

/-- **A circle meets itself in two distinct points.** A point and its reflection in the
centre form a diameter, whose endpoints differ because the radius is positive. We thank
Joseph Myers for Mathlib's sphere and diameter results. This is the equal-circle case
allowed by `CirclesMeet`, and excluded by Circle 4's distinct-circle hypothesis. -/
theorem circlesMeet_self (α : Circle) : plane.CirclesMeet α α := by
  obtain ⟨P, hP⟩ := α.1.nonempty_iff.2 α.2.le
  have hdiam : α.1.IsDiameter P (Equiv.pointReflection α.1.center P) :=
    EuclideanGeometry.Sphere.isDiameter_iff_left_mem_and_pointReflection_center_left.2
      ⟨hP, rfl⟩
  exact ⟨P, _, hdiam.left_ne_right_iff_radius_pos.2 α.2,
    hP, hP, hdiam.right_mem, hdiam.right_mem⟩

end Model.Euclidean
