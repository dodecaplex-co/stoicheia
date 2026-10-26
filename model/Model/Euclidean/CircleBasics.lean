module

public import Model.Euclidean
public import Model.Laws.circles

/-!
# Centres, radii and the inside of a circle, in the plane

Postulate 3 draws the sphere with centre A and radius the distance from A to B.
The hypothesis that A and B differ makes the radius positive. Definition 15 then
says that two points at that radius have equal distances from A.

A centre is the sphere's centre, so it is unique. Its distance from itself is zero,
strictly less than the positive radius; so no point of the circle is its centre, and a radius
is not nothing, our own rule `radius_ne_zero`. An interior point cannot also be on the
circumference: its distance cannot be both less than and equal to the radius.
Two circles with the same centre and equal radii are equal as spheres and as circles.
This includes coincident circles and repeated points wherever the hypotheses allow them.

The remaining three rules compare a point's distance from the centre with a radius
already given by a point on the circle. Lengths are non-negative real distances;
coercing them to real distances preserves both equality and strict inequality.
Our thanks to Joseph Myers for Mathlib's spheres, used throughout these proofs.
-/

@[expose] public section

namespace Model.Euclidean

open scoped NNReal

/-- **Postulate 3 holds in the plane.** The distance between distinct points is a
positive radius for the circle centred at A and passing through B. -/
theorem Postulate3 : Hand.Postulate3 plane := by
  intro A B hAB
  let α : Circle := ⟨⟨A, dist A B⟩, dist_pos.mpr hAB⟩
  refine ⟨α, rfl, onCircle_iff.mpr ?_⟩
  exact dist_comm B A

/-- **Definition 15 holds in the plane.** Both distances equal the circle's radius. -/
theorem Definition15 : Hand.Definition15 plane := by
  intro A B C α hA hB hC
  rw [centre_iff] at hA
  rw [onCircle_iff] at hB hC
  change nndist A B = nndist A C
  apply NNReal.coe_injective
  simpa only [coe_nndist, hA, dist_comm] using hB.trans hC.symm

/-- **A circle has at most one centre.** Both named centres equal the sphere's centre. -/
theorem centre_unique_circles : Hand.centre_unique_circles plane := by
  intro A B α hA hB
  exact hA.trans hB.symm

/-- **The centre lies inside its circle.** The radius is positive, even when the
point being tested is the centre itself. -/
theorem centre_inside_circles : Hand.centre_inside_circles plane := by
  intro A α hA
  rw [insideCircle_iff, centre_iff.mp hA, dist_self]
  exact α.2

/-- **`radius_ne_zero` holds in the plane:** a radius is not nothing. A circle's radius is
positive by the type of circles, and a point on the circle is at that distance from the
centre, so it is not the centre. -/
theorem radius_ne_zero : Hand.radius_ne_zero plane := by
  intro A B α hA hB h
  have hAB : A = B := nndist_eq_zero.1 h
  subst hAB
  rw [centre_iff] at hA
  rw [onCircle_iff, hA, dist_self] at hB
  exact α.2.ne hB

/-- **An interior point is not on the circumference.** A strict inequality excludes
equality with the radius. -/
theorem inside_not_on_circles : Hand.inside_not_on_circles plane := by
  intro A α hA hOn
  exact (insideCircle_iff.mp hA).ne (onCircle_iff.mp hOn)

/-- **One centre and equal radii determine one circle.** We use Mathlib's equality
of spheres by centre and radius, with thanks to Joseph Myers for that development. -/
theorem circle_eq_circles : Hand.circle_eq_circles plane := by
  intro A B C α β hAα hAβ hB hC hlen
  rw [centre_iff] at hAα hAβ
  rw [onCircle_iff] at hB hC
  change nndist A B = nndist A C at hlen
  have hd : dist B A = dist C A := by
    simpa only [coe_nndist, dist_comm] using congrArg (fun x : ℝ≥0 => (x : ℝ)) hlen
  apply Subtype.ext
  apply EuclideanGeometry.Sphere.ext (hAα.symm.trans hAβ)
  rw [← hB, ← hC, ← hAα, ← hAβ]
  exact hd

/-- **A distance less than a radius places the point inside.** -/
theorem inside_of_len_lt_circles : Hand.inside_of_len_lt_circles plane := by
  intro A B C α hA hB hlen
  rw [centre_iff] at hA
  rw [onCircle_iff] at hB
  change nndist A C < nndist A B at hlen
  have hd : dist C A < dist B A := by
    simpa only [coe_nndist, dist_comm] using (NNReal.coe_lt_coe.mpr hlen)
  rw [insideCircle_iff, ← hB, ← hA]
  exact hd

/-- **An interior point is nearer the centre than any point on the circle.** -/
theorem len_lt_of_inside_circles : Hand.len_lt_of_inside_circles plane := by
  intro A B C α hA hB hC
  rw [centre_iff] at hA
  rw [onCircle_iff] at hB
  rw [insideCircle_iff, ← hB, ← hA] at hC
  change nndist A C < nndist A B
  apply NNReal.coe_lt_coe.mp
  simpa only [coe_nndist, dist_comm] using hC

/-- **A distance equal to a radius places the point on the circle.** -/
theorem on_circle_of_len_eq_circles : Hand.on_circle_of_len_eq_circles plane := by
  intro A B C α hA hB hlen
  rw [centre_iff] at hA
  rw [onCircle_iff] at hB
  change nndist A C = nndist A B at hlen
  have hd : dist C A = dist B A := by
    simpa only [coe_nndist, dist_comm] using congrArg (fun x : ℝ≥0 => (x : ℝ)) hlen
  rw [onCircle_iff, ← hB, ← hA]
  exact hd

end Model.Euclidean
