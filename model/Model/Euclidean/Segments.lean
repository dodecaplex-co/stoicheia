module

public import Model.Euclidean
public import Model.Laws.order
public import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Lengths along a line and round a circle, in the plane

The diagram-segment rules. A length is `nndist`, a circle a Mathlib sphere of positive
radius. Lengths add along a segment by Mathlib's distance formula for weak betweenness,
building on Joseph Myers's betweenness lemmas, with our thanks. The circle laws compare
distances with the radius: equal centres and radii give equal spheres, and a smaller
distance means a point is inside. These comparisons also cover the centre itself,
where the distance is zero, and allow the two named points on circles to coincide.
-/

@[expose] public section

namespace Model.Euclidean

open scoped NNReal

/-- **`len_add_of_between` holds in the plane** (Diagram-segment 1). -/
theorem len_add_of_between : Hand.len_add_of_between plane := by
  intro A B C h
  change Sbtw ℝ A B C at h
  change nndist A B + nndist B C = nndist A C
  apply NNReal.coe_injective
  change dist A B + dist B C = dist A C
  exact h.wbtw.dist_add_dist

/-- **`circle_eq` holds in the plane** (Diagram-segment 2). -/
theorem circle_eq : Hand.circle_eq plane := by
  intro A B C α β hAα hAβ hB hC hlen
  change A = α.1.center at hAα
  change A = β.1.center at hAβ
  change nndist A B = nndist A C at hlen
  rw [onCircle_iff, ← hAα, dist_comm] at hB
  rw [onCircle_iff, ← hAβ, dist_comm] at hC
  have hdist : dist A B = dist A C := congrArg (fun r : ℝ≥0 => (r : ℝ)) hlen
  apply Subtype.ext
  exact EuclideanGeometry.Sphere.ext (hAα.symm.trans hAβ)
    (hB.symm.trans (hdist.trans hC))

/-- **`on_circle_of_len_eq` holds in the plane** (Diagram-segment 3). -/
theorem on_circle_of_len_eq : Hand.on_circle_of_len_eq plane := by
  intro A B C α hA hB hlen
  change A = α.1.center at hA
  change nndist A C = nndist A B at hlen
  rw [onCircle_iff, ← hA, dist_comm] at hB ⊢
  have hdist : dist A C = dist A B := congrArg (fun r : ℝ≥0 => (r : ℝ)) hlen
  exact hdist.trans hB

/-- **`inside_of_len_lt` holds in the plane** (Diagram-segment 4). -/
theorem inside_of_len_lt : Hand.inside_of_len_lt plane := by
  intro A B C α hA hB hlen
  change A = α.1.center at hA
  change dist A C < dist A B at hlen
  rw [onCircle_iff, ← hA, dist_comm] at hB
  change dist C α.1.center < α.1.radius
  rwa [← hA, dist_comm, ← hB]

/-- **`len_lt_of_inside` holds in the plane** (Diagram-segment 4). -/
theorem len_lt_of_inside : Hand.len_lt_of_inside plane := by
  intro A B C α hA hB hC
  change A = α.1.center at hA
  change dist C α.1.center < α.1.radius at hC
  change dist A C < dist A B
  rw [onCircle_iff, ← hA, dist_comm] at hB
  rwa [← hA, dist_comm, ← hB] at hC

end Model.Euclidean
