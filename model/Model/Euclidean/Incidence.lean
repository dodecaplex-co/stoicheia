module

public import Model.Euclidean.CircleSides
public import Model.Laws.incidence

/-!
# Lines through points, in the plane

Two distinct points span a line: their difference is nonzero, so its span has dimension
one. Any line containing both points has that same direction, and the shared point fixes
the affine subspace. This proves Postulate 1 and uniqueness, with the distinctness
hypothesis excluding the span of a single point.

A circle's centre is the centre of its sphere, so it is unique. Its distance from itself
is zero, less than the positive radius; an inside point cannot also have distance equal
to that radius. The positive-radius condition excludes the circle of radius zero.

For Intersection 1, two points off a line and not on the same side lie on opposite sides
in the plane. Mathlib then supplies a point of the line between them. Their joining
segment lies in every affine subspace containing both endpoints, so this point is on
the second line as well. The lines differ because an endpoint lies on the second and
off the first; the side hypotheses also exclude coincident endpoints.

We thank Joseph Myers for Mathlib's affine subspaces, betweenness and sides, and Chris
Hughes for its finite-dimensional linear algebra, which carry these arguments.
-/

@[expose] public section

namespace Model.Euclidean

/-- The affine span of two distinct points has a one-dimensional direction. -/
theorem incidence_finrank_affineSpan_pair {A B : Plane} (hAB : A ≠ B) :
    Module.finrank ℝ (line[ℝ, A, B]).direction = 1 := by
  rw [direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (vsub_ne_zero.2 hAB)

/-- A line containing two distinct points is their affine span. -/
theorem incidence_line_eq_affineSpan_pair {A B : Plane} {L : Line}
    (hAB : A ≠ B) (hA : A ∈ L.1) (hB : B ∈ L.1) :
    L.1 = line[ℝ, A, B] := by
  have hdir : L.1.direction = ℝ ∙ (A -ᵥ B) :=
    eq_span_singleton_of_mem_of_finrank_eq_one L.2
      (AffineSubspace.vsub_mem_direction hA hB) (vsub_ne_zero.2 hAB)
  apply AffineSubspace.ext_of_direction_eq
  · rw [direction_affineSpan, vectorSpan_pair]
    exact hdir
  · exact ⟨A, hA, left_mem_affineSpan_pair ℝ A B⟩

/-- **Postulate 1 holds in the plane.** -/
theorem Postulate1 : Hand.Postulate1 plane := by
  intro A B hAB
  exact ⟨⟨line[ℝ, A, B], incidence_finrank_affineSpan_pair hAB⟩,
    left_mem_affineSpan_pair ℝ A B, right_mem_affineSpan_pair ℝ A B⟩

/-- **`line_unique` holds in the plane.** -/
theorem line_unique : Hand.line_unique plane := by
  intro A B L M hAB hAL hBL hAM hBM
  apply Subtype.ext
  exact (incidence_line_eq_affineSpan_pair hAB hAL hBL).trans
    (incidence_line_eq_affineSpan_pair hAB hAM hBM).symm

/-- **`centre_unique` holds in the plane.** -/
theorem centre_unique : Hand.centre_unique plane := by
  intro A B α hA hB
  rw [centre_iff] at hA hB
  exact hA.trans hB.symm

/-- **`centre_inside` holds in the plane.** -/
theorem centre_inside : Hand.centre_inside plane := by
  intro A α hA
  rw [centre_iff] at hA
  rw [insideCircle_iff, hA, dist_self]
  exact α.2

/-- **`inside_not_on` holds in the plane.** -/
theorem inside_not_on : Hand.inside_not_on plane := by
  intro A α hinside hon
  exact (ne_of_lt (insideCircle_iff.1 hinside)) (onCircle_iff.1 hon)

/-- **Intersection 1 (`lines_meet_of_opposite_sides`) holds in the plane.** -/
theorem lines_meet_of_opposite_sides : Hand.lines_meet_of_opposite_sides plane := by
  intro A B L M hside hAM hBM
  obtain ⟨hAL, hBL, hnotSame⟩ := hside
  have hopp : L.1.SOppSide A B :=
    (sSameSide_or_sOppSide L.2 hAL hBL).resolve_left hnotSame
  obtain ⟨P, hPL, hbetween⟩ := AffineSubspace.wOppSide_iff_exists_wbtw.1 hopp.wOppSide
  refine ⟨?_, P, hPL, ?_⟩
  · intro hLM
    subst M
    exact hAL hAM
  · exact (affineSpan_pair_le_of_mem_of_mem hAM hBM) hbetween.mem_affineSpan

end Model.Euclidean
