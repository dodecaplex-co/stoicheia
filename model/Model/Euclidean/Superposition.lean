module

public import Model.Euclidean.CircleSides
public import Model.Euclidean.Incidence
public import Model.Euclidean.Sides
public import Model.Laws.superposition
public import Elements.Foundations.Superposition.Soundness
public import Mathlib.Geometry.Euclidean.Projection

/-!
# Superposition, in the plane

The restricted rule of superposition holds in the plane. Its supporting construction
lays a triangle ABC down with A on the point D of a line L, B on the ray from D through G, and C on the
side of L where H is, with its three sides and three angles kept. In the plane this is a
motion, and the proof builds one, from Mathlib alone, with a reflection when the side needs
one.

Place B' on the ray from D through G, at distance AB from D. A linear reflection sends
the vector AB to the equally long vector DB'; translating its source and target gives
an affine isometry sending A to D and B to B'. The image of C is off L: otherwise the
inverse image of L would be a line containing all three original vertices.

If that image of C is on the wrong side, reflect the whole copy in L. This fixes D and
B' and exchanges the two sides, since the midpoint of a point and its reflection is its
orthogonal projection onto L. Distances and all three angles survive both isometries.
The angle helper also covers repeated points, whose angle is zero in this reading, since
an isometry repeats a point exactly when its image is repeated.

The retained placement theorem supplies the triangle. Its third corner C' is off L, by
Same side 3, whereas D is on L, so Postulate 1 supplies the side through D and C'. The
generic `Rule.of_placement_of_join` takes those three and proves the restricted law,
through `Rule.of_placement`. The library may use that law directly only in I.4 and I.8;
it exports metric equalities about the given figure.

We thank Zhouhang Zhou, Frédéric Dupuis and Heather Macbeth for Mathlib's linear
reflection lemmas, Heather Macbeth for its affine isometries, Joseph Myers and Manuel
Candales for its affine reflections and angle invariance, and Joseph Myers for its
betweenness and sides. Their results supply the isometries and the metric equalities here.
-/

@[expose] public section

namespace Model.Euclidean

/-- Affine isometries preserve the reading of length. -/
theorem len_map_isometry (f : Plane ≃ᵃⁱ[ℝ] Plane) (A B : Plane) :
    plane.len (f A) (f B) = plane.len A B :=
  f.toAffineIsometry.nndist_map A B

/-- Affine isometries preserve the reading of angle, including its zero-arm cases. -/
theorem angle_map_isometry (f : Plane ≃ᵃⁱ[ℝ] Plane) (A B C : Plane) :
    angle (f A) (f B) (f C) = angle A B C := by
  have hangle := f.toAffineIsometry.angle_map A B C
  change EuclideanGeometry.angle (f A) (f B) (f C) =
    EuclideanGeometry.angle A B C at hangle
  simp only [angle, f.injective.eq_iff, hangle]

/-- If two image vertices lie on a line, the third image vertex of a triangle is off it. -/
theorem triangle_image_notMem (f : Plane ≃ᵃⁱ[ℝ] Plane) {A B C : Plane} {L : Line}
    (hABC : Hand.Superposition.Triangle plane A B C) (hA : f A ∈ L.1)
    (hB : f B ∈ L.1) : f C ∉ L.1 := by
  intro hC
  let K : Line := ⟨L.1.map f.symm.toAffineEquiv.toAffineMap, by
    rw [AffineSubspace.map_direction]
    exact (f.symm.toAffineEquiv.linear.finrank_map_eq L.1.direction).trans L.2⟩
  apply hABC
  refine ⟨K, ?_, ?_, ?_⟩
  · exact AffineSubspace.mem_map.2 ⟨f A, hA, f.symm_apply_apply A⟩
  · exact AffineSubspace.mem_map.2 ⟨f B, hB, f.symm_apply_apply B⟩
  · exact AffineSubspace.mem_map.2 ⟨f C, hC, f.symm_apply_apply C⟩

/-- A nonnegative multiple of the direction DG cannot put D strictly between it and G. -/
theorem not_sbtw_smul_vsub_vadd (D G : Plane) {t : ℝ} (ht : 0 ≤ t) :
    ¬ Sbtw ℝ (t • (G -ᵥ D) +ᵥ D) D G := by
  intro h
  have horder := wbtw_or_wbtw_smul_vadd_of_nonneg D (G -ᵥ D) ht
    (show (0 : ℝ) ≤ 1 by norm_num)
  simp only [one_smul, vsub_vadd] at horder
  rcases horder with horder | horder
  · exact h.not_swap_left horder
  · exact h.symm.not_swap_left horder

/-- Equal segments can be matched by translating a linear reflection. -/
theorem exists_isometry_of_dist_eq {A B D E : Plane} (h : dist A B = dist D E) :
    ∃ f : Plane ≃ᵃⁱ[ℝ] Plane, f A = D ∧ f B = E := by
  let ρ := (ℝ ∙ ((B -ᵥ A) - (E -ᵥ D)))ᗮ.reflection
  have hnorm : ‖B -ᵥ A‖ = ‖E -ᵥ D‖ := by
    rw [← dist_eq_norm_vsub Plane, ← dist_eq_norm_vsub Plane, dist_comm B A, dist_comm E D]
    exact h
  have hρ : ρ (B -ᵥ A) = E -ᵥ D := Submodule.reflection_sub hnorm
  let f := ((AffineIsometryEquiv.vaddConst ℝ A).symm.trans
    ρ.toAffineIsometryEquiv).trans (AffineIsometryEquiv.vaddConst ℝ D)
  refine ⟨f, ?_, ?_⟩
  · change ρ (A -ᵥ A) +ᵥ D = D
    simp
  · change ρ (B -ᵥ A) +ᵥ D = E
    rw [hρ, vsub_vadd]

/-- Reflection across a nonempty affine subspace takes an off-subspace point across it. -/
theorem sOppSide_reflection {s : AffineSubspace ℝ Plane} [Nonempty s]
    {x : Plane} (hx : x ∉ s) : s.SOppSide x (EuclideanGeometry.reflection s x) := by
  have hne : x ≠ EuclideanGeometry.reflection s x := by
    intro h
    exact hx ((EuclideanGeometry.reflection_eq_self_iff x).1 h.symm)
  have hmid : midpoint ℝ x (EuclideanGeometry.reflection s x) =
      (EuclideanGeometry.orthogonalProjection s x : Plane) := by
    rw [midpoint_eq_iff, AffineEquiv.pointReflection_apply]
    exact (EuclideanGeometry.reflection_apply' s x).symm
  apply (sbtw_midpoint_of_ne ℝ hne).sOppSide_of_notMem_of_mem hx
  rw [hmid]
  exact (EuclideanGeometry.orthogonalProjection s x).property

/-- An isometry placing two vertices on L can put the third on either prescribed side. -/
theorem exists_isometry_sameSide (f : Plane ≃ᵃⁱ[ℝ] Plane) {A B C H : Plane} {L : Line}
    (hA : f A ∈ L.1) (hB : f B ∈ L.1) (hC : f C ∉ L.1) (hH : H ∉ L.1) :
    ∃ g : Plane ≃ᵃⁱ[ℝ] Plane, g A = f A ∧ g B = f B ∧ L.1.SSameSide (g C) H := by
  rcases sSameSide_or_sOppSide L.2 hC hH with hside | hside
  · exact ⟨f, rfl, rfl, hside⟩
  · let : Nonempty L.1 := ⟨⟨f A, hA⟩⟩
    refine ⟨f.trans (EuclideanGeometry.reflection L.1), ?_, ?_, ?_⟩
    · change EuclideanGeometry.reflection L.1 (f A) = f A
      exact (EuclideanGeometry.reflection_eq_self_iff (f A)).2 hA
    · change EuclideanGeometry.reflection L.1 (f B) = f B
      exact (EuclideanGeometry.reflection_eq_self_iff (f B)).2 hB
    · change L.1.SSameSide (EuclideanGeometry.reflection L.1 (f C)) H
      exact (sOppSide_reflection hC).symm.trans hside

/-- The supporting placement exists in the plane, by isometry and reflection. -/
theorem superposition_placement : Hand.Superposition.placement plane := by
  intro A B C D G H L hABC hD hG hDG hH
  let t := dist A B / dist D G
  have ht : 0 ≤ t := div_nonneg dist_nonneg dist_nonneg
  let B' := t • (G -ᵥ D) +ᵥ D
  have hB' : B' ∈ L.1 :=
    AffineSubspace.vadd_mem_of_mem_direction
      (L.1.direction.smul_mem t (AffineSubspace.vsub_mem_direction hG hD)) hD
  have hdist : dist A B = dist D B' := by
    symm
    change dist D (t • (G -ᵥ D) +ᵥ D) = dist A B
    rw [dist_comm D, dist_eq_norm_vsub Plane, vadd_vsub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht, ← dist_eq_norm_vsub Plane, dist_comm G D]
    exact div_mul_cancel₀ _ (dist_ne_zero.2 hDG)
  obtain ⟨f, hfA, hfB⟩ := exists_isometry_of_dist_eq hdist
  have hfAL : f A ∈ L.1 := hfA.symm ▸ hD
  have hfBL : f B ∈ L.1 := hfB.symm ▸ hB'
  have hfC := triangle_image_notMem f hABC hfAL hfBL
  obtain ⟨g, hgA, hgB, hgC⟩ := exists_isometry_sameSide f hfAL hfBL hfC hH
  have hgD : g A = D := hgA.trans hfA
  have hgB' : g B = B' := hgB.trans hfB
  refine ⟨B', g C, hB', not_sbtw_smul_vsub_vadd D G ht, hgC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hgD, hgB'] using len_map_isometry g A B
  · simpa only [hgB'] using len_map_isometry g B C
  · simpa only [hgD] using len_map_isometry g C A
  · simpa only [hgD, hgB'] using angle_map_isometry g B A C
  · simpa only [hgD, hgB'] using angle_map_isometry g A C B
  · simpa only [hgD, hgB'] using angle_map_isometry g C B A

/-- **Restricted superposition holds in the plane**, including the side laid down. -/
theorem superposition : Hand.Superposition.superposition plane :=
  Elements.Superposition.Rule.of_placement_of_join superposition_placement
    not_on_line_of_same_side fun h => Postulate1 _ _ h

end Model.Euclidean
