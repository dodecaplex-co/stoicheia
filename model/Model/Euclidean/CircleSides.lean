module

public import Model.Euclidean.Circles
public import Mathlib.Geometry.Euclidean.PerpBisector

/-!
# On which side of the line of centres two circles cut one another, in the plane

Intersections 8 and 9: two circles that cut one another, with their centres on a straight
line L, have a common point on each side of L, the side of any given point B off L and the
other side.

`CirclesMeet α α` is true, since a circle has two distinct points, so the laws cover two
cases. When the centres are one point, a common point fixes the radius and the circles are
equal; L is then any line through the centre, and the circle meets the ray from the
centre through B, on B's side, and the opposite ray, on the other side. When the centres
differ, each is as far from one common point as from the other, so L is the perpendicular
bisector of the two common points; they lie on opposite sides of it, and B, off it, is on
the side of one of them and not of the other.

That last step uses a fact about the plane that later laws will need too (Pasch's rules,
`same_side_or`): two points off a line are on one side of it or on opposite sides
(`sSameSide_or_sOppSide`).
-/

@[expose] public section

namespace Model.Euclidean

/-- Two points off a line in the plane lie on the same side or on opposite sides.
The quotient by the line's direction is one-dimensional, so the sign of a scalar decides. -/
theorem sSameSide_or_sOppSide {s : AffineSubspace ℝ Plane}
    (hs : Module.finrank ℝ s.direction = 1) {x y : Plane}
    (hx : x ∉ s) (hy : y ∉ s) : s.SSameSide x y ∨ s.SOppSide x y := by
  have hsne : s ≠ ⊥ := by
    intro h
    rw [h, AffineSubspace.direction_bot] at hs
    simp at hs
  obtain ⟨p, hp⟩ := (s.nonempty_iff_ne_bot).2 hsne
  have hdim : Module.finrank ℝ (Plane ⧸ s.direction) = 1 := by
    have h := s.direction.finrank_quotient_add_finrank
    rw [hs, finrank_euclideanSpace, Fintype.card_fin] at h
    omega
  have hxq : s.direction.mkQ (x -ᵥ p) ≠ 0 := by
    intro h
    apply hx
    apply (AffineSubspace.vsub_right_mem_direction_iff_mem hp x).1
    exact (Submodule.Quotient.mk_eq_zero _).1 h
  obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one hdim hxq
    (s.direction.mkQ (y -ᵥ p))
  have hv : y -ᵥ p - t • (x -ᵥ p) ∈ s.direction := by
    have hzero : s.direction.mkQ (y -ᵥ p - t • (x -ᵥ p)) = 0 := by
      rw [map_sub, map_smul, ht, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).1 hzero
  have htne : t ≠ 0 := by
    intro h
    apply hy
    apply (AffineSubspace.vsub_right_mem_direction_iff_mem hp y).1
    simpa [h] using hv
  let q := (y -ᵥ p - t • (x -ᵥ p)) +ᵥ p
  have hq : q ∈ s := AffineSubspace.vadd_mem_of_mem_direction hv hp
  have hyq : t • (x -ᵥ p) +ᵥ q = y := by
    dsimp [q]
    abel
  rcases lt_or_gt_of_ne htne with htneg | htpos
  · right
    rw [← hyq]
    exact AffineSubspace.sOppSide_smul_vsub_vadd_right hx hp hq htneg
  · left
    rw [← hyq]
    exact AffineSubspace.sSameSide_smul_vsub_vadd_right hx hp hq htpos

/-- For distinct P and Q, a line through two distinct points equidistant from them
is their perpendicular bisector. -/
theorem line_eq_perpBisector {s : AffineSubspace ℝ Plane}
    (hs : Module.finrank ℝ s.direction = 1) {C D P Q : Plane}
    (hCD : C ≠ D) (hPQ : P ≠ Q) (hC : C ∈ s) (hD : D ∈ s)
    (hCPQ : dist P C = dist Q C) (hDPQ : dist P D = dist Q D) :
    s = AffineSubspace.perpBisector P Q := by
  have hCbis := AffineSubspace.mem_perpBisector_iff_dist_eq'.2 hCPQ
  have hDbis := AffineSubspace.mem_perpBisector_iff_dist_eq'.2 hDPQ
  have hbis : Module.finrank ℝ (AffineSubspace.perpBisector P Q).direction = 1 := by
    rw [AffineSubspace.direction_perpBisector]
    apply Submodule.finrank_add_finrank_orthogonal'
    rw [finrank_span_singleton (vsub_ne_zero.2 hPQ.symm),
      finrank_euclideanSpace, Fintype.card_fin]
  have hdir : s.direction = ℝ ∙ (D -ᵥ C) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hs
      (AffineSubspace.vsub_mem_direction hD hC) (vsub_ne_zero.2 hCD.symm)
  have hbisdir : (AffineSubspace.perpBisector P Q).direction = ℝ ∙ (D -ᵥ C) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hbis
      (AffineSubspace.vsub_mem_direction hDbis hCbis) (vsub_ne_zero.2 hCD.symm)
  exact AffineSubspace.ext_of_direction_eq (hdir.trans hbisdir.symm) ⟨C, hC, hCbis⟩

/-- Circles with the same centre and a common point are equal. -/
theorem circle_eq_of_center_eq_of_common_point {α β : Circle} {P : Plane}
    (hc : α.1.center = β.1.center) (hPα : plane.OnCircle P α)
    (hPβ : plane.OnCircle P β) : α = β := by
  apply Subtype.ext
  apply EuclideanGeometry.Sphere.ext hc
  rw [onCircle_iff] at hPα hPβ
  exact hPα.symm.trans ((congrArg (dist P) hc).trans hPβ)

/-- Scaling a nonzero vector by the radius divided by its length reaches the circle. -/
theorem onCircle_radius_smul {α : Circle} {v : Plane} (hv : v ≠ 0) :
    plane.OnCircle ((α.1.radius / ‖v‖) • v +ᵥ α.1.center) α := by
  rw [onCircle_iff, dist_eq_norm_vsub, vadd_vsub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos α.2 (norm_pos_iff.2 hv)), div_mul_cancel₀ _ (norm_ne_zero_iff.2 hv)]

/-- **Intersection 8 holds in the plane.** -/
theorem circles_meet_same_side : Hand.circles_meet_same_side plane := by
  intro α β B C D L hmeet hC hD hCL hDL hB
  obtain ⟨P, Q, hPQ, hPα, hPβ, hQα, hQβ⟩ := hmeet
  rw [centre_iff] at hC hD
  subst C
  subst D
  by_cases hc : α.1.center = β.1.center
  · have heq := circle_eq_of_center_eq_of_common_point hc hPα hPβ
    subst β
    have hv : B -ᵥ α.1.center ≠ 0 :=
      vsub_ne_zero.2 (fun h => hB (h ▸ hCL))
    have ht : 0 < α.1.radius / ‖B -ᵥ α.1.center‖ := div_pos α.2 (norm_pos_iff.2 hv)
    have hA := onCircle_radius_smul (α := α) hv
    exact ⟨_, hA, hA, AffineSubspace.sSameSide_smul_vsub_vadd_left hB hCL hCL ht⟩
  · have hL := line_eq_perpBisector L.2 hc hPQ hCL hDL
      ((onCircle_iff.1 hPα).trans (onCircle_iff.1 hQα).symm)
      ((onCircle_iff.1 hPβ).trans (onCircle_iff.1 hQβ).symm)
    have hPQside : L.1.SOppSide P Q := by
      rw [hL]
      exact (sbtw_midpoint_of_ne ℝ hPQ).sOppSide_of_notMem_of_mem
        (by simpa only [AffineSubspace.left_mem_perpBisector] using hPQ)
        (AffineSubspace.midpoint_mem_perpBisector P Q)
    rcases sSameSide_or_sOppSide L.2 hPQside.left_notMem hB with hPB | hPB
    · exact ⟨P, hPα, hPβ, hPB⟩
    · exact ⟨Q, hQα, hQβ, hPQside.symm.trans hPB⟩

/-- **Intersection 9 holds in the plane.** -/
theorem circles_meet_opposite_side : Hand.circles_meet_opposite_side plane := by
  intro α β B C D L hmeet hC hD hCL hDL hB
  obtain ⟨P, Q, hPQ, hPα, hPβ, hQα, hQβ⟩ := hmeet
  rw [centre_iff] at hC hD
  subst C
  subst D
  by_cases hc : α.1.center = β.1.center
  · have heq := circle_eq_of_center_eq_of_common_point hc hPα hPβ
    subst β
    have hv : B -ᵥ α.1.center ≠ 0 :=
      vsub_ne_zero.2 (fun h => hB (h ▸ hCL))
    have ht : 0 < α.1.radius / ‖B -ᵥ α.1.center‖ := div_pos α.2 (norm_pos_iff.2 hv)
    have hA : plane.OnCircle
        ((-(α.1.radius / ‖B -ᵥ α.1.center‖)) • (B -ᵥ α.1.center) +ᵥ α.1.center) α := by
      simpa only [norm_neg, smul_neg, neg_smul] using
        (onCircle_radius_smul (α := α) (neg_ne_zero.2 hv))
    have hside := AffineSubspace.sOppSide_smul_vsub_vadd_left hB hCL hCL (neg_neg_of_pos ht)
    exact ⟨_, hA, hA, hside.left_notMem, hside.right_notMem, hside.not_sSameSide⟩
  · have hL := line_eq_perpBisector L.2 hc hPQ hCL hDL
      ((onCircle_iff.1 hPα).trans (onCircle_iff.1 hQα).symm)
      ((onCircle_iff.1 hPβ).trans (onCircle_iff.1 hQβ).symm)
    have hPQside : L.1.SOppSide P Q := by
      rw [hL]
      exact (sbtw_midpoint_of_ne ℝ hPQ).sOppSide_of_notMem_of_mem
        (by simpa only [AffineSubspace.left_mem_perpBisector] using hPQ)
        (AffineSubspace.midpoint_mem_perpBisector P Q)
    rcases sSameSide_or_sOppSide L.2 hPQside.left_notMem hB with hPB | hPB
    · have hQB := hPQside.symm.trans_sSameSide hPB
      exact ⟨Q, hQα, hQβ, hQB.left_notMem, hQB.right_notMem, hQB.not_sSameSide⟩
    · exact ⟨P, hPα, hPβ, hPB.left_notMem, hPB.right_notMem, hPB.not_sSameSide⟩

end Model.Euclidean
