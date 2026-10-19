module

public import Model.Euclidean.AngleBasics
public import Model.Laws.angles
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Adding angles in the plane

The points inside an angle have positive coefficients along its two arms. Mathlib's
angle triangle inequality identifies these combinations with equality in angle addition.
The equality criterion is the work of Ilmārs Cīrulis, Alex Meiburg and Jovan Gerbscheid;
the unoriented angle is the work of Joseph Myers and Manuel Candales, and the same-side
lemmas are the work of Joseph Myers.
-/

@[expose] public section

namespace Model.Euclidean

open scoped NNReal Real

/-- Distinct lines through A cannot share another point C. -/
private theorem off_line_of_distinct_lines {A C : Plane} {L M : Line}
    (hAC : A ≠ C) (hAL : A ∈ L.1) (hAM : A ∈ M.1) (hCM : C ∈ M.1)
    (hLM : L ≠ M) : C ∉ L.1 := by
  intro hCL
  apply hLM
  apply Subtype.ext
  exact (line_eq_affineSpan hAC hAL hCL).trans
    (line_eq_affineSpan hAC hAM hCM).symm

/-- A point on AC has a scalar coordinate along the vector from A to C. -/
private theorem vsub_eq_smul_of_mem_line {A C P : Plane} {M : Line}
    (hAC : A ≠ C) (hAM : A ∈ M.1) (hCM : C ∈ M.1) (hPM : P ∈ M.1) :
    ∃ c : ℝ, P -ᵥ A = c • (C -ᵥ A) := by
  have hdir := AffineSubspace.vsub_mem_direction hPM hAM
  rw [line_eq_affineSpan hAC hAM hCM, direction_affineSpan, vectorSpan_pair_rev,
    Submodule.mem_span_singleton] at hdir
  obtain ⟨c, hc⟩ := hdir
  exact ⟨c, hc.symm⟩

/-- In a combination along AB and AC, the coefficient of AC determines the side of AB.
A zero coefficient lies on AB; a negative one lies on the opposite side from C. -/
private theorem sameSide_combination_iff {A B C D : Plane} {L : Line}
    (hAL : A ∈ L.1) (hBL : B ∈ L.1) (hCL : C ∉ L.1) {a c : ℝ}
    (hD : D -ᵥ A = a • (B -ᵥ A) + c • (C -ᵥ A)) :
    L.1.SSameSide C D ↔ 0 < c := by
  have hP : a • (B -ᵥ A) +ᵥ A ∈ L.1 :=
    AffineSubspace.vadd_mem_of_mem_direction
      (L.1.direction.smul_mem a (AffineSubspace.vsub_mem_direction hBL hAL)) hAL
  have hD' : D = c • (C -ᵥ A) +ᵥ (a • (B -ᵥ A) +ᵥ A) := by
    rw [vadd_vadd, add_comm, ← hD, vsub_vadd]
  rw [hD']
  constructor
  · intro hside
    rcases lt_trichotomy c 0 with hc | hc | hc
    · exact False.elim (hside.not_sOppSide
        (AffineSubspace.sOppSide_smul_vsub_vadd_right hCL hAL hP hc))
    · subst c
      exact (hside.right_notMem (by simpa using hP)).elim
    · exact hc
  · exact AffineSubspace.sSameSide_smul_vsub_vadd_right hCL hAL hP

/-- **`angle_add_of_inside` holds in the plane.** The two same-side conditions give
positive coefficients along the arms, so Mathlib's cone criterion gives angle addition.
The distinct endpoints, and D lying on C's side of L (so not on L, and not at the vertex),
exclude repeated points at the vertex, where the model instead assigns angle 0. -/
theorem angle_add_of_inside : Hand.angle_add_of_inside plane := by
  intro A B C D L M hAL hAM hBL hCM hAB hAC _hDL _hDM _hLM hBD hCD
  have hDA : D ≠ A := by
    rintro rfl
    exact hCD.right_notMem hAL
  have hrep : ∃ a : ℝ, 0 < a ∧ ∃ P ∈ M.1, a • (B -ᵥ A) +ᵥ P = D := by
    have hmem : D ∈ {P | M.1.SSameSide B P} := hBD
    rw [AffineSubspace.setOfPred_sSameSide_eq_image2 hBD.left_notMem hAM] at hmem
    exact hmem
  obtain ⟨a, ha, P, hPM, hPD⟩ := hrep
  obtain ⟨c, hc⟩ := vsub_eq_smul_of_mem_line hAC hAM hCM hPM
  have hD : D -ᵥ A = a • (B -ᵥ A) + c • (C -ᵥ A) := by
    rw [← hPD, vadd_vsub_assoc, hc]
  have hcpos := (sameSide_combination_iff hAL hBL hCD.left_notMem hD).1 hCD
  have hcone : D -ᵥ A ∈ Submodule.span ℝ≥0 {B -ᵥ A, C -ᵥ A} := by
    rw [Submodule.mem_span_pair]
    exact ⟨⟨a, ha.le⟩, ⟨c, hcpos.le⟩, hD.symm⟩
  change angle B A C = angle B A D + angle D A C
  apply NNReal.coe_injective
  rw [NNReal.coe_add, coe_angle_of_ne hAB.symm hAC.symm,
    coe_angle_of_ne hAB.symm hDA, coe_angle_of_ne hDA hAC.symm]
  exact (InnerProductGeometry.angle_eq_angle_add_angle_iff (vsub_ne_zero.2 hDA)).2
    (Or.inr hcone)

/-- **`inside_of_angle_add` holds in the plane.** Distinct lines exclude a straight angle,
so Mathlib's equality criterion gives nonnegative coefficients, and D off both lines
makes them positive. The endpoint hypotheses also exclude repeated points at the vertex,
where the model assigns angle 0. -/
theorem inside_of_angle_add : Hand.inside_of_angle_add plane := by
  intro A B C D L M hAL hAM hBL hCM hAB hAC hDL hDM hLM hsum
  have hDA : D ≠ A := by
    rintro rfl
    exact hDL hAL
  have hCL : C ∉ L.1 := off_line_of_distinct_lines hAC hAL hAM hCM hLM
  have hBM : B ∉ M.1 := off_line_of_distinct_lines hAB hAM hAL hBL hLM.symm
  have hnotpi : InnerProductGeometry.angle (B -ᵥ A) (C -ᵥ A) ≠ π := by
    intro hpi
    obtain ⟨_, t, _, ht⟩ := InnerProductGeometry.angle_eq_pi_iff.1 hpi
    apply hCL
    apply (AffineSubspace.vsub_right_mem_direction_iff_mem hAL C).1
    rw [ht]
    exact L.1.direction.smul_mem t (AffineSubspace.vsub_mem_direction hBL hAL)
  change angle B A C = angle B A D + angle D A C at hsum
  have hreal := congrArg (fun x : ℝ≥0 => (x : ℝ)) hsum
  rw [NNReal.coe_add, coe_angle_of_ne hAB.symm hAC.symm,
    coe_angle_of_ne hAB.symm hDA, coe_angle_of_ne hDA hAC.symm] at hreal
  have hcone := ((InnerProductGeometry.angle_eq_angle_add_angle_iff
    (vsub_ne_zero.2 hDA)).1 hreal).resolve_left hnotpi
  obtain ⟨a, c, hcomb⟩ := Submodule.mem_span_pair.1 hcone
  have hD : D -ᵥ A = (a : ℝ) • (B -ᵥ A) + (c : ℝ) • (C -ᵥ A) := hcomb.symm
  have ha : 0 < (a : ℝ) := by
    apply lt_of_le_of_ne a.2
    intro hzero
    have ha0 : a = 0 := NNReal.coe_eq_zero.1 hzero.symm
    subst a
    simp only [NNReal.coe_zero, zero_smul, zero_add] at hD
    apply hDM
    apply (AffineSubspace.vsub_right_mem_direction_iff_mem hAM D).1
    rw [hD]
    exact M.1.direction.smul_mem _ (AffineSubspace.vsub_mem_direction hCM hAM)
  have hc : 0 < (c : ℝ) := by
    apply lt_of_le_of_ne c.2
    intro hzero
    have hc0 : c = 0 := NNReal.coe_eq_zero.1 hzero.symm
    subst c
    simp only [NNReal.coe_zero, zero_smul, add_zero] at hD
    apply hDL
    apply (AffineSubspace.vsub_right_mem_direction_iff_mem hAL D).1
    rw [hD]
    exact L.1.direction.smul_mem _ (AffineSubspace.vsub_mem_direction hBL hAL)
  constructor
  · exact (sameSide_combination_iff hAM hCM hBM (hD.trans (add_comm _ _))).2 ha
  · exact (sameSide_combination_iff hAL hBL hCL hD).2 hc

end Model.Euclidean
