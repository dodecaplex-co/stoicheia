module

public import Model.Euclidean.Areas
public import Model.Euclidean.Sides

/-!
# Three lines through one point, in the plane

For a line through distinct A and B, two points are strictly on the same side exactly
when their determinants against B - A have positive product. This connects the sign
calculation to Mathlib's affine-side relation, including points on the line.

The first two triple-incidence rules follow by reversing determinant signs. The third
uses the determinant identity for four vectors in a plane. The laws' hypotheses provide
each distinctness needed to name a line by two points; none is added to a law.
The proofs use Mathlib's affine subspaces and sides, the work of Joseph Myers, with thanks.
-/

@[expose] public section

namespace Model.Euclidean

namespace TripleIncidence

/-- Strict same-side membership is the positivity of the two signed determinants. -/
theorem sameSide_iff_det_mul_pos {A B C D : Plane} {L : Line}
    (hA : A ∈ L.1) (hB : B ∈ L.1) (hAB : A ≠ B) :
    L.1.SSameSide C D ↔ 0 < det (B - A) (C - A) * det (B - A) (D - A) := by
  constructor
  · intro h
    have hC : det (B - A) (C - A) ≠ 0 :=
      fun hz => h.left_notMem ((Areas.mem_line_iff_det_eq_zero hA hB hAB).2 hz)
    have hmem : D ∈ {y | L.1.SSameSide C y} := h
    rw [AffineSubspace.setOfPred_sSameSide_eq_image2 h.left_notMem hA] at hmem
    obtain ⟨t, ht, P, hP, hDP⟩ := hmem
    have hPdet := (Areas.mem_line_iff_det_eq_zero hA hB hAB).1 hP
    have hdet : det (B - A) (D - A) = t * det (B - A) (C - A) := by
      calc
        det (B - A) (D - A) =
            t * det (B - A) (C - A) + det (B - A) (P - A) := by
          rw [← hDP]
          simp only [vsub_eq_sub, vadd_eq_add, det, PiLp.sub_apply, PiLp.add_apply,
            PiLp.smul_apply, smul_eq_mul]
          ring
        _ = t * det (B - A) (C - A) := by rw [hPdet, add_zero]
    rw [hdet]
    calc
      0 < t * det (B - A) (C - A) ^ 2 := mul_pos ht (sq_pos_of_ne_zero hC)
      _ = det (B - A) (C - A) * (t * det (B - A) (C - A)) := by ring
  · intro h
    have hC : det (B - A) (C - A) ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at h
      exact (lt_irrefl _ h)
    have hCL : C ∉ L.1 :=
      fun hmem => hC ((Areas.mem_line_iff_det_eq_zero hA hB hAB).1 hmem)
    let t := det (B - A) (D - A) / det (B - A) (C - A)
    have ht : 0 < t := div_pos_iff.2 (mul_pos_iff.1 (by rwa [mul_comm] at h))
    have htdet : t * det (B - A) (C - A) = det (B - A) (D - A) :=
      div_mul_cancel₀ _ hC
    let P := D - t • (C - A)
    have hP : P ∈ L.1 := by
      apply (Areas.mem_line_iff_det_eq_zero hA hB hAB).2
      calc
        det (B - A) (P - A) =
            det (B - A) (D - A) - t * det (B - A) (C - A) := by
          simp only [P, det, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
          ring
        _ = 0 := by rw [htdet, sub_self]
    have hDP : t • (C -ᵥ A) +ᵥ P = D := by
      change t • (C - A) + (D - t • (C - A)) = D
      abel
    have hs := AffineSubspace.sSameSide_smul_vsub_vadd_right hCL hA hP ht
    rwa [hDP] at hs

end TripleIncidence

open TripleIncidence

/-- **Triple incidence 1 holds in the plane.** The two side conditions force the
determinants of B and D against AC to have opposite signs. -/
theorem triple_incidence1 : Hand.triple_incidence1 plane := by
  intro A B C D L M N hAL hAM hAN hBL hCM hDN hCD hBC hBD
  have hAB : A ≠ B := fun h => hBC.left_notMem (h ▸ hAN)
  have hAC : A ≠ C := fun h => hCD.left_notMem (h ▸ hAL)
  have hAD : A ≠ D := fun h => hCD.right_notMem (h ▸ hAL)
  have hL := (sameSide_iff_det_mul_pos hAL hBL hAB).1 hCD
  have hN := (sameSide_iff_det_mul_pos hAN hDN hAD).1 hBC
  have hM := (sameSide_iff_det_mul_pos hAM hCM hAC).1 hBD
  rw [Areas.det_swap (D - A) (B - A), Areas.det_swap (D - A) (C - A),
    neg_mul_neg] at hN
  rw [Areas.det_swap (C - A) (B - A)] at hM
  rcases mul_pos_iff.1 hL with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
    rcases mul_pos_iff.1 hN with ⟨hy', hz⟩ | ⟨hy', hz⟩ <;> nlinarith

/-- **Triple incidence 2 holds in the plane.** D off M excludes a zero determinant,
so the negated same-side condition supplies the strict sign needed on N. -/
theorem triple_incidence2 : Hand.triple_incidence2 plane := by
  intro A B C D L M N hAL hAM hAN hBL hCM hDN hCD hBD hDM hBA
  have hAC : A ≠ C := fun h => hCD.left_notMem (h ▸ hAL)
  have hAD : A ≠ D := fun h => hCD.right_notMem (h ▸ hAL)
  have hL := (sameSide_iff_det_mul_pos hAL hBL hBA.symm).1 hCD
  have hM := hBD ∘ (sameSide_iff_det_mul_pos hAM hCM hAC).2
  have hz : det (C - A) (D - A) ≠ 0 :=
    fun h => hDM ((Areas.mem_line_iff_det_eq_zero hAM hCM hAC).2 h)
  rw [Areas.det_swap (C - A) (B - A)] at hM
  apply (sameSide_iff_det_mul_pos hAN hDN hAD).2
  rw [Areas.det_swap (D - A) (B - A), Areas.det_swap (D - A) (C - A), neg_mul_neg]
  rcases mul_pos_iff.1 hL with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hzpos : 0 < det (C - A) (D - A) := by
      rcases lt_or_gt_of_ne hz with hzneg | hzpos
      · exact False.elim (hM (mul_pos_of_neg_of_neg (neg_neg_of_pos hx) hzneg))
      · exact hzpos
    exact mul_pos hy hzpos
  · have hzneg : det (C - A) (D - A) < 0 := by
      rcases lt_or_gt_of_ne hz with hzneg | hzpos
      · exact hzneg
      · exact False.elim (hM (mul_pos (neg_pos.2 hx) hzpos))
    exact mul_pos_of_neg_of_neg hy hzneg

/-- **Triple incidence 3 holds in the plane.** The determinant identity for four
vectors puts E on C's strict side of AB. -/
theorem triple_incidence3 : Hand.triple_incidence3 plane := by
  intro A B C D E L M N hAL hAM hAN hBL hCM hDN hCD hBC hDE hCE
  have hAB : A ≠ B := fun h => hBC.left_notMem (h ▸ hAN)
  have hAC : A ≠ C := fun h => hCD.left_notMem (h ▸ hAL)
  have hAD : A ≠ D := fun h => hCD.right_notMem (h ▸ hAL)
  have hL := (sameSide_iff_det_mul_pos hAL hBL hAB).1 hCD
  have hN := (sameSide_iff_det_mul_pos hAN hDN hAD).1 hBC
  have hM := (sameSide_iff_det_mul_pos hAM hCM hAC).1 hDE
  have hE := (sameSide_iff_det_mul_pos hAN hDN hAD).1 hCE
  rw [Areas.det_swap (D - A) (B - A), Areas.det_swap (D - A) (C - A),
    neg_mul_neg] at hN
  rw [Areas.det_swap (D - A) (C - A)] at hE
  have hid : det (B - A) (E - A) * det (C - A) (D - A) =
      det (B - A) (D - A) * det (C - A) (E - A) -
        det (B - A) (C - A) * det (D - A) (E - A) := by
    unfold det
    ring
  apply (sameSide_iff_det_mul_pos hAL hBL hAB).2
  rcases mul_pos_iff.1 hL with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hz := pos_of_mul_pos_right hN hy.le
    have hp := pos_of_mul_pos_right hM hz.le
    have hq := neg_of_mul_pos_right hE (neg_nonpos.2 hz.le)
    have hr : 0 < det (B - A) (E - A) * det (C - A) (D - A) := by
      rw [hid]
      exact sub_pos.2 ((mul_neg_of_pos_of_neg hx hq).trans (mul_pos hy hp))
    exact mul_pos hx (pos_of_mul_pos_left hr hz.le)
  · have hz := neg_of_mul_pos_right hN hy.le
    have hp := neg_of_mul_pos_right hM hz.le
    have hq := pos_of_mul_pos_right hE (neg_nonneg.2 hz.le)
    have hr : 0 < det (B - A) (E - A) * det (C - A) (D - A) := by
      rw [hid]
      exact sub_pos.2 ((mul_neg_of_neg_of_pos hx hq).trans (mul_pos_of_neg_of_neg hy hp))
    rw [mul_comm] at hr
    exact mul_pos_of_neg_of_neg hx (neg_of_mul_pos_right hr hz.le)

end Model.Euclidean
