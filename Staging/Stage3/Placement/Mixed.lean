import Elements.Figure.Basics
import Elements.BookI.Prop04
import Elements.BookI.Prop08
import Staging.Stage3.Degenerate

/-!
# Stage 3, staged: placement, a point of the base and a point off it

Statements before proofs (brief 0006, stage 3). One file of `Elements/BookIII/Placement/`.
-/

namespace Elements.BookIII

open Tacit

/-- **The mixed case, measured from A.** The step "say from A" of `dist_on_off`, for P on the
ray AB: I.8 gives the angle at A, the rays through P and P' keep it, and I.4 gives the
distance. `dist_on_off` uses it from A, and from B with the bases read as BA and DC. -/
theorem Placement.dist_on_off.from_ray {A B C D P Q P' Q' : Point}
    (hlen : ‖A B‖ = ‖C D‖) (hPray : OnRay P A B) (hQ : Triangle A B Q)
    (hP' : Collinear C D P') (hQ' : Triangle C D Q')
    (hP₁ : ‖C P'‖ = ‖A P‖) (hP₂ : ‖D P'‖ = ‖B P‖)
    (hQ₁ : ‖C Q'‖ = ‖A Q‖) (hQ₂ : ‖D Q'‖ = ‖B Q‖) : ‖P' Q'‖ = ‖P Q‖ := by
  /- The triangles ABQ, CDQ' have their three sides equal, so the angles BAQ, DCQ' are
     equal. [I. 8] -/
  have hbase : ∠ B A Q = ∠ D C Q' := BookI.Prop8 hQ hQ' hlen hQ₁.symm hQ₂.symm
  /- P' is on the ray CD as P is on the ray AB: the three distances decide it. -/
  have horder : Between P A B ↔ Between P' C D :=
    BookI.Prop20.between_congr
      (by rw [len_symm P B, len_symm P' D]; exact hP₂.symm)
      (by rw [len_symm P A, len_symm P' C]; exact hP₁.symm)
      (by rw [len_symm B A, len_symm D C]; exact hlen)
  have hP'ray : OnRay P' C D :=
    ⟨hQ'.ne₁₂, (ne_of_len_eq hP₁ hPray.2.1.symm).symm, hP',
      fun h => hPray.2.2.2 (horder.mpr h)⟩
  /- So the angles PAQ, P'CQ' are the angles BAQ, DCQ' again. -/
  have hangle : ∠ P A Q = ∠ P' C Q' := calc
    ∠ P A Q = ∠ B A Q := angle_onRay_left hPray hQ.ne₁₃.symm
    _ = ∠ D C Q' := hbase
    _ = ∠ P' C Q' := (angle_onRay_left hP'ray hQ'.ne₁₃.symm).symm
  /- P and P' differ from the starts of their rays, and Q and Q' are off the
     bases. Thus APQ and CP'Q' are triangles, with two sides and the angle between them
     equal, and their bases PQ, P'Q' are equal. [I. 4] -/
  obtain ⟨L, hAL, hBL, hPL⟩ := hPray.2.2.1
  have hAPQ : Triangle A P Q :=
    Triangle.of_line hAL hPL hPray.2.1.symm (hQ.off_line hAL hBL)
  obtain ⟨M, hCM, hDM, hP'M⟩ := hP'
  have hCP'Q' : Triangle C P' Q' :=
    Triangle.of_line hCM hP'M hP'ray.2.1.symm (hQ'.off_line hCM hDM)
  exact (BookI.Prop4 hAPQ hCP'Q' hP₁.symm hQ₁.symm hangle).1.symm

/-- **A point of the base and a point off it keep their distance.** On equal straight lines
AB, CD, let P be a point of the straight line AB and Q a point off it; let P' be a point of
the straight line CD and Q' a point off it, each as far from C as its fellow is from A, and
from D as its fellow is from B. Then P'Q' is equal to PQ. (Which side of CD Q' is on does not
matter.)

To be proved with the base point chosen so that P lies on the ray from it through the other
end: from A when P is on the ray AB, from B when A lies between P and B. Say from A: the
triangles ABQ, CDQ' have their sides equal, so the angles BAQ, DCQ' are equal [I. 8]; P' is
on the ray CD as P is on the ray AB (`Prop20.between_congr`); so the angles PAQ, P'CQ' are
those same angles, and the triangles APQ, CP'Q' give PQ equal to P'Q' [I. 4]. P at A or B is
immediate. No supplementary angles arise. -/
theorem Placement.dist_on_off {A B C D P Q P' Q' : Point} (hlen : ‖A B‖ = ‖C D‖)
    (hP : Collinear A B P) (hQ : ¬ Collinear A B Q) (hP' : Collinear C D P')
    (hQ' : ¬ Collinear C D Q') (hP₁ : ‖C P'‖ = ‖A P‖) (hP₂ : ‖D P'‖ = ‖B P‖)
    (hQ₁ : ‖C Q'‖ = ‖A Q‖) (hQ₂ : ‖D Q'‖ = ‖B Q‖) : ‖P' Q'‖ = ‖P Q‖ := by
  /- P at A goes to C, and P at B to D; then P'Q' is one of the given distances. -/
  by_cases hPA : P = A
  · subst P
    have hP'C : P' = C := (eq_of_len_eq_zero (hP₁.trans (len_self A))).symm
    subst P'
    exact hQ₁
  by_cases hPB : P = B
  · subst P
    have hP'D : P' = D := (eq_of_len_eq_zero (hP₂.trans (len_self B))).symm
    subst P'
    exact hQ₂
  have hABQ : Triangle A B Q := hQ
  have hCDQ' : Triangle C D Q' := hQ'
  by_cases hPAB : Between P A B
  · /- P is beyond A from B, so on the ray BA: read the bases as BA and DC. -/
    have hreverse : ‖B A‖ = ‖D C‖ := by rw [len_symm B A, len_symm D C]; exact hlen
    have hP'reverse : Collinear D C P' := by
      obtain ⟨L, hCL, hDL, hP'L⟩ := hP'
      exact ⟨L, hDL, hCL, hP'L⟩
    exact dist_on_off.from_ray hreverse (OnRay.of_beyond (between_symm hPAB))
      hABQ.bac hP'reverse hCDQ'.bac hP₂ hP₁ hQ₂ hQ₁
  · /- P is on the ray AB, so measure from A and C. -/
    exact dist_on_off.from_ray hlen ⟨hABQ.ne₁₂, hPA, hP, hPAB⟩ hABQ hP' hCDQ'
      hP₁ hP₂ hQ₁ hQ₂

end Elements.BookIII
