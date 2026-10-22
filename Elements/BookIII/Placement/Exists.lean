import Elements.Figure.Basics
import Elements.BookI.Prop02
import Elements.BookI.Prop03
import Elements.BookI.Prop20
import Elements.BookI.Prop22

/-!
# Placement: where a point goes

One of the five files of placement's cases (`Elements/BookIII/Placement.lean` gathers them).
On equal straight lines AB, CD, a point P is sent to a point Q as far from C as P is from
A, and as far from D as P is from B. These say that such a point exists: on F's side of CD
when P is off AB, by I.22, I.20 giving the triangle's condition; and on CD when P is on AB,
by I.3 between the ends, and beyond them by producing CD, I.2 first placing the length at
its end (`Placement.exists_on_beyond`).
-/

namespace Elements.BookIII

open Tacit

/-- **A point off the base has a place.** On equal straight lines AB, CD, for a point P off
AB there is a point Q on F's side of CD as far from C as P is from A, and as far from D as P
is from B.

Proved by I.22, the triangle with sides AP, CD, BP on CD towards F, its three straight
lines meeting I.20's condition because ABP is a triangle; the point I.22 finds on the ray CD
at the distance CD is D itself (`OnRay.eq_of_len_eq`). -/
theorem Placement.exists_off {A B C D F P : Point} (hlen : ‖A B‖ = ‖C D‖)
    (hF : ¬ Collinear C D F) (hP : ¬ Collinear A B P) :
    ∃ Q : Point, SameSideOf Q F C D ∧ ‖C Q‖ = ‖A P‖ ∧ ‖D Q‖ = ‖B P‖ := by
  /- I.20, in the triangle ABP, supplies each of the three conditions for constructing a
     triangle out of AP, CD, BP by I.22, AB being equal to CD. -/
  obtain ⟨hBP_BA_AP, hAP_AB_BP, hAB_BP_PA⟩ := BookI.Prop20 hP
  have hAP_CD_gt_BP : ‖B P‖ < ‖A P‖ + ‖C D‖ := by
    rw [← hlen, add_comm, ← len_symm B A]
    exact hBP_BA_AP
  have hAP_BP_gt_CD : ‖C D‖ < ‖A P‖ + ‖B P‖ := by
    rw [← hlen, add_comm, ← len_symm P A]
    exact hAB_BP_PA
  have hCD_BP_gt_AP : ‖A P‖ < ‖C D‖ + ‖B P‖ := by
    rw [← hlen]
    exact hAP_AB_BP
  /- I.22, its F, E and P being C, D and F here, builds the triangle on the ray CD, on F's
     side: KC is AP, CG is CD, GK is BP. -/
  obtain ⟨G, K, hG_ray, hKF, hKC, hCG, hGK⟩ :=
    BookI.Prop22 (F := C) (E := D) (P := F)
      hAP_CD_gt_BP hAP_BP_gt_CD hCD_BP_gt_AP (Triangle.ne₁₂ hF) hF
  /- The point on the ray CD at distance CD from C is D itself. -/
  have hGD : G = D := hG_ray.eq_of_len_eq hCG
  subst G
  exact ⟨K, hKF, (len_symm C K).trans hKC, hGK⟩

/-- Produce CD beyond D by the length XY, the construction used for points beyond
either end of the base. I.2 first places XY at D; `OnRay.exists_len_eq` puts that
length on the produced ray, and `OnRay.between` puts its endpoint beyond D. -/
theorem Placement.exists_on_beyond {C D X Y : Point} (hCD : C ≠ D) (hXY : X ≠ Y) :
    ∃ Q : Point, Between C D Q ∧ ‖D Q‖ = ‖X Y‖ := by
  obtain ⟨E, hCDE⟩ := produce hCD
  obtain ⟨R, hDR⟩ := BookI.Prop2 D X Y hXY
  obtain ⟨Q, hQ_ray, hDQ⟩ :=
    OnRay.exists_len_eq (ne_of_len_eq hDR hXY) (ne_of_between (between_symm hCDE)).symm
  exact ⟨Q, hQ_ray.between hCDE, hDQ.trans hDR⟩

/-- **A point of the base has a place.** On equal straight lines AB, CD, for a point P on
the straight line AB there is a point Q on the straight line CD as far from C as P is from
A, and as far from D as P is from B.

Proved case by case: P at A or B goes to C or D; P between A and B goes to the point cut
off from CD by I.3; P beyond B (or beyond A) goes to the point on CD produced beyond D (or C)
at the distance BP (AP), by `produce`, I.2 and `OnRay.exists_len_eq`
(`Placement.exists_on_beyond`). -/
theorem Placement.exists_on {A B C D P : Point} (hlen : ‖A B‖ = ‖C D‖) (hAB : A ≠ B)
    (hP : Collinear A B P) :
    ∃ Q : Point, Collinear C D Q ∧ ‖C Q‖ = ‖A P‖ ∧ ‖D Q‖ = ‖B P‖ := by
  have hCD : C ≠ D := ne_of_len_eq hlen.symm hAB
  obtain ⟨CD, hC_CD, hD_CD⟩ := Postulate1 C D hCD
  by_cases hPA : P = A
  · /- P is A, and Q is C. -/
    subst P
    exact ⟨C, ⟨CD, hC_CD, hD_CD, hC_CD⟩, by rw [len_self, len_self],
      by rw [len_symm D C, len_symm B A, hlen]⟩
  by_cases hPB : P = B
  · /- P is B, and Q is D. -/
    subst P
    exact ⟨D, ⟨CD, hC_CD, hD_CD, hD_CD⟩, hlen.symm, by rw [len_self, len_self]⟩
  have hAP : A ≠ P := Ne.symm hPA
  have hBP : B ≠ P := Ne.symm hPB
  obtain ⟨AB, hA_AB, hB_AB, hP_AB⟩ := hP
  rcases between_cases hAP hBP.symm hAB hA_AB hP_AB hB_AB with hAPB | hPAB | hABP
  · /- P is between A and B; I.3 cuts CQ equal to AP from CD. -/
    have hAP_CD : ‖A P‖ < ‖C D‖ := by
      rw [← hlen]
      exact len_lt_of_between hAPB
    obtain ⟨Q, hCQD, hCQ⟩ := BookI.Prop3 hAP hAP_CD
    /- Taking CQ and AP from the equal wholes CD and AB leaves DQ equal to BP. -/
    have hDQ : ‖D Q‖ = ‖B P‖ := by
      apply CommonNotion3 (c := ‖C Q‖) (d := ‖A P‖) _ hCQ
      rw [len_symm D Q, add_comm ‖Q D‖, len_add_of_between hCQD,
        len_symm B P, add_comm ‖P B‖, len_add_of_between hAPB, hlen]
    exact ⟨Q, ⟨CD, hC_CD, hD_CD, on_line_of_between_ends hCQD hC_CD hD_CD⟩, hCQ, hDQ⟩
  · /- P is beyond A; Q goes beyond C on DC produced, with CQ equal to AP. -/
    obtain ⟨Q, hDCQ, hCQ⟩ := Placement.exists_on_beyond hCD.symm hAP
    have hDQ : ‖D Q‖ = ‖B P‖ := by
      calc
        ‖D Q‖ = ‖D C‖ + ‖C Q‖ := (len_add_of_between hDCQ).symm
        _ = ‖B A‖ + ‖A P‖ := by rw [hCQ, len_symm D C, ← hlen, len_symm B A]
        _ = ‖B P‖ := len_add_of_between (between_symm hPAB)
    exact ⟨Q, ⟨CD, hC_CD, hD_CD, on_line_of_between hDCQ hD_CD hC_CD⟩, hCQ, hDQ⟩
  · /- P is beyond B; Q goes beyond D on CD produced, with DQ equal to BP. -/
    obtain ⟨Q, hCDQ, hDQ⟩ := Placement.exists_on_beyond hCD hBP
    have hCQ : ‖C Q‖ = ‖A P‖ := by
      calc
        ‖C Q‖ = ‖C D‖ + ‖D Q‖ := (len_add_of_between hCDQ).symm
        _ = ‖A B‖ + ‖B P‖ := by rw [hDQ, ← hlen]
        _ = ‖A P‖ := len_add_of_between hABP
    exact ⟨Q, ⟨CD, hC_CD, hD_CD, on_line_of_between hCDQ hC_CD hD_CD⟩, hCQ, hDQ⟩

end Elements.BookIII
