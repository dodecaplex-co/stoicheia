import Elements.Figure.Basics
import Elements.BookI.Prop04
import Elements.BookI.Prop08
import Elements.BookI.Prop24

/-!
# Stage 3, staged: placement, two points off the base

Statements before proofs (brief 0006, stage 3). One file of `Elements/BookIII/Placement/`.
This is the hardest case, and goes to one strong prover (brief 0005, Step 1).

Two points P, Q on one side of AB are sent to P', Q' on one side of CD. Compare the angles
that AP, AQ make with AB: if they differ, the lesser ray lies within the greater angle, the
difference is the angle PAQ, and at C the same holds; I.4 then gives PQ equal to P'Q'. If
they are equal, P and Q lie on one ray from A; then they do not lie on one ray from B
(unless they are one point), and the comparison is made at B instead. Basing it at
whichever end, A or B, gives unequal angles removes the equal-angle and supplementary-angle
branches. The assembly (`Placement.dist_off_off`) makes the choice.
-/

namespace Elements.BookIII

open Tacit

/-- **One end or the other gives unequal angles.** For two different points P, Q on one side
of AB, the angles BAP, BAQ differ, or the angles ABP, ABQ differ.

To be proved by `onRay_of_angle_eq`: were both pairs equal, Q would lie on the ray AP and on
the ray BP, and those straight lines, different because ABP is a triangle, meet only at P
(System E, Generalities 1). -/
theorem Placement.base_choice {A B P Q : Point} (hPQ : SameSideOf P Q A B) (hne : P ≠ Q) :
    ∠ B A P ≠ ∠ B A Q ∨ ∠ A B P ≠ ∠ A B Q := by
  by_cases hBAP : ∠ B A P = ∠ B A Q
  · right
    intro hABP
    /- If both pairs of angles were equal, Q would lie on the rays AP and BP
       (`onRay_of_angle_eq` in Book Zero). -/
    have hQ_AP : OnRay Q A P := onRay_of_angle_eq hPQ.symm hBAP.symm
    have hQ_BP : OnRay Q B P := onRay_of_angle_eq hPQ.symm.swap hABP.symm
    obtain ⟨-, -, ⟨L, hA_L, hP_L, hQ_L⟩, -⟩ := hQ_AP
    obtain ⟨-, -, ⟨M, hB_M, hP_M, hQ_M⟩, -⟩ := hQ_BP
    /- AP and BP are different straight lines, since ABP is a triangle. But two
       straight lines through the different points P and Q are one (Generalities 1). -/
    have hLM : L ≠ M := fun h => hPQ.triangle ⟨M, h ▸ hA_L, hB_M, hP_M⟩
    exact hLM (line_unique hne hP_L hQ_L hP_M hQ_M)
  · exact Or.inl hBAP

/-- **Two points off the base keep their distance, when the angles at A differ.** On equal
straight lines AB, CD, let P, Q be on one side of AB and P', Q' on one side of CD, each as
far from C as its fellow is from A, and from D as its fellow is from B; and let the angle
BAP be less than the angle BAQ. Then P'Q' is equal to PQ.

To be proved: the triangles ABP, CDP' and ABQ, CDQ' have their sides equal, so the angles
BAP, DCP' and BAQ, DCQ' are equal [I. 8]; P lies within the angle BAQ (`Prop24.within`), and
P' within DCQ', so BAQ is made up of BAP and PAQ, and DCQ' of DCP' and P'CQ'
(`angle_add_of_within`); the remainders PAQ, P'CQ' are equal [C.N. 3]; and the triangles
APQ, CP'Q' give PQ equal to P'Q' [I. 4]. -/
theorem Placement.dist_strict {A B C D P Q P' Q' : Point} (hlen : ‖A B‖ = ‖C D‖)
    (hPQ : SameSideOf P Q A B) (hP'Q' : SameSideOf P' Q' C D)
    (hP₁ : ‖C P'‖ = ‖A P‖) (hP₂ : ‖D P'‖ = ‖B P‖) (hQ₁ : ‖C Q'‖ = ‖A Q‖)
    (hQ₂ : ‖D Q'‖ = ‖B Q‖) (hlt : ∠ B A P < ∠ B A Q) : ‖P' Q'‖ = ‖P Q‖ := by
  /- ABP and CDP' have their three sides equal, as do ABQ and CDQ'. Thus the
     angles they make with the bases are equal [I. 8]. -/
  have hBAP : ∠ B A P = ∠ D C P' :=
    BookI.Prop8 hPQ.triangle hP'Q'.triangle hlen hP₁.symm hP₂.symm
  have hBAQ : ∠ B A Q = ∠ D C Q' :=
    BookI.Prop8 hPQ.symm.triangle hP'Q'.symm.triangle hlen hQ₁.symm hQ₂.symm
  /- These equalities carry the strict inequality from A to C. -/
  have hDCP' : ∠ D C P' < ∠ D C Q' := by
    rw [← hBAP, ← hBAQ]
    exact hlt
  /- The lesser ray lies within the greater angle (`Prop24.within`): P is on
     B's side of AQ, and P' on D's side of CQ'. -/
  have hPB : SameSideOf P B A Q := BookI.Prop24.within hPQ.symm hlt
  have hP'D : SameSideOf P' D C Q' := BookI.Prop24.within hP'Q'.symm hDCP'
  /- Each whole angle is made up of its two parts (`angle_add_of_within`). -/
  have hBAQ_sum : ∠ B A Q = ∠ B A P + ∠ P A Q := angle_add_of_within hPQ hPB
  have hDCQ'_sum : ∠ D C Q' = ∠ D C P' + ∠ P' C Q' := angle_add_of_within hP'Q' hP'D
  /- Subtract the equal angles BAP and DCP' from the equal wholes BAQ and DCQ'.
     The remainders PAQ and P'CQ' are equal [C.N. 3]. -/
  have hwholes : ∠ P A Q + ∠ B A P = ∠ P' C Q' + ∠ D C P' := by
    rw [add_comm (∠ P A Q), add_comm (∠ P' C Q'), ← hBAQ_sum, ← hDCQ'_sum]
    exact hBAQ
  have hPAQ : ∠ P A Q = ∠ P' C Q' := CommonNotion3 hwholes hBAP
  /- P is off AQ and P' off CQ', so APQ and CP'Q' are triangles. Their sides
     about the equal angles are equal, and I.4 gives their bases equal. -/
  have hAPQ : Triangle A P Q := hPB.triangle.acb
  have hCP'Q' : Triangle C P' Q' := hP'D.triangle.acb
  exact (BookI.Prop4 hAPQ hCP'Q' hP₁.symm hQ₁.symm hPAQ).1.symm

end Elements.BookIII
