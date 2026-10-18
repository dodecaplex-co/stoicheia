import Elements.Figure.Basics
import Elements.BookI.Prop21
import Elements.BookIII.Prop21

/-!
# Stage 3, staged: III.23, point by point

Statements before proofs (brief 0006, stage 3). A companion of III.23, destined for
`Elements/BookIII/Prop23.lean`, after III.23, and certified as "III.23 point" (brief 0006).

III.23 says that on one straight line, on one side, there cannot be two similar and unequal
segments. Point by point: on one side of a chord, a point is on the circle exactly when the
chord subtends at it the angle in the segment, and within the circle exactly when it subtends
a greater angle.

III.24 cites it for the cases Euclid leaves to III.23: a segment that would fall within the
other, or outside it, is disposed of by a tacit reference to III.23, as Heath notes in his
commentary on III.24 (vol. 2, p. 54). As III.23's companion, the dependency shows in III.24's
certificate.
-/

namespace Elements.BookIII

open Tacit

/-- If M lies between A and B, and Q between M and the opposite corner P, then Q
lies within the triangle PAB. This supplies the interior point for I.21 in each
circle case: Q lies on P's side of AB, A's side of BP, and B's side of PA. -/
theorem Prop23.insideTriangle_of_between {A B M P Q : Point} (hABP : Triangle A B P)
    (hAMB : Between A M B) (hMQP : Between M Q P) : InsideTriangle Q P A B := by
  /- For either end X of the base, with Y the other: M is on X's side of YP, and the
     ray from P through M keeps Q on that side too. -/
  have side : ∀ {X Y : Point}, Triangle X Y P → Between X M Y → SameSideOf Q X Y P := by
    intro X Y hXYP hXMY
    obtain ⟨K, hY_K, hP_K⟩ := Postulate1 Y P hXYP.ne₂₃
    have hM_K : ¬ OnLine M K := fun hM_K =>
      hXYP.bca.off_line hY_K hP_K (on_line_of_between (between_symm hXMY) hY_K hM_K)
    have hMX : SameSideOf M X P Y :=
      SameSideOf.of_line hXYP.ne₂₃.symm hP_K hY_K
        (pasch2 (between_symm hXMY) hY_K hM_K)
    exact (SameSideOf.of_onRay (OnRay.of_between (between_symm hMQP)) hMX).swap
  refine ⟨?_, side hABP hAMB, (side hABP.bac (between_symm hAMB)).swap⟩
  /- MQ leaves AB at M, so Q and P are on the same side of AB. -/
  refine ⟨hABP.ne₁₂, fun L hA_L hB_L => ?_⟩
  have hM_L : OnLine M L := on_line_of_between_ends hAMB hA_L hB_L
  have hQ_L : ¬ OnLine Q L := fun hQ_L =>
    hABP.off_line hA_L hB_L (on_line_of_between hMQP hM_L hQ_L)
  exact pasch2 hMQP hM_L hQ_L

/-- **On the circle, by the angle.** Let A, B, E be points of a circle with a centre, and P a
point on E's side of AB. Then P is on the circle exactly when the angle APB is equal to the
angle AEB, and P is within the circle exactly when the angle APB is greater than the angle
AEB.

To be proved through a point M between A and B, which is within the circle. On the circle,
the angles in the same segment are equal [III. 21]. Outside it, the finite straight line PM
meets the arc at a point Q, which is within the triangle ABP, so the angle AQB is greater
than the angle APB [I. 21]. Within it, MP produced beyond P meets the circle at a point Q,
and P is within the triangle ABQ, so the angle APB is greater than the angle AQB [I. 21]. In
both, Q is on E's side of AB, and the angle AQB is equal to the angle AEB [III. 21]. (A plan
that draws AP on fails when AP touches the circle at A.)

A companion of III.23 ("III.23 point"): its content, point by point. III.24 cites it. -/
theorem Prop23.point {A B E P : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hA : OnCircle A α) (hB : OnCircle B α) (hE : OnCircle E α) (hPE : SameSideOf P E A B) :
    (OnCircle P α ↔ ∠ A P B = ∠ A E B) ∧ (InsideCircle P α ↔ ∠ A E B < ∠ A P B) := by
  /- Take M between A and B. A chord's interior lies within the circle. -/
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hPE.1
  obtain ⟨M, hM_L, hAMB, -⟩ := exists_point_between hA_L hB_L hPE.1 []
  have hM_in : InsideCircle M α := inside_of_between (Or.inr hA) (Or.inr hB) hAMB
  have hP_L : ¬ OnLine P L := hPE.triangle.off_line hA_L hB_L
  have hMP : M ≠ P := fun e => hP_L (e ▸ hM_L)
  obtain ⟨N, hM_N, hP_N⟩ := Postulate1 M P hMP
  /- On the circle, APB and AEB are angles in the same segment [III. 21]. -/
  have on_angle (hP_on : OnCircle P α) : ∠ A P B = ∠ A E B :=
    Prop21 hα hP_on hA hB hE hPE
  /- Outside, PM meets the circle at Q between M and P. Q lies within the triangle
     PAB, so the angle AQB is greater than the angle APB [I. 21]. -/
  have outside_angle (hP_out : OutsideCircle P α) : ∠ A P B < ∠ A E B := by
    obtain ⟨Q, hQ_on, -, hMQP⟩ := line_circle_between hM_in hM_N hP_out hP_N
    have hQ_in : InsideTriangle Q P A B :=
      Prop23.insideTriangle_of_between hPE.triangle hAMB hMQP
    have hangle : ∠ A P B < ∠ A Q B := (BookI.Prop21 hPE.triangle.cab hQ_in).2
    /- Q is on E's side of AB, so the angle AQB is equal to the angle AEB [III. 21]. -/
    have hQE : SameSideOf Q E A B := hQ_in.1.trans hPE
    rw [Prop21 hα hQ_on hA hB hE hQE] at hangle
    exact hangle
  /- Within, MP produced beyond P meets the circle at Q. Q is on P's side of AB, and so
     on E's; P lies within the triangle QAB, so the angle APB is greater than the angle
     AQB [I. 21]. -/
  have inside_angle (hP_in : InsideCircle P α) : ∠ A E B < ∠ A P B := by
    obtain ⟨Q, hQ_on, -, hQPM⟩ := line_circle_beyond hP_in hP_N hM_N hMP
    have hPQ : SameSideOf P Q A B :=
      SameSideOf.of_line hPE.1 hA_L hB_L (pasch2 (between_symm hQPM) hM_L hP_L)
    have hQE : SameSideOf Q E A B := hPQ.symm.trans hPE
    have hP_triangle : InsideTriangle P Q A B :=
      Prop23.insideTriangle_of_between hQE.triangle hAMB (between_symm hQPM)
    have hangle : ∠ A Q B < ∠ A P B := (BookI.Prop21 hQE.triangle.cab hP_triangle).2
    /- The angle AQB is again equal to the angle AEB [III. 21]. -/
    rw [Prop21 hα hQ_on hA hB hE hQE] at hangle
    exact hangle
  /- P is within the circle, on it, or outside it. Equal angles rule out within and
     outside, and a greater angle rules out on and outside, since no angle is less than
     itself. -/
  refine ⟨⟨on_angle, ?_⟩, ⟨inside_angle, ?_⟩⟩
  · intro heq
    apply Classical.byContradiction
    intro hP_not_on
    by_cases hP_in : InsideCircle P α
    · have hlt := inside_angle hP_in
      rw [heq] at hlt
      exact lt_irrefl _ hlt
    · have hlt := outside_angle ⟨hP_in, hP_not_on⟩
      rw [heq] at hlt
      exact lt_irrefl _ hlt
  · intro hlt
    apply Classical.byContradiction
    intro hP_not_in
    by_cases hP_on : OnCircle P α
    · rw [on_angle hP_on] at hlt
      exact lt_irrefl _ hlt
    · exact lt_irrefl _ (lt_trans hlt (outside_angle ⟨hP_not_in, hP_on⟩))

end Elements.BookIII
