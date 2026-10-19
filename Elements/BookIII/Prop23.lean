import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop16
import Elements.BookI.Prop21
import Elements.BookIII.Prop02
import Elements.BookIII.Prop10
import Elements.BookIII.Prop21

/-!
# Book III, Proposition 23

Euclid's text, in Heath's translation: [`heath/III/23.md`](../../heath/III/23.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

After it comes its companion, `Prop23.point`: III.23's content point by point. On one side
of a straight line AB in a circle, a point is on the circle exactly when AB subtends at it
the angle in the segment, and within the circle exactly when AB subtends a greater angle.
III.24 cites it for the cases Euclid leaves to III.23, a segment falling within the other or
outside it, which Heath says are disposed of by a tacit reference to III.23
(vol. 2, p. 54).
-/

namespace Elements.BookIII

open Tacit

/-- On the same straight line there cannot be constructed two similar and unequal segments of
circles on the same side. -/
theorem Prop23 {A B C D : Point} {ACB ADB : Circle} (hACB : ∃ O : Point, Centre O ACB)
    (hADB : ∃ O : Point, Centre O ADB) (hA₁ : OnCircle A ACB) (hB₁ : OnCircle B ACB)
    (hC : OnCircle C ACB) (hA₂ : OnCircle A ADB) (hB₂ : OnCircle B ADB)
    (hD : OnCircle D ADB) (hCD : SameSideOf C D A B) (hsim : ∠ A C B = ∠ A D B) :
    ACB = ADB := by
  -- For, if possible, on the same straight line AB let two similar and unequal segments of
  -- circles ACB, ADB be constructed on the same side;
  refine Classical.byContradiction fun hne => ?_
  have hABC : Triangle A B C := hCD.triangle
  have hAB : A ≠ B := hCD.1
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  have hC_AB : ¬ OnLine C AB := hABC.off_line hA_AB hB_AB
  -- let ACD be drawn through, and let CB, DB be joined.
  /- This is Robert Simson's preliminary. The circles meet at A and B, so not at C [III.
     10], and C is within the circle ADB or outside it. If within, AC drawn through meets
     ADB at D₀; if outside, the segments are the other way about: MC, from a point M between
     A and B, meets ADB at D₁ within ACB, and AD₁ drawn through meets ACB at C₀. Either way
     a point P of one segment lies within the other, and AP drawn through meets it at Q,
     where III.21 carries the angle. -/
  have hC₂ : ¬ OnCircle C ADB := fun hC₂ =>
    hne (Prop10 hACB hADB hA₁ hA₂ hB₁ hB₂ hC hC₂ hAB hABC.ne₁₃ hABC.ne₂₃)
  obtain ⟨P, Q, hAPQ, hP_AB, hangles⟩ : ∃ P Q : Point, Between A P Q ∧ ¬ OnLine P AB ∧
      ((∠ A P B = ∠ A C B ∧ ∠ A Q B = ∠ A D B) ∨
        (∠ A P B = ∠ A D B ∧ ∠ A Q B = ∠ A C B)) := by
    by_cases hin : InsideCircle C ADB
    · obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hABC.ne₁₃
      obtain ⟨D₀, hD₀, -, hD₀CA⟩ := line_circle_beyond hin hC_AC hA_AC hABC.ne₁₃
      have hD₀C : SameSideOf D₀ C A B :=
        SameSideOf.of_onRay (OnRay.of_beyond (between_symm hD₀CA))
          (SameSideOf.of_line hAB hA_AB hB_AB (same_side_refl hC_AB))
      exact ⟨C, D₀, between_symm hD₀CA, hC_AB,
        Or.inl ⟨rfl, (Prop21 hADB hD hA₂ hB₂ hD₀ (hCD.symm.trans hD₀C.symm)).symm⟩⟩
    · obtain ⟨M, hM_AB, hAMB, -⟩ := exists_point_between hA_AB hB_AB hAB []
      have hM₁ : InsideCircle M ACB := Prop2 hACB hA₁ hB₁ M hAMB
      have hM₂ : InsideCircle M ADB := Prop2 hADB hA₂ hB₂ M hAMB
      have hMC : M ≠ C := fun h => hC_AB (h ▸ hM_AB)
      obtain ⟨MC, hM_MC, hC_MC⟩ := Postulate1 M C hMC
      obtain ⟨D₁, hD₁, hD₁_MC, hMD₁C⟩ := line_circle_between hM₂ hM_MC ⟨hin, hC₂⟩ hC_MC
      have hD₁_in : InsideCircle D₁ ACB := Prop2.within hACB (Or.inl hM₁) (Or.inr hC) hMD₁C
      have hD₁_AB : ¬ OnLine D₁ AB := fun h =>
        hC_AB (line_unique (ne_of_between hMD₁C) hM_MC hD₁_MC hM_AB h ▸ hC_MC)
      have hD₁C : SameSideOf D₁ C A B :=
        SameSideOf.of_line hAB hA_AB hB_AB (pasch2 hMD₁C hM_AB hD₁_AB)
      have hAD₁ : A ≠ D₁ := fun h => hD₁_AB (h ▸ hA_AB)
      obtain ⟨AD₁, hA_AD₁, hD₁_AD₁⟩ := Postulate1 A D₁ hAD₁
      obtain ⟨C₀, hC₀, -, hC₀D₁A⟩ := line_circle_beyond hD₁_in hD₁_AD₁ hA_AD₁ hAD₁
      have hC₀D₁ : SameSideOf C₀ D₁ A B :=
        SameSideOf.of_onRay (OnRay.of_beyond (between_symm hC₀D₁A))
          (SameSideOf.of_line hAB hA_AB hB_AB (same_side_refl hD₁_AB))
      exact ⟨D₁, C₀, between_symm hC₀D₁A, hD₁_AB, Or.inr
        ⟨(Prop21 hADB hD hA₂ hB₂ hD₁ (hCD.symm.trans hD₁C.symm)).symm,
         (Prop21 hACB hC hA₁ hB₁ hC₀ (hD₁C.symm.trans hC₀D₁.symm)).symm⟩⟩
  -- Then, since the segment ACB is similar to the segment ADB,
  -- and similar segments of circles are those which admit equal angles, [III. Def. 11]
  have hPQ : ∠ A P B = ∠ A Q B := by
    rcases hangles with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]; exact hsim
    · rw [h₁, h₂]; exact hsim.symm
  -- the angle ACB is equal to the angle ADB, the exterior to the interior: which is
  -- impossible. [I. 16]
  obtain ⟨AP, hA_AP, hP_AP⟩ := Postulate1 A P (ne_of_between hAPQ)
  have hQ_AP : OnLine Q AP := on_line_of_between hAPQ hA_AP hP_AP
  have hB_AP : ¬ OnLine B AP := fun h =>
    hP_AB (line_unique hAB hA_AP h hA_AB hB_AB ▸ hP_AP)
  have hQPB : Triangle Q P B :=
    Triangle.of_line hQ_AP hP_AP (ne_of_between (between_symm hAPQ)) hB_AP
  have h16 := (BookI.Prop16 hQPB.cab (between_symm hAPQ)).1
  rw [angle_onRay_left (OnRay.of_between (between_symm hAPQ)) hQPB.ne₁₃.symm,
    angle_symm hQPB.ne₂₃.symm (ne_of_between hAPQ), ← hPQ] at h16
  exact lt_irrefl _ h16
  -- Therefore etc.
  -- Q. E. D.

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

Proved through a point M between A and B, which is within the circle. On the circle,
the angles in the same segment are equal [III. 21]. Outside it, the finite straight line PM
meets the circle at a point Q, which is within the triangle ABP, so the angle AQB is greater
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
