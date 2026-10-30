import Elements.Figure.Basics
import Elements.BookI.Prop02
import Elements.BookI.Prop03

/-!
# Book I, Proposition 22

Euclid's text, in Heath's translation: [`heath/I/22.md`](../../heath/I/22.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid names the three given straight lines by single letters, A, B, C. In Lean
they are the finite straight lines A₁A₂, B₁B₂, C₁C₂.

The statement says more than Euclid's, so that I.23 can use it as Euclid does:
the triangle KFG is put in a given place. Its corner F is a given point,
its side FG lies along the given ray from F through E, and K falls on the
side of FE where the given point P is. Euclid's straight line DE is then
set out through F, with D behind F and DF equal to A, and from there his
proof goes through as he writes it.
-/

namespace Elements.BookI

open Tacit

/-! ## What Euclid reads off the figure -/

/-- None of the three given straight lines is nothing. If `a` were nothing, the
other two would each be greater than the other: `c` less than `b` (from `a`, `b`
greater than `c`) and `b` less than `c` (from `a`, `c` greater than `b`). Euclid
calls A, B, C straight lines, so for him the question never arises; in our
foundations a finite straight line is a pair of points, which may coincide, and
I.3 wants them apart. -/
theorem Prop22.ne_zero {k : Kind} {a b c : Magnitude k} (h₁ : c < a + b) (h₂ : b < a + c) :
    a ≠ 0 := by
  intro h
  subst h
  rw [add_comm 0 b, add_zero] at h₁
  rw [add_comm 0 c, add_zero] at h₂
  exact lt_irrefl _ (lt_trans h₁ h₂)

/-- Room to cut off a given straight line. Euclid's DE is "of infinite length in
the direction of E", so that whatever is to be cut off from it, there is room.
Our `Line` is a whole straight line, with no length to cut from, and I.3 cuts off
only from a greater finite straight line; so we find a point Z on DF produced
beyond F with FZ greater than the given straight line X₁X₂. At F place a straight
line FY equal to X₁X₂ [I. 2], and produce DF beyond F further than FY
(`produce_longer`, as in I.11). -/
theorem Prop22.room {D F X₁ X₂ : Point} (hDF : D ≠ F) (hX : X₁ ≠ X₂) :
    ∃ Z : Point, Between D F Z ∧ ‖X₁ X₂‖ < ‖F Z‖ := by
  obtain ⟨Y, hFY⟩ := Prop2 F X₁ X₂ hX
  obtain ⟨Z, hDFZ, hFY_FZ⟩ := produce_longer hDF (ne_of_len_eq hFY hX)
  refine ⟨Z, hDFZ, ?_⟩
  rw [← hFY]
  exact hFY_FZ

/-- The circles meet. Euclid takes K where the circle about F and the circle
about G cut one another, and never says why they should. Heath's own argument
(vol. 1, p. 294) is that the circle about G has a point outside the circle about
F, and a point inside it.

* H is outside: FH is FG and GH together, which is greater than FD.
* The point M where GF (produced if need be) cuts the circle about G is
  inside. GM is equal to GH. If M falls between G and F, then FM and
  GH together make FG, which is less than FD and GH together, so FM is
  less than FD. If M falls beyond F, then FM and FG together make GM,
  that is GH, which is less than FD and FG together, so again FM is less
  than FD. And if M is F, it is the centre.

Then the two circles cut one another (System E, Intersection 4, in LeanEuclid's
corrected form): this is the "Principle of Continuity" that Heath invokes here, as he
does for I.1. -/
theorem Prop22.meet {D F G H : Point} {α β : Circle} (hFGH : Between F G H)
    (hF_α : Centre F α) (hD_α : OnCircle D α) (hG_β : Centre G β) (hH_β : OnCircle H β)
    (h₁ : ‖G H‖ < ‖F D‖ + ‖F G‖) (h₂ : ‖F G‖ < ‖F D‖ + ‖G H‖)
    (h₃ : ‖F D‖ < ‖F G‖ + ‖G H‖) : CirclesMeet β α := by
  /- H is outside the circle about F. -/
  have hH_out : OutsideCircle H α :=
    outside_of_len_gt hF_α hD_α (by rw [← len_add_of_between hFGH]; exact h₃)
  /- M is on the ray from G through F, at the distance GH from G: it is
     where the straight line HG, produced beyond the centre G, cuts the circle
     about G (System E, Intersections 5). -/
  have hFG : F ≠ G := ne_of_between hFGH
  obtain ⟨L, hF_L, hG_L⟩ := Postulate1 F G hFG
  have hH_L : OnLine H L := on_line_of_between hFGH hF_L hG_L
  obtain ⟨M, hM_β, hM_L, hMGH⟩ :=
    line_circle_beyond (centre_inside hG_β) hG_L hH_L (ne_of_between (between_symm hFGH))
  have hGM : ‖G M‖ = ‖G H‖ := Definition15 hG_β hM_β hH_β
  have hM_ray : OnRay M G F :=
    ⟨hFG.symm, ne_of_between hMGH, ⟨L, hG_L, hF_L, hM_L⟩,
      not_between_of_between_between (between_symm hMGH) (between_symm hFGH)⟩
  have hF_ray : OnRay F G F := OnRay.self hFG.symm
  /- M is inside the circle about F. -/
  have hM_in : InsideCircle M α := by
    rcases lt_trichotomy ‖G M‖ ‖G F‖ with h | h | h
    · /- M falls between G and F. -/
      have hGMF : Between G M F := hM_ray.between_of_len_lt hF_ray h
      have hsum : ‖F M‖ + ‖G H‖ = ‖F G‖ := by
        rw [← hGM, len_symm G M]
        exact len_add_of_between (between_symm hGMF)
      refine inside_of_len_lt hF_α hD_α (Magnitude.lt_of_add_lt_add_right (a := ‖G H‖) ?_)
      rw [hsum]
      exact h₂
    · /- M is F itself, the centre. -/
      rw [hM_ray.eq_of_len_eq h]
      exact centre_inside hF_α
    · /- M falls beyond F. -/
      have hGFM : Between G F M := hF_ray.between_of_len_lt hM_ray h
      have hsum : ‖F M‖ + ‖F G‖ = ‖G H‖ := by
        rw [← hGM, add_comm, len_symm F G]
        exact len_add_of_between hGFM
      refine inside_of_len_lt hF_α hD_α (Magnitude.lt_of_add_lt_add_right (a := ‖F G‖) ?_)
      rw [hsum]
      exact h₁
  exact circlesMeet_of_centre hG_β hM_β (Or.inr hH_β) hM_in hH_out

/-- Out of three straight lines, which are equal to three given straight lines, to construct a
triangle: thus it is necessary that two of the straight lines taken together in any manner
should be greater than the remaining one. [I. 20] -/
theorem Prop22 {A₁ A₂ B₁ B₂ C₁ C₂ E F P : Point}
    (hAB : ‖C₁ C₂‖ < ‖A₁ A₂‖ + ‖B₁ B₂‖) (hAC : ‖B₁ B₂‖ < ‖A₁ A₂‖ + ‖C₁ C₂‖)
    (hBC : ‖A₁ A₂‖ < ‖B₁ B₂‖ + ‖C₁ C₂‖) (hFE : F ≠ E) (hP : ¬ Collinear F E P) :
    ∃ G K : Point, OnRay G F E ∧ SameSideOf K P F E ∧
      ‖K F‖ = ‖A₁ A₂‖ ∧ ‖F G‖ = ‖B₁ B₂‖ ∧ ‖G K‖ = ‖C₁ C₂‖ := by
  -- Let the three given straight lines be A, B, C, and of these let two taken together in any
  -- manner be greater than the remaining one,
  /- Straight lines, and so none of them is nothing (`Prop22.ne_zero`): each has
     two different ends, as I.3 will want. -/
  have hA : A₁ ≠ A₂ := fun e => Prop22.ne_zero hAB hAC (by rw [e]; exact len_self A₂)
  have hB : B₁ ≠ B₂ := fun e =>
    Prop22.ne_zero (by rw [add_comm]; exact hAB) hBC (by rw [e]; exact len_self B₂)
  have hC : C₁ ≠ C₂ := fun e =>
    Prop22.ne_zero (by rw [add_comm]; exact hAC) (by rw [add_comm]; exact hBC)
      (by rw [e]; exact len_self C₂)
  -- namely A, B greater than C,
  have hAB_C : ‖C₁ C₂‖ < ‖A₁ A₂‖ + ‖B₁ B₂‖ := hAB
  -- A, C greater than B,
  have hAC_B : ‖B₁ B₂‖ < ‖A₁ A₂‖ + ‖C₁ C₂‖ := hAC
  -- and B, C greater than A;
  have hBC_A : ‖A₁ A₂‖ < ‖B₁ B₂‖ + ‖C₁ C₂‖ := hBC
  -- thus it is required to construct a triangle out of straight lines equal to A, B, C.
  -- Let there be set out a straight line DE, terminated at D but of infinite length in the
  -- direction of E,
  /- The straight line DE is the straight line through the given points F and E
     [Post. 1]. Its end D is not given: it is set out behind F, at the distance A,
     in the next breath. -/
  obtain ⟨DE, hF_DE, hE_DE⟩ := Postulate1 F E hFE
  have hP_DE : ¬ OnLine P DE := fun h => hP ⟨DE, hF_DE, hE_DE, h⟩
  -- and let DF be made equal to A, FG equal to B, and GH equal to C. [I. 3]
  /- Three times I.3, each time cutting off from a straight line produced far
     enough to cut from (`Prop22.room`): FD from EF produced beyond F, FG from DF
     produced beyond F, and GH from FG produced beyond G. So D, F, G, H lie in that
     order along DE, as in Euclid's figure (`between_cut`), and G lies on the ray
     from F through E. -/
  obtain ⟨X, hEFX, hA_FX⟩ := Prop22.room hFE.symm hA
  obtain ⟨D, hFDX, hFD⟩ := Prop3 hA hA_FX
  have hDFE : Between D F E := between_symm (between_cut hEFX hFDX)
  obtain ⟨Y, hDFY, hB_FY⟩ := Prop22.room (ne_of_between hDFE) hB
  obtain ⟨G, hFGY, hFG⟩ := Prop3 hB hB_FY
  have hDFG : Between D F G := between_cut hDFY hFGY
  obtain ⟨Z, hFGZ, hC_GZ⟩ := Prop22.room (ne_of_between hFGY) hC
  obtain ⟨H, hGHZ, hGH⟩ := Prop3 hC hC_GZ
  have hFGH : Between F G H := between_cut hFGZ hGHZ
  have hD_DE : OnLine D DE := on_line_of_between (between_symm hDFE) hE_DE hF_DE
  have hG_DE : OnLine G DE := on_line_of_between hDFG hD_DE hF_DE
  have hG_ray : OnRay G F E :=
    ⟨hFE, (ne_of_between hFGY).symm, ⟨DE, hF_DE, hE_DE, hG_DE⟩,
      not_between_of_between_between hDFG hDFE⟩
  -- With centre F and distance FD let the circle DKL be described;
  obtain ⟨DKL, hF_DKL, hD_DKL⟩ := Postulate3 F D (ne_of_between hDFE).symm
  -- again, with centre G and distance GH let the circle KLH be described;
  obtain ⟨KLH, hG_KLH, hH_KLH⟩ := Postulate3 G H (ne_of_between hGHZ)
  /- Euclid takes K where the circles cut one another, without a word on why they
     should. They do, because two of A, B, C taken together in any manner are
     greater than the remaining one (`Prop22.meet`: Heath's argument, closed by
     System E, Intersection 4). They cut one another on each side of DE, the
     straight line through their centres, and K is taken on P's side (System E,
     Intersections 8). -/
  have hmeet : CirclesMeet KLH DKL :=
    Prop22.meet hFGH hF_DKL hD_DKL hG_KLH hH_KLH
      (by rw [hGH, hFD, hFG]; exact hAB_C) (by rw [hGH, hFD, hFG]; exact hAC_B)
      (by rw [hGH, hFD, hFG]; exact hBC_A)
  obtain ⟨K, hK_KLH, hK_DKL, hKP⟩ :=
    circles_meet_same_side hmeet hG_KLH hF_DKL hG_DE hF_DE hP_DE
  -- and let KF, KG be joined;
  /- KF and KG are named by their ends, as sides of the triangle KFG, so nothing is
     drawn for the joins. -/
  -- I say that the triangle KFG has been constructed out of three straight lines equal to A,
  -- B, C.
  -- For, since the point F is the centre of the circle DKL,
  -- FD is equal to FK.
  have hFD_FK : ‖F D‖ = ‖F K‖ := Definition15 hF_DKL hD_DKL hK_DKL
  -- But FD is equal to A;
  have hFD_A : ‖F D‖ = ‖A₁ A₂‖ := hFD
  -- therefore KF is also equal to A.
  have hKF : ‖K F‖ = ‖A₁ A₂‖ := (len_symm K F).trans (hFD_FK.symm.trans hFD_A)
  -- Again, since the point G is the centre of the circle LKH,
  -- GH is equal to GK.
  have hGH_GK : ‖G H‖ = ‖G K‖ := Definition15 hG_KLH hH_KLH hK_KLH
  -- But GH is equal to C;
  have hGH_C : ‖G H‖ = ‖C₁ C₂‖ := hGH
  -- therefore KG is also equal to C.
  have hKG : ‖K G‖ = ‖C₁ C₂‖ := (len_symm K G).trans (hGH_GK.symm.trans hGH_C)
  -- And FG is also equal to B;
  have hFG_B : ‖F G‖ = ‖B₁ B₂‖ := hFG
  -- therefore the three straight lines KF, FG, GK are equal to the three straight lines A, B,
  -- C.
  have hGK : ‖G K‖ = ‖C₁ C₂‖ := (len_symm G K).trans hKG
  -- Therefore out of the three straight lines KF, FG, GK, which are equal to the three given
  -- straight lines A, B, C, the triangle KFG has been constructed.
  /- With FG along the given ray from F through E, and K on P's side of FE. -/
  exact ⟨G, K, hG_ray, SameSideOf.of_line hFE hF_DE hE_DE hKP, hKF, hFG_B, hGK⟩
  -- Q. E. F.

end Elements.BookI
