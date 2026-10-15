import Elements.Figure.Basics
import Elements.BookI.Prop16

/-!
# Book I, Proposition 27

Euclid's text, in Heath's translation: [`heath/I/27.md`](../../heath/I/27.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid proves that `AB` and `CD` do not meet in the direction of `B`, `D`, and then
says "similarly" for the direction of `A`, `C`. So the Lean makes the argument once,
for any two straight lines on which a straight line falls, and uses it twice: the
second time with the figure read from the other end, `D`, `C`, `B`, `A` for `A`,
`B`, `C`, `D` and `F`, `E` for `E`, `F`. Euclid's two directions are the two sides of
`EF`.
-/

namespace Elements.BookI

open Tacit

/-- If a straight line falling on two straight lines make the alternate angles equal to one another,
the straight lines will be parallel to one another. -/
theorem Prop27 {A B C D E F : Point} (hAEB : Between A E B) (hCFD : Between C F D)
    (hAD : OppositeSidesOf A D E F) (h : ∠ A E F = ∠ E F D) :
    AreParallel A B C D := by
  -- For let the straight line EF falling on the two straight lines AB, CD make the alternate
  -- angles AEF, EFD equal to one another;
  /- The straight lines AB, CD and EF, drawn whole (Post. 1). EF falls on AB at E and on
     CD at F, and A and D are on opposite sides of it, so neither is on it. -/
  have hAB : A ≠ B := ne_of_between_ends hAEB
  have hCD : C ≠ D := ne_of_between_ends hCFD
  have hEF : E ≠ F := hAD.1
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  obtain ⟨CD, hC_CD, hD_CD⟩ := Postulate1 C D hCD
  obtain ⟨EF, hE_EF, hF_EF⟩ := Postulate1 E F hEF
  have hE_AB : OnLine E AB := on_line_of_between_ends hAEB hA_AB hB_AB
  have hF_CD : OnLine F CD := on_line_of_between_ends hCFD hC_CD hD_CD
  have hAD_EF : OppositeSides A D EF := hAD.oppositeSides hE_EF hF_EF
  -- I say that AB is parallel to CD.
  -- For, if not, AB, CD when produced will meet either in the direction of B, D or towards A,
  -- C.
  /- A point where they meet is off EF. Were it on EF, it would be E, the one point
     where AB meets EF, and then CD, through E and F, would be EF itself, with D on it
     (System E, Generalities 1). So it lies on D's side of EF or on A's, for A and D
     are on opposite sides, and a straight line has just two (System E, Same side 5).
     These are Euclid's two directions: B lies on D's side, and C on A's. -/
  have either : ∀ G : Point, OnLine G AB → OnLine G CD →
      SameSideOf G D E F ∨ SameSideOf G A E F := by
    intro G hG_AB hG_CD
    have hG_EF : ¬ OnLine G EF := by
      intro hG_EF
      by_cases hGE : G = E
      · rw [hGE] at hG_CD
        exact hAD_EF.2.1 (line_unique hEF hG_CD hF_CD hE_EF hF_EF ▸ hD_CD)
      · exact hAD_EF.1 (line_unique hGE hG_AB hE_AB hG_EF hE_EF ▸ hA_AB)
    rcases same_side_or hAD_EF.2.1 hAD_EF.1 hG_EF (fun hs => hAD_EF.2.2 (same_side_symm hs))
      with hs | hs
    · exact Or.inl (SameSideOf.of_line hEF hE_EF hF_EF (same_side_symm hs))
    · exact Or.inr (SameSideOf.of_line hEF hE_EF hF_EF (same_side_symm hs))
  /- Euclid's argument, given once for any letters: if EF falls on AB and CD, making
     the alternate angles AEF, EFD equal, then AB and CD do not meet on D's side of
     EF. -/
  have not_meet : ∀ {A B C D E F G : Point}, Between A E B → Between C F D →
      OppositeSidesOf A D E F → ∠ A E F = ∠ E F D → Collinear A B G → Collinear C D G →
      ¬ SameSideOf G D E F := by
    -- Let them be produced and meet, in the direction of B, D, at G.
    rintro A B C D E F G hAEB hCFD hAD h ⟨AB, hA_AB, hB_AB, hG_AB⟩ ⟨CD, hC_CD, hD_CD, hG_CD⟩
      hG
    have hE_AB : OnLine E AB := on_line_of_between_ends hAEB hA_AB hB_AB
    have hF_CD : OnLine F CD := on_line_of_between_ends hCFD hC_CD hD_CD
    -- Then, in the triangle GEF,
    /- G is on one side of EF, so it is off EF, and GEF is a triangle. -/
    have hEFG : Triangle E F G := hG.triangle
    have hE_F : E ≠ F := hEFG.ne₁₂
    have hF_G : F ≠ G := hEFG.ne₂₃
    have hE_G : E ≠ G := hEFG.ne₁₃
    /- G lies on CD, on D's side of EF, so on the ray from F through D, and the angle
       EFG is the angle EFD (`OnRay.of_sameSideOf`, `angle_onRay_right`). -/
    have hG_FD : OnRay G F D := OnRay.of_sameSideOf hG.swap ⟨CD, hF_CD, hD_CD, hG_CD⟩ hF_G.symm
    have hEFG_EFD : ∠ E F G = ∠ E F D := angle_onRay_right hG_FD hE_F
    /- B is on D's side of EF too, for E lies between A and B, and A is on the other
       side. So G lies on the ray from E through B, and E between A and G: AE is GE
       produced, and the angle AEF is exterior to the triangle GEF (`OnRay.between`). -/
    have hBD : SameSideOf B D E F := hAD.sameSideOf_of_between hAEB
    have hG_EB : OnRay G E B :=
      OnRay.of_sameSideOf (hG.trans hBD.symm) ⟨AB, hE_AB, hB_AB, hG_AB⟩ hE_G.symm
    have hAEG : Between A E G := hG_EB.between hAEB
    -- the exterior angle AEF is equal to the interior and opposite angle EFG:
    have hAEF_EFG : ∠ A E F = ∠ E F G := h.trans hEFG_EFD.symm
    -- which is impossible. [I. 16]
    /- I.16, in the triangle FGE with GE produced to A: the exterior angle FEA is
       greater than the interior and opposite angle GFE. -/
    have hGFE_FEA : ∠ G F E < ∠ F E A := (Prop16 hEFG.bca (between_symm hAEG)).2
    rw [angle_symm hF_G.symm hE_F, angle_symm hE_F.symm (ne_of_between hAEB), hAEF_EFG]
      at hGFE_FEA
    exact lt_irrefl _ hGFE_FEA
  -- Therefore AB, CD when produced will not meet in the direction of B, D.
  have hBD : ∀ G : Point, OnLine G AB → OnLine G CD → ¬ SameSideOf G D E F :=
    fun G hG_AB hG_CD =>
      not_meet hAEB hCFD hAD h ⟨AB, hA_AB, hB_AB, hG_AB⟩ ⟨CD, hC_CD, hD_CD, hG_CD⟩
  -- Similarly it can be proved that neither will they meet towards A, C.
  /- The same argument, with the figure read from the other end: EF, as FE, falls on DC
     at F and on BA at E, and the alternate angles DFE, FEA are the angles EFD, AEF. -/
  have hDFE_FEA : ∠ D F E = ∠ F E A :=
    (angle_symm (ne_of_between (between_symm hCFD)) hEF).trans
      (h.symm.trans (angle_symm (ne_of_between hAEB) hEF.symm))
  have hAC : ∀ G : Point, OnLine G AB → OnLine G CD → ¬ SameSideOf G A F E :=
    fun G hG_AB hG_CD =>
      not_meet (between_symm hCFD) (between_symm hAEB) hAD.symm.swap hDFE_FEA
        ⟨CD, hD_CD, hC_CD, hG_CD⟩ ⟨AB, hB_AB, hA_AB, hG_AB⟩
  -- But straight lines which do not meet in either direction are parallel; [Def. 23]
  have hDef23 : (∀ G : Point, OnLine G AB → ¬ OnLine G CD) → AreParallel A B C D :=
    AreParallel.of_not_meet hAB hCD hA_AB hB_AB hC_CD hD_CD
  -- therefore AB is parallel to CD.
  exact hDef23 fun G hG_AB hG_CD =>
    (either G hG_AB hG_CD).elim (hBD G hG_AB hG_CD) (fun hGA => hAC G hG_AB hG_CD hGA.swap)
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookI
