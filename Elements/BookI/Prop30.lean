import Elements.Figure.Basics
import Elements.BookI.Prop27
import Elements.BookI.Prop29

/-!
# Book I, Proposition 30

Euclid's text, in Heath's translation: [`heath/I/30.md`](../../heath/I/30.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid's last step, "and they are alternate. Therefore AB is parallel to CD", is
I.27, though he gives no bracket there; so this file imports it.
-/

namespace Elements.BookI

open Tacit

/-- Euclid chooses the ends of a straight line on the desired sides of the
transversal. A straight line through `G` on `T`, different from `T`, has a point
on either side of `T`: take a point off `T` and, if necessary, produce to the
other side (System E, Points 2, Pasch 3 and Same side 5). -/
theorem Prop30.point_on_side {L T : Line} {G P : Point}
    (hGL : OnLine G L) (hGT : OnLine G T) (hLT : L ≠ T) (hP : ¬ OnLine P T) :
    ∃ A : Point, OnLine A L ∧ SameSide A P T := by
  obtain ⟨A, hAL, hAT, -⟩ := exists_point_on_line_off_line hLT []
  by_cases hs : SameSide A P T
  · exact ⟨A, hAL, hs⟩
  · have hAG : A ≠ G := fun e => hAT (e ▸ hGT)
    obtain ⟨B, hAGB⟩ := produce hAG
    have hBL := on_line_of_between hAGB hAL hGL
    have hBT : ¬ OnLine B T := fun h =>
      hAT (on_line_of_between (between_symm hAGB) h hGT)
    exact ⟨B, hBL, same_side_of_opposite_sides ⟨hAT, hBT, pasch3 hAGB hGT⟩
      ⟨hAT, hP, hs⟩⟩

/-- Euclid's general enunciation also covers the arrangement with the common
parallel outside the other two. Two straight lines through one point, each
parallel to a third, coincide: I.29 makes their interior angles equal after the
common angle is subtracted, and `onRay_of_angle_eq` identifies their rays.
This supplies the uniqueness usually called Playfair's axiom, without assuming it. -/
theorem Prop30.unique {L M N : Line} {G H : Point}
    (hLN : Parallel L N) (hMN : Parallel M N)
    (hGL : OnLine G L) (hGM : OnLine G M) (hHN : OnLine H N) : L = M := by
  have hGH : G ≠ H := fun e => hLN.not_onLine hGL (e ▸ hHN)
  obtain ⟨T, hGT, hHT⟩ := Postulate1 G H hGH
  have hNT : N ≠ T := fun e => hLN.not_onLine hGL (e ▸ hGT)
  obtain ⟨F, hFN, hFT, -⟩ := exists_point_on_line_off_line hNT []
  have hLT : L ≠ T := fun e => hLN.not_onLine (e ▸ hHT) hHN
  have hMT : M ≠ T := fun e => hMN.not_onLine (e ▸ hHT) hHN
  obtain ⟨A, hAL, hAF⟩ := Prop30.point_on_side hGL hGT hLT hFT
  obtain ⟨D, hDM, hDF⟩ := Prop30.point_on_side hGM hGT hMT hFT
  have hAG : A ≠ G := fun e => not_on_line_of_same_side hAF (e ▸ hGT)
  have hDG : D ≠ G := fun e => not_on_line_of_same_side hDF (e ▸ hGT)
  have hHF : H ≠ F := fun e => hFT (e ▸ hHT)
  have hpar₁ := AreParallel.of_parallel hAG.symm hHF hGL hAL hHN hFN hLN
  have hpar₂ := AreParallel.of_parallel hDG.symm hHF hGM hDM hHN hFN hMN
  obtain ⟨B, C, E, K, h₁, h₂, h₃, h₄, hp, hs⟩ :=
    hpar₁.figure_interior (SameSideOf.of_line hGH hGT hHT hAF)
  have ha := (Prop29 hp h₁ h₂ h₃ h₄ hs).2.2
  obtain ⟨B', C', E', K', h₁', h₂', h₃', h₄', hp', hs'⟩ :=
    hpar₂.figure_interior (SameSideOf.of_line hGH hGT hHT hDF)
  have hd := (Prop29 hp' h₁' h₂' h₃' h₄' hs').2.2
  have hang : ∠ A G H = ∠ D G H := CommonNotion3 (ha.trans hd.symm) rfl
  have hAD : SameSideOf A D G H := SameSideOf.of_line hGH hGT hHT
    (same_side_trans (same_side_symm hAF) (same_side_symm hDF))
  have hray : OnRay A G D := onRay_of_angle_eq hAD (by
    rw [angle_symm hGH.symm hAG, angle_symm hGH.symm hDG]
    exact hang)
  exact line_unique hAG hAL hGL (hray.onLine hGM hDM) hGM

/-- Straight lines parallel to the same straight line are also parallel to one another. -/
theorem Prop30 {A B C D E F : Point} (h₁ : AreParallel A B E F) (h₂ : AreParallel C D E F)
    (hC : ¬ Collinear A B C) :
    AreParallel A B C D := by
  -- Let each of the straight lines AB, CD be parallel to EF;
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B h₁.1
  obtain ⟨CD, hC_CD, hD_CD⟩ := Postulate1 C D h₂.1
  obtain ⟨EF, hE_EF, hF_EF⟩ := Postulate1 E F h₁.2.1
  have hAB_EF := h₁.parallel hA_AB hB_AB hE_EF hF_EF
  have hCD_EF := h₂.parallel hC_CD hD_CD hE_EF hF_EF
  -- I say that AB is also parallel to CD.
  /- The given endpoints need not occupy Heath's positions. We prove his case
     with ends chosen on the appropriate sides of GK, then return to the given
     names. The common parallel separates G and K in this case. -/
  have separated : ∀ {G K : Point}, OnLine G AB → OnLine K CD →
      OppositeSides G K EF → Parallel AB CD := by
    intro G K hG_AB hK_CD hGK
    -- For let the straight line GK fall upon them.
    obtain ⟨H, hH_EF, hGHK⟩ := hGK.exists_between
    have hG_K := ne_of_between_ends hGHK
    have hG_H := ne_of_between hGHK
    have hH_K := (ne_of_between (between_symm hGHK)).symm
    obtain ⟨GK, hG_GK, hK_GK⟩ := Postulate1 G K hG_K
    have hH_GK := on_line_of_between_ends hGHK hG_GK hK_GK
    have hEF_GK : EF ≠ GK := fun e => hGK.1 (e ▸ hG_GK)
    obtain ⟨F, hF_EF, hF_GK, -⟩ := exists_point_on_line_off_line hEF_GK []
    have hF_H : F ≠ H := fun e => hF_GK (e ▸ hH_GK)
    obtain ⟨E, hFHE⟩ := produce hF_H
    have hE_EF := on_line_of_between hFHE hF_EF hH_EF
    have hE_GK : ¬ OnLine E GK := fun h =>
      hF_GK (on_line_of_between (between_symm hFHE) h hH_GK)
    have hEF : OppositeSides E F GK :=
      ⟨hE_GK, hF_GK, pasch3 (between_symm hFHE) hH_GK⟩
    have hAB_GK : AB ≠ GK := fun e => hAB_EF.not_onLine (e ▸ hH_GK) hH_EF
    have hCD_GK : CD ≠ GK := fun e => hCD_EF.not_onLine (e ▸ hH_GK) hH_EF
    obtain ⟨A, hA_AB, hAE⟩ := Prop30.point_on_side hG_AB hG_GK hAB_GK hE_GK
    obtain ⟨D, hD_CD, hDF⟩ := Prop30.point_on_side hK_CD hK_GK hCD_GK hF_GK
    have hA_G : A ≠ G := fun e => not_on_line_of_same_side hAE (e ▸ hG_GK)
    have hD_K : D ≠ K := fun e => not_on_line_of_same_side hDF (e ▸ hK_GK)
    obtain ⟨B, hAGB⟩ := produce hA_G
    obtain ⟨C, hDKC⟩ := produce hD_K
    have hB_AB := on_line_of_between hAGB hA_AB hG_AB
    have hC_CD := on_line_of_between hDKC hD_CD hK_CD
    have hAF : OppositeSidesOf A F G H :=
      (SameSideOf.of_line hG_H hG_GK hH_GK hAE).trans_opposite
        (OppositeSidesOf.of_line hG_H hG_GK hH_GK hEF)
    have hFD : SameSideOf F D H K :=
      SameSideOf.of_line hH_K hH_GK hK_GK (same_side_symm hDF)
    -- Then, since the straight line GK has fallen on the parallel straight lines AB, EF,
    have hpar := AreParallel.of_parallel hA_G hF_H.symm hA_AB hG_AB hH_EF hF_EF hAB_EF
    -- the angle AGK is equal to the angle GHF. [I. 29]
    obtain ⟨B₁, E₁, G₁, K₁, ha, hb, hc, hd, hp, hs⟩ := hpar.figure_alternate hAF
    have hAGH : ∠ A G H = ∠ G H F := (Prop29 hp ha hb hc hd hs).1
    have hAGK : ∠ A G K = ∠ G H F :=
      (angle_onRay_right (OnRay.of_between hGHK) hA_G).symm.trans hAGH
    -- Again, since the straight line GK has fallen on the parallel straight lines EF, CD,
    have hpar' := AreParallel.of_parallel hF_H.symm hD_K.symm hH_EF hF_EF hK_CD hD_CD
      hCD_EF.symm
    -- the angle GHF is equal to the angle GKD. [I. 29]
    obtain ⟨E₂, C₂, G₂, K₂, ha', hb', hc', hd', hp', hs'⟩ := hpar'.figure_interior hFD
    have hGHF : ∠ G H F = ∠ G K D := by
      have hext := (Prop29 hp' ha' hb' hc' hd' hs').2.1
      have hG₂ : OnRay G₂ H G :=
        OnRay.of_between_between (between_symm hGHK) (between_symm hc')
      rw [angle_onRay_left hG₂ hF_H] at hext
      exact hext.trans (angle_onRay_left (OnRay.of_between (between_symm hGHK)) hD_K)
    -- But the angle AGK was also proved equal to the angle GHF;
    have hsame : ∠ A G K = ∠ G H F := hAGK
    -- therefore the angle AGK is also equal to the angle GKD; [C.N. 1]
    have hequal : ∠ A G K = ∠ G K D := CommonNotion1 hsame hGHF.symm
    -- and they are alternate.
    have hAF_GK : OppositeSidesOf A F G K :=
      OppositeSidesOf.of_line hG_K hG_GK hK_GK (hAF.oppositeSides hG_GK hH_GK)
    have hDF_GK : SameSideOf D F G K := SameSideOf.of_line hG_K hG_GK hK_GK hDF
    have hAD : OppositeSidesOf A D G K := (hDF_GK.trans_opposite hAF_GK.symm).symm
    -- Therefore AB is parallel to CD.
    exact (Prop27 hAGB (between_symm hDKC) hAD hequal).parallel hA_AB hB_AB hC_CD hD_CD
  /- When EF lies outside the other two straight lines, the pictured segment GK
     need not cross it. If AB and CD met, uniqueness of the parallel through
     their meeting point would identify them, contrary to C being off AB. -/
  have hparallel : Parallel AB CD := by
    by_cases hs : SameSide A C EF
    · apply Parallel.of_not_meet hA_AB
      intro G hG_AB hG_CD
      have heq := Prop30.unique hAB_EF hCD_EF hG_AB hG_CD hE_EF
      exact hC ⟨AB, hA_AB, hB_AB, heq ▸ hC_CD⟩
    · exact separated hA_AB hC_CD
        ⟨hAB_EF.not_onLine hA_AB, hCD_EF.not_onLine hC_CD, hs⟩
  exact AreParallel.of_parallel h₁.1 h₂.1 hA_AB hB_AB hC_CD hD_CD hparallel
  -- Q. E. D.

end Elements.BookI
