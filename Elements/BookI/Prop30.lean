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

/-- Euclid's figure puts the ends of each straight line where the proof wants
them, on one side or the other of the straight line falling on it. A straight line
`L` through the point `G` of `T`, other than `T`, has a point on whichever side of
`T` we name: take a point of `L` off `T`, and if it is on the wrong side, produce
it through `G` to the other (System E, Points 2, Pasch 3 and Same side 5). -/
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

/-- Euclid's enunciation also covers `EF` lying outside `AB` and `CD`, where a
straight line from one to the other need not cross it. For that case: two straight
lines through one point, each parallel to a third, are one straight line. A
straight line from the point to the third makes, with each, interior angles equal
to two right angles (I.29); Common Notion 3 takes away the angle they share, and
`onRay_of_angle_eq` makes the two rays one. This is the uniqueness of the
parallel, often called Playfair's axiom, proved here from I.29 rather than
assumed. Later proofs cite `Prop30.meet` instead: the same uniqueness, drawn
from I.30 itself, as Heath reports Proclus drawing it under I.31. -/
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
  have ha := Prop29.interior hpar₁ (SameSideOf.of_line hGH hGT hHT hAF)
  have hd := Prop29.interior hpar₂ (SameSideOf.of_line hGH hGT hHT hDF)
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
  /- Heath's case, where `EF` separates `G` and `K`. The given points need not
     stand where his do, so we choose ends of each straight line on the sides of
     `GK` his figure wants, and return to the given names at the end: parallels
     are whole straight lines. -/
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
    have hAGH : ∠ A G H = ∠ G H F := Prop29.alternate hpar hAF
    have hAGK : ∠ A G K = ∠ G H F :=
      (angle_onRay_right (OnRay.of_between hGHK) hA_G).symm.trans hAGH
    -- Again, since the straight line GK has fallen on the parallel straight lines EF, CD,
    have hpar' := AreParallel.of_parallel hF_H.symm hD_K.symm hH_EF hF_EF hK_CD hD_CD
      hCD_EF.symm
    -- the angle GHF is equal to the angle GKD. [I. 29]
    have hGHF : ∠ G H F = ∠ G K D :=
      (Prop29.exterior hpar' hFD hGHK).trans
        (angle_onRay_left (OnRay.of_between (between_symm hGHK)) hD_K)
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
  /- When `EF` lies outside `AB` and `CD`, a straight line from one to the other
     need not cross it. Then if `AB` and `CD` met, they would be two parallels to
     `EF` through one point, and so one straight line (`Prop30.unique`); but `C`
     is off `AB`. -/
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
