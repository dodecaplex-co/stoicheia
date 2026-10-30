import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Prop02
import Elements.BookIII.Prop20

/-!
# Book III, Proposition 21

Euclid's text, in Heath's translation: [`heath/III/21.md`](../../heath/III/21.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Heath: "Under the restriction that the 'angle at the centre' used in III. 20 must be less
than two right angles, Euclid's proof of this proposition only applies to the case of a
segment greater than a semicircle, and the case of a segment equal to or less than a
semicircle has to be considered separately. The simplest proof, of many, seems to be that
of Simson" (vol. 2, p. 49). So Euclid's sentences carry his proof where the centre F lies
on A's side of BD, the segment BAED greater than a semicircle: the angle BFD is then less
than two right angles, as his angles at the centre are, and III.20 doubles BAD and BED
there (`Prop20.special`). The semicircle and the less segment follow by Robert Simson's
completion, which Heath gives (vol. 2, p. 50): the diameter through A, ending at C, makes
two segments greater than a semicircle, on BC and on CD, and Euclid's case
(`Prop21.greater`) makes the angles in each equal.
-/

namespace Elements.BookIII

open Tacit

/-- **Euclid's case, the segment greater than a semicircle.** When the centre F lies on A's
side of BD, the angle BFD is double of the angle BAD and of the angle BED, by III.20 with
the angle BFD less than two right angles (`Prop20.special`), and halves of one angle are
equal. It is Euclid's proof below, for any base, so that Simson's completion can take it
twice, "by the first case" (Heath, vol. 2, p. 50). -/
theorem Prop21.greater {A B D E F : Point} {ABCD : Circle} (hF : Centre F ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hD : OnCircle D ABCD)
    (hE : OnCircle E ABCD) (hAE : SameSideOf A E B D) (hFA : SameSideOf F A B D) :
    ∠ B A D = ∠ B E D :=
  Magnitude.eq_of_add_self_eq
    ((Prop20.special hF hA hB hD hFA).symm.trans (Prop20.special hF hE hB hD (hFA.trans hAE)))

/-- In a circle the angles in the same segment are equal to one another. -/
theorem Prop21 {A B D E : Point} {ABCD : Circle}
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hD : OnCircle D ABCD)
    (hE : OnCircle E ABCD) (hAE : SameSideOf A E B D) :
    ∠ B A D = ∠ B E D := by
  -- Let ABCD be a circle, and let the angles BAD, BED be angles in the same segment BAED;
  -- I say that the angles BAD, BED are equal to one another.
  -- For let the centre of the circle ABCD be taken, and let it be F; let BF, FD be joined.
  obtain ⟨F, hF⟩ := exists_centre ABCD
  /- Euclid's figure has F on A's side of BD, and so on E's: the segment BAED is greater
     than a semicircle. Where F is on BD or across it from A, the semicircle and the less
     segment, Simson's completion follows "Therefore etc.". -/
  by_cases hFA : SameSideOf F A B D
  · have hFE : SameSideOf F E B D := hFA.trans hAE
    -- Now, since the angle BFD is at the centre,
    -- and the angle BAD at the circumference,
    -- and they have the same circumference BCD as base,
    -- therefore the angle BFD is double of the angle BAD. [III. 20]
    have h₁ : ∠ B F D = ∠ B A D + ∠ B A D := Prop20.special hF hA hB hD hFA
    -- For the same reason
    -- the angle BFD is also double of the angle BED;
    have h₂ : ∠ B F D = ∠ B E D + ∠ B E D := Prop20.special hF hE hB hD hFE
    -- therefore the angle BAD is equal to the angle BED.
    exact Magnitude.eq_of_add_self_eq (h₁.symm.trans h₂)
  -- Therefore etc.
  /- The segment BAED a semicircle or less than one: Simson's completion (Heath, vol. 2,
     p. 50). AF is drawn through the centre to C on the circle. F is on BD, or across it
     from A, and so C is across BD from A, and from E. -/
  · have hAF : A ≠ F := ne_of_centre_of_on hF hA
    obtain ⟨AF, hA_AF, hF_AF⟩ := Postulate1 A F hAF
    obtain ⟨C, hC, -, hCFA⟩ := line_circle_beyond (centre_inside hF) hF_AF hA_AF hAF
    obtain ⟨L, hB_L, hD_L⟩ := Postulate1 B D hAE.1
    have hA_L : ¬ OnLine A L := hAE.triangle.off_line hB_L hD_L
    have hAC_L : OppositeSides A C L := by
      by_cases hF_L : OnLine F L
      · exact ⟨hA_L, fun hC_L => hA_L (on_line_of_between hCFA hC_L hF_L),
          pasch3 (between_symm hCFA) hF_L⟩
      · have hAF_L : ¬ SameSide A F L := fun hs =>
          hFA (SameSideOf.of_line hAE.1 hB_L hD_L (same_side_symm hs))
        obtain ⟨X, hX_L, hAXF⟩ := OppositeSides.exists_between ⟨hA_L, hF_L, hAF_L⟩
        have hFC : SameSide F C L := pasch2 (between_inner hAXF (between_symm hCFA)) hX_L hF_L
        exact ⟨hA_L, not_on_line_of_same_side (same_side_symm hFC),
          fun hs => hAF_L (same_side_trans (same_side_symm hs) (same_side_symm hFC))⟩
    have hAC : OppositeSidesOf A C B D := OppositeSidesOf.of_line hAE.1 hB_L hD_L hAC_L
    have hEC : OppositeSidesOf E C B D := hAE.symm.trans_opposite hAC
    have hBCD : Triangle B C D := hAC.symm.triangle.acb
    /- AC and EC cross BD at X and Y, within the circle [III. 2], and so between B and D
       (Circle 1). -/
    obtain ⟨X, hX_L, hAXC⟩ := hAC_L.exists_between
    obtain ⟨Y, hY_L, hEYC⟩ := (hEC.oppositeSides hB_L hD_L).exists_between
    have hBXD : Between B X D :=
      between_of_inside_chord hX_L hB_L hD_L (Prop2 hA hC X hAXC) hB hD hAE.1
    have hBYD : Between B Y D :=
      between_of_inside_chord hY_L hB_L hD_L (Prop2 hE hC Y hEYC) hB hD hAE.1
    /- "Therefore the segment BADC is greater than a semicircle": AC crossing BD puts A on
       D's side of BC (`SameSideOf.of_cross`), EC puts E there, and F, between C and A, is
       on A's side. So the angles BAC, BEC are equal, by Euclid's case. -/
    have hDA_BC : SameSideOf D A B C := SameSideOf.of_cross hBXD (between_symm hAXC) hBCD
    have hDE_BC : SameSideOf D E B C := SameSideOf.of_cross hBYD (between_symm hEYC) hBCD
    have hFA_BC : SameSideOf F A B C :=
      (SameSideOf.of_onRay (OnRay.of_between hCFA) hDA_BC.symm.swap).swap.trans hDA_BC
    have h₁ : ∠ B A C = ∠ B E C :=
      Prop21.greater hF hA hB hC hE (hDA_BC.symm.trans hDE_BC) hFA_BC
    /- In the same way A, E and F lie on B's side of CD, and the angles CAD, CED are
       equal. -/
    have hBA_CD : SameSideOf B A D C :=
      SameSideOf.of_cross (between_symm hBXD) (between_symm hAXC) hBCD.cba
    have hBE_CD : SameSideOf B E D C :=
      SameSideOf.of_cross (between_symm hBYD) (between_symm hEYC) hBCD.cba
    have hFA_CD : SameSideOf F A C D :=
      (SameSideOf.of_onRay (OnRay.of_between hCFA) hBA_CD.symm.swap).trans hBA_CD.swap
    have h₂ : ∠ C A D = ∠ C E D :=
      Prop21.greater hF hA hC hD hE (hBA_CD.symm.trans hBE_CD).swap hFA_CD
    /- "Therefore the whole angle BAD is equal to the whole angle BED": AC and EC fall
       within the angles BAD and BED, crossing BD between B and D. -/
    have hBAD : ∠ B A D = ∠ B A C + ∠ C A D := by
      rw [angle_add_of_between hAE.triangle hBXD,
        angle_onRay_right (OnRay.of_between hAXC) hAE.triangle.ne₁₃,
        angle_onRay_left (OnRay.of_between hAXC) hAE.triangle.ne₂₃]
    have hBED : ∠ B E D = ∠ B E C + ∠ C E D := by
      rw [angle_add_of_between hAE.symm.triangle hBYD,
        angle_onRay_right (OnRay.of_between hEYC) hAE.symm.triangle.ne₁₃,
        angle_onRay_left (OnRay.of_between hEYC) hAE.symm.triangle.ne₂₃]
    rw [hBAD, hBED, h₁, h₂]
  -- Q. E. D.

end Elements.BookIII
