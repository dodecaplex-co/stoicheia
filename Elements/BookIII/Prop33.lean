import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop04
import Elements.BookI.Prop10
import Elements.BookI.Prop11
import Elements.BookI.Prop23
import Elements.BookI.Prop24
import Elements.BookIII.Prop02
import Elements.BookIII.Prop16
import Elements.BookIII.Prop31
import Elements.BookIII.Prop32

/-!
# Book III, Proposition 33

Euclid's text, in Heath's translation: [`heath/III/33.md`](../../heath/III/33.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- On a given straight line to describe a segment of a circle admitting an angle equal to a given
rectilineal angle. -/
theorem Prop33 {A B C₁ C C₂ : Point} (hAB : A ≠ B) (hC : Triangle C₁ C C₂) :
    ∃ (AEB : Circle) (E : Point), OnCircle A AEB ∧ OnCircle B AEB ∧ OnCircle E AEB ∧
      ¬ Collinear A B E ∧ ∠ A E B = ∠ C₁ C C₂ := by
  -- Let AB be the given straight line, and the angle at C the given rectilineal angle;
  -- thus it is required to describe on the given straight line AB a segment of a circle
  -- admitting an angle equal to the angle at C.
  obtain ⟨M, hA_M, hB_M⟩ := Postulate1 A B hAB
  -- The angle at C is then acute, or right, or obtuse.
  rcases lt_trichotomy (∠ C₁ C C₂) ∟ with h | h | h
  -- First let it be acute,
  -- and, as in the first figure, on the straight line AB, and at the point A, let the angle
  -- BAD be constructed equal to the angle at C;
  · obtain ⟨P, hP, -⟩ := exists_off_line hAB []
    obtain ⟨D, B', hB', hDP, hDAB'⟩ := BookI.Prop23 hAB hC hP
    have hD : Triangle A B D := hDP.triangle
    have hDA : D ≠ A := hD.ne₁₃.symm
    have hD_M : ¬ OnLine D M := hD.off_line hA_M hB_M
    have hBAD : ∠ B A D = ∠ C₁ C C₂ :=
      (angle_onRay_left hB' hDA).symm.trans ((angle_symm hB'.2.1 hDA).trans hDAB')
    -- therefore the angle BAD is also acute.
    have hacute : ∠ B A D < ∟ := hBAD ▸ h
    -- Let AE be drawn at right angles to DA, let AB be bisected at F, let FG be drawn from the
    -- point F at right angles to AB, and let GB be joined.
    obtain ⟨L, hD_L, hA_L⟩ := Postulate1 D A hDA
    obtain ⟨X, hXB, hX⟩ := BookI.Prop11 hDA ⟨L, hD_L, hA_L, hA_L⟩ hD.cab
    have hDAX : ∠ D A X = ∟ := hX D ⟨L, hD_L, hA_L, hD_L⟩ hDA
    have hXA : X ≠ A := fun e => (hXB.triangle) ⟨L, hD_L, hA_L, e ▸ hA_L⟩
    have hBA : B ≠ A := hAB.symm
    /- AB falls within the right angle DAX, for the angle BAD is acute. -/
    have hlt : ∠ D A B < ∠ D A X := by
      rw [angle_symm hDA hBA, hDAX]; exact hacute
    have hBD_AX : SameSideOf B D A X := BookI.Prop24.within hXB.swap hlt
    have hadd : ∠ D A X = ∠ D A B + ∠ B A X := angle_add_of_within hXB.symm.swap hBD_AX
    have hXAB : ∠ X A B < ∟ := by
      rw [angle_symm hXA hBA, ← hDAX, hadd, add_comm]
      exact CommonNotion5 hD.cab.angle_pos
    obtain ⟨Z, hDZX, hZ⟩ := crossbar hXB.symm.swap hBD_AX
    have hZ_M : OnLine Z M := hZ.onLine hA_M hB_M
    have hX_M : ¬ OnLine X M := fun hX_M =>
      hD_M (on_line_of_between (between_symm hDZX) hX_M hZ_M)
    have hXD : OppositeSidesOf X D A B :=
      (OppositeSidesOf.of_line hAB hA_M hB_M ⟨hD_M, hX_M, pasch3 hDZX hZ_M⟩).symm
    obtain ⟨F, hAFB, hAF⟩ := BookI.Prop10 hAB
    have hF_M : OnLine F M := on_line_of_between_ends hAFB hA_M hB_M
    have hFA : F ≠ A := (ne_of_between hAFB).symm
    have hFB : F ≠ B := (ne_of_between (between_symm hAFB)).symm
    obtain ⟨Y, hYX, hY⟩ := BookI.Prop11 hAB ⟨M, hA_M, hB_M, hF_M⟩ hXD.triangle
    have hY_M : ¬ OnLine Y M := not_on_line_of_same_side (hYX.sameSide hA_M hB_M)
    have hFY : F ≠ Y := fun e => hY_M (e ▸ hF_M)
    obtain ⟨LX, hX_LX, hA_LX⟩ := Postulate1 X A hXA
    obtain ⟨LY, hF_LY, hY_LY⟩ := Postulate1 F Y hFY
    have hAFY : ∠ A F Y = ∟ := hY A ⟨M, hA_M, hB_M, hA_M⟩ hFA.symm
    have hXAF : ∠ X A F = ∠ X A B := angle_onRay_right (OnRay.of_between hAFB) hXA
    /- AE and FG meet on this side: the two interior angles are less than
       two right angles. Postulate 5 supplies the point Euclid draws as G. -/
    obtain ⟨G, hG_LX, hG_LY, hGX⟩ := Postulate5 hX_LX hA_LX hA_M hF_M hF_LY hY_LY hFA.symm
      (same_side_symm (hYX.sameSide hA_M hB_M))
      (by rw [hXAF, hAFY]; exact add_lt_add_right ∟ hXAB)
    have hG_M : ¬ OnLine G M := not_on_line_of_same_side hGX
    have hGA : G ≠ A := fun e => hG_M (e ▸ hA_M)
    have hGX' : SameSideOf G X A B := SameSideOf.of_line hAB hA_M hB_M hGX
    have hGray : OnRay G A X := OnRay.of_sameSideOf hGX' ⟨LX, hA_LX, hX_LX, hG_LX⟩ hGA
    have hGY : OnRay G F Y := OnRay.of_sameSideOf
      (SameSideOf.of_line hFA hF_M hA_M (same_side_trans (same_side_symm hGX)
        (same_side_symm (hYX.sameSide hA_M hB_M)))) ⟨LY, hF_LY, hY_LY, hG_LY⟩
      (fun e => hG_M (e ▸ hF_M))
    -- Then, since AF is equal to FB,
    have hFA_FB : ‖F A‖ = ‖F B‖ := (len_symm F A).trans hAF
    -- and FG is common,
    have hFG : ‖F G‖ = ‖F G‖ := rfl
    -- the two sides AF, FG are equal to the two sides BF, FG;
    -- and the angle AFG is equal to the angle BFG;
    have hAFG : ∠ A F G = ∠ B F G := by
      rw [angle_onRay_right hGY hFA.symm, angle_onRay_right hGY hFB.symm, hAFY,
        hY B ⟨M, hA_M, hB_M, hB_M⟩ hFB.symm]
    -- therefore the base AG is equal to the base BG. [I. 4]
    have hAG : ‖A G‖ = ‖B G‖ :=
      (BookI.Prop4 (Triangle.of_line hF_M hA_M hFA hG_M) (Triangle.of_line hF_M hB_M hFB hG_M)
        hFA_FB hFG hAFG).1
    -- Therefore the circle described with centre G and distance GA will pass through B also.
    have hGB_GA : ‖G B‖ = ‖G A‖ := by
      rw [len_symm G B, ← hAG, len_symm A G]
    -- Let it be drawn, and let it be ABE;
    obtain ⟨ABE, hG, hA⟩ := Postulate3 G A hGA
    have hB : OnCircle B ABE := on_circle_of_len_eq hG hA hGB_GA
    obtain ⟨E, hE, -, hEGA⟩ := line_circle_beyond (centre_inside hG) hG_LX hA_LX hGA.symm
    -- let EB be joined.
    -- Now, since AD is drawn from A, the extremity of the diameter AE, at right angles to AE,
    have hGAD : ∠ G A D = ∟ := by
      rw [angle_onRay_left hGray hDA, angle_symm hXA hDA, hDAX]
    have hGside : SameSideOf G B A D := SameSideOf.of_onRay hGray hXB.swap
    -- therefore AD touches the circle ABE. [III. 16, Por.]
    have htouch : Touches A D ABE := Prop16.porism hG hA hGside.triangle.cab hGAD
    -- Since then a straight line AD touches the circle ABE,
    -- and from the point of contact at A a straight line AB is drawn across in the circle ABE,
    obtain ⟨D', hDAD'⟩ := produce hDA
    have hD'D : D' ≠ D := (ne_of_between_ends hDAD').symm
    have hcol : Collinear A D D' := ⟨L, hA_L, hD_L, on_line_of_between hDAD' hD_L hA_L⟩
    have htouch' : Touches D' D ABE :=
      htouch.of_collinear hcol ⟨L, hA_L, hD_L, hD_L⟩ hD'D
    have hEray : OnRay E A G := OnRay.of_beyond (between_symm hEGA)
    have hED : OppositeSidesOf E D A B := (SameSideOf.of_onRay hEray hGX').trans_opposite hXD
    -- the angle DAB is equal to the angle AEB in the alternate segment of the circle. [III. 32]
    have h32 := (Prop32 hA hB hAB htouch' (between_symm hDAD')).1 E hE hED
    -- But the angle DAB is equal to the angle at C;
    have hDAB : ∠ D A B = ∠ C₁ C C₂ := (angle_symm hDA hBA).trans hBAD
    -- therefore the angle at C is also equal to the angle AEB.
    have hCE : ∠ C₁ C C₂ = ∠ A E B := hDAB.symm.trans h32
    -- Therefore on the given straight line AB the segment AEB of a circle has been described
    -- admitting the angle AEB equal to the given angle, the angle at C.
    exact ⟨ABE, E, hA, hB, hE, hED.triangle, hCE.symm⟩
  -- Next let the angle at C be right;
  -- and let it be again required to describe on AB a segment of a circle admitting an angle
  -- equal to the right angle at C.
  -- Let the angle BAD be constructed equal to the right angle at C, as is the case in the
  -- second figure;
  · obtain ⟨P, hP, -⟩ := exists_off_line hAB []
    obtain ⟨D, B', hB', hDP, hDAB'⟩ := BookI.Prop23 hAB hC hP
    have hD : Triangle A B D := hDP.triangle
    have hDA : D ≠ A := hD.ne₁₃.symm
    have hD_M : ¬ OnLine D M := hD.off_line hA_M hB_M
    have hBAD : ∠ B A D = ∠ C₁ C C₂ :=
      (angle_onRay_left hB' hDA).symm.trans ((angle_symm hB'.2.1 hDA).trans hDAB')
    -- let AB be bisected at F, and with centre F and distance either FA or FB let the circle AEB
    -- be described.
    obtain ⟨F, hAFB, hAF⟩ := BookI.Prop10 hAB
    have hF_M : OnLine F M := on_line_of_between_ends hAFB hA_M hB_M
    have hFA : F ≠ A := (ne_of_between hAFB).symm
    obtain ⟨AEB, hF, hA⟩ := Postulate3 F A hFA
    have hB : OnCircle B AEB := on_circle_of_len_eq hF hA (by rw [← hAF, len_symm A F])
    obtain ⟨E, hE, hED⟩ := Prop2.sameSide hA hB hD
    -- Therefore the straight line AD touches the circle ABE, because the angle at A is
    -- right. [III. 16, Por.]
    have htouchR : Touches A D AEB := Prop16.porism hF hA (Triangle.of_line hF_M hA_M hFA hD_M)
      (by rw [angle_onRay_left (OnRay.of_between hAFB) hDA, hBAD, h])
    -- And the angle BAD is equal to the angle in the segment AEB, for the latter too is itself a
    -- right angle, being an angle in a semicircle. [III. 31]
    have hEt : Triangle A B E := hED.triangle
    have h31 := (Prop31 hF hE hA hB hAFB hEt.ne₁₃.symm hEt.ne₂₃.symm).1
    have hBAD_AEB : ∠ B A D = ∠ A E B := hBAD.trans (h.trans h31.symm)
    -- But the angle BAD is also equal to the angle at C.
    -- Therefore the angle AEB is also equal to the angle at C.
    have hEC : ∠ A E B = ∠ C₁ C C₂ := hBAD_AEB.symm.trans hBAD
    -- Therefore again the segment AEB of a circle has been described on AB admitting an angle
    -- equal to the angle at C.
    exact ⟨AEB, E, hA, hB, hE, hEt, hEC⟩
  -- Next, let the angle at C be obtuse;
  -- and on the straight line AB, and at the point A, let the angle BAD be constructed equal to
  -- it, as is the case in the third figure;
  · obtain ⟨P, hP, -⟩ := exists_off_line hAB []
    obtain ⟨D, B', hB', hDP, hDAB'⟩ := BookI.Prop23 hAB hC hP
    have hD : Triangle A B D := hDP.triangle
    have hDA : D ≠ A := hD.ne₁₃.symm
    have hBAD : ∠ B A D = ∠ C₁ C C₂ :=
      (angle_onRay_left hB' hDA).symm.trans ((angle_symm hB'.2.1 hDA).trans hDAB')
    have hobtuse : ∟ < ∠ B A D := hBAD ▸ h
    -- let AE be drawn at right angles to AD, let AB be again bisected at F, let FG be drawn at
    -- right angles to AB, and let GB be joined.
    obtain ⟨L, hD_L, hA_L⟩ := Postulate1 D A hDA
    obtain ⟨X, hXB, hX⟩ := BookI.Prop11 hDA ⟨L, hD_L, hA_L, hA_L⟩ hD.cab
    have hDAX : ∠ D A X = ∟ := hX D ⟨L, hD_L, hA_L, hD_L⟩ hDA
    have hXA : X ≠ A := fun e => (hXB.triangle) ⟨L, hD_L, hA_L, e ▸ hA_L⟩
    have hBA : B ≠ A := hAB.symm
    have hlt : ∠ D A X < ∠ D A B := by
      rw [angle_symm hDA hBA, hDAX]; exact hobtuse
    /- AE falls within the angle BAD, on D's side of AB. -/
    have hXD : SameSideOf X D A B := BookI.Prop24.within hXB.symm.swap hlt
    /- The angle XAB is less than a right angle: when DA is produced to D', AB falls
       within the right angle XAD'. -/
    obtain ⟨D', hDAD'⟩ := produce hDA
    have hD'_L : OnLine D' L := on_line_of_between hDAD' hD_L hA_L
    have hAD' : A ≠ D' := (ne_of_between (between_symm hDAD')).symm
    have hXAD' : ∠ D' A X = ∟ := hX D' ⟨L, hD_L, hA_L, hD'_L⟩ hAD'.symm
    obtain ⟨Z, hDZB, hZ⟩ := crossbar hXB.swap hXD
    obtain ⟨LX, hX_LX, hA_LX⟩ := Postulate1 X A hXA
    have hZ_LX : OnLine Z LX := hZ.onLine hA_LX hX_LX
    have hD_LX : ¬ OnLine D LX := fun hD_LX =>
      (hXB.triangle) ⟨LX, (line_unique hDA hD_L hA_L hD_LX hA_LX) ▸ hD_L, hA_LX, hX_LX⟩ |>.elim
    have hB_LX : ¬ OnLine B LX := fun hB_LX =>
      hD_LX (on_line_of_between (between_symm hDZB) hB_LX hZ_LX)
    have hD'_LX : ¬ OnLine D' LX := fun h' =>
      hD_LX (on_line_of_between (between_symm hDAD') h' hA_LX)
    have hBD' : SameSide B D' LX := same_side_of_opposite_sides
      ⟨hD_LX, hB_LX, pasch3 hDZB hZ_LX⟩ ⟨hD_LX, hD'_LX, pasch3 hDAD' hA_LX⟩
    have hBD'_AX : SameSideOf B D' A X := SameSideOf.of_line hXA.symm hA_LX hX_LX hBD'
    have hBX_AD' : SameSideOf B X A D' :=
      SameSideOf.of_line hAD' hA_L hD'_L (same_side_symm (hXB.sameSide hD_L hA_L))
    have hadd : ∠ X A D' = ∠ X A B + ∠ B A D' := angle_add_of_within hBD'_AX hBX_AD'
    have hXAB : ∠ X A B < ∟ := by
      rw [← hXAD', angle_symm hAD'.symm hXA, hadd]
      exact CommonNotion5 (hBX_AD'.triangle.cab.angle_pos)
    obtain ⟨F, hAFB, hAF⟩ := BookI.Prop10 hAB
    have hF_M : OnLine F M := on_line_of_between_ends hAFB hA_M hB_M
    have hFA : F ≠ A := (ne_of_between hAFB).symm
    have hFB : F ≠ B := (ne_of_between (between_symm hAFB)).symm
    obtain ⟨Y, hYX, hY⟩ := BookI.Prop11 hAB ⟨M, hA_M, hB_M, hF_M⟩ hXD.triangle
    have hY_M : ¬ OnLine Y M := not_on_line_of_same_side (hYX.sameSide hA_M hB_M)
    have hFY : F ≠ Y := fun e => hY_M (e ▸ hF_M)
    obtain ⟨LY, hF_LY, hY_LY⟩ := Postulate1 F Y hFY
    have hAFY : ∠ A F Y = ∟ := hY A ⟨M, hA_M, hB_M, hA_M⟩ hFA.symm
    have hXAF : ∠ X A F = ∠ X A B := angle_onRay_right (OnRay.of_between hAFB) hXA
    /- Again Postulate 5 makes AE and FG meet at G. -/
    obtain ⟨G, hG_LX, hG_LY, hGX⟩ := Postulate5 hX_LX hA_LX hA_M hF_M hF_LY hY_LY hFA.symm
      (same_side_symm (hYX.sameSide hA_M hB_M))
      (by rw [hXAF, hAFY]; exact add_lt_add_right ∟ hXAB)
    have hG_M : ¬ OnLine G M := not_on_line_of_same_side hGX
    have hGA : G ≠ A := fun e => hG_M (e ▸ hA_M)
    have hGX' : SameSideOf G X A B := SameSideOf.of_line hAB hA_M hB_M hGX
    have hGray : OnRay G A X := OnRay.of_sameSideOf hGX' ⟨LX, hA_LX, hX_LX, hG_LX⟩ hGA
    have hGY : OnRay G F Y := OnRay.of_sameSideOf
      (SameSideOf.of_line hFA hF_M hA_M (same_side_trans (same_side_symm hGX)
        (same_side_symm (hYX.sameSide hA_M hB_M)))) ⟨LY, hF_LY, hY_LY, hG_LY⟩
      (fun e => hG_M (e ▸ hF_M))
    -- Then, since AF is again equal to FB,
    have hFA_FB : ‖F A‖ = ‖F B‖ := (len_symm F A).trans hAF
    -- and FG is common,
    have hFG : ‖F G‖ = ‖F G‖ := rfl
    -- the two sides AF, FG are equal to the two sides BF, FG;
    -- and the angle AFG is equal to the angle BFG;
    have hAFG : ∠ A F G = ∠ B F G := by
      rw [angle_onRay_right hGY hFA.symm, angle_onRay_right hGY hFB.symm, hAFY,
        hY B ⟨M, hA_M, hB_M, hB_M⟩ hFB.symm]
    -- therefore the base AG is equal to the base BG. [I. 4]
    have hAG : ‖A G‖ = ‖B G‖ :=
      (BookI.Prop4 (Triangle.of_line hF_M hA_M hFA hG_M) (Triangle.of_line hF_M hB_M hFB hG_M)
        hFA_FB hFG hAFG).1
    -- Therefore the circle described with centre G and distance GA will pass through B also; let
    -- it so pass, as AEB.
    obtain ⟨AEB, hG, hA⟩ := Postulate3 G A hGA
    have hB : OnCircle B AEB := on_circle_of_len_eq hG hA (by
      rw [len_symm G B, ← hAG, len_symm A G])
    /- Euclid's E, the other end of the diameter AE, is not named: the right angle at A
       below is read on the ray from A through the centre G, along AE. -/
    -- Now, since AD is drawn at right angles to the diameter AE from its extremity,
    have hGAD : ∠ G A D = ∟ := by
      rw [angle_onRay_left hGray hDA, angle_symm hXA hDA, hDAX]
    have hGside : SameSideOf G B A D := SameSideOf.of_onRay hGray hXB.swap
    -- AD touches the circle AEB. [III. 16, Por.]
    have htouch : Touches A D AEB := Prop16.porism hG hA hGside.triangle.cab hGAD
    -- And AB has been drawn across from the point of contact at A;
    have hcol : Collinear A D D' := ⟨L, hA_L, hD_L, hD'_L⟩
    have htouch' : Touches D' D AEB :=
      htouch.of_collinear hcol ⟨L, hA_L, hD_L, hD_L⟩ (ne_of_between_ends hDAD').symm
    obtain ⟨H, hH, hHD⟩ := Prop2.oppositeSide hA hB hD
    -- therefore the angle BAD is equal to the angle constructed in the alternate segment AHB of
    -- the circle. [III. 32]
    have h32 := (Prop32 hA hB hAB htouch' (between_symm hDAD')).1 H hH hHD
    have hBAD_AHB : ∠ B A D = ∠ A H B := (angle_symm hBA hDA).trans h32
    -- But the angle BAD is equal to the angle at C.
    -- Therefore the angle in the segment AHB is also equal to the angle at C.
    have hHC : ∠ A H B = ∠ C₁ C C₂ := hBAD_AHB.symm.trans hBAD
    -- Therefore on the given straight line AB the segment AHB of a circle has been described
    -- admitting an angle equal to the angle at C.
    exact ⟨AEB, H, hA, hB, hH, hHD.triangle, hHC⟩
  -- Q. E. F.

end Elements.BookIII
