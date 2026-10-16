import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop04
import Elements.BookI.Prop05
import Elements.BookI.Prop06
import Elements.BookI.Prop11
import Elements.BookI.Prop28
import Elements.BookI.Prop29
import Elements.BookI.Prop30
import Elements.BookI.Prop31
import Elements.BookI.Prop32
import Elements.BookI.Prop34
import Elements.BookI.Prop46
import Elements.BookI.Prop47
import Elements.BookI.Helpers
import Elements.BookI.HelpersParallels

/-!
# Book II, Proposition 9

Euclid's text, in Heath's translation: [`heath/II/09.md`](../../heath/II/09.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If a straight line be cut into equal and unequal segments, the squares on the unequal segments
of the whole are double of the square on the half and of the square on the straight line between
the points of section. -/
theorem Prop9 {A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖) (hADB : Between A D B)
    (hDC : D ≠ C) :
    sq A D + sq D B = sq A C + sq C D + (sq A C + sq C D) := by
  -- For let a straight line AB be cut into equal segments at C, and into unequal segments at
  -- D;
  -- I say that the squares on AD, DB are double of the squares on AC, CD.
  /- Euclid's figure puts `D` between `C` and `B`; the other side is the same with `A`
     and `B` exchanged. -/
  have euclid : ∀ {A B C D : Point}, Between A C B → ‖A C‖ = ‖C B‖ → Between C D B →
      sq A D + sq D B = sq A C + sq C D + (sq A C + sq C D) := by
    intro A B C D hACB hAC hCDB
    have hAB : A ≠ B := ne_of_between_ends hACB
    have hAC' : A ≠ C := ne_of_between hACB
    have hCB : C ≠ B := ne_of_between_ends hCDB
    have hCD : C ≠ D := ne_of_between hCDB
    have hDB : D ≠ B := ne_of_between (between_symm hCDB) |>.symm
    have hADB : Between A D B :=
      between_symm (between_of_between_left (between_symm hACB) (between_symm hCDB))
    obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
    have hC_AB : OnLine C AB := on_line_of_between_ends hACB hA_AB hB_AB
    have hD_AB : OnLine D AB := on_line_of_between_ends hADB hA_AB hB_AB
    have col : ∀ {P : Point}, OnLine P AB → Collinear A B P := fun h => ⟨AB, hA_AB, hB_AB, h⟩
    -- For let CE be drawn from C at right angles to AB, and let it be made equal to either AC or
    -- CB;
    obtain ⟨Q, hQ, -⟩ := exists_off_line hAB []
    obtain ⟨X, hXQ, hright⟩ := BookI.Prop11 hAB (col hC_AB) hQ
    have hX_AB : ¬ OnLine X AB := not_on_line_of_same_side (hXQ.sameSide hA_AB hB_AB)
    have hCX : C ≠ X := fun e => hX_AB (e ▸ hC_AB)
    obtain ⟨E, hE, hCE⟩ := OnRay.exists_len_eq hAC'.symm hCX
    have hE_AB : ¬ OnLine E AB := fun h => by
      obtain ⟨-, hEC, ⟨M, hC_M, hX_M, hE_M⟩, -⟩ := hE
      exact hX_AB ((line_unique hEC.symm hC_M hE_M hC_AB h) ▸ hX_M)
    have hCE' : C ≠ E := fun e => hE_AB (e ▸ hC_AB)
    have rightAt : ∀ {P : Point}, OnLine P AB → P ≠ C → ∠ P C E = ∟ := fun hP hPC => by
      rw [angle_onRay_right hE hPC]; exact hright _ (col hP) hPC
    obtain ⟨CE, hC_CE, hE_CE⟩ := Postulate1 C E hCE'
    -- let EA, EB be joined,
    have hCAE : Triangle C A E := Triangle.of_line hC_AB hA_AB hAC'.symm hE_AB
    have hCBE : Triangle C B E := Triangle.of_line hC_AB hB_AB hCB hE_AB
    obtain ⟨EB, hE_EB, hB_EB⟩ := Postulate1 E B (fun e => hE_AB (e ▸ hB_AB))
    -- let DF be drawn through D parallel to EC,
    have hD_CE : ¬ OnLine D CE := fun h =>
      hE_AB ((line_unique hCD hC_CE h hC_AB hD_AB) ▸ hE_CE)
    obtain ⟨DF, hD_DF, hDF_CE⟩ := BookI.Prop31.line hD_CE
    have hEB_CE : EB ≠ CE := fun e =>
      hE_AB ((line_unique hCB hC_CE (e ▸ hB_EB) hC_AB hB_AB) ▸ hE_CE)
    obtain ⟨F, hF_EB, hF_DF⟩ := BookI.Prop30.meet hDF_CE hE_CE hE_EB hEB_CE
    have hB_DF : ¬ OnLine B DF := fun h =>
      hDF_CE.not_onLine ((line_unique hDB hD_AB hB_AB hD_DF h).symm ▸ hC_AB) hC_CE
    have hEFB : Between E F B :=
      Between.of_sameSide hCDB hD_DF (hDF_CE.symm.sameSide hE_CE hC_CE) (same_side_refl hB_DF)
        hF_DF ⟨EB, hE_EB, hF_EB, hB_EB⟩
    have hD_EB : ¬ OnLine D EB := fun h =>
      hE_AB ((line_unique hDB h hB_EB hD_AB hB_AB) ▸ hE_EB)
    have hDF : D ≠ F := fun e => hD_EB (e ▸ hF_EB)
    -- and FG through F parallel to AB,
    obtain ⟨G, hG_CE, hpG⟩ := BookI.Prop31.parallelogram hDF_CE.symm hC_CE hD_DF hF_DF hDF
    obtain ⟨FG, hF_FG, hG_FG⟩ := Postulate1 F G hpG.1.2.1
    have hFG_AB : Parallel AB FG := hpG.1.parallel hC_AB hD_AB hF_FG hG_FG
    have hE_FG : ¬ OnLine E FG := fun h =>
      hFG_AB.not_onLine hB_AB (on_line_of_between hEFB h hF_FG)
    have hEGC : Between E G C :=
      Between.of_sameSide hEFB hF_FG (same_side_refl hE_FG) (hFG_AB.sameSide hC_AB hB_AB)
        hG_FG ⟨CE, hE_CE, hG_CE, hC_CE⟩
    -- and let AF be joined.
    have hF_AB : ¬ OnLine F AB := fun h =>
      hE_AB (on_line_of_between (between_symm hEFB) hB_AB h)
    have hDA : D ≠ A := (ne_of_between hADB).symm
    have hDAF : Triangle D A F := Triangle.of_line hD_AB hA_AB hDA hF_AB
    -- Then, since AC is equal to CE,
    have hAC_CE : ‖A C‖ = ‖C E‖ := by rw [hCE, len_symm]
    -- the angle EAC is also equal to the angle AEC.
    have h5a : ∠ C A E = ∠ C E A :=
      BookI.Prop5.base hCAE ((len_symm C A).trans hAC_CE)
    -- And, since the angle at C is right,
    have hACE : ∠ A C E = ∟ := rightAt hA_AB hAC'
    -- the remaining angles EAC, AEC are equal to one right angle. [I. 32]
    have h32a := (BookI.Prop32 hCAE.cba hACB).2
    rw [hACE] at h32a
    have hrem_a : ∠ E A C + ∠ C E A = ∟ :=
      CommonNotion3 (c := ∟) (d := ∟) (by rw [← h32a]; ac_rfl) rfl
    -- And they are equal;
    have hEA : E ≠ A := hCAE.ne₂₃.symm
    have hEAC_CEA : ∠ E A C = ∠ C E A :=
      (angle_symm hEA hAC'.symm).trans h5a
    -- therefore each of the angles CEA, CAE is half a right angle.
    have hhalf_CEA : ∠ C E A + ∠ C E A = ∟ := by
      rw [hEAC_CEA] at hrem_a; exact hrem_a
    have hhalf_CAE : ∠ C A E + ∠ C A E = ∟ := by
      rw [h5a]; exact hhalf_CEA
    -- For the same reason
    -- each of the angles CEB, EBC is also half a right angle;
    have h5b : ∠ C B E = ∠ C E B := BookI.Prop5.base hCBE (by rw [hCE, len_symm C A, hAC])
    have hBCE : ∠ B C E = ∟ := rightAt hB_AB hCB.symm
    have h32b := (BookI.Prop32 hCBE.cba (between_symm hACB)).2
    rw [hBCE] at h32b
    have hEB : E ≠ B := fun e => hE_AB (e ▸ hB_AB)
    have hrem_b : ∠ E B C + ∠ C E B = ∟ :=
      CommonNotion3 (c := ∟) (d := ∟) (by rw [← h32b]; ac_rfl) rfl
    have hhalf_CEB : ∠ C E B + ∠ C E B = ∟ := by
      rw [← hrem_b, angle_symm hEB hCB, h5b]
    have hhalf_EBC : ∠ E B C + ∠ E B C = ∟ := by
      rw [angle_symm hEB hCB, h5b]; exact hhalf_CEB
    -- therefore the whole angle AEB is right.
    have hAEB : ∠ A E B = ∟ := by
      have hsplit := angle_add_of_between (Triangle.of_line hA_AB hB_AB hAB hE_AB) hACB
      have heq : ∠ C E A = ∠ C E B :=
        Magnitude.eq_of_add_self_eq (by rw [← h5a]; exact hhalf_CAE.trans hhalf_CEB.symm)
      rw [hsplit, angle_symm hEA.symm hCE', heq]; exact hhalf_CEB
    -- And, since the angle GEF is half a right angle,
    have hGEF : ∠ G E F = ∠ C E B :=
      angle_eq_of_onRay (OnRay.of_between hEGC) (OnRay.of_between hEFB)
    have hhalf_GEF : ∠ G E F + ∠ G E F = ∟ := by
      rw [hGEF]; exact hhalf_CEB
    -- and the angle EGF is right, for it is equal to the interior and opposite angle
    -- ECB, [I. 29]
    have hEGF : ∠ E G F = ∟ := by
      have h29 := BookI.Prop29.exterior hpG.1.symm.swap_left
        hpG.rotate.rotate.rotate.sameSideOf.symm hEGC
      rw [h29, angle_onRay_left (OnRay.of_between (between_symm hEGC)) hCD.symm,
        angle_symm hCE'.symm hCD.symm]
      exact rightAt hD_AB hCD.symm
    -- the remaining angle EFG is half a right angle; [I. 32]
    have hFEG : Triangle F E G := by
      refine Triangle.of_line hF_EB hE_EB (ne_of_between hEFB).symm fun h => ?_
      exact hE_AB ((line_unique hCB hC_CE ((line_unique (ne_of_between hEGC) hE_CE
        (on_line_of_between_ends hEGC hE_CE hC_CE) hE_EB h) ▸ hB_EB) hC_AB hB_AB) ▸ hE_CE)
    have h32c := (BookI.Prop32 hFEG hEGC).2
    rw [hEGF] at h32c
    have hFE : F ≠ E := (ne_of_between hEFB).symm
    have hGE : G ≠ E := (ne_of_between hEGC).symm
    have hGF : G ≠ F := fun e => hDF_CE.not_onLine hF_DF (e ▸ hG_CE)
    have hhalf_EFG : ∠ E F G + ∠ E F G = ∟ := by
      rw [angle_symm hFE hGE, angle_symm hGF hFE.symm] at h32c
      have hsum : ∠ G E F + ∠ E F G = ∟ :=
        CommonNotion3 (c := ∟) (d := ∟) (by rw [← h32c]; ac_rfl) rfl
      have := hsum.trans hhalf_GEF.symm
      have heq : ∠ E F G = ∠ G E F :=
        CommonNotion3 (by rw [add_comm]; exact this) rfl
      rw [heq]; exact hhalf_GEF
    -- therefore the angle GEF is equal to the angle EFG,
    have hEFG : ∠ E F G = ∠ G E F :=
      Magnitude.eq_of_add_self_eq (hhalf_EFG.trans hhalf_GEF.symm)
    -- so that the side EG is also equal to GF. [I. 6]
    have hEG_GF : ‖G E‖ = ‖G F‖ := by
      refine BookI.Prop6 hFEG.cba ?_
      rw [angle_symm hGF hFE.symm, hEFG]
    -- Again, since the angle at B is half a right angle,
    have hFBD : ∠ F B D = ∠ E B C :=
      angle_eq_of_onRay (OnRay.of_between (between_symm hEFB))
        (OnRay.of_between (between_symm hCDB))
    have hhalf_FBD : ∠ F B D + ∠ F B D = ∟ := by
      rw [hFBD]; exact hhalf_EBC
    -- and the angle FDB is right, for it is again equal to the interior and opposite angle
    -- ECB, [I. 29]
    have hFDB : ∠ F D B = ∟ := by
      have h29 := BookI.Prop29.exterior hpG.2.swap_right hpG.sameSideOf.swap (between_symm hCDB)
      rw [angle_symm hDF.symm hDB.symm, h29,
        angle_onRay_right (OnRay.of_between (between_symm hEGC)) hCD.symm]
      exact rightAt hD_AB hCD.symm
    have hBDF : ∠ B D F = ∟ := (angle_symm hDB.symm hDF.symm).trans hFDB
    -- the remaining angle BFD is half a right angle; [I. 32]
    have hFB : F ≠ B := ne_of_between (between_symm hEFB) |>.symm
    have hFBDt : Triangle F B D := Triangle.of_line hF_EB hB_EB hFB hD_EB
    have h32d := (BookI.Prop32 hFBDt (between_symm hCDB)).2
    rw [hBDF] at h32d
    have hhalf_DFB : ∠ D F B + ∠ D F B = ∟ := by
      have hsum : ∠ F B D + ∠ D F B = ∟ :=
        CommonNotion3 (c := ∟) (d := ∟) (by rw [← h32d]; ac_rfl) rfl
      have := hsum.trans hhalf_FBD.symm
      have heq : ∠ D F B = ∠ F B D :=
        CommonNotion3 (by rw [add_comm]; exact this) rfl
      rw [heq]; exact hhalf_FBD
    -- therefore the angle at B is equal to the angle DFB,
    have hDFB : ∠ D F B = ∠ F B D :=
      Magnitude.eq_of_add_self_eq (hhalf_DFB.trans hhalf_FBD.symm)
    -- so that the side FD is also equal to the side DB. [I. 6]
    have hDB_DF : ‖D B‖ = ‖D F‖ := by
      refine BookI.Prop6 hFBDt.cba ?_
      rw [angle_symm hDB hFB, hDFB]
    -- Now, since AC is equal to CE,
    -- the square on AC is also equal to the square on CE;
    have hsqAC : sq A C = sq C E := sq_congr hAC_CE
    -- therefore the squares on AC, CE are double of the square on AC.
    have h1 : sq A C + sq C E = sq A C + sq A C := by rw [hsqAC]
    -- But the square on EA is equal to the squares on AC, CE, for the angle ACE is
    -- right; [I. 47]
    have h47a : sq A E = sq A C + sq C E := BookI.Prop47.sq hCAE hACE
    -- therefore the square on EA is double of the square on AC.
    have h2 : sq E A = sq A C + sq A C := (sq_symm E A).trans (h47a.trans h1)
    -- Again, since EG is equal to GF,
    -- the square on EG is also equal to the square on GF;
    have hsqEG : sq E G = sq G F := sq_congr (by rw [len_symm]; exact hEG_GF)
    -- therefore the squares on EG, GF are double of the square on GF.
    have h3 : sq E G + sq G F = sq G F + sq G F := by rw [hsqEG]
    -- But the square on EF is equal to the squares on EG, GF;
    have h47b : sq E F = sq E G + sq G F := BookI.Prop47.sq hFEG.cba hEGF
    -- therefore the square on EF is double of the square on GF.
    have hEFdouble : sq E F = sq G F + sq G F := h47b.trans h3
    -- But GF is equal to CD; [I. 34]
    have hGF_CD : ‖G F‖ = ‖C D‖ := (BookI.Prop34 hpG.rotate.rotate.rotate).1
    -- therefore the square on EF is double of the square on CD.
    have h4 : sq E F = sq C D + sq C D := by rw [hEFdouble, sq_congr hGF_CD]
    -- But the square on EA is also double of the square on AC;
    -- therefore the squares on AE, EF are double of the squares on AC, CD.
    have h5 : sq A E + sq E F = sq A C + sq C D + (sq A C + sq C D) := by
      rw [sq_symm A E, h2, h4]; ac_rfl
    -- And the square on AF is equal to the squares on AE, EF, for the angle AEF is
    -- right; [I. 47]
    have hAEF : ∠ A E F = ∟ := by
      rw [angle_onRay_right (OnRay.of_between hEFB) hEA.symm]; exact hAEB
    have hA_EB : ¬ OnLine A EB := fun h =>
      hE_AB ((line_unique hAB h hB_EB hA_AB hB_AB) ▸ hE_EB)
    have h47c : sq A F = sq A E + sq E F :=
      BookI.Prop47.sq (Triangle.of_line hE_EB hF_EB hFE.symm hA_EB).acb hAEF
    -- therefore the square on AF is double of the squares on AC, CD.
    have hAFdouble : sq A F = sq A C + sq C D + (sq A C + sq C D) := h47c.trans h5
    -- But the squares on AD, DF are equal to the square on AF, for the angle at D is
    -- right; [I. 47]
    have hADF : ∠ A D F = ∟ := by
      have := adjacent_eq_of_right hB_AB hA_AB (between_symm hADB) hF_AB hBDF
      rw [angle_symm hDA.symm hDF.symm, ← this, hBDF]
    have h47d : sq A F = sq A D + sq D F :=
      BookI.Prop47.sq hDAF hADF
    -- therefore the squares on AD, DF are double of the squares on AC, CD.
    have hADDF : sq A D + sq D F = sq A C + sq C D + (sq A C + sq C D) :=
      h47d.symm.trans hAFdouble
    -- And DF is equal to DB;
    have hDF_DB : ‖D F‖ = ‖D B‖ := hDB_DF.symm
    -- therefore the squares on AD, DB are double of the squares on AC, CD.
    rw [← sq_congr hDF_DB]; exact hADDF
  -- Therefore etc.
  /- Otherwise `D` lies between `A` and `C`: exchange `A` and `B`. -/
  have hCray : OnRay C A B := OnRay.of_between hACB
  have hDray : OnRay D A B := OnRay.of_between hADB
  rcases lt_trichotomy ‖A D‖ ‖A C‖ with h | h | h
  · have hADC : Between A D C := hDray.between_of_len_lt hCray h
    have := euclid (between_symm hACB) (by rw [len_symm B C, len_symm C A]; exact hAC.symm)
      (between_symm hADC)
    rw [sq_symm B D, sq_symm D A, sq_congr (len_symm B C ▸ hAC.symm : ‖B C‖ = ‖A C‖),
      add_comm (sq D B)] at this
    exact this
  · obtain ⟨L, hA, hB⟩ := Postulate1 A B (ne_of_between_ends hACB)
    have hDray' : OnRay D A C := ⟨ne_of_between hACB, (ne_of_between hADB).symm,
      ⟨L, hA, on_line_of_between_ends hACB hA hB, on_line_of_between_ends hADB hA hB⟩,
      hDray.not_between hCray⟩
    exact absurd (hDray'.eq_of_len_eq h) hDC
  · exact euclid hACB hAC (between_inner (hCray.between_of_len_lt hDray h) hADB)
  -- Q. E. D.

end Elements.BookII
