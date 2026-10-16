import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop03
import Elements.BookI.Prop04
import Elements.BookI.Prop05
import Elements.BookI.Prop06
import Elements.BookI.Prop11
import Elements.BookI.Prop15
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
# Book II, Proposition 10

Euclid's text, in Heath's translation: [`heath/II/10.md`](../../heath/II/10.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If a straight line be bisected, and a straight line be added to it in a straight line, the
square on the whole with the added straight line and the square on the added straight line both
together are double of the square on the half and of the square described on the straight line
made up of the half and the added straight line as on one straight line. -/
theorem Prop10 {A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖)
    (hABD : Between A B D) :
    sq A D + sq D B = sq A C + sq C D + (sq A C + sq C D) := by
  -- For let a straight line AB be bisected at C, and let a straight line BD be added to it in
  -- a straight line;
  have hCBD : Between C B D := between_inner hACB hABD
  have hAB : A ≠ B := ne_of_between_ends hACB
  have hAC' : A ≠ C := ne_of_between hACB
  have hCB : C ≠ B := ne_of_between hCBD
  have hCD : C ≠ D := ne_of_between_ends hCBD
  have hBD : B ≠ D := ne_of_between (between_symm hCBD) |>.symm
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  have hC_AB : OnLine C AB := on_line_of_between_ends hACB hA_AB hB_AB
  have hD_AB : OnLine D AB := on_line_of_between hABD hA_AB hB_AB
  have col : ∀ {P : Point}, OnLine P AB → Collinear A B P := fun h => ⟨AB, hA_AB, hB_AB, h⟩
  -- I say that the squares on AD, DB are double of the squares on AC, CD.
  -- For let CE be drawn from the point C at right angles to AB [I. 11], and let it be made
  -- equal to either AC or CB [I. 3];
  obtain ⟨Q, hQ, -⟩ := exists_off_line hAB []
  obtain ⟨X, hXQ, hright⟩ := BookI.Prop11 hAB (col hC_AB) hQ
  have hX_AB : ¬ OnLine X AB := not_on_line_of_same_side (hXQ.sameSide hA_AB hB_AB)
  have hCX : C ≠ X := fun e => hX_AB (e ▸ hC_AB)
  obtain ⟨Z, hXCZ⟩ := produce hCX.symm
  obtain ⟨Y, hZCY, hCA_CY⟩ := produce_longer (ne_of_between (between_symm hXCZ)) hAC'.symm
  obtain ⟨E, hCEY, hCE⟩ := BookI.Prop3 hAC'.symm hCA_CY
  have hE : OnRay E C X :=
    OnRay.of_between_between (between_symm hXCZ) (between_cut hZCY hCEY)
  have hE_AB : ¬ OnLine E AB := fun h => by
    obtain ⟨-, hEC, ⟨M, hC_M, hX_M, hE_M⟩, -⟩ := hE
    exact hX_AB ((line_unique hEC.symm hC_M hE_M hC_AB h) ▸ hX_M)
  have hCE' : C ≠ E := fun e => hE_AB (e ▸ hC_AB)
  have rightAt : ∀ {P : Point}, OnLine P AB → P ≠ C → ∠ P C E = ∟ := fun hP hPC => by
    rw [angle_onRay_right hE hPC]; exact hright _ (col hP) hPC
  -- let EA, EB be joined;
  have hEB : E ≠ B := fun e => hE_AB (e ▸ hB_AB)
  have hEA : E ≠ A := fun e => hE_AB (e ▸ hA_AB)
  obtain ⟨EB, hE_EB, hB_EB⟩ := Postulate1 E B hEB
  -- through E let EF be drawn parallel to AD,
  obtain ⟨EF, hE_EF, hEF_AB⟩ := BookI.Prop31.line hE_AB
  -- and through D let FD be drawn parallel to CE. [I. 31]
  obtain ⟨F, hF_EF, hpF⟩ := BookI.Prop31.parallelogram hEF_AB hE_EF hC_AB hD_AB hCD
  have hEF : E ≠ F := hpF.2.2.1.symm
  have hDF : D ≠ F := hpF.1.2.1
  obtain ⟨FD, hF_FD, hD_FD⟩ := Postulate1 F D hDF.symm
  obtain ⟨CE, hC_CE, hE_CE⟩ := Postulate1 C E hCE'
  have hCE_FD : Parallel CE FD := hpF.1.parallel hE_CE hC_CE hD_FD hF_FD
  -- Then, since a straight line EF falls on the parallel straight lines EC, FD,
  -- the angles CEF, EFD are equal to two right angles; [I. 29]
  have h29a : ∠ C E F + ∠ E F D = ∟ + ∟ :=
    BookI.Prop29.interior hpF.1.swap_right hpF.rotate.rotate.rotate.sameSideOf.swap
  -- therefore the angles FEB, EFD are less than two right angles.
  have hB_CE : ¬ OnLine B CE := fun h =>
    hE_AB ((line_unique hCB hC_CE h hC_AB hB_AB) ▸ hE_CE)
  have hBF : SameSideOf B F E C :=
    SameSideOf.of_line hCE'.symm hE_CE hC_CE
      (same_side_trans (same_side_symm (pasch2 hCBD hC_CE hB_CE))
        (hpF.1.symm.sameSideOf.sameSide hE_CE hC_CE))
  have hBC : SameSideOf B C E F :=
    SameSideOf.of_line hEF hE_EF hF_EF (hEF_AB.symm.sameSide hB_AB hC_AB)
  have hless : ∠ F E B + ∠ E F D < ∟ + ∟ := by
    have hsplit : ∠ C E F = ∠ C E B + ∠ B E F := angle_add_of_within hBF hBC
    have hpos : 0 < ∠ C E B := (Triangle.of_line hC_AB hB_AB hCB hE_AB).acb.angle_pos
    have hlt : ∠ F E B < ∠ C E F := by
      rw [hsplit, angle_symm hEF.symm hEB.symm, add_comm]
      exact CommonNotion5 hpos
    rw [← h29a]
    exact add_lt_add_right _ hlt
  -- But straight lines produced from angles less than two right angles meet; [I. Post. 5]
  have hBD_EF : SameSide B D EF := hEF_AB.symm.sameSide hB_AB hD_AB
  have hmeet := Postulate5 hB_EB hE_EB hE_EF hF_EF hF_FD hD_FD
    hEF hBD_EF (by rw [angle_symm hEB.symm hEF.symm]; exact hless)
  -- therefore EB, FD, if produced in the direction B, D, will meet.
  /- The meeting lies on B's side of EF; the order on each straight line follows. -/
  -- Let them be produced and meet at G,
  obtain ⟨G, hG_EB, hG_FD, hGB⟩ := hmeet
  have hB_FD : ¬ OnLine B FD := fun h =>
    hCE_FD.not_onLine hC_CE ((line_unique hBD hB_AB hD_AB h hD_FD) ▸ hC_AB)
  have hEBG : Between E B G :=
    Between.of_inside hE_EF hG_FD ⟨EB, hE_EB, hB_EB, hG_EB⟩ (same_side_symm hGB)
      (same_side_trans (same_side_symm (pasch2 (between_symm hCBD) hD_FD hB_FD))
        (hCE_FD.sameSide hC_CE hE_CE))
  have hG_AB : ¬ OnLine G AB := fun h =>
    hE_AB (on_line_of_between (between_symm hEBG) h hB_AB)
  have hFDG : Between F D G :=
    Between.of_sameSide hEBG hB_AB (hEF_AB.sameSide hF_EF hE_EF) (same_side_refl hG_AB)
      hD_AB ⟨FD, hF_FD, hD_FD, hG_FD⟩
  -- and let AG be joined.
  /- AG is the common side of the triangles AEG and ADG below. -/
  -- Then, since AC is equal to CE,
  have hCAE : Triangle C A E := Triangle.of_line hC_AB hA_AB hAC'.symm hE_AB
  have hCBE : Triangle C B E := Triangle.of_line hC_AB hB_AB hCB hE_AB
  -- the angle EAC is also equal to the angle AEC; [I. 5]
  have h5a : ∠ C A E = ∠ C E A := BookI.Prop5.base hCAE (by rw [hCE, len_symm])
  -- and the angle at C is right;
  have hACE : ∠ A C E = ∟ := rightAt hA_AB hAC'
  -- therefore each of the angles EAC, AEC is half a right angle. [I. 32]
  have h32a := (BookI.Prop32 hCAE.cba hACB).2
  rw [hACE] at h32a
  have hrem_a : ∠ E A C + ∠ C E A = ∟ :=
    CommonNotion3 (c := ∟) (d := ∟) (by rw [← h32a]; ac_rfl) rfl
  have hhalf_CEA : ∠ C E A + ∠ C E A = ∟ := by
    rw [← hrem_a, angle_symm hEA hAC'.symm, h5a]
  have hhalf_EAC : ∠ E A C + ∠ E A C = ∟ := by
    rw [angle_symm hEA hAC'.symm, h5a]; exact hhalf_CEA
  -- For the same reason
  -- each of the angles CEB, EBC is also half a right angle;
  have h5b : ∠ C B E = ∠ C E B := BookI.Prop5.base hCBE (by rw [hCE, len_symm C A, hAC])
  have hBCE : ∠ B C E = ∟ := rightAt hB_AB hCB.symm
  have h32b := (BookI.Prop32 hCBE.cba (between_symm hACB)).2
  rw [hBCE] at h32b
  have hrem_b : ∠ E B C + ∠ C E B = ∟ :=
    CommonNotion3 (c := ∟) (d := ∟) (by rw [← h32b]; ac_rfl) rfl
  have hhalf_CEB : ∠ C E B + ∠ C E B = ∟ := by
    rw [← hrem_b, angle_symm hEB hCB, h5b]
  have hhalf_EBC : ∠ E B C + ∠ E B C = ∟ := by
    rw [angle_symm hEB hCB, h5b]; exact hhalf_CEB
  -- therefore the angle AEB is right.
  have hAEB : ∠ A E B = ∟ := by
    have hsplit := angle_add_of_between (Triangle.of_line hA_AB hB_AB hAB hE_AB) hACB
    have heq : ∠ C E A = ∠ C E B :=
      Magnitude.eq_of_add_self_eq (hhalf_CEA.trans hhalf_CEB.symm)
    rw [hsplit, angle_symm hEA.symm hCE', heq]; exact hhalf_CEB
  -- And, since the angle EBC is half a right angle,
  -- the angle DBG is also half a right angle. [I. 15]
  have hG_CE : ¬ OnLine G CE := fun h => hCE_FD.not_onLine h hG_FD
  have hEGC : ¬ Collinear E G C := fun ⟨M, hE_M, hG_M, hC_M⟩ =>
    hG_CE ((line_unique hCE' hC_M hE_M hC_CE hE_CE) ▸ hG_M)
  have h15 := (BookI.Prop15 hEBG hCBD hEGC).1
  have hhalf_DBG : ∠ D B G + ∠ D B G = ∟ := by rw [← h15]; exact hhalf_EBC
  -- But the angle BDG is also right,
  -- for it is equal to the angle DCE, they being alternate; [I. 29]
  have hDG : D ≠ G := fun e => hG_AB (e ▸ hD_AB)
  have hBDG : ∠ B D G = ∟ := by
    have hpar : AreParallel E C D G :=
      AreParallel.of_parallel hCE'.symm hDG hE_CE hC_CE (on_line_of_between_ends hFDG hF_FD hG_FD)
        hG_FD hCE_FD
    have h29 := BookI.Prop29.alternate hpar
      (OppositeSidesOf.of_line hCD hC_AB hD_AB ⟨hE_AB, hG_AB, pasch3 hEBG hB_AB⟩)
    rw [angle_onRay_left (OnRay.of_between (between_symm hCBD)) hDG.symm, ← h29,
      angle_symm hCE'.symm hCD.symm]
    exact rightAt hD_AB hCD.symm
  -- therefore the remaining angle DGB is half a right angle; [I. 32]
  have hGB : G ≠ B := ne_of_between (between_symm hEBG)
  have hDGB : Triangle D G B := Triangle.of_line hD_FD hG_FD hDG hB_FD
  have h32c := (BookI.Prop32 hDGB (between_symm hEBG)).2
  have hhalf_DGB : ∠ D G B + ∠ D G B = ∟ := by
    rw [angle_symm hGB hBD.symm, hBDG] at h32c
    have hsum : ∠ D G B + ∠ D B G = ∟ := CommonNotion3 h32c rfl
    have heq : ∠ D G B = ∠ D B G := CommonNotion3 (hsum.trans hhalf_DBG.symm) rfl
    rw [heq]; exact hhalf_DBG
  -- therefore the angle DGB is equal to the angle DBG,
  have hDGB_DBG : ∠ D G B = ∠ D B G :=
    Magnitude.eq_of_add_self_eq (hhalf_DGB.trans hhalf_DBG.symm)
  -- so that the side BD is also equal to the side GD. [I. 6]
  have hDB_DG : ‖D B‖ = ‖D G‖ := BookI.Prop6 hDGB.acb hDGB_DBG.symm
  -- Again, since the angle EGF is half a right angle,
  have hFG : F ≠ G := ne_of_between_ends hFDG
  have hEGF : ∠ E G F = ∠ D G B := by
    rw [← angle_eq_of_onRay (OnRay.of_between (between_symm hEBG))
      (OnRay.of_between (between_symm hFDG)), angle_symm hGB.symm hDG]
  have hhalf_EGF : ∠ E G F + ∠ E G F = ∟ := by rw [hEGF]; exact hhalf_DGB
  -- and the angle at F is right, for it is equal to the opposite angle, the angle at
  -- C, [I. 34]
  have h34 := BookI.Prop34 hpF
  have hEFG : ∠ E F G = ∟ := by
    rw [angle_onRay_right (OnRay.of_beyond hFDG) hEF, h34.2.2.2.1,
      angle_symm hCE'.symm hCD.symm]
    exact rightAt hD_AB hCD.symm
  -- the remaining angle FEG is half a right angle; [I. 32]
  obtain ⟨P, hFGP⟩ := produce hFG
  have hE_FD : ¬ OnLine E FD := fun h => hCE_FD.not_onLine hE_CE h
  have hEFGt : Triangle E F G := (Triangle.of_line hF_FD hG_FD hFG hE_FD).cab
  have h32d := (BookI.Prop32 hEFGt hFGP).2
  rw [hEFG] at h32d
  have hGE : G ≠ E := (ne_of_between_ends hEBG).symm
  have hhalf_FEG : ∠ F E G + ∠ F E G = ∟ := by
    rw [angle_symm hFG hGE.symm, angle_symm hGE hEF.symm] at h32d
    have hsum : ∠ E G F + ∠ F E G = ∟ :=
      CommonNotion3 (c := ∟) (d := ∟) (by rw [← h32d]; ac_rfl) rfl
    have heq : ∠ F E G = ∠ E G F :=
      CommonNotion3 (by rw [add_comm]; exact hsum.trans hhalf_EGF.symm) rfl
    rw [heq]; exact hhalf_EGF
  -- therefore the angle EGF is equal to the angle FEG,
  have hFEG : ∠ F E G = ∠ E G F :=
    Magnitude.eq_of_add_self_eq (hhalf_FEG.trans hhalf_EGF.symm)
  -- so that the side GF is also equal to the side EF. [I. 6]
  have hFG_FE : ‖F G‖ = ‖F E‖ := by
    refine BookI.Prop6 hEFGt.bca ?_
    rw [angle_symm hFG hGE.symm, hFEG]
  -- Now, since the square on EC is equal to the square on CA,
  have hsqEC : sq E C = sq C A := sq_congr (by rw [len_symm, hCE])
  -- the squares on EC, CA are double of the square on CA.
  have h1 : sq E C + sq C A = sq C A + sq C A := by rw [hsqEC]
  -- But the square on EA is equal to the squares on EC, CA; [I. 47]
  have hECA : ∠ E C A = ∟ := (angle_symm hCE'.symm hAC').trans hACE
  have h47a : sq E A = sq E C + sq C A := BookI.Prop47.sq hCAE.acb hECA
  -- therefore the square on EA is double of the square on AC. [C.N. 1]
  have h2 : sq E A = sq A C + sq A C :=
    CommonNotion1 (h47a.trans h1) (by rw [sq_symm A C])
  -- Again, since FG is equal to EF,
  -- the square on FG is also equal to the square on FE;
  have hsqFG : sq F G = sq F E := sq_congr hFG_FE
  -- therefore the squares on GF, FE are double of the square on EF.
  have h3 : sq G F + sq F E = sq E F + sq E F := by
    rw [sq_symm G F, hsqFG, sq_symm F E]
  -- But the square on EG is equal to the squares on GF, FE; [I. 47]
  have hGFE : ∠ G F E = ∟ := (angle_symm hFG.symm hEF).trans hEFG
  have h47b : sq G E = sq G F + sq F E := BookI.Prop47.sq hEFGt.bca hGFE
  -- therefore the square on EG is double of the square on EF.
  have h4 : sq E G = sq E F + sq E F := by rw [sq_symm E G, h47b, h3]
  -- And EF is equal to CD; [I. 34]
  have hEF_CD : ‖E F‖ = ‖C D‖ := h34.1
  -- therefore the square on EG is double of the square on CD.
  have h5 : sq E G = sq C D + sq C D := by rw [h4, sq_congr hEF_CD]
  -- But the square on EA was also proved double of the square on AC;
  -- therefore the squares on AE, EG are double of the squares on AC, CD.
  have h6 : sq A E + sq E G = sq A C + sq C D + (sq A C + sq C D) := by
    rw [sq_symm A E, h2, h5]; ac_rfl
  -- And the square on AG is equal to the squares on AE, EG; [I. 47]
  have hAEG : ∠ A E G = ∟ := by
    rw [angle_onRay_right (OnRay.of_beyond hEBG) hEA.symm]; exact hAEB
  have hA_EB : ¬ OnLine A EB := fun h =>
    hE_AB ((line_unique hAB h hB_EB hA_AB hB_AB) ▸ hE_EB)
  have h47c : sq A G = sq A E + sq E G :=
    BookI.Prop47.sq (Triangle.of_line hE_EB hG_EB hGE.symm hA_EB).acb hAEG
  -- therefore the square on AG is double of the squares on AC, CD.
  have h7 : sq A G = sq A C + sq C D + (sq A C + sq C D) := h47c.trans h6
  -- But the squares on AD, DG are equal to the square on AG; [I. 47]
  have hADG : ∠ A D G = ∟ := by
    rw [angle_onRay_left (OnRay.of_beyond (between_symm hABD)) hDG.symm]; exact hBDG
  have h47d : sq A G = sq A D + sq D G :=
    BookI.Prop47.sq (Triangle.of_line hD_AB hA_AB (ne_of_between_ends hABD).symm hG_AB) hADG
  -- therefore the squares on AD, DG are double of the squares on AC, CD.
  have h8 : sq A D + sq D G = sq A C + sq C D + (sq A C + sq C D) := h47d.symm.trans h7
  -- And DG is equal to DB;
  have hDG_DB : ‖D G‖ = ‖D B‖ := hDB_DG.symm
  -- therefore the squares on AD, DB are double of the squares on AC, CD.
  rw [sq_congr hDG_DB] at h8
  exact h8
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookII
