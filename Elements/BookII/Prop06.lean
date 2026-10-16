import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.HelpersParallels
import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.Prop36
import Elements.BookI.Prop43
import Elements.BookI.Prop46

/-!
# Book II, Proposition 6

Euclid's text, in Heath's translation: [`heath/II/06.md`](../../heath/II/06.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If a straight line be bisected and a straight line be added to it in a straight line, the
rectangle contained by the whole with the added straight line and the added straight line
together with the square on the half is equal to the square on the straight line made up of the
half and the added straight line. -/
theorem Prop6 {A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖)
    (hABD : Between A B D) :
    rect A D D B + sq C B = sq C D := by
  -- For let a straight line AB be bisected at the point C, and let a straight line BD be added
  -- to it in a straight line;
  have hCBD : Between C B D := between_inner hACB hABD
  have hACD : Between A C D := between_of_between_right hACB hCBD
  have hCD : C ≠ D := ne_of_between_ends hCBD
  -- I say that the rectangle contained by AD, DB together with the square on CB is equal to
  -- the square on CD.
  -- For let the square CEFD be described on CD, [I. 46]
  /- An unlettered point chooses the side on which the square stands. -/
  obtain ⟨X, hX, -⟩ := exists_off_line hCD []
  obtain ⟨E, F, hsq, hE, hF⟩ := BookI.Prop46 hCD hX
  obtain ⟨hp, hCEFD⟩ := Square.described hsq hE hF
  -- and let DE be joined;
  -- through the point B let BG be drawn parallel to either EC or DF,
  -- through the point H let KM be drawn parallel to either AB or EF,
  obtain ⟨G, H, L, M, hDHE, hEGF, hCLE, hFMD, hBHG, hLHM, hDBHM, hHLEG⟩ := hp.figure hCBD
  -- and further through A let AK be drawn parallel to either CL or DM. [I. 31]
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B (ne_of_between_ends hACB)
  have hC_AB : OnLine C AB := on_line_of_between_ends hACB hA_AB hB_AB
  have hD_AB : OnLine D AB := on_line_of_between hABD hA_AB hB_AB
  obtain ⟨KM, hL_KM, hM_KM⟩ := Postulate1 L M (ne_of_between_ends hLHM)
  have hH_KM : OnLine H KM := on_line_of_between_ends hLHM hL_KM hM_KM
  have hKM_AB : Parallel KM AB := (hDBHM.1.parallel hD_AB hB_AB hH_KM hM_KM).symm
  obtain ⟨K, hK_KM, hLCAK⟩ :=
    BookI.Prop31.parallelogram hKM_AB hL_KM hC_AB hA_AB (ne_of_between hACB).symm
  have hDCEF : Parallelogram D C E F := hp.rotate.rotate.rotate
  have hDBC : Between D B C := between_symm hCBD
  obtain ⟨hBCLH, hMHGF⟩ := hDCEF.complements hDHE hDBC hCLE hEGF hFMD hDBHM hHLEG
  -- Then, since AC is equal to CB,
  -- AL is also equal to CH. [I. 36]
  have h36 : quadArea K A C L = quadArea L C B H :=
    BookI.Prop36 hLCAK.rotate.rotate.rotate.reverse hBCLH.rotate.rotate.reverse hAC
      ⟨KM, hK_KM, hL_KM, hL_KM, hH_KM⟩ ⟨AB, hA_AB, hC_AB, hC_AB, hB_AB⟩
  -- But CH is equal to HF. [I. 43]
  have h43 : quadArea B C L H = quadArea M H G F :=
    BookI.Prop43 hDCEF hDHE hDBC hCLE hEGF hFMD hDBHM hHLEG
  -- Therefore AL is also equal to HF.
  have hAL_HF : quadArea K A C L = quadArea M H G F := by
    rw [h36, quadArea_reverse L H B C, hBCLH.rotate.quadArea_rotate, hBCLH.quadArea_rotate]
    exact h43
  -- Let CM be added to each;
  obtain ⟨CE, hC_CE, hE_CE⟩ := Postulate1 C E hp.1.1
  obtain ⟨DF, hD_DF, hF_DF⟩ := Postulate1 D F hp.1.2.1.symm
  have hL_CE : OnLine L CE := on_line_of_between_ends hCLE hC_CE hE_CE
  have hM_DF : OnLine M DF := on_line_of_between_ends hFMD hF_DF hD_DF
  have hCE_DF : Parallel CE DF := hp.1.parallel hC_CE hE_CE hF_DF hD_DF
  have hLCDM : Parallelogram L C D M :=
    ⟨AreParallel.of_parallel (ne_of_between hCLE).symm (ne_of_between (between_symm hFMD))
        hL_CE hC_CE hD_DF hM_DF hCE_DF,
      AreParallel.of_parallel hCD (ne_of_between_ends hLHM).symm hC_AB hD_AB hM_KM hL_KM
        hKM_AB.symm⟩
  have hCM : quadArea L C D M = quadArea L C B H + quadArea H B D M :=
    quadArea_add_of_parallelograms hBCLH.rotate.rotate.reverse hDBHM.rotate.rotate.reverse hLHM
      hCBD
  -- therefore the whole AM is equal to the gnomon NOP.
  obtain ⟨AK, hA_AK, hK_AK⟩ := Postulate1 A K hLCAK.1.2.1
  have hAK_CE : Parallel AK CE := (hLCAK.1.parallel hL_CE hC_CE hA_AK hK_AK).symm
  have hDF_CE : Parallel DF CE := hCE_DF.symm
  have hKLM : Between K L M := Parallel.between hAK_CE hDF_CE hA_AK hC_CE hD_DF hACD hK_AK
    hL_CE hM_DF ⟨KM, hK_KM, hL_KM, hM_KM⟩
  have hAM : quadArea K A D M = quadArea K A C L + quadArea L C D M :=
    quadArea_add_of_parallelograms hLCAK.rotate.rotate.rotate.reverse hLCDM hKLM hACD
  /- NOP names CH, BM and HF together; its letters are not points. -/
  have hgnomon : quadArea K A D M = quadArea B C L H + quadArea D B H M + quadArea M H G F := by
    rw [hAM, hAL_HF, hCM, quadArea_reverse L H B C, hBCLH.rotate.quadArea_rotate,
      hBCLH.quadArea_rotate, quadArea_reverse H M D B, hDBHM.rotate.quadArea_rotate,
      hDBHM.quadArea_rotate]
    ac_rfl
  -- But AM is the rectangle AD, DB,
  have hDBHMsq : Square D B H M :=
    hsq.rotate.rotate.rotate.about_diameter hDCEF hDHE hDBC (between_symm hFMD) hDBHM
  have hAD : A ≠ D := ne_of_between_ends hACD
  have hAK_DF : Parallel AK DF := BookI.Prop30.parallel hAK_CE hDF_CE fun e => by
    have hAB_DF : AB = DF := line_unique hAD hA_AB hD_AB (e ▸ hA_AK) hD_DF
    exact hKM_AB.not_onLine hM_KM (hAB_DF ▸ hM_DF)
  have hDAKM : Parallelogram D A K M :=
    ⟨AreParallel.of_parallel hAD.symm (ne_of_between_ends hKLM) hD_AB hA_AB hK_KM hM_KM
        hKM_AB.symm,
      AreParallel.of_parallel hLCAK.1.2.1 (ne_of_between (between_symm hFMD)).symm
        hA_AK hK_AK hM_DF hD_DF hAK_DF⟩
  have hright : ∠ M D A = ∟ := by
    rw [angle_onRay_right (OnRay.of_beyond (between_symm hABD))
      (ne_of_between (between_symm hFMD)).symm]
    exact hDBHMsq.2.2.2.1
  -- for DM is equal to DB;
  have hAMrect : quadArea D A K M = rect A D D B :=
    (Rectangle.of_right hDAKM hright).eq_rect (len_symm D A) hDBHMsq.len_eq
  -- therefore the gnomon NOP is also equal to the rectangle AD, DB.
  have hNOP : quadArea B C L H + quadArea D B H M + quadArea M H G F = rect A D D B :=
    hgnomon.symm.trans ((quadArea_reverse K M D A).trans
      (hDAKM.rotate.quadArea_rotate.trans (hDAKM.quadArea_rotate.trans hAMrect)))
  -- Let LG, which is equal to the square on BC, be added to each;
  have hLG : Square E G H L :=
    hsq.rotate.about_diameter hp.rotate (between_symm hDHE) hEGF (between_symm hCLE)
      hHLEG.rotate.rotate
  obtain ⟨-, hBC_HL, -, -, -⟩ := BookI.Prop34 (A := B) (B := H) (C := C) (D := L) hBCLH
  have hLGsq : quadArea H L E G = sq B C := by
    rw [quadArea_rotate₂ E G H L, hLG.eq_sq hHLEG.rotate.rotate]
    exact sq_congr ((hLG.1.trans hLG.2.1).trans hBC_HL.symm)
  -- therefore the rectangle contained by AD, DB together with the square on CB is equal to the
  -- gnomon NOP and LG.
  have hadd := CommonNotion2 hNOP.symm ((sq_symm C B).trans hLGsq.symm)
  -- But the gnomon NOP and LG are the whole square CEFD, which is described on CD;
  have hwhole := hDCEF.about_diameter hDHE hDBC hCLE hEGF hFMD hDBHM hHLEG
  -- therefore the rectangle contained by AD, DB together with the square on CB is equal to the
  -- square on CD.
  rw [hadd, ← hCEFD, hDCEF.quadArea_rotate, hwhole]
  ac_rfl
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookII
