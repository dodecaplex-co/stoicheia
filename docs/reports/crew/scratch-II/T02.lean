import Elements.BookII.Rectangles
import Elements.BookI.HelpersParallels
import Elements.BookI.Prop46

namespace Elements.BookII
open Tacit

/-- II.2 in full along Euclid's route: I.46, I.31, then the rectangles named. -/
theorem T02 {A B C : Point} (hACB : Between A C B) :
    rect A B B C + rect B A A C = sq A B := by
  have hAB : A ≠ B := ne_of_between_ends hACB
  have hAC : A ≠ C := ne_of_between hACB
  have hCB : C ≠ B := (ne_of_between (between_symm hACB)).symm
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  have hC_AB : OnLine C AB := on_line_of_between_ends hACB hA_AB hB_AB
  -- let the square ADEB be described on AB [I. 46]
  obtain ⟨P, hP, -⟩ := exists_off_line hAB []
  obtain ⟨D, E, hsq, hD, hE⟩ := BookI.Prop46 hAB hP
  obtain ⟨hp, hAE⟩ := Square.described hsq hD hE
  -- and let CF be drawn through C parallel to either AD or BE [I. 31]
  obtain ⟨AD, hA_AD, hD_AD⟩ := Postulate1 A D hp.1.1
  obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hp.2.1
  obtain ⟨BE, hB_BE, hE_BE⟩ := Postulate1 B E hp.1.2.1.symm
  have hAD_BE : Parallel AD BE := hp.1.parallel hA_AD hD_AD hE_BE hB_BE
  have hDE_AB : Parallel DE AB := hp.2.parallel hD_DE hE_DE hB_AB hA_AB
  have hE_AB : ¬ OnLine E AB := not_on_line_of_same_side (hE.sameSide hA_AB hB_AB)
  have hC_BE : ¬ OnLine C BE := fun h =>
    hE_AB ((line_unique hCB h hB_BE hC_AB hB_AB) ▸ hE_BE)
  /- I.31 draws the parallel, and I.30 finds `F` where it meets `DE`
  (`Prop31.parallelogram`): `ADFC` is a parallelogram. -/
  obtain ⟨F, hF_DE, hDACF⟩ := BookI.Prop31.parallelogram hDE_AB hD_DE hA_AB hC_AB hAC
  have hADFC : Parallelogram A D F C := hDACF.reverse.rotate.rotate.rotate
  have hFC : F ≠ C := hADFC.1.2.1
  obtain ⟨CF, hC_CF, hF_CF⟩ := Postulate1 C F hFC.symm
  have hCF_AD : Parallel CF AD := (hADFC.1.parallel hA_AD hD_AD hF_CF hC_CF).symm
  have hCF_BE : Parallel CF BE :=
    BookI.Prop30.parallel hCF_AD hAD_BE.symm fun e => hC_BE (e ▸ hC_CF)
  -- Then AE is equal to AF, CE.
  have hDFE : Between D F E :=
    Parallel.between hCF_AD.symm hCF_BE.symm hA_AD hC_CF hB_BE hACB hD_AD hF_CF hE_BE
      ⟨DE, hD_DE, hF_DE, hE_DE⟩
  have hFE : F ≠ E := fun e => hCF_BE.not_onLine hF_CF (e ▸ hE_BE)
  have hCFEB : Parallelogram C F E B :=
    ⟨AreParallel.of_parallel hFC.symm hp.1.2.1 hC_CF hF_CF hE_BE hB_BE hCF_BE,
      AreParallel.of_parallel hFE hCB.symm hF_DE hE_DE hB_AB hC_AB hDE_AB⟩
  have hwhole : quadArea A D E B = quadArea A D F C + quadArea C F E B :=
    quadArea_add_of_parallelograms hADFC hCFEB hACB hDFE
  -- Now AE is the square on AB;
  -- AF is the rectangle contained by BA, AC, for it is contained by DA, AC, and AD is equal
  -- to AB;
  have hAF : quadArea A D F C = rect B A A C := by
    refine (Rectangle.of_right hADFC ?_).eq_rect ?_ rfl
    · rw [angle_onRay_left (OnRay.of_between hACB) hp.1.1.symm]
      exact hsq.2.2.2.1
    · rw [len_symm B A]; exact hsq.len_eq.symm
  -- and CE is the rectangle AB, BC, for BE is equal to AB.
  have hCE : quadArea C F E B = rect A B B C := by
    have hBCFE : Parallelogram B C F E := hCFEB.rotate.rotate.rotate
    rw [hBCFE.quadArea_rotate, ← rect_comm B C A B]
    refine (Rectangle.of_right hBCFE ?_).eq_rect rfl ?_
    · rw [angle_onRay_right (OnRay.of_between (between_symm hACB)) hp.1.2.1]
      exact hsq.2.2.2.2.2.2
    · rw [len_symm B E, len_symm A B]; exact hsq.2.2.1
  -- Therefore the rectangle BA, AC together with the rectangle AB, BC is equal to the
  -- square on AB.
  rw [← hAE, hwhole, hAF, hCE, add_comm]

end Elements.BookII
