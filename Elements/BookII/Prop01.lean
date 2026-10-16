import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop02
import Elements.BookI.Prop03
import Elements.BookI.Prop04
import Elements.BookI.Prop11
import Elements.BookI.Prop29
import Elements.BookI.Prop30
import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.HelpersParallels

/-!
# Book II, Proposition 1

Euclid's text, in Heath's translation: [`heath/II/01.md`](../../heath/II/01.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If there be two straight lines, and one of them be cut into any number of segments whatever, the
rectangle contained by the two straight lines is equal to the rectangles contained by the uncut
straight line and each of the segments. -/
theorem Prop1 {A₁ A₂ B C D E : Point} (hA : A₁ ≠ A₂) (hBDE : Between B D E) (hDEC : Between D E C) :
    rect A₁ A₂ B C = rect A₁ A₂ B D + rect A₁ A₂ D E + rect A₁ A₂ E C := by
  -- Let A, BC be two straight lines, and let BC be cut at random at the points D, E;
  have hBDC : Between B D C := between_of_between_right hBDE hDEC
  have hBEC : Between B E C :=
    between_symm (between_of_between_right (between_symm hDEC) (between_symm hBDE))
  have hBC : B ≠ C := ne_of_between_ends hBDC
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hBC
  have hD_BC : OnLine D BC := on_line_of_between_ends hBDC hB_BC hC_BC
  have hE_BC : OnLine E BC := on_line_of_between_ends hBEC hB_BC hC_BC
  -- I say that the rectangle contained by A, BC is equal to the rectangle contained by A, BD,
  -- that contained by A, DE and that contained by A, EC.
  -- For let BF be drawn from B at right angles to BC; [I. 11]
  obtain ⟨Q, hQ, -⟩ := exists_off_line hBC []
  obtain ⟨F, hFQ, hright⟩ := BookI.Prop11 hBC ⟨BC, hB_BC, hC_BC, hB_BC⟩ hQ
  have hCBF : ∠ C B F = ∟ := hright C ⟨BC, hB_BC, hC_BC, hC_BC⟩ hBC.symm
  -- let BG be made equal to A, [I. 3]
  /- I.3 needs a greater straight line. Place A at B by I.2 and produce BF
     far enough along its ray before cutting off BG. -/
  obtain ⟨P, hP⟩ := BookI.Prop2 B A₁ A₂ hA
  have hBP : B ≠ P := ne_of_len_eq hP hA
  have hBF : B ≠ F := hFQ.triangle.ne₁₃
  obtain ⟨Y, hFBY⟩ := produce hBF.symm
  obtain ⟨X, hYBX, hlt⟩ := produce_longer (ne_of_between (between_symm hFBY)) hBP
  have hX : OnRay X B F := OnRay.of_between_between (between_symm hFBY) hYBX
  obtain ⟨G, hBGX, hBG⟩ := BookI.Prop3 hA (hP ▸ hlt)
  have hCBG : ∠ C B G = ∟ := by
    rw [angle_onRay_right (OnRay.of_between hBGX) hBC.symm, angle_onRay_right hX hBC.symm]
    exact hCBF
  have hGQ : SameSideOf G Q B C :=
    SameSideOf.of_onRay (OnRay.of_between hBGX) (SameSideOf.of_onRay hX hFQ)
  have hG_BC : ¬ OnLine G BC := not_on_line_of_same_side (hGQ.sameSide hB_BC hC_BC)
  -- through G let GH be drawn parallel to BC, [I. 31]
  obtain ⟨GH, hG_GH, hGH_BC⟩ := BookI.Prop31.line hG_BC
  -- and through D, E, C let DK, EL, CH be drawn parallel to BG.
  obtain ⟨K, hK_GH, hGBDK⟩ :=
    BookI.Prop31.parallelogram hGH_BC hG_GH hB_BC hD_BC (ne_of_between hBDC)
  obtain ⟨L, hL_GH, hGBEL⟩ :=
    BookI.Prop31.parallelogram hGH_BC hG_GH hB_BC hE_BC (ne_of_between hBEC)
  obtain ⟨H, hH_GH, hGBCH⟩ := BookI.Prop31.parallelogram hGH_BC hG_GH hB_BC hC_BC hBC
  obtain ⟨BG, hB_BG, hG_BG⟩ := Postulate1 B G (ne_of_between hBGX)
  obtain ⟨DK, hD_DK, hK_DK⟩ := Postulate1 D K hGBDK.1.2.1
  obtain ⟨EL, hE_EL, hL_EL⟩ := Postulate1 E L hGBEL.1.2.1
  obtain ⟨CH, hC_CH, hH_CH⟩ := Postulate1 C H hGBCH.1.2.1
  have hDK_BG : Parallel DK BG := (hGBDK.1.parallel hG_BG hB_BG hD_DK hK_DK).symm
  have hEL_BG : Parallel EL BG := (hGBEL.1.parallel hG_BG hB_BG hE_EL hL_EL).symm
  have hCH_BG : Parallel CH BG := (hGBCH.1.parallel hG_BG hB_BG hC_CH hH_CH).symm
  -- Then BH is equal to BK, DL, EH.
  have hDE : D ≠ E := ne_of_between hDEC
  have hDC : D ≠ C := (ne_of_between (between_symm hBDC)).symm
  have hEC : E ≠ C := (ne_of_between (between_symm hBEC)).symm
  /- Each upright meets BC at its own point alone, so these are distinct
     straight lines (`Parallel.off_transversal`). I.30 makes them parallel. -/
  have hE_DK : ¬ OnLine E DK :=
    hGH_BC.symm.off_transversal hD_BC hK_GH hD_DK hK_DK hE_BC hDE.symm
  have hC_DK : ¬ OnLine C DK :=
    hGH_BC.symm.off_transversal hD_BC hK_GH hD_DK hK_DK hC_BC hDC.symm
  have hC_EL : ¬ OnLine C EL :=
    hGH_BC.symm.off_transversal hE_BC hL_GH hE_EL hL_EL hC_BC hEC.symm
  have hDK_EL : Parallel DK EL :=
    BookI.Prop30.parallel hDK_BG hEL_BG (fun e => hE_DK (e.symm ▸ hE_EL))
  have hDK_CH : Parallel DK CH :=
    BookI.Prop30.parallel hDK_BG hCH_BG (fun e => hC_DK (e.symm ▸ hC_CH))
  have hEL_CH : Parallel EL CH :=
    BookI.Prop30.parallel hEL_BG hCH_BG (fun e => hC_EL (e.symm ▸ hC_CH))
  /- The parallels keep the order of `B`, `D`, `E`, `C` on `GH`. -/
  have hGKL : Between G K L := Parallel.between hDK_BG.symm hDK_EL.symm hB_BG hD_DK hE_EL
    hBDE hG_BG hK_DK hL_EL ⟨GH, hG_GH, hK_GH, hL_GH⟩
  have hKLH : Between K L H := Parallel.between hDK_EL hEL_CH.symm hD_DK hE_EL hC_CH
    hDEC hK_DK hL_EL hH_CH ⟨GH, hK_GH, hL_GH, hH_GH⟩
  have hGKH : Between G K H := between_of_between_right hGKL hKLH
  have hBGKD : Parallelogram B G K D := hGBDK.reverse.rotate.rotate.rotate
  have hBGLE : Parallelogram B G L E := hGBEL.reverse.rotate.rotate.rotate
  have hBGHC : Parallelogram B G H C := hGBCH.reverse.rotate.rotate.rotate
  have hDKHC : Parallelogram D K H C :=
    ⟨AreParallel.of_parallel hGBDK.1.2.1 hGBCH.1.2.1.symm hD_DK hK_DK hH_CH hC_CH hDK_CH,
      AreParallel.of_parallel (ne_of_between_ends hKLH) hDC.symm hK_GH hH_GH hC_BC hD_BC hGH_BC⟩
  have hDKLE : Parallelogram D K L E :=
    ⟨AreParallel.of_parallel hGBDK.1.2.1 hGBEL.1.2.1.symm hD_DK hK_DK hL_EL hE_EL hDK_EL,
      AreParallel.of_parallel (ne_of_between hKLH) hDE.symm hK_GH hL_GH hE_BC hD_BC hGH_BC⟩
  have hELHC : Parallelogram E L H C :=
    ⟨AreParallel.of_parallel hGBEL.1.2.1 hGBCH.1.2.1.symm hE_EL hL_EL hH_CH hC_CH hEL_CH,
      AreParallel.of_parallel (ne_of_between (between_symm hKLH)).symm hEC.symm hL_GH hH_GH
        hC_BC hE_BC hGH_BC⟩
  have h₁ : quadArea B G H C = quadArea B G K D + quadArea D K H C :=
    quadArea_add_of_parallelograms hBGKD hDKHC hBDC hGKH
  have h₂ : quadArea D K H C = quadArea D K L E + quadArea E L H C :=
    quadArea_add_of_parallelograms hDKLE hELHC hDEC hKLH
  -- Now BH is the rectangle A, BC, for it is contained by GB, BC, and BG is equal to A;
  have hBH : quadArea B G H C = rect A₁ A₂ B C :=
    (Rectangle.of_right hBGHC hCBG).eq_rect hBG rfl
  -- BK is the rectangle A, BD, for it is contained by GB, BD, and BG is equal to A;
  have hBK_rect : Rectangle B G K D := by
    refine Rectangle.of_right hBGKD ?_
    rw [angle_onRay_left (OnRay.of_between hBDC) (ne_of_between hBGX).symm]
    exact hCBG
  have hBK : quadArea B G K D = rect A₁ A₂ B D := hBK_rect.eq_rect hBG rfl
  -- and DL is the rectangle A, DE, for DK, that is BG [I. 34], is equal to A.
  have hDK : ‖D K‖ = ‖A₁ A₂‖ := by
    rw [len_symm D K, ← (BookI.Prop34 hGBDK).2.1, len_symm G B]; exact hBG
  have hK_BC : ¬ OnLine K BC := hGH_BC.not_onLine hK_GH
  have hEDK : ∠ E D K = ∟ := by
    have h := hBK_rect.2.2.2.2
    rw [angle_symm hGBDK.1.2.1.symm (ne_of_between hBDE)] at h
    rw [angle_symm hDE.symm hGBDK.1.2.1.symm, ← adjacent_eq_of_right hB_BC hE_BC hBDE hK_BC h]
    exact h
  have hDL : quadArea D K L E = rect A₁ A₂ D E :=
    (Rectangle.of_right hDKLE hEDK).eq_rect hDK rfl
  -- Similarly also EH is the rectangle A, EC.
  have hEL : ‖E L‖ = ‖A₁ A₂‖ := by
    rw [len_symm E L, ← (BookI.Prop34 hGBEL).2.1, len_symm G B]; exact hBG
  have hL_BC : ¬ OnLine L BC := hGH_BC.not_onLine hL_GH
  have hBGLE_rect : Rectangle B G L E := by
    refine Rectangle.of_right hBGLE ?_
    rw [angle_onRay_left (OnRay.of_between hBEC) (ne_of_between hBGX).symm]
    exact hCBG
  have hCEL : ∠ C E L = ∟ := by
    have h := hBGLE_rect.2.2.2.2
    rw [angle_symm hGBEL.1.2.1.symm (ne_of_between hBEC)] at h
    rw [angle_symm hEC.symm hGBEL.1.2.1.symm, ← adjacent_eq_of_right hB_BC hC_BC hBEC hL_BC h]
    exact h
  have hEH : quadArea E L H C = rect A₁ A₂ E C :=
    (Rectangle.of_right hELHC hCEL).eq_rect hEL rfl
  -- Therefore the rectangle A, BC is equal to the rectangle A, BD, the rectangle A, DE and the
  -- rectangle A, EC.
  have hequal : rect A₁ A₂ B C = rect A₁ A₂ B D + rect A₁ A₂ D E + rect A₁ A₂ E C := by
    rw [← hBH, h₁, h₂, hBK, hDL, hEH]
    ac_rfl
  -- Therefore etc.
  exact hequal
  -- Q. E. D.

end Elements.BookII
