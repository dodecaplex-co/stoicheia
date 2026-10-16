import Elements.BookI.Prop04
import Elements.BookI.Prop14
import Elements.BookI.Prop17
import Elements.BookI.Prop31
import Elements.BookI.Prop41
import Elements.BookI.HelpersParallels
import Elements.BookI.Prop47

namespace Elements.BookI
open Tacit

/-- Throwaway: the "half" of I.47, written once over any letters. The parallelogram
`XBDL` (with `A` on `XL`) is equal to the square `ABFG`. -/
theorem X47.half {A B C D F G X L : Point} (hABC : Triangle A B C) (hright : ∠ B A C = ∟)
    (hBD : ‖B D‖ = ‖B C‖) (hCBD : ∠ C B D = ∟) (hD : OppositeSidesOf D A B C)
    (hsq : Square A B F G) (hF : OppositeSidesOf F C A B) (hG : OppositeSidesOf G C A B)
    (hp : Parallelogram X B D L) (hX : Collinear X L A) :
    quadArea X B D L = quadArea A B F G := by
  obtain ⟨hAB_BF, -, -, hGAB, hABF, -, -⟩ := id hsq
  /- the angle ABC is acute [I. 17] -/
  have hacute : ∠ A B C < ∟ := by
    have h17 := (Prop17 hABC).2.2
    rw [angle_symm hABC.ne₁₃.symm hABC.ne₁₂.symm, hright] at h17
    exact Magnitude.lt_of_add_lt_add_left h17
  /- C within the angle DBA; A within the angle FBC -/
  obtain ⟨hCA_BD, hCD_BA⟩ := Prop47.within hABC hD hCBD hacute
  obtain ⟨hAC_BF, hAF_BC⟩ := Prop47.within hABC.cba hF.swap hABF
    (by rw [angle_symm hABC.ne₂₃.symm hABC.ne₁₂]; exact hacute)
  have hDBA : ∠ D B A = ∠ D B C + ∠ C B A := angle_add_of_within hCA_BD hCD_BA
  have hFBC : ∠ F B C = ∠ F B A + ∠ A B C := angle_add_of_within hAC_BF hAF_BC
  have hBD_ne : B ≠ D := hCA_BD.1
  have hBF_ne : B ≠ F := hAC_BF.1
  have hang : ∠ A B D = ∠ F B C := by
    rw [angle_symm hABC.ne₁₂ hBD_ne.symm, hDBA, hFBC,
      angle_symm hBD_ne.symm hABC.ne₂₃.symm, hCBD, angle_symm hBF_ne.symm hABC.ne₁₂, hABF,
      angle_symm hABC.ne₂₃.symm hABC.ne₁₂]
  /- [I. 4] -/
  have h4 : △ B A D = △ B F C :=
    (Prop4 hCD_BA.symm.triangle hAC_BF.symm.triangle
      ((len_symm B A).trans hAB_BF) hBD hang).2.1
  /- C A G on one straight line [I. 14] -/
  have hCAG : Between C A G := Prop14 hG.symm.swap (by
    rw [hright, angle_symm hABC.ne₁₂.symm hG.triangle.ne₁₃.symm, hGAB])
  /- the square ABFG is a parallelogram -/
  have hpsq : Parallelogram A B F G :=
    Prop28.square hsq (OppositeSidesOf.sameSideOf hF.symm hG.symm)
  /- BL is double of ABD [I. 41]; GB is double of FBC [I. 41] -/
  have h41a : quadArea X B D L = △ B A D + △ B A D := Prop41 hp hX
  have h41b : quadArea G F B A = △ F C B + △ F C B :=
    Prop41 hpsq.rotate.rotate.rotate.reverse ⟨Classical.choose (collinear_of_between hCAG),
      (Classical.choose_spec (collinear_of_between hCAG)).2.2,
      (Classical.choose_spec (collinear_of_between hCAG)).2.1,
      (Classical.choose_spec (collinear_of_between hCAG)).1⟩
  rw [h41a, h4, ← area_cab F C B, ← h41b, quadArea_reverse,
    hpsq.rotate.rotate.rotate.quadArea_rotate]

/-- Throwaway: I.47 against its statement. -/
theorem X47 {A B C D E F G H K : Point} (hABC : Triangle A B C) (hright : ∠ B A C = ∟)
    (hBDEC : Square B D E C) (hD : OppositeSidesOf D A B C) (hE : OppositeSidesOf E A B C)
    (hABFG : Square A B F G) (hF : OppositeSidesOf F C A B) (hG : OppositeSidesOf G C A B)
    (hACKH : Square A C K H) (hK : OppositeSidesOf K B A C) (hH : OppositeSidesOf H B A C) :
    quadArea B D E C = quadArea A B F G + quadArea A C K H := by
  obtain ⟨hBD_DE, hDE_EC, hEC_CB, hCBD, -, -, hECB⟩ := id hBDEC
  have hBD_BC : ‖B D‖ = ‖B C‖ := hBD_DE.trans (hDE_EC.trans (hEC_CB.trans (len_symm C B)))
  have hCE_CB : ‖C E‖ = ‖C B‖ := (len_symm C E).trans hEC_CB
  have hBCE : ∠ B C E = ∟ := (angle_symm hABC.ne₂₃ hE.triangle.ne₂₃.symm).trans hECB
  have hright' : ∠ C A B = ∟ := (angle_symm hABC.ne₁₃.symm hABC.ne₁₂.symm).trans hright
  /- the square BDEC is a parallelogram -/
  have hpsq : Parallelogram B D E C :=
    (Prop28.square hBDEC.rotate.rotate.rotate
      (OppositeSidesOf.sameSideOf hD.symm hE.symm).swap).rotate
  /- the acute angles at B and C [I. 17], and where A lies -/
  have hacB : ∠ A B C < ∟ := by
    have h17 := (Prop17 hABC).2.2
    rw [hright'] at h17
    exact Magnitude.lt_of_add_lt_add_left h17
  have hacC : ∠ A C B < ∟ := by
    have h17 := (Prop17 hABC).2.1
    rw [hright] at h17
    exact Magnitude.lt_of_add_lt_add_left h17
  obtain ⟨hCA_BD, -⟩ := Prop47.within hABC hD hCBD hacB
  obtain ⟨hBA_CE, -⟩ := Prop47.within hABC.acb hE.swap hBCE hacC
  /- the straight lines -/
  have hBD : B ≠ D := hCA_BD.1
  have hCE : C ≠ E := hBA_CE.1
  obtain ⟨BD, hB_BD, hD_BD⟩ := Postulate1 B D hBD
  obtain ⟨CE, hC_CE, hE_CE⟩ := Postulate1 C E hCE
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABC.ne₂₃
  obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hpsq.2.1
  have hBD_CE : Parallel BD CE := hpsq.1.parallel hB_BD hD_BD hE_CE hC_CE
  have hDE_BC : Parallel DE BC := hpsq.2.parallel hD_DE hE_DE hC_BC hB_BC
  have hA_BD : ¬ OnLine A BD := not_on_line_of_same_side (same_side_symm (hCA_BD.sameSide hB_BD hD_BD))
  /- through A, AL parallel to BD [I. 31] -/
  obtain ⟨U, V, hUAV, hUV⟩ := Prop31 hBD (fun ⟨K', hB', hD', hA'⟩ =>
    hA_BD ((line_unique hBD hB' hD' hB_BD hD_BD) ▸ hA'))
  obtain ⟨AL, hU_AL, hV_AL⟩ := Postulate1 U V hUV.1
  have hA_AL : OnLine A AL := on_line_of_between_ends hUAV hU_AL hV_AL
  have hAL_BD : Parallel AL BD := hUV.parallel hU_AL hV_AL hB_BD hD_BD
  have hA_CE : ¬ OnLine A CE :=
    not_on_line_of_same_side (same_side_symm (hBA_CE.sameSide hC_CE hE_CE))
  have hAL_CE : Parallel AL CE :=
    Prop30.parallel hAL_BD hBD_CE.symm (fun e => hA_CE (e ▸ hA_AL))
  /- X where AL meets BC; L where it meets DE -/
  have hBC_BD : BC ≠ BD := fun e => hD.triangle.off_line hB_BC hC_BC (e ▸ hD_BD)
  obtain ⟨X, hX_BC, hX_AL⟩ := Prop30.meet hAL_BD hB_BD hB_BC hBC_BD
  have hDE_BD : DE ≠ BD := fun e => hDE_BC.not_onLine (e ▸ hB_BD) hB_BC
  obtain ⟨L, hL_DE, hL_AL⟩ := Prop30.meet hAL_BD hD_BD hD_DE hDE_BD
  /- X falls between B and C, L between D and E (A lies between the parallels BD, CE) -/
  have ss : ∀ {P Q R : Point} {N : Line}, SameSide P Q N → SameSide Q R N → SameSide P R N :=
    fun h1 h2 => same_side_trans (same_side_symm h1) h2
  have hAC_BD : SameSide A C BD := same_side_symm (hCA_BD.sameSide hB_BD hD_BD)
  have hAB_CE : SameSide A B CE := same_side_symm (hBA_CE.sameSide hC_CE hE_CE)
  have hBXC : Between B X C :=
    Between.of_inside hB_BD hC_CE ⟨BC, hB_BC, hX_BC, hC_BC⟩
      (ss (hAL_BD.sameSide hX_AL hA_AL) hAC_BD) (ss (hAL_CE.sameSide hX_AL hA_AL) hAB_CE)
  have hCE_BD : SameSide C E BD := same_side_symm (hpsq.sameSideOf.sameSide hB_BD hD_BD)
  have hBD_CE' : SameSide B D CE := hpsq.rotate.rotate.sameSideOf.sameSide hE_CE hC_CE
  have hDLE : Between D L E :=
    Between.of_inside hD_BD hE_CE ⟨DE, hD_DE, hL_DE, hE_DE⟩
      (ss (ss (hAL_BD.sameSide hL_AL hA_AL) hAC_BD) hCE_BD)
      (ss (ss (hAL_CE.sameSide hL_AL hA_AL) hAB_CE) hBD_CE')
  /- the parallelograms BL and CL -/
  have hXL : X ≠ L := fun e => hDE_BC.not_onLine (e ▸ hL_DE) hX_BC
  have hDL : D ≠ L := fun e => hAL_BD.not_onLine (e ▸ hL_AL) hD_BD
  have hXB : X ≠ B := fun e => hAL_BD.not_onLine (e ▸ hX_AL) hB_BD
  have hLE : L ≠ E := fun e => hAL_CE.not_onLine hL_AL (e ▸ hE_CE)
  have hCX : C ≠ X := fun e => hAL_CE.not_onLine hX_AL (e ▸ hC_CE)
  have P₁ : Parallelogram B D L X :=
    ⟨AreParallel.of_parallel hBD hXL.symm hB_BD hD_BD hL_AL hX_AL hAL_BD.symm,
      AreParallel.of_parallel hDL hXB hD_DE hL_DE hX_BC hB_BC hDE_BC⟩
  have P₂ : Parallelogram X L E C :=
    ⟨AreParallel.of_parallel hXL hCE.symm hX_AL hL_AL hE_CE hC_CE hAL_CE,
      AreParallel.of_parallel hLE hCX hL_DE hE_DE hC_BC hX_BC hDE_BC⟩
  have hXLA : Collinear X L A := ⟨AL, hX_AL, hL_AL, hA_AL⟩
  /- BL is equal to the square GB; similarly CL to HC -/
  have h₁ : quadArea X B D L = quadArea A B F G :=
    X47.half hABC hright hBD_BC hCBD hD hABFG hF hG P₁.rotate.rotate.rotate hXLA
  have h₂ : quadArea X C E L = quadArea A C K H :=
    X47.half hABC.acb hright' hCE_CB hBCE hE.swap hACKH hK hH P₂.reverse hXLA
  /- the whole square BDEC [C.N. 2] -/
  rw [quadArea_add_of_parallelograms P₁ P₂ hBXC hDLE, ← h₁, ← h₂,
    P₁.rotate.rotate.rotate.quadArea_rotate, quadArea_reverse X C E L]

end Elements.BookI
