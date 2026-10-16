import Elements.Figure.Basics
import Elements.BookI.Prop34

/-!
# Book I, Proposition 43

Euclid's text, in Heath's translation: [`heath/I/43.md`](../../heath/I/43.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- Euclid takes for granted that the triangle ABC is made up of AEK, the
complement BK and KGC. The diameters EG and BK of the complement cross, so either
measures its area; cutting the triangle then gives the three pieces. Only the
three betweennesses are needed, with no parallels. -/
theorem Prop43.cut {A B C E G K : Point} (hABC : Triangle A B C) (hK : Between A K C)
    (hE : Between A E B) (hG : Between B G C) :
    △ A B C = △ A E K + quadArea E B G K + △ K G C := by
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hABC.ne₁₂
  obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hABC.ne₁₃
  have hK_AC : OnLine K AC := on_line_of_between_ends hK hA_AC hC_AC
  have hC_AB : ¬ OnLine C AB := hABC.off_line hA_AB hB_AB
  have hB_AC : ¬ OnLine B AC := hABC.acb.off_line hA_AC hC_AC
  have hK_AB : ¬ OnLine K AB := fun h => hC_AB (on_line_of_between hK hA_AB h)
  have hBK : B ≠ K := fun e => hB_AC (e ▸ hK_AC)
  obtain ⟨BK, hB_BK, hK_BK⟩ := Postulate1 B K hBK
  have hA_BK : ¬ OnLine A BK := fun h =>
    hK_AB ((line_unique hABC.ne₁₂ h hB_BK hA_AB hB_AB) ▸ hK_BK)
  have hC_BK : ¬ OnLine C BK := fun h =>
    hA_BK (on_line_of_between (between_symm hK) h hK_BK)
  have hE_BK : ¬ OnLine E BK := fun h =>
    hA_BK (on_line_of_between (between_symm hE) hB_BK h)
  have hG_BK : ¬ OnLine G BK := fun h =>
    hC_BK (on_line_of_between hG hB_BK h)
  /- E lies on A's side of BK, and G on C's; BK separates A from C. -/
  have hEA : SameSide E A BK := pasch2 (between_symm hE) hB_BK hE_BK
  have hGC : SameSide G C BK := pasch2 hG hB_BK hG_BK
  have hEG : OppositeSides E G BK := ⟨hE_BK, hG_BK, fun hs =>
    pasch3 hK hK_BK (same_side_trans (same_side_symm (same_side_trans hEA hs)) hGC)⟩
  obtain ⟨X, hX_BK, hEXG⟩ := hEG.exists_between
  /- X lies on K's side of AB and B's side of AC, hence between B and K. -/
  have hE_AB : OnLine E AB := on_line_of_between_ends hE hA_AB hB_AB
  have hG_AB : ¬ OnLine G AB := fun h =>
    hC_AB (on_line_of_between hG hB_AB h)
  have hX_AB : ¬ OnLine X AB := fun h =>
    hG_AB (on_line_of_between hEXG hE_AB h)
  have hXC : SameSide X C AB :=
    same_side_trans (same_side_symm (pasch2 hEXG hE_AB hX_AB)) (pasch2 hG hB_AB hG_AB)
  have hXK : SameSide X K AB :=
    same_side_trans (same_side_symm hXC) (same_side_symm (pasch2 hK hA_AB hK_AB))
  have hE_AC : ¬ OnLine E AC := fun h => hB_AC (on_line_of_between hE hA_AC h)
  have hEB : SameSide E B AC := pasch2 hE hA_AC hE_AC
  have hGB : SameSide G B AC :=
    pasch2 (between_symm hG) hC_AC (fun h => hB_AC (on_line_of_between (between_symm hG) hC_AC h))
  have hXB : SameSide X B AC :=
    same_side_trans (pasch1 hEXG (same_side_trans (same_side_symm hEB) (same_side_symm hGB))) hEB
  have hBXK : Between B X K :=
    Between.of_inside hB_AB hK_AC ⟨BK, hB_BK, hX_BK, hK_BK⟩ hXK hXB
  /- Measure the complement by BK, then cut ABC along BK, KE and KG. -/
  have hq : quadArea B G K E = quadArea E B G K := quadArea_rotate_of_cross hEXG hBXK
  rw [← hq]
  unfold quadArea
  rw [area_bac A B C, ← area_cut (A := B) hK, area_cba B A K, ← area_cut (A := K) hE,
    area_bac B K C, ← area_cut (A := K) hG, area_cab A E K, area_cab B G K, area_bca B K E]
  ac_rfl

/-- In any parallelogram the complements of the parallelograms about the diameter are equal to one
another. -/
theorem Prop43 {A B C D E F G H K : Point} (hABCD : Parallelogram A B C D) (hK : Between A K C)
    (hE : Between A E B) (hG : Between B G C) (hF : Between C F D) (hH : Between D H A)
    (hEH : Parallelogram A E K H) (hFG : Parallelogram K G C F) :
    quadArea E B G K = quadArea H K F D := by
  -- Let ABCD be a parallelogram, and AC its diameter; and about AC let EH, FG be
  -- parallelograms, and BK, KD the so-called complements;
  -- I say that the complement BK is equal to the complement KD.
  -- For, since ABCD is a parallelogram, and AC its diameter, the triangle ABC is equal to the
  -- triangle ACD. [I. 34]
  have hABC_ACD : △ A B C = △ A C D := by
    have h := (Prop34 (A := B) (B := A) (C := C) (D := D) hABCD.rotate).2.2.2.2
    rw [area_bac B A C, area_cba D C A] at h
    exact h
  -- Again, since EH is a parallelogram, and AK is its diameter, the triangle AEK is equal to
  -- the triangle AHK.
  have hAEK_AHK : △ A E K = △ A H K := by
    have h := (Prop34 (A := E) (B := A) (C := K) (D := H) hEH.rotate).2.2.2.2
    rw [area_bac E A K, area_cab H K A] at h
    exact h
  -- For the same reason the triangle KFC is also equal to KGC.
  have hKFC_KGC : △ K F C = △ K G C := by
    have h := (Prop34 (A := G) (B := K) (C := C) (D := F) hFG.rotate).2.2.2.2
    rw [area_bac G K C, area_cab F C K] at h
    exact h.symm
  -- Now, since the triangle AEK is equal to the triangle AHK, and KFC to KGC, the triangle AEK
  -- together with KGC is equal to the triangle AHK together with KFC. [C.N. 2]
  have hsum : △ A E K + △ K G C = △ A H K + △ K F C :=
    CommonNotion2 hAEK_AHK hKFC_KGC.symm
  -- And the whole triangle ABC is also equal to the whole ADC; therefore the complement BK
  -- which remains is equal to the complement KD which remains. [C.N. 3]
  have hABC_ADC : △ A B C = △ A D C := hABC_ACD.trans (area_acb A C D)
  have hABC := Prop43.cut hABCD.triangle hK hE hG
  have hADC := Prop43.cut hABCD.reverse.triangle hK (between_symm hH) (between_symm hF)
  rw [quadArea_reverse H K F D] at hADC
  refine CommonNotion3 (c := △ A E K + △ K G C) (d := △ A H K + △ K F C) ?_ hsum
  calc
    quadArea E B G K + (△ A E K + △ K G C) = △ A B C := by rw [hABC]; ac_rfl
    _ = △ A D C := hABC_ADC
    _ = quadArea H K F D + (△ A H K + △ K F C) := by rw [hADC]; ac_rfl
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookI
