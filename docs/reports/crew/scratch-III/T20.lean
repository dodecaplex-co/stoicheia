import Elements
open Elements Elements.Tacit

namespace Scratch

/-- Three points, one on the straight line through the other two, named in another
order. -/
theorem col_of {A B C : Point} (h : Collinear A B C) : Collinear B A C := by
  obtain ⟨L, h1, h2, h3⟩ := h; exact ⟨L, h2, h1, h3⟩

/-- The exterior angle at the centre is double: if `AE` is produced to `F`, `E` the
centre and `A`, `X` on the circle, the angle `XEF` is double of the angle `EAX`.
[I. 5, I. 32] -/
theorem dbl {A E F X : Point} {α : Circle} (hE : Centre E α) (hA : OnCircle A α)
    (hX : OnCircle X α) (hAEF : Between A E F) (hX_AE : Triangle A E X) :
    ∠ X E F = ∠ E A X + ∠ E A X := by
  obtain ⟨h32, -⟩ := BookI.Prop32 hX_AE.cab hAEF
  have h5 : ∠ E A X = ∠ E X A := BookI.Prop5.base hX_AE.bac (Definition15 hE hA hX)
  rw [h32, ← h5, angle_symm hX_AE.ne₁₃.symm hX_AE.ne₁₂.symm]

/-- III.20 when the centre is on the other side of `AB` from `C` (Euclid's second
case, `BDC`): the straight line `EC` crosses `AB` within the circle. -/
theorem case_across {A B C E F : Point} {α : Circle} (hE : Centre E α) (hA : OnCircle A α)
    (hB : OnCircle B α) (hC : OnCircle C α) (hAEF : Between A E F)
    (hEC : OppositeSidesOf E C A B) : ∠ B E C = ∠ B A C + ∠ B A C := by
  have hAB : A ≠ B := hEC.1
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  obtain ⟨Y, hY_L, hEYC⟩ := (hEC.2 L hA_L hB_L).exists_between
  have hY_in : InsideCircle Y α := inside_of_between (Or.inl (centre_inside hE)) (Or.inr hC) hEYC
  have hAYB : Between A Y B := between_of_inside_chord hY_L hA_L hB_L hY_in hA hB hAB
  have hABE : Triangle A B E := hEC.triangle
  have hABC : Triangle A B C := hEC.symm.triangle
  have hAY : A ≠ Y := ne_of_between hAYB
  /- `A` is off `EC`, `C` and `B` off `AE`. -/
  have hECA : Triangle E C A := by
    rintro ⟨M, hE_M, hC_M, hA_M⟩
    have hY_M : OnLine Y M := on_line_of_between_ends hEYC hE_M hC_M
    have := line_unique hAY hA_M hY_M hA_L hY_L
    exact hABC.off_line hA_L hB_L (this ▸ hC_M)
  have hAEC : Triangle A E C := hECA.cab
  have hAEB : Triangle A E B := hABE.acb
  /- The angle `EAC` is the angles `EAB`, `BAC`. -/
  have hsplitA : ∠ E A C = ∠ E A B + ∠ B A C := by
    rw [angle_add_of_between hECA hEYC, angle_onRay_right (OnRay.of_between hAYB) hABE.ne₁₃.symm,
      angle_onRay_left (OnRay.of_between hAYB) hABC.ne₁₃.symm]
  /- The angle `AEB` is the angles `AEC`, `CEB`. -/
  have hsplitE : ∠ A E B = ∠ A E C + ∠ C E B := by
    rw [angle_add_of_between hABE hAYB, angle_onRay_right (OnRay.of_between hEYC) hAEC.ne₁₂,
      angle_onRay_left (OnRay.of_between hEYC) hABE.ne₂₃]
  /- `AF` is the straight line `AE`; `C`, `B` are off it. [I. 13] -/
  have hcolF : ∀ {X : Point}, Triangle A E X → ¬ Collinear A F X := by
    intro X hX ⟨M, hA_M, hF_M, hX_M⟩
    exact hX ⟨M, hA_M, on_line_of_between_ends hAEF hA_M hF_M, hX_M⟩
  have h13C : ∠ A E C + ∠ C E F = ∟ + ∟ := BookI.Prop13 hAEF (hcolF hAEC)
  have h13B : ∠ A E B + ∠ B E F = ∟ + ∟ := BookI.Prop13 hAEF (hcolF hAEB)
  have hCEF : ∠ C E F = ∠ C E B + ∠ B E F := by
    apply CommonNotion3 (c := ∠ A E C) (d := ∠ A E C) _ rfl
    rw [add_comm, h13C, ← h13B, hsplitE]
    ac_rfl
  rw [dbl hE hA hC hAEF hAEC, dbl hE hA hB hAEF hAEB, hsplitA] at hCEF
  have : ∠ C E B = ∠ B A C + ∠ B A C := by
    apply CommonNotion3 (c := ∠ E A B + ∠ E A B) (d := ∠ E A B + ∠ E A B) _ rfl
    rw [← hCEF]
    ac_rfl
  rw [angle_symm hABE.ne₂₃ hAEC.ne₂₃.symm, this]

/-- **III.20**, every case: the centre within the angle `BAC` (Euclid's first case),
outside it (his second, `case_across`), or on one of its arms. -/
theorem T20 {A B C E : Point} {ABC : Circle} (hE : Centre E ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hEA : SameSideOf E A B C) :
    ∠ B E C = ∠ B A C + ∠ B A C := by
  have hBCA : Triangle B C A := hEA.symm.triangle
  have hBCE : Triangle B C E := hEA.triangle
  have hAE : A ≠ E := (ne_of_centre_of_on hE hA)
  obtain ⟨F, hAEF⟩ := produce hAE
  have hAB : A ≠ B := hBCA.ne₁₃.symm
  have hAC : A ≠ C := hBCA.ne₂₃.symm
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  obtain ⟨M, hA_M, hC_M⟩ := Postulate1 A C hAC
  have hC_L : ¬ OnLine C L := hBCA.cab.off_line hA_L hB_L
  have hB_M : ¬ OnLine B M := hBCA.cab.acb.off_line hA_M hC_M
  by_cases hE_L : OnLine E L
  · /- `E` on `AB`: the angle `BEC` is exterior to the triangle `AEC`. -/
    have hAEB : Between A E B := between_of_inside_chord hE_L hA_L hB_L (centre_inside hE) hA hB hAB
    have hAEC : Triangle A E C := Triangle.of_line hA_L hE_L hAE hC_L
    rw [angle_onRay_left (OnRay.of_between_between hAEF hAEB) hAEC.ne₂₃.symm,
      angle_symm (ne_of_between (between_symm hAEF)) hAEC.ne₂₃.symm, dbl hE hA hC hAEF hAEC,
      angle_onRay_left (OnRay.of_between hAEB) hAC.symm]
  by_cases hE_M : OnLine E M
  · /- `E` on `AC`, the same with `B` and `C` exchanged. -/
    have hAEC : Between A E C := between_of_inside_chord hE_M hA_M hC_M (centre_inside hE) hA hC hAC
    have hAEB : Triangle A E B := Triangle.of_line hA_M hE_M hAE hB_M
    rw [angle_symm hBCE.ne₁₃ hBCE.ne₂₃,
      angle_onRay_left (OnRay.of_between_between hAEF hAEC) hAEB.ne₂₃.symm,
      angle_symm (ne_of_between (between_symm hAEF)) hAEB.ne₂₃.symm, dbl hE hA hB hAEF hAEB,
      angle_onRay_left (OnRay.of_between hAEC) hAB.symm, angle_symm hAC.symm hAB.symm]
  by_cases hs1 : SameSide E C L
  · by_cases hs2 : SameSide E B M
    · /- `E` within the angle `BAC`: `AE` produced meets `BC` at `X`, beyond `E`. -/
      have hEC : SameSideOf E C A B := SameSideOf.of_line hAB hA_L hB_L hs1
      have hEB : SameSideOf E B A C := SameSideOf.of_line hAC hA_M hC_M hs2
      obtain ⟨X, hBXC, hX⟩ := crossbar hEC hEB
      obtain ⟨N, hB_N, hC_N⟩ := Postulate1 B C hBCA.ne₁₂
      have hX_N : OnLine X N := on_line_of_between_ends hBXC hB_N hC_N
      have hAEX : Between A E X := by
        obtain ⟨-, hXA, ⟨K, hA_K, hE_K, hX_K⟩, hXAE⟩ := hX
        have hEX : E ≠ X := fun e => hBCE.off_line hB_N hC_N (e ▸ hX_N)
        rcases between_cases hAE hEX hXA.symm hA_K hE_K hX_K with h | h | h
        · exact h
        · exact absurd (between_symm h) hXAE
        · exact absurd (hEA.symm.sameSide hB_N hC_N) (pasch3 h hX_N)
      have hXray : OnRay X E F := OnRay.of_between_between hAEF hAEX
      have hAEB : Triangle A E B := (Triangle.of_line hA_L hB_L hAB hE_L).acb
      have hAEC : Triangle A E C := (Triangle.of_line hA_M hC_M hAC hE_M).acb
      rw [angle_add_of_between hBCE hBXC, angle_onRay_right hXray hBCE.ne₁₃,
        angle_onRay_left hXray hBCE.ne₂₃, angle_symm (ne_of_between (between_symm hAEF))
        hBCE.ne₂₃, dbl hE hA hB hAEF hAEB, dbl hE hA hC hAEF hAEC, angle_add_of_within hEC hEB,
        angle_symm hAB.symm hAE.symm]
      ac_rfl
    · /- `E` on the other side of `AC` from `B`. -/
      have hEB : OppositeSidesOf E B A C :=
        OppositeSidesOf.of_line hAC hA_M hC_M ⟨hE_M, hB_M, hs2⟩
      rw [angle_symm hBCE.ne₁₃ hBCE.ne₂₃, case_across hE hA hC hB hAEF hEB,
        angle_symm hAC.symm hAB.symm]
  · /- `E` on the other side of `AB` from `C`: Euclid's second case. -/
    exact case_across hE hA hB hC hAEF (OppositeSidesOf.of_line hAB hA_L hB_L ⟨hE_L, hC_L, hs1⟩)

end Scratch
