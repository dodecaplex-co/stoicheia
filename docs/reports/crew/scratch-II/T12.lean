import Elements.BookII.Prop04
import Elements.BookII.Prop07
import Elements.BookI.Prop13
import Elements.BookI.Prop17

namespace Elements.BookII
open Tacit

/-- II.12 in full, against its statement: the foot `D` falls on `CA` produced because
the angle at `A` is obtuse (I.17); then II.4 and I.47 twice. -/
theorem T12 {A B C D : Point} (hABC : Triangle A B C) (hBAC : IsObtuse B A C)
    (hD : Collinear C A D) (hBD : ∀ P : Point, Collinear C A P → P ≠ D → ∠ B D P = ∟) :
    sq B C = sq B A + sq A C + (rect C A A D + rect C A A D) := by
  obtain ⟨L, hC, hA⟩ := Postulate1 C A hABC.ne₁₃.symm
  have hD_L : OnLine D L := by
    obtain ⟨M, hC_M, hA_M, hD_M⟩ := hD
    exact (line_unique hABC.ne₁₃.symm hC_M hA_M hC hA) ▸ hD_M
  have hB_L : ¬ OnLine B L := fun h => hABC ⟨L, hA, h, hC⟩
  have col : ∀ {P : Point}, OnLine P L → Collinear C A P := fun h => ⟨L, hC, hA, h⟩
  /- The foot does not lie on the ray from `A` through `C`: the triangle `ABD` would
     have an obtuse angle and a right angle. [I. 17] -/
  have hDA : D ≠ A := by
    intro e
    have h : ∟ < ∠ B A C := hBAC
    rw [← e, hBD C (col hC) (e ▸ hABC.ne₁₃.symm)] at h
    exact lt_irrefl _ h
  have hDB : D ≠ B := fun e => hB_L (e ▸ hD_L)
  have notray : ¬ OnRay D A C := by
    intro hray
    have hABD : Triangle A B D := Triangle.of_line hA hD_L hDA.symm hB_L |>.acb
    have h17 := (BookI.Prop17 hABD).2.1
    rw [angle_onRay_right hray hABC.ne₁₂.symm, angle_symm hDA.symm hDB.symm,
      hBD A (col hA) hDA.symm] at h17
    exact lt_irrefl _ (lt_trans (add_lt_add_right ∟ hBAC) h17)
  have hCAD : Between C A D := by
    by_cases hDC : D = C
    · rw [hDC] at notray
      exact absurd (OnRay.self hABC.ne₁₃) notray
    rcases between_cases hABC.ne₁₃.symm hDA.symm (Ne.symm hDC) hC hA hD_L with h | h | h
    · exact h
    · exact absurd (OnRay.of_beyond h) notray
    · exact absurd (OnRay.of_between (between_symm h)) notray
  -- the square on DC is equal to the squares on CA, AD and twice the rectangle [II. 4]
  have h4 := Prop4 hCAD
  have hDC : D ≠ C := (ne_of_between_ends hCAD).symm
  have hDCB : Triangle D C B := Triangle.of_line hD_L hC hDC hB_L
  have hDAB : Triangle D A B := Triangle.of_line hD_L hA hDA hB_L
  have hCDB : ∠ C D B = ∟ := by
    rw [angle_symm hDC.symm hDB.symm]; exact hBD C (col hC) hDC.symm
  have hADB : ∠ A D B = ∟ := by
    rw [angle_symm hDA.symm hDB.symm]; exact hBD A (col hA) hDA.symm
  -- the square on CB is equal to the squares on CD, DB [I. 47]; and AB to AD, DB [I. 47]
  have h47a := BookI.Prop47.sq hDCB hCDB
  have h47b := BookI.Prop47.sq hDAB hADB
  rw [sq_symm B C, h47a, h4, sq_symm B A, h47b, sq_symm C A]
  ac_rfl

/-- II.13 in full: the foot `D` falls within `BC` because the angles at `B` and `C` are
acute (I.13, I.17); then II.7 and I.47 twice. -/
theorem T13 {A B C D : Point} (hABC : Triangle A B C) (hB : IsAcute A B C) (hC : IsAcute A C B)
    (hD : Collinear B C D) (hAD : ∀ P : Point, Collinear B C P → P ≠ D → ∠ A D P = ∟) :
    sq A C + (rect C B B D + rect C B B D) = sq C B + sq B A := by
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hABC.ne₂₃
  have hD_L : OnLine D L := by
    obtain ⟨M, hB_M, hC_M, hD_M⟩ := hD
    exact (line_unique hABC.ne₂₃ hB_M hC_M hB_L hC_L) ▸ hD_M
  have hA_L : ¬ OnLine A L := hABC.bca.off_line hB_L hC_L
  have col : ∀ {P : Point}, OnLine P L → Collinear B C P := fun h => ⟨L, hB_L, hC_L, h⟩
  have hDB : D ≠ B := by
    intro e
    have h : ∠ A B C < ∟ := hB
    rw [← e, hAD C (col hC_L) (e ▸ hABC.ne₂₃.symm)] at h
    exact lt_irrefl _ h
  have hDC : D ≠ C := by
    intro e
    have h : ∠ A C B < ∟ := hC
    rw [← e, hAD B (col hB_L) (e ▸ hABC.ne₂₃)] at h
    exact lt_irrefl _ h
  have hDA : D ≠ A := fun e => hA_L (e ▸ hD_L)
  /- Not beyond `B`, nor beyond `C`: the angle at `B` (or `C`) of the triangle with the
     foot would be obtuse [I. 13], beside a right angle [I. 17]. -/
  have beyond : ∀ {X Y : Point}, OnLine X L → OnLine Y L → X ≠ Y → IsAcute A X Y →
      ¬ Between D X Y := by
    intro X Y hX hY hXY hacute h
    have hX' : Collinear B C X := col hX
    have hDX : D ≠ X := ne_of_between h
    have h13 := BookI.Prop13 h (fun ⟨M, hD_M, hY_M, hA_M⟩ =>
      hA_L ((line_unique (ne_of_between_ends h) hD_M hY_M hD_L hY) ▸ hA_M))
    have hAXD : Triangle A X D := (Triangle.of_line hX hD_L hDX.symm hA_L).cab
    have hobtuse : ∟ < ∠ D X A := by
      have h₁ : ∠ D X A + ∠ A X Y < ∠ D X A + ∟ := by
        rw [add_comm _ ∟, add_comm (∠ D X A)]
        exact add_lt_add_right _ hacute
      rw [h13] at h₁
      exact Magnitude.lt_of_add_lt_add_right (by rw [add_comm]; exact h₁)
    have h17 := (BookI.Prop17 hAXD).1
    rw [angle_symm (Triangle.ne₁₂ hAXD) hDX, angle_symm hDX.symm hDA.symm,
      hAD X hX' hDX.symm] at h17
    exact lt_irrefl _ (lt_trans (add_lt_add_right ∟ hobtuse) h17)
  have hBDC : Between B D C := by
    rcases between_cases hDB.symm hDC (hABC.ne₂₃) hB_L hD_L hC_L with h | h | h
    · exact h
    · exact absurd h (beyond hB_L hC_L hABC.ne₂₃ hB)
    · exact absurd (between_symm h) (beyond hC_L hB_L hABC.ne₂₃.symm hC)
  -- the squares on CB, BD are equal to twice the rectangle CB, BD and the square on DC [II. 7]
  have h7 := Prop7 (between_symm hBDC)
  have hDBA : Triangle D B A := Triangle.of_line hD_L hB_L hDB hA_L
  have hDAC : Triangle D A C := (Triangle.of_line hD_L hC_L hDC hA_L).acb
  have hBDA : ∠ B D A = ∟ := by
    rw [angle_symm hDB.symm hDA.symm]; exact hAD B (col hB_L) hDB.symm
  have hADC : ∠ A D C = ∟ := hAD C (col hC_L) hDC.symm
  -- the square on AB is equal to the squares on BD, DA [I. 47]
  have h47a := BookI.Prop47.sq hDBA hBDA
  -- and the square on AC is equal to the squares on AD, DC
  have h47b := BookI.Prop47.sq hDAC hADC
  rw [h47b, h47a]
  have : sq C B + (sq B D + sq D A) = (sq C B + sq B D) + sq D A := by ac_rfl
  rw [this, h7, sq_symm D C, sq_symm A D]
  ac_rfl

end Elements.BookII
