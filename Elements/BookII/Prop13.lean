import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop13
import Elements.BookI.Prop17
import Elements.BookI.Prop47
import Elements.BookII.Prop07

/-!
# Book II, Proposition 13

Euclid's text, in Heath's translation: [`heath/II/13.md`](../../heath/II/13.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- The foot does not fall beyond X when the angle AXY is acute, because the angle
DXA beside it would be obtuse [I. 13] and the triangle AXD would have an obtuse and
a right angle [I. 17]. Euclid reads this off his figure when he takes the straight
line CB to be "cut at random at D". -/
theorem Prop13.not_beyond {A D X Y : Point} {L : Line} (hX : OnLine X L) (hY : OnLine Y L)
    (hD_L : OnLine D L) (hA_L : ¬ OnLine A L) (hacute : IsAcute A X Y)
    (hright : ∠ A D X = ∟) : ¬ Between D X Y := by
  intro h
  have hDX : D ≠ X := ne_of_between h
  have hDA : D ≠ A := fun e => hA_L (e ▸ hD_L)
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
  rw [angle_symm hAXD.ne₁₂ hDX, angle_symm hDX.symm hDA.symm, hright] at h17
  exact lt_irrefl _ (lt_trans (add_lt_add_right ∟ hobtuse) h17)

/-- In acute-angled triangles the square on the side subtending the acute angle is less than the
squares on the sides containing the acute angle by twice the rectangle contained by one of the
sides about the acute angle, namely that on which the perpendicular falls, and the straight line
cut off within by the perpendicular towards the acute angle. -/
theorem Prop13 {A B C D : Point} (hABC : Triangle A B C) (hB : IsAcute A B C) (hC : IsAcute A C B)
    (hD : Collinear B C D) (hAD : ∀ P : Point, Collinear B C P → P ≠ D → ∠ A D P = ∟) :
    sq A C + (rect C B B D + rect C B B D) = sq C B + sq B A := by
  -- Let ABC be an acute-angled triangle having the angle at B acute, and let AD be drawn from
  -- the point A perpendicular to BC;
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABC.ne₂₃
  have hD_BC : OnLine D BC := by
    obtain ⟨L, hB_L, hC_L, hD_L⟩ := hD
    exact (line_unique hABC.ne₂₃ hB_L hC_L hB_BC hC_BC) ▸ hD_L
  have hA_BC : ¬ OnLine A BC := hABC.bca.off_line hB_BC hC_BC
  have col : ∀ {P : Point}, OnLine P BC → Collinear B C P :=
    fun h => ⟨BC, hB_BC, hC_BC, h⟩
  have hDB : D ≠ B := by
    intro e
    have h : ∠ A B C < ∟ := hB
    rw [← e, hAD C (col hC_BC) (e ▸ hABC.ne₂₃.symm)] at h
    exact lt_irrefl _ h
  have hDC : D ≠ C := by
    intro e
    have h : ∠ A C B < ∟ := hC
    rw [← e, hAD B (col hB_BC) (e ▸ hABC.ne₂₃)] at h
    exact lt_irrefl _ h
  have hDA : D ≠ A := fun e => hA_BC (e ▸ hD_BC)
  have hADB : ∠ A D B = ∟ := hAD B (col hB_BC) hDB.symm
  have hADC : ∠ A D C = ∟ := hAD C (col hC_BC) hDC.symm
  -- I say that the square on AC is less than the squares on CB, BA by twice the rectangle
  -- contained by CB, BD.
  -- For, since the straight line CB has been cut at random at D,
  /- "Cut off within": the acute angles at B and C exclude a foot beyond either
     end, by I.13 and I.17. -/
  have hBDC : Between B D C := by
    rcases between_cases hDB.symm hDC hABC.ne₂₃ hB_BC hD_BC hC_BC with h | h | h
    · exact h
    · exact absurd h (Prop13.not_beyond hB_BC hC_BC hD_BC hA_BC hB hADB)
    · exact absurd (between_symm h)
        (Prop13.not_beyond hC_BC hB_BC hD_BC hA_BC hC hADC)
  -- the squares on CB, BD are equal to twice the rectangle contained by CB, BD and the square
  -- on DC. [II. 7]
  have h7 : sq C B + sq B D = rect C B B D + rect C B B D + sq D C :=
    Prop7 (between_symm hBDC)
  -- Let the square on DA be added to each;
  have haddDA := CommonNotion2 h7 (rfl : sq D A = sq D A)
  -- therefore the squares on CB, BD, DA are equal to twice the rectangle contained by CB, BD
  -- and the squares on AD, DC.
  have hadd : sq C B + sq B D + sq D A =
      rect C B B D + rect C B B D + (sq A D + sq D C) := by
    rw [haddDA, sq_symm D A]
    ac_rfl
  -- But the square on AB is equal to the squares on BD, DA, for the angle at D is
  -- right; [I. 47]
  have hBDA : ∠ B D A = ∟ := (angle_symm hDB.symm hDA.symm).trans hADB
  have h47a : sq A B = sq B D + sq D A := by
    rw [sq_symm A B]
    exact BookI.Prop47.sq (Triangle.of_line hD_BC hB_BC hDB hA_BC) hBDA
  -- and the square on AC is equal to the squares on AD, DC;
  have h47b : sq A C = sq A D + sq D C :=
    BookI.Prop47.sq (Triangle.of_line hD_BC hC_BC hDC hA_BC).acb hADC
  -- therefore the squares on CB, BA are equal to the square on AC and twice the rectangle CB,
  -- BD,
  have h : sq C B + sq B A = sq A C + (rect C B B D + rect C B B D) := by
    rw [sq_symm B A, h47a, h47b, ← add_assoc, hadd]
    ac_rfl
  -- so that the square on AC alone is less than the squares on CB, BA by twice the rectangle
  -- contained by CB, BD.
  exact h.symm
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookII
