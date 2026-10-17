import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop08
import Elements.BookI.Prop20
import Elements.BookI.Prop46
import Elements.BookIII.Prop01
import Elements.BookIII.Prop16
import Elements.BookIII.Prop17
import Elements.BookIII.Prop18
import Elements.BookIII.Prop36

/-!
# Book III, Proposition 37

Euclid's text, in Heath's translation: [`heath/III/37.md`](../../heath/III/37.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- The triangle `DBF` of Euclid's figure. A point `B` of the circle, with `DB` equal to a
straight line `DE` from `D` to a point `E` of the circle, `DEF` a triangle, is not on the
straight line through `D` and the centre `F`: were `B` between `D` and `F`, the sides `DE`,
`EF` would make up `DF`; were `F` between `D` and `B`, the sides `DF`, `FE` would make up
`DE`; either way two sides of the triangle `DEF` would not be greater than the third
[I. 20]. And `D`, outside the circle, is not between `B` and the centre. -/
theorem Prop37.triangle {B D E F : Point} {ABC : Circle} (hF : Centre F ABC)
    (hD : OutsideCircle D ABC) (hB : OnCircle B ABC) (hE : OnCircle E ABC)
    (hDEF : Triangle D E F) (hDE_DB : ‖D E‖ = ‖D B‖) : Triangle D B F := by
  rintro ⟨L, hD_L, hB_L, hF_L⟩
  have hDB : D ≠ B := fun e => hD.2 (e ▸ hB)
  have hBF : B ≠ F := fun e => inside_not_on (centre_inside hF) (e ▸ hB)
  have hDF : D ≠ F := fun e => hD.1 (e ▸ centre_inside hF)
  have hFE_FB : ‖F E‖ = ‖F B‖ := Definition15 hF hE hB
  rcases between_cases hDB hBF hDF hD_L hB_L hF_L with h | h | h
  · have h1 : ‖D B‖ + ‖B F‖ = ‖D F‖ := len_add_of_between h
    have h20 : ‖D F‖ < ‖D E‖ + ‖E F‖ := (BookI.Prop20 hDEF).2.1
    rw [← h1, hDE_DB, len_symm E F, hFE_FB, len_symm F B] at h20
    exact lt_irrefl _ h20
  · exact hD.1 (inside_of_between (Or.inr hB) (Or.inl (centre_inside hF)) h)
  · have h1 : ‖D F‖ + ‖F B‖ = ‖D B‖ := len_add_of_between h
    have h20 : ‖D E‖ < ‖E F‖ + ‖F D‖ := (BookI.Prop20 hDEF).2.2
    rw [hDE_DB, ← h1, len_symm E F, hFE_FB, len_symm F D, add_comm] at h20
    exact lt_irrefl _ h20

/-- If a point be taken outside a circle and from the point there fall on the circle two straight
lines, if one of them cut the circle, and the other fall on it, and if further the rectangle
contained by the whole of the straight line which cuts the circle and the straight line
intercepted on it outside between the point and the convex circumference be equal to the square
on the straight line which falls on the circle, the straight line which falls on it will touch
the circle. -/
theorem Prop37 {A B C D : Point} {ABC : Circle} (hABC : ∃ F : Point, Centre F ABC)
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hDCA : Between D C A) (h : rect A D D C = sq D B) :
    Touches D B ABC := by
  -- For let a point D be taken outside the circle ABC; from D let the two straight lines DCA,
  -- DB fall on the circle ACB; let DCA cut the circle and DB fall on it; and let the rectangle
  -- AD, DC be equal to the square on DB.
  -- I say that DB touches the circle ABC.
  -- For let DE be drawn touching ABC; let the centre of the circle ABC be taken, and let it be
  -- F; let FE, FB, FD be joined.
  obtain ⟨E, hE, hDE⟩ := Prop17 hABC hD
  obtain ⟨F, -, -, -, hF, -⟩ := Prop1 hABC hA hC (ne_of_between (between_symm hDCA))
  have hDE' : D ≠ E := hDE.1
  have hDB : D ≠ B := fun e => hD.2 (e ▸ hB)
  have hFE : F ≠ E := fun e => inside_not_on (centre_inside hF) (e ▸ hE)
  have hFB : F ≠ B := fun e => inside_not_on (centre_inside hF) (e ▸ hB)
  -- Thus the angle FED is right. [III. 18]
  obtain ⟨L, hD_L, hE_L⟩ := Postulate1 D E hDE'
  have hFED : ∠ F E D = ∟ :=
    Prop18 hF hE hDE ⟨L, hD_L, hE_L, hE_L⟩ D ⟨L, hD_L, hE_L, hD_L⟩ hDE'
  -- Now, since DE touches the circle ABC, and DCA cuts it,
  -- the rectangle AD, DC is equal to the square on DE. [III. 36]
  have h36 : rect A D D C = sq D E := Prop36 hABC hD hA hE hC hDCA hDE
  -- But the rectangle AD, DC was also equal to the square on DB;
  -- therefore the square on DE is equal to the square on DB;
  have hsq : sq D E = sq D B := CommonNotion1 h36.symm h.symm
  -- therefore DE is equal to DB.
  have hDE_DB : ‖D E‖ = ‖D B‖ := BookI.Prop46.sq hsq
  -- And FE is equal to FB;
  have hFE_FB : ‖F E‖ = ‖F B‖ := Definition15 hF hE hB
  -- therefore the two sides DE, EF are equal to the two sides DB, BF;
  have hED_BD : ‖E D‖ = ‖B D‖ := by rw [len_symm E D, hDE_DB, len_symm]
  have hEF_BF : ‖E F‖ = ‖B F‖ := by rw [len_symm E F, hFE_FB, len_symm]
  -- and FD is the common base of the triangles;
  have hDEF : Triangle D E F := fun hcol => hDE.not_inside hcol (centre_inside hF)
  have hDBF : Triangle D B F := Prop37.triangle hF hD hB hE hDEF hDE_DB
  -- therefore the angle DEF is equal to the angle DBF. [I. 8]
  have h8 : ∠ D E F = ∠ D B F := BookI.Prop8 hDEF.bac hDBF.bac hED_BD hEF_BF rfl
  -- But the angle DEF is right;
  have hDEF_right : ∠ D E F = ∟ := (angle_symm hDE' hFE).trans hFED
  -- therefore the angle DBF is also right.
  have hDBF_right : ∠ D B F = ∟ := h8.symm.trans hDEF_right
  -- And FB produced is a diameter;
  /- Our porism of III.16 is stated at the end of a radius, so Lean need not produce FB. -/
  -- and the straight line drawn at right angles to the diameter of a circle, from its
  -- extremity, touches the circle; [III. 16, Por.]
  have hBD : Touches B D ABC :=
    Prop16.porism hF hB hDBF.cba ((angle_symm hFB hDB).trans hDBF_right)
  -- therefore DB touches the circle.
  obtain ⟨M, hB_M, hD_M⟩ := Postulate1 B D hDB.symm
  have hDB_touch : Touches D B ABC :=
    hBD.of_collinear ⟨M, hB_M, hD_M, hD_M⟩ ⟨M, hB_M, hD_M, hB_M⟩ hDB
  -- Similarly this can be proved to be the case even if the centre be on AC.
  /- Lean needs no second case: III.36 is cited by its statement, which holds wherever
     the centre lies, and nothing else above looks at AC. -/
  -- Therefore etc.
  exact hDB_touch
  -- Q. E. D.

end Elements.BookIII
