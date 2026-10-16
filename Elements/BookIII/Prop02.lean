import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop05
import Elements.BookI.Helpers
import Elements.BookI.Prop16
import Elements.BookI.Prop19
import Elements.BookIII.Prop01

/-!
# Book III, Proposition 2

Euclid's text, in Heath's translation: [`heath/III/02.md`](../../heath/III/02.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- Euclid's figure takes the centre off `AB`. When the centre `D` is on `AB`,
a point `E` between its ends is nearer `D` than either end: `DE` is part of
`DA` or of `DB`, which are equal. -/
theorem Prop2.through_centre {A B D E : Point} {L : Line} (hADB : Between A D B)
    (hAEB : Between A E B) (hD_L : OnLine D L) (hA_L : OnLine A L) (hDA_DB : ‖D A‖ = ‖D B‖) :
    ‖D E‖ < ‖D B‖ := by
  by_cases hED : E = D
  · subst hED
    rw [len_self]
    exact len_pos (ne_of_between (between_symm hADB)).symm
  have hB_L := on_line_of_between hADB hA_L hD_L
  have hE_L := on_line_of_between_ends hAEB hA_L hB_L
  rcases between_cases (ne_of_between hADB) (Ne.symm hED) (ne_of_between hAEB)
      hA_L hD_L hE_L with h | h | h
  · /- If D is between A and E, then E is between D and B. -/
    exact len_lt_of_between (between_inner h hAEB)
  · /- A cannot be between D and E, since D is between A and B. -/
    exact absurd (between_of_between_right h hAEB) (not_between_of_between hADB)
  · /- If E is between A and D, then DE is less than DA. -/
    rw [← hDA_DB]
    exact len_lt_of_between (between_symm h)

/-- If on the circumference of a circle two points be taken at random, the straight line joining the
points will fall within the circle. -/
theorem Prop2 {A B : Point} {ABC : Circle} (hABC : ∃ D : Point, Centre D ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) :
    ∀ E : Point, Between A E B → InsideCircle E ABC := by
  -- Let ABC be a circle, and let two points A, B be taken at random on its circumference;
  -- I say that the straight line joined from A to B will fall within the circle.
  intro E hAEB
  -- For suppose it does not, but, if possible, let it fall outside, as AEB;
  /- The comparison DE < DB serves both suppositions, outside and on the circle.
     The outside supposition, and the point F it supplies, are taken below in `hout`. -/
  -- let the centre of the circle ABC be taken [III. 1], and let it be D; let DA, DB be joined,
  -- and let DFE be drawn through.
  obtain ⟨D, -, -, -, hD, -⟩ := Prop1 hABC hA hB (ne_of_between_ends hAEB)
  have hAB : A ≠ B := ne_of_between_ends hAEB
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hE_L := on_line_of_between_ends hAEB hA_L hB_L
  -- Then, since DA is equal to DB,
  have hDA_DB : ‖D A‖ = ‖D B‖ := Definition15 hD hA hB
  have hDE_DB : ‖D E‖ < ‖D B‖ := by
    by_cases hD_L : OnLine D L
    · exact Prop2.through_centre
        (between_of_inside_chord hD_L hA_L hB_L (centre_inside hD) hA hB hAB)
        hAEB hD_L hA_L hDA_DB
    have hDAB : Triangle D A B := Triangle.of_line hA_L hB_L hAB hD_L |>.cab
    have hDAE : Triangle D A E :=
      Triangle.of_line hA_L hE_L (ne_of_between hAEB) hD_L |>.cab
    have hDEB : Triangle D E B :=
      Triangle.of_line hE_L hB_L (ne_of_between (between_symm hAEB)).symm hD_L |>.cab
    -- the angle DAE is also equal to the angle DBE. [I. 5]
    have hDAE_DBE : ∠ D A E = ∠ D B E := by
      rw [angle_onRay_right (OnRay.of_between hAEB) hDAB.ne₁₂,
        angle_onRay_right (OnRay.of_between (between_symm hAEB)) hDAB.ne₁₃]
      exact BookI.Prop5.base hDAB hDA_DB
    -- And, since one side AEB of the triangle DAE is produced,
    -- the angle DEB is greater than the angle DAE. [I. 16]
    have hDAE_DEB : ∠ D A E < ∠ D E B := by
      rw [angle_symm hDAE.ne₁₂ hDAE.ne₂₃.symm]
      exact (BookI.Prop16 hDAE hAEB).1
    -- But the angle DAE is equal to the angle DBE;
    -- therefore the angle DEB is greater than the angle DBE.
    have hDBE_DEB : ∠ D B E < ∠ D E B := hDAE_DBE ▸ hDAE_DEB
    -- And the greater angle is subtended by the greater side; [I. 19]
    -- therefore DB is greater than DE.
    exact BookI.Prop19 hDEB (by rw [angle_symm hDEB.ne₂₃ hDEB.ne₁₃]; exact hDBE_DEB)
  have hout : ¬ OutsideCircle E ABC := by
    intro hE_out
    have hDE : D ≠ E := fun e => hE_out.1 (e ▸ centre_inside hD)
    obtain ⟨N, hD_N, hE_N⟩ := Postulate1 D E hDE
    /- DFE crosses the circle between its centre D and the supposed outside point E
       (System E, Intersections 4). -/
    obtain ⟨F, hF, -, hDFE⟩ := line_circle_between (centre_inside hD) hD_N hE_out hE_N
    -- But DB is equal to DF;
    have hDB_DF : ‖D B‖ = ‖D F‖ := Definition15 hD hB hF
    -- therefore DF is greater than DE,
    have hDE_DF : ‖D E‖ < ‖D F‖ := hDB_DF ▸ hDE_DB
    -- the less than the greater: which is impossible.
    exact lt_irrefl _ (lt_trans hDE_DF (len_lt_of_between hDFE))
  -- Therefore the straight line joined from A to B will not fall outside the circle.
  -- Similarly we can prove that neither will it fall on the circumference itself;
  have hon : ¬ OnCircle E ABC := by
    intro hE_on
    have hDB_DE : ‖D B‖ = ‖D E‖ := Definition15 hD hB hE_on
    exact lt_irrefl _ (hDB_DE ▸ hDE_DB)
  -- therefore it will fall within.
  exact Classical.byContradiction fun hin => hout ⟨hin, hon⟩
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
