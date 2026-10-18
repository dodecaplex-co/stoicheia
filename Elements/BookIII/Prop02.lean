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

/-- Euclid's figure takes the centre off AB. When the centre D is on AB,
a point E between its ends is nearer D than either end is, for DE is part of
DA or of DB, which are equal. -/
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
  /- DE is less than DB, and that one comparison serves both suppositions, outside and on
     the circle. We take up the outside one, and the point F it supplies, below. -/
  -- let the centre of the circle ABC be taken [III. 1], and let it be D; let DA, DB be joined,
  -- and let DFE be drawn through.
  have hAB : A ≠ B := ne_of_between_ends hAEB
  obtain ⟨D, -, -, -, hD, -⟩ := Prop1 hABC hA hB hAB
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


/-- III.2 for points on or within the circle: a point between two such points is within
it. Produced beyond each end that is within, the straight line meets the circle (System E,
Intersections 5), and the point lies between the two points where it meets it, so within
the circle by III.2. [III. 2] -/
theorem Prop2.within {A B C : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hA : InsideCircle A α ∨ OnCircle A α) (hB : InsideCircle B α ∨ OnCircle B α)
    (h : Between A C B) : InsideCircle C α := by
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B (ne_of_between_ends h)
  obtain ⟨P, hP, hP_L, hPCB⟩ : ∃ P : Point, OnCircle P α ∧ OnLine P L ∧ Between P C B := by
    rcases hA with hA | hA
    · obtain ⟨P, hP, hP_L, hPAB⟩ :=
        line_circle_beyond hA hA_L hB_L (ne_of_between_ends h).symm
      exact ⟨P, hP, hP_L,
        between_symm (between_of_between_left (between_symm hPAB) (between_symm h))⟩
    · exact ⟨A, hA, hA_L, h⟩
  obtain ⟨Q, hQ, hPCQ⟩ : ∃ Q : Point, OnCircle Q α ∧ Between P C Q := by
    rcases hB with hB | hB
    · obtain ⟨Q, hQ, -, hQBP⟩ := line_circle_beyond hB hB_L hP_L (ne_of_between_ends hPCB)
      exact ⟨Q, hQ, between_of_between_left (between_symm hQBP) hPCB⟩
    · exact ⟨B, hB, hPCB⟩
  exact Prop2 hα hP hQ C hPCQ

/-- Three points of a circle are not on one straight line: were they, one would lie
between the other two, and so within the circle, not on it. [III. 2] -/
theorem Prop2.triangle {A B C : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hA : OnCircle A α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) : Triangle A B C := by
  rintro ⟨L, hA_L, hB_L, hC_L⟩
  rcases between_cases hAB hBC hAC hA_L hB_L hC_L with h | h | h
  · exact inside_not_on (Prop2 hα hA hC B h) hB
  · exact inside_not_on (Prop2 hα hB hC A h) hA
  · exact inside_not_on (Prop2 hα hA hB C h) hC

/-- A straight line `BC` in a circle has a point of the circle on the other side of it
from any point `K` off it. Take `M` between `B` and `C`; it is within the circle [III. 2],
so the straight line `KM`, produced beyond `M`, meets the circle (System E, Intersections
5), on the other side of `BC` from `K` (Pasch 3). -/
theorem Prop2.oppositeSide {B C K : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hB : OnCircle B α) (hC : OnCircle C α) (hK : Triangle B C K) :
    ∃ A : Point, OnCircle A α ∧ OppositeSidesOf A K B C := by
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hK.ne₁₂
  obtain ⟨M, hM_L, hBMC, -⟩ := exists_point_between hB_L hC_L hK.ne₁₂ []
  have hM_in : InsideCircle M α := Prop2 hα hB hC M hBMC
  have hK_L : ¬ OnLine K L := hK.off_line hB_L hC_L
  have hKM : K ≠ M := fun e => hK_L (e ▸ hM_L)
  obtain ⟨N, hK_N, hM_N⟩ := Postulate1 K M hKM
  obtain ⟨A, hA_α, hA_N, hAMK⟩ := line_circle_beyond hM_in hM_N hK_N hKM
  /- `A` is off `BC`: the straight lines `KM` and `BC` meet only at `M`, and `A` is on
     the circle, not within it. -/
  have hAM : A ≠ M := fun e => inside_not_on hM_in (e ▸ hA_α)
  have hA_L : ¬ OnLine A L := fun hA_L =>
    hK_L ((line_unique hAM hA_N hM_N hA_L hM_L) ▸ hK_N)
  exact ⟨A, hA_α, OppositeSidesOf.of_line hK.ne₁₂ hB_L hC_L
    ⟨hA_L, hK_L, pasch3 hAMK hM_L⟩⟩

/-- A straight line `BC` in a circle has a point of the circle on the same side of it as
any point `K` off it: take a point on the other side from `K`, and a point of the circle
on the other side from that (`Prop2.oppositeSide`). [III. 2] -/
theorem Prop2.sameSide {B C K : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hB : OnCircle B α) (hC : OnCircle C α) (hK : Triangle B C K) :
    ∃ A : Point, OnCircle A α ∧ SameSideOf A K B C := by
  obtain ⟨Q, hQ, -⟩ := exists_oppositeSidesOf hK []
  obtain ⟨A, hA_α, hAQ⟩ := Prop2.oppositeSide hα hB hC hQ.triangle
  exact ⟨A, hA_α, OppositeSidesOf.sameSideOf hAQ.symm hQ⟩

end Elements.BookIII
