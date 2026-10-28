import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop05
import Elements.BookI.Helpers
import Elements.BookI.Prop16
import Elements.BookI.Prop19

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
theorem Prop2 {A B : Point} {ABC : Circle} (hA : OnCircle A ABC)
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
  /- III.1 is not needed: the proof uses the centre alone, which the rule `exists_centre`
     gives, so the centre is taken from it, and Heath's reference stays on the page. -/
  obtain ⟨D, hD⟩ := exists_centre ABC
  have hAB : A ≠ B := ne_of_between_ends hAEB
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hE_L := on_line_of_between_ends hAEB hA_L hB_L
  -- Then, since DA is equal to DB,
  have hDA_DB : ‖D A‖ = ‖D B‖ := Definition15 hD hA hB
  have hDE_DB : ‖D E‖ < ‖D B‖ := by
    by_cases hD_L : OnLine D L
    · exact Prop2.through_centre
        (between_of_centre_chord hD_L hA_L hB_L hD hA hB hAB)
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
theorem Prop2.within {A B C : Point} {α : Circle}
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
  exact Prop2 hP hQ C hPCQ

/-- Three points of a circle are not on one straight line: were they, one would lie
between the other two, and so within the circle, not on it. [III. 2] -/
theorem Prop2.triangle {A B C : Point} {α : Circle}
    (hA : OnCircle A α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) : Triangle A B C := by
  rintro ⟨L, hA_L, hB_L, hC_L⟩
  rcases between_cases hAB hBC hAC hA_L hB_L hC_L with h | h | h
  · exact inside_not_on (Prop2 hA hC B h) hB
  · exact inside_not_on (Prop2 hB hC A h) hA
  · exact inside_not_on (Prop2 hA hB C h) hC

/-- A straight line BC in a circle has a point of the circle on the other side of it from
any point K off it. Take M between B and C; it is within the circle [III. 2], so the
straight line KM, produced beyond M, meets the circle (System E, Intersections 5), on the
other side of BC from K (Pasch 3). -/
theorem Prop2.oppositeSide {B C K : Point} {α : Circle}
    (hB : OnCircle B α) (hC : OnCircle C α) (hK : Triangle B C K) :
    ∃ A : Point, OnCircle A α ∧ OppositeSidesOf A K B C := by
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hK.ne₁₂
  obtain ⟨M, hM_L, hBMC, -⟩ := exists_point_between hB_L hC_L hK.ne₁₂ []
  have hM_in : InsideCircle M α := Prop2 hB hC M hBMC
  have hK_L : ¬ OnLine K L := hK.off_line hB_L hC_L
  have hKM : K ≠ M := fun e => hK_L (e ▸ hM_L)
  obtain ⟨N, hK_N, hM_N⟩ := Postulate1 K M hKM
  obtain ⟨A, hA_α, hA_N, hAMK⟩ := line_circle_beyond hM_in hM_N hK_N hKM
  /- A is off BC: the straight lines KM and BC meet only at M, and A is on the circle,
     not within it. -/
  have hAM : A ≠ M := fun e => inside_not_on hM_in (e ▸ hA_α)
  have hA_L : ¬ OnLine A L := fun hA_L =>
    hK_L ((line_unique hAM hA_N hM_N hA_L hM_L) ▸ hK_N)
  exact ⟨A, hA_α, OppositeSidesOf.of_line hK.ne₁₂ hB_L hC_L
    ⟨hA_L, hK_L, pasch3 hAMK hM_L⟩⟩

/-- A straight line BC in a circle has a point of the circle on the same side of it as any
point K off it: take a point on the other side from K, and a point of the circle on the
other side from that (`Prop2.oppositeSide`). [III. 2] -/
theorem Prop2.sameSide {B C K : Point} {α : Circle}
    (hB : OnCircle B α) (hC : OnCircle C α) (hK : Triangle B C K) :
    ∃ A : Point, OnCircle A α ∧ SameSideOf A K B C := by
  obtain ⟨Q, hQ, -⟩ := exists_oppositeSidesOf hK []
  obtain ⟨A, hA_α, hAQ⟩ := Prop2.oppositeSide hB hC hQ.triangle
  exact ⟨A, hA_α, OppositeSidesOf.sameSideOf hAQ.symm hQ⟩

/-! ## Rules that III.2 gives back

System E's Circle 2 and Circle 3 say what III.2 proves, so they are proved here, after
it, under their own names, with Points 9 and Intersection 2, whose proofs used Circle 3
and now take its step from III.2 itself, and with Circle 1, which III.2 gives with the
order of three points on a straight line. Nothing before III.2 may use them: a use cites
III.2. -/

/-- A straight line through a point within a circle has that point between the points
where it meets the circle (System E, Circle 1). We prove it from III.2, by `Prop2.within`:
A is neither point, since it is within the circle and they are on it (Generalities 4), so
one of the three is between the other two (Between 6); and were B or C between the others,
it would be between a point on the circle and a point within it, and so within the circle,
not on it. This was an assumption until 26 October 2026. -/
theorem _root_.Elements.Tacit.between_of_inside_chord {A B C : Point} {L : Line}
    {α : Circle} (hA : OnLine A L) (hB : OnLine B L) (hC : OnLine C L)
    (hAin : InsideCircle A α) (hBon : OnCircle B α) (hCon : OnCircle C α) (hBC : B ≠ C) :
    Between B A C := by
  have hBA : B ≠ A := fun e => inside_not_on hAin (e ▸ hBon)
  have hAC : A ≠ C := fun e => inside_not_on hAin (e ▸ hCon)
  rcases between_cases hBA hAC hBC hB hA hC with h | h | h
  · exact h
  · exact absurd hBon (inside_not_on (Prop2.within (Or.inl hAin) (Or.inr hCon) h))
  · exact absurd hCon (inside_not_on (Prop2.within (Or.inr hBon) (Or.inl hAin) h))

/-- Once a straight line has left a circle, it does not come back (System E, Circle 3):
with A on or within the circle, and C, between A and B, not within it, B is outside the
circle. We prove it from III.2, by `Prop2.within`: were B within the circle or on it, C,
between A and B, would be within it. This was an assumption until 24 October 2026. -/
theorem _root_.Elements.Tacit.outside_of_between {A B C : Point} {α : Circle}
    (hA : InsideCircle A α ∨ OnCircle A α) (hC : ¬ InsideCircle C α)
    (h : Between A C B) : OutsideCircle B α :=
  ⟨fun hB => hC (Prop2.within hA (Or.inl hB) h), fun hB => hC (Prop2.within hA (Or.inr hB) h)⟩

/-- Between two points on or within a circle, every point is within it (System E,
Circle 2). This is `Prop2.within`, III.2 for points on or within the circle. It was an
assumption until 19 October 2026, and was then proved from Circle 3, an assumption until
24 October 2026. -/
theorem _root_.Elements.Tacit.inside_of_between {A B C : Point} {α : Circle}
    (hA : InsideCircle A α ∨ OnCircle A α)
    (hB : InsideCircle B α ∨ OnCircle B α) (h : Between A C B) : InsideCircle C α :=
  Prop2.within hA hB h

/-- Two distinct circumference points enclose an interior point avoiding any finite list. -/
private theorem inside_point_of_chord (α : Circle) (avoid : List Point) :
    ∃ A : Point, InsideCircle A α ∧ A ∉ avoid := by
  obtain ⟨B, hB, _⟩ := Elements.Tacit.exists_point_on_circle α []
  obtain ⟨C, hC, hCB⟩ := Elements.Tacit.exists_point_on_circle α [B]
  have hBC : B ≠ C := by
    intro e
    exact hCB (e ▸ List.mem_singleton_self B)
  obtain ⟨L, hBL, hCL⟩ := Postulate1 B C hBC
  obtain ⟨A, _, hBAC, hA⟩ := exists_point_between hBL hCL hBC avoid
  exact ⟨A, Prop2 hB hC A hBAC, hA⟩

/-- A point can be taken outside a circle while avoiding any finite list of points
(System E, Points 9). This was an assumption until 19 October 2026, and is proved from
Points 7 and 3, Postulates 1 and 2, and III.2, which took the place of Circle 3 on
24 October 2026: take a point between two points on the circle, within it by III.2, then
produce a straight line from it beyond the circumference. Postulate 2 chooses the endpoint
outside the given list, and the endpoint is outside the circle: were it within the circle
or on it, the point of the circle between would be within it, by III.2 again. -/
theorem _root_.Elements.Tacit.exists_point_outside_circle (α : Circle) (avoid : List Point) :
    ∃ A : Point, OutsideCircle A α ∧ A ∉ avoid := by
  obtain ⟨B, hB, _⟩ := inside_point_of_chord α []
  obtain ⟨C, hC, _⟩ := Elements.Tacit.exists_point_on_circle α []
  have hBC : B ≠ C := fun e => inside_not_on (e ▸ hB) hC
  obtain ⟨L, hBL, hCL⟩ := Postulate1 B C hBC
  obtain ⟨A, _, hBCA, hA⟩ := Postulate2 hBL hCL hBC avoid
  exact ⟨A, ⟨fun hA' => inside_not_on (Prop2.within (Or.inl hB) (Or.inl hA') hBCA) hC,
    fun hA' => inside_not_on (Prop2.within (Or.inl hB) (Or.inr hA') hBCA) hC⟩, hA⟩

/-- Two opposite extensions from an interior point meet the circumference distinctly. -/
private theorem circle_intersections_of_inside {A : Point} {L : Line} {α : Circle}
    (hA : InsideCircle A α) (hAL : OnLine A L) : LineMeetsCircle L α := by
  obtain ⟨C, hCL, hCA⟩ := exists_point_on_line L [A]
  have hCA' : C ≠ A := by simpa using hCA
  obtain ⟨P, hP, hPL, hPAC⟩ := line_circle_beyond hA hAL hCL hCA'
  obtain ⟨Q, hQ, hQL, hQAP⟩ :=
    line_circle_beyond hA hAL hPL (ne_of_between hPAC)
  exact ⟨Q, P, ne_of_between_ends hQAP, hQL, hQ, hPL, hP⟩

/-- A straight line separating two points on or inside a circle cuts the circle
(System E, Intersection 2). This was an assumption until 19 October 2026, and is proved
from Intersection 1, the order of collinear points, Pasch 2, III.2 and Intersections 5;
III.2 took the place of Circle 3 on 24 October 2026. The crossing lies between the given
points, and so within the circle by III.2; producing the straight line in both directions
gives two distinct circumference points. -/
theorem _root_.Elements.Tacit.line_meets_circle_of_opposite_sides {A B : Point} {L : Line}
    {α : Circle} (hA : InsideCircle A α ∨ OnCircle A α)
    (hB : InsideCircle B α ∨ OnCircle B α) (h : OppositeSides A B L) : LineMeetsCircle L α := by
  have hAB : A ≠ B := fun e => h.2.2 (e ▸ same_side_refl h.1)
  obtain ⟨M, hAM, hBM⟩ := Postulate1 A B hAB
  obtain ⟨hLM, X, hXL, hXM⟩ := lines_meet_of_opposite_sides h hAM hBM
  have hAXB : Between A X B := between_at_crossing hLM hXL hXM hAM hBM hAB
    (fun e => h.1 (e ▸ hXL)) (fun e => h.2.1 (e ▸ hXL)) h.2.2
  exact circle_intersections_of_inside (Prop2.within hA hB hAXB) hXL

end Elements.BookIII
