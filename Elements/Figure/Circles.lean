import Elements.Figure.Lines
import Elements.Figure.Areas

/-!
# Book Zero: circles

Euclid draws a circle with "centre A and distance AB" and then reads off his
figure which points are on it, inside it or outside it. These small facts
follow from Definition 15 and System E's rules for circles. So does one he
needs without drawing any circle at all: that a point taken "at random" on a
straight line can be taken near enough.
-/

namespace Elements

open Tacit

variable {A B C D : Point} {α : Circle}

/-- A circle has only one centre (System E, Generalities 2). This was an assumption
until 19 October 2026 and is now proved from the foundations: a straight line through
two supposed centres meets the circle at P and Q, and both centres bisect PQ by
Definition I.15. Equal doubles have equal halves, contradicting the strict order of
the lengths from P if the centres differ. -/
theorem Tacit.centre_unique {A B : Point} {α : Circle}
    (hA : Centre A α) (hB : Centre B α) : A = B := by
  by_cases hAB : A = B
  · exact hAB
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hAB
  obtain ⟨P, hP, hPL, hPAB⟩ :=
    line_circle_beyond (centre_inside hA) hAL hBL (Ne.symm hAB)
  obtain ⟨Q, hQ, hQL, hQAP⟩ :=
    line_circle_beyond (centre_inside hA) hAL hPL (ne_of_between hPAB)
  have hPAQ := between_symm hQAP
  have hPBQ := between_of_inside_chord hBL hPL hQL
    (centre_inside hB) hP hQ (ne_of_between_ends hPAQ)
  have eA := len_add_of_between hPAQ
  have eB := len_add_of_between hPBQ
  have rA : ‖P A‖ = ‖A Q‖ := (len_symm P A).trans (Definition15 hA hP hQ)
  have rB : ‖P B‖ = ‖B Q‖ := (len_symm P B).trans (Definition15 hB hP hQ)
  rw [← rA] at eA
  rw [← rB] at eB
  have heq : ‖P A‖ = ‖P B‖ := Magnitude.eq_of_add_self_eq (eA.trans eB.symm)
  exact False.elim (Magnitude.ne_of_lt (len_lt_of_between hPAB) heq)

/-- Between two points on or inside a circle, every point is inside (System E,
Circle 2). This was an assumption until 19 October 2026 and is now proved from
Circle 3, `outside_of_between`: if the middle point were not inside, the second
endpoint would be outside, contrary to its being inside or on the circle. -/
theorem Tacit.inside_of_between {A B C : Point} {α : Circle}
    (hA : InsideCircle A α ∨ OnCircle A α)
    (hB : InsideCircle B α ∨ OnCircle B α) (h : Between A C B) : InsideCircle C α :=
  Classical.byContradiction fun hC =>
    hB.elim (outside_of_between hA hC h).1 (outside_of_between hA hC h).2

/-- A point on a circle is not its centre. -/
theorem ne_of_centre_of_on (hA : Centre A α) (hC : OnCircle C α) : C ≠ A := by
  intro h
  subst h
  exact inside_not_on (centre_inside hA) hC

/-- A point farther from the centre than the circumference is outside the
circle. -/
theorem outside_of_len_gt (hA : Centre A α) (hD : OnCircle D α) (h : ‖A D‖ < ‖A B‖) :
    OutsideCircle B α := by
  constructor
  · intro hin
    exact lt_irrefl _ (lt_trans (len_lt_of_inside hA hD hin) h)
  · intro hon
    rw [Definition15 hA hD hon] at h
    exact lt_irrefl _ h

/-- A point between the centre and a point on the circle is within it. It is nearer the
centre than that point is, as the part is less than the whole, and so nearer than the
circumference by Definition I.15 and the transfer rules. This proof uses no proposition
and neither Circle 2 nor Circle 3. -/
theorem InsideCircle.of_between_centre {O P : Point} (hO : Centre O α)
    (hP : OnCircle P α) (h : Between O C P) : InsideCircle C α := by
  exact inside_of_len_lt hO hP (len_lt_of_between h)

/-- A point between the centre and a point within the circle is within it, when a point
of the circle is given. The nearer point is nearer than the point within, which is nearer
than the circumference by Definition I.15 and the transfer rules. This proof uses no
proposition and neither Circle 2 nor Circle 3. -/
theorem InsideCircle.of_between_centre_of_inside {O P R : Point} (hO : Centre O α)
    (hR : OnCircle R α) (hP : InsideCircle P α) (h : Between O C P) : InsideCircle C α := by
  exact inside_of_len_lt hO hR
    (lt_trans (len_lt_of_between h) (len_lt_of_inside hO hR hP))

/-- A chance point, but not too far out. If `P` is nearer to `O` than `C` is, and `Q`
lies beyond `P` as seen from `O` (or `O` is `P` itself), there is a point `F` between
`P` and `Q` that is nearer to `O` than `C` is, too. Euclid takes a point "at random" on
a straight line and in the next breath needs it near enough (I.5, I.9). A circle about
`O` through `C` keeps it in: `P` is inside that circle; if `Q` is not outside it, any
point between `P` and `Q` will do; if `Q` is outside, take a point between `P` and the
place `X` where `PQ` leaves the circle (Intersections 4). Either way `F` lies between
`O` and a point no farther from `O` than `C` is, `Q` or `X`, so `OF` is the less, as
the part is less than the whole. This proof uses the order of the points and neither
Circle 2 nor Circle 3; I.5 and I.9 therefore inherit neither through this lemma. -/
theorem exists_between_nearer {O P Q C : Point} (hPQ : P ≠ Q)
    (hO : O = P ∨ Between O P Q) (h : ‖O P‖ < ‖O C‖) :
    ∃ F : Point, Between P F Q ∧ ‖O F‖ < ‖O C‖ := by
  obtain ⟨α, hO_α, hC_α⟩ := Postulate3 O C (ne_of_len_gt h)
  have hP_α : InsideCircle P α := inside_of_len_lt hO_α hC_α h
  obtain ⟨L, hP_L, hQ_L⟩ := Postulate1 P Q hPQ
  by_cases hQ_α : InsideCircle Q α ∨ OnCircle Q α
  · /- `Q` is not outside the circle: `F`, taken between `P` and `Q`, lies between `O`
       and `Q`, so `OF` is less than `OQ`, which is not greater than `OC`. -/
    obtain ⟨F, -, hPFQ, -⟩ := exists_point_between hP_L hQ_L hPQ []
    have hOFQ : Between O F Q := by
      rcases hO with rfl | hOPQ
      · exact hPFQ
      · exact between_symm
          (between_of_between_left (between_symm hOPQ) (between_symm hPFQ))
    refine ⟨F, hPFQ, ?_⟩
    rcases hQ_α with hQ_in | hQ_on
    · exact lt_trans (len_lt_of_between hOFQ) (len_lt_of_inside hO_α hC_α hQ_in)
    · rw [Definition15 hO_α hC_α hQ_on]
      exact len_lt_of_between hOFQ
  · /- `Q` is outside: `PQ` leaves the circle at `X`, and `F` is taken between `P` and
       `X`. `F` lies between `O` and `X`, so `OF` is less than the radius `OX`. -/
    have hQ_out : OutsideCircle Q α := ⟨fun h => hQ_α (Or.inl h), fun h => hQ_α (Or.inr h)⟩
    obtain ⟨X, hX_α, hX_L, hPXQ⟩ := line_circle_between hP_α hP_L hQ_out hQ_L
    obtain ⟨F, -, hPFX, -⟩ := exists_point_between hP_L hX_L (ne_of_between hPXQ) []
    have hOFX : Between O F X := by
      rcases hO with rfl | hOPQ
      · exact hPFX
      · have hOPX : Between O P X := between_cut hOPQ hPXQ
        exact between_symm
          (between_of_between_left (between_symm hOPX) (between_symm hPFX))
    refine ⟨F, between_of_between_left hPXQ hPFX, ?_⟩
    rw [Definition15 hO_α hC_α hX_α]
    exact len_lt_of_between hOFX

end Elements
