import Elements.Figure.Lengths

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

/-- A point on a circle is not its centre. -/
theorem ne_of_centre_of_on (hA : Centre A α) (hC : OnCircle C α) : C ≠ A := by
  intro h
  subst h
  exact inside_not_on (centre_inside hA) hC

/-- A point on a circle is not inside it. -/
theorem not_inside_of_on (h : OnCircle A α) : ¬ InsideCircle A α :=
  fun h' => inside_not_on h' h

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

/-- A chance point, but not too far out. If `P` is nearer to `O` than `C` is, there is
a point `F` between `P` and `Q` that is nearer to `O` than `C` is, too. Euclid takes a
point "at random" on a straight line and in the next breath needs it near enough
(I.5, I.9). A circle about `O` through `C` keeps it in: `P` is inside that circle; if
`Q` is not outside it, any point between `P` and `Q` will do (System E, Circle 2); if
`Q` is outside, take a point between `P` and the place where `PQ` leaves the circle
(Intersections 4). -/
theorem exists_between_nearer {O P Q C : Point} (hPQ : P ≠ Q) (h : ‖O P‖ < ‖O C‖) :
    ∃ F : Point, Between P F Q ∧ ‖O F‖ < ‖O C‖ := by
  obtain ⟨α, hO_α, hC_α⟩ := Postulate3 O C (ne_of_len_gt h)
  have hP_α : InsideCircle P α := inside_of_len_lt hO_α hC_α h
  obtain ⟨L, hP_L, hQ_L⟩ := Postulate1 P Q hPQ
  by_cases hQ_α : InsideCircle Q α ∨ OnCircle Q α
  · /- `Q` is not outside the circle: any point between `P` and `Q` is inside it. -/
    obtain ⟨F, -, hPFQ, -⟩ := exists_point_between hP_L hQ_L hPQ []
    exact ⟨F, hPFQ, len_lt_of_inside hO_α hC_α (inside_of_between (Or.inl hP_α) hQ_α hPFQ)⟩
  · /- `Q` is outside: `PQ` leaves the circle at a point `X` between `P` and `Q`, and
       `F` is taken between `P` and `X`. -/
    have hQ_out : OutsideCircle Q α := ⟨fun h => hQ_α (Or.inl h), fun h => hQ_α (Or.inr h)⟩
    obtain ⟨X, hX_α, hX_L, hPXQ⟩ := line_circle_between hP_α hP_L hQ_out hQ_L
    obtain ⟨F, -, hPFX, -⟩ := exists_point_between hP_L hX_L (ne_of_between hPXQ) []
    exact ⟨F, between_of_between_left hPXQ hPFX,
      len_lt_of_inside hO_α hC_α (inside_of_between (Or.inl hP_α) (Or.inr hX_α) hPFX)⟩

end Elements
