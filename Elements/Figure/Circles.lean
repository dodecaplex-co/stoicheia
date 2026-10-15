import Elements.Figure.Lengths

/-!
# Book Zero: circles

Euclid draws a circle with "centre A and distance AB" and then reads off his
figure which points are on it, inside it or outside it. These small facts
follow from Definition 15 and System E's rules for circles.
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

end Elements
