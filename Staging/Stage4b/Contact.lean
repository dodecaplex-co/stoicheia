import Elements.Figure.OnCircles

/-!
# Staging: the point of contact of a straight line touching a circle

Brief 0007, stage 4b: the shared step the coordinator asked for on issue #53. `Touches A X α`
(Definition III.2) holds the point of contact inside it, behind a straight line named by A
and X. `Touches.contact` reads it off in one step, for a citer of `Prop17.general` that
needs the point where its straight line meets the circle. It cites no proposition, so it
belongs to Book Zero: it moves into `Elements/Figure/OnCircles.lean` when proved, beside
`Touches.not_inside`, and its proof falls to the owner of Book Zero.
-/

namespace Elements

open Tacit

/-- The point of contact of a straight line touching a circle. If the straight line AX
touches the circle α, some point B of α is on it; B may be A or X. -/
theorem Touches.contact {A X : Point} {α : Circle} (h : Touches A X α) :
    ∃ B : Point, OnCircle B α ∧ Collinear A X B := by
  sorry

end Elements
