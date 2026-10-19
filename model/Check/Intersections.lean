import Check.Hand
import Model.Laws.intersections

/-!
# Checking the hand-translated intersection rules against the library

`Model/Laws/intersections.lean` translates the intersection rules and the circle rules by
hand. As in `Check/Hand.lean`, the library's own words are put in for the signature's
fields (`original`), and Lean is asked whether each translated law, and each defined word
it reaches, is then the library's declaration. Each check is `rfl`: the kernel accepts it
only if the two are the same proposition, up to unfolding definitions, so a dropped guard,
two swapped arguments or a change in the order of the binders fails here, and the build
with it. Binder kinds, which the kernel does not see, are checked by reading each
statement against the lock's printed one, quoted above it, until the generator's syntactic
round trip covers them.

This file reads the library's axioms only through `type_of%`, which takes a declaration's
statement and does not use it. Nothing in `Model/` imports this file.
-/

namespace Check

/-! ## The defined words -/

example : original.LineMeetsCircle = Elements.LineMeetsCircle := rfl
example : original.LinesMeet = Elements.LinesMeet := rfl

/-! ## The intersection rules -/

example : Model.Hand.lines_meet_of_opposite_sides original =
    type_of% @Elements.Tacit.lines_meet_of_opposite_sides := rfl

example : Model.Hand.line_meets_circle_of_opposite_sides original =
    type_of% @Elements.Tacit.line_meets_circle_of_opposite_sides := rfl

example : Model.Hand.line_meets_circle_of_inside original =
    type_of% @Elements.Tacit.line_meets_circle_of_inside := rfl

example : Model.Hand.line_circle_between original =
    type_of% @Elements.Tacit.line_circle_between := rfl

example : Model.Hand.line_circle_beyond original =
    type_of% @Elements.Tacit.line_circle_beyond := rfl

/-! ## The circle rules -/

example : Model.Hand.between_of_inside_chord original =
    type_of% @Elements.Tacit.between_of_inside_chord := rfl

example : Model.Hand.inside_of_between original =
    type_of% @Elements.Tacit.inside_of_between := rfl

example : Model.Hand.outside_of_between original =
    type_of% @Elements.Tacit.outside_of_between := rfl

example : Model.Hand.not_same_side_of_circles_meet original =
    type_of% @Elements.Tacit.not_same_side_of_circles_meet := rfl

end Check
