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

example : Model.Hand.lines_meet_of_opposite_sides_intersections original =
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

example : Model.Hand.between_of_inside_chord_intersections original =
    type_of% @Elements.Tacit.between_of_inside_chord := rfl

example : Model.Hand.inside_of_between_intersections original =
    type_of% @Elements.Tacit.inside_of_between := rfl

example : Model.Hand.outside_of_between_intersections original =
    type_of% @Elements.Tacit.outside_of_between := rfl

example : Model.Hand.not_same_side_of_circles_meet_intersections original =
    type_of% @Elements.Tacit.not_same_side_of_circles_meet := rfl

example (S : Model.Signature) : Model.Hand.Intersections.LinesMeet S = S.LinesMeet := rfl
example : Model.Hand.Intersections.LinesMeet original = Elements.LinesMeet := rfl
example (S : Model.Signature) : Model.Hand.Intersections.LineMeetsCircle S = S.LineMeetsCircle := rfl
example : Model.Hand.Intersections.LineMeetsCircle original = Elements.LineMeetsCircle := rfl

/-! ## The hand translations against the generated laws -/

example (S : Model.Signature) : Model.Hand.lines_meet_of_opposite_sides_intersections S =
    Model.Law.Tacit.lines_meet_of_opposite_sides S := rfl
example (S : Model.Signature) : Model.Hand.line_meets_circle_of_opposite_sides S =
    Model.Law.Tacit.line_meets_circle_of_opposite_sides S := rfl
example (S : Model.Signature) : Model.Hand.line_meets_circle_of_inside S =
    Model.Law.Tacit.line_meets_circle_of_inside S := rfl
example (S : Model.Signature) : Model.Hand.line_circle_between S =
    Model.Law.Tacit.line_circle_between S := rfl
example (S : Model.Signature) : Model.Hand.line_circle_beyond S =
    Model.Law.Tacit.line_circle_beyond S := rfl
example (S : Model.Signature) : Model.Hand.between_of_inside_chord_intersections S =
    Model.Law.Tacit.between_of_inside_chord S := rfl
example (S : Model.Signature) : Model.Hand.inside_of_between_intersections S =
    Model.Law.Tacit.inside_of_between S := rfl
example (S : Model.Signature) : Model.Hand.outside_of_between_intersections S =
    Model.Law.Tacit.outside_of_between S := rfl
example (S : Model.Signature) : Model.Hand.not_same_side_of_circles_meet_intersections S =
    Model.Law.Tacit.not_same_side_of_circles_meet S := rfl

end Check
