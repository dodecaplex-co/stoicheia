import Elements.Foundations.Postulates
import Check.Hand
import Model.Laws.incidence

/-!
# Checking the incidence and line laws against the library

`Model/Laws/incidence.lean` translates the incidence and line laws by hand. Here, as in
`Check/Hand.lean`, the library's own words are put in for the signature's fields
(`original`), and the kernel is asked whether each translated law, and the one new defined
word, then is the library's declaration. Each check is `rfl`, and a dropped guard, two
swapped arguments or a change in the order of the binders fails it, and the build with it.

This file reads the library's axioms only through `type_of%`, which takes a declaration's
statement and does not use it. Nothing in `Model/` imports this file.
-/

namespace Check

/-! ## The defined word -/

example : original.LinesMeet = Elements.LinesMeet := rfl

/-! ## The laws -/

example : Model.Hand.Postulate1 original = type_of% @Elements.Postulate1 := rfl

example : Model.Hand.line_unique original = type_of% @Elements.Tacit.line_unique := rfl

example : Model.Hand.centre_unique original = type_of% @Elements.Tacit.centre_unique := rfl

example : Model.Hand.centre_inside original = type_of% @Elements.Tacit.centre_inside := rfl

example : Model.Hand.inside_not_on original = type_of% @Elements.Tacit.inside_not_on := rfl

example : Model.Hand.lines_meet_of_opposite_sides original =
    type_of% @Elements.Tacit.lines_meet_of_opposite_sides := rfl

example : Model.Hand.exists_point original = type_of% @Elements.Tacit.exists_point := rfl

example : Model.Hand.exists_point_on_line original =
    type_of% @Elements.Tacit.exists_point_on_line := rfl

example : Model.Hand.exists_point_on_line_off_line original =
    type_of% @Elements.Tacit.exists_point_on_line_off_line := rfl

example : Model.Hand.exists_point_between original =
    type_of% @Elements.Tacit.exists_point_between := rfl

example : Model.Hand.Postulate2 original = type_of% @Elements.Postulate2 := rfl

end Check
