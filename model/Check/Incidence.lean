import Elements.Figure.Circles
import Elements.Foundations.Postulates
import Check.Hand
import Check.Generator
import Model.Laws.incidence

/-!
# Checking the incidence and line laws against the library

`Model/Laws/incidence.lean` translates the incidence and line laws by hand. Here, as in
`Check/Hand.lean`, the library's own words are put in for the signature's fields
(`original`), and the kernel is asked whether each translated law, and the one new defined
word, then is the library's declaration. Each kernel check is `rfl`, and a dropped guard, two
swapped arguments or a change in the order of the binders fails it, and the build with it.

The kernel comparisons read the library's declarations through `type_of%`. For the
properties retained through axiom retirement, `comparePlanted` also translates the
hand definition back and compares it directly with the declaration's type, including
binder kinds. Both checks read only the statement, whether it is an axiom or a theorem.
Nothing in `Model/` imports this file.
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

/-! ## The hand translations against generated laws or declaration types -/

example (S : Model.Signature) : Model.Hand.LinesMeet S = S.LinesMeet := rfl
example : Model.Hand.LinesMeet original = Elements.LinesMeet := rfl

example (S : Model.Signature) : Model.Hand.Postulate1 S = Model.Law.Postulate1 S := rfl
example (S : Model.Signature) : Model.Hand.line_unique S = Model.Law.Tacit.line_unique S := rfl
run_cmd (Check.Generator.comparePlanted ``Model.Hand.centre_unique
  ``Elements.Tacit.centre_unique)
example (S : Model.Signature) : Model.Hand.centre_inside S = Model.Law.Tacit.centre_inside S := rfl
example (S : Model.Signature) : Model.Hand.inside_not_on S = Model.Law.Tacit.inside_not_on S := rfl
example (S : Model.Signature) : Model.Hand.lines_meet_of_opposite_sides S = Model.Law.Tacit.lines_meet_of_opposite_sides S := rfl
example (S : Model.Signature) : Model.Hand.exists_point S = Model.Law.Tacit.exists_point S := rfl
example (S : Model.Signature) : Model.Hand.exists_point_on_line S = Model.Law.Tacit.exists_point_on_line S := rfl
example (S : Model.Signature) : Model.Hand.exists_point_on_line_off_line S = Model.Law.Tacit.exists_point_on_line_off_line S := rfl
example (S : Model.Signature) : Model.Hand.exists_point_between S = Model.Law.Tacit.exists_point_between S := rfl
example (S : Model.Signature) : Model.Hand.Postulate2 S = Model.Law.Postulate2 S := rfl

end Check
