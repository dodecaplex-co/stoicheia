import Elements.Figure.Basics
import Elements.Foundations.Postulates
import Elements.Foundations.Tacit.Metric
import Elements.Foundations.Tacit.Transfer
import Check.Hand
import Check.Generator
import Model.Laws.«areas-p5»

/-!
# Checking the hand translation of the areas and Postulate 5

As in [Check/Hand.lean](Hand.lean): the library's own words are put in for the signature's
fields (`Check.original`), and Lean is asked whether each law translated by hand in
`Model/Laws/areas-p5.lean` then is the library's declaration. Each check is `rfl`, which
the kernel accepts only if the two are the same proposition, up to unfolding definitions.
None of these laws quantifies over the kind of magnitude, so every kernel comparison
is `rfl`. The library's axioms and theorems are read through `type_of%`, which takes
a declaration's statement and does not use its proof. `area_swap` and
`between_of_area_add`, now proved from area rotation, addition and positivity in
`Elements/Figure/AreaRules.lean`, are also compared directly with their theorem types
by `comparePlanted`, including binder kinds.
-/

namespace Check

example : Model.Hand.area_degenerate original = type_of% @Elements.Tacit.area_degenerate :=
  rfl

example : Model.Hand.area_rotate original = type_of% @Elements.Tacit.area_rotate := rfl

example : Model.Hand.area_swap original = type_of% @Elements.Tacit.area_swap := rfl

example : Model.Hand.area_congruent original = type_of% @Elements.Tacit.area_congruent := rfl

example : Model.Hand.area_eq_zero_of_on_line original =
    type_of% @Elements.Tacit.area_eq_zero_of_on_line := rfl

example : Model.Hand.on_line_of_area_eq_zero original =
    type_of% @Elements.Tacit.on_line_of_area_eq_zero := rfl

example : Model.Hand.area_add_of_between original =
    type_of% @Elements.Tacit.area_add_of_between := rfl

example : Model.Hand.between_of_area_add original =
    type_of% @Elements.Tacit.between_of_area_add := rfl

example : Model.Hand.Postulate5 original = type_of% @Elements.Postulate5 := rfl

/-! ## The hand translations against the generated laws -/

example (S : Model.Signature) : Model.Hand.area_degenerate S =
    Model.Law.Tacit.area_degenerate S := rfl
example (S : Model.Signature) : Model.Hand.area_rotate S =
    Model.Law.Tacit.area_rotate S := rfl
run_cmd (Check.Generator.comparePlanted ``Model.Hand.area_swap
  ``Elements.Tacit.area_swap)
example (S : Model.Signature) : Model.Hand.area_congruent S =
    Model.Law.Tacit.area_congruent S := rfl
example (S : Model.Signature) : Model.Hand.area_eq_zero_of_on_line S =
    Model.Law.Tacit.area_eq_zero_of_on_line S := rfl
example (S : Model.Signature) : Model.Hand.on_line_of_area_eq_zero S =
    Model.Law.Tacit.on_line_of_area_eq_zero S := rfl
example (S : Model.Signature) : Model.Hand.area_add_of_between S =
    Model.Law.Tacit.area_add_of_between S := rfl
run_cmd (Check.Generator.comparePlanted ``Model.Hand.between_of_area_add
  ``Elements.Tacit.between_of_area_add)
example (S : Model.Signature) : Model.Hand.Postulate5 S =
    Model.Law.Postulate5 S := rfl

end Check
