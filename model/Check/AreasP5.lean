import Elements.Foundations.Postulates
import Elements.Foundations.Tacit.Metric
import Elements.Foundations.Tacit.Transfer
import Check.Hand
import Model.Laws.«areas-p5»

/-!
# Checking the hand translation of the areas and Postulate 5

As in [Check/Hand.lean](Hand.lean): the library's own words are put in for the signature's
fields (`Check.original`), and Lean is asked whether each law translated by hand in
`Model/Laws/areas-p5.lean` then is the library's declaration. Each check is `rfl`, which
the kernel accepts only if the two are the same proposition, up to unfolding definitions.
None of these laws quantifies over the kind of magnitude, so every check is `rfl`. The
library's axioms are read only through `type_of%`, which takes a declaration's statement
and does not use it.
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

end Check
