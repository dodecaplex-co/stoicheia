import Elements.Foundations.Postulates
import Elements.Foundations.Definitions
import Elements.Foundations.Tacit.Constructions
import Elements.Foundations.Tacit.Diagram
import Elements.Foundations.Tacit.Transfer
import Check.Hand
import Model.Laws.circles

/-!
# Checking the hand-translated circle rules against the library

`Model/Laws/circles.lean` translates the circle rules by hand. As in `Check/Hand.lean`, the
library's own words are put in for the signature's fields (`original`), and the kernel is
asked whether each translated law then is the library's declaration. Each check is `rfl`:
a translation that drops a guard, swaps two arguments or changes the order of the binders
fails here, and the build fails with it. The defined words these laws reach,
`OutsideCircle`, `OppositeSides` and `CirclesMeet`, are checked in `Check/Hand.lean`.

This file reads the library's axioms only through `type_of%`, which takes a declaration's
statement and does not use it. Nothing in `Model/` imports this file.
-/

namespace Check

open Model.Hand

/-! ## Drawing a circle -/

example : Postulate3 original = type_of% @Elements.Postulate3 := rfl
example : Definition15 original = type_of% @Elements.Definition15 := rfl

/-! ## A centre, and the inside of a circle -/

example : centre_unique original = type_of% @Elements.Tacit.centre_unique := rfl
example : centre_inside original = type_of% @Elements.Tacit.centre_inside := rfl
example : inside_not_on original = type_of% @Elements.Tacit.inside_not_on := rfl
example : circle_eq original = type_of% @Elements.Tacit.circle_eq := rfl
example : inside_of_len_lt original = type_of% @Elements.Tacit.inside_of_len_lt := rfl
example : len_lt_of_inside original = type_of% @Elements.Tacit.len_lt_of_inside := rfl
example : on_circle_of_len_eq original = type_of% @Elements.Tacit.on_circle_of_len_eq := rfl

/-! ## System E's Circle 1 to 4 -/

example : between_of_inside_chord original =
    type_of% @Elements.Tacit.between_of_inside_chord := rfl
example : inside_of_between original = type_of% @Elements.Tacit.inside_of_between := rfl
example : outside_of_between original = type_of% @Elements.Tacit.outside_of_between := rfl
example : not_same_side_of_circles_meet original =
    type_of% @Elements.Tacit.not_same_side_of_circles_meet := rfl

/-! ## Finite avoidance: open regions and the circumference -/

example : exists_point original = type_of% @Elements.Tacit.exists_point := rfl
example : exists_point_same_side original = type_of% @Elements.Tacit.exists_point_same_side :=
  rfl
example : exists_point_opposite_side original =
    type_of% @Elements.Tacit.exists_point_opposite_side := rfl
example : exists_point_inside_circle original =
    type_of% @Elements.Tacit.exists_point_inside_circle := rfl
example : exists_point_outside_circle original =
    type_of% @Elements.Tacit.exists_point_outside_circle := rfl
example : exists_point_on_circle original = type_of% @Elements.Tacit.exists_point_on_circle :=
  rfl

end Check
