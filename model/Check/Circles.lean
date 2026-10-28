import Elements.Figure.Basics
import Elements.BookI.Prop07
import Elements.Figure.Circles
import Elements.BookIII.Prop02
import Elements.Foundations.Postulates
import Elements.Foundations.Definitions
import Elements.Foundations.Tacit.Constructions
import Elements.Foundations.Tacit.Diagram
import Elements.Foundations.Tacit.Metric
import Elements.Foundations.Tacit.Transfer
import Check.Hand
import Check.Generator
import Model.Laws.circles

/-!
# Checking the hand-translated circle rules against the library

`Model/Laws/circles.lean` translates the circle rules by hand. As in `Check/Hand.lean`, the
library's own words are put in for the signature's fields (`original`), and the kernel is
asked whether each translated law then is the library's declaration. Each kernel check is `rfl`:
a translation that drops a guard, swaps two arguments or changes the order of the binders
fails here, and the build fails with it. The defined words these laws reach,
`OutsideCircle`, `OppositeSides` and `CirclesMeet`, are checked in `Check/Hand.lean`.

The kernel comparisons read the library's declarations through `type_of%`. For the
properties retained through axiom retirement, `comparePlanted` also translates the
hand definition back and compares it directly with the declaration's type, including
binder kinds. Both checks read only the statement, whether it is an axiom or a theorem.
Nothing in `Model/` imports this file.
-/

namespace Check

open Model.Hand

/-! ## Drawing a circle -/

example : Postulate3 original = type_of% @Elements.Postulate3 := rfl
example : Definition15 original = type_of% @Elements.Definition15 := rfl

/-! ## A centre, and the inside of a circle -/

example : centre_unique_circles original = type_of% @Elements.Tacit.centre_unique := rfl
example : centre_inside_circles original = type_of% @Elements.Tacit.centre_inside := rfl
example : inside_not_on_circles original = type_of% @Elements.Tacit.inside_not_on := rfl
example : circle_eq_circles original = type_of% @Elements.Tacit.circle_eq := rfl
example : inside_of_len_lt_circles original = type_of% @Elements.Tacit.inside_of_len_lt := rfl
example : len_lt_of_inside_circles original = type_of% @Elements.Tacit.len_lt_of_inside := rfl
example : on_circle_of_len_eq_circles original = type_of% @Elements.Tacit.on_circle_of_len_eq := rfl
example : radius_ne_zero original = type_of% @Elements.Tacit.radius_ne_zero := rfl

/-! ## System E's Circle 1 to 4 -/

example : between_of_inside_chord original =
    type_of% @Elements.Tacit.between_of_inside_chord := rfl
example : inside_of_between original = type_of% @Elements.Tacit.inside_of_between := rfl
example : outside_of_between original = type_of% @Elements.Tacit.outside_of_between := rfl
example : not_same_side_of_circles_meet original =
    type_of% @Elements.Tacit.not_same_side_of_circles_meet := rfl

/-! ## Finite avoidance: open regions and the circumference -/

example : exists_point_circles original = type_of% @Elements.Tacit.exists_point := rfl
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

/-! ## The hand translations against generated laws or declaration types -/

example (S : Model.Signature) : Model.Hand.Postulate3 S =
    Model.Law.Postulate3 S := rfl
example (S : Model.Signature) : Model.Hand.Definition15 S =
    Model.Law.Definition15 S := rfl
run_cmd (Check.Generator.comparePlanted ``Model.Hand.centre_unique_circles
  ``Elements.Tacit.centre_unique)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.centre_inside_circles
  ``Elements.Tacit.centre_inside)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.inside_not_on_circles
  ``Elements.Tacit.inside_not_on)
example (S : Model.Signature) : Model.Hand.circle_eq_circles S =
    Model.Law.Tacit.circle_eq S := rfl
run_cmd (Check.Generator.comparePlanted ``Model.Hand.inside_of_len_lt_circles
  ``Elements.Tacit.inside_of_len_lt)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.len_lt_of_inside_circles
  ``Elements.Tacit.len_lt_of_inside)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.on_circle_of_len_eq_circles
  ``Elements.Tacit.on_circle_of_len_eq)
example (S : Model.Signature) : Model.Hand.radius_ne_zero S =
    Model.Law.Tacit.radius_ne_zero S := rfl
run_cmd (Check.Generator.comparePlanted ``Model.Hand.between_of_inside_chord
  ``Elements.Tacit.between_of_inside_chord)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.inside_of_between
  ``Elements.Tacit.inside_of_between)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.outside_of_between
  ``Elements.Tacit.outside_of_between)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.not_same_side_of_circles_meet
  ``Elements.Tacit.not_same_side_of_circles_meet)
example (S : Model.Signature) : Model.Hand.exists_point_circles S =
    Model.Law.Tacit.exists_point S := rfl
run_cmd (Check.Generator.comparePlanted ``Model.Hand.exists_point_same_side
  ``Elements.Tacit.exists_point_same_side)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.exists_point_opposite_side
  ``Elements.Tacit.exists_point_opposite_side)
example (S : Model.Signature) : Model.Hand.exists_point_inside_circle S =
    Model.Law.Tacit.exists_point_inside_circle S := rfl
run_cmd (Check.Generator.comparePlanted ``Model.Hand.exists_point_outside_circle
  ``Elements.Tacit.exists_point_outside_circle)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.exists_point_on_circle
  ``Elements.Tacit.exists_point_on_circle)

end Check
