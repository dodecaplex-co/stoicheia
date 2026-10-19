import Elements.Foundations.Postulates
import Elements.Foundations.Tacit.Transfer
import Check.Hand
import Model.Laws.angles

/-!
# Checking the hand translation of the angle laws

`Model/Laws/angles.lean` translates the ten angle laws, and the two words they reach, by
hand. As in `Check/Hand.lean`, the library's own words are put in for the signature's fields
(`Check.original`), and the kernel is asked whether each translated word and law then is the
library's declaration. Each check is `rfl`, up to unfolding definitions; a dropped guard, two
swapped arguments or a change in the order of the binders fails here, and the build with it.

This file reads the library's axioms only through `type_of%`, which takes a declaration's
statement and does not use it. Nothing in `Model/` imports this file.
-/

namespace Check

/-! ## The words -/

example : Model.Hand.Collinear original = Elements.Collinear := rfl
example : Model.Hand.IsRightAngle original = Elements.IsRightAngle := rfl

/-! ## The laws -/

example : Model.Hand.Definition15 original = type_of% @Elements.Definition15 := rfl
example : Model.Hand.Postulate4 original = type_of% @Elements.Postulate4 := rfl
example : Model.Hand.angle_symm original = type_of% @Elements.Tacit.angle_symm := rfl
example : Model.Hand.angle_le_two_right original =
    type_of% @Elements.Tacit.angle_le_two_right := rfl
example : Model.Hand.angle_eq_zero_of_same_ray original =
    type_of% @Elements.Tacit.angle_eq_zero_of_same_ray := rfl
example : Model.Hand.same_ray_of_angle_eq_zero original =
    type_of% @Elements.Tacit.same_ray_of_angle_eq_zero := rfl
example : Model.Hand.angle_add_of_inside original =
    type_of% @Elements.Tacit.angle_add_of_inside := rfl
example : Model.Hand.inside_of_angle_add original =
    type_of% @Elements.Tacit.inside_of_angle_add := rfl
example : Model.Hand.adjacent_eq_of_right original =
    type_of% @Elements.Tacit.adjacent_eq_of_right := rfl
example : Model.Hand.angle_eq_of_same_rays original =
    type_of% @Elements.Tacit.angle_eq_of_same_rays := rfl

end Check
