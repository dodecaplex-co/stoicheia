import Check.Hand
import Model.Laws.sides

/-!
# Checking the hand translation of the side rules against the library

`Model/Laws/sides.lean` translates the five same-side rules and the four Pasch rules by
hand. As in `Check/Hand.lean`, the library's own words are put in for the signature's
fields (`Check.original`), and Lean is asked whether each translated law then is the
library's declaration, read through `type_of%`, which takes a declaration's statement and
does not use it. Each check is `rfl`; a dropped guard, two swapped arguments or a change in
the order of the binders fails it, and the build with it.
-/

namespace Check

example : Model.Hand.same_side_refl original = type_of% @Elements.Tacit.same_side_refl := rfl

example : Model.Hand.same_side_symm original = type_of% @Elements.Tacit.same_side_symm := rfl

example : Model.Hand.not_on_line_of_same_side original =
    type_of% @Elements.Tacit.not_on_line_of_same_side := rfl

example : Model.Hand.same_side_trans original = type_of% @Elements.Tacit.same_side_trans :=
  rfl

example : Model.Hand.same_side_or original = type_of% @Elements.Tacit.same_side_or := rfl

example : Model.Hand.pasch1 original = type_of% @Elements.Tacit.pasch1 := rfl

example : Model.Hand.pasch2 original = type_of% @Elements.Tacit.pasch2 := rfl

example : Model.Hand.pasch3 original = type_of% @Elements.Tacit.pasch3 := rfl

example : Model.Hand.pasch4 original = type_of% @Elements.Tacit.pasch4 := rfl

end Check
