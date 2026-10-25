import Elements.Figure.Basics
import Elements.Figure.Circles
import Check.Hand
import Check.Generator
import Model.Laws.sides

/-!
# Checking the hand translation of the side rules against the library

`Model/Laws/sides.lean` translates the five same-side rules, four Pasch rules and three
triple-incidence rules by hand. As in `Check/Hand.lean`, the library's own words are put
in for the signature's fields (`Check.original`), and Lean is asked whether each translated
law then is the library's declaration, read through `type_of%`, which takes a declaration's statement and
does not use it. Each check is `rfl`; a dropped guard, two swapped arguments or a change in
the order of the binders fails it, and the build with it.

The kernel comparisons read the library's declarations through `type_of%`. For
`triple_incidence3`, `comparePlanted` also translates the hand definition back and
compares it directly with the declaration's type, including binder kinds. Both checks
read only the statement, whether it is an axiom or a theorem.
Nothing in `Model/` imports this file.
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

example : Model.Hand.triple_incidence1 original =
    type_of% @Elements.Tacit.triple_incidence1 := rfl
example : Model.Hand.triple_incidence2 original =
    type_of% @Elements.Tacit.triple_incidence2 := rfl
example : Model.Hand.triple_incidence3 original =
    type_of% @Elements.Tacit.triple_incidence3 := rfl

/-! ## The hand translations against generated laws or declaration types -/

run_cmd (Check.Generator.comparePlanted ``Model.Hand.same_side_refl
  ``Elements.Tacit.same_side_refl)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.same_side_symm
  ``Elements.Tacit.same_side_symm)
example (S : Model.Signature) : Model.Hand.not_on_line_of_same_side S =
    Model.Law.Tacit.not_on_line_of_same_side S := rfl
example (S : Model.Signature) : Model.Hand.same_side_trans S =
    Model.Law.Tacit.same_side_trans S := rfl
run_cmd (Check.Generator.comparePlanted ``Model.Hand.same_side_or
  ``Elements.Tacit.same_side_or)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.pasch1
  ``Elements.Tacit.pasch1)
example (S : Model.Signature) : Model.Hand.pasch2 S =
    Model.Law.Tacit.pasch2 S := rfl
run_cmd (Check.Generator.comparePlanted ``Model.Hand.pasch3
  ``Elements.Tacit.pasch3)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.pasch4
  ``Elements.Tacit.pasch4)

run_cmd (Check.Generator.comparePlanted ``Model.Hand.triple_incidence1
  ``Elements.Tacit.triple_incidence1)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.triple_incidence2
  ``Elements.Tacit.triple_incidence2)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.triple_incidence3
  ``Elements.Tacit.triple_incidence3)

end Check
