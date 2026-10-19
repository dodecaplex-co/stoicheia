import Elements.Foundations.Tacit.Diagram
import Elements.Foundations.Tacit.Transfer
import Check.Hand
import Model.Laws.order

/-!
# Checking the hand-translated order laws against the library

`Model/Laws/order.lean` translates the fifteen order laws by hand: Between 1 to 7 and the
diagram-segment rules. Here, as in `Check/Hand.lean`, the library's own words are put in for
the signature's fields (`Check.original`), and Lean is asked whether each translated law then
is the library's declaration. Each check is `rfl`: the kernel accepts it only if the two are
the same proposition, up to unfolding definitions, so a dropped guard, two swapped arguments
or a change in the order of the binders fails here, and the build with it.

This file reads the library's axioms only through `type_of%`, which takes a declaration's
statement and does not use it. Nothing in `Model/` imports this file.
-/

namespace Check

/-! ## Between -/

example : Model.Hand.between_symm original = type_of% @Elements.Tacit.between_symm := rfl

example : Model.Hand.ne_of_between original = type_of% @Elements.Tacit.ne_of_between := rfl

example : Model.Hand.ne_of_between_ends original =
    type_of% @Elements.Tacit.ne_of_between_ends := rfl

example : Model.Hand.not_between_of_between original =
    type_of% @Elements.Tacit.not_between_of_between := rfl

example : Model.Hand.on_line_of_between original =
    type_of% @Elements.Tacit.on_line_of_between := rfl

example : Model.Hand.on_line_of_between_ends original =
    type_of% @Elements.Tacit.on_line_of_between_ends := rfl

example : Model.Hand.between_of_between_left original =
    type_of% @Elements.Tacit.between_of_between_left := rfl

example : Model.Hand.between_of_between_right original =
    type_of% @Elements.Tacit.between_of_between_right := rfl

example : Model.Hand.between_cases original = type_of% @Elements.Tacit.between_cases := rfl

example : Model.Hand.not_between_of_between_between original =
    type_of% @Elements.Tacit.not_between_of_between_between := rfl

/-! ## Diagram-segment -/

example : Model.Hand.len_add_of_between original =
    type_of% @Elements.Tacit.len_add_of_between := rfl

example : Model.Hand.circle_eq original = type_of% @Elements.Tacit.circle_eq := rfl

example : Model.Hand.on_circle_of_len_eq original =
    type_of% @Elements.Tacit.on_circle_of_len_eq := rfl

example : Model.Hand.inside_of_len_lt original = type_of% @Elements.Tacit.inside_of_len_lt :=
  rfl

example : Model.Hand.len_lt_of_inside original = type_of% @Elements.Tacit.len_lt_of_inside :=
  rfl

/-! ## The hand translations against the generated laws -/

example (S : Model.Signature) : Model.Hand.between_symm S =
    Model.Law.Tacit.between_symm S := rfl
example (S : Model.Signature) : Model.Hand.ne_of_between S =
    Model.Law.Tacit.ne_of_between S := rfl
example (S : Model.Signature) : Model.Hand.ne_of_between_ends S =
    Model.Law.Tacit.ne_of_between_ends S := rfl
example (S : Model.Signature) : Model.Hand.not_between_of_between S =
    Model.Law.Tacit.not_between_of_between S := rfl
example (S : Model.Signature) : Model.Hand.on_line_of_between S =
    Model.Law.Tacit.on_line_of_between S := rfl
example (S : Model.Signature) : Model.Hand.on_line_of_between_ends S =
    Model.Law.Tacit.on_line_of_between_ends S := rfl
example (S : Model.Signature) : Model.Hand.between_of_between_left S =
    Model.Law.Tacit.between_of_between_left S := rfl
example (S : Model.Signature) : Model.Hand.between_of_between_right S =
    Model.Law.Tacit.between_of_between_right S := rfl
example (S : Model.Signature) : Model.Hand.between_cases S =
    Model.Law.Tacit.between_cases S := rfl
example (S : Model.Signature) : Model.Hand.not_between_of_between_between S =
    Model.Law.Tacit.not_between_of_between_between S := rfl
example (S : Model.Signature) : Model.Hand.len_add_of_between S =
    Model.Law.Tacit.len_add_of_between S := rfl
example (S : Model.Signature) : Model.Hand.circle_eq S =
    Model.Law.Tacit.circle_eq S := rfl
example (S : Model.Signature) : Model.Hand.on_circle_of_len_eq S =
    Model.Law.Tacit.on_circle_of_len_eq S := rfl
example (S : Model.Signature) : Model.Hand.inside_of_len_lt S =
    Model.Law.Tacit.inside_of_len_lt S := rfl
example (S : Model.Signature) : Model.Hand.len_lt_of_inside S =
    Model.Law.Tacit.len_lt_of_inside S := rfl

end Check
