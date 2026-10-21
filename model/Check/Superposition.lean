import Elements.Foundations.Tacit.Superposition
import Check.Hand
import Model.Laws.superposition

/-!
# Checking the hand translation of superposition against the library

`Model/Laws/superposition.lean` translates the rule of superposition, and its primitive interpretation
by hand. Here the library's own words are put in for the signature's
fields (`Check.original`, from `Check/Hand.lean`), and the kernel is asked whether each
result is the library's declaration. Each check is `rfl`, so a dropped guard, two swapped
arguments or a change in the order of the binders fails here, and the build with it.

This file reads the axiom only through `type_of%`, which takes a declaration's statement and
does not use it. Nothing in `Model/` imports this file.
-/

namespace Check

example : Model.Hand.Superposition.Collinear original = Elements.Collinear := rfl
example : Model.Hand.Superposition.Triangle original = Elements.Triangle := rfl

example : Model.Hand.Superposition.primitives original = Elements.primitives := rfl

example : Model.Hand.Superposition.superposition original =
    type_of% @Elements.Tacit.superposition := rfl

example (S : Model.Signature) : Model.Hand.Superposition.Collinear S = S.Collinear := rfl
example (S : Model.Signature) : Model.Hand.Superposition.Triangle S =
    Elements.Superposition.Triangle S.primitives := rfl

/-! ## The hand translations against the generated laws -/

example (S : Model.Signature) : Model.Hand.Superposition.primitives S = S.primitives := rfl

example (S : Model.Signature) : Model.Hand.Superposition.superposition S =
    Model.Law.Tacit.superposition S := rfl

end Check
