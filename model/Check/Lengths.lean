import Elements.Foundations.Tacit.Metric
import Check.Hand
import Model.Laws.lengths

/-!
# Checking the hand translations of the metric length laws

The kernel compares each translation with the original declaration, read through
`type_of%`, and with the generated law over every signature. Nothing under `Model/`
imports this file.
-/

namespace Check

example : Model.Hand.eq_of_len_eq_zero original =
    type_of% @Elements.Tacit.eq_of_len_eq_zero := rfl
example : Model.Hand.len_self original = type_of% @Elements.Tacit.len_self := rfl
example : Model.Hand.len_symm original = type_of% @Elements.Tacit.len_symm := rfl

example (S : Model.Signature) : Model.Hand.eq_of_len_eq_zero S =
    Model.Law.Tacit.eq_of_len_eq_zero S := rfl
example (S : Model.Signature) : Model.Hand.len_self S = Model.Law.Tacit.len_self S := rfl
example (S : Model.Signature) : Model.Hand.len_symm S = Model.Law.Tacit.len_symm S := rfl

end Check
