module

public import Model.Signature

/-!
# The metric length laws, translated by hand

Each statement retains its original binders and guards. `len_self` and `len_symm`
remain axioms in `Certificate/axioms.lock`; `eq_of_len_eq_zero` is now proved in
`Elements/Figure/RuleBase.lean` from Postulate 3 and the proved circle rules: distinct
points at no distance would put a circle's centre on its circumference.
`Check/Lengths.lean` compares the hand translations with the original declarations,
the retained axioms with the generated laws, and the retired rule directly with its
theorem type, including binder kinds.
-/

@[expose] public section

namespace Model.Hand

variable (S : Signature)

/-- `Elements.Tacit.eq_of_len_eq_zero` (Metric 1), hand-translated. The theorem's unchanged type is
`∀ {A B : Elements.Point}, Eq (Elements.len A B) 0 → Eq A B`. -/
def eq_of_len_eq_zero : Prop :=
  ∀ {A B : S.Point}, S.len A B = (0 : S.Length) → A = B

/-- `Elements.Tacit.len_self` (Metric 1), hand-translated. The lock prints it as
`∀ (A : Elements.Point), Eq (Elements.len A A) 0`. -/
def len_self : Prop :=
  ∀ (A : S.Point), S.len A A = (0 : S.Length)

/-- `Elements.Tacit.len_symm` (Metric 3), hand-translated. The lock prints it as
`∀ (A B : Elements.Point), Eq (Elements.len A B) (Elements.len B A)`. -/
def len_symm : Prop :=
  ∀ (A B : S.Point), S.len A B = S.len B A

end Model.Hand
