module

public import Model.Signature

/-!
# The order laws, translated by hand

**Hand-translated.** This file holds, translated by hand, the fifteen laws about
betweenness and its measure: the ten statements of System E's Between rules 1 to 7
(Between 1 says four things), and the five of the diagram-segment rules 1 to 4
(Diagram-segment 4 has two directions; rule 3's forward half is Definition 15, which is
not among them). Five remain axioms and ten are now proved in the library's
`Elements/Figure/RuleBase.lean` and `Incidence.lean`, from the retained order, length
and circle rules, as the [derivation table](../../../docs/FORMALIZATION.md#rules-now-proved)
sets out. The generator described in the [README](../../README.md) writes the retained
axioms in `Model/Laws.lean`. `Check/Order.lean` compares their hand translations with
the generated laws by `rfl`, and the retired rules directly with their theorem types,
including binder kinds.

Each declaration is the library's, word for word, with `S.Point` for `Elements.Point`,
`S.Between` for `Elements.Between`, and so on. The printed original is quoted above each
law, from `Certificate/axioms.lock` for a retained axiom, or its unchanged theorem type
for a retired rule.
`Check/Order.lean` puts the library's own words in for `S` and asks Lean whether each
result is the original declaration; the build fails if it is not.

The rules are System E's diagrammatic and transfer inferences, from Jeremy Avigad, Edward
Dean and John Mumma, "A formal system for Euclid's *Elements*" (2009), sections 3.4 and
3.6, with our thanks.
-/

@[expose] public section

namespace Model

namespace Hand

variable (S : Signature)

/-! ## Between -/

/-- `Elements.Tacit.between_symm` (Between 1), hand-translated. The lock prints it as
`∀ {A B C : Elements.Point}, Elements.Between A B C → Elements.Between C B A`. -/
def between_symm : Prop :=
  ∀ {A B C : S.Point}, S.Between A B C → S.Between C B A

/-- `Elements.Tacit.ne_of_between` (Between 1), hand-translated. The theorem's unchanged type is
`∀ {A B C : Elements.Point}, Elements.Between A B C → Ne A B`. -/
def ne_of_between : Prop :=
  ∀ {A B C : S.Point}, S.Between A B C → A ≠ B

/-- `Elements.Tacit.ne_of_between_ends` (Between 1), hand-translated. The theorem's unchanged type is
`∀ {A B C : Elements.Point}, Elements.Between A B C → Ne A C`. -/
def ne_of_between_ends : Prop :=
  ∀ {A B C : S.Point}, S.Between A B C → A ≠ C

/-- `Elements.Tacit.not_between_of_between` (Between 1), hand-translated. The lock prints it
as `∀ {A B C : Elements.Point}, Elements.Between A B C → Not (Elements.Between B A C)`. -/
def not_between_of_between : Prop :=
  ∀ {A B C : S.Point}, S.Between A B C → ¬ S.Between B A C

/-- `Elements.Tacit.on_line_of_between` (Between 2), hand-translated. The theorem's unchanged type is
`∀ {A B C : Elements.Point} {L : Elements.Line}, Elements.Between A B C →
Elements.OnLine A L → Elements.OnLine B L → Elements.OnLine C L`. -/
def on_line_of_between : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, S.Between A B C → S.OnLine A L → S.OnLine B L →
    S.OnLine C L

/-- `Elements.Tacit.on_line_of_between_ends` (Between 3), hand-translated. The theorem's unchanged
type is `∀ {A B C : Elements.Point} {L : Elements.Line}, Elements.Between A B C →
Elements.OnLine A L → Elements.OnLine C L → Elements.OnLine B L`. -/
def on_line_of_between_ends : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, S.Between A B C → S.OnLine A L → S.OnLine C L →
    S.OnLine B L

/-- `Elements.Tacit.between_of_between_left` (Between 4), hand-translated. The theorem's unchanged type
is `∀ {A B C D : Elements.Point}, Elements.Between A B C → Elements.Between A D B →
Elements.Between A D C`. -/
def between_of_between_left : Prop :=
  ∀ {A B C D : S.Point}, S.Between A B C → S.Between A D B → S.Between A D C

/-- `Elements.Tacit.between_of_between_right` (Between 5), hand-translated. The theorem's unchanged type
is `∀ {A B C D : Elements.Point}, Elements.Between A B C → Elements.Between B C D →
Elements.Between A B D`. -/
def between_of_between_right : Prop :=
  ∀ {A B C D : S.Point}, S.Between A B C → S.Between B C D → S.Between A B D

/-- `Elements.Tacit.between_cases` (Between 6), hand-translated. The lock prints it as
`∀ {A B C : Elements.Point} {L : Elements.Line}, Ne A B → Ne B C → Ne A C →
Elements.OnLine A L → Elements.OnLine B L → Elements.OnLine C L → Or (Elements.Between A B C)
(Or (Elements.Between B A C) (Elements.Between A C B))`. -/
def between_cases : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, A ≠ B → B ≠ C → A ≠ C → S.OnLine A L → S.OnLine B L →
    S.OnLine C L → S.Between A B C ∨ S.Between B A C ∨ S.Between A C B

/-- `Elements.Tacit.not_between_of_between_between` (Between 7), hand-translated. The theorem's
unchanged type is `∀ {A B C D : Elements.Point}, Elements.Between A B C → Elements.Between A B D →
Not (Elements.Between C B D)`. -/
def not_between_of_between_between : Prop :=
  ∀ {A B C D : S.Point}, S.Between A B C → S.Between A B D → ¬ S.Between C B D

/-! ## Diagram-segment

Three of these laws add or compare lengths. A field of the signature writes its carrier
out, so `S.len A B` has the type `(S.MagnitudeImpl .length).type`, and Lean does not look
through the definition `S.Magnitude` to find the instances behind `+` and `<` for it. So
these three name the carrier as the library does, `S.Length`, with `@HAdd.hAdd` and
`@LT.lt`, and Lean finds the instances of `Model/Signature.lean` for it: the same
instances, at the same carrier, as the library's `‖A B‖ + ‖B C‖` and `‖A C‖ < ‖A B‖`. -/

/-- `Elements.Tacit.len_add_of_between` (Diagram-segment 1), hand-translated. The lock
prints it as `∀ {A B C : Elements.Point}, Elements.Between A B C → Eq (HAdd.hAdd
(Elements.len A B) (Elements.len B C)) (Elements.len A C)`. -/
def len_add_of_between : Prop :=
  ∀ {A B C : S.Point}, S.Between A B C →
    @HAdd.hAdd S.Length S.Length S.Length _ (S.len A B) (S.len B C) = S.len A C

/-- `Elements.Tacit.circle_eq` (Diagram-segment 2), hand-translated. The lock prints it as
`∀ {A B C : Elements.Point} {α β : Elements.Circle}, Elements.Centre A α →
Elements.Centre A β → Elements.OnCircle B α → Elements.OnCircle C β → Eq (Elements.len A B)
(Elements.len A C) → Eq α β`. -/
def circle_eq : Prop :=
  ∀ {A B C : S.Point} {α β : S.Circle}, S.Centre A α → S.Centre A β → S.OnCircle B α →
    S.OnCircle C β → S.len A B = S.len A C → α = β

/-- `Elements.Tacit.on_circle_of_len_eq` (Diagram-segment 3, the half Definition 15 does not
give), hand-translated. The theorem's unchanged type is `∀ {A B C : Elements.Point}
{α : Elements.Circle}, Elements.Centre A α → Elements.OnCircle B α → Eq (Elements.len A C)
(Elements.len A B) → Elements.OnCircle C α`. -/
def on_circle_of_len_eq : Prop :=
  ∀ {A B C : S.Point} {α : S.Circle}, S.Centre A α → S.OnCircle B α →
    S.len A C = S.len A B → S.OnCircle C α

/-- `Elements.Tacit.inside_of_len_lt` (Diagram-segment 4), hand-translated. The theorem's unchanged type
is `∀ {A B C : Elements.Point} {α : Elements.Circle}, Elements.Centre A α →
Elements.OnCircle B α → LT.lt (Elements.len A C) (Elements.len A B) →
Elements.InsideCircle C α`. -/
def inside_of_len_lt : Prop :=
  ∀ {A B C : S.Point} {α : S.Circle}, S.Centre A α → S.OnCircle B α →
    @LT.lt S.Length _ (S.len A C) (S.len A B) → S.InsideCircle C α

/-- `Elements.Tacit.len_lt_of_inside` (Diagram-segment 4), hand-translated. The theorem's unchanged type
is `∀ {A B C : Elements.Point} {α : Elements.Circle}, Elements.Centre A α →
Elements.OnCircle B α → Elements.InsideCircle C α → LT.lt (Elements.len A C)
(Elements.len A B)`. -/
def len_lt_of_inside : Prop :=
  ∀ {A B C : S.Point} {α : S.Circle}, S.Centre A α → S.OnCircle B α →
    S.InsideCircle C α → @LT.lt S.Length _ (S.len A C) (S.len A B)

end Hand

end Model
