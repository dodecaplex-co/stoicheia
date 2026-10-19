module

public import Model.Signature

/-!
# The same-side rules and Pasch's rules, translated by hand

**This file is written by hand, and so is every translation in it.** It holds, for now, the
translations of the five same-side rules and the four Pasch rules of
`Elements/Foundations/Tacit/Diagram.lean`, until the generator described in the
[README](../../README.md) writes every law from the elaborated declarations; the generator
will then check each translation here against the field it writes, and replace this file.

Each law is the library's, word for word, with `S.Point` for `Elements.Point`, `S.OnLine`
for `Elements.OnLine`, `S.SameSide` for `Elements.SameSide`, `S.Between` for
`Elements.Between`, and `S.Line` for `Elements.Line`, keeping every binder, its kind
(all are implicit) and its order, and every guard. The printed original is quoted above
each law, from `Certificate/axioms.lock` (the same text as `axiom_types` in `facts.json`).
`Check/Sides.lean` puts the library's own words in for `S` and asks Lean whether each
result is the original declaration; the build fails if it is not.

The rules come from System E, the diagrammatic system of Jeremy Avigad, Edward Dean and
John Mumma, with our thanks; the numbering (Same side 1 to 5, Pasch 1 to 4) is theirs and
the library's.
-/

@[expose] public section

namespace Model

namespace Hand

variable (S : Signature)

/-! ## Same side -/

/-- `Elements.Tacit.same_side_refl` (Same side 1), translated by hand. The lock prints it as
`∀ {A : Elements.Point} {L : Elements.Line}, Not (Elements.OnLine A L) →
Elements.SameSide A A L`. -/
def same_side_refl : Prop :=
  ∀ {A : S.Point} {L : S.Line}, ¬ S.OnLine A L → S.SameSide A A L

/-- `Elements.Tacit.same_side_symm` (Same side 2), translated by hand. The lock prints it as
`∀ {A B : Elements.Point} {L : Elements.Line}, Elements.SameSide A B L →
Elements.SameSide B A L`. -/
def same_side_symm : Prop :=
  ∀ {A B : S.Point} {L : S.Line}, S.SameSide A B L → S.SameSide B A L

/-- `Elements.Tacit.not_on_line_of_same_side` (Same side 3), translated by hand. The lock
prints it as `∀ {A B : Elements.Point} {L : Elements.Line}, Elements.SameSide A B L →
Not (Elements.OnLine A L)`. -/
def not_on_line_of_same_side : Prop :=
  ∀ {A B : S.Point} {L : S.Line}, S.SameSide A B L → ¬ S.OnLine A L

/-- `Elements.Tacit.same_side_trans` (Same side 4), translated by hand. The lock prints it
as `∀ {A B C : Elements.Point} {L : Elements.Line}, Elements.SameSide A B L →
Elements.SameSide A C L → Elements.SameSide B C L`. -/
def same_side_trans : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, S.SameSide A B L → S.SameSide A C L → S.SameSide B C L

/-- `Elements.Tacit.same_side_or` (Same side 5), translated by hand. The lock prints it as
`∀ {A B C : Elements.Point} {L : Elements.Line}, Not (Elements.OnLine A L) →
Not (Elements.OnLine B L) → Not (Elements.OnLine C L) → Not (Elements.SameSide A B L) →
Or (Elements.SameSide A C L) (Elements.SameSide B C L)`. -/
def same_side_or : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, ¬ S.OnLine A L → ¬ S.OnLine B L → ¬ S.OnLine C L →
    ¬ S.SameSide A B L → S.SameSide A C L ∨ S.SameSide B C L

/-! ## Pasch -/

/-- `Elements.Tacit.pasch1` (Pasch 1), translated by hand. The lock prints it as
`∀ {A B C : Elements.Point} {L : Elements.Line}, Elements.Between A B C →
Elements.SameSide A C L → Elements.SameSide A B L`. -/
def pasch1 : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, S.Between A B C → S.SameSide A C L → S.SameSide A B L

/-- `Elements.Tacit.pasch2` (Pasch 2), translated by hand. The lock prints it as
`∀ {A B C : Elements.Point} {L : Elements.Line}, Elements.Between A B C →
Elements.OnLine A L → Not (Elements.OnLine B L) → Elements.SameSide B C L`. -/
def pasch2 : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, S.Between A B C → S.OnLine A L → ¬ S.OnLine B L →
    S.SameSide B C L

/-- `Elements.Tacit.pasch3` (Pasch 3), translated by hand. The lock prints it as
`∀ {A B C : Elements.Point} {L : Elements.Line}, Elements.Between A B C →
Elements.OnLine B L → Not (Elements.SameSide A C L)`. -/
def pasch3 : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, S.Between A B C → S.OnLine B L → ¬ S.SameSide A C L

/-- `Elements.Tacit.pasch4` (Pasch 4), translated by hand. The lock prints it as
`∀ {A B C : Elements.Point} {L M : Elements.Line}, Ne L M → Elements.OnLine B L →
Elements.OnLine B M → Elements.OnLine A M → Elements.OnLine C M → Ne A C → Ne A B →
Ne C B → Not (Elements.SameSide A C L) → Elements.Between A B C`. -/
def pasch4 : Prop :=
  ∀ {A B C : S.Point} {L M : S.Line}, L ≠ M → S.OnLine B L → S.OnLine B M → S.OnLine A M →
    S.OnLine C M → A ≠ C → A ≠ B → C ≠ B → ¬ S.SameSide A C L → S.Between A B C

end Hand

end Model
