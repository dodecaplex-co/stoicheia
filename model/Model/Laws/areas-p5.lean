module

public import Model.Signature

/-!
# Areas and Postulate 5, translated by hand

**This file is written by hand.** Like [Model/Hand.lean](../Hand.lean), it holds laws
translated by hand from `Certificate/axioms.lock`. The generator described in the
[README](../../README.md) writes every law from its elaborated declaration, and
`Check/AreasP5.lean` compares each statement here with its generated field.

Each declaration is the library's, word for word, with `S.Point` for `Elements.Point`,
`S.area` for `Elements.area`, and so on, and keeps the original's binders, their kinds and
their order. The lock's printed statement is quoted above each law. `Check/AreasP5.lean`
puts the library's own words in for `S` and asks Lean whether each result is the original
declaration; the build fails if it is not.

The laws here are the eight rules about area, from `Tacit/Metric.lean` and
`Tacit/Transfer.lean`, and Postulate 5, with its conclusion on the stated side. None of them
reaches a defined word of the library beyond the magnitude instances of
`Model/Signature.lean`. Where a law adds two areas or two angles, the sum is written
`@HAdd.hAdd S.Area S.Area S.Area _ a b`, naming the carrier: a field such as `S.area` has
the unfolded type `(S.MagnitudeImpl .area).type`, on which Lean does not look for the
instance of `S.Area`, and this is the form the library's own `a + b` elaborates to.
-/

@[expose] public section

namespace Model

namespace Hand

variable (S : Signature)

/-! ## Areas -/

/-- `Elements.Tacit.area_degenerate` (Metric 6), by hand. The lock prints it as
`∀ (A B : Elements.Point), Eq (Elements.area A A B) 0`. -/
def area_degenerate : Prop :=
  ∀ (A B : S.Point), S.area A A B = (0 : S.Area)

/-- `Elements.Tacit.area_rotate` (Metric 8), by hand. The lock prints it as
`∀ (A B C : Elements.Point), Eq (Elements.area A B C) (Elements.area C A B)`. -/
def area_rotate : Prop :=
  ∀ (A B C : S.Point), S.area A B C = S.area C A B

/-- `Elements.Tacit.area_swap` (Metric 8), by hand. The lock prints it as
`∀ (A B C : Elements.Point), Eq (Elements.area A B C) (Elements.area A C B)`. -/
def area_swap : Prop :=
  ∀ (A B C : S.Point), S.area A B C = S.area A C B

/-- `Elements.Tacit.area_congruent` (Metric 9), by hand. The lock prints it as
`∀ {A B C D E F : Elements.Point}, Eq (Elements.len A B) (Elements.len D E) →
Eq (Elements.len B C) (Elements.len E F) → Eq (Elements.len C A) (Elements.len F D) →
Eq (Elements.ang A B C) (Elements.ang D E F) → Eq (Elements.ang B C A) (Elements.ang E F D) →
Eq (Elements.ang C A B) (Elements.ang F D E) → Eq (Elements.area A B C) (Elements.area D E F)`.
-/
def area_congruent : Prop :=
  ∀ {A B C D E F : S.Point}, S.len A B = S.len D E → S.len B C = S.len E F →
    S.len C A = S.len F D → S.ang A B C = S.ang D E F → S.ang B C A = S.ang E F D →
    S.ang C A B = S.ang F D E → S.area A B C = S.area D E F

/-- `Elements.Tacit.area_eq_zero_of_on_line` (Diagram-area 1), by hand. The lock prints it
as `∀ {A B C : Elements.Point} {L : Elements.Line}, Elements.OnLine A L →
Elements.OnLine B L → Ne A B → Elements.OnLine C L → Eq (Elements.area A B C) 0`. -/
def area_eq_zero_of_on_line : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, S.OnLine A L → S.OnLine B L → A ≠ B → S.OnLine C L →
    S.area A B C = (0 : S.Area)

/-- `Elements.Tacit.on_line_of_area_eq_zero` (Diagram-area 1), by hand. The lock prints it
as `∀ {A B C : Elements.Point} {L : Elements.Line}, Elements.OnLine A L →
Elements.OnLine B L → Ne A B → Eq (Elements.area A B C) 0 → Elements.OnLine C L`. -/
def on_line_of_area_eq_zero : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, S.OnLine A L → S.OnLine B L → A ≠ B →
    S.area A B C = (0 : S.Area) → S.OnLine C L

/-- `Elements.Tacit.area_add_of_between` (Diagram-area 2), by hand. The lock prints it as
`∀ {A B C D : Elements.Point} {L : Elements.Line}, Elements.OnLine A L →
Elements.OnLine B L → Elements.OnLine C L → Ne A B → Ne A C → Ne B C →
Not (Elements.OnLine D L) → Elements.Between A C B → Eq (HAdd.hAdd (Elements.area A C D)
(Elements.area D C B)) (Elements.area A D B)`. -/
def area_add_of_between : Prop :=
  ∀ {A B C D : S.Point} {L : S.Line}, S.OnLine A L → S.OnLine B L → S.OnLine C L →
    A ≠ B → A ≠ C → B ≠ C → ¬ S.OnLine D L → S.Between A C B →
    @HAdd.hAdd S.Area S.Area S.Area _ (S.area A C D) (S.area D C B) = S.area A D B

/-- `Elements.Tacit.between_of_area_add` (Diagram-area 2, converse), by hand. The lock
prints it as `∀ {A B C D : Elements.Point} {L : Elements.Line}, Elements.OnLine A L →
Elements.OnLine B L → Elements.OnLine C L → Ne A B → Ne A C → Ne B C →
Not (Elements.OnLine D L) → Eq (HAdd.hAdd (Elements.area A C D) (Elements.area D C B))
(Elements.area A D B) → Elements.Between A C B`. -/
def between_of_area_add : Prop :=
  ∀ {A B C D : S.Point} {L : S.Line}, S.OnLine A L → S.OnLine B L → S.OnLine C L →
    A ≠ B → A ≠ C → B ≠ C → ¬ S.OnLine D L →
    @HAdd.hAdd S.Area S.Area S.Area _ (S.area A C D) (S.area D C B) = S.area A D B →
    S.Between A C B

/-! ## Postulate 5 -/

/-- `Elements.Postulate5`, by hand. The lock prints it as
`∀ {A B C D : Elements.Point} {L M N : Elements.Line}, Elements.OnLine A L →
Elements.OnLine B L → Elements.OnLine B M → Elements.OnLine C M → Elements.OnLine C N →
Elements.OnLine D N → Ne B C → Elements.SameSide A D M → LT.lt (HAdd.hAdd (Elements.ang A B C)
(Elements.ang B C D)) (HAdd.hAdd Elements.rightAngle Elements.rightAngle) →
Exists fun (E : Elements.Point) => And (Elements.OnLine E L) (And (Elements.OnLine E N)
(Elements.SameSide E A M))`. -/
def Postulate5 : Prop :=
  ∀ {A B C D : S.Point} {L M N : S.Line}, S.OnLine A L → S.OnLine B L → S.OnLine B M →
    S.OnLine C M → S.OnLine C N → S.OnLine D N → B ≠ C → S.SameSide A D M →
    @HAdd.hAdd S.Angle S.Angle S.Angle _ (S.ang A B C) (S.ang B C D) <
      @HAdd.hAdd S.Angle S.Angle S.Angle _ S.rightAngle S.rightAngle →
    ∃ E : S.Point, S.OnLine E L ∧ S.OnLine E N ∧ S.SameSide E A M

end Hand

end Model
