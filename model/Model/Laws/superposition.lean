module

public import Model.Signature

/-!
# Superposition, translated by hand

**Hand-translated, for now.** This file holds the translation of one law, the rule of
superposition (`Elements.Tacit.superposition`), and of the two defined words it reaches,
`Collinear` and `Triangle`, until the generator described in the [README](../../README.md)
writes every law from the elaborated declarations. When it lands, this file gives way to the
generated `superposition` field of `Laws`, and the generator checks that field against the
library's declaration.

The translation is the lock's statement, word for word, with `S.Point` for
`Elements.Point`, `S.OnLine` for `Elements.OnLine`, `S.len` for `Elements.len`, and so on:
the same binders, in the same order and of the same kinds, and every guard. The lock prints
the law as

```text
∀ {A B C D G H : Elements.Point} {L : Elements.Line}, Elements.Triangle A B C →
Elements.OnLine D L → Elements.OnLine G L → Ne D G → Not (Elements.OnLine H L) →
Exists fun (B' : Elements.Point) => Exists fun (C' : Elements.Point) => And
(Elements.OnLine B' L) (And (Not (Elements.Between B' D G)) (And (Elements.SameSide C' H L)
(And (Eq (Elements.len D B') (Elements.len A B)) (And (Eq (Elements.len B' C')
(Elements.len B C)) (And (Eq (Elements.len C' D) (Elements.len C A)) (And (Eq
(Elements.ang B' D C') (Elements.ang B A C)) (And (Eq (Elements.ang D C' B') (Elements.ang
A C B)) (Eq (Elements.ang C' B' D) (Elements.ang C B A)))))))))
```

and `facts.json` gives the same text as its `axiom_types` entry. `Check/Superposition.lean`
puts the library's own words in for `S` and asks the kernel whether the result is the
library's declaration; the build fails if it is not.

The words are kept in a namespace of their own, `Model.Hand.Superposition`, so that this
file can stand beside other hand translations, and beside the generated laws, without two
definitions of `Triangle` meeting.

The rule is the one we owe to LeanEuclid (Logan Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu
Li, Anima Anandkumar and Xujie Si), which joins System E's two superposition rules into one;
our thanks to them, and to Jeremy Avigad, Edward Dean and John Mumma for System E.
-/

@[expose] public section

namespace Model.Hand.Superposition

variable (S : Signature)

/-- `Elements.Collinear`, by hand. The lock prints it as `fun (A B C : Elements.Point) =>
Exists fun (L : Elements.Line) => And (Elements.OnLine A L) (And (Elements.OnLine B L)
(Elements.OnLine C L))`. -/
def Collinear (A B C : S.Point) : Prop :=
  ∃ L : S.Line, S.OnLine A L ∧ S.OnLine B L ∧ S.OnLine C L

/-- `Elements.Triangle`, by hand. The lock prints it as `fun (A B C : Elements.Point) =>
Not (Elements.Collinear A B C)`. -/
def Triangle (A B C : S.Point) : Prop :=
  ¬ Collinear S A B C

/-- `Elements.Tacit.superposition`, by hand: the triangle ABC can be laid down with A on
the point D of the line L, B on the ray from D through G, and C on the side of L where H
is, with every side and angle kept. The lock's statement is quoted in the module's
docstring. -/
def superposition : Prop :=
  ∀ {A B C D G H : S.Point} {L : S.Line}, Triangle S A B C → S.OnLine D L → S.OnLine G L →
    D ≠ G → ¬ S.OnLine H L →
    ∃ B' C' : S.Point, S.OnLine B' L ∧ ¬ S.Between B' D G ∧ S.SameSide C' H L ∧
      S.len D B' = S.len A B ∧ S.len B' C' = S.len B C ∧ S.len C' D = S.len C A ∧
      S.ang B' D C' = S.ang B A C ∧ S.ang D C' B' = S.ang A C B ∧
      S.ang C' B' D = S.ang C B A

end Model.Hand.Superposition
