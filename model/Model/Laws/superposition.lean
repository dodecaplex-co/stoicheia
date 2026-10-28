module

public import Model.Signature
public import Elements.Foundations.Superposition.Semantics

/-!
# Superposition, translated by hand

The law is the generic restricted `Elements.Superposition.Rule` applied to an
interpretation built from the signature. Only the four pure calculus modules may be
shared with the library. They define symbols, derivations and their semantics, and
assume no geometry. `Check/Generator.lean` audits their transitive dependencies and
translates them by identity, preserving universe arguments.

`Check/Superposition.lean` checks the interpretation and the law by `rfl`, both against
the library under `Check.original` and against the generated definitions. The explicit
placement proposition below is supporting mathematics, not a field of `Laws`.
`Rule.of_placement_of_join` reduces the restricted law to that placement, Same side 3's
form and Postulate 1's, deriving the side before `Rule.of_placement` finishes the proof.

The combined placement follows LeanEuclid, by Logan Murphy, Kaiyu Yang, Jialiang Sun,
Zhaoyu Li, Anima Anandkumar and Xujie Si, with thanks. The restriction follows the style
of System E, by Jeremy Avigad, Edward Dean and John Mumma. Equivalence with its two-rule
presentation is not claimed.
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

/-- The primitive words of the signature, interpreted by the shared calculus. -/
def primitives : Elements.Superposition.Interpretation where
  Point := S.Point
  Line := S.Line
  OnLine := S.OnLine
  Between := S.Between
  SameSide := S.SameSide
  Length := S.Length
  Angle := S.Angle
  Area := S.Area
  len := S.len
  ang := S.ang
  area := S.area

/-- `Elements.Tacit.superposition`, by hand: a restricted inference of metric equalities
about the given figure from a hypothetical placement. -/
def superposition : Prop :=
  Elements.Superposition.Rule (primitives S)

/-- Supporting placement mathematics: lay ABC on the ray DG, on H's side of L,
keeping all three sides and angles. This existential is not the superposition law. -/
def placement : Prop :=
  ∀ {A B C D G H : S.Point} {L : S.Line}, Triangle S A B C → S.OnLine D L → S.OnLine G L →
    D ≠ G → ¬ S.OnLine H L →
    ∃ B' C' : S.Point, S.OnLine B' L ∧ ¬ S.Between B' D G ∧ S.SameSide C' H L ∧
      S.len D B' = S.len A B ∧ S.len B' C' = S.len B C ∧ S.len C' D = S.len C A ∧
      S.ang B' D C' = S.ang B A C ∧ S.ang D C' B' = S.ang A C B ∧
      S.ang C' B' D = S.ang C B A

end Model.Hand.Superposition
