import Elements.Foundations.Superposition.Syntax

/-!
# Superposition, restricted: interpretation and rule

The restricted rule of superposition, interpreted in any meanings of the primitive words,
as a hypothesis `Rule I` ([brief 0009](../../../docs/briefs/0009-superposition.md)).

System E writes the rule as a sequent inference (Avigad, Dean and Mumma, 2009, §3.7). We read
it so: if the facts Γ, with the facts Π of a triangle laid down, prove Δ′, then Γ proves Δ′,
where Δ′ speaks only of the objects Γ already has. Ours is that inference over a finite
symbolic context:

* **The figure's symbols.** The given facts Γ are literals over the symbols `Fin n` for
  points and `Fin m` for straight lines; a valuation `v` says which point and which straight
  line each symbol stands for, and the rule asks that Γ hold under it.
* **The placement's symbols** (`Name`, `LineName`). Laid down with A on D, the triangle ABC
  becomes D B′ C′, its side AC a straight line through D and C′. The placement adds exactly
  three symbols to the figure's: `Name.second` (B′), `Name.third` (C′) and `LineName.side`
  (the side AC laid down). They are fresh by their type: no symbol of the figure is one of
  them, and no valuation of the figure gives them a point or a straight line.
* **The guards.** The triangle ABC is a triangle; D and G are two points of the straight line
  L, so the ray from D through G has a direction; H is off L, so it has a side. Those that are
  literals are available in the placement (`guards`).
* **What the placement keeps** (`kept`). B′ is on the ray from D through G, C′ is on H's side
  of L, and each side and each angle is kept.
  And the side AC, laid down, is a straight line through D and C′: Euclid's "the straight
  line AC" of I.4, as it falls.
* **What it exports.** One equality of lengths, angles or triangles over the figure's
  symbols, a `Metric (Fin n)`, which can name no symbol of the placement.
* **What it assumes.** Nothing about lengths, angles, areas or rays: a derivation cites the
  laws it uses (`Cited`), and the rule asks each of them to hold.

The derivation comes before the valuation in the rule's statement: one derivation, over
symbols, gives the conclusion for every figure that satisfies the guards and the given facts.

`Symbols` lets a proof name its symbols with an inductive type of its own (`Rule.apply`);
`Rule.of_placement` shows that wherever triangles can be laid down, with the side AC drawn,
the restricted rule holds, by logic alone.
-/

namespace Elements.Superposition

/-- **An interpretation of the primitive words.** It gives their types and meanings, with
no law of geometry assumed. -/
structure Interpretation where
  /-- The points. -/
  Point : Type
  /-- The straight lines. -/
  Line : Type
  /-- A point lying on a straight line. -/
  OnLine : Point → Line → Prop
  /-- The middle point lying between the other two. -/
  Between : Point → Point → Point → Prop
  /-- Two points lying on the same side of a straight line. -/
  SameSide : Point → Point → Line → Prop
  /-- The lengths. -/
  Length : Type
  /-- The angles. -/
  Angle : Type
  /-- The areas. -/
  Area : Type
  /-- The length between two points. -/
  len : Point → Point → Length
  /-- The angle at the middle of three points. -/
  ang : Point → Point → Point → Angle
  /-- The area of a triangle. -/
  area : Point → Point → Point → Area

/-- **A valuation**: the point each point symbol stands for, and the straight line each line
symbol stands for. The symbols are data; the valuation is the figure. -/
structure Val (I : Interpretation) (P L : Type) where
  /-- The point a point symbol stands for. -/
  pt : P → I.Point
  /-- The straight line a line symbol stands for. -/
  line : L → I.Line

variable {I : Interpretation}

namespace Val

variable {P L P' L' : Type}

/-- The valuation read through renamings `f` and `g` of the symbols: the symbol `p` stands
for what `f p` stands for. -/
def comap (v : Val I P' L') (f : P → P') (g : L → L') : Val I P L := ⟨v.pt ∘ f, v.line ∘ g⟩

end Val

namespace Atom

variable {P L : Type}

/-- What the atom says of the figure, once each symbol stands for what `v` gives it. -/
def Holds (v : Val I P L) : Atom P L → Prop
  | eq p q => v.pt p = v.pt q
  | onLine p l => I.OnLine (v.pt p) (v.line l)
  | between p q r => I.Between (v.pt p) (v.pt q) (v.pt r)
  | sameSide p q l => I.SameSide (v.pt p) (v.pt q) (v.line l)
  | len p q r s => I.len (v.pt p) (v.pt q) = I.len (v.pt r) (v.pt s)
  | angle p q r s t u => I.ang (v.pt p) (v.pt q) (v.pt r) = I.ang (v.pt s) (v.pt t) (v.pt u)
  | area p q r s t u => I.area (v.pt p) (v.pt q) (v.pt r) = I.area (v.pt s) (v.pt t) (v.pt u)

end Atom

namespace Lit

variable {P L : Type}

/-- What the literal says of the figure, once each symbol stands for what `v` gives it. -/
def Holds (v : Val I P L) : Lit P L → Prop
  | pos a => a.Holds v
  | neg a => ¬ a.Holds v

end Lit

namespace Metric

variable {P L : Type}

/-- What the metric formula says of the figure, once each symbol stands for what `v` gives
it. -/
def Holds (v : Val I P L) (m : Metric P) : Prop := (m.toAtom : Atom P L).Holds v

end Metric

/-- What a law asserts: whatever points and straight lines its letters stand for, if its
premises hold, its conclusion holds. -/
def Law.Holds (I : Interpretation) (law : Law) : Prop :=
  ∀ v : Val I Letter LineLetter, (∀ ℓ ∈ law.premises, ℓ.Holds v) → law.conclusion.Holds v

/-- What a cited law asserts. -/
def Cited.Holds (I : Interpretation) (c : Cited) : Prop := c.law.Holds I

/-- A straight line passes through all three points. -/
def Collinear (I : Interpretation) (A B C : I.Point) : Prop :=
  ∃ L : I.Line, I.OnLine A L ∧ I.OnLine B L ∧ I.OnLine C L

/-- The three points do not lie on one straight line. -/
def Triangle (I : Interpretation) (A B C : I.Point) : Prop := ¬ Collinear I A B C

/-- The triangle ABC, laid down with A on D, is D B′ C′, with B′ on the ray from D through G
and C′ on H's side of L, its sides and angles kept. -/
def Placed (I : Interpretation) (A B C D G H : I.Point) (L : I.Line) (B' C' : I.Point) : Prop :=
  I.OnLine B' L ∧ ¬ I.Between B' D G ∧ I.SameSide C' H L ∧
    I.len D B' = I.len A B ∧ I.len B' C' = I.len B C ∧ I.len C' D = I.len C A ∧
    I.ang B' D C' = I.ang B A C ∧ I.ang D C' B' = I.ang A C B ∧ I.ang C' B' D = I.ang C B A

open Lit

/-- **The restricted rule of superposition**, as a hypothesis. For a triangle abc, a ray from
d through g along the straight line l, and a point h off l, all symbols of the figure: an
equality of lengths, angles or triangles over the figure's symbols that a restricted
derivation proves from the given facts Γ, the guards and what the placement keeps, holds in
every figure that satisfies the guards and Γ. A derivation may cite the laws listed in
`cites`, once they hold.

The placement's symbols are symbols of the derivation and nowhere else: the conclusion is a
`Metric (Fin n)`, which names only the figure's symbols, and the valuation `v` gives a point
and a straight line to the figure's symbols only. -/
structure Rule (I : Interpretation) : Prop where
  /-- Use the rule: lay abc down on the ray from d through g, on h's side, and keep what a
  restricted derivation proves of the figure. -/
  infer : ∀ {cites : List Cited}, (∀ c ∈ cites, c.Holds I) →
    ∀ {n m : Nat} {Γ : List (Lit (Fin n) (Fin m))} {a b c d g h : Fin n} {l : Fin m}
      {φ : Metric (Fin n)},
      Derives cites (branch Γ a b c d g h l) (pos (φ.map Name.given).toAtom) →
      ∀ v : Val I (Fin n) (Fin m), Triangle I (v.pt a) (v.pt b) (v.pt c) →
        I.OnLine (v.pt d) (v.line l) → I.OnLine (v.pt g) (v.line l) → v.pt d ≠ v.pt g →
        ¬ I.OnLine (v.pt h) (v.line l) → (∀ ℓ ∈ Γ, ℓ.Holds v) → φ.Holds v

end Elements.Superposition
