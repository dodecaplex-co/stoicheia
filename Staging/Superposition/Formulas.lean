import Elements.Figure.Basics

/-!
# Superposition, restricted: the formulas

A prototype for [brief 0009](../../docs/briefs/0009-superposition.md), after Astra's third
answer (question 2) and System E's superposition rule (Avigad, Dean and Mumma, 2009, §3.7).
It adds no axiom: the restricted rule is a hypothesis, `Rule`, which the theorems built on it
take as an argument.

System E lets a proof act as though a triangle had been laid down on another, but only to
prove facts about the figure already drawn: the corners laid down may never be handed back
as constructed points. To say that in Lean, the facts a hypothetical placement may use and
prove are written as data over **symbols**, and the figure is given separately, as a
**valuation** that says which point or straight line each symbol stands for. This file is
that language.

* A symbol is a member of a type the proof chooses: `P` for points, `L` for straight lines.
  The rule (`Rule`) takes its symbols from `Fin n` and `Fin m`, so a symbol is a number and
  nothing else; a proof may name its symbols with an inductive type of its own
  (`Symbols`, in `Rule.lean`).
* An `Atom` is one of the primitive relations on symbols: equality of points, a point on a
  straight line, betweenness, the same side, and equality of two lengths, two angles or two
  triangles. A `Lit` is an atom or its denial. None of them holds a point, a straight line or
  a proposition: each says one primitive thing of the symbols it names.
* A `Metric` formula is an equality of lengths, of angles or of triangles: the only kind of
  conclusion the rule exports.
* A `Val` is a valuation: a point for each point symbol and a straight line for each line
  symbol. `Holds v` reads a formula in the plane under the valuation `v`.

Two symbols are one symbol only when they are the same symbol. So a derivation, which works
on symbols, can never learn that two of them stand for one point unless a step proves it.
-/

namespace Elements.Superposition

/-- **A valuation**: the point each point symbol stands for, and the straight line each line
symbol stands for. The symbols are data; the valuation is the figure. -/
structure Val (P L : Type) where
  /-- The point a point symbol stands for. -/
  pt : P → Point
  /-- The straight line a line symbol stands for. -/
  line : L → Line

namespace Val

variable {P L P' L' : Type}

/-- The valuation read through renamings `f` and `g` of the symbols: the symbol `p` stands
for what `f p` stands for. -/
def comap (v : Val P' L') (f : P → P') (g : L → L') : Val P L := ⟨v.pt ∘ f, v.line ∘ g⟩

end Val

/-- A primitive relation on symbols. -/
inductive Atom (P L : Type) where
  /-- `p` and `q` are one point. -/
  | eq (p q : P)
  /-- `p` lies on the straight line `l`. -/
  | onLine (p : P) (l : L)
  /-- `q` lies between `p` and `r`. -/
  | between (p q r : P)
  /-- `p` and `q` lie on the same side of the straight line `l`. -/
  | sameSide (p q : P) (l : L)
  /-- The straight line `pq` is equal to the straight line `rs`. -/
  | len (p q r s : P)
  /-- The angle `pqr` is equal to the angle `stu`. -/
  | angle (p q r s t u : P)
  /-- The triangle `pqr` is equal to the triangle `stu`. -/
  | area (p q r s t u : P)

namespace Atom

variable {P L P' L' P'' L'' : Type}

/-- What the atom says of the figure, once each symbol stands for what `v` gives it. -/
def Holds (v : Val P L) : Atom P L → Prop
  | eq p q => v.pt p = v.pt q
  | onLine p l => OnLine (v.pt p) (v.line l)
  | between p q r => Between (v.pt p) (v.pt q) (v.pt r)
  | sameSide p q l => SameSide (v.pt p) (v.pt q) (v.line l)
  | len p q r s => ‖(v.pt p) (v.pt q)‖ = ‖(v.pt r) (v.pt s)‖
  | angle p q r s t u => ∠ (v.pt p) (v.pt q) (v.pt r) = ∠ (v.pt s) (v.pt t) (v.pt u)
  | area p q r s t u => △ (v.pt p) (v.pt q) (v.pt r) = △ (v.pt s) (v.pt t) (v.pt u)

/-- The atom with its point symbols renamed by `f` and its line symbols by `g`. -/
def map (f : P → P') (g : L → L') : Atom P L → Atom P' L'
  | eq p q => eq (f p) (f q)
  | onLine p l => onLine (f p) (g l)
  | between p q r => between (f p) (f q) (f r)
  | sameSide p q l => sameSide (f p) (f q) (g l)
  | len p q r s => len (f p) (f q) (f r) (f s)
  | angle p q r s t u => angle (f p) (f q) (f r) (f s) (f t) (f u)
  | area p q r s t u => area (f p) (f q) (f r) (f s) (f t) (f u)

/-- A renamed atom says under `v` what the atom says under `v` read through the renaming. -/
theorem holds_map (f : P → P') (g : L → L') (v : Val P' L') (a : Atom P L) :
    (a.map f g).Holds v ↔ a.Holds (v.comap f g) := by
  cases a <;> exact Iff.rfl

/-- Renaming twice is renaming once, by the composite. -/
theorem map_map (f : P → P') (g : L → L') (f' : P' → P'') (g' : L' → L'') (a : Atom P L) :
    (a.map f g).map f' g' = a.map (f' ∘ f) (g' ∘ g) := by
  cases a <;> rfl

end Atom

/-- An atom, or its denial: the facts a placement may use and the steps it may take. -/
inductive Lit (P L : Type) where
  /-- The atom holds. -/
  | pos (a : Atom P L)
  /-- The atom does not hold. -/
  | neg (a : Atom P L)

namespace Lit

variable {P L P' L' P'' L'' : Type}

/-- What the literal says of the figure, once each symbol stands for what `v` gives it. -/
def Holds (v : Val P L) : Lit P L → Prop
  | pos a => a.Holds v
  | neg a => ¬ a.Holds v

/-- The literal with its symbols renamed. -/
def map (f : P → P') (g : L → L') : Lit P L → Lit P' L'
  | pos a => pos (a.map f g)
  | neg a => neg (a.map f g)

/-- A renamed literal says under `v` what the literal says under `v` read through the
renaming. -/
theorem holds_map (f : P → P') (g : L → L') (v : Val P' L') (ℓ : Lit P L) :
    (ℓ.map f g).Holds v ↔ ℓ.Holds (v.comap f g) := by
  cases ℓ with
  | pos a => exact Atom.holds_map f g v a
  | neg a => exact not_congr (Atom.holds_map f g v a)

/-- Renaming twice is renaming once, by the composite. -/
theorem map_map (f : P → P') (g : L → L') (f' : P' → P'') (g' : L' → L'') (ℓ : Lit P L) :
    (ℓ.map f g).map f' g' = ℓ.map (f' ∘ f) (g' ∘ g) := by
  cases ℓ <;> simp only [map, Atom.map_map]

end Lit

/-- An equality of magnitudes: of two lengths, two angles or two triangles. These are the
only conclusions the restricted rule exports. They name points and no straight line. -/
inductive Metric (P : Type) where
  /-- The straight line `pq` is equal to the straight line `rs`. -/
  | len (p q r s : P)
  /-- The angle `pqr` is equal to the angle `stu`. -/
  | angle (p q r s t u : P)
  /-- The triangle `pqr` is equal to the triangle `stu`. -/
  | area (p q r s t u : P)

namespace Metric

variable {P L P' L' : Type}

/-- The metric formula as an atom, in a language with any line symbols. -/
def toAtom : Metric P → Atom P L
  | len p q r s => .len p q r s
  | angle p q r s t u => .angle p q r s t u
  | area p q r s t u => .area p q r s t u

/-- What the metric formula says of the figure, once each symbol stands for what `v` gives
it. -/
def Holds (v : Val P L) (m : Metric P) : Prop := (m.toAtom : Atom P L).Holds v

/-- The metric formula with its symbols renamed by `f`. -/
def map (f : P → P') : Metric P → Metric P'
  | len p q r s => len (f p) (f q) (f r) (f s)
  | angle p q r s t u => angle (f p) (f q) (f r) (f s) (f t) (f u)
  | area p q r s t u => area (f p) (f q) (f r) (f s) (f t) (f u)

/-- The symbols the metric formula names, in order. -/
def names : Metric P → List P
  | len p q r s => [p, q, r, s]
  | angle p q r s t u => [p, q, r, s, t, u]
  | area p q r s t u => [p, q, r, s, t, u]

/-- Renaming a metric formula and then reading it as an atom is reading it as an atom and
then renaming. -/
theorem toAtom_map (f : P → P') (g : L → L') (m : Metric P) :
    ((m.map f).toAtom : Atom P' L') = (m.toAtom : Atom P L).map f g := by
  cases m <;> rfl

/-- A renamed metric formula says under `v` what the formula says under `v` read through
the renaming. -/
theorem holds_map (f : P → P') (g : L → L') (v : Val P' L') (m : Metric P) :
    (m.map f).Holds v ↔ m.Holds (v.comap f g) := by
  cases m <;> exact Iff.rfl

/-- The symbols of a renamed formula are the renamed symbols. -/
theorem names_map (f : P → P') (m : Metric P) : (m.map f).names = m.names.map f := by
  cases m <;> rfl

end Metric

end Elements.Superposition
