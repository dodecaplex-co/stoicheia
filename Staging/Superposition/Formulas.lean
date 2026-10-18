import Elements.Figure.Basics

/-!
# Superposition, restricted: the formulas

A prototype for [brief 0009](../../docs/briefs/0009-superposition.md), after Astra's third
answer (question 2) and System E's superposition rules (Avigad, Dean and Mumma, 2009,
§3.7). It adds no axiom: the restricted rule is a hypothesis, `Rule`, which the theorems
built on it take as an argument.

System E lets a proof act as though a triangle had been laid down on another, but only to
prove facts about the figure already drawn: the corners laid down may never be handed
back as constructed points. To say that in Lean, the facts a hypothetical placement may
use and prove are written as data, formulas over named objects, rather than as arbitrary
propositions. This file is that language.

* A `Name` is a given point, or one of the two corners the placement lays down,
  `Name.second` and `Name.third` (B′ and C′ in I.4). The laid-down corners are names in a
  formula, never points that Lean can hand back.
* An `Atom` is one of the primitive relations on named points and given straight lines:
  equality of points, a point on a straight line, betweenness, the same side, and
  equality of two lengths, two angles or two triangles. A `Lit` is an atom or its denial.
  None of them hides a quantifier: each says something of the objects it names, and of no
  other.
* A `Metric` formula is an equality of lengths, of angles or of triangles: the only kind
  of conclusion the rule exports.

`Holds` reads a formula in the plane, once each name is given a point.
-/

namespace Elements.Superposition

/-- The names a hypothetical placement may use: the given points, and the two corners it
lays down. When the triangle ABC is laid down with A on D, `second` is where B comes down
and `third` is where C comes down. -/
inductive Name where
  /-- A point the proof already holds. Any point may be named so: naming a point it holds
  constructs nothing. -/
  | given (P : Point)
  /-- Where the second corner of the triangle comes down. -/
  | second
  /-- Where the third corner of the triangle comes down. -/
  | third

instance : Coe Point Name := ⟨Name.given⟩

/-- The point each name stands for, once the laid-down corners are put at `B'` and `C'`. -/
def Name.at (B' C' : Point) : Name → Point
  | given P => P
  | second => B'
  | third => C'

/-- A primitive relation on named points and given straight lines. -/
inductive Atom (V : Type) where
  /-- `P` and `Q` are one point. -/
  | eq (P Q : V)
  /-- `P` lies on the straight line `L`. -/
  | onLine (P : V) (L : Line)
  /-- `Q` lies between `P` and `R`. -/
  | between (P Q R : V)
  /-- `P` and `Q` lie on the same side of the straight line `L`. -/
  | sameSide (P Q : V) (L : Line)
  /-- The straight line `PQ` is equal to the straight line `RS`. -/
  | len (P Q R S : V)
  /-- The angle `PQR` is equal to the angle `STU`. -/
  | angle (P Q R S T U : V)
  /-- The triangle `PQR` is equal to the triangle `STU`. -/
  | area (P Q R S T U : V)

namespace Atom

variable {V W : Type}

/-- What the atom says, once each name `n` stands for the point `σ n`. -/
def Holds (σ : V → Point) : Atom V → Prop
  | eq P Q => σ P = σ Q
  | onLine P L => OnLine (σ P) L
  | between P Q R => Between (σ P) (σ Q) (σ R)
  | sameSide P Q L => SameSide (σ P) (σ Q) L
  | len P Q R S => ‖(σ P) (σ Q)‖ = ‖(σ R) (σ S)‖
  | angle P Q R S T U => ∠ (σ P) (σ Q) (σ R) = ∠ (σ S) (σ T) (σ U)
  | area P Q R S T U => △ (σ P) (σ Q) (σ R) = △ (σ S) (σ T) (σ U)

/-- The atom with each name renamed by `f`. -/
def map (f : V → W) : Atom V → Atom W
  | eq P Q => eq (f P) (f Q)
  | onLine P L => onLine (f P) L
  | between P Q R => between (f P) (f Q) (f R)
  | sameSide P Q L => sameSide (f P) (f Q) L
  | len P Q R S => len (f P) (f Q) (f R) (f S)
  | angle P Q R S T U => angle (f P) (f Q) (f R) (f S) (f T) (f U)
  | area P Q R S T U => area (f P) (f Q) (f R) (f S) (f T) (f U)

/-- A renamed atom says of `σ` what the atom says of `σ ∘ f`. -/
theorem holds_map (f : V → W) (σ : W → Point) (a : Atom V) :
    (a.map f).Holds σ ↔ a.Holds (σ ∘ f) := by
  cases a <;> exact Iff.rfl

end Atom

/-- An atom, or its denial: the facts a placement may use and the steps it may take. -/
inductive Lit (V : Type) where
  /-- The atom holds. -/
  | pos (a : Atom V)
  /-- The atom does not hold. -/
  | neg (a : Atom V)

namespace Lit

variable {V W : Type}

/-- What the literal says, once each name `n` stands for the point `σ n`. -/
def Holds (σ : V → Point) : Lit V → Prop
  | pos a => a.Holds σ
  | neg a => ¬ a.Holds σ

/-- The literal with each name renamed by `f`. -/
def map (f : V → W) : Lit V → Lit W
  | pos a => pos (a.map f)
  | neg a => neg (a.map f)

/-- A renamed literal says of `σ` what the literal says of `σ ∘ f`. -/
theorem holds_map (f : V → W) (σ : W → Point) (ℓ : Lit V) :
    (ℓ.map f).Holds σ ↔ ℓ.Holds (σ ∘ f) := by
  cases ℓ with
  | pos a => exact Atom.holds_map f σ a
  | neg a => exact not_congr (Atom.holds_map f σ a)

end Lit

/-- An equality of magnitudes: of two lengths, two angles or two triangles. These are the
only conclusions the restricted rule exports. -/
inductive Metric (V : Type) where
  /-- The straight line `PQ` is equal to the straight line `RS`. -/
  | len (P Q R S : V)
  /-- The angle `PQR` is equal to the angle `STU`. -/
  | angle (P Q R S T U : V)
  /-- The triangle `PQR` is equal to the triangle `STU`. -/
  | area (P Q R S T U : V)

namespace Metric

variable {V W : Type}

/-- The metric formula as an atom. -/
def toAtom : Metric V → Atom V
  | len P Q R S => .len P Q R S
  | angle P Q R S T U => .angle P Q R S T U
  | area P Q R S T U => .area P Q R S T U

/-- What the metric formula says, once each name `n` stands for the point `σ n`. -/
def Holds (σ : V → Point) (m : Metric V) : Prop := m.toAtom.Holds σ

/-- The metric formula with each name renamed by `f`. -/
def map (f : V → W) : Metric V → Metric W
  | len P Q R S => len (f P) (f Q) (f R) (f S)
  | angle P Q R S T U => angle (f P) (f Q) (f R) (f S) (f T) (f U)
  | area P Q R S T U => area (f P) (f Q) (f R) (f S) (f T) (f U)

/-- The names the metric formula mentions, in order. -/
def names : Metric V → List V
  | len P Q R S => [P, Q, R, S]
  | angle P Q R S T U => [P, Q, R, S, T, U]
  | area P Q R S T U => [P, Q, R, S, T, U]

/-- Renaming a metric formula and then reading it as an atom is reading it as an atom and
then renaming. -/
theorem toAtom_map (f : V → W) (m : Metric V) : (m.map f).toAtom = m.toAtom.map f := by
  cases m <;> rfl

/-- A renamed metric formula says of `σ` what the formula says of `σ ∘ f`. -/
theorem holds_map (f : V → W) (σ : W → Point) (m : Metric V) :
    (m.map f).Holds σ ↔ m.Holds (σ ∘ f) := by
  cases m <;> exact Iff.rfl

/-- The names of a renamed formula are the renamed names. -/
theorem names_map (f : V → W) (m : Metric V) : (m.map f).names = m.names.map f := by
  cases m <;> rfl

end Metric

end Elements.Superposition
