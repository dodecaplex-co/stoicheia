module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Side
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Model.Signature

/-!
# The ordinary plane, as a reading of the words

This is the reading that [tests/model/MODEL.md](../../tests/model/MODEL.md) describes and
tests numerically, now as Lean definitions over Mathlib's Euclidean plane
`EuclideanSpace ℝ (Fin 2)`. Each word is read by a standard Mathlib notion wherever one
exists, so that Mathlib's lemmas about it can do the work:

| Word | Reading |
|---|---|
| `Point` | a point of `EuclideanSpace ℝ (Fin 2)` |
| `Line` | a one-dimensional affine subspace; two lines are equal when they have the same points |
| `OnLine A L` | membership |
| `SameSide A B L` | strictly on one side, Mathlib's `SSameSide` |
| `Between A B C` | strictly between, Mathlib's `Sbtw` (so `A ≠ C`, and `B` is neither) |
| `Circle` | a Mathlib `Sphere` of positive radius |
| `OnCircle A α` | at the radius's distance from the centre |
| `InsideCircle A α` | nearer the centre than the radius |
| `Centre A α` | `A` is the sphere's centre |
| each kind of magnitude | `ℝ≥0`, with its own `0`, `+` and `<` |
| `len A B` | the distance, `nndist A B` |
| `ang A B C` | Mathlib's unoriented angle at `B`, in [0, π], but 0 when `A = B` or `C = B` |
| `area A B C` | half the absolute value of the determinant of `B - A` and `C - A` |
| `rightAngle` | π/2 |

Three choices matter.

* **The angle carrier is all of `ℝ≥0`,** not [0, π]. Single angles lie in [0, π], but
  Euclid adds angles (in I.13, "the angles CBA, ABD are either two right angles or equal to
  two right angles"), and a sum of angle magnitudes must have somewhere to live.
* **An angle with a repeated point is 0,** as in MODEL.md's reading. Mathlib's
  `EuclideanGeometry.angle` is π/2 when an arm is a zero vector, that is when `A = B` or
  `C = B`, which would make all four angle conditions of `Square A A A A` hold; so the
  reading takes Mathlib's angle only when both arms are nonzero.
* **A line is a subspace, not an equation.** Two equations can name one line, which would
  break `line_unique`; a subspace with extensional equality cannot.

Nothing here imports the library (`Elements`), and nothing here uses its axioms: the proofs
that this reading satisfies the laws rest on Lean's logic and Mathlib alone, as
`Model/Audit.lean` checks.
-/

@[expose] public section

namespace Model.Euclidean

open scoped NNReal Real

/-- The plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- A whole straight line: a one-dimensional affine subspace of the plane. Equality is
equality of subspaces, so a line is fixed by its points. -/
def Line : Type := {L : AffineSubspace ℝ Plane // Module.finrank ℝ L.direction = 1}

/-- A circle: a Mathlib sphere in the plane, with positive radius. A circle's centre and
radius are fixed by its points, so equality of these structures is equality of circles. -/
def Circle : Type := {s : EuclideanGeometry.Sphere Plane // 0 < s.radius}

/-- The determinant of two vectors of the plane, `u₀ v₁ - u₁ v₀`: twice the signed area of
the triangle they span from a common corner. -/
def det (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

/-- The angle `ABC` with vertex `B`: Mathlib's unoriented angle when `A` and `C` both differ
from `B`, and 0 when either is `B`. -/
noncomputable def angle (A B C : Plane) : ℝ≥0 :=
  open Classical in
  if A = B ∨ C = B then 0
  else ⟨EuclideanGeometry.angle A B C, EuclideanGeometry.angle_nonneg A B C⟩

/-- The area of the triangle `ABC`: half the absolute value of the determinant of its sides
from `A`. It is 0 when the corners lie on one straight line. -/
noncomputable def triArea (A B C : Plane) : ℝ≥0 :=
  ⟨|det (B - A) (C - A)| / 2, by positivity⟩

/-- The Euclidean plane as a reading of the seventeen words. It is reducible, so that a
law about `plane` reads directly as a statement about the plane. -/
noncomputable abbrev plane : Signature where
  Point := Plane
  Line := Line
  Circle := Circle
  OnLine A L := A ∈ L.1
  SameSide A B L := L.1.SSameSide A B
  Between A B C := Sbtw ℝ A B C
  OnCircle A α := A ∈ α.1
  InsideCircle A α := dist A α.1.center < α.1.radius
  Centre A α := A = α.1.center
  MagnitudeImpl _ := ⟨ℝ≥0, ⟨0⟩⟩
  zero {_} := (0 : ℝ≥0)
  add {_} a b := (a + b : ℝ≥0)
  lt {_} a b := (a < b : Prop)
  len A B := nndist A B
  ang := angle
  area := triArea
  rightAngle := ⟨π / 2, by positivity⟩

/-! ## How the words read

These unfold the reading, one word at a time, for the proofs. -/

@[simp] theorem onCircle_iff {A : Plane} {α : Circle} :
    plane.OnCircle A α ↔ dist A α.1.center = α.1.radius :=
  EuclideanGeometry.mem_sphere

@[simp] theorem insideCircle_iff {A : Plane} {α : Circle} :
    plane.InsideCircle A α ↔ dist A α.1.center < α.1.radius :=
  Iff.rfl

@[simp] theorem centre_iff {A : Plane} {α : Circle} :
    plane.Centre A α ↔ A = α.1.center :=
  Iff.rfl

end Model.Euclidean
