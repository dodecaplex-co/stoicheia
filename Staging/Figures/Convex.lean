import Elements.Figure.Basics
import Elements.Figure.Rectilineal

/-!
# Staging: a convex rectilineal figure given by its outline

Prototype statements for brief 0013 (a draft for the owner's approval), so that the convex
case can be tried while the brief is written. A convex figure is given by its corners in
order, either way round; its region is defined from the outline alone, as the points on or
within every side's straight line, on the side of the other corners (the inward closed
half-planes); and the straight lines from its first corner divide it into triangles, the
fan. Nothing here is frozen: the brief may rename or reshape every word.

The probe of 19 October proved the quadrilateral case of `fan_covers` and the step of
`fanSum_rotate` across one side, from the axioms already in the library.
-/

namespace Elements.Figures

open Tacit

/-- **The sides of an outline**: each corner with the next, and the last with the first. -/
def sides : List Point → List (Point × Point)
  | [] => []
  | c :: cs => segments (c :: cs ++ [c])

/-- `X` lies on the straight line `AB`, or on the same side of it as `P`: the closed side of
`AB` towards `P`, when `A` and `B` differ and `P` is off `AB`. -/
def ClosedSide (X P A B : Point) : Prop := Collinear A B X ∨ SameSideOf X P A B

/-- `X` lies on the straight line `L`, or on the same side of it as `R`: the closed side of
`L` towards `R`, when `R` is off `L` (if `R` is on `L`, only the points of `L`). -/
def Half (X R : Point) (L : Line) : Prop := OnLine X L ∨ SameSide X R L

/-- **A convex outline**: three corners or more, all different, and for each side, every
other corner off its straight line, all of them on one side of it. -/
def ConvexOutline (cs : List Point) : Prop :=
  3 ≤ cs.length ∧ cs.Nodup ∧
    ∀ s ∈ sides cs, ∀ P ∈ cs, ∀ Q ∈ cs, P ≠ s.1 → P ≠ s.2 → Q ≠ s.1 → Q ≠ s.2 →
      SameSideOf P Q s.1 s.2

/-- **The region of a convex outline**, from the outline alone: the points on the closed
side of each side towards the other corners. A raw list construction: its geometric reading
needs `ConvexOutline`, and on a list of fewer than three points it holds of every point. -/
def ConvexRegion (cs : List Point) (X : Point) : Prop :=
  ∀ s ∈ sides cs, ∀ P ∈ cs, P ≠ s.1 → P ≠ s.2 → ClosedSide X P s.1 s.2

/-- **The fan**: the triangles made by the straight lines from the first corner to the
others, one for each side away from it. Like `ConvexRegion`, a raw list construction: its
geometric reading needs `ConvexOutline`. -/
def fan : List Point → List (Point × Point × Point)
  | [] => []
  | c :: cs => (segments cs).map fun s => (c, s.1, s.2)

/-- `X` is within or on one of the triangles. -/
def Covers (ts : List (Point × Point × Point)) (X : Point) : Prop :=
  ∃ t ∈ ts, OnOrInsideTriangle X t.1 t.2.1 t.2.2

/-- The sum of the triangles of a fan. -/
noncomputable def fanSum (cs : List Point) : Area :=
  Magnitude.sum ((fan cs).map fun t => △ t.1 t.2.1 t.2.2)

end Elements.Figures
