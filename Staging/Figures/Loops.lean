import Staging.Figures.Convex

/-!
Proposed vocabulary for brief 0013. Nothing here assumes a geometric theorem.
The numerical operations count finite lists, never geometric magnitudes.
-/

namespace Elements.Figures

/-- A point is on the boundary when it is on one of the finite sides. -/
def loopBoundary (ps : List Point) (X : Point) : Prop :=
  ∃ s ∈ sides ps, OnFiniteLine X s.1 s.2

/-- A simple closed outline has distinct vertices and at least three sides.
Different sides meet only at a common end. Collinear subdivisions are allowed. -/
def SimpleLoop (ps : List Point) : Prop :=
  3 ≤ ps.length ∧ ps.Nodup ∧
    (∀ s ∈ sides ps, s.1 ≠ s.2) ∧
    (sides ps).Pairwise (fun s t => ∀ X : Point,
      OnFiniteLine X s.1 s.2 → OnFiniteLine X t.1 t.2 →
        (X = s.1 ∨ X = s.2) ∧ (X = t.1 ∨ X = t.2))

/-- No three cyclically consecutive vertices are collinear.
This reduction condition is used together with `SimpleLoop`. -/
def ReducedLoop (ps : List Point) : Prop :=
  ∀ t ∈ triples (ps ++ ps.take 2), Triangle t.1 t.2.1 t.2.2

/-- A ray from X through Q whose whole straight line avoids every vertex. -/
def GoodRay (ps : List Point) (X Q : Point) : Prop :=
  X ≠ Q ∧ ∀ V ∈ ps, ¬ Collinear X Q V

/-- The ray meets the open finite side.
Under `GoodRay` this is a transverse crossing. -/
def RayCrosses (X Q : Point) (s : Point × Point) : Prop :=
  ∃ Y : Point, OnRay Y X Q ∧ Between s.1 Y s.2

/-- The number of sides crossed by a ray. -/
noncomputable def crossingCount (ps : List Point) (X Q : Point) : Nat := by
  classical
  exact ((sides ps).filter fun s => decide (RayCrosses X Q s)).length

/-- Inside a loop means off its boundary and an odd number of crossings.
Independence of the good ray is a theorem, not part of this definition. -/
def loopInside (ps : List Point) (X : Point) : Prop :=
  ¬ loopBoundary ps X ∧
    ∃ Q : Point, GoodRay ps X Q ∧ crossingCount ps X Q % 2 = 1

/-- The closed region of one loop, defined without triangles. -/
def loopRegion (ps : List Point) (X : Point) : Prop :=
  loopBoundary ps X ∨ loopInside ps X

/-- Two contours may touch at finitely many vertices, including a vertex
against another contour's side. Their interiors are disjoint or nested.
Shared sides and transverse crossings are excluded. -/
def CompatibleLoops (ps qs : List Point) : Prop :=
  (∀ X : Point, loopBoundary ps X → loopBoundary qs X →
    X ∈ ps ∨ X ∈ qs) ∧
  ((∀ X : Point, loopInside ps X → ¬ loopInside qs X) ∨
    (∀ X : Point, loopRegion ps X → loopRegion qs X) ∨
    (∀ X : Point, loopRegion qs X → loopRegion ps X))

/-- A figure is a nonempty finite family of compatible simple contours.
It contains no division, triangle list or area witness. -/
structure Outline where
  /-- The contours, each with its vertices in cyclic order. -/
  loops : List (List Point)
  /-- A figure has at least one contour. -/
  ne : loops ≠ []
  /-- Each contour is simple. -/
  simple : ∀ ps ∈ loops, SimpleLoop ps
  /-- Distinct contours have disjoint or nested interiors and no common side. -/
  compatible : loops.Pairwise CompatibleLoops

/-- Every contour, outer or inner, belongs to the figure's boundary. -/
def Outline.boundary (F : Outline) (X : Point) : Prop :=
  ∃ ps ∈ F.loops, loopBoundary ps X

/-- The number of contours containing X strictly inside them. -/
noncomputable def Outline.depth (F : Outline) (X : Point) : Nat := by
  classical
  exact (F.loops.filter fun ps => decide (loopInside ps X)).length

/-- The filled interior has odd nesting depth. Even depths describe the
exterior and holes; a further nested contour can enclose an island. -/
def Outline.inside (F : Outline) (X : Point) : Prop :=
  ¬ F.boundary X ∧ F.depth X % 2 = 1

/-- The figure includes its outer and inner boundaries. -/
def Outline.region (F : Outline) (X : Point) : Prop :=
  F.boundary X ∨ F.inside X

/-- A simple loop regarded as a figure with one contour. -/
def singleOutline (ps : List Point) (h : SimpleLoop ps) : Outline where
  loops := [ps]
  ne := List.cons_ne_nil _ _
  simple := by
    intro qs hqs
    have heq : qs = ps := List.mem_singleton.mp hqs
    subst qs
    exact h
  compatible := List.pairwise_singleton _ _

/-- Every triangular neighbourhood of X meets a region and its complement.
This is a synthetic boundary test and introduces no metric or topology. -/
def RegionBoundary (r : Point → Prop) (X : Point) : Prop :=
  ∀ A B C : Point, Triangle A B C → InsideTriangle X A B C →
    ∃ Y Z : Point, InsideTriangle Y A B C ∧ InsideTriangle Z A B C ∧
      r Y ∧ ¬ r Z

end Elements.Figures
