import Elements.Foundations.Phrases

/-!
# Rectilineal figures given by their outlines: the words

I.45 and II.14 take "a given rectilineal figure". Euclid defines a figure as "that which is
contained by any boundary or boundaries" (Definition I.14), and rectilineal figures as
"those which are contained by straight lines" (Definition I.19). Here such a figure is
given by its boundary alone, with no division or area supplied (brief 0013), and the words
for it are defined once, from the undefined words and the phrases of `Phrases.lean`. None
of them is an assumption. What is proved of them is in Book Zero (`Elements/Figure/`).

* **Convex outlines** (`ConvexOutline`, `ConvexRegion`, `fan`). A convex figure is given by
  its corners in order, either way round; its region is the points on the closed side of
  each side's straight line towards the other corners; and the straight lines from its first
  corner divide it into triangles, the fan.
* **Loops and outlines** (`SimpleLoop`, `LoopInside`, `LoopRegion`, `Outline`). A contour is
  a list of distinct corners in cyclic order whose sides meet only at common ends. A point
  off it is inside when a ray from it whose straight line misses every corner crosses an odd
  number of sides (`GoodRay`, `crossingCount`). A figure is a nonempty finite family of
  contours that do not cross, whose insides are apart or nested; it is filled where a point
  is inside an odd number of them (`Outline.depth`), so holes and islands need no
  orientation, and its region includes every boundary. Natural numbers count sides,
  crossings and contours; they measure nothing.
* **Cells** (`ConvexCell`, `Cell`, `AgreeOff`, `Tiles`, `Clips`, `Intersection`,
  `CutPieces`). A convex cell is a convex outline taken as one piece of a figure, with its
  fan's sum for area; a cell cut down to no inside is nothing (`none`). These carry the
  proof that a figure's area does not depend on its division
  (`Elements/Figure/Content.lean`).
* **A division, and the area** (`Covers`, `Divides`, `Outline.area`). Triangles divide a
  region when a point is within or on one of them exactly when it is in the region.
  `Outline.area` is an area that some division of the outline gives, chosen once; that a
  division exists (`division_exists`) and that every division gives that area (`area_eq`)
  are proved in `Elements/Figure/Divisions.lean`.

The probe of 19 October (brief 0013, section 8) first tried the convex words: it proved the
quadrilateral case of `fan_covers` and the step of `fanSum_rotate` across one side, from the
axioms already in the library.
-/

namespace Elements.Figures

open Tacit

/-! ## Convex outlines -/

/-- **The sides of an outline**: each corner with the next, and the last with the first. -/
def sides : List Point → List (Point × Point)
  | [] => []
  | c :: cs => segments (c :: cs ++ [c])

/-- X lies on the straight line AB, or on the same side of it as P: the closed side of
AB towards P, when A and B differ and P is off AB. -/
def ClosedSide (X P A B : Point) : Prop := Collinear A B X ∨ SameSideOf X P A B

/-- X lies on the straight line L, or on the same side of it as R: the closed side of
L towards R, when R is off L (if R is on L, only the points of L). -/
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

/-- X is within or on one of the triangles. -/
def Covers (ts : List (Point × Point × Point)) (X : Point) : Prop :=
  ∃ t ∈ ts, OnOrInsideTriangle X t.1 t.2.1 t.2.2

/-- The sum of the triangles of a fan. -/
noncomputable def fanSum (cs : List Point) : Area :=
  Magnitude.sum ((fan cs).map fun t => △ t.1 t.2.1 t.2.2)

/-! ## Loops and outlines -/

/-- A point is on the boundary when it is on one of the finite sides. -/
def LoopBoundary (ps : List Point) (X : Point) : Prop :=
  ∃ s ∈ sides ps, OnFiniteLine X s.1 s.2

/-- A point of a chain: on one of its finite straight lines. -/
def OnChain (cs : List Point) (X : Point) : Prop := ∃ s ∈ segments cs, OnFiniteLine X s.1 s.2

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
def LoopInside (ps : List Point) (X : Point) : Prop :=
  ¬ LoopBoundary ps X ∧
    ∃ Q : Point, GoodRay ps X Q ∧ crossingCount ps X Q % 2 = 1

/-- The closed region of one loop, defined without triangles. -/
def LoopRegion (ps : List Point) (X : Point) : Prop :=
  LoopBoundary ps X ∨ LoopInside ps X

/-- Two contours may touch at finitely many vertices, including a vertex
against another contour's side. Their interiors are disjoint or nested.
Shared sides and transverse crossings are excluded. -/
def CompatibleLoops (ps qs : List Point) : Prop :=
  (∀ X : Point, LoopBoundary ps X → LoopBoundary qs X →
    X ∈ ps ∨ X ∈ qs) ∧
  ((∀ X : Point, LoopInside ps X → ¬ LoopInside qs X) ∨
    (∀ X : Point, LoopRegion ps X → LoopRegion qs X) ∨
    (∀ X : Point, LoopRegion qs X → LoopRegion ps X))

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
def Outline.Boundary (F : Outline) (X : Point) : Prop :=
  ∃ ps ∈ F.loops, LoopBoundary ps X

/-- The number of contours containing X strictly inside them. -/
noncomputable def Outline.depth (F : Outline) (X : Point) : Nat := by
  classical
  exact (F.loops.filter fun ps => decide (LoopInside ps X)).length

/-- The filled interior has odd nesting depth. Even depths describe the
exterior and holes; a further nested contour can enclose an island. -/
def Outline.Inside (F : Outline) (X : Point) : Prop :=
  ¬ F.Boundary X ∧ F.depth X % 2 = 1

/-- The figure includes its outer and inner boundaries. -/
def Outline.Region (F : Outline) (X : Point) : Prop :=
  F.Boundary X ∨ F.Inside X

/-- All the corners of all the contours. -/
def Outline.corners (F : Outline) : List Point := F.loops.flatten

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

/-! ## Cells -/

/-- X is on none of the straight lines `ls`. -/
def Avoid (ls : List Line) (X : Point) : Prop := ∀ L ∈ ls, ¬ OnLine X L

/-- **A convex cell**: a convex outline, taken as one piece of a figure. -/
structure ConvexCell where
  /-- Its corners in order, either way round. -/
  corners : List Point
  /-- They make a convex outline. -/
  convex : ConvexOutline corners

/-- The region of a cell, within or on its outline. -/
def ConvexCell.Region (P : ConvexCell) : Point → Prop := ConvexRegion P.corners

/-- The inside of a cell: strictly on the side of each side towards the other corners. -/
def ConvexCell.Core (P : ConvexCell) (X : Point) : Prop :=
  ∀ s ∈ sides P.corners, ∀ A ∈ P.corners, A ≠ s.1 → A ≠ s.2 → SameSideOf X A s.1 s.2

/-- The area of a cell: its fan's sum. -/
noncomputable def ConvexCell.area (P : ConvexCell) : Area := fanSum P.corners

/-- A cell, or nothing: what is left of a cell after a cut. -/
abbrev Cell := Option ConvexCell

/-- The region of a cell or of nothing. -/
def CellRegion : Cell → Point → Prop
  | none, _ => False
  | some P, X => P.Region X

/-- The inside of a cell or of nothing. -/
def CellCore : Cell → Point → Prop
  | none, _ => False
  | some P, X => P.Core X

/-- The area of a cell, or of nothing. -/
noncomputable def cellArea : Cell → Area
  | none => 0
  | some P => P.area

/-- Two regions **agree off finitely many straight lines**: some finite list of straight lines
holds every point at which they differ. -/
def AgreeOff (U V : Point → Prop) : Prop :=
  ∃ ls : List Line, ∀ X : Point, Avoid ls X → (U X ↔ V X)

/-- **Cells that tile a cell**: no point is inside two of them, and together they make up the
cell, off finitely many straight lines. -/
def Tiles (P : ConvexCell) (qs : List ConvexCell) : Prop :=
  qs.Pairwise (fun Q R => ∀ X : Point, Q.Core X → ¬ R.Core X) ∧
    AgreeOff (fun X => ∃ Q ∈ qs, Q.Region X) P.Region

/-- Q is what is left of the cell P on R's side of L. -/
def Clips (P : ConvexCell) (L : Line) (R : Point) (Q : Cell) : Prop :=
  (∀ X : Point, CellCore Q X ↔ P.Core X ∧ SameSide X R L) ∧
    AgreeOff (CellRegion Q) (fun X => P.Region X ∧ Half X R L)

/-- C is the common part of the cells P and Q. -/
def Intersection (P Q : ConvexCell) (C : Cell) : Prop :=
  (∀ X : Point, CellCore C X ↔ P.Core X ∧ Q.Core X) ∧
    AgreeOff (CellRegion C) (fun X => P.Region X ∧ Q.Region X)

/-- U and V are what the straight line L leaves of the cell P, the one on A's side
and the other on B's, in either order, and together they make up P exactly. -/
def CutPieces (P : ConvexCell) (L : Line) (A B : Point) (U V : ConvexCell) : Prop :=
  (Clips P L A (some U) ∧ Clips P L B (some V) ∧
      ∀ X : Point, P.Region X ↔ CellRegion (some U) X ∨ CellRegion (some V) X) ∨
    (Clips P L A (some V) ∧ Clips P L B (some U) ∧
      ∀ X : Point, P.Region X ↔ CellRegion (some V) X ∨ CellRegion (some U) X)

/-! ## A division, and the area -/

/-- The triangles R divide the region U: a point is within or on one of them exactly when
it is in U. -/
def Divides (U : Point → Prop) (R : Apart) : Prop :=
  ∀ X : Point, Covers R.pieces X ↔ U X

/-- An area selected from divisions of the outline. A division exists (`division_exists`)
and any two have the same sum (`divisions_equal`), so every division gives this area
(`area_eq`). -/
noncomputable def Outline.area (F : Outline) : Area :=
  Classical.epsilon fun a : Area => ∃ R : Apart, Divides F.Region R ∧ R.area = a

end Elements.Figures
