import Staging.Figures.Convex
import Staging.Figures.Avoid

/-!
# Staging: convex cells, and cutting them

Words and statements for the route to brief 0013's content theorem (a draft for the owner's
approval), with `sorry` where a proof is due. A convex cell is a convex outline taken as a
piece of a figure; its area is its fan's sum, which does not depend on the corner the fan is
drawn from (`fanSum_rotate`). A straight line cuts a cell into at most two cells; a cell may
be cut down to nothing, or to a segment or a point, which has no inside, and then it is
`none`. Two regions that agree at every point off finitely many straight lines are said to
agree off them (`AgreeOff`): a cut's pieces are pinned exactly by their insides, and up to
finitely many lines by their regions. The final theorems about outlines are exact.

The route is the convex-cut induction of brief 0013's section on the proof route, after
David Hilbert's theory of content.
-/

namespace Elements.Figures

open Tacit

/-- **A convex cell**: a convex outline, taken as one piece of a figure. -/
structure ConvexCell where
  /-- Its corners in order, either way round. -/
  corners : List Point
  /-- They make a convex outline. -/
  convex : ConvexOutline corners

/-- The region of a cell, within or on its outline. -/
def ConvexCell.region (P : ConvexCell) : Point → Prop := ConvexRegion P.corners

/-- The inside of a cell: strictly on the side of each side towards the other corners. -/
def ConvexCell.core (P : ConvexCell) (X : Point) : Prop :=
  ∀ s ∈ sides P.corners, ∀ A ∈ P.corners, A ≠ s.1 → A ≠ s.2 → SameSideOf X A s.1 s.2

/-- The area of a cell: its fan's sum. -/
noncomputable def ConvexCell.area (P : ConvexCell) : Area := fanSum P.corners

/-- A cell, or nothing: what is left of a cell after a cut. -/
abbrev Cell := Option ConvexCell

/-- The region of a cell or of nothing. -/
def cellRegion : Cell → Point → Prop
  | none, _ => False
  | some P, X => P.region X

/-- The inside of a cell or of nothing. -/
def cellCore : Cell → Point → Prop
  | none, _ => False
  | some P, X => P.core X

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
  qs.Pairwise (fun Q R => ∀ X : Point, Q.core X → ¬ R.core X) ∧
    AgreeOff (fun X => ∃ Q ∈ qs, Q.region X) P.region

/-- `Q` is what is left of the cell `P` on `R`'s side of `L`. -/
def Clips (P : ConvexCell) (L : Line) (R : Point) (Q : Cell) : Prop :=
  (∀ X : Point, cellCore Q X ↔ P.core X ∧ SameSide X R L) ∧
    AgreeOff (cellRegion Q) (fun X => P.region X ∧ Half X R L)

/-- `C` is the common part of the cells `P` and `Q`. -/
def Intersection (P Q : ConvexCell) (C : Cell) : Prop :=
  (∀ X : Point, cellCore C X ↔ P.core X ∧ Q.core X) ∧
    AgreeOff (cellRegion C) (fun X => P.region X ∧ Q.region X)

/-- **A triangle is a cell**, with the same region and the same area. -/
theorem triangle_cell {A B C : Point} (h : Triangle A B C) :
    ∃ P : ConvexCell, P.corners = [A, B, C] ∧
      (∀ X : Point, P.region X ↔ OnOrInsideTriangle X A B C) ∧ P.area = △ A B C := by
  sorry

/-- A corner put in between two corners next to each other, on the straight line joining
them, does not change a fan's sum. -/
theorem fan_insert_between {O A B X : Point} (us vs : List Point) (h : Between A X B) :
    fanSum (O :: (us ++ A :: X :: B :: vs)) = fanSum (O :: (us ++ A :: B :: vs)) := by
  sorry

/-- **A fan from a point of a side**: a convex outline's fan from a point of its first side
has the fan's sum from its first corner. -/
theorem boundary_fan_sum {A B X : Point} {ps : List Point}
    (h : ConvexOutline (A :: B :: ps)) (hX : OnFiniteLine X A B) :
    fanSum (X :: ((B :: ps) ++ [A])) = fanSum (A :: B :: ps) := by
  sorry

/-- **The corners of a cell are its region's extreme points**: the points of the region on
no finite straight line between two other points of it. -/
theorem convex_extreme_iff (P : ConvexCell) (X : Point) :
    (P.region X ∧ ∀ A B : Point, P.region A → P.region B → ¬ Between A X B) ↔
      X ∈ P.corners := by
  sorry

/-- **A cell's area depends only on its region**: two cells whose regions agree off finitely
many straight lines have the same area. -/
theorem convex_area_ext (P Q : ConvexCell) (h : AgreeOff P.region Q.region) :
    P.area = Q.area := by
  sorry

/-- **A straight cut**: a straight line cuts a cell into what is left on each side of it,
which together make up the cell exactly, and whose areas make up its area. -/
theorem convex_cut (P : ConvexCell) {L : Line} {A B : Point} (hAB : OppositeSides A B L) :
    ∃ U V : Cell, Clips P L A U ∧ Clips P L B V ∧
      (∀ X : Point, P.region X ↔ cellRegion U X ∨ cellRegion V X) ∧
      P.area = cellArea U + cellArea V := by
  sorry

/-- **The common part of two cells** is a cell, or has no inside. -/
theorem convex_intersection (P Q : ConvexCell) : ∃ C : Cell, Intersection P Q C := by
  sorry

/-- **Content for cells**: cells that tile a cell have its area together. -/
theorem convex_tiles_area (P : ConvexCell) (qs : List ConvexCell) (h : Tiles P qs) :
    Magnitude.sum (qs.map ConvexCell.area) = P.area := by
  sorry

end Elements.Figures
