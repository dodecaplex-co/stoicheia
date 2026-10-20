import Staging.Figures.Outline
import Staging.Figures.Content
import Staging.Figures.ConvexArea

/-!
# Staging: from side lines to a division of an outline

Internal statements for brief 0013, all awaiting their own proofs. The convex
precursors make the proposed dependency order explicit without changing the existing
convex files. Regular rays and their parity are `good_ray_exists` and
`crossing_parity_independent` in `Outline.lean`.

The recommended division route selects cells of a finite arrangement. The first two
diagonal statements below describe splits joining original corners.
`simple_triangulation` asserts division existence without restricting the triangle
vertices; the arrangement route can also supply that conclusion. A proof that cites Book I must move to a shared Book I module after its
latest cited proposition, as brief 0013 requires.
-/

namespace Elements.Figures

/-- The two boundary chains of a convex outline lie across its diagonal. -/
theorem convex_diagonal_separates {A B : Point} {us vs : List Point}
    (h : ConvexOutline (A :: (us ++ B :: vs))) (hu : us ≠ []) (hv : vs ≠ []) :
    ∀ U ∈ us, ∀ V ∈ vs, OppositeSidesOf U V A B := by
  sorry

/-- A diagonal divides a convex region into two convex regions, whose common
part is exactly the finite diagonal. -/
theorem convex_diagonal_split {A B : Point} {us vs : List Point}
    (h : ConvexOutline (A :: (us ++ B :: vs))) (hu : us ≠ []) (hv : vs ≠ []) :
    ConvexOutline (A :: (us ++ [B])) ∧ ConvexOutline (B :: (vs ++ [A])) ∧
      (∀ X : Point, ConvexRegion (A :: (us ++ B :: vs)) X ↔
        ConvexRegion (A :: (us ++ [B])) X ∨ ConvexRegion (B :: (vs ++ [A])) X) ∧
      (∀ X : Point,
        (ConvexRegion (A :: (us ++ [B])) X ∧ ConvexRegion (B :: (vs ++ [A])) X) ↔
          OnFiniteLine X A B) := by
  sorry

/-- The convex fan has the same sum from any starting corner. -/
theorem fanSum_rotateLeft {cs : List Point} (h : ConvexOutline cs) (n : Nat) :
    fanSum (cs.rotateLeft n) = fanSum cs := by
  sorry

/-- Finitely many points containing a triangle lie in a convex cell. -/
theorem convex_enclosure (ps : List Point)
    (h : ∃ A ∈ ps, ∃ B ∈ ps, ∃ C ∈ ps, Triangle A B C) :
    ∃ P : ConvexCell, ∀ V ∈ ps, P.region V := by
  sorry

/-- An outline's whole region lies strictly inside an enclosing cell. -/
theorem outline_enclosure (F : Outline) :
    ∃ P : ConvexCell, ∀ X : Point, F.region X → P.core X := by
  sorry

/-- The supporting straight lines of every contour side form a finite list. -/
theorem outline_side_lines (F : Outline) :
    ∃ ls : List Line, ∀ L : Line, L ∈ ls ↔
      ∃ ps ∈ F.loops, ∃ s ∈ sides ps, OnLine s.1 L ∧ OnLine s.2 L := by
  sorry

/-- Cutting a convex cell by finitely many straight lines preserves its exact
closed region and gives cells with disjoint interiors, each off every cut line. -/
theorem convex_arrangement (P : ConvexCell) (ls : List Line) :
    ∃ qs : List ConvexCell, qs ≠ [] ∧
      qs.Pairwise (fun Q R => ∀ X : Point, Q.core X → ¬ R.core X) ∧
      (∀ X : Point, P.region X ↔ ∃ Q ∈ qs, Q.region X) ∧
      ∀ Q ∈ qs, ∀ L ∈ ls, ∀ X Y : Point,
        Q.core X → Q.core Y → SameSide X Y L := by
  sorry

/-- Inside one open arrangement cell, an outline's parity is constant. -/
theorem outline_cell_constant (F : Outline) (Q : ConvexCell) (ls : List Line)
    (hs : ∀ ps ∈ F.loops, ∀ s ∈ sides ps,
      ∃ L ∈ ls, OnLine s.1 L ∧ OnLine s.2 L)
    (hQ : ∀ L ∈ ls, ∀ X Y : Point,
      Q.core X → Q.core Y → SameSide X Y L)
    {X Y : Point} (hX : Q.core X) (hY : Q.core Y) :
    F.inside X ↔ F.inside Y := by
  sorry

/-- Selecting the cells with an interior point in the figure gives its exact
closed region, including hole boundaries, auxiliary cuts and corner contacts. -/
theorem outline_cells_cover (F : Outline) (P : ConvexCell)
    (hP : ∀ X : Point, F.region X → P.core X) (ls : List Line)
    (hs : ∀ ps ∈ F.loops, ∀ s ∈ sides ps,
      ∃ L ∈ ls, OnLine s.1 L ∧ OnLine s.2 L)
    (qs : List ConvexCell)
    (ha : qs.Pairwise (fun Q R => ∀ X : Point, Q.core X → ¬ R.core X))
    (hc : ∀ X : Point, P.region X ↔ ∃ Q ∈ qs, Q.region X)
    (hl : ∀ Q ∈ qs, ∀ L ∈ ls, ∀ X Y : Point,
      Q.core X → Q.core Y → SameSide X Y L) :
    ∃ rs : List ConvexCell, rs ≠ [] ∧ rs.Sublist qs ∧
      (∀ Q : ConvexCell, Q ∈ rs ↔
        Q ∈ qs ∧ ∃ X : Point, Q.core X ∧ F.inside X) ∧
      (∀ X : Point, F.region X ↔ ∃ Q ∈ rs, Q.region X) := by
  sorry

/-- A simple outline with at least four corners has an interior diagonal
joining two of its original, nonadjacent corners. -/
theorem simple_diagonal {ps : List Point} (h : SimpleLoop ps) (hn : 4 ≤ ps.length) :
    ∃ (n : Nat) (A B : Point) (us vs : List Point),
      ps.rotateLeft n = A :: (us ++ B :: vs) ∧ us ≠ [] ∧ vs ≠ [] ∧
        ∀ X : Point, Between A X B → loopInside ps X := by
  sorry

/-- An interior diagonal splits a simple region into two simple regions with
exactly that diagonal in common. Disjoint interiors need their own argument. -/
theorem simple_diagonal_partition {A B : Point} {us vs : List Point}
    (h : SimpleLoop (A :: (us ++ B :: vs))) (hu : us ≠ []) (hv : vs ≠ [])
    (hd : ∀ X : Point, Between A X B → loopInside (A :: (us ++ B :: vs)) X) :
    SimpleLoop (A :: (us ++ [B])) ∧ SimpleLoop (B :: (vs ++ [A])) ∧
      (∀ X : Point, loopRegion (A :: (us ++ B :: vs)) X ↔
        loopRegion (A :: (us ++ [B])) X ∨ loopRegion (B :: (vs ++ [A])) X) ∧
      (∀ X : Point,
        (loopRegion (A :: (us ++ [B])) X ∧ loopRegion (B :: (vs ++ [A])) X) ↔
          OnFiniteLine X A B) := by
  sorry

/-- A simple outline admits a division. The arrangement route also supplies
this conclusion; the optional diagonal route proves it by splitting the outline. -/
theorem simple_triangulation {ps : List Point} (h : SimpleLoop ps) :
    ∃ R : Apart, Divides (loopRegion ps) R := by
  sorry

end Elements.Figures
