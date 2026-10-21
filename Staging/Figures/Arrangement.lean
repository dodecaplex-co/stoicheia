import Staging.Figures.Outline
import Staging.Figures.Content
import Staging.Figures.ConvexArea
import Staging.Figures.CoverFacts

/-!
# Staging: from side lines to a division of an outline

Internal statements for brief 0013, all awaiting their own proofs. The convex
precursors make the proposed dependency order explicit. Regular rays and their parity are `good_ray_exists` and
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
  /- A point of the cell's inside is off every side line, so off the boundary. Join X and Y
  to a third point Z of the inside, off the straight lines from X and from Y to the corners:
  neither finite straight line meets a side line, and good rays along them cross the same
  sides, so no contour's inside changes from X to Z or from Z to Y. -/
  exact CoverFacts.cell_constant F hs hQ hX hY

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
  classical
  /- Keep the cells with a point of their inside inside the figure. -/
  obtain ⟨rs, hrs⟩ : ∃ rs : List ConvexCell,
      rs = qs.filter fun Q => decide (∃ X : Point, Q.core X ∧ F.inside X) := ⟨_, rfl⟩
  have hmem : ∀ Q : ConvexCell, Q ∈ rs ↔ Q ∈ qs ∧ ∃ X : Point, Q.core X ∧ F.inside X := by
    intro Q
    rw [hrs, List.mem_filter, decide_eq_true_eq]
  have hreg : ∀ X : Point, F.region X ↔ ∃ Q ∈ rs, Q.region X := by
    intro X
    constructor
    · /- Near X lie only the cells whose closed regions hold X (`cells_apart`). Near X there
      is a point Y inside the figure: X itself, or, on the boundary, an end of a short finite
      straight line across a side, near a point of that side at no corner, where exactly one
      contour's inside changes (`region_filled`). Y lies in some cell, which therefore holds
      X; and from Y a point of that cell's inside is inside the figure as Y is
      (`cell_point`). -/
      intro hX
      obtain ⟨hp, hp1, hp2⟩ := CoverFacts.cells_apart X qs
      obtain ⟨Y, hY, hYp⟩ := CoverFacts.region_filled F hX hp hp1
      obtain ⟨Q, hQ, hQY⟩ := (hc Y).mp (CoverFacts.core_region (hP Y (Or.inr hY)))
      obtain ⟨W, hW, hWY⟩ := CoverFacts.cell_point F hs (hl Q hQ) hY.1 hQY
      exact ⟨Q, (hmem Q).mpr ⟨hQ, W, hW, hWY.mpr hY⟩, hp2 Y hYp Q hQ hQY⟩
    · /- A kept cell's inside is inside the figure throughout (`outline_cell_constant`). A
      point of its closed region off the boundary has a point of its inside within the same
      contours (`cell_point`), so it is inside the figure too. -/
      rintro ⟨Q, hQ, hQX⟩
      obtain ⟨hQ, Z, hZ, hZi⟩ := (hmem Q).mp hQ
      by_cases hb : F.boundary X
      · exact Or.inl hb
      · obtain ⟨W, hW, hWX⟩ := CoverFacts.cell_point F hs (hl Q hQ) hb hQX
        exact Or.inr (hWX.mp ((outline_cell_constant F Q ls hs (hl Q hQ) hZ hW).mp hZi))
  refine ⟨rs, ?_, hrs ▸ List.filter_sublist, hmem, hreg⟩
  /- A corner of a contour is in the figure, so in a kept cell. -/
  obtain ⟨ps, hps⟩ := List.exists_mem_of_ne_nil F.loops F.ne
  obtain ⟨V, hV⟩ : ∃ V : Point, V ∈ ps := by
    have hlen := (F.simple ps hps).1
    cases ps with
    | nil => simp at hlen
    | cons V _ => exact ⟨V, List.mem_cons_self⟩
  obtain ⟨E, hE⟩ := outgoing_side hV
  obtain ⟨Q, hQ, -⟩ := (hreg V).mp (Or.inl ⟨ps, hps, (V, E), hE, Or.inl rfl⟩)
  exact List.ne_nil_of_mem hQ

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
