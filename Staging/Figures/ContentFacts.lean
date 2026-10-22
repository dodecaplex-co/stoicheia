import Staging.Figures.Cells

/-!
# Staging: the cells of two divisions, and where they meet

Helpers for brief 0013's content theorem (a draft for the owner's approval; route C4, brief
0013, section 8, "Content", step 5). Each triangle of a division is a cell (`triangle_cell`);
each triangle of one division meets each of the other in a cell or in nothing
(`convex_intersection`), chosen once, so that the same common part is counted by its row and
by its column. A row of common parts tiles its triangle, and its areas make up the
triangle's (`convex_tiles_area`), because the triangles of the other division lie apart and
cover the same points. The route follows David Hilbert's theory of content, gratefully
acknowledged in brief 0006.
-/

namespace Elements.Figures

open Tacit

namespace Content

/-! ## The cell of a triangle -/

open Classical in
/-- The cell of a triangle named by its corners, chosen once by `triangle_cell`; nothing when
the corners are on one straight line. -/
noncomputable def triCell (t : Point × Point × Point) : Cell :=
  if h : Triangle t.1 t.2.1 t.2.2 then some (Classical.choose (triangle_cell h)) else none

/-- The cell of a triangle has the triangle's corners, region and area. -/
theorem triCell_eq {t : Point × Point × Point} (h : Triangle t.1 t.2.1 t.2.2) :
    ∃ P : ConvexCell, triCell t = some P ∧ P.corners = [t.1, t.2.1, t.2.2] ∧
      (∀ X : Point, P.region X ↔ OnOrInsideTriangle X t.1 t.2.1 t.2.2) ∧
      P.area = △ t.1 t.2.1 t.2.2 := by
  refine ⟨Classical.choose (triangle_cell h), ?_, Classical.choose_spec (triangle_cell h)⟩
  unfold triCell
  rw [dite_eq_left h]

/-- The inside of a cell with the corners of a triangle is within the triangle. -/
theorem core_inside {P : ConvexCell} {A B C X : Point} (hc : P.corners = [A, B, C])
    (h : Triangle A B C) (hX : P.core X) : InsideTriangle X A B C := by
  unfold ConvexCell.core at hX
  rw [hc] at hX
  have side (s : Point × Point) (hs : s ∈ [(A, B), (B, C), (C, A)]) (D : Point)
      (hD : D ∈ [A, B, C]) (h₁ : D ≠ s.1) (h₂ : D ≠ s.2) : SameSideOf X D s.1 s.2 :=
    hX s hs D hD h₁ h₂
  exact ⟨side (B, C) (by simp) A (by simp) h.ne₁₂ h.ne₁₃,
    side (C, A) (by simp) B (by simp) h.ne₂₃ h.ne₁₂.symm,
    side (A, B) (by simp) C (by simp) h.ne₁₃.symm h.ne₂₃.symm⟩

/-- A point inside the cell of a triangle is inside the triangle. -/
theorem triCell_core (t : Point × Point × Point) {X : Point} (hX : cellCore (triCell t) X) :
    InsideTriangle X t.1 t.2.1 t.2.2 := by
  by_cases h : Triangle t.1 t.2.1 t.2.2
  · obtain ⟨P, hP, hc, -, -⟩ := triCell_eq h
    rw [hP] at hX
    exact core_inside hc h hX
  · unfold triCell at hX
    rw [dite_eq_right h] at hX
    exact hX.elim

/-- The region of the cell of a triangle is the triangle, within or on it. -/
theorem triCell_region {t : Point × Point × Point} (h : Triangle t.1 t.2.1 t.2.2) (X : Point) :
    cellRegion (triCell t) X ↔ OnOrInsideTriangle X t.1 t.2.1 t.2.2 := by
  obtain ⟨P, hP, -, hr, -⟩ := triCell_eq h
  rw [hP]
  exact hr X

/-! ## Where two cells meet -/

/-- The common part of two cells, chosen once by `convex_intersection`; nothing, if either is
nothing. -/
noncomputable def meet : Cell → Cell → Cell
  | some P, some Q => Classical.choose (convex_intersection P Q)
  | _, _ => none

/-- A point inside the common part of two cells or nothings is inside both. -/
theorem meet_core (c d : Cell) {X : Point} (hX : cellCore (meet c d) X) :
    cellCore c X ∧ cellCore d X := by
  cases c with
  | none => exact hX.elim
  | some P =>
    cases d with
    | none => exact hX.elim
    | some Q => exact ((Classical.choose_spec (convex_intersection P Q)).1 X).mp hX

/-- The region of the common part of two cells or nothings is the common part of their
regions, off finitely many straight lines. -/
theorem meet_region (c d : Cell) :
    AgreeOff (cellRegion (meet c d)) (fun X => cellRegion c X ∧ cellRegion d X) := by
  cases c with
  | none => exact Tiling.agreeOff_of_iff fun X => ⟨False.elim, fun h => h.1⟩
  | some P =>
    cases d with
    | none => exact Tiling.agreeOff_of_iff fun X => ⟨False.elim, fun h => h.2⟩
    | some Q => exact (Classical.choose_spec (convex_intersection P Q)).2

/-! ## Cells or nothings that tile a cell -/

/-- The cells present in a list of cells or nothings have the area of the whole list: a
nothing adds nothing. -/
theorem sum_present (l : List Cell) :
    Magnitude.sum ((l.filterMap id).map ConvexCell.area) = Magnitude.sum (l.map cellArea) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    cases c with
    | none =>
      change Magnitude.sum ((l.filterMap id).map ConvexCell.area) =
        0 + Magnitude.sum (l.map cellArea)
      rw [ih, add_comm 0, add_zero]
    | some P =>
      change P.area + Magnitude.sum ((l.filterMap id).map ConvexCell.area) =
        P.area + Magnitude.sum (l.map cellArea)
      rw [ih]

/-- A point is in a cell present in a list of cells or nothings exactly when it is in the
region of one of the list. -/
theorem present_region (l : List Cell) (X : Point) :
    (∃ Q ∈ l.filterMap id, Q.region X) ↔ ∃ c ∈ l, cellRegion c X := by
  constructor
  · rintro ⟨Q, hQ, hX⟩
    obtain ⟨c, hc, he⟩ := List.mem_filterMap.mp hQ
    cases c with
    | none => exact absurd he (by simp)
    | some P =>
      cases he
      exact ⟨some Q, hc, hX⟩
  · rintro ⟨c, hc, hX⟩
    cases c with
    | none => exact hX.elim
    | some P => exact ⟨P, List.mem_filterMap.mpr ⟨some P, hc, rfl⟩, hX⟩

/-- **A row tiles its cell** (brief 0013, section 8, "Content", step 5). A cell `P` lies within
the triangles `ts`, which lie apart; to each triangle belongs a cell or nothing `f t`, inside
it, whose region is, off finitely many straight lines, the part of `P` within or on it. Then
the cells `f t` tile `P`, and their areas make up its area (`convex_tiles_area`). -/
theorem row_area (P : ConvexCell) (ts : List (Point × Point × Point))
    (hap : ts.Pairwise fun s s' => ∀ Y : Point,
      InsideTriangle Y s.1 s.2.1 s.2.2 → ¬ InsideTriangle Y s'.1 s'.2.1 s'.2.2)
    (f : Point × Point × Point → Cell)
    (hcore : ∀ t X, cellCore (f t) X → InsideTriangle X t.1 t.2.1 t.2.2)
    (hreg : ∀ t ∈ ts, AgreeOff (cellRegion (f t))
      (fun X => P.region X ∧ OnOrInsideTriangle X t.1 t.2.1 t.2.2))
    (hsub : ∀ X : Point, P.region X → Covers ts X) :
    Magnitude.sum (ts.map fun t => cellArea (f t)) = P.area := by
  /- No point is inside two of the cells present: they are inside triangles that lie
  apart. -/
  have hp : ((ts.map f).filterMap id).Pairwise
      (fun Q R => ∀ X : Point, Q.core X → ¬ R.core X) := by
    rw [List.pairwise_filterMap, List.pairwise_map]
    refine hap.imp fun {s s'} hss' Q hQ R hR X hX hX' => ?_
    have hs : cellCore (f s) X := by
      cases hfs : f s with
      | none => simp [hfs] at hQ
      | some Q' =>
        rw [hfs] at hQ
        cases hQ
        exact hX
    have hs' : cellCore (f s') X := by
      cases hfs : f s' with
      | none => simp [hfs] at hR
      | some R' =>
        rw [hfs] at hR
        cases hR
        exact hX'
    exact hss' X (hcore s X hs) (hcore s' X hs')
  /- Together they make up `P`, off finitely many straight lines: each is the part of `P` on
  its triangle, and the triangles cover `P`. -/
  have hag : AgreeOff (fun X => ∃ Q ∈ (ts.map f).filterMap id, Q.region X) P.region := by
    refine Tiling.agreeOff_trans (Tiling.agreeOff_of_iff fun X =>
      (present_region (ts.map f) X).trans (CellFacts.exists_mem_map_iff ts f
        (fun c => cellRegion c X))) (Tiling.agreeOff_trans
      (Tiling.agreeOff_exists_mem ts hreg) (Tiling.agreeOff_of_iff fun X => ?_))
    constructor
    · rintro ⟨t, -, hX, -⟩
      exact hX
    · intro hX
      obtain ⟨t, ht, hXt⟩ := hsub X hX
      exact ⟨t, ht, hX, hXt⟩
  have ha := convex_tiles_area P ((ts.map f).filterMap id) ⟨hp, hag⟩
  rw [sum_present, List.map_map] at ha
  exact ha

end Content

end Elements.Figures
