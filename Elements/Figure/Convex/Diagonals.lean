import Elements.Figure.Cells.CutPieces
import Elements.Figure.Outlines.LoopFacts

/-!
# Book Zero: the diagonals of a convex outline

The convex precursors of brief 0013's route (section 8, rows B1, B2 and B4 of its ledger),
which the route proposed as steps to later rows:

* **B1** (`convex_diagonal_separates`). The two chains of a convex outline between the ends
  of a diagonal lie on opposite sides of it, by cutting off ears (`Pieces.convex_sublist`,
  `ear_opposite`).
* **B2** (`convex_diagonal_split`). A diagonal divides the convex region into two convex
  regions whose common part is exactly the finite diagonal. By B1 the diagonal cuts the
  outline corner to corner, so the proof cites that case of the cut's pieces
  (`Pieces.form_corner_corner`) rather than prove it again by a fan induction; this file
  therefore comes after `Cells/CutPieces.lean`.
* **B4's `fanSum_rotateLeft`.** The fan has the same sum from any starting corner, from
  `fanSum_rotate`, one corner at a time.

As proved, no later step uses them: the convex enclosure grows one point at a time
(`Arrangement.insert_point`), and the division of an outline selects cells of an
arrangement (brief 0013, section 8, "The routes taken", B2 and D2). Nothing in Book Zero
cites a proposition of the *Elements*.
-/

namespace Elements.Figures

/-- The two boundary chains of a convex outline lie across its diagonal. -/
theorem convex_diagonal_separates {A B : Point} {us vs : List Point}
    (h : ConvexOutline (A :: (us ++ B :: vs))) :
    ∀ U ∈ us, ∀ V ∈ vs, OppositeSidesOf U V A B := by
  /- The corners A, U, B, V, taken in order, make a convex outline
  (`Pieces.convex_sublist`, by cutting off ears, `cut_convex`), and its diagonal AB
  separates U from the later corner V (`ear_opposite`). -/
  intro U hU V hV
  have hs : [A, U, B, V].Sublist (A :: (us ++ B :: vs)) := by
    apply List.Sublist.cons_cons
    have h₁ : [U].Sublist us := List.singleton_sublist.mpr hU
    have h₂ : [B, V].Sublist (B :: vs) :=
      List.Sublist.cons_cons B (List.singleton_sublist.mpr hV)
    simpa using h₁.append h₂
  have hq : ConvexOutline [A, U, B, V] := by
    simpa using Pieces.convex_sublist [] hs (by simpa using h) (by simp)
  exact ear_opposite hq (List.mem_singleton_self V)

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
  /- The straight line AB has the corners of one chain from A to B, other than A and B, on
  one side, and those of the other chain on the other (`convex_diagonal_separates`), so it
  cuts the outline corner to corner (`Pieces.form_corner_corner`): each chain, closed by AB,
  is a convex outline whose region is the outline's region on one closed side of AB. -/
  have hsep := convex_diagonal_separates h
  obtain ⟨u, hu₀⟩ := List.exists_mem_of_ne_nil us hu
  obtain ⟨v, hv₀⟩ := List.exists_mem_of_ne_nil vs hv
  have hAB : A ≠ B := (hsep u hu₀ v hv₀).1
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hAB
  have huv : OppositeSides u v L := (hsep u hu₀ v hv₀).oppositeSides hAL hBL
  have hus : ∀ U ∈ us, SameSide U u L := fun U hU =>
    ((hsep U hU v hv₀).symm.sameSideOf (hsep u hu₀ v hv₀).symm).sameSide hAL hBL
  have hvs : ∀ V ∈ vs, SameSide V v L := fun V hV =>
    ((hsep u hu₀ V hV).sameSideOf (hsep u hu₀ v hv₀)).sameSide hAL hBL
  obtain ⟨h₁, h₂⟩ := Pieces.form_corner_corner h rfl hAL hBL hu hv hus hvs
  have hreg₂ (X : Point) : ConvexRegion (B :: (vs ++ [A])) X ↔ ConvexRegion (A :: B :: vs) X :=
    convexRegion_rotate A (B :: vs) X
  refine ⟨h₁.1, (convexOutline_rotate_iff A (B :: vs)).mpr h₂.1, fun X => ?_, fun X => ?_⟩
  · /- Off AB, a point of the region is on one side or the other. -/
    rw [h₁.2.1 X, hreg₂ X, h₂.2.1 X]
    constructor
    · intro hX
      by_cases hXL : OnLine X L
      · exact Or.inl ⟨hX, Or.inl hXL⟩
      · rcases Pieces.side_cases huv hXL with hs | hs
        · exact Or.inl ⟨hX, Or.inr hs⟩
        · exact Or.inr ⟨hX, Or.inr hs⟩
    · rintro (⟨hX, -⟩ | ⟨hX, -⟩) <;> exact hX
  · /- On both closed sides means on AB; there the first piece's region is its side BA
    (`LoopFacts.convex_supporting`). -/
    rw [h₁.2.1 X, hreg₂ X, h₂.2.1 X]
    constructor
    · rintro ⟨⟨hX, hXu⟩, -, hXv⟩
      have hXL : OnLine X L := by
        rcases hXu with hu' | hu'
        · exact hu'
        rcases hXv with hv' | hv'
        · exact hv'
        exact (Pieces.not_both huv hu' hv').elim
      have hside : (B, A) ∈ sides (A :: (us ++ [B])) := by
        simpa [sides] using Extreme.closing_segment A B (A :: us)
      exact LoopFacts.onFiniteLine_comm.mp (LoopFacts.convex_supporting h₁.1 hside
        ((h₁.2.1 X).mpr ⟨hX, Or.inl hXL⟩) ⟨L, hBL, hAL, hXL⟩)
    · intro hX
      have hA : ConvexRegion (A :: (us ++ B :: vs)) A := Extreme.corner_region h (by simp)
      have hB : ConvexRegion (A :: (us ++ B :: vs)) B := Extreme.corner_region h (by simp)
      have hXr : ConvexRegion (A :: (us ++ B :: vs)) X := by
        rcases hX with e | e | hb
        · exact e ▸ hA
        · exact e ▸ hB
        · exact convex_region_between h hA hB hb
      have hXL : OnLine X L := LoopFacts.onFiniteLine_onLine hX hAL hBL
      exact ⟨⟨hXr, Or.inl hXL⟩, hXr, Or.inl hXL⟩

/-- The convex fan has the same sum from any starting corner. -/
theorem fanSum_rotateLeft {cs : List Point} (h : ConvexOutline cs) (n : Nat) :
    fanSum (cs.rotateLeft n) = fanSum cs := by
  /- A rotation moves a first run of the corners to the end, which preserves the fan's sum
  (`Extreme.fanSum_rotate_prefix`, from `fanSum_rotate` one corner at a time). -/
  unfold List.rotateLeft
  dsimp only
  split
  · rfl
  · have he := List.take_append_drop (n % cs.length) cs
    rw [← he] at h
    exact (Extreme.fanSum_rotate_prefix _ _ h).trans (congrArg fanSum he)

end Elements.Figures
