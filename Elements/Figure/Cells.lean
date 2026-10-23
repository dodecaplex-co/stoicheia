import Elements.Foundations.Figures
import Elements.Figure.Basics
import Elements.Figure.Rectilineal
import Elements.Figure.Convex.Avoid
import Elements.Figure.Cells.ExtHelpers
import Elements.Figure.Cells.CutHelpers
import Elements.Figure.Cells.CutPieces
import Elements.Figure.Cells.CellFacts
import Elements.Figure.Lists

/-!
# Book Zero: convex cells, and cutting them

Steps B0, B5, B6 and C1 to C3 of brief 0013's route to its content theorem: the convex-cut
induction of section 8, route (b), after David Hilbert's theory of content. The words are in
`Foundations/Figures.lean`. A convex cell is a convex outline taken as a piece of a figure
(`ConvexCell`); its area is its fan's sum, which does not depend on the corner the fan is
drawn from (`fanSum_rotate`).

* **B0.** A triangle is a cell, with the same region and area (`triangle_cell`).
* **B5.** A corner put in on a side, or a fan drawn from a point of a side, leaves the fan's
  sum as it was (`fan_insert_between`, `boundary_fan_sum`).
* **B6.** The corners of a cell are its region's extreme points, so a cell's area depends
  only on its region (`convex_extreme_iff`, `convex_area_ext`).
* **C1.** A straight line cuts a cell into at most two cells, which make up the cell and
  whose areas make up its area (`convex_cut`); a cell may be cut down to nothing, or to a
  segment or a point, which has no inside, and then it is `none`. A genuine cut's pieces are
  `convex_cut_pieces`, from the helpers of `Cells/CutPieces.lean`. Where the cutting line
  crosses a side, it crosses strictly within it, a crossing at a corner being a case of its
  own; so the cut puts such a crossing in as a corner and measures by the library's
  `area_cut`, for a point strictly between two others, not by A4's `area_cut_closed`
  (brief 0013, section 8, "The routes taken", C1).
* **C3 and C2.** The section after the cut clips cells by half-planes, for the common part of
  two cells (`convex_intersection`) and for cells that tile a cell (`convex_tiles_area`).

Two regions that agree at every point off finitely many straight lines are said to agree off
them (`AgreeOff`): a cut's pieces are pinned exactly by their insides, and up to finitely many
lines by their regions. The theorems about outlines that rest on them are exact.

Nothing in Book Zero cites a proposition of the *Elements*.
-/

namespace Elements.Figures

open Tacit

/-- **A triangle is a cell**, with the same region and the same area. -/
theorem triangle_cell {A B C : Point} (h : Triangle A B C) :
    ∃ P : ConvexCell, P.corners = [A, B, C] ∧
      (∀ X : Point, P.Region X ↔ OnOrInsideTriangle X A B C) ∧ P.area = △ A B C := by
  let P : ConvexCell := ⟨[A, B, C], Extreme.triangle_outline h⟩
  refine ⟨P, rfl, ?_, ?_⟩
  · intro X
    simpa [P, ConvexCell.Region, Covers, fan, segments] using
      (fan_covers (Extreme.triangle_outline h) X).symm
  · change Magnitude.sum [△ A B C] = △ A B C
    exact Magnitude.sum_singleton _

/-- A corner put in between two corners next to each other, on the straight line joining
them, does not change a fan's sum. -/
theorem fan_insert_between {O A B X : Point} (us vs : List Point) (h : Between A X B) :
    fanSum (O :: (us ++ A :: X :: B :: vs)) = fanSum (O :: (us ++ A :: B :: vs)) := by
  induction us with
  | nil =>
    change △ O A X + (△ O X B + fanSum (O :: B :: vs)) =
      △ O A B + fanSum (O :: B :: vs)
    rw [← add_assoc, area_cut h]
  | cons C us ih =>
    cases us with
    | nil =>
      change △ O C A + fanSum (O :: A :: X :: B :: vs) =
        △ O C A + fanSum (O :: A :: B :: vs)
      exact congrArg (fun z => △ O C A + z) ih
    | cons D us =>
      change △ O C D + fanSum (O :: (D :: us ++ A :: X :: B :: vs)) =
        △ O C D + fanSum (O :: (D :: us ++ A :: B :: vs))
      exact congrArg (fun z => △ O C D + z) ih

/-- **A fan from a point of a side**: a convex outline's fan from a point of its first side
has the fan's sum from its first corner. -/
theorem boundary_fan_sum {A B X : Point} {ps : List Point}
    (h : ConvexOutline (A :: B :: ps)) (hX : OnFiniteLine X A B) :
    fanSum (X :: ((B :: ps) ++ [A])) = fanSum (A :: B :: ps) := by
  rcases hX with hX | hX | hX
  · subst X
    rw [fanSum_cons, fanSum_cons, fanArea_append, area_acb A (endOf B ps) A, area_degenerate,
      add_zero]
  · subst X
    change fanSum (B :: B :: (ps ++ [A])) = _
    rw [cut_fan_repeat]
    exact fanSum_rotate h
  · cases ps with
    | nil => have := h.1; simp at this
    | cons C ps =>
      induction ps generalizing C with
      | nil =>
        have hc := area_cut (A := C) hX
        simp only [List.cons_append, List.nil_append, fanSum, fan, segments,
          List.map_cons, List.map_nil, Magnitude.sum, add_zero] at *
        rw [area_cab X B C, area_bca X C A, area_cab A B C, add_comm]
        exact hc
      | cons D ps ih =>
        have hi := ih D h.erase_third
        change △ X B C + (△ X C D + fanSum (X :: ((D :: ps) ++ [A]))) =
          △ A B C + (△ A C D + fanSum (A :: D :: ps))
        rw [← add_assoc, cut_boundary_flip h hX, add_assoc]
        change △ B C D + fanSum (X :: ((B :: D :: ps) ++ [A])) = _
        rw [hi, cut_fan_cons A B D ps, ← add_assoc, ← cut_vertex_flip h, add_assoc]

/-- **The corners of a cell are its region's extreme points**: the points of the region on
no finite straight line between two other points of it. -/
theorem convex_extreme_iff (P : ConvexCell) (X : Point) :
    (P.Region X ∧ ∀ A B : Point, P.Region A → P.Region B → ¬ Between A X B) ↔
      X ∈ P.corners := by
  classical
  constructor
  · rintro ⟨hX, he⟩
    apply Classical.byContradiction
    intro hn
    obtain ⟨A, B, hA, hB, hb⟩ := Extreme.noncorner_segment P.convex hX hn
    exact he A B hA hB hb
  · intro hX
    exact ⟨Extreme.corner_region P.convex hX, fun _ _ hA hB =>
      Extreme.corner_not_between P.convex hX hA hB⟩

/-- **A cell's area depends only on its region**: two cells whose regions agree off finitely
many straight lines have the same area. -/
theorem convex_area_ext (P Q : ConvexCell) (h : AgreeOff P.Region Q.Region) :
    P.area = Q.area := by
  obtain ⟨ls, hls⟩ := h
  have hr : ∀ X, P.Region X ↔ Q.Region X := by
    intro X
    exact ⟨Extreme.region_inclusion P.convex ls (fun Y hy => (hls Y hy).mp) X,
      Extreme.region_inclusion Q.convex ls (fun Y hy => (hls Y hy).mpr) X⟩
  have hm : ∀ X, X ∈ P.corners ↔ X ∈ Q.corners := by
    intro X
    constructor
    · intro hx
      obtain ⟨hp, he⟩ := (convex_extreme_iff P X).mpr hx
      exact (convex_extreme_iff Q X).mp ⟨(hr X).mp hp,
        fun A B ha hb => he A B ((hr A).mpr ha) ((hr B).mpr hb)⟩
    · intro hx
      obtain ⟨hq, he⟩ := (convex_extreme_iff Q X).mpr hx
      exact (convex_extreme_iff P X).mp ⟨(hr X).mpr hq,
        fun A B ha hb => he A B ((hr A).mp ha) ((hr B).mp hb)⟩
  have hp := P.convex
  have hq := Q.convex
  change fanSum P.corners = fanSum Q.corners
  generalize heP : P.corners = ps at hp hm ⊢
  generalize heQ : Q.corners = qs at hq hm ⊢
  cases ps with
  | nil => have := hp.1; simp at this
  | cons A ps =>
    cases ps with
    | nil => have := hp.1; simp at this
    | cons B ps =>
      obtain ⟨us, vs, rfl⟩ := List.mem_iff_append.mp ((hm A).mp (by simp))
      have hq' : ConvexOutline (A :: (vs ++ us)) := Extreme.convex_rotate_prefix us (A :: vs) hq
      have hm' : ∀ X, X ∈ A :: B :: ps ↔ X ∈ A :: (vs ++ us) := by
        intro X
        exact (hm X).trans (by simp only [List.mem_append, List.mem_cons, or_comm, or_left_comm])
      rcases Extreme.head_order_unique hp hq' hm' with he | he
      · calc
          fanSum (A :: B :: ps) = fanSum (A :: (vs ++ us)) := congrArg fanSum he
          _ = fanSum (us ++ A :: vs) := Extreme.fanSum_rotate_prefix us (A :: vs) hq
      · calc
          fanSum (A :: B :: ps) = fanSum (A :: (vs ++ us).reverse) := congrArg fanSum he
          _ = fanSum ((vs ++ us).reverse ++ [A]) :=
            Extreme.fanSum_rotate_prefix (vs ++ us).reverse [A] (by simpa using hq'.reverse)
          _ = fanSum (A :: (vs ++ us)) := by simpa using fanSum_reverse hq'
          _ = fanSum (us ++ A :: vs) := Extreme.fanSum_rotate_prefix us (A :: vs) hq

/-- A piece of a cell's outline on R's side of a straight line is what the line leaves of
the cell there. -/
theorem clips_of_piece {P Q : ConvexCell} {L : Line} {R : Point}
    (h : Pieces.IsPiece P.corners L R Q.corners) : Clips P L R (some Q) :=
  ⟨fun X => h.2.2 X, ⟨[], fun X _ => h.2.1 X⟩⟩

/-- Two pieces of a cell's outline, one on each side of a straight line, are the cells of
the cut, and together they make up the cell exactly. -/
theorem cut_pieces_of_lists (P : ConvexCell) {L : Line} {A B : Point}
    (hAB : OppositeSides A B L) {qs rs : List Point}
    (h : (Pieces.IsPiece P.corners L A qs ∧ Pieces.IsPiece P.corners L B rs) ∨
      (Pieces.IsPiece P.corners L B qs ∧ Pieces.IsPiece P.corners L A rs)) :
    ∃ U V : ConvexCell, U.corners = qs ∧ V.corners = rs ∧ CutPieces P L A B U V := by
  have cover {S T : ConvexCell} (hS : Pieces.IsPiece P.corners L A S.corners)
      (hT : Pieces.IsPiece P.corners L B T.corners) (X : Point) :
      P.Region X ↔ CellRegion (some S) X ∨ CellRegion (some T) X := by
    change ConvexRegion P.corners X ↔ ConvexRegion S.corners X ∨ ConvexRegion T.corners X
    rw [hS.2.1 X, hT.2.1 X]
    constructor
    · intro hX
      by_cases hon : OnLine X L
      · exact Or.inl ⟨hX, Or.inl hon⟩
      rcases Pieces.side_cases hAB hon with hs | hs
      · exact Or.inl ⟨hX, Or.inr hs⟩
      · exact Or.inr ⟨hX, Or.inr hs⟩
    · rintro (hX | hX) <;> exact hX.1
  rcases h with ⟨hq, hr⟩ | ⟨hq, hr⟩
  · let U : ConvexCell := ⟨qs, hq.1⟩
    let V : ConvexCell := ⟨rs, hr.1⟩
    exact ⟨U, V, rfl, rfl, Or.inl ⟨clips_of_piece (Q := U) hq, clips_of_piece (Q := V) hr,
      cover (S := U) (T := V) hq hr⟩⟩
  · let U : ConvexCell := ⟨qs, hq.1⟩
    let V : ConvexCell := ⟨rs, hr.1⟩
    exact ⟨U, V, rfl, rfl, Or.inr ⟨clips_of_piece (Q := V) hr, clips_of_piece (Q := U) hq,
      cover (S := V) (T := U) hr hq⟩⟩

/-- **The pieces of a genuine cut**: a straight line with corners of the cell strictly on
both sides of it cuts the cell corner to corner, corner to side, or side to side; read from
the first crossing, the outline splits into two chains, and each, closed by the cut, is the
outline of a cell on one side. It is proved by route C1, from the helpers of
`Cells/CutPieces.lean`. -/
theorem convex_cut_pieces (P : ConvexCell) {L : Line} {A B : Point}
    (hAB : OppositeSides A B L) (hA : ¬ ∀ C ∈ P.corners, Half C A L)
    (hB : ¬ ∀ C ∈ P.corners, Half C B L) :
    (∃ (pre post us vs : List Point) (X Y : Point) (U V : ConvexCell),
      P.corners = pre ++ post ∧ post ++ pre = X :: (us ++ Y :: vs) ∧
      U.corners = X :: (us ++ [Y]) ∧ V.corners = X :: Y :: vs ∧ CutPieces P L A B U V) ∨
    (∃ (pre post us vs : List Point) (X C D Y : Point) (U V : ConvexCell),
      P.corners = pre ++ post ∧ post ++ pre = X :: (us ++ C :: D :: vs) ∧
      Between C Y D ∧ U.corners = X :: (us ++ [C, Y]) ∧
      V.corners = X :: Y :: D :: vs ∧ CutPieces P L A B U V) ∨
    (∃ (pre post ps us vs : List Point) (E F C D X Y : Point) (U V : ConvexCell),
      P.corners = pre ++ post ∧ post ++ pre = E :: F :: ps ∧
      F :: ps = us ++ C :: D :: vs ∧ Between E X F ∧ Between C Y D ∧
      U.corners = X :: (us ++ [C, Y]) ∧
      V.corners = X :: Y :: (D :: vs ++ [E]) ∧ CutPieces P L A B U V) := by
  rcases Pieces.cut_lists P.convex hAB hA hB with
    ⟨pre, post, us, vs, X, Y, hp, hr, hs⟩ |
    ⟨pre, post, us, vs, X, C, D, Y, hp, hr, hy, hs⟩ |
    ⟨pre, post, ps, us, vs, E, F, C, D, X, Y, hp, hr, hc, hx, hy, hs⟩
  · obtain ⟨U, V, hU, hV, hcut⟩ := cut_pieces_of_lists P hAB hs
    exact Or.inl ⟨pre, post, us, vs, X, Y, U, V, hp, hr, hU, hV, hcut⟩
  · obtain ⟨U, V, hU, hV, hcut⟩ := cut_pieces_of_lists P hAB hs
    exact Or.inr (Or.inl ⟨pre, post, us, vs, X, C, D, Y, U, V, hp, hr, hy, hU, hV, hcut⟩)
  · obtain ⟨U, V, hU, hV, hcut⟩ := cut_pieces_of_lists P hAB hs
    exact Or.inr (Or.inr ⟨pre, post, ps, us, vs, E, F, C, D, X, Y, U, V, hp, hr, hc, hx, hy,
      hU, hV, hcut⟩)

/-- **A straight cut**: a straight line cuts a cell into what is left on each side of it,
which together make up the cell exactly, and whose areas make up its area. -/
theorem convex_cut (P : ConvexCell) {L : Line} {A B : Point} (hAB : OppositeSides A B L) :
    ∃ U V : Cell, Clips P L A U ∧ Clips P L B V ∧
      (∀ X : Point, P.Region X ↔ CellRegion U X ∨ CellRegion V X) ∧
      P.area = cellArea U + cellArea V := by
  classical
  have whole {R S : Point} (hrs : OppositeSides R S L)
      (hc : ∀ C ∈ P.corners, Half C R L) :
      Clips P L R (some P) ∧ Clips P L S none := by
    have side {X : Point} (hx : P.Region X) : Half X R L :=
      cut_region_half P.convex hc hx
    have core_side {X : Point} (hx : P.Core X) : SameSide X R L := by
      obtain ⟨C, D, E, hi, ht⟩ := cut_core_neighbourhood hx
      have hC : OnOrInsideTriangle C C D E := by simp [OnOrInsideTriangle]
      have hD : OnOrInsideTriangle D C D E := by simp [OnOrInsideTriangle]
      have hE : OnOrInsideTriangle E C D E := by simp [OnOrInsideTriangle]
      exact cut_inside_closed_half (side (ht C hC)) (side (ht D hD)) (side (ht E hE)) hi
    have no_other {X : Point} (hr : SameSide X R L) (hs : SameSide X S L) : False :=
      hrs.2.2 (same_side_trans hr hs)
    constructor
    · constructor
      · intro X
        exact ⟨fun hx => ⟨hx, core_side hx⟩, fun hx => hx.1⟩
      · refine ⟨[], fun X _ => ?_⟩
        exact ⟨fun hx => ⟨hx, side hx⟩, fun hx => hx.1⟩
    · constructor
      · intro X
        exact ⟨False.elim, fun hx => no_other (core_side hx.1) hx.2⟩
      · refine ⟨[L], fun X hx => ⟨False.elim, ?_⟩⟩
        have hoff := hx L (List.mem_cons_self ..)
        rintro ⟨hr, hs⟩
        exact no_other ((side hr).resolve_left hoff) (hs.resolve_left hoff)
  /- No crossing, touching at a corner, or lying along a supporting side: when
  every corner is on one closed side, keep the whole cell there. The opposite
  piece has no interior. Its missing boundary lies on L, as AgreeOff permits;
  the retained whole cell gives exact combined coverage. -/
  by_cases hA : ∀ C ∈ P.corners, Half C A L
  · obtain ⟨hu, hv⟩ := whole hAB hA
    exact ⟨some P, none, hu, hv, fun _ => by simp [CellRegion], (add_zero P.area).symm⟩
  have hBA : OppositeSides B A L :=
    ⟨hAB.2.1, hAB.1, fun hs => hAB.2.2 (same_side_symm hs)⟩
  by_cases hB : ∀ C ∈ P.corners, Half C B L
  · obtain ⟨hv, hu⟩ := whole hBA hB
    refine ⟨none, some P, hu, hv, fun _ => by simp [CellRegion], ?_⟩
    change P.area = 0 + P.area
    rw [add_comm, add_zero]
  let good (U V : Cell) : Prop := Clips P L A U ∧ Clips P L B V ∧
    (∀ X : Point, P.Region X ↔ CellRegion U X ∨ CellRegion V X)
  let fits (U V : ConvexCell) : Prop :=
    good (some U) (some V) ∨ good (some V) (some U)
  /- A genuine cut: its two pieces, by `convex_cut_pieces`. -/
  have geometry :
      (∃ (pre post us vs : List Point) (X Y : Point) (U V : ConvexCell),
        P.corners = pre ++ post ∧ post ++ pre = X :: (us ++ Y :: vs) ∧
        U.corners = X :: (us ++ [Y]) ∧ V.corners = X :: Y :: vs ∧ fits U V) ∨
      (∃ (pre post us vs : List Point) (X C D Y : Point) (U V : ConvexCell),
        P.corners = pre ++ post ∧ post ++ pre = X :: (us ++ C :: D :: vs) ∧
        Between C Y D ∧ U.corners = X :: (us ++ [C, Y]) ∧
        V.corners = X :: Y :: D :: vs ∧ fits U V) ∨
      (∃ (pre post ps us vs : List Point) (E F C D X Y : Point) (U V : ConvexCell),
        P.corners = pre ++ post ∧ post ++ pre = E :: F :: ps ∧
        F :: ps = us ++ C :: D :: vs ∧ Between E X F ∧ Between C Y D ∧
        U.corners = X :: (us ++ [C, Y]) ∧
        V.corners = X :: Y :: (D :: vs ++ [E]) ∧ fits U V) :=
    convex_cut_pieces P hAB hA hB
  have rotate (pre post : List Point) (hp : P.corners = pre ++ post) :
      P.area = fanSum (post ++ pre) := by
    have he := Extreme.fanSum_rotate_prefix pre post (hp ▸ P.convex)
    simpa only [ConvexCell.area, ← hp] using he.symm
  have finish (U V : ConvexCell) (hg : fits U V) (ha : P.area = U.area + V.area) :
      ∃ U V : Cell, Clips P L A U ∧ Clips P L B V ∧
        (∀ X : Point, P.Region X ↔ CellRegion U X ∨ CellRegion V X) ∧
        P.area = cellArea U + cellArea V := by
    rcases hg with hg | hg
    · exact ⟨some U, some V, hg.1, hg.2.1, hg.2.2, ha⟩
    · exact ⟨some V, some U, hg.1, hg.2.1, hg.2.2, (by
        change P.area = V.area + U.area
        rw [add_comm]
        exact ha)⟩
  rcases geometry with hg | hg | hg
  · obtain ⟨pre, post, us, vs, X, Y, U, V, hp, hr, hu, hv, hg⟩ := hg
    apply finish U V hg
    change P.area = fanSum U.corners + fanSum V.corners
    rw [rotate pre post hp, hr, hu, hv]
    exact cut_fan_split X Y us vs
  · obtain ⟨pre, post, us, vs, X, C, D, Y, U, V, hp, hr, hy, hu, hv, hg⟩ := hg
    apply finish U V hg
    change P.area = fanSum U.corners + fanSum V.corners
    rw [rotate pre post hp, hr, hu, hv, ← fan_insert_between (O := X) us vs hy]
    simpa only [List.append_assoc, List.singleton_append] using
      cut_fan_split X Y (us ++ [C]) (D :: vs)
  · obtain ⟨pre, post, ps, us, vs, E, F, C, D, X, Y, U, V,
      hp, hr, hchain, hx, hy, hu, hv, hg⟩ := hg
    have hc : ConvexOutline (E :: F :: ps) :=
      hr ▸ Extreme.convex_rotate_prefix pre post (hp ▸ P.convex)
    apply finish U V hg
    change P.area = fanSum U.corners + fanSum V.corners
    rw [rotate pre post hp, hr, hu, hv,
      ← boundary_fan_sum hc (Or.inr (Or.inr hx)), hchain]
    simp only [List.cons_append, List.append_assoc]
    rw [← fan_insert_between (O := X) us (vs ++ [E]) hy]
    simpa only [List.cons_append, List.append_assoc, List.nil_append] using
      cut_fan_split X Y (us ++ [C]) (D :: vs ++ [E])

/-! ## Clipping cells, and cells that tile a cell

Helpers for `convex_intersection` and `convex_tiles_area`. A cell or nothing is cut by a
straight line as `convex_cut` cuts a cell. Clipping a cell by the half-planes of another's
sides, one after another, leaves their common part. For content, the cell and every tile are
cut by the sides of one tile, Q, one side after another (brief 0013, section 8, "Content",
step 4): what lies beyond a side has lost Q, and so has fewer tiles; what lies within all of
them has only Q, since the other tiles' insides are apart from Q's. Pieces are pinned
exactly by their insides, and up to finitely many straight lines by their regions. -/

namespace Tiling

/-- Regions that agree at every point agree off finitely many straight lines. -/
theorem agreeOff_of_iff {U V : Point → Prop} (h : ∀ X : Point, U X ↔ V X) : AgreeOff U V :=
  ⟨[], fun X _ => h X⟩

/-- Agreeing off finitely many straight lines, read the other way. -/
theorem agreeOff_symm {U V : Point → Prop} (h : AgreeOff U V) : AgreeOff V U := by
  obtain ⟨ls, h⟩ := h
  exact ⟨ls, fun X hX => (h X hX).symm⟩

/-- Agreeing off finitely many straight lines, twice: off both lists, the first region and
the last agree. -/
theorem agreeOff_trans {U V W : Point → Prop} (h₁ : AgreeOff U V) (h₂ : AgreeOff V W) :
    AgreeOff U W := by
  obtain ⟨l₁, h₁⟩ := h₁
  obtain ⟨l₂, h₂⟩ := h₂
  exact ⟨l₁ ++ l₂, fun X hX =>
    (h₁ X (CellFacts.avoid_left hX)).trans (h₂ X (CellFacts.avoid_right hX))⟩

/-- The common parts of regions that agree off finitely many straight lines agree off them. -/
theorem agreeOff_and {U U' V V' : Point → Prop} (h₁ : AgreeOff U U') (h₂ : AgreeOff V V') :
    AgreeOff (fun X => U X ∧ V X) (fun X => U' X ∧ V' X) := by
  obtain ⟨l₁, h₁⟩ := h₁
  obtain ⟨l₂, h₂⟩ := h₂
  exact ⟨l₁ ++ l₂, fun X hX =>
    and_congr (h₁ X (CellFacts.avoid_left hX)) (h₂ X (CellFacts.avoid_right hX))⟩

/-- Finitely many pairs of regions, each agreeing off finitely many straight lines: their
unions agree off all those lines. -/
theorem agreeOff_exists_mem {α : Type} :
    ∀ (l : List α) {F G : α → Point → Prop}, (∀ a ∈ l, AgreeOff (F a) (G a)) →
      AgreeOff (fun X => ∃ a ∈ l, F a X) (fun X => ∃ a ∈ l, G a X)
  | [], _, _, _ => agreeOff_of_iff fun X => by simp
  | a :: l, F, G, h => by
    obtain ⟨l₁, h₁⟩ := h a List.mem_cons_self
    obtain ⟨l₂, h₂⟩ := agreeOff_exists_mem l (fun b hb => h b (List.mem_cons_of_mem a hb))
    refine ⟨l₁ ++ l₂, fun X hX => ?_⟩
    show (∃ b ∈ a :: l, F b X) ↔ ∃ b ∈ a :: l, G b X
    rw [exists_mem_cons_iff, exists_mem_cons_iff]
    exact or_congr (h₁ X (CellFacts.avoid_left hX)) (h₂ X (CellFacts.avoid_right hX))

/-- A point inside a cell is in its region. -/
theorem core_region {P : ConvexCell} {X : Point} (h : P.Core X) : P.Region X :=
  fun s hs A hA hA₁ hA₂ => Or.inr (h s hs A hA hA₁ hA₂)

/-- **A cell's inside has a point off any finitely many straight lines.** -/
theorem core_avoiding (P : ConvexCell) (ls : List Line) : ∃ X : Point, Avoid ls X ∧ P.Core X :=
  CellFacts.core_point_avoiding P.convex ls

/-- A cell or nothing, with no inside, is nothing. -/
theorem eq_none_of_core {c : Cell} (h : ∀ X : Point, ¬ CellCore c X) : c = none := by
  cases c with
  | none => rfl
  | some P =>
    obtain ⟨X, -, hX⟩ := core_avoiding P []
    exact absurd hX (h X)

/-- A cell or nothing, whose region is empty off finitely many straight lines, is nothing. -/
theorem eq_none_of_region {c : Cell} (h : AgreeOff (CellRegion c) (fun _ => False)) :
    c = none := by
  cases c with
  | none => rfl
  | some P =>
    obtain ⟨ls, hls⟩ := h
    obtain ⟨X, hX, hc⟩ := core_avoiding P ls
    exact False.elim ((hls X hX).mp (core_region hc))

/-- **A cut of a cell or of nothing**: what a straight line leaves on each side, pinned as
`Clips` pins it, with their areas making up the whole. Nothing is cut into nothing and
nothing. -/
theorem cut_cell {L : Line} {A B : Point} (hAB : OppositeSides A B L) (c : Cell) :
    ∃ uv : Cell × Cell,
      (∀ X : Point, CellCore uv.1 X ↔ CellCore c X ∧ SameSide X A L) ∧
      AgreeOff (CellRegion uv.1) (fun X => CellRegion c X ∧ Half X A L) ∧
      (∀ X : Point, CellCore uv.2 X ↔ CellCore c X ∧ SameSide X B L) ∧
      AgreeOff (CellRegion uv.2) (fun X => CellRegion c X ∧ Half X B L) ∧
      cellArea c = cellArea uv.1 + cellArea uv.2 := by
  cases c with
  | none =>
    refine ⟨(none, none), fun X => ?_, agreeOff_of_iff fun X => ?_, fun X => ?_,
      agreeOff_of_iff fun X => ?_, (add_zero 0).symm⟩ <;>
    exact ⟨False.elim, fun h => h.1⟩
  | some P =>
    obtain ⟨U, V, hU, hV, -, ha⟩ := convex_cut P hAB
    exact ⟨(U, V), hU.1, hU.2, hV.1, hV.2, ha⟩

/-- A point on the other side of a straight line from a point off it. -/
theorem opposite_point {R : Point} {L : Line} (hR : ¬ OnLine R L) :
    ∃ B : Point, OppositeSides R B L := by
  obtain ⟨B, hB, -⟩ := exists_point_opposite_side hR []
  exact ⟨B, hB.2.1, hB.1, fun h => hB.2.2 (same_side_symm h)⟩

/-- **Clipping by finitely many half-planes**: what is left of a cell or of nothing, on the
side of each of finitely many straight lines towards a point off it, is pinned exactly by its
inside and, off finitely many straight lines, by its region. -/
theorem clip_cells (hs : List (Point × Line)) (hoff : ∀ p ∈ hs, ¬ OnLine p.1 p.2) (c : Cell) :
    ∃ C : Cell, (∀ X : Point, CellCore C X ↔ CellCore c X ∧ ∀ p ∈ hs, SameSide X p.1 p.2) ∧
      AgreeOff (CellRegion C) (fun X => CellRegion c X ∧ ∀ p ∈ hs, Half X p.1 p.2) := by
  induction hs generalizing c with
  | nil => exact ⟨c, fun X => by simp, agreeOff_of_iff fun X => by simp⟩
  | cons p hs ih =>
    obtain ⟨B, hAB⟩ := opposite_point (hoff p List.mem_cons_self)
    obtain ⟨⟨u, v⟩, hu, hur, -, -, -⟩ := cut_cell hAB c
    obtain ⟨C, hC, hCr⟩ := ih (fun q hq => hoff q (List.mem_cons_of_mem p hq)) u
    refine ⟨C, fun X => ?_, ?_⟩
    · rw [hC X, hu X, List.forall_mem_cons]
      exact and_assoc
    · refine agreeOff_trans hCr (agreeOff_trans (agreeOff_and hur (agreeOff_of_iff fun X =>
        Iff.rfl)) (agreeOff_of_iff fun X => ?_))
      rw [List.forall_mem_cons]
      exact and_assoc

/-- **One branch of a cut**: a region V made up, off finitely many straight lines, of U
and some cells; cut each, and V, by one closed half-plane H. Off finitely many straight
lines, what is left of V is made up of what is left of U and of the cells. -/
theorem agree_branch {U U' V V' H : Point → Prop} {ts : List Cell} {g : Cell → Cell}
    (hag : AgreeOff (fun X => U X ∨ ∃ t ∈ ts, CellRegion t X) V)
    (hu : AgreeOff U' (fun X => U X ∧ H X)) (hv : AgreeOff V' (fun X => V X ∧ H X))
    (hg : ∀ t ∈ ts, AgreeOff (CellRegion (g t)) (fun X => CellRegion t X ∧ H X)) :
    AgreeOff (fun X => U' X ∨ ∃ t ∈ ts.map g, CellRegion t X) V' := by
  obtain ⟨l₁, h₁⟩ := hag
  obtain ⟨l₂, h₂⟩ := hu
  obtain ⟨l₃, h₃⟩ := hv
  obtain ⟨l₄, h₄⟩ := agreeOff_exists_mem ts hg
  refine ⟨l₁ ++ (l₂ ++ (l₃ ++ l₄)), fun X hX => ?_⟩
  have e₁ := h₁ X (CellFacts.avoid_left hX)
  have e₂ := h₂ X (CellFacts.avoid_left (CellFacts.avoid_right hX))
  have e₃ := h₃ X (CellFacts.avoid_left (CellFacts.avoid_right (CellFacts.avoid_right hX)))
  have e₄ := h₄ X (CellFacts.avoid_right (CellFacts.avoid_right (CellFacts.avoid_right hX)))
  show (U' X ∨ ∃ t ∈ ts.map g, CellRegion t X) ↔ V' X
  rw [exists_mem_map_iff ts g (fun t => CellRegion t X), e₃]
  constructor
  · rintro (h | h)
    · obtain ⟨hU, hH⟩ := e₂.mp h
      exact ⟨e₁.mp (Or.inl hU), hH⟩
    · obtain ⟨t, ht, hr, hH⟩ := e₄.mp h
      exact ⟨e₁.mp (Or.inr ⟨t, ht, hr⟩), hH⟩
  · rintro ⟨hV, hH⟩
    rcases e₁.mpr hV with hU | ⟨t, ht, hr⟩
    · exact Or.inl (e₂.mpr ⟨hU, hH⟩)
    · exact Or.inr (e₄.mpr ⟨t, ht, hr, hH⟩)

/-- Cells and nothings, all of them nothing, that make up a cell or nothing off finitely many
straight lines: it is nothing too, and both areas are nothing. -/
theorem tiles_none {D : Cell} {ts : List Cell} (hall : ∀ t ∈ ts, t = none)
    (hag : AgreeOff (fun X => ∃ t ∈ ts, CellRegion t X) (CellRegion D)) :
    Magnitude.sum (ts.map cellArea) = cellArea D := by
  have hD : D = none := eq_none_of_region (agreeOff_trans (agreeOff_symm hag)
    (agreeOff_of_iff fun X => ⟨fun ⟨t, ht, hr⟩ => by rw [hall t ht] at hr; exact hr,
      False.elim⟩))
  rw [sum_eq_zero ts cellArea (fun t ht => by rw [hall t ht]; rfl), hD]
  rfl

/-- **The induction on one tile's sides** (brief 0013, section 8, "Content", step 4). A cell
or nothing D is made up, off finitely many straight lines, of a cell Q and a list of cells or
nothings, with no point inside two of them; a list of half-planes remains of Q's sides, Q's
inside is within all of them, and any of the list inside all of them is inside Q. Granted
content for at most m cells, where the list holds at most m, the area of D is that of Q with
the list. Cut everything by the first remaining side: beyond it Q is gone, and content for
at most m cells applies; within it, the induction goes on. When no side remains, the list
has no inside, and D is Q off finitely many straight lines. -/
theorem tiles_branch (m : Nat)
    (ih : ∀ (D : Cell) (ts : List Cell), (ts.filterMap id).length ≤ m →
      ts.Pairwise (fun a b => ∀ X : Point, CellCore a X → ¬ CellCore b X) →
      AgreeOff (fun X => ∃ t ∈ ts, CellRegion t X) (CellRegion D) →
      Magnitude.sum (ts.map cellArea) = cellArea D) :
    ∀ hs : List (Point × Line), (∀ p ∈ hs, ¬ OnLine p.1 p.2) →
    ∀ (D : Cell) (Q : ConvexCell) (ts : List Cell), (ts.filterMap id).length ≤ m →
      (∀ t ∈ ts, ∀ X : Point, Q.Core X → ¬ CellCore t X) →
      ts.Pairwise (fun a b => ∀ X : Point, CellCore a X → ¬ CellCore b X) →
      AgreeOff (fun X => Q.Region X ∨ ∃ t ∈ ts, CellRegion t X) (CellRegion D) →
      (∀ X : Point, Q.Core X → ∀ p ∈ hs, SameSide X p.1 p.2) →
      (∀ t ∈ ts, ∀ X : Point, CellCore t X → (∀ p ∈ hs, SameSide X p.1 p.2) → Q.Core X) →
      cellArea D = Q.area + Magnitude.sum (ts.map cellArea) := by
  intro hs
  induction hs with
  | nil =>
    intro _ D Q ts _ hQt _ hag _ hin
    /- No side remains: the other pieces have no inside, so they are nothing. -/
    have hnone : ∀ t ∈ ts, t = none := fun t ht =>
      eq_none_of_core fun X hX => hQt t ht X (hin t ht X hX (by simp)) hX
    have hsum : Magnitude.sum (ts.map cellArea) = 0 :=
      sum_eq_zero ts cellArea (fun t ht => by rw [hnone t ht]; rfl)
    have hQD : AgreeOff Q.Region (CellRegion D) := by
      refine agreeOff_trans (agreeOff_of_iff fun X => ⟨Or.inl, ?_⟩) hag
      rintro (h | ⟨t, ht, hr⟩)
      · exact h
      · rw [hnone t ht] at hr
        exact False.elim hr
    cases D with
    | none =>
      obtain ⟨ls, hls⟩ := hQD
      obtain ⟨X, hX, hc⟩ := core_avoiding Q ls
      exact False.elim ((hls X hX).mp (core_region hc))
    | some D =>
      rw [hsum, add_zero]
      exact (convex_area_ext Q D hQD).symm
  | cons p hs ih' =>
    intro hoff D Q ts hm hQt hpw hag hQin hin
    obtain ⟨B, hAB⟩ := opposite_point (hoff p List.mem_cons_self)
    obtain ⟨f, hf⟩ := Classical.axiomOfChoice (fun c : Cell => cut_cell hAB c)
    have hQside : ∀ X : Point, Q.Core X → SameSide X p.1 p.2 :=
      fun X hX => hQin X hX p List.mem_cons_self
    /- Nothing is cut into nothing. -/
    have hR0 : (f none).1 = none := eq_none_of_core fun X hX => (((hf none).1 X).mp hX).1
    have hB0 : (f none).2 = none := eq_none_of_core fun X hX => (((hf none).2.2.1 X).mp hX).1
    have hshR : ∀ (t : Cell) (X : Point), CellCore (f t).1 X → CellCore t X :=
      fun t X h => (((hf t).1 X).mp h).1
    have hshB : ∀ (t : Cell) (X : Point), CellCore (f t).2 X → CellCore t X :=
      fun t X h => (((hf t).2.2.1 X).mp h).1
    /- Q lies within the side: within, it keeps its inside; beyond, it is nothing. -/
    have hQR : ∀ X : Point, CellCore (f (some Q)).1 X ↔ Q.Core X := fun X =>
      ((hf (some Q)).1 X).trans ⟨fun h => h.1, fun h => ⟨h, hQside X h⟩⟩
    have hQB : (f (some Q)).2 = none := eq_none_of_core fun X hX => by
      obtain ⟨hq, hb⟩ := ((hf (some Q)).2.2.1 X).mp hX
      exact hAB.2.2 (same_side_trans (hQside X hq) hb)
    obtain ⟨Q', hQ'⟩ : ∃ Q' : ConvexCell, (f (some Q)).1 = some Q' := by
      cases hq : (f (some Q)).1 with
      | none =>
        obtain ⟨X, -, hX⟩ := core_avoiding Q []
        have hc := (hQR X).mpr hX
        rw [hq] at hc
        exact False.elim hc
      | some Q' => exact ⟨Q', rfl⟩
    have hQ'core : ∀ X : Point, Q'.Core X ↔ Q.Core X := fun X => by
      have hc := hQR X
      rw [hQ'] at hc
      exact hc
    /- Within the side: the induction on the remaining sides. -/
    have hagR : AgreeOff (fun X => Q'.Region X ∨ ∃ t ∈ ts.map (fun t => (f t).1),
        CellRegion t X) (CellRegion (f D).1) := by
      have hu : AgreeOff Q'.Region (fun X => Q.Region X ∧ Half X p.1 p.2) := by
        have hr := (hf (some Q)).2.1
        rw [hQ'] at hr
        exact hr
      exact agree_branch hag hu (hf D).2.1 (fun t _ => (hf t).2.1)
    have hR := ih' (fun q hq => hoff q (List.mem_cons_of_mem p hq)) (f D).1 Q'
      (ts.map fun t => (f t).1) (Nat.le_trans (count_map_le _ hR0 ts) hm)
      (by
        intro t ht X hX htX
        obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
        exact hQt t₀ ht₀ X ((hQ'core X).mp hX) (hshR t₀ X htX))
      (List.Pairwise.map _ (fun a b hab X ha hb => hab X (hshR a X ha) (hshR b X hb)) hpw)
      hagR
      (fun X hX q hq => hQin X ((hQ'core X).mp hX) q (List.mem_cons_of_mem p hq))
      (by
        intro t ht X htX hall
        obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
        obtain ⟨hc, hs⟩ := ((hf t₀).1 X).mp htX
        exact (hQ'core X).mpr (hin t₀ ht₀ X hc (List.forall_mem_cons.mpr ⟨hs, hall⟩)))
    /- Beyond the side: Q is gone, and content for fewer cells applies. -/
    have hagB : AgreeOff (fun X => ∃ t ∈ ts.map (fun t => (f t).2), CellRegion t X)
        (CellRegion (f D).2) := by
      have hb := agree_branch hag (hf (some Q)).2.2.2.1 (hf D).2.2.2.1
        (fun t _ => (hf t).2.2.2.1)
      rw [hQB] at hb
      exact agreeOff_trans (agreeOff_of_iff fun X =>
        ⟨Or.inr, fun h => h.elim (fun h => False.elim h) id⟩) hb
    have hB := ih (f D).2 (ts.map fun t => (f t).2)
      (Nat.le_trans (count_map_le _ hB0 ts) hm)
      (List.Pairwise.map _ (fun a b hab X ha hb => hab X (hshB a X ha) (hshB b X hb)) hpw)
      hagB
    /- The areas: each piece's area is what the side leaves of it on its two sides. -/
    have haQ : Q.area = Q'.area := by
      have ha := (hf (some Q)).2.2.2.2
      rw [hQ', hQB] at ha
      change Q.area = Q'.area + 0 at ha
      rw [add_zero] at ha
      exact ha
    have hts : Magnitude.sum (ts.map cellArea) =
        Magnitude.sum ((ts.map fun t => (f t).1).map cellArea) +
          Magnitude.sum ((ts.map fun t => (f t).2).map cellArea) := by
      rw [List.map_map, List.map_map, ← sum_map_add]
      exact congrArg Magnitude.sum (List.map_congr_left fun t _ => (hf t).2.2.2.2)
    rw [(hf D).2.2.2.2, hR, ← hB, hts, haQ, add_assoc]

/-- **Content for cells and nothings**, by induction on how many cells at most there are:
cells and nothings, no point inside two of them, that make up a cell or nothing off finitely
many straight lines, have its area together. -/
theorem tiles_cells : ∀ (m : Nat) (D : Cell) (ts : List Cell),
    (ts.filterMap id).length ≤ m →
    ts.Pairwise (fun a b => ∀ X : Point, CellCore a X → ¬ CellCore b X) →
    AgreeOff (fun X => ∃ t ∈ ts, CellRegion t X) (CellRegion D) →
    Magnitude.sum (ts.map cellArea) = cellArea D := by
  intro m
  induction m with
  | zero =>
    intro D ts hm _ hag
    exact tiles_none (all_none_of_count (Nat.le_zero.mp hm)) hag
  | succ m ih =>
    intro D ts hm hpw hag
    by_cases hall : ∀ t ∈ ts, t = none
    · exact tiles_none hall hag
    obtain ⟨pre, Q, post, rfl⟩ := split_some hall
    have hm' : ((pre ++ post).filterMap id).length ≤ m := by
      rw [count_split_some] at hm
      omega
    rw [List.pairwise_append, List.pairwise_cons] at hpw
    obtain ⟨hpre, ⟨hQpost, hpost⟩, hcross⟩ := hpw
    obtain ⟨hs, hoff, hcore, -⟩ := CellFacts.outline_halfplanes Q.convex
    have hag' : AgreeOff (fun X => Q.Region X ∨ ∃ t ∈ pre ++ post, CellRegion t X)
        (CellRegion D) := by
      refine agreeOff_trans (agreeOff_of_iff fun X => ?_) hag
      constructor
      · rintro (h | ⟨t, ht, hr⟩)
        · exact ⟨some Q, List.mem_append_right _ List.mem_cons_self, h⟩
        · rcases List.mem_append.mp ht with ht | ht
          · exact ⟨t, List.mem_append_left _ ht, hr⟩
          · exact ⟨t, List.mem_append_right _ (List.mem_cons_of_mem _ ht), hr⟩
      · rintro ⟨t, ht, hr⟩
        rcases List.mem_append.mp ht with ht | ht
        · exact Or.inr ⟨t, List.mem_append_left _ ht, hr⟩
        · rcases List.mem_cons.mp ht with rfl | ht
          · exact Or.inl hr
          · exact Or.inr ⟨t, List.mem_append_right _ ht, hr⟩
    have hb := tiles_branch m ih hs hoff D Q (pre ++ post) hm'
      (by
        intro t ht X hQX htX
        rcases List.mem_append.mp ht with ht | ht
        · exact hcross t ht (some Q) List.mem_cons_self X htX hQX
        · exact hQpost t ht X hQX htX)
      (List.pairwise_append.mpr ⟨hpre, hpost,
        fun a ha b hb => hcross a ha b (List.mem_cons_of_mem _ hb)⟩)
      hag' (fun X hX => (hcore X).mp hX) (fun _ _ X _ hX => (hcore X).mpr hX)
    rw [hb]
    simp only [List.map_append, List.map_cons, Magnitude.sum_append]
    change Magnitude.sum (pre.map cellArea) + (Q.area + Magnitude.sum (post.map cellArea)) =
      Q.area + (Magnitude.sum (pre.map cellArea) + Magnitude.sum (post.map cellArea))
    rw [← add_assoc, add_comm (Magnitude.sum (pre.map cellArea)) Q.area, add_assoc]

end Tiling

/-- **The common part of two cells** is a cell, or has no inside. -/
theorem convex_intersection (P Q : ConvexCell) : ∃ C : Cell, Intersection P Q C := by
  /- Clip P by the half-planes of Q's sides, one after another. -/
  obtain ⟨hs, hoff, hcore, hreg⟩ := CellFacts.outline_halfplanes Q.convex
  obtain ⟨C, hC, hCr⟩ := Tiling.clip_cells hs hoff (some P)
  exact ⟨C, fun X => (hC X).trans (and_congr_right fun _ => (hcore X).symm),
    Tiling.agreeOff_trans hCr
      (Tiling.agreeOff_of_iff fun X => and_congr_right fun _ => (hreg X).symm)⟩

/-- **Content for cells**: cells that tile a cell have its area together. -/
theorem convex_tiles_area (P : ConvexCell) (qs : List ConvexCell) (h : Tiles P qs) :
    Magnitude.sum (qs.map ConvexCell.area) = P.area := by
  /- Induction on a bound for the number of tiles present in a branch, through
  `Tiling.tiles_cells`: each tile is one cell present, to begin with. -/
  have hm : ((qs.map some).filterMap id).length ≤ qs.length := by
    rw [List.filterMap_map]
    exact List.length_filterMap_le _ _
  have hag : AgreeOff (fun X => ∃ t ∈ qs.map some, CellRegion t X) (CellRegion (some P)) :=
    Tiling.agreeOff_trans (Tiling.agreeOff_of_iff fun X =>
      exists_mem_map_iff qs some (fun t => CellRegion t X)) h.2
  have ha := Tiling.tiles_cells qs.length (some P) (qs.map some) hm
    (List.Pairwise.map some (fun _ _ hab => hab) h.1) hag
  rw [List.map_map] at ha
  exact ha

end Elements.Figures
