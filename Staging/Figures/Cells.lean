import Staging.Figures.Convex
import Staging.Figures.Avoid
import Staging.Figures.ExtHelpers
import Staging.Figures.CutHelpers

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
  let P : ConvexCell := ⟨[A, B, C], Ext.triangle_outline h⟩
  refine ⟨P, rfl, ?_, ?_⟩
  · intro X
    simpa [P, ConvexCell.region, Covers, fan, segments] using
      (fan_covers (Ext.triangle_outline h) X).symm
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
    rw [cut_fan_close, area_acb A (endOf B ps) A, area_degenerate, add_zero]
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
        have hi := ih D (cut_remove_third h)
        change △ X B C + (△ X C D + fanSum (X :: ((D :: ps) ++ [A]))) =
          △ A B C + (△ A C D + fanSum (A :: D :: ps))
        rw [← add_assoc, cut_boundary_flip h hX, add_assoc]
        change △ B C D + fanSum (X :: ((B :: D :: ps) ++ [A])) = _
        rw [hi, cut_fan_cons A B D ps, ← add_assoc, ← cut_vertex_flip h, add_assoc]

/-- **The corners of a cell are its region's extreme points**: the points of the region on
no finite straight line between two other points of it. -/
theorem convex_extreme_iff (P : ConvexCell) (X : Point) :
    (P.region X ∧ ∀ A B : Point, P.region A → P.region B → ¬ Between A X B) ↔
      X ∈ P.corners := by
  classical
  constructor
  · rintro ⟨hX, he⟩
    apply Classical.byContradiction
    intro hn
    obtain ⟨A, B, hA, hB, hb⟩ := Ext.noncorner_segment P.convex hX hn
    exact he A B hA hB hb
  · intro hX
    exact ⟨Ext.corner_region P.convex hX, fun _ _ hA hB =>
      Ext.corner_not_between P.convex hX hA hB⟩

/-- **A cell's area depends only on its region**: two cells whose regions agree off finitely
many straight lines have the same area. -/
theorem convex_area_ext (P Q : ConvexCell) (h : AgreeOff P.region Q.region) :
    P.area = Q.area := by
  obtain ⟨ls, hls⟩ := h
  have hr : ∀ X, P.region X ↔ Q.region X := by
    intro X
    exact ⟨Ext.region_inclusion P.convex ls (fun Y hy => (hls Y hy).mp) X,
      Ext.region_inclusion Q.convex ls (fun Y hy => (hls Y hy).mpr) X⟩
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
      have hq' : ConvexOutline (A :: (vs ++ us)) := Ext.convex_rotate_prefix us (A :: vs) hq
      have hm' : ∀ X, X ∈ A :: B :: ps ↔ X ∈ A :: (vs ++ us) := by
        intro X
        exact (hm X).trans (by simp only [List.mem_append, List.mem_cons, or_comm, or_left_comm])
      rcases Ext.head_order_unique hp hq' hm' with he | he
      · calc
          fanSum (A :: B :: ps) = fanSum (A :: (vs ++ us)) := congrArg fanSum he
          _ = fanSum (us ++ A :: vs) := Ext.fanSum_rotate_prefix us (A :: vs) hq
      · calc
          fanSum (A :: B :: ps) = fanSum (A :: (vs ++ us).reverse) := congrArg fanSum he
          _ = fanSum ((vs ++ us).reverse ++ [A]) :=
            Ext.fanSum_rotate_prefix (vs ++ us).reverse [A] (by simpa using hq'.reverse)
          _ = fanSum (A :: (vs ++ us)) := by simpa using fanSum_reverse hq'
          _ = fanSum (us ++ A :: vs) := Ext.fanSum_rotate_prefix us (A :: vs) hq

/-- `U` and `V` are what the straight line `L` leaves of the cell `P`, the one on `A`'s side
and the other on `B`'s, in either order, and together they make up `P` exactly. -/
def CutPieces (P : ConvexCell) (L : Line) (A B : Point) (U V : ConvexCell) : Prop :=
  (Clips P L A (some U) ∧ Clips P L B (some V) ∧
      ∀ X : Point, P.region X ↔ cellRegion (some U) X ∨ cellRegion (some V) X) ∨
    (Clips P L A (some V) ∧ Clips P L B (some U) ∧
      ∀ X : Point, P.region X ↔ cellRegion (some V) X ∨ cellRegion (some U) X)

/-- **The pieces of a genuine cut**: a straight line with corners of the cell strictly on
both sides of it cuts the cell corner to corner, corner to side, or side to side; read from
the first crossing, the outline splits into two chains, and each, closed by the cut, is the
outline of a cell on one side. Its proof is due (route C1). -/
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
  sorry

/-- **A straight cut**: a straight line cuts a cell into what is left on each side of it,
which together make up the cell exactly, and whose areas make up its area. -/
theorem convex_cut (P : ConvexCell) {L : Line} {A B : Point} (hAB : OppositeSides A B L) :
    ∃ U V : Cell, Clips P L A U ∧ Clips P L B V ∧
      (∀ X : Point, P.region X ↔ cellRegion U X ∨ cellRegion V X) ∧
      P.area = cellArea U + cellArea V := by
  classical
  have whole {R S : Point} (hrs : OppositeSides R S L)
      (hc : ∀ C ∈ P.corners, Half C R L) :
      Clips P L R (some P) ∧ Clips P L S none := by
    have side {X : Point} (hx : P.region X) : Half X R L :=
      cut_region_half P.convex hc hx
    have core_side {X : Point} (hx : P.core X) : SameSide X R L := by
      obtain ⟨C, D, E, hi, ht⟩ := cut_core_neighbourhood hx
      have hc : OnOrInsideTriangle C C D E := by simp [OnOrInsideTriangle]
      have hd : OnOrInsideTriangle D C D E := by simp [OnOrInsideTriangle]
      have he : OnOrInsideTriangle E C D E := by simp [OnOrInsideTriangle]
      exact cut_inside_closed_half (side (ht C hc)) (side (ht D hd)) (side (ht E he)) hi
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
    exact ⟨some P, none, hu, hv, fun _ => by simp [cellRegion], (add_zero P.area).symm⟩
  have hBA : OppositeSides B A L :=
    ⟨hAB.2.1, hAB.1, fun hs => hAB.2.2 (same_side_symm hs)⟩
  by_cases hB : ∀ C ∈ P.corners, Half C B L
  · obtain ⟨hv, hu⟩ := whole hBA hB
    refine ⟨none, some P, hu, hv, fun _ => by simp [cellRegion], ?_⟩
    change P.area = 0 + P.area
    rw [add_comm, add_zero]
  let good (U V : Cell) : Prop := Clips P L A U ∧ Clips P L B V ∧
    (∀ X : Point, P.region X ↔ cellRegion U X ∨ cellRegion V X)
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
    have he := cut_fan_rotate_append pre post (hp ▸ P.convex)
    simpa only [ConvexCell.area, ← hp] using he.symm
  have finish (U V : ConvexCell) (hg : fits U V) (ha : P.area = U.area + V.area) :
      ∃ U V : Cell, Clips P L A U ∧ Clips P L B V ∧
        (∀ X : Point, P.region X ↔ cellRegion U X ∨ cellRegion V X) ∧
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
      hr ▸ cut_convex_rotate_append pre post (hp ▸ P.convex)
    apply finish U V hg
    change P.area = fanSum U.corners + fanSum V.corners
    rw [rotate pre post hp, hr, hu, hv,
      ← boundary_fan_sum hc (Or.inr (Or.inr hx)), hchain]
    simp only [List.cons_append, List.append_assoc]
    rw [← fan_insert_between (O := X) us (vs ++ [E]) hy]
    simpa only [List.cons_append, List.append_assoc, List.nil_append] using
      cut_fan_split X Y (us ++ [C]) (D :: vs ++ [E])

/-- **The common part of two cells** is a cell, or has no inside. -/
theorem convex_intersection (P Q : ConvexCell) : ∃ C : Cell, Intersection P Q C := by
  sorry

/-- **Content for cells**: cells that tile a cell have its area together. -/
theorem convex_tiles_area (P : ConvexCell) (qs : List ConvexCell) (h : Tiles P qs) :
    Magnitude.sum (qs.map ConvexCell.area) = P.area := by
  sorry

end Elements.Figures
