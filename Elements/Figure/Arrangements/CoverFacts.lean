import Elements.Figure.Outlines
import Elements.Figure.Cells
import Elements.Figure.Lists

/-!
# Book Zero: the cells of an arrangement that fill an outline

Helper lemmas, in the namespace `CoverFacts`, for `outline_cell_constant` and
`outline_cells_cover`, in `Arrangements.lean` (brief 0013, section 8, "The arrangement and
general division"; D9). The diagonal route, the extraction of an outline and the fan's
bridge beside I.45 use them too. Nothing in Book Zero cites a proposition of the *Elements*.

* **Along a finite straight line that meets no side** (`inside_of_segment`). If a finite
  straight line XZ meets no side of a simple loop, and its straight line passes through no
  corner, then X is inside the loop exactly when Z is: a good ray from Z through X, and its
  continuation from X, cross the same sides.
* **Across one side** (`inside_flip`). If the finite straight line meets the loop's boundary
  only at one point strictly within one side, the two ends disagree. Produce it beyond one end
  to Q: the good ray through Q from the end farther from Q crosses that side and every side
  the ray from the nearer end crosses, and no other.
* **A point of the boundary has filled points near it** (`boundary_filled`). Slide along a
  side from the point to a point M strictly within it, near the point and at no corner of any
  contour; there M is on that side alone, for two sides of one contour meet only at corners
  and two contours' boundaries only at corners. A short finite straight line through M,
  across that side, changes one contour's inside and no other's, so one of its ends is at odd
  depth. Brief 0013 (section 8, "The arrangement and general division") divides a small
  neighbourhood of a corner into sectors; here no sector at a corner need be examined.
* **A cell's region and its inside** (`cell_point`, `clear_of_cells`). A point of a cell's
  closed region off the figure's boundary has a point of the cell's inside that is inside the
  figure exactly when it is, reached along a short finite straight line that meets no side;
  and finitely many conditions, each holding at a point, keep away every cell whose closed
  region misses that point.

Natural numbers count sides, contours and crossings; they measure nothing.
-/

namespace Elements.Figures

open Tacit

namespace CoverFacts

/-! ## Rays along one straight line -/

/-- **Moving a ray's start forward along it.** With Y₂ between Y₁ and Q, if no point from Y₁
up to and including Y₂ lies strictly within a side, the rays from Y₁ and from Y₂ through Q
cross that side together or not at all. -/
theorem crosses_shift {Y₁ Y₂ Q : Point} {t : Point × Point} (h : Between Y₁ Y₂ Q)
    (hseg : ∀ U : Point, (U = Y₂ ∨ Between Y₁ U Y₂) → ¬ Between t.1 U t.2) :
    RayCrosses Y₁ Q t ↔ RayCrosses Y₂ Q t := by
  obtain ⟨ℓ, h1, hQ⟩ := Postulate1 Y₁ Q (ne_of_between_ends h)
  have h2 : OnLine Y₂ ℓ := on_line_of_between_ends h h1 hQ
  have hY12 : Y₁ ≠ Y₂ := ne_of_between h
  have hY2Q : Y₂ ≠ Q := (ne_of_between (between_symm h)).symm
  constructor
  · rintro ⟨U, hU, hUt⟩
    have hU2 : U ≠ Y₂ := fun e => hseg U (Or.inl e) hUt
    have hUℓ : OnLine U ℓ := hU.onLine h1 hQ
    refine ⟨U, ⟨hY2Q, hU2, ⟨ℓ, h2, hQ, hUℓ⟩, fun hb => ?_⟩, hUt⟩
    rcases between_cases hU.2.1 hY12 hU2 hUℓ h1 h2 with h' | h' | h'
    · exact hU.2.2.2 (between_of_between_right h' h)
    · exact hseg U (Or.inr h') hUt
    · exact not_between_of_between_between h' hb h
  · rintro ⟨U, hU, hUt⟩
    have hUℓ : OnLine U ℓ := hU.onLine h2 hQ
    have hU1 : U ≠ Y₁ := by
      intro e
      rw [e] at hU
      exact hU.2.2.2 h
    refine ⟨U, ⟨ne_of_between_ends h, hU1, ⟨ℓ, h1, hQ, hUℓ⟩, fun hb => ?_⟩, hUt⟩
    exact hU.2.2.2 (between_symm (between_of_between_left (between_symm hb) (between_symm h)))

/-- **Crossing one side on the way.** With M between Y₁ and Y₂, and Y₂ between Y₁ and Q, a
side through M whose end a is off the straight line is crossed by the ray from Y₁ through Q,
and not by the ray from Y₂, which meets that side's straight line only behind its start. -/
theorem crosses_once {Y₁ M Y₂ Q a b : Point} {ℓ : Line} (h : Between Y₁ Y₂ Q)
    (hM : Between Y₁ M Y₂) (h1 : OnLine Y₁ ℓ) (hQ : OnLine Q ℓ) (ha : ¬ OnLine a ℓ)
    (hab : Between a M b) :
    RayCrosses Y₁ Q (a, b) ∧ ¬ RayCrosses Y₂ Q (a, b) := by
  have hMQ : Between Y₁ M Q := between_of_between_left h hM
  have hMℓ : OnLine M ℓ := on_line_of_between_ends hMQ h1 hQ
  have h2 : OnLine Y₂ ℓ := on_line_of_between_ends h h1 hQ
  refine ⟨⟨M, OnRay.of_between hMQ, hab⟩, fun hc => ?_⟩
  exact ((Parity.crosses_at h2 hQ ha hab hMℓ).mp hc).2.2.2 (between_inner hM h)

/-! ## Counting crossings -/

/-- Rays crossing the same sides have the same count. -/
theorem count_congr {ps : List Point} {X Y Q : Point}
    (h : ∀ t ∈ sides ps, RayCrosses X Q t ↔ RayCrosses Y Q t) :
    crossingCount ps X Q = crossingCount ps Y Q := by
  unfold crossingCount
  congr 1
  exact List.filter_congr fun t ht => decide_eq_decide.mpr (h t ht)

/-- One side crossed by the first ray and not the second, and the others crossed alike: the
first count is one more. -/
theorem count_succ {ps : List Point} (hnd : ps.Nodup) {X Y Q : Point} {s : Point × Point}
    (hs : s ∈ sides ps) (hX : RayCrosses X Q s) (hY : ¬ RayCrosses Y Q s)
    (h : ∀ t ∈ sides ps, t ≠ s → (RayCrosses X Q t ↔ RayCrosses Y Q t)) :
    crossingCount ps X Q = crossingCount ps Y Q + 1 := by
  unfold crossingCount
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact countP_succ _ _ (sides ps) s (LoopFacts.sides_nodup hnd) hs (by simpa using hX)
    (by simpa using hY) fun t ht hts => decide_eq_decide.mpr (h t ht hts)

/-! ## One loop along a finite straight line -/

/-- **Along a finite straight line that meets no side.** If the finite straight line XZ
meets no side of a simple loop, ends included, and its straight line passes through no corner,
then X is inside the loop exactly when Z is. Produce ZX beyond X to Q: the good rays from Z
and from X through Q cross the same sides. -/
theorem inside_of_segment {ps : List Point} (h : SimpleLoop ps) {X Z : Point} {ℓ : Line}
    (hXZ : X ≠ Z) (hXℓ : OnLine X ℓ) (hZℓ : OnLine Z ℓ) (hoff : ∀ V ∈ ps, ¬ OnLine V ℓ)
    (hX : ¬ LoopBoundary ps X) (hZ : ¬ LoopBoundary ps Z)
    (hseg : ∀ U : Point, Between X U Z → ¬ LoopBoundary ps U) :
    LoopInside ps X ↔ LoopInside ps Z := by
  obtain ⟨Q, hZXQ⟩ := produce hXZ.symm
  have hQℓ : OnLine Q ℓ := on_line_of_between hZXQ hZℓ hXℓ
  have hgZ : GoodRay ps Z Q := OutlineFacts.good_of_line (ne_of_between_ends hZXQ) hZℓ hQℓ hoff
  have hgX : GoodRay ps X Q :=
    OutlineFacts.good_of_line (ne_of_between (between_symm hZXQ)).symm hXℓ hQℓ hoff
  have hc : crossingCount ps Z Q = crossingCount ps X Q := by
    apply count_congr
    intro t ht
    apply crosses_shift hZXQ
    intro U hU hUt
    rcases hU with e | hU
    · rw [e] at hUt
      exact hX ⟨t, ht, Or.inr (Or.inr hUt)⟩
    · exact hseg U (between_symm hU) ⟨t, ht, Or.inr (Or.inr hUt)⟩
  rw [loop_inside_iff h hX hgX, loop_inside_iff h hZ hgZ, hc]

/-- **Across one side.** If the finite straight line Y₁Y₂ meets the boundary of a simple loop
only at a point M strictly within the side s, and its straight line passes through no corner,
then exactly one of Y₁ and Y₂ is inside the loop. Produce Y₁Y₂ beyond Y₂ to Q: the good ray
from Y₁ through Q crosses s and every side the ray from Y₂ crosses, and no other. -/
theorem inside_flip {ps : List Point} (h : SimpleLoop ps) {s : Point × Point}
    (hs : s ∈ sides ps) {Y₁ M Y₂ : Point} {ℓ : Line} (hM : Between Y₁ M Y₂)
    (hMs : Between s.1 M s.2) (h1 : OnLine Y₁ ℓ) (h2 : OnLine Y₂ ℓ)
    (hoff : ∀ V ∈ ps, ¬ OnLine V ℓ)
    (hseg : ∀ U : Point, OnFiniteLine U Y₁ Y₂ → ∀ t ∈ sides ps,
      OnFiniteLine U t.1 t.2 → U = M ∧ t = s) :
    LoopInside ps Y₁ ↔ ¬ LoopInside ps Y₂ := by
  have hY12 : Y₁ ≠ Y₂ := ne_of_between_ends hM
  obtain ⟨Q, hQ⟩ := produce hY12
  have hQℓ : OnLine Q ℓ := on_line_of_between hQ h1 h2
  have hb1 : ¬ LoopBoundary ps Y₁ := fun ⟨t, ht, hY⟩ =>
    ne_of_between hM (hseg Y₁ (Or.inl rfl) t ht hY).1
  have hb2 : ¬ LoopBoundary ps Y₂ := fun ⟨t, ht, hY⟩ =>
    ne_of_between (between_symm hM) (hseg Y₂ (Or.inr (Or.inl rfl)) t ht hY).1
  have hg1 : GoodRay ps Y₁ Q := OutlineFacts.good_of_line (ne_of_between_ends hQ) h1 hQℓ hoff
  have hg2 : GoodRay ps Y₂ Q :=
    OutlineFacts.good_of_line (ne_of_between (between_symm hQ)).symm h2 hQℓ hoff
  obtain ⟨c1, c2⟩ := crosses_once (b := s.2) hQ hM h1 hQℓ
    (hoff _ (LoopFacts.side_mem hs).1) hMs
  have hc : crossingCount ps Y₁ Q = crossingCount ps Y₂ Q + 1 := by
    refine count_succ h.2.1 hs c1 c2 fun t ht hts => crosses_shift hQ ?_
    intro U hU hUt
    have hU' : OnFiniteLine U Y₁ Y₂ := by
      rcases hU with e | hU
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr hU)
    exact hts (hseg U hU' t ht (Or.inr (Or.inr hUt))).2
  rw [loop_inside_iff h hb1 hg1, loop_inside_iff h hb2 hg2, hc]
  generalize crossingCount ps Y₂ Q = n
  constructor
  · intro h₁ h₂
    omega
  · intro h₁
    omega

/-! ## The depth of a figure -/

/-- Points inside the same contours have the same depth. -/
theorem depth_congr (F : Outline) {X Y : Point}
    (h : ∀ ps ∈ F.loops, LoopInside ps X ↔ LoopInside ps Y) : F.depth X = F.depth Y := by
  unfold Outline.depth
  congr 1
  exact List.filter_congr fun ps hps => decide_eq_decide.mpr (h ps hps)

/-- **One contour changes, and no other**: then one of the two points has odd depth. -/
theorem depth_flip (F : Outline) {pre post : List (List Point)} {ps : List Point}
    (hF : F.loops = pre ++ ps :: post) {X Y : Point}
    (h : ∀ qs ∈ pre ++ post, LoopInside qs X ↔ LoopInside qs Y)
    (hps : LoopInside ps X ↔ ¬ LoopInside ps Y) :
    F.depth X % 2 = 1 ∨ F.depth Y % 2 = 1 := by
  unfold Outline.depth
  rw [hF, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  refine countP_flip pre post ps _ _ (fun qs hqs => decide_eq_decide.mpr (h qs hqs)) ?_
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact hps

/-- Two points off the boundary, inside the same contours, are inside the figure together. -/
theorem inside_congr (F : Outline) {X Y : Point} (hX : ¬ F.Boundary X) (hY : ¬ F.Boundary Y)
    (h : ∀ ps ∈ F.loops, LoopInside ps X ↔ LoopInside ps Y) : F.Inside X ↔ F.Inside Y := by
  unfold Outline.Inside
  rw [depth_congr F h]
  exact ⟨fun hX' => ⟨hY, hX'.2⟩, fun hY' => ⟨hX, hY'.2⟩⟩

/-! ## Corners and the straight lines to them -/

/-- A corner of a contour is a corner of the figure. -/
theorem mem_corners {F : Outline} {ps : List Point} (hps : ps ∈ F.loops) {V : Point}
    (hV : V ∈ ps) : V ∈ F.corners :=
  List.mem_flatten.mpr ⟨ps, hps, hV⟩

/-- A point off the boundary is no corner. -/
theorem not_corner {F : Outline} {X : Point} (hX : ¬ F.Boundary X) : X ∉ F.corners := by
  intro hm
  obtain ⟨ps, hps, hV⟩ := List.mem_flatten.mp hm
  obtain ⟨E, hE⟩ := outgoing_side hV
  exact hX ⟨ps, hps, (X, E), hE, Or.inl rfl⟩

/-- A straight line through X and a point off all the joining lines passes through none of
the points, when X is none of them. -/
theorem joins_off {X Z : Point} {vs : List Point}
    (hZ : Avoid (vs.map fun V => Classical.choose (collinear_of_two X V)) Z) (hX : X ∉ vs)
    {ℓ : Line} (hXℓ : OnLine X ℓ) (hZℓ : OnLine Z ℓ) : ∀ V ∈ vs, ¬ OnLine V ℓ := by
  intro V hV hVℓ
  have hspec := Classical.choose_spec (collinear_of_two X V)
  have hXV : X ≠ V := fun e => hX (e ▸ hV)
  have he : ℓ = Classical.choose (collinear_of_two X V) :=
    line_unique hXV hXℓ hVℓ hspec.1 hspec.2
  exact hZ _ (List.mem_map_of_mem hV) (he ▸ hZℓ)

/-- For each straight line of a list that misses X, the pair of X and that line. -/
theorem pairs_off (X : Point) : ∀ ls : List Line, ∃ hs : List (Point × Line),
    (∀ p ∈ hs, SameSide X p.1 p.2) ∧ ∀ L ∈ ls, ¬ OnLine X L → (X, L) ∈ hs
  | [] => ⟨[], by simp, by simp⟩
  | L :: ls => by
    obtain ⟨hs, h1, h2⟩ := pairs_off X ls
    by_cases hL : OnLine X L
    · refine ⟨hs, h1, fun M hM hXM => ?_⟩
      rcases List.mem_cons.mp hM with e | hM
      · exact absurd (e ▸ hL) hXM
      · exact h2 M hM hXM
    · refine ⟨(X, L) :: hs, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with e | hp
        · rw [e]
          exact same_side_refl hL
        · exact h1 p hp
      · intro M hM hXM
        rcases List.mem_cons.mp hM with e | hM
        · rw [e]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h2 M hM hXM)

/-! ## Off the side lines -/

/-- A point off every straight line holding a side is off the boundary. -/
theorem off_boundary {F : Outline} {ls : List Line}
    (hs : ∀ ps ∈ F.loops, ∀ s ∈ sides ps, ∃ L ∈ ls, OnLine s.1 L ∧ OnLine s.2 L)
    {X : Point} (hX : ∀ L ∈ ls, ¬ OnLine X L) : ¬ F.Boundary X := by
  rintro ⟨ps, hps, s, hs', hXs⟩
  obtain ⟨L, hL, h1, h2⟩ := hs ps hps s hs'
  exact hX L hL (LoopFacts.onFiniteLine_onLine hXs h1 h2)

/-- A point of a cell's inside is off every straight line its inside keeps to one side of. -/
theorem core_off {Q : ConvexCell} {ls : List Line}
    (hQ : ∀ L ∈ ls, ∀ X Y : Point, Q.Core X → Q.Core Y → SameSide X Y L) {X : Point}
    (hX : Q.Core X) : ∀ L ∈ ls, ¬ OnLine X L :=
  fun L hL => not_on_line_of_same_side (hQ L hL X X hX hX)

/-- **Within one cell, along a straight line through no corner.** Two points of a cell's
inside, whose straight line passes through no corner, are inside the same contours: the
finite straight line between them meets no side line. -/
theorem core_segment (F : Outline) {ls : List Line}
    (hs : ∀ ps ∈ F.loops, ∀ s ∈ sides ps, ∃ L ∈ ls, OnLine s.1 L ∧ OnLine s.2 L)
    {Q : ConvexCell} (hQ : ∀ L ∈ ls, ∀ X Y : Point, Q.Core X → Q.Core Y → SameSide X Y L)
    {X Z : Point} (hX : Q.Core X) (hZ : Q.Core Z) (hXZ : X ≠ Z) {ℓ : Line}
    (hXℓ : OnLine X ℓ) (hZℓ : OnLine Z ℓ) (hoff : ∀ V ∈ F.corners, ¬ OnLine V ℓ) :
    ∀ ps ∈ F.loops, LoopInside ps X ↔ LoopInside ps Z := by
  intro ps hps
  refine inside_of_segment (F.simple ps hps) hXZ hXℓ hZℓ
    (fun V hV => hoff V (mem_corners hps hV))
    (fun hb => off_boundary hs (core_off hQ hX) ⟨ps, hps, hb⟩)
    (fun hb => off_boundary hs (core_off hQ hZ) ⟨ps, hps, hb⟩) ?_
  rintro U hU ⟨t, ht, hUt⟩
  obtain ⟨L, hL, h1, h2⟩ := hs ps hps t ht
  exact pasch3 hU (LoopFacts.onFiniteLine_onLine hUt h1 h2) (hQ L hL X Z hX hZ)

/-- **Inside one open cell the depth's parity is constant.** Join each of the two points to a
third point of the cell's inside, off the straight lines from either point to the corners. -/
theorem cell_constant (F : Outline) {ls : List Line}
    (hs : ∀ ps ∈ F.loops, ∀ s ∈ sides ps, ∃ L ∈ ls, OnLine s.1 L ∧ OnLine s.2 L)
    {Q : ConvexCell} (hQ : ∀ L ∈ ls, ∀ X Y : Point, Q.Core X → Q.Core Y → SameSide X Y L)
    {X Y : Point} (hX : Q.Core X) (hY : Q.Core Y) : F.Inside X ↔ F.Inside Y := by
  have hXb := off_boundary hs (core_off hQ hX)
  have hYb := off_boundary hs (core_off hQ hY)
  obtain ⟨KX, hKX⟩ := exists_line_through X
  obtain ⟨KY, hKY⟩ := exists_line_through Y
  obtain ⟨Z, hZa, hZ⟩ := CellFacts.core_point_avoiding Q.convex
    (KX :: KY :: ((F.corners.map fun V => Classical.choose (collinear_of_two X V)) ++
      F.corners.map fun V => Classical.choose (collinear_of_two Y V)))
  have hZQ : Q.Core Z := hZ
  have hXZ : X ≠ Z := fun e => hZa KX List.mem_cons_self (e ▸ hKX)
  have hYZ : Y ≠ Z := fun e =>
    hZa KY (List.mem_cons_of_mem _ List.mem_cons_self) (e ▸ hKY)
  have hjX : Avoid (F.corners.map fun V => Classical.choose (collinear_of_two X V)) Z :=
    fun L hL =>
    hZa L (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hL)))
  have hjY : Avoid (F.corners.map fun V => Classical.choose (collinear_of_two Y V)) Z :=
    fun L hL =>
    hZa L (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hL)))
  obtain ⟨ℓ, hXℓ, hZℓ⟩ := Postulate1 X Z hXZ
  obtain ⟨m, hYm, hZm⟩ := Postulate1 Y Z hYZ
  have eX := core_segment F hs hQ hX hZQ hXZ hXℓ hZℓ
    (joins_off hjX (not_corner hXb) hXℓ hZℓ)
  have eY := core_segment F hs hQ hY hZQ hYZ hYm hZm
    (joins_off hjY (not_corner hYb) hYm hZm)
  exact inside_congr F hXb hYb fun ps hps => (eX ps hps).trans (eY ps hps).symm

/-! ## A cell's closed region and its inside -/

/-- **From a point of a cell's closed region to its inside.** A point of a cell's closed region
off the figure's boundary has a point of the cell's inside that is inside the figure exactly
when the first point is: go a little way towards a point of the inside off the straight lines
to the corners, staying on the point's side of every side line that misses it. The finite
straight line so drawn meets no side, so it changes no contour's inside. -/
theorem cell_point (F : Outline) {ls : List Line}
    (hs : ∀ ps ∈ F.loops, ∀ s ∈ sides ps, ∃ L ∈ ls, OnLine s.1 L ∧ OnLine s.2 L)
    {Q : ConvexCell} (hQ : ∀ L ∈ ls, ∀ X Y : Point, Q.Core X → Q.Core Y → SameSide X Y L)
    {X : Point} (hX : ¬ F.Boundary X) (hXQ : Q.Region X) :
    ∃ W : Point, Q.Core W ∧ (F.Inside W ↔ F.Inside X) := by
  obtain ⟨K, hXK⟩ := exists_line_through X
  obtain ⟨Z, hZa, hZ⟩ := CellFacts.core_point_avoiding Q.convex
    (K :: F.corners.map fun V => Classical.choose (collinear_of_two X V))
  have hZQ : Q.Core Z := hZ
  have hXZ : X ≠ Z := fun e => hZa K List.mem_cons_self (e ▸ hXK)
  have hZls := core_off hQ hZQ
  obtain ⟨ℓ, hXℓ, hZℓ⟩ := Postulate1 X Z hXZ
  have hoff := joins_off (fun L hL => hZa L (List.mem_cons_of_mem _ hL)) (not_corner hX)
    hXℓ hZℓ
  obtain ⟨hp, hp1, hp2⟩ := pairs_off X ls
  obtain ⟨W, hXWZ, hW⟩ := shorten_off_lines hXZ hp hp1
  have hWQ : Q.Core W := ConvexCell.core_between hXQ hZQ hXWZ
  have hWℓ : OnLine W ℓ := on_line_of_between_ends hXWZ hXℓ hZℓ
  have hXW : X ≠ W := ne_of_between hXWZ
  /- No point of the finite straight line XW but X is on a side line. -/
  have hline : ∀ U : Point, (U = W ∨ Between X U W) → ∀ L ∈ ls, ¬ OnLine U L := by
    intro U hU L hL hUL
    have hUℓ : OnLine U ℓ := by
      rcases hU with e | hU
      · exact e ▸ hWℓ
      · exact on_line_of_between_ends hU hXℓ hWℓ
    have hXU : X ≠ U := by
      rcases hU with e | hU
      · exact e ▸ hXW
      · exact ne_of_between hU
    by_cases hXL : OnLine X L
    · exact hZls L hL (line_unique hXU hXℓ hUℓ hXL hUL ▸ hZℓ)
    · have hWX : SameSide W X L := hW (X, L) (hp2 L hL hXL)
      rcases hU with e | hU
      · exact not_on_line_of_same_side hWX (e ▸ hUL)
      · exact pasch3 hU hUL (same_side_symm hWX)
  have hoffF : ∀ U : Point, (U = W ∨ Between X U W) → ¬ F.Boundary U :=
    fun U hU => off_boundary hs (hline U hU)
  refine ⟨W, hWQ, inside_congr F (hoffF W (Or.inl rfl)) hX fun ps hps => ?_⟩
  exact (inside_of_segment (F.simple ps hps) hXW hXℓ hWℓ
    (fun V hV => hoff V (mem_corners hps hV)) (fun hb => hX ⟨ps, hps, hb⟩)
    (fun hb => hoffF W (Or.inl rfl) ⟨ps, hps, hb⟩)
    (fun U hU hb => hoffF U (Or.inr hU) ⟨ps, hps, hb⟩)).symm

/-- **A cell whose closed region misses a point** is kept off it by one side line: every point
on the point's side of that straight line is outside the cell. -/
theorem clear_of_cell {Q : ConvexCell} {X : Point} (hX : ¬ Q.Region X) :
    ∃ L : Line, ¬ OnLine X L ∧ ∀ Y : Point, SameSide Y X L → ¬ Q.Region Y := by
  obtain ⟨s, hs, A, hA, h1, h2, hn⟩ : ∃ s ∈ sides Q.corners, ∃ A ∈ Q.corners,
      A ≠ s.1 ∧ A ≠ s.2 ∧ ¬ ClosedSide X A s.1 s.2 := by
    refine Classical.byContradiction fun hno => hX ?_
    intro s hs A hA h1 h2
    exact Classical.byContradiction fun hc => hno ⟨s, hs, A, hA, h1, h2, hc⟩
  have hne := convex_side_ne Q.convex hs
  obtain ⟨L, hL1, hL2⟩ := Postulate1 s.1 s.2 hne
  have hiff := closedSide_iff_half (X := X) (P := A) hne hL1 hL2
  refine ⟨L, fun hXL => hn (hiff.mpr (Or.inl hXL)), fun Y hYX hY => ?_⟩
  rcases (closedSide_iff_half hne hL1 hL2).mp (hY s hs A hA h1 h2) with hYL | hYA
  · exact not_on_line_of_same_side hYX hYL
  · exact hn (hiff.mpr (Or.inr (same_side_trans hYX hYA)))

/-- **Near a point, only the cells holding it.** Finitely many conditions, each holding at X,
such that a point satisfying them all lies in no cell of the list whose closed region misses X.
-/
theorem clear_of_cells (X : Point) : ∀ qs : List ConvexCell, ∃ hs : List (Point × Line),
    (∀ p ∈ hs, SameSide X p.1 p.2) ∧
      ∀ Y : Point, (∀ p ∈ hs, SameSide Y p.1 p.2) → ∀ Q ∈ qs, Q.Region Y → Q.Region X
  | [] => ⟨[], by simp, by simp⟩
  | Q :: qs => by
    obtain ⟨hs, h1, h2⟩ := clear_of_cells X qs
    by_cases hQ : Q.Region X
    · refine ⟨hs, h1, fun Y hY R hR hRY => ?_⟩
      rcases List.mem_cons.mp hR with e | hR
      · exact e ▸ hQ
      · exact h2 Y hY R hR hRY
    · obtain ⟨L, hXL, hL⟩ := clear_of_cell hQ
      refine ⟨(X, L) :: hs, ?_, fun Y hY R hR hRY => ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with e | hp
        · rw [e]
          exact same_side_refl hXL
        · exact h1 p hp
      · rcases List.mem_cons.mp hR with e | hR
        · rw [e] at hRY
          exact absurd hRY (hL Y (hY (X, L) List.mem_cons_self))
        · exact h2 Y (fun p hp => hY p (List.mem_cons_of_mem _ hp)) R hR hRY

/-! ## Filled points near the boundary -/

/-- **A point strictly within a side, near a point of it.** Given conditions that hold at a
point X of the finite straight line ab, some point strictly between a and b satisfies them
too, and is none of finitely many given points. -/
theorem side_point {a b X : Point} (hab : a ≠ b) (hX : OnFiniteLine X a b)
    (hs : List (Point × Line)) (hXs : ∀ p ∈ hs, SameSide X p.1 p.2) (vs : List Point) :
    ∃ M : Point, Between a M b ∧ M ∉ vs ∧ ∀ p ∈ hs, SameSide M p.1 p.2 := by
  obtain ⟨E, hXE, hE⟩ : ∃ E : Point, X ≠ E ∧ ∀ M : Point, Between X M E → Between a M b := by
    rcases hX with e | e | hb
    · rw [e]
      exact ⟨b, hab, fun M hM => hM⟩
    · rw [e]
      exact ⟨a, hab.symm, fun M hM => between_symm hM⟩
    · exact ⟨b, (ne_of_between (between_symm hb)).symm, fun M hM =>
        between_symm (between_of_between_left (between_symm hb) (between_symm hM))⟩
  obtain ⟨M₀, hXM₀E, hM₀⟩ := shorten_off_lines hXE hs hXs
  have hXM₀ : X ≠ M₀ := ne_of_between hXM₀E
  obtain ⟨N, hXN, hM₀N⟩ := Postulate1 X M₀ hXM₀
  obtain ⟨M, -, hXMM₀, hMv⟩ := exists_point_between hXN hM₀N hXM₀ vs
  exact ⟨M, hE M (between_of_between_left hXM₀E hXMM₀), hMv,
    fun p hp => same_side_between hXMM₀ (hXs p hp) (hM₀ p hp)⟩

/-- **A boundary point has filled points near it.** Given conditions that hold at a point of
the boundary, some point inside the figure satisfies them too. Slide along a side through the
point to a point M strictly within it, at no corner; draw a short finite straight line across
the side through M, its straight line through no corner and its ends on M's side of every
side line missing M. It meets the boundary only at M, so it changes one contour's inside and
no other's, and one of its ends has odd depth. -/
theorem boundary_filled (F : Outline) {X : Point} (hX : F.Boundary X)
    (hs : List (Point × Line)) (hXs : ∀ p ∈ hs, SameSide X p.1 p.2) :
    ∃ Y : Point, F.Inside Y ∧ ∀ p ∈ hs, SameSide Y p.1 p.2 := by
  obtain ⟨ps, hps, s, hs₀, hXs₀⟩ := hX
  have hsimple := F.simple ps hps
  obtain ⟨pre, post, hF⟩ := List.append_of_mem hps
  /- The sides of all the contours, and a straight line through each. -/
  let ss : List (Point × Point) := F.loops.flatMap sides
  let lineS (t : Point × Point) : Line := Classical.choose (collinear_of_two t.1 t.2)
  have hlineS (t : Point × Point) : OnLine t.1 (lineS t) ∧ OnLine t.2 (lineS t) :=
    Classical.choose_spec (collinear_of_two t.1 t.2)
  have hss {qs : List Point} (hqs : qs ∈ F.loops) {t : Point × Point} (ht : t ∈ sides qs) :
      t ∈ ss := List.mem_flatMap.mpr ⟨qs, hqs, ht⟩
  /- A point M strictly within the side s, near X, at no corner. -/
  obtain ⟨M, hMs, hMv, hMh⟩ := side_point (hsimple.2.2.1 s hs₀) hXs₀ hs hXs F.corners
  have hMS : OnLine M (lineS s) := on_line_of_between_ends hMs (hlineS s).1 (hlineS s).2
  /- Conditions at M: those given, and M's side of every side line missing it. -/
  obtain ⟨hm, hm1, hm2⟩ := pairs_off M (ss.map lineS)
  have hMall : ∀ p ∈ hs ++ hm, SameSide M p.1 p.2 := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hMh p hp
    · exact hm1 p hp
  /- A small triangle with a corner at M, its other corners towards the end s.1 and towards a
  corner C of the contour off the straight line of s; a point Z inside it off the side lines
  and off the straight lines from M to the corners. No circle is drawn. -/
  obtain ⟨C, hCS⟩ : ∃ C : Point, ¬ OnLine C (lineS s) := by
    obtain ⟨A₁, -, B₁, -, C₁, -, hABC⟩ := LoopFacts.simple_frame hsimple
    by_cases hA : OnLine A₁ (lineS s)
    · by_cases hB : OnLine B₁ (lineS s)
      · exact ⟨C₁, hABC.off_line hA hB⟩
      · exact ⟨B₁, hB⟩
    · exact ⟨A₁, hA⟩
  have hMa : M ≠ s.1 := (ne_of_between hMs).symm
  have hT : Triangle M s.1 C := Triangle.of_line hMS (hlineS s).1 hMa hCS
  obtain ⟨a', hMa'a, ha'⟩ := shorten_off_lines hMa (hs ++ hm) hMall
  obtain ⟨c', hMc'C, hc'⟩ := shorten_off_lines hT.ne₁₃ (hs ++ hm) hMall
  obtain ⟨Z, hZT, hZa⟩ := triangle_point_avoiding (corner_triangle hT hMa'a hMc'C).1
    (ss.map lineS ++ F.corners.map fun V => Classical.choose (collinear_of_two M V))
  have hZs : ∀ p ∈ hs ++ hm, SameSide Z p.1 p.2 := fun p hp =>
    closed_same_side (hMall p hp) (ha' p hp) (hc' p hp) (Or.inl hZT)
  have hZS : ∀ t ∈ ss, ¬ OnLine Z (lineS t) := fun t ht =>
    hZa _ (List.mem_append_left _ (List.mem_map_of_mem ht))
  have hZM : Z ≠ M := fun e => hZS s (hss hps hs₀) (e ▸ hMS)
  obtain ⟨ℓ, hZℓ, hMℓ⟩ := Postulate1 Z M hZM
  have hoff : ∀ V ∈ F.corners, ¬ OnLine V ℓ :=
    joins_off (fun L hL => hZa L (List.mem_append_right _ hL)) hMv hMℓ hZℓ
  /- Across s from Z, through M, to Y₂ near M. -/
  obtain ⟨Y', hZMY'⟩ := produce hZM
  obtain ⟨Y₂, hMY₂Y', hY₂s⟩ :=
    shorten_off_lines (ne_of_between (between_symm hZMY')).symm (hs ++ hm) hMall
  have hZMY₂ : Between Z M Y₂ := between_cut hZMY' hMY₂Y'
  have hY₂ℓ : OnLine Y₂ ℓ := on_line_of_between hZMY₂ hZℓ hMℓ
  have hY₂M : Y₂ ≠ M := (ne_of_between hMY₂Y').symm
  /- The finite straight line ZY₂ meets the boundary only at M. -/
  have hone : ∀ t ∈ ss, ∀ U : Point, OnFiniteLine U Z Y₂ → OnFiniteLine U t.1 t.2 → U = M := by
    intro t ht U hU hUt
    have hUL : OnLine U (lineS t) :=
      LoopFacts.onFiniteLine_onLine hUt (hlineS t).1 (hlineS t).2
    have hUℓ : OnLine U ℓ := LoopFacts.onFiniteLine_onLine hU hZℓ hY₂ℓ
    by_cases hML : OnLine M (lineS t)
    · refine Classical.byContradiction fun hUM => ?_
      exact hZS t ht (line_unique hUM hUℓ hMℓ hUL hML ▸ hZℓ)
    · have hp : (M, lineS t) ∈ hs ++ hm :=
        List.mem_append_right _ (hm2 _ (List.mem_map_of_mem ht) hML)
      have hZM' := hZs _ hp
      have hYM' := hY₂s _ hp
      rcases hU with e | e | hb
      · exact absurd (e ▸ hUL) (not_on_line_of_same_side hZM')
      · exact absurd (e ▸ hUL) (not_on_line_of_same_side hYM')
      · exact absurd (same_side_trans (same_side_symm hZM') (same_side_symm hYM'))
          (pasch3 hb hUL)
  have hZb : ¬ F.Boundary Z := fun ⟨qs, hqs, t, ht, hZt⟩ =>
    hZM (hone t (hss hqs ht) Z (Or.inl rfl) hZt)
  have hY₂b : ¬ F.Boundary Y₂ := fun ⟨qs, hqs, t, ht, hYt⟩ =>
    hY₂M (hone t (hss hqs ht) Y₂ (Or.inr (Or.inl rfl)) hYt)
  /- The contour of s changes across M. -/
  have hflip : LoopInside ps Z ↔ ¬ LoopInside ps Y₂ := by
    refine inside_flip hsimple hs₀ hZMY₂ hMs hZℓ hY₂ℓ
      (fun V hV => hoff V (mem_corners hps hV)) ?_
    intro U hU t ht hUt
    have hUM := hone t (hss hps ht) U hU hUt
    refine ⟨hUM, Classical.byContradiction fun hts => ?_⟩
    rw [hUM] at hUt
    rcases (Parity.side_meet hsimple hs₀ ht (Ne.symm hts) M (Or.inr (Or.inr hMs)) hUt).1 with
      e | e
    · exact ne_of_between hMs e.symm
    · exact ne_of_between (between_symm hMs) e.symm
  /- No other contour passes through M, so none changes. -/
  have hpw := F.compatible
  rw [hF, List.pairwise_append, List.pairwise_cons] at hpw
  have hMps : LoopBoundary ps M := ⟨s, hs₀, Or.inr (Or.inr hMs)⟩
  have hmemF : ∀ qs ∈ pre ++ post, qs ∈ F.loops := by
    intro qs hqs
    rw [hF]
    rcases List.mem_append.mp hqs with hq | hq
    · exact List.mem_append_left _ hq
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)
  have hcomp : ∀ qs ∈ pre ++ post, ¬ LoopBoundary qs M := by
    intro qs hqs hMq
    have hmem : M ∈ ps ∨ M ∈ qs := by
      rcases List.mem_append.mp hqs with hq | hq
      · exact ((hpw.2.2 qs hq ps List.mem_cons_self).1 M hMq hMps).symm
      · exact (hpw.2.1.1 qs hq).1 M hMps hMq
    rcases hmem with h | h
    · exact hMv (mem_corners hps h)
    · exact hMv (mem_corners (hmemF qs hqs) h)
  have hsame : ∀ qs ∈ pre ++ post, LoopInside qs Z ↔ LoopInside qs Y₂ := by
    intro qs hqs
    have hqF := hmemF qs hqs
    refine inside_of_segment (F.simple qs hqF) (ne_of_between_ends hZMY₂) hZℓ hY₂ℓ
      (fun V hV => hoff V (mem_corners hqF hV)) (fun hb => hZb ⟨qs, hqF, hb⟩)
      (fun hb => hY₂b ⟨qs, hqF, hb⟩) ?_
    rintro U hU ⟨t, ht, hUt⟩
    have hUM := hone t (hss hqF ht) U (Or.inr (Or.inr hU)) hUt
    rw [hUM] at hUt
    exact hcomp qs hqs ⟨t, ht, hUt⟩
  rcases depth_flip F hF hsame hflip with h | h
  · exact ⟨Z, ⟨hZb, h⟩, fun p hp => hZs p (List.mem_append_left _ hp)⟩
  · exact ⟨Y₂, ⟨hY₂b, h⟩, fun p hp => hY₂s p (List.mem_append_left _ hp)⟩

/-- **Every point of the figure has filled points near it**: given conditions holding at a
point of the closed region, some point inside the figure satisfies them. -/
theorem region_filled (F : Outline) {X : Point} (hX : F.Region X)
    (hs : List (Point × Line)) (hXs : ∀ p ∈ hs, SameSide X p.1 p.2) :
    ∃ Y : Point, F.Inside Y ∧ ∀ p ∈ hs, SameSide Y p.1 p.2 := by
  rcases hX with hb | hi
  · exact boundary_filled F hb hs hXs
  · exact ⟨X, hi, hXs⟩

end CoverFacts

end Elements.Figures
