import Elements.Figure.Outlines
import Elements.Figure.Content
import Elements.Figure.Convex.Area
import Elements.Figure.Arrangements.ArrangementFacts
import Elements.Figure.Arrangements.CoverFacts
import Elements.Figure.Arrangements.Diagonal
import Elements.Figure.Divisions.DivisionFacts

/-!
# Book Zero: from side lines to a division of an outline

Brief 0013's route to a division selects cells of a finite arrangement (section 8, "The
arrangement and general division"). Its statements are here, with their proofs:

* **D2.** Finitely many points with a triangle among them lie in a convex cell, grown one
  point at a time; it need not be their hull (`convex_enclosure`).
* **D9, the enclosure.** So the whole region of an outline lies strictly inside a cell
  (`outline_enclosure`).
* **D8.** The straight lines of the outline's sides (`outline_side_lines`) cut that cell
  into cells with disjoint insides, each off every side line (`convex_arrangement`).
* **D9, the selection.** An outline's parity is constant inside each cell
  (`outline_cell_constant`), and the cells with a point of their inside within the figure
  make up exactly its closed region, holes, cuts and contacts at corners included
  (`outline_cells_cover`). Their fans divide the outline (`division_exists`, in
  `Divisions.lean`).

Good rays and their parity are `good_ray_exists` and `crossing_parity_independent`, in
`Outlines.lean`. The selection examines no sector at a corner: from a point of the boundary
it slides to an ordinary point of a side, and across it (`CoverFacts.boundary_filled`;
brief 0013, section 8, "The routes taken", D9).

The ledger's optional diagonal route, D5 to D7, is here too. `simple_diagonal` and
`simple_diagonal_partition` split a simple outline along an interior diagonal joining two of
its original corners (helpers in `Arrangements/Diagonal.lean`); the proof draws no parallel.
`simple_triangulation` asserts a division of a simple outline without restricting its
triangles' corners to the original ones, and the arrangement route proves it. The convex
precursors B1, B2 and B4's `fanSum_rotateLeft` are in `Convex/Diagonals.lean`.

Nothing in Book Zero cites a proposition of the *Elements*.
-/

namespace Elements.Figures

/-- Finitely many points containing a triangle lie in a convex cell. -/
theorem convex_enclosure (ps : List Point)
    (h : ∃ A ∈ ps, ∃ B ∈ ps, ∃ C ∈ ps, Triangle A B C) :
    ∃ P : ConvexCell, ∀ V ∈ ps, P.Region V := by
  /- Begin with the triangle, a convex outline, and add the points one after another
  (`Arrangement.enclose_list`, by `Arrangement.insert_point`): each time, a convex outline holding the region
  before and the new point. Its corners need not be among the points. -/
  obtain ⟨A, -, B, -, C, -, hABC⟩ := h
  obtain ⟨ds, hds, -, hps⟩ := Arrangement.enclose_list ps (Extreme.triangle_outline hABC)
  exact ⟨⟨ds, hds⟩, hps⟩

/-- An outline's whole region lies strictly inside an enclosing cell. -/
theorem outline_enclosure (F : Outline) :
    ∃ P : ConvexCell, ∀ X : Point, F.Region X → P.Core X := by
  classical
  /- A convex cell holding every corner of every contour (`convex_enclosure`), three of them
  making a triangle by simplicity (`LoopFacts.simple_frame`). -/
  obtain ⟨ps₀, hps₀⟩ := List.exists_mem_of_ne_nil F.loops F.ne
  obtain ⟨A, hA, B, hB, C, hC, hABC⟩ := LoopFacts.simple_frame (F.simple ps₀ hps₀)
  have hm {V : Point} {ps : List Point} (hps : ps ∈ F.loops) (hV : V ∈ ps) :
      V ∈ F.loops.flatten := List.mem_flatten.mpr ⟨ps, hps, hV⟩
  obtain ⟨P₀, hP₀⟩ := convex_enclosure F.loops.flatten
    ⟨A, hm hps₀ hA, B, hm hps₀ hB, C, hm hps₀ hC, hABC⟩
  /- The figure lies in its region. A boundary point is on a side between two corners. A
  point inside is inside some contour; were it outside the cell's region, a good ray from it
  would cross no side of that contour (`Arrangement.outside_ray`), an even count, while being inside
  gives a good ray with an odd count: two good rays from one point have one parity
  (`crossing_parity_independent`). -/
  have hin : ∀ X : Point, F.Region X → P₀.Region X := by
    rintro X (⟨ps, hps, s, hs, hX⟩ | ⟨-, hd⟩)
    · have h₁ := hP₀ _ (hm hps (LoopFacts.side_mem hs).1)
      have h₂ := hP₀ _ (hm hps (LoopFacts.side_mem hs).2)
      rcases hX with e | e | hb
      · exact e ▸ h₁
      · exact e ▸ h₂
      · exact convex_region_between P₀.convex h₁ h₂ hb
    · have hpos : 0 < F.depth X := by omega
      unfold Outline.depth at hpos
      obtain ⟨ps, hps⟩ := List.exists_mem_of_length_pos hpos
      rw [List.mem_filter] at hps
      obtain ⟨hXb, R, hR, hodd⟩ : LoopInside ps X := of_decide_eq_true hps.2
      refine Classical.byContradiction fun hout => ?_
      obtain ⟨Q, hQ, h0⟩ := Arrangement.outside_ray P₀.convex (fun V hV => hP₀ V (hm hps.1 hV)) hout
      have hpar := crossing_parity_independent (F.simple ps hps.1) hXb hQ hR
      rw [h0, hodd] at hpar
      exact absurd hpar (by decide)
  /- A larger cell has that whole region inside it (`Arrangement.strict_enclosure`). -/
  obtain ⟨P, hP⟩ := Arrangement.strict_enclosure P₀
  exact ⟨P, fun X hX => hP X (hin X hX)⟩

/-- The supporting straight lines of every contour side form a finite list. -/
theorem outline_side_lines (F : Outline) :
    ∃ ls : List Line, ∀ L : Line, L ∈ ls ↔
      ∃ ps ∈ F.loops, ∃ s ∈ sides ps, OnLine s.1 L ∧ OnLine s.2 L := by
  /- The two ends of a side of a simple contour differ, so one straight line holds both; list
  that line for each side of each contour. -/
  let line (s : Point × Point) : Line := Classical.choose (collinear_of_two s.1 s.2)
  have hline (s : Point × Point) : OnLine s.1 (line s) ∧ OnLine s.2 (line s) :=
    Classical.choose_spec (collinear_of_two s.1 s.2)
  refine ⟨F.loops.flatMap (fun ps => (sides ps).map line), fun L => ?_⟩
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨ps, hps, s, hs, rfl⟩
    exact ⟨ps, hps, s, hs, hline s⟩
  · rintro ⟨ps, hps, s, hs, h₁, h₂⟩
    have hne := (F.simple ps hps).2.2.1 s hs
    exact ⟨ps, hps, s, hs, Tacit.line_unique hne (hline s).1 (hline s).2 h₁ h₂⟩

/-- Cutting a convex cell by finitely many straight lines preserves its exact
closed region and gives cells with disjoint interiors, each off every cut line. -/
theorem convex_arrangement (P : ConvexCell) (ls : List Line) :
    ∃ qs : List ConvexCell, qs ≠ [] ∧
      qs.Pairwise (fun Q R => ∀ X : Point, Q.Core X → ¬ R.Core X) ∧
      (∀ X : Point, P.Region X ↔ ∃ Q ∈ qs, Q.Region X) ∧
      ∀ Q ∈ qs, ∀ L ∈ ls, ∀ X Y : Point,
        Q.Core X → Q.Core Y → SameSide X Y L := by
  /- Cut by one straight line after another, keeping both pieces of every cell
  (`Arrangement.cut_cells`, from `convex_cut`). -/
  induction ls with
  | nil =>
    refine ⟨[P], List.cons_ne_nil _ _, List.pairwise_singleton _ _, fun X => ⟨fun hX =>
      ⟨P, List.mem_singleton_self P, hX⟩, ?_⟩, fun _ _ L hL => absurd hL List.not_mem_nil⟩
    rintro ⟨Q, hQ, hX⟩
    rw [List.mem_singleton.mp hQ] at hX
    exact hX
  | cons L ls ih =>
    obtain ⟨qs, -, hpw, hcov, hside⟩ := ih
    obtain ⟨A, B, hAB⟩ := Arrangement.opposite_pair P L
    obtain ⟨f, hf⟩ := Arrangement.cut_cells hAB
    /- The pieces make up the cells exactly, so the cell P too. -/
    have hcov' : ∀ X : Point, P.Region X ↔ ∃ R ∈ qs.flatMap f, R.Region X := by
      intro X
      rw [hcov X]
      simp only [List.mem_flatMap]
      constructor
      · rintro ⟨Q, hQ, hX⟩
        obtain ⟨R, hR, hRX⟩ := ((hf Q).1 X).mp hX
        exact ⟨R, ⟨Q, hQ, hR⟩, hRX⟩
      · rintro ⟨R, ⟨Q, hQ, hR⟩, hRX⟩
        exact ⟨Q, hQ, ((hf Q).1 X).mpr ⟨R, hR, hRX⟩⟩
    refine ⟨qs.flatMap f, ?_, ?_, hcov', ?_⟩
    · /- A corner of P is in some piece. -/
      obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil P.corners (by
        intro he
        have hl := P.convex.1
        rw [he] at hl
        simp at hl)
      obtain ⟨R, hR, -⟩ := (hcov' c).mp (Extreme.corner_region P.convex hc)
      exact List.ne_nil_of_mem hR
    · /- Pieces of one cell lie on opposite sides; pieces of different cells, inside cells
      that lie apart. -/
      refine List.pairwise_flatMap.mpr ⟨fun Q _ => (hf Q).2.2.2, ?_⟩
      exact hpw.imp fun {Q₁ Q₂} h₁₂ R hR S hS X hRX hSX =>
        h₁₂ X ((hf Q₁).2.1 R hR X hRX) ((hf Q₂).2.1 S hS X hSX)
    · /- Each piece is on one side of the new line, and within its cell for the others. -/
      intro R hR L' hL' X Y hX hY
      obtain ⟨Q, hQ, hRQ⟩ := List.mem_flatMap.mp hR
      rcases List.mem_cons.mp hL' with rfl | hL'
      · exact (hf Q).2.2.1 R hRQ X Y hX hY
      · exact hside Q hQ L' hL' X Y ((hf Q).2.1 R hRQ X hX) ((hf Q).2.1 R hRQ Y hY)

/-- Inside one open arrangement cell, an outline's parity is constant. -/
theorem outline_cell_constant (F : Outline) (Q : ConvexCell) (ls : List Line)
    (hs : ∀ ps ∈ F.loops, ∀ s ∈ sides ps,
      ∃ L ∈ ls, OnLine s.1 L ∧ OnLine s.2 L)
    (hQ : ∀ L ∈ ls, ∀ X Y : Point,
      Q.Core X → Q.Core Y → SameSide X Y L)
    {X Y : Point} (hX : Q.Core X) (hY : Q.Core Y) :
    F.Inside X ↔ F.Inside Y := by
  /- A point of the cell's inside is off every side line, so off the boundary. Join X and Y
  to a third point Z of the inside, off the straight lines from X and from Y to the corners:
  neither finite straight line meets a side line, and good rays along them cross the same
  sides, so no contour's inside changes from X to Z or from Z to Y. -/
  exact CoverFacts.cell_constant F hs hQ hX hY

/-- Selecting the cells with an interior point in the figure gives its exact
closed region, including hole boundaries, auxiliary cuts and corner contacts. -/
theorem outline_cells_cover (F : Outline) (P : ConvexCell)
    (hP : ∀ X : Point, F.Region X → P.Core X) (ls : List Line)
    (hs : ∀ ps ∈ F.loops, ∀ s ∈ sides ps,
      ∃ L ∈ ls, OnLine s.1 L ∧ OnLine s.2 L)
    (qs : List ConvexCell)
    (hc : ∀ X : Point, P.Region X ↔ ∃ Q ∈ qs, Q.Region X)
    (hl : ∀ Q ∈ qs, ∀ L ∈ ls, ∀ X Y : Point,
      Q.Core X → Q.Core Y → SameSide X Y L) :
    ∃ rs : List ConvexCell, rs ≠ [] ∧ rs.Sublist qs ∧
      (∀ Q : ConvexCell, Q ∈ rs ↔
        Q ∈ qs ∧ ∃ X : Point, Q.Core X ∧ F.Inside X) ∧
      (∀ X : Point, F.Region X ↔ ∃ Q ∈ rs, Q.Region X) := by
  classical
  /- Keep the cells with a point of their inside inside the figure. -/
  obtain ⟨rs, hrs⟩ : ∃ rs : List ConvexCell,
      rs = qs.filter fun Q => decide (∃ X : Point, Q.Core X ∧ F.Inside X) := ⟨_, rfl⟩
  have hmem : ∀ Q : ConvexCell, Q ∈ rs ↔ Q ∈ qs ∧ ∃ X : Point, Q.Core X ∧ F.Inside X := by
    intro Q
    rw [hrs, List.mem_filter, decide_eq_true_eq]
  have hreg : ∀ X : Point, F.Region X ↔ ∃ Q ∈ rs, Q.Region X := by
    intro X
    constructor
    · /- Near X lie only the cells whose closed regions hold X (`clear_of_cells`). Near X there
      is a point Y inside the figure: X itself, or, on the boundary, an end of a short finite
      straight line across a side, near a point of that side at no corner, where exactly one
      contour's inside changes (`region_filled`). Y lies in some cell, which therefore holds
      X; and from Y a point of that cell's inside is inside the figure as Y is
      (`cell_point`). -/
      intro hX
      obtain ⟨hp, hp1, hp2⟩ := CoverFacts.clear_of_cells X qs
      obtain ⟨Y, hY, hYp⟩ := CoverFacts.region_filled F hX hp hp1
      obtain ⟨Q, hQ, hQY⟩ := (hc Y).mp (Tiling.core_region (hP Y (Or.inr hY)))
      obtain ⟨W, hW, hWY⟩ := CoverFacts.cell_point F hs (hl Q hQ) hY.1 hQY
      exact ⟨Q, (hmem Q).mpr ⟨hQ, W, hW, hWY.mpr hY⟩, hp2 Y hYp Q hQ hQY⟩
    · /- A kept cell's inside is inside the figure throughout (`outline_cell_constant`). A
      point of its closed region off the boundary has a point of its inside that is inside the
      figure exactly when it is (`cell_point`), so it is inside the figure too. -/
      rintro ⟨Q, hQ, hQX⟩
      obtain ⟨hQ, Z, hZ, hZi⟩ := (hmem Q).mp hQ
      by_cases hb : F.Boundary X
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
        ∀ X : Point, Between A X B → LoopInside ps X := by
  /- An extreme corner V, with every other corner strictly across a straight line through it,
  has neighbours U and W. Either UW is an interior diagonal (an ear), or a corner in the
  triangle VUW (inside it, or strictly between U and W), on a straight line across V that cuts
  off a triangle with no corner inside it, is joined to V by one (`Diagonal.diagonal_exists`). Two
  corners that are not neighbours split the loop read from one of them
  (`Diagonal.diagonal_rotate`). -/
  obtain ⟨A, hA, B, hB, hAB, h₁, h₂, hd⟩ := Diagonal.diagonal_exists h hn
  obtain ⟨n, us, vs, he, hu, hv⟩ := Diagonal.diagonal_rotate h.2.1 hA hB hAB h₁ h₂
  exact ⟨n, A, B, us, vs, he, hu, hv, hd⟩

/-- An interior diagonal splits a simple region into two simple regions with
exactly that diagonal in common. Disjoint interiors need their own argument. -/
theorem simple_diagonal_partition {A B : Point} {us vs : List Point}
    (h : SimpleLoop (A :: (us ++ B :: vs))) (hu : us ≠ []) (hv : vs ≠ [])
    (hd : ∀ X : Point, Between A X B → LoopInside (A :: (us ++ B :: vs)) X) :
    SimpleLoop (A :: (us ++ [B])) ∧ SimpleLoop (B :: (vs ++ [A])) ∧
      (∀ X : Point, LoopRegion (A :: (us ++ B :: vs)) X ↔
        LoopRegion (A :: (us ++ [B])) X ∨ LoopRegion (B :: (vs ++ [A])) X) ∧
      (∀ X : Point,
        (LoopRegion (A :: (us ++ [B])) X ∧ LoopRegion (B :: (vs ++ [A])) X) ↔
          OnFiniteLine X A B) := by
  /- Read the loop as two chains, A through `us` to B and B through `vs` to A; each piece is a
  chain closed by the diagonal. The pieces are simple: the diagonal meets a side only at A or B,
  its other points being inside (`Diagonal.piece_simple`). Off the sides and the diagonal, a good
  ray crosses the loop as often as both pieces together, less the diagonal twice, so the loop's
  inside is the points inside exactly one piece (`Diagonal.inside_xor`). That parity cancellation
  does not keep the pieces apart; a separate argument does: along each chain the other piece's
  inside is constant, and rays from either side of the diagonal show it is outside
  (`Diagonal.chains_outside`); so no point is inside both pieces (`Diagonal.pieces_apart`). -/
  have hP := Diagonal.piece_simple h hu hd
  have hQ := Diagonal.piece_simple₂ h hv hd
  obtain ⟨ho₁, ho₂⟩ := Diagonal.chains_outside h hu hv hd
  have hb := Diagonal.boundary_split (A := A) (B := B) (us := us) (vs := vs)
  have hbP := Diagonal.boundary_piece A B us
  have hbQ := Diagonal.boundary_piece B A vs
  have hA : A ∈ A :: (us ++ B :: vs) := List.mem_cons_self
  have hB : B ∈ A :: (us ++ B :: vs) := by simp
  /- A point of the diagonal is in the loop's region: A and B on its boundary, the rest inside. -/
  have diag {X : Point} (hX : OnFiniteLine X A B) : LoopRegion (A :: (us ++ B :: vs)) X := by
    rcases hX with rfl | rfl | hX
    · exact Or.inl (OutlineFacts.vertex_boundary hA)
    · exact Or.inl (OutlineFacts.vertex_boundary hB)
    · exact Or.inr (hd X hX)
  /- A point inside one piece and off the loop's boundary is inside the loop: off the diagonal,
  and not inside the other piece. -/
  have one {X : Point} (h₁ : LoopInside (A :: (us ++ [B])) X ∨ LoopInside (B :: (vs ++ [A])) X)
      (hXb : ¬ LoopBoundary (A :: (us ++ B :: vs)) X) (hXd : ¬ OnFiniteLine X A B) :
      LoopInside (A :: (us ++ B :: vs)) X := by
    refine (Diagonal.inside_xor h hu hv hd hXb hXd).mpr ⟨fun hi hi' => ?_, fun hn => ?_⟩
    · exact Diagonal.pieces_apart h hu hv hd hi hi'
    · exact h₁.resolve_right hn
  refine ⟨hP, hQ, fun X => ⟨?_, ?_⟩, fun X => ⟨?_, ?_⟩⟩
  · /- The loop's region is in the pieces': its boundary is the two chains, and inside it, off
    the diagonal, a point is inside one piece. -/
    rintro (hX | hX)
    · rcases (hb X).mp hX with hc | hc
      · exact Or.inl (Or.inl ((hbP X).mpr (Or.inl hc)))
      · exact Or.inr (Or.inl ((hbQ X).mpr (Or.inl hc)))
    · by_cases hXd : OnFiniteLine X A B
      · exact Or.inl (Or.inl ((hbP X).mpr (Or.inr hXd)))
      · have e := (Diagonal.inside_xor h hu hv hd hX.1 hXd).mp hX
        by_cases h₁ : LoopInside (A :: (us ++ [B])) X
        · exact Or.inl (Or.inr h₁)
        · exact Or.inr (Or.inr (Classical.byContradiction fun h₂ => h₁ (e.mpr h₂)))
  · /- The pieces' regions are in the loop's: a chain is on its boundary, the diagonal in its
    region, and a point inside a piece is on its boundary or inside it. -/
    have inside {X : Point} (hi : LoopInside (A :: (us ++ [B])) X ∨
        LoopInside (B :: (vs ++ [A])) X) (hXd : ¬ OnFiniteLine X A B) :
        LoopRegion (A :: (us ++ B :: vs)) X := by
      by_cases hXb : LoopBoundary (A :: (us ++ B :: vs)) X
      · exact Or.inl hXb
      · exact Or.inr (one hi hXb hXd)
    rintro ((hX | hX) | (hX | hX))
    · rcases (hbP X).mp hX with hc | hc
      · exact Or.inl ((hb X).mpr (Or.inl hc))
      · exact diag hc
    · exact inside (Or.inl hX) fun hc => hX.1 ((hbP X).mpr (Or.inr hc))
    · rcases (hbQ X).mp hX with hc | hc
      · exact Or.inl ((hb X).mpr (Or.inr hc))
      · exact diag (LoopFacts.onFiniteLine_comm.mp hc)
    · exact inside (Or.inr hX) fun hc =>
        hX.1 ((hbQ X).mpr (Or.inr (LoopFacts.onFiniteLine_comm.mp hc)))
  · /- In both regions means on the diagonal: two chains meet only at A and B (`chains_meet`),
    each chain but A and B is outside the other piece, and no point is inside both. -/
    have on_ends {Y : Point} (e : Y = A ∨ Y = B) : OnFiniteLine Y A B := by
      rcases e with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    rintro ⟨hX₁ | hX₁, hX₂ | hX₂⟩
    · rcases (hbP X).mp hX₁ with ⟨s, hs, hXs⟩ | hc
      · rcases (hbQ X).mp hX₂ with ⟨t, ht, hXt⟩ | hc
        · exact on_ends (Diagonal.chains_meet h hs ht hXs hXt)
        · exact LoopFacts.onFiniteLine_comm.mp hc
      · exact hc
    · rcases (hbP X).mp hX₁ with hc | hc
      · by_cases hXA : X = A
        · exact Or.inl hXA
        by_cases hXB : X = B
        · exact Or.inr (Or.inl hXB)
        exact absurd hX₂ (ho₁ X hc hXA hXB)
      · exact hc
    · rcases (hbQ X).mp hX₂ with hc | hc
      · by_cases hXA : X = A
        · exact Or.inl hXA
        by_cases hXB : X = B
        · exact Or.inr (Or.inl hXB)
        exact absurd hX₁ (ho₂ X hc hXA hXB)
      · exact LoopFacts.onFiniteLine_comm.mp hc
    · exact (Diagonal.pieces_apart h hu hv hd hX₁ hX₂).elim
  · /- The diagonal is a side of each piece. -/
    intro hX
    exact ⟨Or.inl ((hbP X).mpr (Or.inr hX)),
      Or.inl ((hbQ X).mpr (Or.inr (LoopFacts.onFiniteLine_comm.mp hX)))⟩

/-- A simple outline admits a division. The arrangement route proves it; the optional
diagonal route, splitting the outline along interior diagonals, could prove it too. -/
theorem simple_triangulation {ps : List Point} (h : SimpleLoop ps) :
    ∃ R : Apart, Divides (LoopRegion ps) R := by
  /- The arrangement route (ledger D9), not the diagonal route: the one-contour outline of
  `ps` (`singleOutline`, whose compatibility is vacuous) has the loop's region
  (`single_region`). A convex cell holds it strictly inside (`outline_enclosure`); the side
  lines (`outline_side_lines`) cut the cell into cells with disjoint insides
  (`convex_arrangement`); those with a point inside the outline make up its region exactly
  (`outline_cells_cover`), and their fans divide it (`DivisionFacts.cells_division`). -/
  let F := singleOutline ps h
  obtain ⟨P, hP⟩ := outline_enclosure F
  obtain ⟨ls, hls⟩ := outline_side_lines F
  have hs : ∀ qs ∈ F.loops, ∀ s ∈ sides qs, ∃ L ∈ ls, OnLine s.1 L ∧ OnLine s.2 L := by
    intro qs hqs s hs
    obtain ⟨L, h₁, h₂⟩ := collinear_of_two s.1 s.2
    exact ⟨L, (hls L).mpr ⟨qs, hqs, s, hs, h₁, h₂⟩, h₁, h₂⟩
  obtain ⟨qs, -, ha, hc, hl⟩ := convex_arrangement P ls
  obtain ⟨rs, hne, hsub, -, hcov⟩ := outline_cells_cover F P hP ls hs qs hc hl
  obtain ⟨R, -, hR⟩ := DivisionFacts.cells_division rs hne (List.Pairwise.sublist hsub ha)
  exact ⟨R, fun X => (hR X).trans ((hcov X).symm.trans (single_region ps h X))⟩

end Elements.Figures
