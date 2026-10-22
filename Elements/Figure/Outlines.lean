import Elements.Foundations.Figures
import Elements.Figure.Basics
import Elements.Figure.Rectilineal
import Elements.Figure.Outlines.LoopFacts
import Elements.Figure.Outlines.Parity
import Elements.Figure.Outlines.OutlineFacts
import Elements.Figure.Sides
import Elements.Figure.Angles

/-!
The boundary bridges proposed by brief 0013, with their proofs.
Only `outline_bounded` cites a proposition of the Elements: its enclosing triangle
(`OutlineBound.lean`) copies an angle by I.23 and uses Postulate 5, so this file imports I.23
and the propositions it rests on. The other statements cite no proposition and rest on
neither Postulate 5 nor superposition.
-/

namespace Elements.Figures

/-- Every point off a simple boundary admits a ray avoiding all its vertices. -/
theorem good_ray_exists {ps : List Point} (h : SimpleLoop ps) {X : Point}
    (hX : ¬ loopBoundary ps X) : ∃ Q : Point, GoodRay ps X Q := by
  /- Every corner starts a side, so is on the boundary, and differs from X. -/
  have hne : ∀ V ∈ ps, V ≠ X := by
    intro V hV hVX
    obtain ⟨E, hE⟩ := outgoing_side hV
    exact hX ⟨(V, E), hE, Or.inl hVX.symm⟩
  /- The straight lines joining X to the corners, and a frame of three corners from
  simplicity. A point of the frame off all those lines gives the ray. -/
  let line (V : Point) : Line := Classical.choose (collinear_of_two X V)
  have hline (V : Point) : OnLine X (line V) ∧ OnLine V (line V) :=
    Classical.choose_spec (collinear_of_two X V)
  obtain ⟨A, hA, B, -, C, -, hABC⟩ := LoopFacts.simple_frame h
  obtain ⟨Q, -, hQ⟩ := triangle_point_avoiding hABC (ps.map line)
  refine ⟨Q, fun hXQ => ?_, fun V hV hcol => ?_⟩
  · exact hQ (line A) (List.mem_map_of_mem hA) (hXQ ▸ (hline A).1)
  · obtain ⟨M, hXM, hQM, hVM⟩ := hcol
    have he : line V = M := Tacit.line_unique (hne V hV).symm (hline V).1 (hline V).2 hXM hVM
    exact hQ (line V) (List.mem_map_of_mem hV) (he ▸ hQM)

/-- Two good rays from the same point give the same crossing parity. -/
theorem crossing_parity_independent {ps : List Point} (h : SimpleLoop ps)
    {X Q R : Point} (hX : ¬ loopBoundary ps X)
    (hQ : GoodRay ps X Q) (hR : GoodRay ps X R) :
    crossingCount ps X Q % 2 = crossingCount ps X R % 2 := by
  /- Each side crosses two rays not on one straight line together oddly exactly when its
  ends disagree about the angle between them, and round the outline those ends pair off.
  Rays on one straight line each compare with a third good ray off it. -/
  exact Parity.parity_independent h hX hQ hR

/-- Any good ray decides interior membership, once the point is off the boundary. -/
theorem loop_inside_iff {ps : List Point} (h : SimpleLoop ps)
    {X Q : Point} (hX : ¬ loopBoundary ps X) (hQ : GoodRay ps X Q) :
    loopInside ps X ↔ crossingCount ps X Q % 2 = 1 := by
  constructor
  · rintro ⟨_, R, hR, hodd⟩
    exact (crossing_parity_independent h hX hQ hR).trans hodd
  · intro hodd
    exact ⟨hX, Q, hQ, hodd⟩

/-- Reversing a simple outline preserves its boundary and its region. -/
theorem loop_reverse {ps : List Point} (h : SimpleLoop ps) :
    SimpleLoop ps.reverse ∧
      (∀ X : Point, loopBoundary ps.reverse X ↔ loopBoundary ps X) ∧
      (∀ X : Point, loopRegion ps.reverse X ↔ loopRegion ps X) := by
  /- The reversed outline has the same sides, each read the other way. -/
  have hf : ∀ s : Point × Point, Prod.swap s = s ∨ Prod.swap s = s.swap := fun _ => Or.inr rfl
  have hperm := LoopFacts.sides_reverse_perm ps
  obtain ⟨hb, hc, hg⟩ := LoopFacts.transfer hf hperm fun _ => List.mem_reverse
  exact ⟨LoopFacts.simple_transfer hf hperm List.length_reverse
      (List.reverse_perm ps).nodup_iff.mpr h,
    hb, LoopFacts.region_transfer hb hc hg⟩

/-- Starting at another vertex preserves simplicity, boundary and region. -/
theorem loop_rotate (ps qs : List Point) (h : SimpleLoop (ps ++ qs)) :
    SimpleLoop (qs ++ ps) ∧
      (∀ X : Point, loopBoundary (qs ++ ps) X ↔ loopBoundary (ps ++ qs) X) ∧
      (∀ X : Point, loopRegion (qs ++ ps) X ↔ loopRegion (ps ++ qs) X) := by
  /- Read from another corner, the outline has the same sides, in another order. -/
  have hf : ∀ s : Point × Point, id s = s ∨ id s = s.swap := fun _ => Or.inl rfl
  have hperm : (sides (qs ++ ps)).Perm ((sides (ps ++ qs)).map id) := by
    rw [List.map_id]
    exact LoopFacts.sides_rotate_perm qs ps
  obtain ⟨hb, hc, hg⟩ := LoopFacts.transfer hf hperm fun _ => by
    simp only [List.mem_append]
    exact or_comm
  exact ⟨LoopFacts.simple_transfer hf hperm (by simp only [List.length_append]; omega)
      List.perm_append_comm.nodup_iff.mp h,
    hb, LoopFacts.region_transfer hb hc hg⟩

/-- Redundant collinear vertices can be removed without changing the figure. -/
theorem loop_normalise {ps : List Point} (h : SimpleLoop ps) :
    ∃ qs : List Point, SimpleLoop qs ∧ ReducedLoop qs ∧
      (∀ X : Point, loopBoundary qs X ↔ loopBoundary ps X) ∧
      (∀ X : Point, loopRegion qs X ↔ loopRegion ps X) := by
  /- By induction on the number of corners. A loop that is not reduced has a corner between
  its neighbours (`Parity.straight_corner`); read from the corner before it, the loop loses
  that corner and keeps its boundary and region (`Parity.remove_corner`). A corner that
  turns back is never removed: simplicity puts the middle corner between the others. -/
  obtain ⟨n, hn⟩ : ∃ n, ps.length = n := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing ps with
  | ind n ih =>
    by_cases hr : ReducedLoop ps
    · exact ⟨ps, h, hr, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
    obtain ⟨us, vs, a, b, c, rest, rfl, hrot, hrest, habc⟩ := Parity.straight_corner h hr
    obtain ⟨hs₁, hb₁, hg₁⟩ := loop_rotate us vs h
    rw [hrot] at hs₁ hb₁ hg₁
    obtain ⟨hs₂, hb₂, hg₂⟩ := Parity.remove_corner hs₁ hrest habc
    have hlen : (a :: c :: rest).length < n := by
      have e := congrArg List.length hrot
      simp only [List.length_append, List.length_cons] at e hn ⊢
      omega
    obtain ⟨qs, hq, hqr, hqb, hqg⟩ := ih _ hlen hs₂ rfl
    exact ⟨qs, hq, hqr, fun X => (hqb X).trans ((hb₂ X).trans (hb₁ X)),
      fun X => (hqg X).trans ((hg₂ X).trans (hg₁ X))⟩

/-- A triangle's outline encloses exactly its existing closed triangle. -/
theorem triangle_region {A B C : Point} (h : Triangle A B C) :
    SimpleLoop [A, B, C] ∧
      ∀ X : Point, loopRegion [A, B, C] X ↔ OnOrInsideTriangle X A B C := by
  /- A triangle's corners make a convex outline, whose closed region is the closed
  triangle (`closed_triangle_sides`). From a point inside it a good ray crosses one side;
  from a point outside, none or two. -/
  have hc := Ext.triangle_outline h
  have hsimple := LoopFacts.convex_simple hc
  refine ⟨hsimple, fun X => ?_⟩
  rw [← LoopFacts.triangle_convexRegion h]
  constructor
  · rintro (hb | ⟨hXb, Q, hQ, hodd⟩)
    · exact LoopFacts.convex_boundary_region hc hb
    · refine Classical.byContradiction fun hX => ?_
      rcases LoopFacts.convex_count_outside hc hX hXb hQ with h0 | h2
      · rw [h0] at hodd
        exact absurd hodd (by decide)
      · rw [h2] at hodd
        exact absurd hodd (by decide)
  · intro hX
    by_cases hXb : loopBoundary [A, B, C] X
    · exact Or.inl hXb
    · obtain ⟨Q, hQ⟩ := good_ray_exists hsimple hXb
      exact Or.inr ⟨hXb, Q, hQ, by rw [LoopFacts.convex_count_inside hc hX hXb hQ]⟩

/-- A single contour has exactly its loop's region. -/
theorem single_region (ps : List Point) (h : SimpleLoop ps) (X : Point) :
    (singleOutline ps h).region X ↔ loopRegion ps X := by
  /- With one contour, the boundary is its boundary, and the depth is one exactly when
  the point is inside it. -/
  have hb : (singleOutline ps h).boundary X ↔ loopBoundary ps X := by
    simp [Outline.boundary, singleOutline]
  have hd : (singleOutline ps h).depth X % 2 = 1 ↔ loopInside ps X := by
    unfold Outline.depth
    by_cases hi : loopInside ps X <;> simp [singleOutline, hi]
  unfold Outline.region Outline.inside loopRegion
  rw [hb, hd]
  constructor
  · rintro (hb | ⟨-, hi⟩)
    · exact Or.inl hb
    · exact Or.inr hi
  · rintro (hb | hi)
    · exact Or.inl hb
    · exact Or.inr ⟨hi.1, hi⟩

/-- A strictly convex outline is simple, and its loop region is exactly the
intersection of its inward closed sides. -/
theorem convex_loop_region {cs : List Point} (h : ConvexOutline cs) :
    SimpleLoop cs ∧ ∀ X : Point, loopRegion cs X ↔ ConvexRegion cs X := by
  /- Two sides meet only at a common end, each other corner being strictly on one side of
  a side's straight line. A boundary point is in the region. From a point strictly inside,
  a good ray crosses exactly one side; from a point outside the region, none or two. -/
  have hsimple := LoopFacts.convex_simple h
  refine ⟨hsimple, fun X => ⟨?_, ?_⟩⟩
  · rintro (hb | ⟨hXb, Q, hQ, hodd⟩)
    · exact LoopFacts.convex_boundary_region h hb
    · refine Classical.byContradiction fun hX => ?_
      rcases LoopFacts.convex_count_outside h hX hXb hQ with h0 | h2
      · rw [h0] at hodd
        exact absurd hodd (by decide)
      · rw [h2] at hodd
        exact absurd hodd (by decide)
  · intro hX
    by_cases hXb : loopBoundary cs X
    · exact Or.inl hXb
    · obtain ⟨Q, hQ⟩ := good_ray_exists hsimple hXb
      exact Or.inr ⟨hXb, Q, hQ, by rw [LoopFacts.convex_count_inside h hX hXb hQ]⟩

/-- A supporting line cuts out exactly the finite side of a strictly convex outline. -/
theorem convex_supporting_side {cs : List Point} (h : ConvexOutline cs)
    {s : Point × Point} (hs : s ∈ sides cs) (X : Point) :
    (ConvexRegion cs X ∧ Collinear s.1 s.2 X) ↔ OnFiniteLine X s.1 s.2 := by
  /- Beyond either end, a point of the side's straight line crosses the straight line of
  the neighbouring side there, away from the region (`LoopFacts.convex_supporting`).
  Conversely, the finite side is on its straight line and in the region. -/
  constructor
  · rintro ⟨hX, hcol⟩
    exact LoopFacts.convex_supporting h hs hX hcol
  · intro hX
    refine ⟨LoopFacts.convex_boundary_region h ⟨s, hs, hX⟩, ?_⟩
    obtain ⟨L, h₁, h₂⟩ := collinear_of_two s.1 s.2
    exact ⟨L, h₁, h₂, LoopFacts.onFiniteLine_onLine hX h₁ h₂⟩

/-- The stated contours are exactly the boundary of the independently defined region. -/
theorem outline_boundary (F : Outline) (X : Point) :
    F.boundary X ↔ RegionBoundary F.region X := by
  /- On a contour, the point is in the region, and across a side of its contour, away from
  every corner, the depth changes parity: no other contour passes there. Off the contours, a
  small triangle about the point misses every side, and no contour's inside changes in it. -/
  constructor
  · exact OutlineFacts.boundary_regionBoundary F
  · intro hR
    exact Classical.byContradiction fun hX => OutlineFacts.not_regionBoundary F hX hR

/-- The same boundary describes the same region, regardless of its listing,
orientations, starting vertices or decomposition into simple contours. -/
theorem same_boundary_region (F G : Outline)
    (h : ∀ X : Point, F.boundary X ↔ G.boundary X) :
    ∀ X : Point, F.region X ↔ G.region X := by
  /- Off the boundary, the depth has the parity of the crossings of one good ray, through no
  corner of either description. Each crossing is a point of the boundary, read as a point set,
  strictly within exactly one side of one contour, however the sides are subdivided; so both
  descriptions count the same points. -/
  intro X
  by_cases hX : F.boundary X
  · exact ⟨fun _ => Or.inl ((h X).mp hX), fun _ => Or.inl hX⟩
  · have hXG : ¬ G.boundary X := fun hg => hX ((h X).mpr hg)
    rw [OutlineFacts.region_off hX, OutlineFacts.region_off hXG,
      OutlineFacts.depth_parity_eq F G h hX]

/-- Every outline has a reduced description with the same boundary.
Contacts against the middle of a side remain allowed. -/
theorem outline_normalise (F : Outline) :
    ∃ G : Outline, (∀ ps ∈ G.loops, ReducedLoop ps) ∧
      ∀ X : Point, G.boundary X ↔ F.boundary X := by
  /- Normalise each contour (`loop_normalise`), keeping its boundary and region, so its
  inside. The reduced family is still compatible: a contact strictly within a side of each
  reduced contour would be, for the original contours, either an overlap of two sides on one
  straight line, with infinitely many contacts, or a crossing, near which insides are neither
  disjoint nor nested (`OutlineFacts.contact_vertex`). So a redundant corner of one contour
  that lies on another is a true corner of that other, and contacts survive. -/
  classical
  have hn : ∀ ps ∈ F.loops, ∃ qs : List Point, SimpleLoop qs ∧ ReducedLoop qs ∧
      (∀ X : Point, loopBoundary qs X ↔ loopBoundary ps X) ∧
      (∀ X : Point, loopRegion qs X ↔ loopRegion ps X) :=
    fun ps hps => loop_normalise (F.simple ps hps)
  let f : List Point → List Point := fun ps =>
    if h : ps ∈ F.loops then Classical.choose (hn ps h) else ps
  have hf : ∀ ps ∈ F.loops, SimpleLoop (f ps) ∧ ReducedLoop (f ps) ∧
      (∀ X : Point, loopBoundary (f ps) X ↔ loopBoundary ps X) ∧
      (∀ X : Point, loopRegion (f ps) X ↔ loopRegion ps X) := by
    intro ps hps
    have e : f ps = Classical.choose (hn ps hps) := by simp only [f, hps, ↓reduceDIte]
    rw [e]
    exact Classical.choose_spec (hn ps hps)
  refine ⟨⟨F.loops.map f, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro e
    exact F.ne (List.map_eq_nil_iff.mp e)
  · intro qs hqs
    obtain ⟨ps, hps, rfl⟩ := List.mem_map.mp hqs
    exact (hf ps hps).1
  · rw [List.pairwise_map]
    refine F.compatible.imp_of_mem fun {a b} ha hb hab => ?_
    obtain ⟨ha₁, -, ha₃, ha₄⟩ := hf a ha
    obtain ⟨hb₁, -, hb₃, hb₄⟩ := hf b hb
    exact OutlineFacts.compatible_transfer ha₁ hb₁ ha₃ ha₄ hb₃ hb₄ hab
  · intro qs hqs
    obtain ⟨ps, hps, rfl⟩ := List.mem_map.mp hqs
    exact (hf ps hps).2.1
  · intro X
    constructor
    · rintro ⟨qs, hqs, hX⟩
      obtain ⟨ps, hps, rfl⟩ := List.mem_map.mp hqs
      exact ⟨ps, hps, ((hf ps hps).2.2.1 X).mp hX⟩
    · rintro ⟨ps, hps, hX⟩
      exact ⟨f ps, List.mem_map_of_mem hps, ((hf ps hps).2.2.1 X).mpr hX⟩

/-- One outer contour with unnested holes means its closed region with the
strict interiors of the holes removed. All hole boundaries remain.
Isolated contacts are allowed by the outline's compatibility condition. -/
theorem region_with_holes (F : Outline) (outer : List Point)
    (holes : List (List Point)) (hl : F.loops = outer :: holes)
    (hin : ∀ ps ∈ holes, ∀ X : Point, loopRegion ps X → loopRegion outer X)
    (hapart : holes.Pairwise (fun ps qs =>
      ∀ X : Point, loopInside ps X → ¬ loopInside qs X))
    (X : Point) :
    F.region X ↔ loopRegion outer X ∧
      ∀ ps ∈ holes, ¬ loopInside ps X := by
  /- Off the boundary, the depth counts the outer contour and at most one hole, which lies
  in it. On the boundary, no hole holds the point inside: near a point of any contour are
  points inside that contour and outside the outer region, while near a point inside a hole
  every point is inside it. -/
  exact OutlineFacts.region_holes F outer holes hl hin hapart X

end Elements.Figures
