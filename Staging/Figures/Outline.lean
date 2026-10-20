import Staging.Figures.Loops
import Elements.Figure.Sides
import Elements.Figure.Angles

/-!
The boundary bridges proposed by brief 0013. Their own proofs await approval.
No proposition of the Elements is imported.
-/

namespace Elements.Figures

/-- Every point off a simple boundary admits a ray avoiding all its vertices. -/
theorem good_ray_exists {ps : List Point} (h : SimpleLoop ps) {X : Point}
    (hX : ¬ loopBoundary ps X) : ∃ Q : Point, GoodRay ps X Q := by
  sorry

/-- Two good rays from the same point give the same crossing parity. -/
theorem crossing_parity_independent {ps : List Point} (h : SimpleLoop ps)
    {X Q R : Point} (hX : ¬ loopBoundary ps X)
    (hQ : GoodRay ps X Q) (hR : GoodRay ps X R) :
    crossingCount ps X Q % 2 = crossingCount ps X R % 2 := by
  sorry

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
  sorry

/-- Starting at another vertex preserves simplicity, boundary and region. -/
theorem loop_rotate (ps qs : List Point) (h : SimpleLoop (ps ++ qs)) :
    SimpleLoop (qs ++ ps) ∧
      (∀ X : Point, loopBoundary (qs ++ ps) X ↔ loopBoundary (ps ++ qs) X) ∧
      (∀ X : Point, loopRegion (qs ++ ps) X ↔ loopRegion (ps ++ qs) X) := by
  sorry

/-- Redundant collinear vertices can be removed without changing the figure. -/
theorem loop_normalise {ps : List Point} (h : SimpleLoop ps) :
    ∃ qs : List Point, SimpleLoop qs ∧ ReducedLoop qs ∧
      (∀ X : Point, loopBoundary qs X ↔ loopBoundary ps X) ∧
      (∀ X : Point, loopRegion qs X ↔ loopRegion ps X) := by
  sorry

/-- A triangle's outline encloses exactly its existing closed triangle. -/
theorem triangle_region {A B C : Point} (h : Triangle A B C) :
    SimpleLoop [A, B, C] ∧
      ∀ X : Point, loopRegion [A, B, C] X ↔ OnOrInsideTriangle X A B C := by
  sorry

/-- A single contour has exactly its loop's region. -/
theorem single_region (ps : List Point) (h : SimpleLoop ps) (X : Point) :
    (singleOutline ps h).region X ↔ loopRegion ps X := by
  sorry

/-- A strictly convex outline is simple, and its loop region is exactly the
intersection of its inward closed sides. -/
theorem convex_loop_region {cs : List Point} (h : ConvexOutline cs) :
    SimpleLoop cs ∧ ∀ X : Point, loopRegion cs X ↔ ConvexRegion cs X := by
  sorry

/-- A supporting line cuts out exactly the finite side of a strictly convex outline. -/
theorem convex_supporting_side {cs : List Point} (h : ConvexOutline cs)
    {s : Point × Point} (hs : s ∈ sides cs) (X : Point) :
    (ConvexRegion cs X ∧ Collinear s.1 s.2 X) ↔ OnFiniteLine X s.1 s.2 := by
  sorry

/-- Every admitted figure is bounded, with an enclosing triangle. -/
theorem outline_bounded (F : Outline) :
    ∃ A B C : Point, Triangle A B C ∧
      ∀ X : Point, F.region X → InsideTriangle X A B C := by
  sorry

/-- The stated contours are exactly the boundary of the independently defined region. -/
theorem outline_boundary (F : Outline) (X : Point) :
    F.boundary X ↔ RegionBoundary F.region X := by
  sorry

/-- The same boundary describes the same region, regardless of its listing,
orientations, starting vertices or decomposition into simple contours. -/
theorem same_boundary_region (F G : Outline)
    (h : ∀ X : Point, F.boundary X ↔ G.boundary X) :
    ∀ X : Point, F.region X ↔ G.region X := by
  sorry

/-- Every outline has a reduced description with the same boundary.
Contacts against the middle of a side remain allowed. -/
theorem outline_normalise (F : Outline) :
    ∃ G : Outline, (∀ ps ∈ G.loops, ReducedLoop ps) ∧
      ∀ X : Point, G.boundary X ↔ F.boundary X := by
  sorry

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
  sorry

end Elements.Figures
