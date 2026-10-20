import Staging.Figures.Convex

/-!
# Staging: the fan of a convex outline covers its region

Prototype statements for brief 0013 (a draft for the owner's approval), with `sorry` where
a proof is due. The words are in `Staging/Figures/Convex.lean`.
-/

namespace Elements.Figures

open Tacit

/-- A convex outline read from its second corner is convex. -/
theorem ConvexOutline.rotate {c : Point} {cs : List Point} (h : ConvexOutline (c :: cs)) :
    ConvexOutline (cs ++ [c]) := by
  sorry

/-- A convex outline read the other way round is convex. -/
theorem ConvexOutline.reverse {cs : List Point} (h : ConvexOutline cs) :
    ConvexOutline cs.reverse := by
  sorry

/-- The region does not depend on the corner the outline is read from. -/
theorem convexRegion_rotate (c : Point) (cs : List Point) (X : Point) :
    ConvexRegion (cs ++ [c]) X ↔ ConvexRegion (c :: cs) X := by
  sorry

/-- Each triangle of a convex outline's fan is a triangle. -/
theorem fan_triangle {cs : List Point} (h : ConvexOutline cs) :
    ∀ t ∈ fan cs, Triangle t.1 t.2.1 t.2.2 := by
  sorry

/-- No point is inside two triangles of a convex outline's fan. -/
theorem fan_apart {cs : List Point} (h : ConvexOutline cs) :
    (fan cs).Pairwise fun s s' => ∀ Y : Point,
      InsideTriangle Y s.1 s.2.1 s.2.2 → ¬ InsideTriangle Y s'.1 s'.2.1 s'.2.2 := by
  sorry

/-- **The boundary bridge**: the fan's triangles cover exactly the region of the outline. -/
theorem fan_covers {cs : List Point} (h : ConvexOutline cs) (X : Point) :
    Covers (fan cs) X ↔ ConvexRegion cs X := by
  sorry

end Elements.Figures
