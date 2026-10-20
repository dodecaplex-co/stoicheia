import Staging.Figures.Convex

/-!
# Staging: the fan of a convex outline has one sum, from any corner

Prototype statements for brief 0013 (a draft for the owner's approval), with `sorry` where
a proof is due. The words are in `Staging/Figures/Convex.lean`.
-/

namespace Elements.Figures

open Tacit

/-- **The fan does not depend on its corner**: read from the next corner, the sum is the
same. -/
theorem fanSum_rotate {c : Point} {cs : List Point} (h : ConvexOutline (c :: cs)) :
    fanSum (cs ++ [c]) = fanSum (c :: cs) := by
  sorry

/-- Read the other way round, the fan's sum is the same. -/
theorem fanSum_reverse {cs : List Point} (h : ConvexOutline cs) :
    fanSum cs.reverse = fanSum cs := by
  sorry

end Elements.Figures
