import Elements.Figure.Convex.Facts
import Elements.Figure.Convex.AreaHelpers

/-!
# Staging: the fan of a convex outline has one sum, from any corner

Successive diagonal changes preserve the fan sum when its first corner changes.
Reversing the corner order preserves the sum too. These results compare vertex
fans of strictly convex outlines. The words are in `Staging/Figures/Convex.lean`.
-/

namespace Elements.Figures

open Tacit

/-- Reading the convex outline from its next corner preserves the fan sum. -/
theorem fanSum_rotate {c : Point} {cs : List Point} (h : ConvexOutline (c :: cs)) :
    fanSum (cs ++ [c]) = fanSum (c :: cs) := by
  cases cs with
  | nil => exact False.elim (by simpa using h.1)
  | cons B cs =>
    cases cs with
    | nil => exact False.elim (by simpa using h.1)
    | cons C ps =>
      change fanSum (B :: ((C :: ps) ++ [c])) = fanSum (c :: B :: C :: ps)
      rw [fanSum_cons, fanSum_cons]
      exact (fanArea_rotate c B C ps h.fan_cross).symm

/-- Read the other way round, the fan's sum is the same. -/
theorem fanSum_reverse {cs : List Point} (h : ConvexOutline cs) :
    fanSum cs.reverse = fanSum cs := by
  cases hr : cs.reverse with
  | nil =>
    have he : cs = [] := List.reverse_eq_nil_iff.mp hr
    subst cs
    exact False.elim (by simpa using h.1)
  | cons A ps =>
    have he : cs = ps.reverse ++ [A] := by
      have he := congrArg List.reverse hr
      simpa using he
    have hc : ConvexOutline (A :: ps.reverse) :=
      (convexOutline_rotate_iff A ps.reverse).mp (he ▸ h)
    rw [he, fanSum_rotate hc, fanSum_cons, fanSum_cons, fanArea_reverse]

end Elements.Figures
