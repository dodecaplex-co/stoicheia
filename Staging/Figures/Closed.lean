import Staging.Figures.Convex

/-!
# Staging: a triangle with its sides, and a triangle cut in two

Statements for brief 0013 (a draft for the owner's approval), with `sorry` where a proof is
due: a closed triangle is the three closed sides of its sides' straight lines, towards the
opposite corners; and a straight line from a corner to a point of the opposite side cuts the
triangle into two that cover it and whose areas make up its area. The probe of 19 October
proved the first, for its own words, in `BoundaryBridge.lean`.
-/

namespace Elements.Figures

open Tacit

/-- **A closed triangle is three closed sides**: a point is within or on the triangle ABC
exactly when it is on the closed side of each side's straight line towards the opposite
corner. -/
theorem closed_triangle_sides {A B C X : Point} (h : Triangle A B C) :
    OnOrInsideTriangle X A B C ↔
      ClosedSide X A B C ∧ ClosedSide X B C A ∧ ClosedSide X C A B := by
  sorry

/-- A triangle cut from a corner to a point of the opposite side, the point an end or between
the ends: the two parts make up its area. -/
theorem area_cut_closed {A B C D : Point} (h : OnFiniteLine D B C) :
    △ A B D + △ A D C = △ A B C := by
  sorry

/-- A triangle cut from a corner to a point of the opposite side: a point is within or on the
triangle exactly when it is within or on one of the two parts. -/
theorem triangle_cut_cover {A B C D X : Point} (hABC : Triangle A B C)
    (hD : OnFiniteLine D B C) :
    OnOrInsideTriangle X A B C ↔
      OnOrInsideTriangle X A B D ∨ OnOrInsideTriangle X A D C := by
  sorry

end Elements.Figures
