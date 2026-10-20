import Staging.Figures.Convex

/-!
# Staging: points off finitely many straight lines

Statements for brief 0013 (a draft for the owner's approval), with `sorry` where a proof is
due. Arguments about figures often take a point "in general position": off every straight
line of a finite list. Here such a point is found inside any triangle, and about any point a
small triangle is found that stays on the same side of finitely many straight lines as the
point. No coordinates, limits or measures are used: each is a finite construction.
-/

namespace Elements.Figures

open Tacit

/-- `X` is on none of the straight lines `ls`. -/
def Avoid (ls : List Line) (X : Point) : Prop := ∀ L ∈ ls, ¬ OnLine X L

/-- **A point inside a triangle, off finitely many straight lines.** -/
theorem triangle_point_avoiding {A B C : Point} (h : Triangle A B C) (ls : List Line) :
    ∃ X : Point, InsideTriangle X A B C ∧ Avoid ls X := by
  sorry

/-- **A small triangle about a point**: given a point `X` on the same side as `P` of each of
finitely many straight lines `L` (the pairs `(P, L)`), there is a triangle with `X` inside
it, all of whose points, within or on it, are on those same sides. -/
theorem small_triangle {X : Point} (hs : List (Point × Line))
    (hX : ∀ s ∈ hs, SameSide X s.1 s.2) :
    ∃ A B C : Point, InsideTriangle X A B C ∧
      ∀ Y : Point, OnOrInsideTriangle Y A B C → ∀ s ∈ hs, SameSide Y s.1 s.2 := by
  sorry

end Elements.Figures
