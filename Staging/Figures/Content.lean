import Staging.Figures.Cells

/-!
# Staging: the content of a figure does not depend on its division

The central statement of brief 0013 (a draft for the owner's approval), with `sorry` where
its proof is due: two divisions of a figure into triangles that lie apart, whose triangles
cover the same points, have the same sum. The figure may have holes, touch itself at a
corner, or be in pieces; the triangles may meet a side of another at a corner of their own.
Euclid takes it for granted under I.45; David Hilbert proved it, for the measure of area he
builds from his axioms (*The Foundations of Geometry*, chapter IV, section 20).
-/

namespace Elements.Figures

open Tacit

/-- The triangles `R` divide the region `U`: a point is within or on one of them exactly when
it is in `U`. -/
def Divides (U : Point → Prop) (R : Apart) : Prop :=
  ∀ X : Point, Covers R.pieces X ↔ U X

/-- **The content theorem**: two divisions into triangles that lie apart, covering the same
points, have the same sum. -/
theorem Apart.area_eq_of_same_region (R S : Apart)
    (h : ∀ X : Point, Covers R.pieces X ↔ Covers S.pieces X) : R.area = S.area := by
  sorry

/-- A triangle divided into triangles that lie apart has their sum for its area. -/
theorem triangle_division_area {A B C : Point} (hABC : Triangle A B C) (R : Apart)
    (hR : Divides (fun X => OnOrInsideTriangle X A B C) R) : R.area = △ A B C := by
  sorry

end Elements.Figures
