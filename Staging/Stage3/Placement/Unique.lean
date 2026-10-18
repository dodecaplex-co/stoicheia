import Elements.Figure.Basics
import Elements.BookI.Prop07

/-!
# Stage 3, staged: placement, only one place

Statements before proofs (brief 0006, stage 3). One file of `Elements/BookIII/Placement/`.

A point is fixed by its distances from C and D together with whether it is on F's side of
CD or on CD: on one side, by I.7; on the straight line, by the order of points on it. (A
point on the side and a point on the line cannot share both distances: that is
`Prop20.collinear_congr`, used in the assembly.)
-/

namespace Elements.BookIII

open Tacit

/-- **Only one place off the base.** Two points on F's side of CD, equally far from C and
equally far from D, are one point. This is I.7 itself. -/
theorem Placement.unique_off {C D F Q₁ Q₂ : Point} (hQ₁ : SameSideOf Q₁ F C D)
    (hQ₂ : SameSideOf Q₂ F C D) (hC : ‖C Q₁‖ = ‖C Q₂‖) (hD : ‖D Q₁‖ = ‖D Q₂‖) : Q₁ = Q₂ :=
  BookI.Prop7 (hQ₁.trans hQ₂.symm) (by rw [len_symm Q₁ C, hC, len_symm C Q₂])
    (by rw [len_symm Q₁ D, hD, len_symm D Q₂])

/-- **Only one place on the base.** Two points of the straight line CD, equally far from C
and equally far from D, are one point.

To be proved from the order of points on a straight line: on one ray from C only one point
lies at a given distance (`OnRay.eq_of_len_eq`), and two points on opposite rays from C at
the same distance are told apart by their distances from D (`len_add_of_between`). -/
theorem Placement.unique_on {C D Q₁ Q₂ : Point} (hCD : C ≠ D) (hQ₁ : Collinear C D Q₁)
    (hQ₂ : Collinear C D Q₂) (hC : ‖C Q₁‖ = ‖C Q₂‖) (hD : ‖D Q₁‖ = ‖D Q₂‖) : Q₁ = Q₂ := by
  sorry

end Elements.BookIII
