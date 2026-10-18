import Elements.Figure.Basics
import Staging.Stage3.Degenerate

/-!
# Stage 3, staged: placement, two points of the base

Statements before proofs (brief 0006, stage 3). One file of `Elements/BookIII/Placement/`.
-/

namespace Elements.BookIII

open Tacit

/-- **Two points of the base keep their distance.** On equal straight lines AB, CD, let P,
Q be points of the straight line AB, and P', Q' points of the straight line CD, each as far
from C as its fellow is from A, and from D as its fellow is from B. Then P'Q' is equal to PQ.

To be proved from the order of points on a straight line: P and Q are on one ray from A or
on opposite rays, and P', Q' alike (their distances from B and D decide it, by
`Prop20.between_congr`); then PQ is the difference or the sum of AP and AQ
(`len_add_of_between`), and P'Q' the same of CP' and CQ'. -/
theorem Placement.dist_on_on {A B C D P Q P' Q' : Point} (hlen : ‖A B‖ = ‖C D‖)
    (hAB : A ≠ B) (hP : Collinear A B P) (hQ : Collinear A B Q) (hP' : Collinear C D P')
    (hQ' : Collinear C D Q') (hP₁ : ‖C P'‖ = ‖A P‖) (hP₂ : ‖D P'‖ = ‖B P‖)
    (hQ₁ : ‖C Q'‖ = ‖A Q‖) (hQ₂ : ‖D Q'‖ = ‖B Q‖) : ‖P' Q'‖ = ‖P Q‖ := by
  sorry

end Elements.BookIII
