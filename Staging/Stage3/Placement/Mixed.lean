import Elements.Figure.Basics
import Elements.BookI.Prop04
import Elements.BookI.Prop08
import Staging.Stage3.Degenerate

/-!
# Stage 3, staged: placement, a point of the base and a point off it

Statements before proofs (brief 0006, stage 3). One file of `Elements/BookIII/Placement/`.
-/

namespace Elements.BookIII

open Tacit

/-- **A point of the base and a point off it keep their distance.** On equal straight lines
AB, CD, let P be a point of the straight line AB and Q a point off it; let P' be a point of
the straight line CD and Q' a point off it, each as far from C as its fellow is from A, and
from D as its fellow is from B. Then P'Q' is equal to PQ. (Which side of CD Q' is on does not
matter.)

To be proved with the base point chosen so that P lies on the ray from it through the other
end: from A when P is on the ray AB, from B when A lies between P and B. Say from A: the
triangles ABQ, CDQ' have their sides equal, so the angles BAQ, DCQ' are equal [I. 8]; P' is
on the ray CD as P is on the ray AB (`Prop20.between_congr`); so the angles PAQ, P'CQ' are
those same angles, and the triangles APQ, CP'Q' give PQ equal to P'Q' [I. 4]. P at A or B is
immediate. No supplementary angles arise. -/
theorem Placement.dist_on_off {A B C D P Q P' Q' : Point} (hlen : ‖A B‖ = ‖C D‖)
    (hP : Collinear A B P) (hQ : ¬ Collinear A B Q) (hP' : Collinear C D P')
    (hQ' : ¬ Collinear C D Q') (hP₁ : ‖C P'‖ = ‖A P‖) (hP₂ : ‖D P'‖ = ‖B P‖)
    (hQ₁ : ‖C Q'‖ = ‖A Q‖) (hQ₂ : ‖D Q'‖ = ‖B Q‖) : ‖P' Q'‖ = ‖P Q‖ := by
  sorry

end Elements.BookIII
