import Elements.Figure.Basics
import Elements.BookI.Prop03
import Elements.BookI.Prop20
import Elements.BookI.Prop22

/-!
# Stage 3, staged: placement, where a point goes

Statements before proofs (brief 0006, stage 3). One file of `Elements/BookIII/Placement/`,
so that parallel provers never share one. The assembly is in `Staging/Stage3/Placement.lean`.

On equal straight lines AB, CD, a point P is sent to a point Q as far from C as P is from
A, and as far from D as P is from B. These say that such a point exists, on F's side of
CD when P is off AB, and on CD when P is on AB.
-/

namespace Elements.BookIII

open Tacit

/-- **A point off the base has a place.** On equal straight lines AB, CD, for a point P off
AB there is a point Q on F's side of CD as far from C as P is from A, and as far from D as P
is from B.

To be proved by I.22, the triangle with sides AP, CD, BP on CD towards F, its three
straight lines meeting I.20's condition because ABP is a triangle; the point I.22 finds on
the ray CD at the distance CD is D itself (`OnRay.eq_of_len_eq`). -/
theorem Placement.exists_off {A B C D F P : Point} (hlen : ‖A B‖ = ‖C D‖)
    (hF : ¬ Collinear C D F) (hP : ¬ Collinear A B P) :
    ∃ Q : Point, SameSideOf Q F C D ∧ ‖C Q‖ = ‖A P‖ ∧ ‖D Q‖ = ‖B P‖ := by
  sorry

/-- **A point of the base has a place.** On equal straight lines AB, CD, for a point P on
the straight line AB there is a point Q on the straight line CD as far from C as P is from
A, and as far from D as P is from B.

To be proved case by case: P at A or B goes to C or D; P between A and B goes to the point
cut off from CD by I.3; P beyond B (or beyond A) goes to the point on CD produced beyond D
(or C) at the distance BP (AP), by `produce` and `OnRay.exists_len_eq`. -/
theorem Placement.exists_on {A B C D P : Point} (hlen : ‖A B‖ = ‖C D‖) (hAB : A ≠ B)
    (hP : Collinear A B P) :
    ∃ Q : Point, Collinear C D Q ∧ ‖C Q‖ = ‖A P‖ ∧ ‖D Q‖ = ‖B P‖ := by
  sorry

end Elements.BookIII
