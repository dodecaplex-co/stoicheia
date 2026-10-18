import Elements.Figure.Basics
import Elements.BookI.Prop32
import Elements.BookIII.Circumferences
import Elements.BookIII.Prop22

/-!
# Stage 3, staged: adding circumferences

Statements before proofs (brief 0006, stage 3). Destined for
`Elements/BookIII/Circumferences.lean`, for Book IV.
-/

namespace Elements.BookIII

open Tacit

/-- **Circumferences add.** Let B, C, D be points of a circle with a centre, and C on K's side
of BD. Then the circumference BC away from D, and the circumference CD away from B, make up
the circumference BD on K's side, the one through C.

To be proved: measured at D and at B, the two are twice the angles BDC and CBD; measured at a
point A on the other side of BD from C, the whole is twice the angle BAD [III. 21]; the three
angles of BCD make two right angles [I. 32], and the angles at A and C make two right angles
[III. 22].

Ground for Book IV; no proposition of Book III cites it. -/
theorem Circumference.add {B C D K X Y : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hB : OnCircle B α) (hC : OnCircle C α) (hD : OnCircle D α) (hCK : SameSideOf C K B D)
    (hX : OppositeSidesOf X D B C) (hY : OppositeSidesOf Y B C D) :
    circumference α B X C + circumference α C Y D = circumference α B K D := by
  sorry

end Elements.BookIII
