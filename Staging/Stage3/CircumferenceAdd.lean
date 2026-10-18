import Elements.Figure.Basics
import Elements.BookI.Prop32
import Elements.BookIII.Circumferences
import Elements.BookIII.Prop22

/-!
# Stage 3, staged: adding circumferences

Statements frozen before their proofs (brief 0006, stage 3), and proved here. Destined for
`Elements/BookIII/Circumferences.lean`, for Book IV.
-/

namespace Elements.BookIII

open Tacit

/-- **Circumferences add.** Let B, C, D be points of a circle with a centre, and C on K's side
of BD. Then the circumference BC away from D, and the circumference CD away from B, make up
the circumference BD on K's side, the one through C.

Proved: measured at D and at B, the two are twice the angles BDC and CBD; measured at a
point A on the other side of BD from C, the whole is twice the angle BAD [III. 21]; the three
angles of BCD make two right angles [I. 32], and the angles at A and C make two right angles
[III. 22].

Ground for Book IV; no proposition of Book III cites it. -/
theorem Circumference.add {B C D K X Y : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hB : OnCircle B α) (hC : OnCircle C α) (hD : OnCircle D α) (hCK : SameSideOf C K B D)
    (hX : OppositeSidesOf X D B C) (hY : OppositeSidesOf Y B C D) :
    circumference α B X C + circumference α C Y D = circumference α B K D := by
  /- Take A on the circle across BD from C, and therefore across BD from K. -/
  obtain ⟨A, hA, hAC⟩ := exists_onCircle_oppositeSidesOf hB hD hCK.triangle
  have hAK : OppositeSidesOf A K B D := (hCK.symm.trans_opposite hAC.symm).symm
  /- Measure BXC at D, CYD at B, and BKD at A. [III. 21] -/
  rw [Circumference.eq hα hD hB hC hX.symm,
    Circumference.eq hα hB hC hD hY.symm, Circumference.eq hα hA hB hD hAK]
  /- The three angles of the triangle CBD make two right angles. [I. 32] -/
  have hCBD : Triangle C B D := hCK.triangle.cab
  obtain ⟨E, hBDE⟩ := produce hCBD.ne₂₃
  have h32 : ∠ C B D + ∠ B D C + ∠ D C B = ∟ + ∟ := (BookI.Prop32 hCBD hBDE).2
  /- The angles at A and C of the quadrilateral ABCD also make two right angles. [III. 22] -/
  have h22 : ∠ B A D + ∠ D C B = ∟ + ∟ := (Prop22 hα hA hB hC hD hAC).2
  /- Take away the common angle DCB: the angles CBD and BDC together equal BAD. -/
  have hsum : ∠ C B D + ∠ B D C = ∠ B A D :=
    CommonNotion3 (h32.trans h22.symm) rfl
  /- Doubling this equality gives the sum of the two circumferences. -/
  calc
    ∠ B D C + ∠ B D C + (∠ C B D + ∠ C B D) =
        (∠ C B D + ∠ B D C) + (∠ C B D + ∠ B D C) := by ac_rfl
    _ = ∠ B A D + ∠ B A D := by rw [hsum]

end Elements.BookIII
