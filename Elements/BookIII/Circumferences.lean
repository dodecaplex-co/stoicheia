import Elements.Figure.Basics
import Elements.BookI.Helpers
import Elements.BookI.Prop32
import Elements.BookIII.Prop02
import Elements.BookIII.Prop20
import Elements.BookIII.Prop21
import Elements.BookIII.Prop22

/-!
# Book III: circumferences, from III.20–III.22

From III.26 on, Euclid compares circumferences: "the circumference BKC is equal to the
circumference ELF" (III.26), "BK is also equal to BC, the less to the greater" (III.27),
"the circumference ACB which remains is also equal to the circumference DFE which
remains" (III.28). Lean measures the circumference BKC by the angle that stands on it
at the circumference, taken twice (`circumference`, Definitions III.6 and III.9). What
Euclid takes for granted about circumferences then follows from the three propositions
before them, III.2's corollaries supplying the points of the circle on either side of BC:

* any point of the circle on the other side measures it, the angles in a segment being
  equal (III.21): `Circumference.eq`, `Circumference.standing`;
* a circumference less than a semicircle is measured by its angle at the centre (III.20):
  `Circumference.centre`;
* the two circumferences that a straight line cuts off make up the whole circle, four
  right angles (III.22): `Circumference.whole`;
* a semicircle is two right angles, a circumference beyond which the centre lies is less,
  and one on the centre's side is greater: `Circumference.semicircle`,
  `Circumference.lt_semicircle`, `Circumference.gt_semicircle`;
* a circumference cut at a point of it is the two circumferences it is cut into, for Book
  IV, which adds them (I.32, III.21, III.22): `Circumference.add`.

Each docstring ends with the propositions the step cites; the certificate walks through
it and records them.
-/

namespace Elements.BookIII

open Tacit

variable {A B C G K : Point} {α : Circle}

/-- The point A itself is on its own side of BC, when it is off BC. -/
private theorem sameSideOf_self (h : Triangle B C A) : SameSideOf A A B C := by
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C h.ne₁₂
  exact SameSideOf.of_line h.ne₁₂ hB_L hC_L (same_side_refl (h.off_line hB_L hC_L))

/-- **A circumference is measured at any point of the other segment.** The circumference
BKC is twice the angle BAC, for every point A of the circle on the other side of
BC: Lean's choice measured it at some such point, and the angles in that segment are
all equal. [III. 21] -/
theorem Circumference.eq (hA : OnCircle A α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hAK : OppositeSidesOf A K B C) :
    circumference α B K C = ∠ B A C + ∠ B A C := by
  obtain ⟨X, hX, hXK, hx⟩ := Classical.epsilon_spec
    (p := fun x => ∃ X : Point, OnCircle X α ∧ OppositeSidesOf X K B C ∧
      x = ∠ B X C + ∠ B X C) ⟨_, A, hA, hAK, rfl⟩
  unfold circumference
  rw [hx, Prop21 hX hB hC hA (OppositeSidesOf.sameSideOf hXK.symm hAK.symm)]

/-- **The circumference on which an angle stands.** For a point A of the circle off
BC, the circumference on which the angle BAC stands is twice that angle, as any other
point of the segment would make it. [III. 21] -/
theorem Circumference.standing (hA : OnCircle A α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hBCA : Triangle B C A) :
    standing α B A C = ∠ B A C + ∠ B A C := by
  obtain ⟨X, hX, hXA, hx⟩ := Classical.epsilon_spec
    (p := fun x => ∃ X : Point, OnCircle X α ∧ SameSideOf X A B C ∧
      x = ∠ B X C + ∠ B X C) ⟨_, A, hA, sameSideOf_self hBCA, rfl⟩
  unfold Elements.standing
  rw [hx, Prop21 hX hB hC hA hXA]

/-- **The angle at the centre.** A circumference BKC beyond which the centre G lies,
on the other side of BC, is measured by the angle BGC: for a point A of the circle
on the centre's side, the angle BGC is double of the angle BAC. [III. 2, III. 20, III. 21] -/
theorem Circumference.centre (hG : Centre G α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hGK : OppositeSidesOf G K B C) : circumference α B K C = ∠ B G C := by
  obtain ⟨A, hA, hAG⟩ := Prop2.sameSide hB hC hGK.triangle
  rw [Circumference.eq hA hB hC (hAG.trans_opposite hGK),
    Prop20.special hG hA hB hC hAG.symm]

/-- **The whole circle.** A straight line BC cuts the circle into two circumferences,
one on each side, and together they are four right angles. Measured at a point of each,
they are twice the opposite angles of a quadrilateral in the circle, which are together
two right angles. [III. 2, III. 21, III. 22] -/
theorem Circumference.whole (hB : OnCircle B α) (hC : OnCircle C α)
    (hAK : OppositeSidesOf A K B C) :
    circumference α B K C + circumference α B A C = ∟ + ∟ + (∟ + ∟) := by
  /- We take a point A' of the circle on A's side, and a point K' on K's side. -/
  obtain ⟨A', hA', hA'A⟩ := Prop2.sameSide hB hC hAK.triangle
  obtain ⟨K', hK', hK'K⟩ := Prop2.sameSide hB hC hAK.symm.triangle
  have hA'K : OppositeSidesOf A' K B C := hA'A.trans_opposite hAK
  have hK'A : OppositeSidesOf K' A B C := hK'K.trans_opposite hAK.symm
  have hA'K' : OppositeSidesOf A' K' B C := (hK'K.trans_opposite hA'K.symm).symm
  rw [Circumference.eq hA' hB hC hA'K, Circumference.eq hK' hB hC hK'A]
  /- III.22 gives the opposite angles at A' and K' of the quadrilateral A'CK'B. -/
  have h22 := (Prop22 hA' hC hK' hB hA'K'.swap).2
  rw [angle_symm hA'K.triangle.ne₂₃ hA'K.triangle.ne₁₃] at h22
  rw [← h22]
  ac_rfl

/-- **A semicircle is two right angles.** When the centre G is on BC, the angle BAC
at any point A of the circle is half of two right angles: the radii GA, GB, GC
make the angles at B and C equal to the two parts of the angle at A [I. 5], and the
three angles of the triangle ABC are two right angles [I. 32]. Since that holds at
every point, it holds at the one that measures the circumference, and the angles in a
segment being equal (III.21) is not needed. Euclid proves the same of the angle in a
semicircle in III.31; III.28 and III.29 need it of circumferences first.
[I. 5, I. 32, III. 2] -/
theorem Circumference.semicircle (hG : Centre G α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hBGC : Between B G C) (hK : Triangle B C K) : circumference α B K C = ∟ + ∟ := by
  /- Lean measured the circumference at some point A of the circle on the other side of BC
     from K, and there is such a point. -/
  obtain ⟨A₀, hA₀, hA₀K⟩ := Prop2.oppositeSide hB hC hK
  obtain ⟨A, hA, hAK, hx⟩ := Classical.epsilon_spec
    (p := fun x => ∃ A : Point, OnCircle A α ∧ OppositeSidesOf A K B C ∧
      x = ∠ B A C + ∠ B A C) ⟨_, A₀, hA₀, hA₀K, rfl⟩
  unfold circumference
  rw [hx]
  have hBCA : Triangle B C A := hAK.triangle
  have hGA : ‖G A‖ = ‖G B‖ := Definition15 hG hA hB
  have hGC : ‖G C‖ = ‖G B‖ := Definition15 hG hC hB
  /- G is off the straight lines AB and AC, for it lies on BC between B and C. -/
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hBCA.ne₁₂
  have hG_L : OnLine G L := on_line_of_between_ends hBGC hB_L hC_L
  have hA_L : ¬ OnLine A L := hBCA.off_line hB_L hC_L
  have hGBA : Triangle G B A := Triangle.of_line hG_L hB_L (ne_of_between hBGC).symm hA_L
  have hGCA : Triangle G C A :=
    Triangle.of_line hG_L hC_L (ne_of_between (between_symm hBGC)).symm hA_L
  /- The angle BAC is made up of the angles BAG, GAC. -/
  have hsplit : ∠ B A C = ∠ B A G + ∠ G A C := angle_add_of_between hBCA hBGC
  /- The angles at the base of the isosceles triangles GAB, GAC are equal. [I. 5] -/
  have h₁ : ∠ G B A = ∠ G A B := BookI.Prop5.base hGBA (hGA.symm)
  have h₂ : ∠ G C A = ∠ G A C := BookI.Prop5.base hGCA (hGC.trans hGA.symm)
  have e₁ : ∠ B A G = ∠ A B C := by
    rw [angle_symm hGBA.ne₂₃ hGBA.ne₁₃, ← h₁,
      angle_onRay_left (OnRay.of_between hBGC) hGBA.ne₂₃.symm,
      angle_symm hBCA.ne₁₂.symm hGBA.ne₂₃.symm]
  have e₂ : ∠ G A C = ∠ B C A := by
    rw [← h₂, angle_onRay_left (OnRay.of_between (between_symm hBGC)) hGCA.ne₂₃.symm]
  have hA : ∠ B A C = ∠ A B C + ∠ B C A := by rw [hsplit, e₁, e₂]
  /- The angles of the triangle ABC are two right angles [I. 32]. -/
  obtain ⟨D, hBCD⟩ := produce hBCA.ne₁₂
  obtain ⟨-, h32⟩ := BookI.Prop32 hBCA.cab hBCD
  rw [← h32, angle_symm hBCA.ne₂₃ hBCA.ne₁₃, ← hA]

/-- **A circumference beyond which the centre lies is less than a semicircle.** Its
angle at the centre, an angle of the triangle BGC, is less than two right angles, the
three angles being two right angles [I. 32]. [I. 32, III. 2, III. 20, III. 21] -/
theorem Circumference.lt_semicircle (hG : Centre G α) (hB : OnCircle B α)
    (hC : OnCircle C α) (hGK : OppositeSidesOf G K B C) : circumference α B K C < ∟ + ∟ := by
  rw [Circumference.centre hG hB hC hGK]
  have hGBC : Triangle G B C := hGK.triangle.cab
  obtain ⟨D, hBCD⟩ := produce hGBC.ne₂₃
  obtain ⟨-, h32⟩ := BookI.Prop32 hGBC hBCD
  have hpos : 0 < ∠ G B C + ∠ B C G :=
    lt_trans hGBC.angle_pos (CommonNotion5 hGBC.bca.angle_pos)
  have := CommonNotion5 (a := ∠ C G B) hpos
  rw [add_comm, h32, angle_symm hGBC.ne₁₃.symm hGBC.ne₁₂.symm] at this
  exact this

/-- **A circumference on the centre's side is greater than a semicircle**: with the
circumference on the other side, less than a semicircle, it makes up four right angles.
[I. 32, III. 2, III. 20, III. 21, III. 22] -/
theorem Circumference.gt_semicircle (hG : Centre G α) (hB : OnCircle B α)
    (hC : OnCircle C α) (hGK : SameSideOf G K B C) : ∟ + ∟ < circumference α B K C := by
  obtain ⟨Q, hQ, -⟩ := exists_oppositeSidesOf hGK.symm.triangle []
  have hw := Circumference.whole hB hC hQ
  have hlt := Circumference.lt_semicircle hG hB hC (hGK.trans_opposite hQ.symm)
  have h1 := add_lt_add_right (circumference α B K C) hlt
  rw [add_comm (circumference α B Q C), hw, add_comm (∟ + ∟) (circumference α B K C)] at h1
  exact Magnitude.lt_of_add_lt_add_right h1

/-- **Circumferences add.** Let B, C, D be points of a circle, and C on K's side
of BD. Then the circumference BC away from D, and the circumference CD away from B, make up
the circumference BD on K's side, the one through C.

Proved: measured at D and at B, the two are twice the angles BDC and CBD; measured at a
point A on the other side of BD from C, the whole is twice the angle BAD [III. 21]; the three
angles of BCD make two right angles [I. 32], and the angles at A and C make two right angles
[III. 22].

Ground for Book IV, where IV.11 and IV.16 add circumferences; no proposition of Book III
cites it. [I. 32, III. 2, III. 21, III. 22] -/
theorem Circumference.add {B C D K X Y : Point} {α : Circle} (hB : OnCircle B α)
    (hC : OnCircle C α) (hD : OnCircle D α) (hCK : SameSideOf C K B D)
    (hX : OppositeSidesOf X D B C) (hY : OppositeSidesOf Y B C D) :
    circumference α B X C + circumference α C Y D = circumference α B K D := by
  /- Take A on the circle across BD from C, and therefore across BD from K: BD is a straight
     line in the circle, which has points on either side of it (`Prop2.oppositeSide`). -/
  obtain ⟨A, hA, hAC⟩ := Prop2.oppositeSide hB hD hCK.triangle
  have hAK : OppositeSidesOf A K B D := (hCK.symm.trans_opposite hAC.symm).symm
  /- Measure BXC at D, CYD at B, and BKD at A. [III. 21] -/
  rw [Circumference.eq hD hB hC hX.symm,
    Circumference.eq hB hC hD hY.symm, Circumference.eq hA hB hD hAK]
  /- The three angles of the triangle CBD make two right angles. [I. 32] -/
  have hCBD : Triangle C B D := hCK.triangle.cab
  obtain ⟨E, hBDE⟩ := produce hCBD.ne₂₃
  have h32 : ∠ C B D + ∠ B D C + ∠ D C B = ∟ + ∟ := (BookI.Prop32 hCBD hBDE).2
  /- The angles at A and C of the quadrilateral ABCD also make two right angles. [III. 22] -/
  have h22 : ∠ B A D + ∠ D C B = ∟ + ∟ := (Prop22 hA hB hC hD hAC).2
  /- Take away the common angle DCB: the angles CBD and BDC together equal BAD. -/
  have hsum : ∠ C B D + ∠ B D C = ∠ B A D :=
    CommonNotion3 (h32.trans h22.symm) rfl
  /- Doubling this equality gives the sum of the two circumferences. -/
  calc
    ∠ B D C + ∠ B D C + (∠ C B D + ∠ C B D) =
        (∠ C B D + ∠ B D C) + (∠ C B D + ∠ B D C) := by ac_rfl
    _ = ∠ B A D + ∠ B A D := by rw [hsum]

end Elements.BookIII
