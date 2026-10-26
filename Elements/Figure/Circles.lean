import Elements.Figure.Lines
import Elements.Figure.CirclePoints
import Elements.Figure.Incidence
import Elements.Figure.RuleBase
import Elements.Figure.Areas

/-!
# Book Zero: circles

Euclid draws a circle with "centre A and distance AB" and then reads off his
figure which points are on it, inside it or outside it. These small facts
follow from Definition 15 and System E's rules for circles. So does one he
needs without drawing any circle at all: that a point taken "at random" on a
straight line can be taken near enough.
-/

namespace Elements

open Tacit

variable {A B C D : Point} {α : Circle}

/-- A circle has only one centre (System E, Generalities 2). This was an assumption
until 19 October 2026 and is now proved from the foundations: a straight line through
two supposed centres meets the circle at P and Q, and both centres bisect PQ by
Definition I.15. Equal doubles have equal halves, contradicting the strict order of
the lengths from P if the centres differ. -/
theorem Tacit.centre_unique {A B : Point} {α : Circle}
    (hA : Centre A α) (hB : Centre B α) : A = B := by
  by_cases hAB : A = B
  · exact hAB
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hAB
  obtain ⟨P, hP, hPL, hPAB⟩ :=
    line_circle_beyond (centre_inside hA) hAL hBL (Ne.symm hAB)
  obtain ⟨Q, hQ, hQL, hQAP⟩ :=
    line_circle_beyond (centre_inside hA) hAL hPL (ne_of_between hPAB)
  have hPAQ := between_symm hQAP
  have hPBQ := between_of_inside_chord hBL hPL hQL
    (centre_inside hB) hP hQ (ne_of_between_ends hPAQ)
  have eA := len_add_of_between hPAQ
  have eB := len_add_of_between hPBQ
  have rA : ‖P A‖ = ‖A Q‖ := (len_symm P A).trans (Definition15 hA hP hQ)
  have rB : ‖P B‖ = ‖B Q‖ := (len_symm P B).trans (Definition15 hB hP hQ)
  rw [← rA] at eA
  rw [← rB] at eB
  have heq : ‖P A‖ = ‖P B‖ := Magnitude.eq_of_add_self_eq (eA.trans eB.symm)
  exact False.elim (Magnitude.ne_of_lt (len_lt_of_between hPAB) heq)

/-- Where two different straight lines L and M meet at B, and A and C are points of M,
different from B and from each other, that are not on the same side of L, B lies between
A and C. Neither A nor C is on L, for L and M meet only at B; of the three orders of three
points of a straight line (Between 6), the other two would put A and C on the same side of
L, by Pasch 2. This uses no rule about circles. It finds the crossing in Triple
incidence 3, below, and in Intersection 2, proved after III.2. -/
theorem between_at_crossing {A B C : Point} {L M : Line}
    (hLM : L ≠ M) (hBL : OnLine B L) (hBM : OnLine B M) (hAM : OnLine A M)
    (hCM : OnLine C M) (hAC : A ≠ C) (hAB : A ≠ B) (hCB : C ≠ B)
    (hs : ¬ SameSide A C L) : Between A B C := by
  have hAL : ¬ OnLine A L := fun hAL =>
    hLM (line_unique hAB hAL hBL hAM hBM)
  have hCL : ¬ OnLine C L := fun hCL =>
    hLM (line_unique hCB hCL hBL hCM hBM)
  rcases between_cases hAB hCB.symm hAC hAM hBM hCM with h | h | h
  · exact h
  · exact False.elim (hs (pasch2 h hBL hAL))
  · exact False.elim (hs (same_side_symm (pasch2 (between_symm h) hBL hCL)))

/-- Angle addition and positivity exclude three incompatible same-side relations. -/
private theorem separates_of_angle_add {A B C D : Point} {L M N : Line}
    (hAL : OnLine A L) (hAM : OnLine A M) (hAN : OnLine A N)
    (hBL : OnLine B L) (hCM : OnLine C M) (hDN : OnLine D N)
    (hCD : SameSide C D L) (hBC : SameSide B C N) : ¬ SameSide B D M := by
  intro hBD
  have hCL := not_on_line_of_same_side hCD
  have hDL := not_on_line_of_same_side (same_side_symm hCD)
  have hBN := not_on_line_of_same_side hBC
  have hCN := not_on_line_of_same_side (same_side_symm hBC)
  have hDM := not_on_line_of_same_side (same_side_symm hBD)
  have hAB : A ≠ B := fun e => hBN (e ▸ hAN)
  have hAC : A ≠ C := fun e => hCL (e ▸ hAL)
  have hAD : A ≠ D := fun e => hDL (e ▸ hAL)
  have hLN : L ≠ N := fun e => hBN (e ▸ hBL)
  have hLM : L ≠ M := fun e => hCL (e ▸ hCM)
  have e₁ := angle_add_of_inside hAL hAN hBL hDN hAB hAD hCL hCN hLN hBC
    (same_side_symm hCD)
  have e₂ := angle_add_of_inside hAL hAM hBL hCM hAB hAC hDL hDM hLM hBD hCD
  have hp₁ : 0 < ∠ C A D := Magnitude.pos_of_ne_zero
    (fun hz => hDM (same_ray_of_angle_eq_zero hAC hAD hAM hCM hz).1)
  have hp₂ : 0 < ∠ D A C := Magnitude.pos_of_ne_zero
    (fun hz => hCN (same_ray_of_angle_eq_zero hAD hAC hAN hDN hz).1)
  have hlt₁ := CommonNotion5 (a := ∠ B A C) hp₁
  have hlt₂ := CommonNotion5 (a := ∠ B A D) hp₂
  rw [← e₁] at hlt₁
  rw [← e₂] at hlt₂
  exact lt_irrefl _ (lt_trans hlt₁ hlt₂)

/-- Take B on L, C on M and D on N, three straight lines through A, with C within
BAD and E within CAD. Then E is on C's side of L (System E, Triple incidence 3).
This was an assumption until 19 October 2026 and is now proved from angle addition
and positivity, Intersection 1, and the order and side rules. The straight line AE
crosses CD between C and D; Pasch carries that crossing's side of L to E. The given
point B and its side relation are retained in the statement, although the proof does
not need them. -/
theorem Tacit.triple_incidence3 {A B C D E : Point} {L M N : Line}
    (hAL : OnLine A L) (hAM : OnLine A M) (hAN : OnLine A N)
    (_hB : OnLine B L) (hC : OnLine C M) (hD : OnLine D N) (hCD : SameSide C D L)
    (_hBC : SameSide B C N) (hDE : SameSide D E M) (hCE : SameSide C E N) : SameSide C E L := by
  have hAC : A ≠ C := fun e => not_on_line_of_same_side hCD (e ▸ hAL)
  have hEM := not_on_line_of_same_side (same_side_symm hDE)
  have hEN := not_on_line_of_same_side (same_side_symm hCE)
  have hCN := not_on_line_of_same_side hCE
  have hAE : A ≠ E := fun e => hEM (e ▸ hAM)
  have hAD : A ≠ D := fun e => not_on_line_of_same_side hDE (e ▸ hAM)
  obtain ⟨R, hAR, hER⟩ := Postulate1 A E hAE
  have hCR : ¬ OnLine C R := fun hCR =>
    hEM (line_unique hAC hAR hCR hAM hC ▸ hER)
  have hDR : ¬ OnLine D R := fun hDR =>
    hEN (line_unique hAD hAR hDR hAN hD ▸ hER)
  have hCDR : ¬ SameSide C D R := fun hs =>
    separates_of_angle_add hAM hAN hAR hC hD hER hDE hs hCE
  have hCD' : C ≠ D := fun e => hCN (e ▸ hD)
  obtain ⟨Q, hCQ, hDQ⟩ := Postulate1 C D hCD'
  obtain ⟨hRQ, X, hXR, hXQ⟩ :=
    lines_meet_of_opposite_sides ⟨hCR, hDR, hCDR⟩ hCQ hDQ
  have hCXD : Between C X D := between_at_crossing hRQ hXR hXQ hCQ hDQ hCD'
    (fun e => hCR (e ▸ hXR)) (fun e => hDR (e ▸ hXR)) hCDR
  have hCX : SameSide C X L := pasch1 hCXD hCD
  have hXL := not_on_line_of_same_side (same_side_symm hCX)
  have hXA : X ≠ A := fun e => hXL (e ▸ hAL)
  have hXM : ¬ OnLine X M := fun hXM =>
    hEM (line_unique hXA hXR hAR hXM hAM ▸ hER)
  have hXE_M : SameSide X E M :=
    same_side_trans (same_side_symm (pasch2 hCXD hC hXM)) hDE
  have hXE_L : SameSide X E L := by
    by_cases he : X = E
    · exact he ▸ same_side_refl hXL
    apply Classical.byContradiction
    intro hn
    have hLR : L ≠ R := fun e => hXL (e ▸ hXR)
    exact pasch3 (between_at_crossing hLR hAL hAR hXR hER he hXA hAE.symm hn) hAM hXE_M
  exact same_side_trans (same_side_symm hCX) hXE_L

/-- A point on a circle is not its centre. -/
theorem ne_of_centre_of_on (hA : Centre A α) (hC : OnCircle C α) : C ≠ A := by
  intro h
  subst h
  exact inside_not_on (centre_inside hA) hC

/-- A point farther from the centre than the circumference is outside the
circle. -/
theorem outside_of_len_gt (hA : Centre A α) (hD : OnCircle D α) (h : ‖A D‖ < ‖A B‖) :
    OutsideCircle B α := by
  constructor
  · intro hin
    exact lt_irrefl _ (lt_trans (len_lt_of_inside hA hD hin) h)
  · intro hon
    rw [Definition15 hA hD hon] at h
    exact lt_irrefl _ h

/-- A point between the centre and a point on the circle is within it. It is nearer the
centre than that point is, as the part is less than the whole, and so nearer than the
circumference by Definition I.15 and the transfer rules. This proof uses no proposition
and neither Circle 2 nor Circle 3. -/
theorem InsideCircle.of_between_centre {O P : Point} (hO : Centre O α)
    (hP : OnCircle P α) (h : Between O C P) : InsideCircle C α := by
  exact inside_of_len_lt hO hP (len_lt_of_between h)

/-- A point between the centre and a point within the circle is within it, when a point
of the circle is given. The nearer point is nearer than the point within, which is nearer
than the circumference by Definition I.15 and the transfer rules. This proof uses no
proposition and neither Circle 2 nor Circle 3. -/
theorem InsideCircle.of_between_centre_of_inside {O P R : Point} (hO : Centre O α)
    (hR : OnCircle R α) (hP : InsideCircle P α) (h : Between O C P) : InsideCircle C α := by
  exact inside_of_len_lt hO hR
    (lt_trans (len_lt_of_between h) (len_lt_of_inside hO hR hP))

/-- A chance point, but not too far out. If P is nearer to O than C is, and Q
lies beyond P as seen from O (or O is P itself), there is a point F between
P and Q that is nearer to O than C is, too. Euclid takes a point "at random" on
a straight line and in the next breath needs it near enough (I.5, I.9). A circle about
O through C keeps it in: P is inside that circle; if Q is not outside it, any
point between P and Q will do; if Q is outside, take a point between P and the
place X where PQ leaves the circle (Intersections 4). Either way F lies between
O and a point no farther from O than C is, Q or X, so OF is the less, as
the part is less than the whole. This proof uses the order of the points and neither
Circle 2 nor Circle 3; I.5 and I.9 therefore inherit neither through this lemma. -/
theorem exists_between_nearer {O P Q C : Point} (hPQ : P ≠ Q)
    (hO : O = P ∨ Between O P Q) (h : ‖O P‖ < ‖O C‖) :
    ∃ F : Point, Between P F Q ∧ ‖O F‖ < ‖O C‖ := by
  obtain ⟨α, hO_α, hC_α⟩ := Postulate3 O C (ne_of_len_gt h)
  have hP_α : InsideCircle P α := inside_of_len_lt hO_α hC_α h
  obtain ⟨L, hP_L, hQ_L⟩ := Postulate1 P Q hPQ
  by_cases hQ_α : InsideCircle Q α ∨ OnCircle Q α
  · /- Q is not outside the circle: F, taken between P and Q, lies between O
       and Q, so OF is less than OQ, which is not greater than OC. -/
    obtain ⟨F, -, hPFQ, -⟩ := exists_point_between hP_L hQ_L hPQ []
    have hOFQ : Between O F Q := by
      rcases hO with rfl | hOPQ
      · exact hPFQ
      · exact between_symm
          (between_of_between_left (between_symm hOPQ) (between_symm hPFQ))
    refine ⟨F, hPFQ, ?_⟩
    rcases hQ_α with hQ_in | hQ_on
    · exact lt_trans (len_lt_of_between hOFQ) (len_lt_of_inside hO_α hC_α hQ_in)
    · rw [Definition15 hO_α hC_α hQ_on]
      exact len_lt_of_between hOFQ
  · /- Q is outside: PQ leaves the circle at X, and F is taken between P and
       X. F lies between O and X, so OF is less than the radius OX. -/
    have hQ_out : OutsideCircle Q α := ⟨fun h => hQ_α (Or.inl h), fun h => hQ_α (Or.inr h)⟩
    obtain ⟨X, hX_α, hX_L, hPXQ⟩ := line_circle_between hP_α hP_L hQ_out hQ_L
    obtain ⟨F, -, hPFX, -⟩ := exists_point_between hP_L hX_L (ne_of_between hPXQ) []
    have hOFX : Between O F X := by
      rcases hO with rfl | hOPQ
      · exact hPFX
      · have hOPX : Between O P X := between_cut hOPQ hPXQ
        exact between_symm
          (between_of_between_left (between_symm hOPX) (between_symm hPFX))
    refine ⟨F, between_of_between_left hPXQ hPFX, ?_⟩
    rw [Definition15 hO_α hC_α hX_α]
    exact len_lt_of_between hOFX

end Elements
