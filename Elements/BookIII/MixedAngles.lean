import Elements.Figure.Basics
import Elements.BookI.Prop12
import Elements.BookI.Prop17
import Elements.BookI.Prop19
import Elements.BookI.Prop20
import Elements.BookIII.Prop02

/-!
# Book III: comparing angles near a vertex

The steps that the companions of III.16 and III.31 share, and that cite a proposition; the
words they use are in `Foundations/DefinitionsIII.lean`, and the facts that cite none are
in Book Zero (`Figure/Regions.lean`).

* **Within the circle, by III.2.** A point between two points on or within a circle is
  within it; once a straight line has left a circle it does not come back; three points of
  a circle are not on one straight line. Each follows from III.2.
* **Whole circles about a point.** A point on one side of a straight line, within a circle
  or without it, has a whole circle about it on that side, within, or without. The radius
  is the distance to the foot of the perpendicular [I. 12], or to the circumference along
  the straight line through the centre, and the other points are farther [I. 17, I. 19,
  I. 20].
* **The order of rectilineal angles.** For two rectilineal angles with a common arm, on one
  side of it, the comparison near the vertex is the order of the angles, and comparisons
  chain.
* **Near the vertex, in a circle.** An angle between two straight lines in a circle lies
  within it near its vertex; and where one arm runs into a circle and the other stays
  without it, every circle about the vertex holds whole circles on either side of the
  circumference, within the angle.

Each docstring ends with the propositions the step cites; the certificate walks through it
and records them.
-/

namespace Elements

open Tacit

variable {A B C D E F P Q : Point} {α γ : Circle}

/-! ## Within the circle, by III.2 -/

/-- **III.2 for points on or within the circle.** A point between two points on or within a
circle is within it. Produced beyond each end that is within, the
straight line meets the circle (System E, Intersections 5), and the point lies between the
two points where it meets it. [III. 2] -/
theorem InsideCircle.of_between
    (hA : InsideCircle A α ∨ OnCircle A α) (hB : InsideCircle B α ∨ OnCircle B α)
    (h : Between A C B) : InsideCircle C α := by
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B (ne_of_between_ends h)
  obtain ⟨P, hP, hP_L, hPCB⟩ : ∃ P : Point, OnCircle P α ∧ OnLine P L ∧ Between P C B := by
    rcases hA with hA | hA
    · obtain ⟨P, hP, hP_L, hPAB⟩ :=
        line_circle_beyond hA hA_L hB_L (ne_of_between_ends h).symm
      exact ⟨P, hP, hP_L,
        between_symm (between_of_between_left (between_symm hPAB) (between_symm h))⟩
    · exact ⟨A, hA, hA_L, h⟩
  obtain ⟨Q, hQ, hPCQ⟩ : ∃ Q : Point, OnCircle Q α ∧ Between P C Q := by
    rcases hB with hB | hB
    · obtain ⟨Q, hQ, -, hQBP⟩ := line_circle_beyond hB hB_L hP_L (ne_of_between_ends hPCB)
      exact ⟨Q, hQ, between_of_between_left (between_symm hQBP) hPCB⟩
    · exact ⟨B, hB, hPCB⟩
  exact BookIII.Prop2 hP hQ C hPCQ

/-- **A straight line that has left the circle does not come back.** If C, not within the
circle, lies between A, on or within it, and B, then B is without the circle: were B on or within it, C would be within. [III. 2] -/
theorem OutsideCircle.of_between
    (hA : InsideCircle A α ∨ OnCircle A α) (hC : ¬ InsideCircle C α) (h : Between A C B) :
    OutsideCircle B α :=
  ⟨fun hB => hC (InsideCircle.of_between hA (Or.inl hB) h),
    fun hB => hC (InsideCircle.of_between hA (Or.inr hB) h)⟩

/-- Three points of a circle are not on one straight line: were they, one
would lie between the other two, and so within the circle, not on it. [III. 2] -/
theorem Triangle.of_onCircle_centre
    (hA : OnCircle A α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) : Triangle A B C := by
  rintro ⟨L, hA_L, hB_L, hC_L⟩
  rcases between_cases hAB hBC hAC hA_L hB_L hC_L with h | h | h
  · exact inside_not_on (BookIII.Prop2 hA hC B h) hB
  · exact inside_not_on (BookIII.Prop2 hB hC A h) hA
  · exact inside_not_on (BookIII.Prop2 hA hB C h) hC

/-- **The angle of a segment, as Euclid draws it.** For a straight line AC in a circle, and a
point S off AC, the angle of the segment on S's side is well formed: the ray AC passes
within the circle, between A and C. [III. 2] -/
theorem MixedAngle.wellFormed_ofSegment {S : Point}
    (hA : OnCircle A α) (hC : OnCircle C α) (hAC : A ≠ C) (hS : ¬ Collinear A C S) :
    (MixedAngle.ofSegment A C α S).WellFormed := by
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hAC
  obtain ⟨X, -, hAXC, -⟩ := exists_point_between hA_L hC_L hAC []
  exact ⟨hA, ⟨X, OnRay.of_between hAXC, BookIII.Prop2 hA hC X hAXC⟩, hS⟩

/-! ## Whole circles about a point -/

/-- **The perpendicular is the least straight line to a straight line.** If N is the foot of
the perpendicular from A to the straight line BC, every other point X of BC is farther from
A: the angle at N is right, so the angle at X is less, and the greater side is opposite the
greater angle. [I. 17, I. 19] -/
theorem foot_nearest {N : Point} (hBC : B ≠ C) (hA : ¬ Collinear B C A)
    (hN : Collinear B C N) (hright : ∀ X : Point, Collinear B C X → X ≠ N → ∠ A N X = ∟) :
    ∀ X : Point, Collinear B C X → X = N ∨ ‖A N‖ < ‖A X‖ := by
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hBC
  have hA_L : ¬ OnLine A L := fun h => hA ⟨L, hB_L, hC_L, h⟩
  have hN_L : OnLine N L := onLine_of_collinear hBC hN hB_L hC_L
  intro X hX
  by_cases hXN : X = N
  · exact Or.inl hXN
  · right
    have hX_L : OnLine X L := onLine_of_collinear hBC hX hB_L hC_L
    have hANX : Triangle A N X := (Triangle.of_line hN_L hX_L (Ne.symm hXN) hA_L).cab
    have hANX' : ∠ A N X = ∟ := hright X hX hXN
    have h17 := (BookI.Prop17 hANX).1
    rw [hANX'] at h17
    have hNXA : ∠ N X A < ∠ A N X := by
      rw [hANX']; exact Magnitude.lt_of_add_lt_add_left h17
    exact BookI.Prop19 hANX hNXA

/-- **Two sides of a triangle are greater than the third**, said so that it holds when the
three points make no triangle too: if OP and PQ together are less than a length `x`, so is
OQ. For three points of one straight line, one lies between the other two (System E,
Between 6), and the whole is the sum of its parts or less than it. [I. 20] -/
theorem len_lt_of_add_lt {O : Point} {x : Length} (h : ‖O P‖ + ‖P Q‖ < x) : ‖O Q‖ < x := by
  by_cases hOP : O = P
  · subst hOP
    rw [len_self, add_comm, add_zero] at h
    exact h
  by_cases hPQ : P = Q
  · subst hPQ
    rw [len_self, add_zero] at h
    exact h
  by_cases hOQ : O = Q
  · subst hOQ
    rw [len_self]
    rcases lt_trichotomy 0 x with h0 | h0 | h0
    · exact h0
    · subst h0; exact absurd h (not_lt_zero _)
    · exact absurd h0 (not_lt_zero _)
  by_cases hcol : Collinear O P Q
  · obtain ⟨L, hO, hP, hQ⟩ := hcol
    rcases between_cases hOP hPQ hOQ hO hP hQ with hb | hb | hb
    · rw [len_add_of_between hb] at h; exact h
    · have h₁ : ‖O Q‖ < ‖P Q‖ := by
        rw [len_symm O Q, len_symm P Q]; exact len_lt_of_between (between_symm hb)
      have h₂ : ‖P Q‖ < ‖O P‖ + ‖P Q‖ := by
        rw [add_comm]; exact CommonNotion5 (len_pos hOP)
      exact lt_trans h₁ (lt_trans h₂ h)
    · exact lt_trans (len_lt_of_between hb) (lt_trans (CommonNotion5 (len_pos hPQ)) h)
  · have hOPQ : Triangle O P Q := hcol
    exact lt_trans (BookI.Prop20 hOPQ.bac).1 h

/-- **A point on one side of a straight line has a whole circle about it on that side.** The
circle about P through N, the foot of the perpendicular from P to AB: a point within it,
on AB or beyond it, would put a point of AB nearer P than N is (System E, Intersection 1).
[I. 12, I. 17, I. 19] -/
theorem surrounds_sameSideOf (h : SameSideOf P C A B) :
    Surrounds (fun Q => SameSideOf Q C A B) P := by
  have hAB : A ≠ B := h.1
  have hABP : Triangle A B P := h.triangle
  obtain ⟨N, hN, hright⟩ := BookI.Prop12 hAB hABP
  have hnear := foot_nearest hAB hABP hN hright
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hP_L : ¬ OnLine P L := hABP.off_line hA_L hB_L
  have hPN : P ≠ N := fun e => hP_L (e ▸ onLine_of_collinear hAB hN hA_L hB_L)
  obtain ⟨δ, hδ, hNδ⟩ := Postulate3 P N hPN
  refine ⟨δ, hδ, fun Q hQ => ?_⟩
  have hPQ : ‖P Q‖ < ‖P N‖ := len_lt_of_inside hδ hNδ hQ
  have hnot : ∀ X : Point, OnLine X L → ‖P X‖ < ‖P N‖ → False := fun X hX hlt => by
    rcases hnear X ⟨L, hA_L, hB_L, hX⟩ with e | h'
    · rw [e] at hlt; exact lt_irrefl _ hlt
    · exact lt_irrefl _ (lt_trans hlt h')
  have hQ_L : ¬ OnLine Q L := fun hQL => hnot Q hQL hPQ
  refine (SameSideOf.of_line hAB hA_L hB_L ?_ : SameSideOf Q P A B).trans h
  refine Classical.byContradiction fun hs => ?_
  obtain ⟨X, hX_L, hQXP⟩ := OppositeSides.exists_between ⟨hQ_L, hP_L, hs⟩
  exact hnot X hX_L (lt_trans (len_lt_of_between (between_symm hQXP)) hPQ)

/-- **A point within a circle has a whole circle about it within the circle.** If P is not
the centre O, the circle about P through K, where OP produced beyond P meets the
circumference (System E, Intersections 5): a point Q within it is nearer O than K is, since
OQ is at most OP and PQ together, and their sum is less than OP and PK together, which make OK.
[I. 20] -/
theorem surrounds_inside (hP : InsideCircle P α) :
    Surrounds (fun Q => InsideCircle Q α) P := by
  obtain ⟨O, hO⟩ := exists_centre α
  by_cases hPO : P = O
  · subst hPO
    exact ⟨α, hO, fun Q hQ => hQ⟩
  obtain ⟨L, hP_L, hO_L⟩ := Postulate1 P O hPO
  obtain ⟨K, hK, -, hKPO⟩ := line_circle_beyond hP hP_L hO_L (Ne.symm hPO)
  have hPK : P ≠ K := fun e => inside_not_on (e ▸ hP) hK
  obtain ⟨δ, hδ, hKδ⟩ := Postulate3 P K hPK
  refine ⟨δ, hδ, fun Q hQ => inside_of_len_lt hO hK (len_lt_of_add_lt (P := P) ?_)⟩
  have hsum : ‖O P‖ + ‖P K‖ = ‖O K‖ := len_add_of_between (between_symm hKPO)
  rw [← hsum, add_comm ‖O P‖, add_comm ‖O P‖]
  exact add_lt_add_right _ (len_lt_of_inside hδ hKδ hQ)

/-- **A point without a circle has a whole circle about it without the circle.** The circle
about P through K, where the straight line from the centre O to P crosses the circumference
(System E, Intersections 4): were a point Q within it no farther from O than K is, OQ, QP
together would be less than OK, KP together, which make OP. [I. 20] -/
theorem surrounds_outside (hP : OutsideCircle P α) :
    Surrounds (fun Q => OutsideCircle Q α) P := by
  obtain ⟨O, hO⟩ := exists_centre α
  have hPO : P ≠ O := fun e => hP.1 (e ▸ centre_inside hO)
  obtain ⟨L, hO_L, hP_L⟩ := Postulate1 O P (Ne.symm hPO)
  obtain ⟨K, hK, -, hOKP⟩ := line_circle_between (centre_inside hO) hO_L hP hP_L
  have hPK : P ≠ K := fun e => hP.2 (e ▸ hK)
  obtain ⟨δ, hδ, hKδ⟩ := Postulate3 P K hPK
  refine ⟨δ, hδ, fun Q hQ => outside_of_len_gt hO hK ?_⟩
  have hQP : ‖Q P‖ < ‖K P‖ := by
    rw [len_symm Q P, len_symm K P]; exact len_lt_of_inside hδ hKδ hQ
  have hsum : ‖O K‖ + ‖K P‖ = ‖O P‖ := len_add_of_between hOKP
  rcases lt_trichotomy ‖O K‖ ‖O Q‖ with h | h | h
  · exact h
  · exfalso
    have hlt : ‖O Q‖ + ‖Q P‖ < ‖O P‖ := by
      rw [← hsum, h, add_comm ‖O Q‖, add_comm ‖O Q‖]; exact add_lt_add_right _ hQP
    exact lt_irrefl _ (len_lt_of_add_lt hlt)
  · exfalso
    have h₂ : ‖O K‖ + ‖Q P‖ < ‖O K‖ + ‖K P‖ := by
      rw [add_comm ‖O K‖, add_comm ‖O K‖]; exact add_lt_add_right _ hQP
    have hlt : ‖O Q‖ + ‖Q P‖ < ‖O P‖ := by
      rw [← hsum]; exact lt_trans (add_lt_add_right _ h) h₂
    exact lt_irrefl _ (len_lt_of_add_lt hlt)

/-- **Only the neighbourhood of A counts.** If, within some circle `γ₀` about A, the points
of T are points of U, then whole circles of T as near A as we please give whole circles
of U: each is shrunk to lie within `γ₀`. [I. 20] -/
theorem NearVertexOpen.mono_near {T U : Point → Prop} {γ₀ : Circle} (h : NearVertexOpen A T)
    (hγ₀ : Centre A γ₀) (hTU : ∀ Q, InsideCircle Q γ₀ → T Q → U Q) : NearVertexOpen A U := by
  intro γ hγ
  obtain ⟨γ', hγ', hboth⟩ := exists_inside_both hγ hγ₀
  obtain ⟨P, hPγ', δ, hδ, hT⟩ := h γ' hγ'
  obtain ⟨δ₁, hδ₁, hin⟩ := surrounds_inside (hboth P hPγ').2
  obtain ⟨δ', hδ', hδδ⟩ := exists_inside_both hδ hδ₁
  exact ⟨P, (hboth P hPγ').1, δ', hδ', fun Q hQ =>
    hTU Q (hin Q (hδδ Q hQ).2) (hT Q (hδδ Q hQ).1)⟩

/-- **The region of an angle has no edge points.** A point within the angle BAC has a whole
circle about it within the angle. [I. 12, I. 17, I. 19] -/
theorem WithinAngle.surrounds (h : WithinAngle B A C P) : Surrounds (WithinAngle B A C) P :=
  (surrounds_sameSideOf h.1).and (surrounds_sameSideOf h.2)

/-- Every circle about the vertex of an angle holds a whole circle within the angle.
[I. 12, I. 17, I. 19] -/
theorem WithinAngle.nearVertexOpen {U V : Point} (hUAV : Triangle U A V) :
    NearVertexOpen A (WithinAngle U A V) :=
  NearVertexOpen.of_nearVertex (fun _ hP => hP.surrounds) (fun _ hγ => exists_near hUAV hγ)

/-! ## The order of rectilineal angles -/

/-- **The less angle is locally less.** If D and C are on the same side of AB, and the angle
BAD is less than the angle BAC, then the region of BAD lies within that of BAC, near A and
everywhere, and every circle about A holds a whole circle within the angle DAC, which is
within BAC and has no point within BAD. [I. 12, I. 17, I. 19] -/
theorem WithinAngle.locallyLess_of_lt (hDC : SameSideOf D C A B) (h : ∠ B A D < ∠ B A C) :
    LocallyLess A (WithinAngle B A D) (WithinAngle B A C) := by
  have hD : WithinAngle B A C D := ⟨hDC, sameSideOf_of_angle_lt hDC h⟩
  obtain ⟨γ₀, hγ₀⟩ := exists_circle_about A
  refine ⟨⟨γ₀, hγ₀, fun P _ hP => WithinAngle.mono_left hD hP⟩, ?_⟩
  exact (WithinAngle.nearVertexOpen hD.2.triangle.cab).mono fun P hP =>
    ⟨WithinAngle.mono_right hD hP, fun h' => hD.not_sameSideOf (h'.2.symm.trans hP.1)⟩

/-- **Locally less is less.** For two rectilineal angles BAD, BAC with the common arm AB and
D, C on the same side of it, the angle BAD is locally less than the angle BAC exactly when it
is less as an angle. [I. 12, I. 17, I. 19] -/
theorem WithinAngle.locallyLess_iff (hDC : SameSideOf D C A B) :
    LocallyLess A (WithinAngle B A D) (WithinAngle B A C) ↔ ∠ B A D < ∠ B A C := by
  refine ⟨fun hL => ?_, WithinAngle.locallyLess_of_lt hDC⟩
  rcases lt_trichotomy (∠ B A D) (∠ B A C) with h | h | h
  · exact h
  · exfalso
    obtain ⟨γ, hγ⟩ := exists_circle_about A
    obtain ⟨P, -, hC, hD⟩ := hL.2.nearVertex γ hγ
    exact hD ((WithinAngle.eq_of_angle_eq hDC h).2 hC)
  · exact (not_locallyWithin hL.1 (WithinAngle.locallyLess_of_lt hDC.symm h).2.nearVertex).elim

/-- **Locally equal is equal.** For two rectilineal angles BAD, BAC with the common arm AB
and D, C on the same side of it, the angles are locally equal exactly when they are equal as
angles. [I. 12, I. 17, I. 19] -/
theorem WithinAngle.locallyEqual_iff (hDC : SameSideOf D C A B) :
    LocallyEqual A (WithinAngle B A D) (WithinAngle B A C) ↔ ∠ B A D = ∠ B A C := by
  constructor
  · intro hE
    rcases lt_trichotomy (∠ B A D) (∠ B A C) with h | h | h
    · exact (not_locallyWithin hE.2 (WithinAngle.locallyLess_of_lt hDC h).2.nearVertex).elim
    · exact h
    · exact (not_locallyWithin hE.1
        (WithinAngle.locallyLess_of_lt hDC.symm h).2.nearVertex).elim
  · intro h
    obtain ⟨γ, hγ⟩ := exists_circle_about A
    exact ⟨⟨γ, hγ, fun P _ hP => (WithinAngle.eq_of_angle_eq (P := P) hDC h).1 hP⟩,
      ⟨γ, hγ, fun P _ hP => (WithinAngle.eq_of_angle_eq (P := P) hDC h).2 hP⟩⟩

/-- **Less than a less is less.** Near A, R lies within S and S within T; the whole
circles of T outside S, shrunk to the circle where R lies within S, are outside R.
[I. 20] -/
theorem LocallyLess.trans {R S T : Point → Prop} (h₁ : LocallyLess A R S)
    (h₂ : LocallyLess A S T) : LocallyLess A R T := by
  refine ⟨h₁.1.trans h₂.1, ?_⟩
  obtain ⟨γ₁, hγ₁, f₁⟩ := h₁.1
  exact h₂.2.mono_near hγ₁ fun Q hQ hT => ⟨hT.1, fun hR => hT.2 (f₁ Q hQ hR)⟩

/-- **Equal angles compare alike, on the left.** If R and R' are locally equal, and R is
locally less than S, so is R'. [I. 20] -/
theorem LocallyLess.congr_left {R R' S : Point → Prop} (hE : LocallyEqual A R R')
    (h : LocallyLess A R S) : LocallyLess A R' S := by
  refine ⟨hE.2.trans h.1, ?_⟩
  obtain ⟨γ₁, hγ₁, f₁⟩ := hE.2
  exact h.2.mono_near hγ₁ fun Q hQ hT => ⟨hT.1, fun hR' => hT.2 (f₁ Q hQ hR')⟩

/-- **Equal angles compare alike, on the right.** If S and S' are locally equal, and R is
locally less than S, it is locally less than S'. [I. 20] -/
theorem LocallyLess.congr_right {R S S' : Point → Prop} (hE : LocallyEqual A S S')
    (h : LocallyLess A R S) : LocallyLess A R S' := by
  refine ⟨h.1.trans hE.1, ?_⟩
  obtain ⟨γ₁, hγ₁, f₁⟩ := hE.1
  exact h.2.mono_near hγ₁ fun Q hQ hT => ⟨f₁ Q hQ hT.1, hT.2⟩

/-! ## Near the vertex, in a circle -/

/-- **An angle between two straight lines in a circle lies within it near its vertex.** If A,
B and C are on or within a circle that has a centre, and BAC is a true angle, some circle
about A holds no point of the angle BAC, nor of its arms, that is not within the circle.
The circle about A passes through N, the foot of the perpendicular from A to BC; every other
point X of the straight line BC is farther from A. A point P of the angle within that
circle lies on a ray from A that crosses BC at some X, nearer A than X, and so between A and
a point within the circle. [I. 12, I. 17, I. 19, III. 2] -/
theorem near_inside_of_angle
    (hA : InsideCircle A α ∨ OnCircle A α) (hB : InsideCircle B α ∨ OnCircle B α)
    (hC : InsideCircle C α ∨ OnCircle C α) (hBAC : Triangle B A C) :
    LocallyWithin A (fun P => WithinAngle B A C P ∨ OnRay P A B ∨ OnRay P A C)
      (fun P => InsideCircle P α) := by
  have hBC : B ≠ C := hBAC.ne₁₃
  have hA_BC : ¬ Collinear B C A := fun ⟨L, hB_L, hC_L, hA_L⟩ => hBAC ⟨L, hB_L, hA_L, hC_L⟩
  obtain ⟨N, hN, hright⟩ := BookI.Prop12 hBC hA_BC
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hBC
  have hA_L : ¬ OnLine A L := fun h => hA_BC ⟨L, hB_L, hC_L, h⟩
  have hN_L : OnLine N L := onLine_of_collinear hBC hN hB_L hC_L
  have hAN : A ≠ N := fun e => hA_L (e ▸ hN_L)
  have hfar := foot_nearest hBC hA_BC hN hright
  obtain ⟨γ, hγ, hNγ⟩ := Postulate3 A N hAN
  refine ⟨γ, hγ, fun P hPγ hP => ?_⟩
  have hAP : ‖A P‖ < ‖A N‖ := len_lt_of_inside hγ hNγ hPγ
  have hnear : ∀ X : Point, OnLine X L → OnRay P A X → Between A P X := by
    intro X hX hPX
    have hlt : ‖A P‖ < ‖A X‖ := by
      rcases hfar X ⟨L, hB_L, hC_L, hX⟩ with e | h
      · rw [e]; exact hAP
      · exact lt_trans hAP h
    exact OnRay.between_of_len_lt hPX (OnRay.self hPX.1) hlt
  rcases hP with hW | hPB | hPC
  · obtain ⟨X, hBXC, hXP⟩ := crossbar hW.1 hW.2
    have hXα : InsideCircle X α := InsideCircle.of_between hB hC hBXC
    exact InsideCircle.of_between hA (Or.inl hXα)
      (hnear X (on_line_of_between_ends hBXC hB_L hC_L) hXP.symm)
  · exact InsideCircle.of_between hA hB (hnear B hB_L hPB)
  · exact InsideCircle.of_between hA hC (hnear C hC_L hPC)

/-- **Points on either side of the circumference, near the vertex.** Let UAV be a true angle,
with the points of the ray AU near A within a circle, and every point of the ray AV
without it. Then every circle about A holds a point within the angle UAV and within the
circle, and another within the angle and without it: on the straight line from a point Y of
AU to a point W of AV, both near A, on either side of the point where it crosses the
circumference (System E, Intersections 4). [III. 2] -/
theorem exists_near_across {U V : Point} (hUAV : Triangle U A V)
    (hU : LocallyWithin A (fun P => OnRay P A U) (fun P => InsideCircle P α))
    (hV : ∀ P : Point, OnRay P A V → OutsideCircle P α) (hγ : Centre A γ) :
    (∃ P : Point, InsideCircle P γ ∧ WithinAngle U A V P ∧ InsideCircle P α) ∧
      (∃ P : Point, InsideCircle P γ ∧ WithinAngle U A V P ∧ OutsideCircle P α) := by
  obtain ⟨γ₀, hγ₀, hU'⟩ := hU
  obtain ⟨γ', hγ', hboth⟩ := exists_inside_both hγ hγ₀
  obtain ⟨Y, hY, hYγ'⟩ := exists_onRay_inside hγ' hUAV.ne₁₂.symm
  obtain ⟨W, hW, hWγ'⟩ := exists_onRay_inside hγ' hUAV.ne₂₃
  have hYα : InsideCircle Y α := hU' Y (hboth Y hYγ').2 hY
  have hWα : OutsideCircle W α := hV W hW
  have hYW : Y ≠ W := fun e => hWα.1 (e ▸ hYα)
  obtain ⟨L, hY_L, hW_L⟩ := Postulate1 Y W hYW
  obtain ⟨X, hXα, hX_L, hYXW⟩ := line_circle_between hYα hY_L hWα hW_L
  obtain ⟨P₁, -, hYP₁X, -⟩ := exists_point_between hY_L hX_L (ne_of_between hYXW) []
  have hYP₁W : Between Y P₁ W := between_of_between_left hYXW hYP₁X
  obtain ⟨P₂, -, hXP₂W, -⟩ :=
    exists_point_between hX_L hW_L (ne_of_between (between_symm hYXW)).symm []
  have hYP₂W : Between Y P₂ W :=
    between_symm (between_of_between_left (between_symm hYXW) (between_symm hXP₂W))
  have hinγ : ∀ P : Point, Between Y P W → InsideCircle P γ := fun P h =>
    (hboth P (InsideCircle.of_between (Or.inl hYγ') (Or.inl hWγ') h)).1
  exact ⟨⟨P₁, hinγ P₁ hYP₁W, WithinAngle.of_between hUAV hY hW hYP₁W,
      InsideCircle.of_between (Or.inl hYα) (Or.inr hXα) hYP₁X⟩,
    ⟨P₂, hinγ P₂ hYP₂W, WithinAngle.of_between hUAV hY hW hYP₂W,
      OutsideCircle.of_between (Or.inl hYα) (fun h => inside_not_on h hXα)
        (between_cut hYXW hXP₂W)⟩⟩

/-- **Whole circles on either side of the circumference, near the vertex.** In the figure of
`exists_near_across`, every circle about A holds a whole circle within the angle UAV and
within the circle, and another within the angle and without it. [I. 12, I. 17, I. 19,
I. 20, III. 2] -/
theorem near_across {U V : Point} (hUAV : Triangle U A V)
    (hU : LocallyWithin A (fun P => OnRay P A U) (fun P => InsideCircle P α))
    (hV : ∀ P : Point, OnRay P A V → OutsideCircle P α) :
    NearVertexOpen A (fun P => WithinAngle U A V P ∧ InsideCircle P α) ∧
      NearVertexOpen A (fun P => WithinAngle U A V P ∧ OutsideCircle P α) :=
  ⟨NearVertexOpen.of_nearVertex (fun _ hP => hP.1.surrounds.and (surrounds_inside hP.2))
      (fun _ hγ => (exists_near_across hUAV hU hV hγ).1),
    NearVertexOpen.of_nearVertex (fun _ hP => hP.1.surrounds.and (surrounds_outside hP.2))
      (fun _ hγ => (exists_near_across hUAV hU hV hγ).2)⟩

/-- The points of a ray from a point A of a circle towards a point B on or within it are,
near A, within the circle: some circle about A holds no point of the ray that is not between
A and B. [III. 2] -/
theorem near_inside_of_ray (hA : OnCircle A α)
    (hB : InsideCircle B α ∨ OnCircle B α) (hAB : A ≠ B) :
    LocallyWithin A (fun P => OnRay P A B) (fun P => InsideCircle P α) := by
  obtain ⟨γ₀, hγ₀, hBγ₀⟩ := Postulate3 A B hAB
  exact ⟨γ₀, hγ₀, fun P hP hPB => InsideCircle.of_between (Or.inr hA) hB
    (OnRay.between_of_len_lt hPB (OnRay.self hAB) (len_lt_of_inside hγ₀ hBγ₀ hP))⟩

/-- The ray AC is, near A, within the circle if some point K of it is on or within the
circle: the ray AC is the ray AK. [III. 2] -/
theorem near_inside_of_onRay {K : Point} (hA : OnCircle A α)
    (hK : OnRay K A C) (hKα : InsideCircle K α ∨ OnCircle K α) :
    LocallyWithin A (fun P => OnRay P A C) (fun P => InsideCircle P α) := by
  obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside_of_ray hA hKα hK.2.1.symm
  exact ⟨γ₀, hγ₀, fun P hP hPC => hnear P hP (OnRay.of_sameRay hPC hK)⟩

end Elements
