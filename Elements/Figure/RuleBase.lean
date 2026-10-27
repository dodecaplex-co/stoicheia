import Elements.Foundations.Tacit.Transfer

/-!
# Book Zero: elementary incidence and separation

These rules keep their original names and statements from System E. Their proofs use
point construction, Pasch 2, angle addition and circle chords. Lengths then build on
the proved separation of distinct endpoints, without assuming it: a circle drawn about
one end through the other has a radius, and a radius is not nothing, by a rule of our
own (`Tacit.radius_ne_zero`).
-/

namespace Elements

open Tacit

variable {A B C D E F : Point} {L M N : Line} {α β : Circle}

namespace RuleProofs.Circle

/-- If a sum of magnitudes is nothing, its second part is nothing. -/
theorem right_eq_zero_of_add_eq_zero {k : Kind} {a b : Magnitude k}
    (h : a + b = 0) : b = 0 := by
  rcases lt_trichotomy b 0 with hb | hb | hb
  · exact False.elim (not_lt_zero b hb)
  · exact hb
  · have ha := CommonNotion5 (a := a) hb
    rw [h] at ha
    exact False.elim (not_lt_zero a ha)

/-- The first and middle points of an order differ: were they one point, Between 1 would
deny the order itself. -/
theorem ne_first (h : Between A B C) : A ≠ B := by
  intro e
  subst B
  exact not_between_of_between h h

/-- A circle's radius is not nothing: the radius rule (`Tacit.radius_ne_zero`), a rule of our
own. Every positive length in Book Zero comes through this lemma. -/
theorem radius_ne_zero (hA : Centre A α) (hB : OnCircle B α) : ‖A B‖ ≠ 0 :=
  Tacit.radius_ne_zero hA hB

/-- Distinct points are some distance apart: a circle about one through the other has a radius. -/
theorem length_pos (h : A ≠ B) : 0 < ‖A B‖ := by
  obtain ⟨α, hA, hB⟩ := Postulate3 A B h
  rcases lt_trichotomy 0 ‖A B‖ with h₁ | h₁ | h₁
  · exact h₁
  · exact False.elim (radius_ne_zero hA hB h₁.symm)
  · exact False.elim (not_lt_zero _ h₁)

end RuleProofs.Circle

/-- The centre of a circle is inside it. (Generalities 3) A centre that were not inside would
lie on a straight line through an inside point beyond it, and its radii to the two crossings
would be unequal. -/
theorem Tacit.centre_inside (hA : Centre A α) : InsideCircle A α := by
  apply Classical.byContradiction
  intro hnot
  obtain ⟨O, hO, havoid⟩ := exists_point_inside_circle α [A]
  have hAO : A ≠ O := by
    intro e
    subst O
    exact havoid (List.mem_singleton_self A)
  obtain ⟨L, hAL, hOL⟩ := Postulate1 A O hAO
  obtain ⟨P, hP, _, hPOA⟩ := line_circle_beyond hO hOL hAL hAO
  have hnoton : ¬ OnCircle A α := fun hon =>
    RuleProofs.Circle.radius_ne_zero hA hon (len_self A)
  obtain ⟨Q, hQ, _, hOQA⟩ := line_circle_between hO hOL ⟨hnot, hnoton⟩ hAL
  have h₁ := CommonNotion5 (a := ‖O A‖)
    (RuleProofs.Circle.length_pos (RuleProofs.Circle.ne_first hPOA))
  rw [add_comm ‖O A‖ ‖P O‖, len_add_of_between hPOA] at h₁
  have h₂ := CommonNotion5 (a := ‖Q A‖)
    (RuleProofs.Circle.length_pos (RuleProofs.Circle.ne_first hOQA))
  rw [add_comm ‖Q A‖ ‖O Q‖, len_add_of_between hOQA] at h₂
  have heq : ‖Q A‖ = ‖P A‖ :=
    (len_symm Q A).trans ((Definition15 hA hQ hP).trans (len_symm A P))
  have hlt := lt_trans h₂ h₁
  rw [heq] at hlt
  exact lt_irrefl _ hlt

/-- A point at the distance of the radius from the centre is on the circle. (Diagram-segment 3,
the half that Definition 15 doesn't give) The centre itself is excluded, since a radius is never
nothing. A point within would be nearer the centre than the place where the straight line
from the centre through it, produced, meets the circle (Intersections 5); a point without
would be farther than the place where that line leaves the circle (Intersections 4). -/
theorem Tacit.on_circle_of_len_eq (hA : Centre A α) (hB : OnCircle B α) (h : ‖A C‖ = ‖A B‖) :
    OnCircle C α := by
  by_cases hAC : A = C
  · subst C
    exact False.elim (RuleProofs.Circle.radius_ne_zero hA hB (h.symm.trans (len_self A)))
  apply Classical.byContradiction
  intro hon
  obtain ⟨L, hAL, hCL⟩ := Postulate1 A C hAC
  by_cases hin : InsideCircle C α
  · obtain ⟨P, hP, _, hPCA⟩ := line_circle_beyond hin hCL hAL hAC
    have hlt := CommonNotion5 (a := ‖C A‖)
      (RuleProofs.Circle.length_pos (RuleProofs.Circle.ne_first hPCA))
    rw [add_comm ‖C A‖ ‖P C‖, len_add_of_between hPCA, len_symm C A, h, len_symm P A,
      Definition15 hA hP hB] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨P, hP, _, hAPC⟩ := line_circle_between (centre_inside hA) hAL ⟨hin, hon⟩ hCL
    have hlt := CommonNotion5 (a := ‖A P‖)
      (RuleProofs.Circle.length_pos (RuleProofs.Circle.ne_first (between_symm hAPC)).symm)
    rw [len_add_of_between hAPC, h, Definition15 hA hP hB] at hlt
    exact lt_irrefl _ hlt

namespace RuleProofs.Circle

/-- A point other than the centre, as far from it as a point of the circle, is on the circle:
Diagram-segment 3's proved half gives the result from the radius rule and Intersections 4
and 5. -/
theorem on_circle_of_len_eq_of_ne (hA : Centre A α) (hB : OnCircle B α) (hAC : A ≠ C)
    (h : ‖A C‖ = ‖A B‖) : OnCircle C α := by
  exact Tacit.on_circle_of_len_eq hA hB h

end RuleProofs.Circle

/-- If A is on the same side of a straight line as B, then B is on the same side as A.
(Same side 2) Two circles about points of the line cut on A's side, by Intersection 5,
Generalities 3 and Intersections 8; Same side 4 then makes B's relation to A follow from A's to B. -/
theorem Tacit.same_side_symm (h : SameSide A B L) : SameSide B A L := by
  have hA := not_on_line_of_same_side h
  have hAA : SameSide A A L := by
    obtain ⟨O, hOL, _⟩ := exists_point_on_line L []
    obtain ⟨P, hPL, hP⟩ := exists_point_on_line L [O]
    have hOP : O ≠ P := fun e => hP (e ▸ List.mem_singleton_self O)
    obtain ⟨α, hOα, hPα⟩ := Postulate3 O P hOP
    obtain ⟨β, hPβ, hOβ⟩ := Postulate3 P O hOP.symm
    have hm := circles_meet hPα (centre_inside hOα) (centre_inside hPβ) hOβ
    obtain ⟨X, _, _, hXA⟩ := circles_meet_same_side hm hOα hPβ hOL hPL hA
    exact same_side_trans hXA hXA
  exact same_side_trans h hAA

/-- Let a point be taken on the same side of L as B. (Points 5) Postulate 2 extends a line from
a point of L beyond B; Pasch 2 puts its endpoint on B's side. -/
theorem Tacit.exists_point_same_side {B : Point} {L : Line} (hB : ¬ OnLine B L) (avoid : List Point) :
    ∃ A : Point, SameSide A B L ∧ A ∉ avoid := by
  obtain ⟨O, hO, _⟩ := exists_point_on_line L []
  have hOB : O ≠ B := fun e => hB (e ▸ hO)
  obtain ⟨M, hOM, hBM⟩ := Postulate1 O B hOB
  obtain ⟨A, _, hOBA, hA⟩ := Postulate2 hOM hBM hOB avoid
  exact ⟨A, same_side_symm (pasch2 hOBA hO hB), hA⟩

/-- A point between two others differs from the first. (Between 1) Coincidence would make the
forbidden reversed order identical to the given order. -/
theorem Tacit.ne_of_between (h : Between A B C) : A ≠ B := by
  intro e
  subst B
  exact not_between_of_between h h

/-- A straight line through A and C passes through every point between them. (Between 3) If the
middle point were off the line, Pasch 2 would put the last endpoint off it too. -/
theorem Tacit.on_line_of_between_ends (h : Between A B C) (hA : OnLine A L) (hC : OnLine C L) :
    OnLine B L := by
  apply Classical.byContradiction
  intro hB
  exact not_on_line_of_same_side (same_side_symm (pasch2 h hA hB)) hC

/-- If two different straight lines L and M meet at B, and A and C are points of M, different
from each other and from B, that are not on the same side of L, then B is between A and C.
(Pasch 4) The other two collinear orders put the endpoints on the same side by Pasch 2. -/
theorem Tacit.pasch4 (hLM : L ≠ M) (hBL : OnLine B L) (hBM : OnLine B M) (hAM : OnLine A M)
    (hCM : OnLine C M) (hAC : A ≠ C) (hAB : A ≠ B) (hCB : C ≠ B) (h : ¬ SameSide A C L) :
    Between A B C := by
  have hAL : ¬ OnLine A L := fun hAL =>
    hLM (line_unique hAB hAL hBL hAM hBM)
  have hCL : ¬ OnLine C L := fun hCL =>
    hLM (line_unique hCB hCL hBL hCM hBM)
  rcases between_cases hAB hCB.symm hAC hAM hBM hCM with horder | horder | horder
  · exact horder
  · exact False.elim (h (pasch2 horder hBL hAL))
  · exact False.elim (h (same_side_symm (pasch2 (between_symm horder) hBL hCL)))

/-- A point off a straight line is on the same side of it as itself. (Same side 1) Choose a
point on its side and apply transitivity to that relation twice. -/
theorem Tacit.same_side_refl (h : ¬ OnLine A L) : SameSide A A L := by
  obtain ⟨B, hBA, _⟩ := exists_point_same_side h []
  exact same_side_trans hBA hBA

namespace RuleProofs.Elementary

/-- A nonzero magnitude is positive, by trichotomy and nonnegativity. -/
theorem positive {k : Kind} {a : Magnitude k} (h : a ≠ 0) : 0 < a := by
  rcases lt_trichotomy 0 a with h₁ | h₁ | h₁
  · exact h₁
  · exact absurd h₁.symm h
  · exact absurd h₁ (not_lt_zero a)

end RuleProofs.Elementary

/-- Take B on L, C on M and D on N, three straight lines through A. If C lies within the angle
BAD (on D's side of L and on B's side of N), then B and D are not on the same side of M: the
straight line AC separates them. (Triple incidence 1) Two angle decompositions would make
each of two angles greater than the other. -/
theorem Tacit.triple_incidence1 (hAL : OnLine A L) (hAM : OnLine A M) (hAN : OnLine A N)
    (hB : OnLine B L) (hC : OnLine C M) (hD : OnLine D N) (hCD : SameSide C D L)
    (hBC : SameSide B C N) : ¬ SameSide B D M := by
  intro hBD
  have hCL := not_on_line_of_same_side hCD
  have hDL := not_on_line_of_same_side (same_side_symm hCD)
  have hBN := not_on_line_of_same_side hBC
  have hCN := not_on_line_of_same_side (same_side_symm hBC)
  have hDM := not_on_line_of_same_side (same_side_symm hBD)
  have hAB : A ≠ B := fun e => hBN (e ▸ hAN)
  have hAC : A ≠ C := fun e => hCL (e ▸ hAL)
  have hAD : A ≠ D := fun e => hDL (e ▸ hAL)
  have hLN : L ≠ N := fun e => hBN (e ▸ hB)
  have hLM : L ≠ M := fun e => hCL (e ▸ hC)
  have e₁ := angle_add_of_inside hAL hAN hB hD hAB hAD hCL hCN hLN hBC
    (same_side_symm hCD)
  have e₂ := angle_add_of_inside hAL hAM hB hC hAB hAC hDL hDM hLM hBD hCD
  have hp₁ : 0 < ∠ C A D := RuleProofs.Elementary.positive
    (fun hz => hDM (same_ray_of_angle_eq_zero hAC hAD hAM hC hz).1)
  have hp₂ : 0 < ∠ D A C := RuleProofs.Elementary.positive
    (fun hz => hCN (same_ray_of_angle_eq_zero hAD hAC hAN hD hz).1)
  have hlt₁ := CommonNotion5 (a := ∠ B A C) hp₁
  have hlt₂ := CommonNotion5 (a := ∠ B A D) hp₂
  rw [← e₁] at hlt₁
  rw [← e₂] at hlt₂
  exact lt_irrefl _ (lt_trans hlt₁ hlt₂)

/-- A straight line through a point between A and C separates them. (Pasch 3) Join A and C to
another point of the line: Pasch 2 puts B within the angle they make there, and Triple
incidence 1 then forbids A and C one side. -/
theorem Tacit.pasch3 (h : Between A B C) (hB : OnLine B L) : ¬ SameSide A C L := by
  intro hAC
  have hAL := not_on_line_of_same_side hAC
  have hCL := not_on_line_of_same_side (same_side_symm hAC)
  obtain ⟨Y, hYL, hY⟩ := exists_point_on_line L [B]
  have hYB : Y ≠ B := fun e => hY (e ▸ List.mem_singleton_self B)
  have hYA : Y ≠ A := fun e => hAL (e ▸ hYL)
  have hYC : Y ≠ C := fun e => hCL (e ▸ hYL)
  obtain ⟨M, hYM, hAM⟩ := Postulate1 Y A hYA
  obtain ⟨N, hYN, hCN⟩ := Postulate1 Y C hYC
  have hBM : ¬ OnLine B M := by
    intro hBM
    exact hAL (line_unique hYB hYM hBM hYL hB ▸ hAM)
  have hBN : ¬ OnLine B N := by
    intro hBN
    exact hCL (line_unique hYB hYN hBN hYL hB ▸ hCN)
  exact triple_incidence1 hYM hYL hYN hAM hB hCN
    (pasch2 h hAM hBM)
    (same_side_symm (pasch2 (between_symm h) hCN hBN)) hAC

/-- A point inside a circle is not on it. (Generalities 4) A line produced from the point meets
the circle; Circle 1 would put that point between itself and the crossing. -/
theorem Tacit.inside_not_on (hA : InsideCircle A α) : ¬ OnCircle A α := by
  intro hon
  obtain ⟨B, hBA⟩ := exists_point [A]
  have hAB : A ≠ B := by
    intro e
    subst B
    exact hBA (List.mem_singleton_self A)
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hAB
  obtain ⟨C, hC, hCL, hCAB⟩ := line_circle_beyond hA hAL hBL hAB.symm
  exact ne_of_between (between_of_inside_chord hAL hAL hCL hA hon hC
    (ne_of_between hCAB).symm) rfl

/-- A finite straight line with distinct ends has length. (Metric 1) A circle drawn about one
end through the other (Postulate 3) has the line for a radius, and a radius is not nothing. -/
theorem Tacit.eq_of_len_eq_zero (h : ‖A B‖ = 0) : A = B := by
  apply Classical.byContradiction
  intro hAB
  obtain ⟨α, hA, hB⟩ := Postulate3 A B hAB
  exact RuleProofs.Circle.radius_ne_zero hA hB h

end Elements
