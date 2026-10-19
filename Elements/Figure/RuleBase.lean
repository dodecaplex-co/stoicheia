import Elements.Foundations.Tacit.Transfer

/-!
# Book Zero: elementary incidence and separation

These rules keep their original names and statements from System E. Their proofs use
point construction, Pasch 2, angle addition and circle chords. Lengths then build on
the proved separation of distinct endpoints, without assuming it.
-/

namespace Elements

open Tacit

variable {A B C D E F : Point} {L M N : Line} {α β : Circle}

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

/-- A finite straight line with distinct ends has length. (Metric 1) A circle drawn with
distinct endpoints would put its own centre on its circumference. -/
theorem Tacit.eq_of_len_eq_zero (h : ‖A B‖ = 0) : A = B := by
  apply Classical.byContradiction
  intro hAB
  obtain ⟨α, hA, hB⟩ := Postulate3 A B hAB
  have hself : ‖A A‖ = ‖A B‖ := (len_self A).trans h.symm
  exact inside_not_on (centre_inside hA) (on_circle_of_len_eq hA hB hself)

end Elements
