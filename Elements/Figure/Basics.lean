import Elements.Foundations.Tacit.Superposition
import Elements.Foundations.Phrases

/-!
# Book Zero: small facts every figure needs

Euclid never proves these, and nobody reading him would want him to. They are
proved here once, from the postulates and the tacit rules, so that the proofs
of the propositions can cite them by name and stay close to Euclid's words.

Nothing in this file cites a proposition of the *Elements*.
-/

namespace Elements

open Tacit

variable {A B C D : Point} {L M : Line} {α β : Circle}

/-! ## Magnitudes -/

/-- If `a` is something, then `a` and `a` together are more than `a`. -/
theorem Magnitude.add_self_ne {k : Kind} {a : Magnitude k} (h : a ≠ 0) : a + a ≠ a := by
  intro h'
  have hpos : 0 < a := by
    rcases lt_trichotomy 0 a with h₁ | h₁ | h₁
    · exact h₁
    · exact absurd h₁.symm h
    · exact absurd h₁ (not_lt_zero a)
  have := CommonNotion5 (a := a) hpos
  rw [h'] at this
  exact lt_irrefl a this

/-- A magnitude that is something is more than nothing. -/
theorem Magnitude.pos_of_ne_zero {k : Kind} {a : Magnitude k} (h : a ≠ 0) : 0 < a := by
  rcases lt_trichotomy 0 a with h₁ | h₁ | h₁
  · exact h₁
  · exact absurd h₁.symm h
  · exact absurd h₁ (not_lt_zero a)

/-- Unequal magnitudes, if one is less. -/
theorem Magnitude.ne_of_lt {k : Kind} {a b : Magnitude k} (h : a < b) : a ≠ b := by
  intro e
  rw [e] at h
  exact lt_irrefl _ h

/-- A finite straight line with different ends has some length. -/
theorem len_ne_zero (h : A ≠ B) : ‖A B‖ ≠ 0 := fun h' => h (eq_of_len_eq_zero h')

/-- A finite straight line with different ends has some length. -/
theorem len_pos (h : A ≠ B) : 0 < ‖A B‖ := Magnitude.pos_of_ne_zero (len_ne_zero h)

/-- If a finite straight line `AB` has the length of one with different ends,
its own ends are different. -/
theorem ne_of_len_eq {C D : Point} (h : ‖A B‖ = ‖C D‖) (hCD : C ≠ D) : A ≠ B := by
  intro e
  subst e
  rw [len_self] at h
  exact len_ne_zero hCD h.symm

/-- If `AB` is longer than something, its ends are different. -/
theorem ne_of_len_gt {x : Length} (h : x < ‖A B‖) : A ≠ B := by
  intro e
  subst e
  rw [len_self] at h
  exact not_lt_zero x h

/-! ## Points and lines -/

/-- Every point lies on some straight line. -/
theorem exists_line_through (A : Point) : ∃ L : Line, OnLine A L := by
  obtain ⟨B, hB⟩ := exists_point [A]
  have hAB : A ≠ B := fun h => hB (h ▸ List.mem_singleton_self A)
  obtain ⟨L, hA, -⟩ := Postulate1 A B hAB
  exact ⟨L, hA⟩

/-- Any two points lie on some straight line. -/
theorem collinear_of_two (A B : Point) : ∃ L : Line, OnLine A L ∧ OnLine B L := by
  by_cases h : A = B
  · subst h
    obtain ⟨L, hL⟩ := exists_line_through A
    exact ⟨L, hL, hL⟩
  · exact Postulate1 A B h

/-- The corners of a triangle are different points. -/
theorem Triangle.ne₁₂ (h : Triangle A B C) : A ≠ B := by
  intro hAB
  subst hAB
  obtain ⟨L, hA, hC⟩ := collinear_of_two A C
  exact h ⟨L, hA, hA, hC⟩

/-- The corners of a triangle are different points. -/
theorem Triangle.ne₂₃ (h : Triangle A B C) : B ≠ C := by
  intro hBC
  subst hBC
  obtain ⟨L, hA, hB⟩ := collinear_of_two A B
  exact h ⟨L, hA, hB, hB⟩

/-- The corners of a triangle are different points. -/
theorem Triangle.ne₁₃ (h : Triangle A B C) : A ≠ C := by
  intro hAC
  subst hAC
  obtain ⟨L, hA, hB⟩ := collinear_of_two A B
  exact h ⟨L, hA, hB, hA⟩

/-! ## Circles -/

/-- A point on a circle is not its centre. -/
theorem ne_of_centre_of_on (hA : Centre A α) (hC : OnCircle C α) : C ≠ A := by
  intro h
  subst h
  exact inside_not_on (centre_inside hA) hC

/-- A point on a circle is not inside it. -/
theorem not_inside_of_on (h : OnCircle A α) : ¬ InsideCircle A α :=
  fun h' => inside_not_on h' h

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

end Elements
