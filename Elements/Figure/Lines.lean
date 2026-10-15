import Elements.Figure.Lengths

/-!
# Book Zero: points on a straight line

Euclid reads the order of points on a straight line straight off his figure:
that some straight line passes through two points, which point lies between
which, that a finite straight line can always be produced. These are those
readings, proved from Postulates 1 and 2 and System E's rules for "between"
(Avigad, Dean and Mumma, §3.4).
-/

namespace Elements

open Tacit

variable {A B C D : Point}

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

/-- Three points, one between the other two, lie on one straight line. -/
theorem collinear_of_between (h : Between A B C) : Collinear A B C := by
  obtain ⟨L, hA, hC⟩ := Postulate1 A C (ne_of_between_ends h)
  exact ⟨L, hA, on_line_of_between_ends h hA hC, hC⟩

/-- Order on a straight line: if `B` is between `A` and `C`, and `C` is between `A`
and `D`, then `C` is between `B` and `D`. -/
theorem between_inner (h₁ : Between A B C) (h₂ : Between A C D) : Between B C D := by
  obtain ⟨L, hA, hC⟩ := Postulate1 A C (ne_of_between_ends h₁)
  have hB : OnLine B L := on_line_of_between_ends h₁ hA hC
  have hD : OnLine D L := on_line_of_between h₂ hA hC
  have hBC : B ≠ C := (ne_of_between (between_symm h₁)).symm
  have hCD : C ≠ D := (ne_of_between (between_symm h₂)).symm
  have hBD : B ≠ D := by
    rintro rfl
    exact not_between_of_between (between_symm h₂) (between_symm h₁)
  /- Of the three points B, C, D one is between the other two; only C can be. -/
  rcases between_cases hBC hCD hBD hB hC hD with h | h | h
  · exact h
  · exact absurd (between_of_between_left (between_symm h₂) (between_symm h))
      (not_between_of_between_between h (between_symm h₁))
  · exact absurd (between_of_between_left (between_symm h₁) (between_symm h))
      (not_between_of_between (between_symm h₂))

/-- A finite straight line `AB` can be produced beyond `B`. [Post. 1, Post. 2] -/
theorem produce (h : A ≠ B) : ∃ C : Point, Between A B C := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B h
  obtain ⟨C, -, hC, -⟩ := Postulate2 hA hB h []
  exact ⟨C, hC⟩

end Elements
