import Elements.Figure.Lines

/-!
# Book Zero: triangles

"Let ABC be a triangle": three points not on one straight line (Definition 19).
Euclid names a triangle from whichever corner suits him, and never doubts that
its corners are three different points, or that each corner is off the straight
line through the other two. Nor does he doubt that two points of a straight line
and a third point off it make a triangle. These are those facts.
-/

namespace Elements

open Tacit

variable {A B C : Point} {L : Line}

/-! ## The corners -/

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

/-! ## Naming a triangle from another corner

Three points that are not on one straight line stay so, in whatever order we
name them. -/

/-- The triangle `ABC`, named from `B`, as `BCA`. -/
theorem Triangle.bca (h : Triangle A B C) : Triangle B C A := by
  rintro ⟨L, hB, hC, hA⟩
  exact h ⟨L, hA, hB, hC⟩

/-- The triangle `ABC`, named from `C`, as `CAB`. -/
theorem Triangle.cab (h : Triangle A B C) : Triangle C A B := by
  rintro ⟨L, hC, hA, hB⟩
  exact h ⟨L, hA, hB, hC⟩

/-- The triangle `ABC`, named the other way round, as `ACB`. -/
theorem Triangle.acb (h : Triangle A B C) : Triangle A C B := by
  rintro ⟨L, hA, hC, hB⟩
  exact h ⟨L, hA, hB, hC⟩

/-- The triangle `ABC`, named the other way round, as `BAC`. -/
theorem Triangle.bac (h : Triangle A B C) : Triangle B A C := by
  rintro ⟨L, hB, hA, hC⟩
  exact h ⟨L, hA, hB, hC⟩

/-- The triangle `ABC`, named the other way round, as `CBA`. -/
theorem Triangle.cba (h : Triangle A B C) : Triangle C B A := by
  rintro ⟨L, hC, hB, hA⟩
  exact h ⟨L, hA, hB, hC⟩

/-! ## Triangles and straight lines -/

/-- In the triangle `ABC`, the corner `C` is off every straight line through `A`
and `B`. -/
theorem Triangle.off_line (h : Triangle A B C) (hA : OnLine A L) (hB : OnLine B L) :
    ¬ OnLine C L :=
  fun hC => h ⟨L, hA, hB, hC⟩

/-- Two different points of a straight line, and a third point off it, make a
triangle. -/
theorem Triangle.of_line {P Q R : Point} (hP : OnLine P L) (hQ : OnLine Q L) (hPQ : P ≠ Q)
    (hR : ¬ OnLine R L) : Triangle P Q R := by
  rintro ⟨M, hPM, hQM, hRM⟩
  exact hR (line_unique hPQ hPM hQM hP hQ ▸ hRM)

end Elements
