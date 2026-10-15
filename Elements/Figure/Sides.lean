import Elements.Figure.Triangles

/-!
# Book Zero: the sides of a straight line

"On the same side of AB", "on the other side of the straight line AB": Euclid
uses these phrases freely and reads from his figure which side a point is on.

Lean has two ways of saying them. `SameSide P Q L` speaks of a straight line `L`
that has been drawn and named; `SameSideOf P Q A B` (from
`Foundations/Phrases.lean`) speaks, as Euclid does, of "the straight line AB".
Since two points fix one straight line (System E, Generalities 1), these say the
same thing, and the lemmas here pass between them. They also record what
Euclid never doubts: that "the same side of AB" is "the same side of BA", that
if `P` is on `Q`'s side then `Q` is on `P`'s, and that a point on either side of
`AB` is off it.
-/

namespace Elements

open Tacit

variable {A B P Q R : Point} {L : Line}

/-! ## The same side -/

/-- Two points on the same side of a straight line `L` through `A` and `B` are on
the same side of the straight line `AB`, however that line is named: two points
fix one straight line. -/
theorem SameSideOf.of_line (hAB : A ≠ B) (hA : OnLine A L) (hB : OnLine B L)
    (h : SameSide P Q L) : SameSideOf P Q A B := by
  refine ⟨hAB, fun M hAM hBM => ?_⟩
  rw [← line_unique hAB hA hB hAM hBM]
  exact h

/-- Two points on the same side of the straight line `AB` are on the same side of
any straight line drawn through `A` and `B`. -/
theorem SameSideOf.sameSide (h : SameSideOf P Q A B) (hA : OnLine A L) (hB : OnLine B L) :
    SameSide P Q L :=
  h.2 L hA hB

/-- "On the same side of `AB`" is the same as "on the same side of `BA`". -/
theorem SameSideOf.swap (h : SameSideOf P Q A B) : SameSideOf P Q B A :=
  ⟨h.1.symm, fun L hB hA => h.2 L hA hB⟩

/-- If `P` is on the same side of `AB` as `Q`, then `Q` is on the same side as `P`. -/
theorem SameSideOf.symm (h : SameSideOf P Q A B) : SameSideOf Q P A B :=
  ⟨h.1, fun L hA hB => same_side_symm (h.2 L hA hB)⟩

/-- Points on the same side as a third are on the same side as each other. -/
theorem SameSideOf.trans (h₁ : SameSideOf P Q A B) (h₂ : SameSideOf Q R A B) :
    SameSideOf P R A B :=
  ⟨h₁.1, fun L hA hB => same_side_trans (same_side_symm (h₁.2 L hA hB)) (h₂.2 L hA hB)⟩

/-- A point on one side of the straight line `AB` is not on it, so `ABP` is a
triangle. -/
theorem SameSideOf.triangle (h : SameSideOf P Q A B) : Triangle A B P := by
  rintro ⟨L, hA, hB, hP⟩
  exact not_on_line_of_same_side (h.2 L hA hB) hP

/-! ## Opposite sides -/

/-- Two points on opposite sides of a straight line `L` through `A` and `B` are on
opposite sides of the straight line `AB`, however that line is named. -/
theorem OppositeSidesOf.of_line (hAB : A ≠ B) (hA : OnLine A L) (hB : OnLine B L)
    (h : OppositeSides P Q L) : OppositeSidesOf P Q A B := by
  refine ⟨hAB, fun M hAM hBM => ?_⟩
  rw [← line_unique hAB hA hB hAM hBM]
  exact h

/-- Two points on opposite sides of the straight line `AB` are on opposite sides of
any straight line drawn through `A` and `B`. -/
theorem OppositeSidesOf.oppositeSides (h : OppositeSidesOf P Q A B) (hA : OnLine A L)
    (hB : OnLine B L) : OppositeSides P Q L :=
  h.2 L hA hB

/-- "On opposite sides of `AB`" is the same as "on opposite sides of `BA`". -/
theorem OppositeSidesOf.swap (h : OppositeSidesOf P Q A B) : OppositeSidesOf P Q B A :=
  ⟨h.1.symm, fun L hB hA => h.2 L hA hB⟩

/-- If `P` is on the other side of `AB` from `Q`, then `Q` is on the other side
from `P`. -/
theorem OppositeSidesOf.symm (h : OppositeSidesOf P Q A B) : OppositeSidesOf Q P A B :=
  ⟨h.1, fun L hA hB =>
    ⟨(h.2 L hA hB).2.1, (h.2 L hA hB).1, fun hs => (h.2 L hA hB).2.2 (same_side_symm hs)⟩⟩

/-- A point on either side of the straight line `AB` is not on it, so `ABP` is a
triangle. -/
theorem OppositeSidesOf.triangle (h : OppositeSidesOf P Q A B) : Triangle A B P := by
  rintro ⟨L, hA, hB, hP⟩
  exact (h.2 L hA hB).1 hP

/-- "Let a point be taken at random on the other side of the straight line AB"
(I.12): if `P` is off the straight line `AB`, there is a point on the other side
of it from `P`, which may be chosen different from any points already in the
figure. (System E, Points 6) -/
theorem exists_oppositeSidesOf (hP : Triangle A B P) (avoid : List Point) :
    ∃ Q : Point, OppositeSidesOf Q P A B ∧ Q ∉ avoid := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B hP.ne₁₂
  obtain ⟨Q, hQ, hQa⟩ := exists_point_opposite_side (hP.off_line hA hB) avoid
  exact ⟨Q, OppositeSidesOf.of_line hP.ne₁₂ hA hB hQ, hQa⟩

end Elements
