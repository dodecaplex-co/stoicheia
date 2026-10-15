import Elements.Figure.Lines

/-!
# Book Zero: rays

"The straight line DE, terminated at D but of infinite length in the direction
of E": often Euclid needs not a whole straight line but the half of it that
starts at a point and runs one way. In Lean that is `OnRay P A B`: the point `P`
lies on the straight line from `A` through `B`, on `B`'s side of `A`.

Euclid takes for granted that a point between `A` and `B`, or beyond `B`, lies on
that ray; that two points of one ray are never on opposite sides of its start;
and that on a ray only one point lies at a given distance from its start, so
that a point "laid along" the ray at the right distance "coincides" with the
point already there. These are those facts.
-/

namespace Elements

open Tacit

variable {A B P Q : Point} {L : Line}

/-- `B` itself is on the ray from `A` through `B`. -/
theorem OnRay.self (h : A ≠ B) : OnRay B A B := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B h
  exact ⟨h, h.symm, ⟨L, hA, hB, hB⟩, fun hb => ne_of_between_ends hb rfl⟩

/-- A point between `A` and `B` is on the ray from `A` through `B`. -/
theorem OnRay.of_between (h : Between A P B) : OnRay P A B := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B (ne_of_between_ends h)
  exact ⟨ne_of_between_ends h, (ne_of_between h).symm,
    ⟨L, hA, hB, on_line_of_between_ends h hA hB⟩, not_between_of_between h⟩

/-- A point beyond `B`, on the straight line from `A` through `B` produced, is on
the ray from `A` through `B`. -/
theorem OnRay.of_beyond (h : Between A B P) : OnRay P A B := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B (ne_of_between h)
  exact ⟨ne_of_between h, (ne_of_between_ends h).symm, ⟨L, hA, hB, on_line_of_between h hA hB⟩,
    fun hb => not_between_of_between h (between_symm hb)⟩

/-- `P` is on the ray from `A` through `B` exactly when `B` is on the ray from `A`
through `P`: they are one and the same ray. -/
theorem OnRay.symm (h : OnRay P A B) : OnRay B A P := by
  obtain ⟨hAB, hPA, ⟨L, hA, hB, hP⟩, hn⟩ := h
  exact ⟨hPA.symm, hAB.symm, ⟨L, hA, hP, hB⟩, fun hb => hn (between_symm hb)⟩

/-- Every straight line through `A` and `B` passes through each point of the ray
from `A` through `B`. -/
theorem OnRay.onLine (h : OnRay P A B) (hA : OnLine A L) (hB : OnLine B L) : OnLine P L := by
  obtain ⟨hAB, -, ⟨M, hAM, hBM, hPM⟩, -⟩ := h
  rw [line_unique hAB hA hB hAM hBM]
  exact hPM

/-- Two points of one ray are never on opposite sides of its start: `A` does not
lie between them. -/
theorem OnRay.not_between (hP : OnRay P A B) (hQ : OnRay Q A B) : ¬ Between P A Q := by
  intro hPAQ
  obtain ⟨hAB, hPA, ⟨L, hA, hB, hPL⟩, hP'⟩ := hP
  obtain ⟨-, -, -, hQ'⟩ := hQ
  by_cases hPB : P = B
  · subst hPB
    exact hQ' (between_symm hPAQ)
  by_cases hQB : Q = B
  · subst hQB
    exact hP' hPAQ
  /- Of the three points P, A, B one is between the other two. A can't be; and
     if P or B is, then A lies between Q and B. -/
  rcases between_cases hPA hAB hPB hPL hA hB with h | h | h
  · exact hP' h
  · exact hQ' (between_of_between_right (between_symm hPAQ) h)
  · exact hQ' (between_symm (between_inner h hPAQ))

/-- Of two points on a ray, the one nearer the start lies between the start and
the other. -/
theorem OnRay.between_of_len_lt (hP : OnRay P A B) (hQ : OnRay Q A B) (h : ‖A P‖ < ‖A Q‖) :
    Between A P Q := by
  have hPQ : P ≠ Q := by
    rintro rfl
    exact lt_irrefl _ h
  obtain ⟨L, hA, hB, hPL⟩ := hP.2.2.1
  have hQL : OnLine Q L := hQ.onLine hA hB
  rcases between_cases hP.2.1.symm hPQ hQ.2.1.symm hA hPL hQL with h' | h' | h'
  · exact h'
  · exact absurd h' (hP.not_between hQ)
  · /- Q between A and P: then AQ would be only a part of AP. -/
    exact absurd (lt_trans h (len_lt_of_between h')) (lt_irrefl _)

/-- On a ray, only one point lies at a given distance from its start: a point `P`
on the ray from `A` through `B`, as far from `A` as `B` is, is `B` itself.

This is Sir Henry Savile's argument, which Heath reports on I.4 (vol. 1,
p. 250): otherwise `P` falls short of `B` or beyond it, and either way the less
would be equal to the greater. -/
theorem OnRay.eq_of_len_eq (hP : OnRay P A B) (h : ‖A P‖ = ‖A B‖) : P = B := by
  obtain ⟨hAB, hPA, ⟨L, hA, hB, hPL⟩, hPAB⟩ := hP
  refine Classical.byContradiction fun (hPB : P ≠ B) => ?_
  rcases between_cases hPA.symm hPB hAB hA hPL hB with h' | h' | h'
  · /- `P` falls short of `B`: then `AB` is `AP` and `PB` together, and so
       greater than `AP`, which is equal to it. -/
    have hsum : ‖A P‖ + ‖P B‖ = ‖A P‖ := (len_add_of_between h').trans h.symm
    have hlt := CommonNotion5 (a := ‖A P‖) (len_pos hPB)
    rw [hsum] at hlt
    exact lt_irrefl _ hlt
  · /- `P` is on the far side of `A`, off the ray altogether. -/
    exact hPAB h'
  · /- `P` falls beyond `B`: then `AP` is `AB` and `BP` together, and so
       greater than `AB`, which is equal to it. -/
    have hsum : ‖A B‖ + ‖B P‖ = ‖A B‖ := (len_add_of_between h').trans h
    have hlt := CommonNotion5 (a := ‖A B‖) (len_pos hPB.symm)
    rw [hsum] at hlt
    exact lt_irrefl _ hlt

end Elements
