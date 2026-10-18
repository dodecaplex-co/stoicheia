import Elements.Figure.Basics
import Elements.BookI.Prop20

/-!
# Stage 3, staged: I.20's degenerate case

Statements frozen before their proofs (brief 0006, stage 3), and proved here. These are
shared steps that cite I.20, so they go in a Book I helper file at or after I.20.
`Elements/BookI/Helpers.lean` imports only I.5 and is imported by I.7, so it cannot take
them without a cycle: they go to a new helper file, `Elements/BookI/HelpersTriangles.lean`,
after I.20 and citing nothing later.
It has one owner, named in the orders of the wave that adds it (brief 0006).

This is the one statement of `Prop20.collinear_iff` in Staging: placement uses it, and
stage 4's `Prop14.general` and `Prop15.le_diameter` will cite it too. (Stage 2's draft had a
second copy, with the distances in another order; it was removed when the two were merged.)

`placement` uses them to carry "on the straight line AB" and "between A and B" across: both
are decided by the three distances alone.
-/

namespace Elements.BookI

open Tacit

/-- **I.20's degenerate case.** Three points lie on one straight line exactly when one of the
three distances between them is the other two together: when the triangle "collapses", I.20's
"greater" becomes "equal". (The points may coincide; then the equality holds trivially.)

Proved from I.20 for three points off one straight line, and from `between_cases` and
`len_add_of_between` (Transfer, Diagram-segment 1) for three on one. -/
theorem Prop20.collinear_iff {A B P : Point} :
    Collinear A B P ↔
      ‖A B‖ = ‖A P‖ + ‖P B‖ ∨ ‖A P‖ = ‖A B‖ + ‖B P‖ ∨ ‖B P‖ = ‖B A‖ + ‖A P‖ := by
  constructor
  · intro hcol
    /- If two points coincide, one length is nothing and another is unchanged. -/
    by_cases hAB : A = B
    · subst B
      right; left
      rw [len_self, add_comm (0 : Length), add_zero]
    by_cases hAP : A = P
    · subst P
      left
      rw [len_self, add_comm (0 : Length), add_zero]
    by_cases hBP : B = P
    · subst P
      left
      rw [len_self, add_zero]
    /- The three different points share a straight line, so one is between the others. -/
    obtain ⟨L, hA, hB, hP⟩ := hcol
    rcases between_cases hAB hBP hAP hA hB hP with hABP | hBAP | hAPB
    · /- With B between A and P, AB and BP make AP. -/
      exact Or.inr (Or.inl (len_add_of_between hABP).symm)
    · /- With A between B and P, BA and AP make BP. -/
      exact Or.inr (Or.inr (len_add_of_between hBAP).symm)
    · /- With P between A and B, AP and PB make AB. -/
      exact Or.inl (len_add_of_between hAPB).symm
  · intro hsum
    /- Off one straight line, the points make a triangle and I.20 gives strict inequalities. -/
    apply Classical.byContradiction
    intro hoff
    have htriangle : Triangle A B P := hoff
    obtain ⟨hBP, hAP, hAB⟩ := Prop20 htriangle
    rcases hsum with hsum | hsum | hsum
    · /- AP and PB are greater than AB, so they cannot equal it. -/
      have hAB_lt : ‖A B‖ < ‖A P‖ + ‖P B‖ := by
        rw [len_symm A P, len_symm P B, add_comm]
        exact hAB
      exact Magnitude.ne_of_lt hAB_lt hsum
    · /- AB and BP are greater than AP. -/
      exact Magnitude.ne_of_lt hAP hsum
    · /- BA and AP are greater than BP. -/
      exact Magnitude.ne_of_lt hBP hsum

/-- **Collinearity carried across.** If `AB`, `AP`, `BP` are equal to `CD`, `CQ`, `DQ`, then
`P` is on the straight line `AB` exactly when `Q` is on the straight line `CD`. Proved from
`Prop20.collinear_iff`. -/
theorem Prop20.collinear_congr {A B P C D Q : Point} (hAB : ‖A B‖ = ‖C D‖)
    (hAP : ‖A P‖ = ‖C Q‖) (hBP : ‖B P‖ = ‖D Q‖) : Collinear A B P ↔ Collinear C D Q := by
  rw [Prop20.collinear_iff, Prop20.collinear_iff, hAB, hAP, len_symm P B, hBP, len_symm B A,
    hAB, len_symm Q D, len_symm D C]

/-- **Between, by distances.** `P` lies between `A` and `B` exactly when it is neither end
and `AP`, `PB` together make `AB`. Proved from `len_add_of_between` one way, and the other
way from `Prop20.collinear_iff` and `between_cases`, the other two orders making something
nothing. -/
theorem Prop20.between_iff {A B P : Point} :
    Between A P B ↔ ‖A P‖ ≠ 0 ∧ ‖P B‖ ≠ 0 ∧ ‖A P‖ + ‖P B‖ = ‖A B‖ := by
  constructor
  · intro hAPB
    /- P differs from both ends, and the two parts together make the whole. -/
    have hAP : A ≠ P := ne_of_between hAPB
    have hPB : P ≠ B := (ne_of_between (between_symm hAPB)).symm
    exact ⟨len_ne_zero hAP, len_ne_zero hPB, len_add_of_between hAPB⟩
  · rintro ⟨hAP0, hPB0, hsum⟩
    /- Neither part is nothing, so P is neither end. -/
    have hAP : A ≠ P := by
      intro hAP
      subst P
      exact hAP0 (len_self A)
    have hPB : P ≠ B := by
      intro hPB
      subst B
      exact hPB0 (len_self P)
    /- If A were B, the sum would be nothing, though greater than AP by C.N. 5. -/
    have hAB : A ≠ B := by
      intro hAB
      subst B
      have hAP_lt : ‖A P‖ < ‖A P‖ + ‖P A‖ :=
        CommonNotion5 (Magnitude.pos_of_ne_zero hPB0)
      rw [hsum, len_self] at hAP_lt
      exact not_lt_zero _ hAP_lt
    /- The given sum puts the points on one straight line. It remains to find their order. -/
    have hcol : Collinear A B P := Prop20.collinear_iff.mpr (Or.inl hsum.symm)
    obtain ⟨L, hA, hB, hP⟩ := hcol
    rcases between_cases hAP hPB hAB hA hP hB with hAPB | hPAB | hABP
    · exact hAPB
    · /- If A were between P and B, PA and AB would make PB, so AP, PA and AB together
         would make AB; removing AB would leave AP and PA together equal to nothing
         (C.N. 3). But together they are greater than AP (C.N. 5). -/
      have hPB_sum : ‖P A‖ + ‖A B‖ = ‖P B‖ := len_add_of_between hPAB
      have hzero : ‖A P‖ + ‖P A‖ = 0 := by
        apply CommonNotion3 (c := ‖A B‖) (d := ‖A B‖) ?_ rfl
        calc
          (‖A P‖ + ‖P A‖) + ‖A B‖ = ‖A P‖ + (‖P A‖ + ‖A B‖) := add_assoc _ _ _
          _ = ‖A B‖ := by rw [hPB_sum, hsum]
          _ = 0 + ‖A B‖ := by rw [add_comm, add_zero]
      have hAP_lt : ‖A P‖ < ‖A P‖ + ‖P A‖ := CommonNotion5 (len_pos hAP.symm)
      rw [hzero] at hAP_lt
      exact False.elim (not_lt_zero _ hAP_lt)
    · /- If B were between A and P, AB and BP would make AP, so BP, PB and AB together
         would make AB; removing AB would leave BP and PB together equal to nothing
         (C.N. 3). But together they are greater than BP (C.N. 5). -/
      have hAP_sum : ‖A B‖ + ‖B P‖ = ‖A P‖ := len_add_of_between hABP
      have hzero : ‖B P‖ + ‖P B‖ = 0 := by
        apply CommonNotion3 (c := ‖A B‖) (d := ‖A B‖) ?_ rfl
        calc
          (‖B P‖ + ‖P B‖) + ‖A B‖ = (‖A B‖ + ‖B P‖) + ‖P B‖ := by
            rw [add_comm (‖B P‖ + ‖P B‖) ‖A B‖, ← add_assoc]
          _ = ‖A B‖ := by rw [hAP_sum, hsum]
          _ = 0 + ‖A B‖ := by rw [add_comm, add_zero]
      have hBP_lt : ‖B P‖ < ‖B P‖ + ‖P B‖ :=
        CommonNotion5 (Magnitude.pos_of_ne_zero hPB0)
      rw [hzero] at hBP_lt
      exact False.elim (not_lt_zero _ hBP_lt)

/-- **Between carried across.** If `AB`, `AP`, `BP` are equal to `CD`, `CQ`, `DQ`, then `P`
is between `A` and `B` exactly when `Q` is between `C` and `D`. Proved from
`Prop20.between_iff`. -/
theorem Prop20.between_congr {A B P C D Q : Point} (hAB : ‖A B‖ = ‖C D‖)
    (hAP : ‖A P‖ = ‖C Q‖) (hBP : ‖B P‖ = ‖D Q‖) : Between A P B ↔ Between C Q D := by
  rw [Prop20.between_iff, Prop20.between_iff, hAB, hAP, len_symm P B, hBP, len_symm Q D]

end Elements.BookI
