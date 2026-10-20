import Elements.Figure.Sums

/-!
# Staging: finite sums of magnitudes, in any order

Statements for brief 0013's content theorem (a draft for the owner's approval), with `sorry`
where a proof is due: a sum does not depend on the order of its terms, a sum of sums may be
taken all at once, and a table of magnitudes has one total, by rows or by columns. They use
only the laws of Tacit/Magnitudes.lean.
-/

namespace Elements.Figures

open Tacit

/-- A sum does not depend on the order of its terms. -/
theorem sum_perm {k : Kind} {xs ys : List (Magnitude k)} (h : xs.Perm ys) :
    Magnitude.sum xs = Magnitude.sum ys := by
  sorry

/-- The sum of a list of lists, taken all at once, is the sum of their sums. -/
theorem sum_flatMap {α : Type} {k : Kind} (xs : List α) (f : α → List (Magnitude k)) :
    Magnitude.sum (xs.flatMap f) = Magnitude.sum (xs.map fun x => Magnitude.sum (f x)) := by
  sorry

/-- **A table has one total**: the sum of its rows' sums is the sum of its columns' sums. -/
theorem sum_exchange {α β : Type} {k : Kind} (xs : List α) (ys : List β)
    (f : α → β → Magnitude k) :
    Magnitude.sum (xs.map fun x => Magnitude.sum (ys.map (f x))) =
      Magnitude.sum (ys.map fun y => Magnitude.sum (xs.map fun x => f x y)) := by
  sorry

/-- Terms that are nothing may be left out of a sum. -/
theorem sum_filter_ne_zero {α : Type} {k : Kind} (xs : List α) (f : α → Magnitude k)
    (p : α → Bool) (h : ∀ x ∈ xs, p x = false → f x = 0) :
    Magnitude.sum ((xs.filter p).map f) = Magnitude.sum (xs.map f) := by
  sorry

end Elements.Figures
