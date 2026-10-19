import Elements.Foundations.Tacit.Transfer
import Elements.Foundations.Phrases

/-!
# Book Zero: sums of magnitudes, and points in order

II.1 cuts a straight line "into any number of segments whatever", and I.45 and II.14 take a
figure of any number of triangles. Lean says "any number" with a list, in words of the
foundations: the sum of a list of magnitudes (`Magnitude.sum`), points in order along one
straight line (`InOrder`), the segments between them (`segments`) and the last of them
(`endOf`). These are facts about those words that any figure of many pieces may use, each
proved from the laws of magnitudes or from one rule of order, Between 5: the sum of one
magnitude is that magnitude; the sum of two lists, one after the other, is the sum of the
first and the sum of the second; and, of three or more points in order, the second lies
between the first and the last, which II.1's companion for any number of segments uses to
cut off one segment at a time.

Nothing in Book Zero cites a proposition of the *Elements*.
-/

namespace Elements

open Tacit

/-! ## Sums of magnitudes -/

/-- The sum of one magnitude is that magnitude. -/
theorem Magnitude.sum_singleton {k : Kind} (a : Magnitude k) : Magnitude.sum [a] = a := by
  change a + 0 = a
  exact add_zero a

/-- The sum of two lists, one after the other, is the sum of the first added to the sum of
the second. -/
theorem Magnitude.sum_append {k : Kind} (l₁ l₂ : List (Magnitude k)) :
    Magnitude.sum (l₁ ++ l₂) = Magnitude.sum l₁ + Magnitude.sum l₂ := by
  induction l₁ with
  | nil =>
      /- Nothing added to a magnitude: the laws give `a + 0 = a`, so turn the sum round. -/
      change Magnitude.sum l₂ = 0 + Magnitude.sum l₂
      rw [add_comm 0, add_zero]
  | cons a as ih =>
      /- A first magnitude `a`: the induction, then the law for adding three in a row. -/
      change a + Magnitude.sum (as ++ l₂) = (a + Magnitude.sum as) + Magnitude.sum l₂
      rw [ih, add_assoc]

/-! ## Points in order on a straight line -/

/-- Of three or more points in order, the second lies between the first and the last. -/
theorem InOrder.between_end {B P : Point} {ps : List Point} (h : InOrder (B :: P :: ps))
    (hps : ps ≠ []) : Between B P (endOf P ps) := by
  induction ps generalizing B P with
  | nil =>
      /- No point after P: `hps` rules this case out. -/
      exact absurd rfl hps
  | cons Q qs ih =>
      cases qs with
      | nil =>
          /- Three points B, P, Q: the last is Q, and P is between B and Q. -/
          exact h.2.1
      | cons R rest =>
          /- P is between B and Q; by the induction, Q is between P and the last point E;
          so, by Between 5, P is between B and E. -/
          have hQE : Between P Q (endOf Q (R :: rest)) := ih h.2.2 (List.cons_ne_nil R rest)
          exact between_of_between_right h.2.1 hQE

end Elements
