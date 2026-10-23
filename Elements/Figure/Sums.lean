import Elements.Foundations.Tacit.Transfer
import Elements.Figure.Incidence
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

The last section is step A1 of brief 0013's route (section 8), for its content theorem: a
sum does not depend on the order of its terms, a sum of sums may be taken all at once, terms
that are nothing may be left out, terms that are all nothing sum to nothing, and a table of
magnitudes has one total, by rows or by columns (`sum_exchange`, which the content theorem
uses). With them is one fact of order that the enclosing triangle of brief 0013 uses: a
magnitude less than a second, which is not greater than a third, is less than the third. They
use only the laws of magnitudes. Facts about lists alone, and sums of natural numbers, are
in `Lists.lean`.

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
      /- No point after P: there is one by hypothesis, so this case does not arise. -/
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

/-! ## Sums in any order

For brief 0013's content theorem (step A1 of its route): a sum does not depend on the order
of its terms, a sum of sums may be taken all at once, and a table of magnitudes has one
total, by rows or by columns. They use only the laws of `Tacit/Magnitudes.lean`, as does the
fact of order at the end, for brief 0013's enclosing triangle. -/

namespace Elements.Figures

open Tacit

/-- A sum does not depend on the order of its terms. -/
theorem sum_perm {k : Kind} {xs ys : List (Magnitude k)} (h : xs.Perm ys) :
    Magnitude.sum xs = Magnitude.sum ys := by
  induction h with
  | nil => rfl
  | cons a h ih => exact congrArg (fun s => a + s) ih
  | swap a b xs =>
      change b + (a + Magnitude.sum xs) = a + (b + Magnitude.sum xs)
      rw [← add_assoc, add_comm b a, add_assoc]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The sum of a list of lists, taken all at once, is the sum of their sums. -/
theorem sum_flatMap {α : Type} {k : Kind} (xs : List α) (f : α → List (Magnitude k)) :
    Magnitude.sum (xs.flatMap f) = Magnitude.sum (xs.map fun x => Magnitude.sum (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change Magnitude.sum (f x ++ xs.flatMap f) =
        Magnitude.sum (f x) + Magnitude.sum (xs.map fun x => Magnitude.sum (f x))
      rw [Magnitude.sum_append, ih]

/-- Adding two terms at each place and then summing gives the sum of the two totals. -/
theorem sum_map_add {α : Type} {k : Kind} (xs : List α)
    (f g : α → Magnitude k) :
    Magnitude.sum (xs.map fun x => f x + g x) =
      Magnitude.sum (xs.map f) + Magnitude.sum (xs.map g) := by
  induction xs with
  | nil => exact (add_zero 0).symm
  | cons x xs ih =>
      change (f x + g x) + Magnitude.sum (xs.map fun x => f x + g x) =
        (f x + Magnitude.sum (xs.map f)) + (g x + Magnitude.sum (xs.map g))
      rw [ih, add_assoc, ← add_assoc (g x), add_comm (g x) (Magnitude.sum (xs.map f)),
        add_assoc, ← add_assoc]

/-- **A table has one total**: the sum of its rows' sums is the sum of its columns' sums. -/
theorem sum_exchange {α β : Type} {k : Kind} (xs : List α) (ys : List β)
    (f : α → β → Magnitude k) :
    Magnitude.sum (xs.map fun x => Magnitude.sum (ys.map (f x))) =
      Magnitude.sum (ys.map fun y => Magnitude.sum (xs.map fun x => f x y)) := by
  induction xs with
  | nil =>
      change 0 = Magnitude.sum (ys.map fun _ => (0 : Magnitude k))
      induction ys with
      | nil => rfl
      | cons y ys ih =>
          change 0 = 0 + Magnitude.sum (ys.map fun _ => (0 : Magnitude k))
          rw [← ih, add_zero]
  | cons x xs ih =>
      change Magnitude.sum (ys.map (f x)) +
          Magnitude.sum (xs.map fun x => Magnitude.sum (ys.map (f x))) =
        Magnitude.sum (ys.map fun y => f x y + Magnitude.sum (xs.map fun x => f x y))
      rw [sum_map_add, ih]

/-- Terms that are nothing may be left out of a sum. -/
theorem sum_filter_ne_zero {α : Type} {k : Kind} (xs : List α) (f : α → Magnitude k)
    (p : α → Bool) (h : ∀ x ∈ xs, p x = false → f x = 0) :
    Magnitude.sum ((xs.filter p).map f) = Magnitude.sum (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have ht : ∀ y ∈ xs, p y = false → f y = 0 :=
        fun y hy => h y (List.mem_cons_of_mem x hy)
      cases hp : p x with
      | false =>
          have hx : f x = 0 := h x (List.mem_cons_self) hp
          simp only [List.filter_cons, hp, List.map_cons, Bool.false_eq_true, ↓reduceIte]
          change Magnitude.sum ((xs.filter p).map f) = f x + Magnitude.sum (xs.map f)
          rw [ih ht, hx, add_comm 0, add_zero]
      | true =>
          simp only [List.filter_cons, hp, List.map_cons, ↓reduceIte]
          exact congrArg (fun s => f x + s) (ih ht)

/-- A sum whose terms are all nothing is nothing. -/
theorem sum_eq_zero {α : Type} {k : Kind} (l : List α) (f : α → Magnitude k)
    (h : ∀ a ∈ l, f a = 0) : Magnitude.sum (l.map f) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change f a + Magnitude.sum (l.map f) = 0
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem a hb)), add_zero]

/-! ## Less, then not greater -/

/-- Less, then not greater: less. -/
theorem mag_lt_of_lt_of_le {k : Kind} {a b c : Magnitude k} (h₁ : a < b) (h₂ : b ≤ c) :
    a < c := by
  rcases Tacit.lt_trichotomy a c with h | rfl | h
  · exact h
  · exact absurd h₁ h₂
  · exact absurd (Tacit.lt_trans h h₁) h₂

end Elements.Figures
