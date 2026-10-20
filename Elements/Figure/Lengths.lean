import Elements.Foundations.Tacit.Transfer
import Elements.Figure.RuleBase
import Elements.Foundations.Phrases

/-!
# Book Zero: lengths

Euclid compares lengths on every page and never stops to say the obvious: that a
finite straight line with two different ends has some length, that something
added makes a thing greater, that the part is less than the whole. These are
those facts, proved once from the laws of magnitudes
(`Foundations/Tacit/Magnitudes.lean`), the Common Notions, and System E's rules
for segments.

Nothing in Book Zero cites a proposition of the *Elements*.
-/

namespace Elements

open Tacit

variable {A B C D : Point}

/-! ## Magnitudes -/

/-- A magnitude that is something is more than nothing. -/
theorem Magnitude.pos_of_ne_zero {k : Kind} {a : Magnitude k} (h : a ≠ 0) : 0 < a := by
  rcases lt_trichotomy 0 a with h₁ | h₁ | h₁
  · exact h₁
  · exact absurd h₁.symm h
  · exact absurd h₁ (not_lt_zero a)

/-- If `a` is something, then `a` and `a` together are not equal to `a`: they are
more (C.N. 5). -/
theorem Magnitude.add_self_ne {k : Kind} {a : Magnitude k} (h : a ≠ 0) : a + a ≠ a := by
  intro h'
  have := CommonNotion5 (a := a) (Magnitude.pos_of_ne_zero h)
  rw [h'] at this
  exact lt_irrefl a this

/-- Unequal magnitudes, if one is less. -/
theorem Magnitude.ne_of_lt {k : Kind} {a b : Magnitude k} (h : a < b) : a ≠ b := by
  intro e
  rw [e] at h
  exact lt_irrefl _ h

/-- Take the same thing away from two unequal magnitudes, and the less remains the
less: if `x` and `a` together are less than `y` and `a` together, then `x` is less
than `y`. Otherwise `y` would be equal to `x` or less, and adding `a` to each would
keep it so (the laws of magnitudes, System E §3.5). -/
theorem Magnitude.lt_of_add_lt_add_right {k : Kind} {a x y : Magnitude k} (h : x + a < y + a) :
    x < y := by
  rcases lt_trichotomy x y with h' | h' | h'
  · exact h'
  · subst h'
    exact absurd h (lt_irrefl _)
  · exact absurd (lt_trans h (add_lt_add_right a h')) (lt_irrefl _)

/-- The same, with the common part first: if `a` and `b` together are less than `a`
and `c` together, then `b` is less than `c`. -/
theorem Magnitude.lt_of_add_lt_add_left {k : Kind} {a b c : Magnitude k} (h : a + b < a + c) :
    b < c := by
  rw [add_comm a b, add_comm a c] at h
  exact Magnitude.lt_of_add_lt_add_right h

/-! ## Lengths -/

/-- A finite straight line with different ends has some length. -/
theorem len_ne_zero (h : A ≠ B) : ‖A B‖ ≠ 0 := fun h' => h (eq_of_len_eq_zero h')

/-- A finite straight line with different ends has some length. -/
theorem len_pos (h : A ≠ B) : 0 < ‖A B‖ := Magnitude.pos_of_ne_zero (len_ne_zero h)

/-- If a finite straight line AB has the length of one with different ends,
its own ends are different. -/
theorem ne_of_len_eq (h : ‖A B‖ = ‖C D‖) (hCD : C ≠ D) : A ≠ B := by
  intro e
  subst e
  rw [len_self] at h
  exact len_ne_zero hCD h.symm

/-- If AB is longer than something, its ends are different. -/
theorem ne_of_len_gt {x : Length} (h : x < ‖A B‖) : A ≠ B := by
  intro e
  subst e
  rw [len_self] at h
  exact not_lt_zero x h

/-- The part is less than the whole: if B lies between A and C, then AB is
less than AC, for AC is AB and BC together. (System E, Diagram-segment 1,
and C.N. 5) -/
theorem len_lt_of_between (h : Between A B C) : ‖A B‖ < ‖A C‖ := by
  rw [← len_add_of_between h]
  exact CommonNotion5 (len_pos (ne_of_between (between_symm h)).symm)

end Elements
