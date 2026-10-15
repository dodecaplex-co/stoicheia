import Elements.Foundations.Tacit.Magnitudes

/-!
# The Common Notions

> 1. Things which are equal to the same thing are also equal to one another.
> 2. If equals be added to equals, the wholes are equal.
> 3. If equals be subtracted from equals, the remainders are equal.
> 4. Things which coincide with one another are equal to one another.
> 5. The whole is greater than the part.

In Lean all five are *theorems*. The first, second and fourth are laws of logic
(Lean's equality already behaves this way), and the third and fifth follow from
the tacit laws of magnitudes. We still give each one its own name, so that a
proof can cite "C.N. 1" exactly where Euclid does, and the certificate can show
which Common Notions each proposition uses.
-/

namespace Elements

open Tacit

variable {k : Kind}

/-- **Common Notion 1.** Things which are equal to the same thing are also equal
to one another. -/
theorem CommonNotion1 {α : Sort _} {a b c : α} (h₁ : a = c) (h₂ : b = c) : a = b :=
  h₁.trans h₂.symm

/-- **Common Notion 2.** If equals be added to equals, the wholes are equal. -/
theorem CommonNotion2 {a b c d : Magnitude k} (h₁ : a = b) (h₂ : c = d) :
    a + c = b + d := by
  rw [h₁, h₂]

/-- **Common Notion 3.** If equals be subtracted from equals, the remainders
are equal. (From `a + c = b + d` and `c = d`, conclude `a = b`.) -/
theorem CommonNotion3 {a b c d : Magnitude k} (h₁ : a + c = b + d) (h₂ : c = d) :
    a = b := by
  subst h₂
  rcases lt_trichotomy a b with h | h | h
  · have := add_lt_add_right c h
    rw [h₁] at this
    exact absurd this (lt_irrefl _)
  · exact h
  · have := add_lt_add_right c h
    rw [h₁] at this
    exact absurd this (lt_irrefl _)

/-- **Common Notion 4.** Things which coincide with one another are equal to one
another: if the ends of two finite straight lines coincide, so do the lines. -/
theorem CommonNotion4 {A B C D : Point} (hA : A = C) (hB : B = D) : ‖A B‖ = ‖C D‖ := by
  subst hA; subst hB; rfl

/-- **Common Notion 4**, for angles. -/
theorem CommonNotion4.angle {A B C D E F : Point} (hA : A = D) (hB : B = E) (hC : C = F) :
    ∠ A B C = ∠ D E F := by
  subst hA; subst hB; subst hC; rfl

/-- **Common Notion 4**, for triangles. -/
theorem CommonNotion4.triangle {A B C D E F : Point} (hA : A = D) (hB : B = E) (hC : C = F) :
    △ A B C = △ D E F := by
  subst hA; subst hB; subst hC; rfl

/-- **Common Notion 5.** The whole is greater than the part: if `b` is something
(not nothing), then `a + b` is greater than `a`. -/
theorem CommonNotion5 {a b : Magnitude k} (h : 0 < b) : a < a + b := by
  have := add_lt_add_right a h
  rw [add_comm 0 a, add_zero, add_comm b a] at this
  exact this

end Elements
