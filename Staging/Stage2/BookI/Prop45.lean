import Staging.Stage2.Rectilineal

/-!
# Staging: I.45 for any rectilineal figure

Brief 0006, stage 2. Companions of `Elements.BookI.Prop45`, which stays as Euclid's worked
configuration, a figure of two triangles. His proof makes a parallelogram for the first
triangle [I. 42], applies one for the second to its side [I. 44], and shows the two make one
parallelogram; a figure of more triangles repeats the second step. `Prop45.append` is that
step, `Prop45.sum` its repetition over any number of triangles, and `Prop45.figure` the
proposition for any rectilineal figure (`Rectilineal`). They move into
`Elements/BookI/Prop45.lean` when proved, as "I.45 append", "I.45 sum" and "I.45 figure".
-/

namespace Elements.BookI

open Tacit

/-- **I.45, one more triangle** (companion of I.45). Given a parallelogram KFLM in the
given rectilineal angle E, and a triangle ABC, to construct a parallelogram in the same
angle equal to KFLM and ABC together: the second half of Euclid's proof, which applies a
parallelogram equal to the triangle to a side of the first [I. 44] and shows that the two
make one. -/
theorem Prop45.append {A B C K F L M E₁ E E₂ : Point} (hKFLM : Parallelogram K F L M)
    (hang : ∠ F K M = ∠ E₁ E E₂) (hABC : Triangle A B C) (hE : Triangle E₁ E E₂) :
    ∃ K' F' L' M' : Point, Parallelogram K' F' L' M' ∧ ∠ F' K' M' = ∠ E₁ E E₂ ∧
      quadArea K' F' L' M' = quadArea K F L M + △ A B C := by
  sorry

/-- **I.45, any number of triangles** (companion of I.45). To construct, in a given
rectilineal angle E, a parallelogram equal to any number of given triangles taken together:
I.42 for the first, then `Prop45.append` for each of the rest. The triangles are any
triangles; they need not fit together into one figure. -/
theorem Prop45.sum {E₁ E E₂ : Point} (ts : List (Point × Point × Point)) (hne : ts ≠ [])
    (hts : ∀ t ∈ ts, Triangle t.1 t.2.1 t.2.2) (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M = Magnitude.sum (ts.map fun t => △ t.1 t.2.1 t.2.2) := by
  sorry

/-- **I.45, for any rectilineal figure** (companion of I.45). To construct, in a given
rectilineal angle E, a parallelogram equal to a given rectilineal figure, given with the
triangles it is cut into. It is `Prop45.sum` for the figure's triangles. -/
theorem Prop45.figure {E₁ E E₂ : Point} (R : Rectilineal) (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M = R.area :=
  Prop45.sum R.pieces R.fitted.ne_nil R.fitted.triangle hE

/-- The check: today's statement of I.45, for the two triangles ABD, DBC, follows from
`Prop45.sum` for the list of those two (checked by Lean). -/
example : type_of% @Elements.BookI.Prop45 := by
  intro A B C D E₁ E E₂ hABD hDBC hE
  have hts : ∀ t ∈ [(A, B, D), (D, B, C)], Triangle t.1 t.2.1 t.2.2 := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hABD
    · exact hDBC
  obtain ⟨K, F, L, M, hp, hang, harea⟩ := Prop45.sum _ (List.cons_ne_nil _ _) hts hE
  refine ⟨K, F, L, M, hp, hang, ?_⟩
  rw [harea]
  simp only [List.map, Magnitude.sum, add_zero]

end Elements.BookI
