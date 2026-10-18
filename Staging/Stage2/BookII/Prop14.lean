import Staging.Stage2.BookI.Prop45

/-!
# Staging: II.14 for any rectilineal figure, with a drawn square

Brief 0006, stage 2. Companions of `Elements.BookII.Prop14`, which stays as Euclid's worked
configuration, a figure of two triangles, and returns the side of the square. His proof
makes a rectangle equal to the figure [I. 45] and then a square equal to the rectangle.
`Prop14.rectangle` is that second part, `Prop14.general` the proposition for any rectilineal
figure (`Rectilineal`), `Prop14.square` the same with the square drawn, and `Prop14.sum`
today's two-triangle statement, derived from the general steps. They move into
`Elements/BookII/Prop14.lean` when proved, as "II.14 rectangle", "II.14 general",
"II.14 square" and "II.14 sum".
-/

namespace Elements.BookII

open Tacit

/-- **II.14, for a rectangle** (companion of II.14). To construct a square equal to a given
rectangle EBCD: the second part of Euclid's proof, with both of its cases, the rectangle
already a square or not, and in the second his semicircle [II. 5, I. 47]. The square is the
square on PQ. -/
theorem Prop14.rectangle {E B C D : Point} (h : Rectangle E B C D) :
    ∃ P Q : Point, sq P Q = quadArea E B C D := by
  sorry

/-- **II.14, for any rectilineal figure** (companion of II.14). To construct a square equal
to a given rectilineal figure, given with the triangles it is cut into: a rectangle equal to
the figure [I. 45, `Prop45.figure`], then a square equal to the rectangle
(`Prop14.rectangle`). The square is the square on PQ. -/
theorem Prop14.general (R : Rectilineal) : ∃ P Q : Point, sq P Q = R.area := by
  sorry

/-- **II.14, with the square drawn** (companion of II.14). To construct a square PQST equal
to a given rectilineal figure: the square on the side that `Prop14.general` finds,
described on it [I. 46]. The square is a parallelogram, and its area is the figure's. -/
theorem Prop14.square (R : Rectilineal) :
    ∃ P Q S T : Point, Square P Q S T ∧ Parallelogram P Q S T ∧ quadArea P Q S T = R.area := by
  sorry

/-- **II.14, for two triangles** (companion of II.14). Today's statement of II.14, derived
from the general steps: a rectangle equal to the two triangles ABD, DBC taken together
(`Prop45.sum`, in a right angle from I.11), then a square equal to the rectangle
(`Prop14.rectangle`). The two triangles are any two; they need not fit together into one
figure, so this does not follow from `Prop14.general`. -/
theorem Prop14.sum {A₁ A₂ A₃ A₄ : Point} (h₁ : Triangle A₁ A₂ A₄) (h₂ : Triangle A₄ A₂ A₃) :
    ∃ E H : Point, sq E H = △ A₁ A₂ A₄ + △ A₄ A₂ A₃ := by
  obtain ⟨L, hA₁, hA₂⟩ := Postulate1 A₁ A₂ h₁.ne₁₂
  obtain ⟨R, hR, hright⟩ := BookI.Prop11 h₁.ne₁₂ ⟨L, hA₁, hA₂, hA₁⟩ h₁
  have hR' : ∠ A₂ A₁ R = ∟ := hright A₂ ⟨L, hA₁, hA₂, hA₂⟩ h₁.ne₁₂.symm
  have hts : ∀ t ∈ [(A₁, A₂, A₄), (A₄, A₂, A₃)], Triangle t.1 t.2.1 t.2.2 := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact h₁
    · exact h₂
  obtain ⟨E, B, C, D, hp, hang, hBD⟩ :=
    BookI.Prop45.sum _ (List.cons_ne_nil _ _) hts hR.triangle.bac
  have hrect : Rectangle E B C D := by
    refine Rectangle.of_right hp ?_
    rw [angle_symm hp.2.2.1 hp.1.1.symm, hang, hR']
  obtain ⟨P, Q, hPQ⟩ := Prop14.rectangle hrect
  refine ⟨P, Q, ?_⟩
  rw [hPQ, hBD]
  simp only [List.map, Magnitude.sum, add_zero]

/-- The check: `Prop14.sum` has today's statement of II.14, exactly. -/
example : type_of% @Elements.BookII.Prop14 := @Prop14.sum

end Elements.BookII
