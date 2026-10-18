import Staging.Stage2.BookI.Prop45

/-!
# Staging: II.14 for a figure of any number of sides, with a drawn square

Brief 0006, stage 2. Companions of `Elements.BookII.Prop14`, which stays as Euclid's worked
configuration, I.45's figure of two triangles, and returns the side of the square. His proof
makes a rectangle equal to the figure [I. 45] and then a square equal to the rectangle.
`Prop14.rectangle` is that second part; `Prop14.general` is the proposition for a figure of
any number of sides, given by its corners and divided by the straight lines from its first
corner, as in I.45's companion `Prop45.figure`; and `Prop14.square` is the same with the
square drawn. As there, the square is equal to the triangles of that division taken
together, and nothing is claimed of another division. Today's II.14 follows from
`Prop14.general` (the check at the end).

`Prop14.rectangle` is proved directly, by Euclid's second part, and never cites II.14:
otherwise `Prop14.general` and `Prop14.square` would rest on the two-triangle statement
rather than on Euclid's square construction, and the check that today's II.14 follows from
`Prop14.general` would prove II.14 from II.14 (brief 0006). They move into
`Elements/BookII/Prop14.lean` when proved, as "II.14 rectangle", "II.14 general" and
"II.14 square".
-/

namespace Elements.BookII

open Tacit

/-- **II.14, for a rectangle** (companion of II.14). To construct a square equal to a given
rectangle EBCD: the second part of Euclid's proof, with both of its cases. If BE is equal to
ED, the rectangle is a square already. If not, the greater, say BE, is produced to F with EF
equal to ED, BF is bisected at G, the semicircle BHF is described with centre G, and DE is
produced to H; then the rectangle BE, EF with the square on EG is the square on GF [II. 5],
which is the squares on HE, EG [I. 47], and the rectangle is the square on EH. This is
today's proof of II.14 after the rectangle is made. It does not cite II.14. The square is the
square on PQ. -/
theorem Prop14.rectangle {E B C D : Point} (h : Rectangle E B C D) :
    ∃ P Q : Point, sq P Q = quadArea E B C D := by
  sorry

/-- **II.14, for a figure of any number of sides** (companion of II.14). To construct a
square equal to a given rectilineal figure, given by its corners A₀, A₁, A₂, …, Aₙ and divided
by the straight lines from A₀ into the triangles A₀A₁A₂, …, A₀Aₙ₋₁Aₙ, as in `Prop45.figure`:
the square on PQ is equal to those triangles taken together. A rectangle equal to them
[I. 45, `Prop45.figure`, in a right angle from I.11 at A₀ on A₀A₁], then a square equal to
the rectangle (`Prop14.rectangle`). -/
theorem Prop14.general {A₀ A₁ A₂ : Point} {ps : List Point}
    (htri : ∀ s ∈ segments (A₁ :: A₂ :: ps), Triangle A₀ s.1 s.2) :
    ∃ P Q : Point,
      sq P Q = Magnitude.sum ((segments (A₁ :: A₂ :: ps)).map fun s => △ A₀ s.1 s.2) := by
  have h₁ : Triangle A₀ A₁ A₂ := htri (A₁, A₂) (List.mem_cons_self ..)
  obtain ⟨L, hA₀, hA₁⟩ := Postulate1 A₀ A₁ h₁.ne₁₂
  obtain ⟨X, hX, hright⟩ := BookI.Prop11 h₁.ne₁₂ ⟨L, hA₀, hA₁, hA₀⟩ h₁
  have hX' : ∠ A₁ A₀ X = ∟ := hright A₁ ⟨L, hA₀, hA₁, hA₁⟩ h₁.ne₁₂.symm
  obtain ⟨E, F, G, H, hp, hang, harea⟩ := BookI.Prop45.figure htri hX.triangle.bac
  have hrect : Rectangle E F G H := by
    refine Rectangle.of_right hp ?_
    rw [angle_symm hp.2.2.1 hp.1.1.symm, hang, hX']
  obtain ⟨P, Q, hPQ⟩ := Prop14.rectangle hrect
  exact ⟨P, Q, hPQ.trans harea⟩

/-- **II.14, with the square drawn** (companion of II.14). To construct a square PQST equal
to a given rectilineal figure, given and divided as in `Prop14.general`: the square on the
side that `Prop14.general` finds, described on it [I. 46]. The square is a parallelogram,
and it is equal to the figure's triangles taken together. -/
theorem Prop14.square {A₀ A₁ A₂ : Point} {ps : List Point}
    (htri : ∀ s ∈ segments (A₁ :: A₂ :: ps), Triangle A₀ s.1 s.2) :
    ∃ P Q S T : Point, Square P Q S T ∧ Parallelogram P Q S T ∧
      quadArea P Q S T =
        Magnitude.sum ((segments (A₁ :: A₂ :: ps)).map fun s => △ A₀ s.1 s.2) := by
  sorry

/-- The check: today's statement of II.14, for I.45's two triangles A₁A₂A₄ and A₄A₂A₃ (ABD
and DBC), follows from `Prop14.general` for the figure with corners A₄, A₁, A₂, A₃, whose
triangles are A₄A₁A₂ and A₄A₂A₃ (checked by Lean, up to unfolding definitions and naming the
triangle A₁A₂A₄ from A₄). -/
example : type_of% @Elements.BookII.Prop14 := by
  intro A₁ A₂ A₃ A₄ h₁ h₂
  have htri : ∀ s ∈ segments [A₁, A₂, A₃], Triangle A₄ s.1 s.2 := by
    intro s hs
    simp only [segments, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact h₁.cab
    · exact h₂
  obtain ⟨P, Q, hPQ⟩ := Prop14.general (A₀ := A₄) htri
  refine ⟨P, Q, ?_⟩
  rw [hPQ]
  simp only [segments, List.map, Magnitude.sum, add_zero]
  rw [area_bca A₄ A₁ A₂]

end Elements.BookII
