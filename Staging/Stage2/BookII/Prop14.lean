import Staging.Stage2.BookI.Prop45

/-!
# Staging: II.14 for any rectilineal figure, with a drawn square

Brief 0006, stage 2, as revised on 18 October 2026. Companions of `Elements.BookII.Prop14`,
which stays as Euclid's worked configuration, I.45's figure of two triangles, and returns
the side of the square. His proof makes a rectangle equal to the figure [I. 45] and then a
square equal to the rectangle.

* `Prop14.rectangle` is that second part.
* `Prop14.sum` is the proof for any number of triangles, by I.45's `Prop45.sum`: the
  construction, which claims nothing of a figure.
* `Prop14.general` is the proposition for any rectilineal figure, given with a division
  into triangles that is checked to be one (`Rectilineal`), as in I.45's `Prop45.figure`;
  `Prop14.square` is the same with the square drawn.
* `Prop14.fan` is the proposition for a figure divided as Euclid and Byrne divide it, from
  one corner, with the division checked as in `Prop45.fan`; it follows from
  `Prop14.general`, since such a division is fitted (`Fitted.fan`).

As in I.45, the square is equal to the triangles the figure is given with, taken together,
and nothing is claimed of another division. Today's II.14 follows from `Prop14.sum` (the
check at the end).

`Prop14.rectangle` is proved directly, by Euclid's second part, and never cites II.14:
otherwise the companions would rest on the two-triangle statement rather than on Euclid's
square construction, and the check that today's II.14 follows from `Prop14.sum` would prove
II.14 from II.14 (brief 0006). They move into `Elements/BookII/Prop14.lean` when proved, as
"II.14 rectangle", "II.14 sum", "II.14 general", "II.14 square" and "II.14 fan".
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

/-- **II.14, any number of triangles** (companion of II.14). To construct a square equal to
any number of given triangles taken together, at least one: a rectangle equal to them
[I. 45, `Prop45.sum`, in a right angle from I.11 at a corner A of the first triangle ABC, on
AB], then a square equal to the rectangle (`Prop14.rectangle`). The triangles are any
triangles; they need not fit together into one figure, and the statement claims nothing of
a figure. The square is the square on PQ. -/
theorem Prop14.sum (ts : List (Point × Point × Point)) (hne : ts ≠ [])
    (hts : ∀ t ∈ ts, Triangle t.1 t.2.1 t.2.2) :
    ∃ P Q : Point, sq P Q = Magnitude.sum (ts.map fun t => △ t.1 t.2.1 t.2.2) := by
  match ts, hne, hts with
  | (A, B, C) :: rest, _, hts =>
    have hABC : Triangle A B C := hts (A, B, C) (List.mem_cons_self ..)
    obtain ⟨L, hA, hB⟩ := Postulate1 A B hABC.ne₁₂
    obtain ⟨X, hX, hright⟩ := BookI.Prop11 hABC.ne₁₂ ⟨L, hA, hB, hA⟩ hABC
    have hX' : ∠ B A X = ∟ := hright B ⟨L, hA, hB, hB⟩ hABC.ne₁₂.symm
    obtain ⟨E, F, G, H, hp, hang, harea⟩ :=
      BookI.Prop45.sum _ (List.cons_ne_nil _ _) hts hX.triangle.bac
    have hrect : Rectangle E F G H := by
      refine Rectangle.of_right hp ?_
      rw [angle_symm hp.2.2.1 hp.1.1.symm, hang, hX']
    obtain ⟨P, Q, hPQ⟩ := Prop14.rectangle hrect
    exact ⟨P, Q, hPQ.trans harea⟩

/-- **II.14, for any rectilineal figure** (companion of II.14). To construct a square equal
to a given rectilineal figure, given with the triangles it is cut into, each glued across a
side of an earlier one and meeting the earlier ones only along it (`Rectilineal`), as in
`Prop45.figure`: the square on PQ is equal to those triangles taken together
(`Rectilineal.area`). It is `Prop14.sum` for the figure's triangles. Nothing is claimed of
another division of the figure. -/
theorem Prop14.general (R : Rectilineal) : ∃ P Q : Point, sq P Q = R.area :=
  Prop14.sum R.pieces R.fitted.ne_nil R.fitted.triangle

/-- **II.14, with the square drawn** (companion of II.14). To construct a square PQST equal
to a given rectilineal figure, given with its triangles as in `Prop14.general`: the square on
the side that `Prop14.general` finds, described on it [I. 46]. The square is a
parallelogram, and it is equal to the figure's triangles taken together. -/
theorem Prop14.square (R : Rectilineal) :
    ∃ P Q S T : Point, Square P Q S T ∧ Parallelogram P Q S T ∧ quadArea P Q S T = R.area := by
  sorry

/-- **II.14, for a figure divided from one corner** (companion of II.14), as Euclid and
Byrne divide it. To construct a square equal to a given rectilineal figure with corners A₀,
A₁, A₂, …, Aₙ in order round it, divided by the straight lines from A₀ into the triangles
A₀A₁A₂, …, A₀Aₙ₋₁Aₙ, with the division checked as in `Prop45.fan`: each piece a triangle,
each two neighbouring triangles on opposite sides of the straight line A₀Aᵢ they share
(`hopp`), and the angles at A₀ together less than four right angles (`hA₀`). The square on PQ
is equal to those triangles taken together. It is `Prop14.general` for the fitted figure
that `Fitted.fan` gives; the square drawn is `Prop14.square` for the same figure. -/
theorem Prop14.fan {A₀ A₁ A₂ : Point} {ps : List Point}
    (htri : ∀ s ∈ segments (A₁ :: A₂ :: ps), Triangle A₀ s.1 s.2)
    (hopp : ∀ t ∈ triples (A₁ :: A₂ :: ps), OppositeSidesOf t.1 t.2.2 A₀ t.2.1)
    (hA₀ : Magnitude.sum ((segments (A₁ :: A₂ :: ps)).map fun s => ∠ s.1 A₀ s.2) <
      ∟ + ∟ + (∟ + ∟)) :
    ∃ P Q : Point,
      sq P Q = Magnitude.sum ((segments (A₁ :: A₂ :: ps)).map fun s => △ A₀ s.1 s.2) := by
  obtain ⟨P, Q, hPQ⟩ := Prop14.general ⟨_, Fitted.fan htri hopp hA₀⟩
  refine ⟨P, Q, ?_⟩
  rw [hPQ, Rectilineal.area, List.map_map]
  rfl

/-- The check: today's statement of II.14, for I.45's two triangles A₁A₂A₄ and A₄A₂A₃ (ABD
and DBC), follows from `Prop14.sum` for the list of those two (checked by Lean, up to
unfolding definitions). -/
example : type_of% @Elements.BookII.Prop14 := by
  intro A₁ A₂ A₃ A₄ h₁ h₂
  have hts : ∀ t ∈ [(A₁, A₂, A₄), (A₄, A₂, A₃)], Triangle t.1 t.2.1 t.2.2 := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact h₁
    · exact h₂
  obtain ⟨P, Q, hPQ⟩ := Prop14.sum _ (List.cons_ne_nil _ _) hts
  refine ⟨P, Q, ?_⟩
  rw [hPQ]
  simp only [List.map, Magnitude.sum, add_zero]

end Elements.BookII
