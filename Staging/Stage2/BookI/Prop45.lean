import Staging.Stage2.Rectilineal

/-!
# Staging: I.45 for any rectilineal figure

Brief 0006, stage 2, as revised on 18 October 2026. Companions of `Elements.BookI.Prop45`,
which stays as Euclid's worked configuration: the four-sided figure ABCD, cut by DB into
the triangles ABD and DBC. Euclid's proof makes a parallelogram for the first triangle
[I. 42], applies one for the second to its side [I. 44], and shows that the two make one
parallelogram; a figure of more triangles repeats the second step, as Byrne draws it for
three (1847, p. 46).

* `Prop45.append` is that second step.
* `Prop45.sum` repeats it, for any number of triangles. It is the construction, and claims
  nothing of a figure: the triangles need not fit together.
* `Prop45.apart` is the proposition for any rectilineal figure, with any boundaries, given
  with triangles that lie apart, no point inside two of them (`Apart`). The figure may have
  a hole (Definition I.14: "any boundary or boundaries").
* `Prop45.figure` is the proposition for a figure with one boundary, given with a division
  into triangles fitted together (`Rectilineal`, `Fitted`). It follows from `Prop45.apart`,
  since fitted triangles lie apart (`Fitted.inside_pairwise`).
* `Prop45.fan` is the proposition for a figure divided as Euclid and Byrne divide it, by the
  straight lines from one corner A₀, with the two conditions that make those triangles a
  division of the figure: neighbouring triangles on opposite sides of the straight line
  they share, and the angles at A₀ together less than four right angles. It follows from
  `Prop45.figure`, since such a division is fitted (`Fitted.fan`). The construction does not
  use the two conditions: they make the triangles a division of the figure, and the proof
  goes through `Fitted.fan` on purpose, so that the fan companion is the general one applied
  to a checked fan.

The names: `figure` is Euclid's word for what is given ("a given rectilineal figure"), so the
companion for any figure glued together has it; `apart` names the figure whose triangles
lie apart; `fan` names the division Euclid draws, from one corner,
which not every figure admits. The two agree, since a checked fan is a fitted figure and its
triangles are the figure's. They move into `Elements/BookI/Prop45.lean` when proved, as
"I.45 append", "I.45 sum", "I.45 apart", "I.45 figure" and "I.45 fan".

**What "equal to the figure" means here.** The parallelogram is equal to the triangles the
figure is given with, taken together. That sum is what Euclid adds up when he calls ABD and
DBC "the whole rectilineal figure ABCD". Nothing here says that another division of the
figure gives the same sum: Euclid takes that for granted, and David Hilbert proved it, for
his measure of area (brief 0006, for the gap catalogue). Today's I.45, whose ABD and DBC
need only be triangles, follows from `Prop45.sum` (the check at the end). Those two triangles
are not checked, and may overlap; the checked case of today's figure is `Prop45.fan` for the
corners D, A, B, C, where the condition on neighbours is that A and C lie on opposite sides
of DB.
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
rectilineal angle E, a parallelogram equal to any number of given triangles taken together,
at least one: I.42 for the first, then `Prop45.append` for each of the rest, in order. The
triangles are any triangles, each with its corners off one straight line; they need not fit
together into one figure, and the statement claims nothing of a figure. -/
theorem Prop45.sum {E₁ E E₂ : Point} (ts : List (Point × Point × Point)) (hne : ts ≠ [])
    (hts : ∀ t ∈ ts, Triangle t.1 t.2.1 t.2.2) (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M = Magnitude.sum (ts.map fun t => △ t.1 t.2.1 t.2.2) := by
  /- One triangle after another: a parallelogram in the angle E equal to X, with the
     triangles of `rest` added one at a time by `Prop45.append`. -/
  have step : ∀ (rest : List (Point × Point × Point)) (K F L M : Point) (X : Area),
      Parallelogram K F L M → ∠ F K M = ∠ E₁ E E₂ → quadArea K F L M = X →
      (∀ t ∈ rest, Triangle t.1 t.2.1 t.2.2) →
      ∃ K' F' L' M' : Point, Parallelogram K' F' L' M' ∧ ∠ F' K' M' = ∠ E₁ E E₂ ∧
        quadArea K' F' L' M' = X + Magnitude.sum (rest.map fun t => △ t.1 t.2.1 t.2.2) := by
    intro rest
    induction rest with
    | nil =>
      intro K F L M X hp hang harea _
      refine ⟨K, F, L, M, hp, hang, ?_⟩
      rw [harea]
      exact (add_zero X).symm
    | cons t rest ih =>
      intro K F L M X hp hang harea hts
      obtain ⟨K', F', L', M', hp', hang', harea'⟩ :=
        Prop45.append hp hang (hts t (List.mem_cons_self ..)) hE
      obtain ⟨K'', F'', L'', M'', hp'', hang'', harea''⟩ :=
        ih K' F' L' M' (X + △ t.1 t.2.1 t.2.2) hp' hang' (by rw [harea', harea])
          (fun s hs => hts s (List.mem_cons_of_mem _ hs))
      refine ⟨K'', F'', L'', M'', hp'', hang'', ?_⟩
      rw [harea'']
      exact add_assoc X (△ t.1 t.2.1 t.2.2) _
  match ts, hne, hts with
  | (A, B, C) :: rest, _, hts =>
    /- The first triangle, ABC, by I.42. Its parallelogram FGCH, with its angle at G equal
       to E, is named from G, as GFHC. -/
    have h₁ : Triangle A B C := hts (A, B, C) (List.mem_cons_self ..)
    obtain ⟨G, F, H, -, -, hp, hang, harea⟩ := Prop42 h₁ hE
    have hFG : F ≠ G := hp.1.1
    have hGC : G ≠ C := hp.2.1
    obtain ⟨K, F', L, M, hp', hang', harea'⟩ :=
      step rest G F H C (△ A B C) hp.reverse.rotate.rotate.rotate
        (by rw [angle_symm hFG hGC.symm]; exact hang)
        (by rw [quadArea_reverse G C H F, hp.quadArea_rotate, harea])
        (fun s hs => hts s (List.mem_cons_of_mem _ hs))
    exact ⟨K, F', L, M, hp', hang', harea'⟩

/-- **I.45, for any rectilineal figure, with any boundaries** (companion of I.45). To
construct, in a given rectilineal angle E, a parallelogram KFLM, its angle at K equal to E,
equal to a given rectilineal figure: the figure given with the triangles it is cut into, no
point inside two of them (`Apart`), and "equal to the figure" meaning equal to those
triangles taken together (`Apart.area`). The figure may have a hole, touch itself at a
corner, or be in more than one piece. It is `Prop45.sum` for the figure's triangles; lying
apart is what makes their sum the figure's. Nothing is claimed of another division of the
figure. -/
theorem Prop45.apart {E₁ E E₂ : Point} (R : Apart) (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M = R.area :=
  Prop45.sum R.pieces R.ne R.triangle hE

/-- **I.45, for any rectilineal figure with one boundary** (companion of I.45). To
construct, in a given rectilineal angle E, a parallelogram KFLM, its angle at K equal to E,
equal to a given rectilineal figure: the figure given with the triangles it is cut into, each
glued across a side of an earlier one and meeting the earlier ones only along it
(`Rectilineal`), and "equal to the figure" meaning equal to those triangles taken together
(`Rectilineal.area`). The figure may be convex or not, and need have no corner from which the
straight lines to the others divide it. It is `Prop45.apart` for the figure's triangles,
which lie apart (`Fitted.inside_pairwise`). Nothing is claimed of another division of the
figure. -/
theorem Prop45.figure {E₁ E E₂ : Point} (R : Rectilineal) (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M = R.area :=
  Prop45.apart ⟨R.pieces, R.fitted.ne_nil, R.fitted.triangle, R.fitted.inside_pairwise⟩ hE

/-- **I.45, for a figure divided from one corner** (companion of I.45), as Euclid and Byrne
divide it. To construct, in a given rectilineal angle E, a parallelogram KFLM, its angle at
K equal to E, equal to a given rectilineal figure with corners A₀, A₁, A₂, …, Aₙ, the list
`ps` being A₃, …, Aₙ (empty for a triangle), divided by the straight lines from A₀ into the
triangles A₀A₁A₂, A₀A₂A₃, …, A₀Aₙ₋₁Aₙ, one on each side
`segments (A₁ :: A₂ :: ps)`. The division is checked: each piece is a triangle; each two
neighbouring triangles A₀Aᵢ₋₁Aᵢ and A₀AᵢAᵢ₊₁ lie on opposite sides of the straight line
A₀Aᵢ they share (`hopp`, over `triples (A₁ :: A₂ :: ps)`); and the angles A₁A₀A₂, …,
Aₙ₋₁A₀Aₙ together are less than four right angles (`hA₀`). Then the triangles are fitted
together into one figure (`Fitted.fan`), read as the figure with corners A₀, A₁, …, Aₙ in
order round it (that its boundary is that closed line is not stated in Lean), and the
parallelogram is equal to them taken together, which is the figure as given. It claims
nothing of another division.

The construction does not use `hopp` and `hA₀`: its conclusion follows from `htri` alone, by
`Prop45.sum`. The two conditions make the triangles a division of the figure, and the proof
goes through `Fitted.fan` on purpose, so that this companion is `Prop45.figure` applied to a
checked fan.

Euclid's ABCD with DB joined is the figure with corners D, A, B, C, its triangles DAB and
DBC: A and C lie on opposite sides of DB. Byrne's figure has its corners listed from its
re-entrant corner, from which both his straight lines are drawn. -/
theorem Prop45.fan {A₀ A₁ A₂ E₁ E E₂ : Point} {ps : List Point}
    (htri : ∀ s ∈ segments (A₁ :: A₂ :: ps), Triangle A₀ s.1 s.2)
    (hopp : ∀ t ∈ triples (A₁ :: A₂ :: ps), OppositeSidesOf t.1 t.2.2 A₀ t.2.1)
    (hA₀ : Magnitude.sum ((segments (A₁ :: A₂ :: ps)).map fun s => ∠ s.1 A₀ s.2) <
      ∟ + ∟ + (∟ + ∟))
    (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M =
        Magnitude.sum ((segments (A₁ :: A₂ :: ps)).map fun s => △ A₀ s.1 s.2) := by
  obtain ⟨K, F, L, M, hp, hang, harea⟩ :=
    Prop45.figure ⟨_, Fitted.fan htri hopp hA₀⟩ hE
  refine ⟨K, F, L, M, hp, hang, ?_⟩
  rw [harea, Rectilineal.area, List.map_map]
  rfl

/-- The check: today's statement of I.45, for the two triangles ABD, DBC, follows from
`Prop45.sum` for the list of those two (checked by Lean, up to unfolding definitions). -/
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
