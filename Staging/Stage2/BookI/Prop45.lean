import Staging.Stage2.Sums

/-!
# Staging: I.45 for a figure of any number of sides

Brief 0006, stage 2. Companions of `Elements.BookI.Prop45`, which stays as Euclid's worked
configuration: the four-sided figure ABCD, cut by DB into the triangles ABD and DBC. The
companions state the proposition as Euclid and Byrne show it, for a figure of any number of
sides, as the owner decided (brief 0006, decision 1). The figure is given by its corners
A₀, A₁, …, Aₙ, at least three of them, in order round it, and the straight lines from the
first corner A₀ to the others divide it into the triangles A₀A₁A₂, A₀A₂A₃, …, A₀Aₙ₋₁Aₙ, one
on each side A₁A₂, A₂A₃, …, Aₙ₋₁Aₙ. Euclid's DB, drawn from D, makes two such triangles;
Byrne's two straight lines from one corner, in his I.45, make three. The parallelogram is
built one triangle at a time, as Byrne builds it: I.42 for the first triangle, and for each of
the rest a parallelogram applied to a side of the one built so far [I. 44], the two making one
parallelogram, as Euclid's proof shows. `Prop45.append` is that step, and `Prop45.figure` the
proposition. They move into `Elements/BookI/Prop45.lean` when proved, as "I.45 append" and
"I.45 figure".

**What "equal to the figure" means here.** The parallelogram is equal to the triangles
A₀A₁A₂, …, A₀Aₙ₋₁Aₙ taken together. That sum is what Euclid adds up when he calls the
triangles ABD and DBC "the whole rectilineal figure ABCD". Nothing here defines an area of
the figure apart from this division, or says that another division into triangles gives the
same sum: Euclid takes that for granted, and David Hilbert proved it (brief 0006, for the gap
catalogue). Each triangle is asked to have its corners off one straight line, and nothing
more. When the straight lines from A₀ run within the figure, as they do in every convex
figure and in Euclid's and Byrne's, the triangles fill it without overlapping, and the sum is
what Euclid calls the figure. When they do not, the theorem still holds of the triangles, but
they are not the figure's pieces.
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

/-- **I.45, for a figure of any number of sides** (companion of I.45). To construct, in a
given rectilineal angle E, a parallelogram equal to a given rectilineal figure. The figure is
given by its corners A₀, A₁, A₂, …, Aₙ, the list `ps` being A₃, …, Aₙ (empty for a triangle),
and the straight lines from A₀ divide it into the triangles A₀A₁A₂, A₀A₂A₃, …, A₀Aₙ₋₁Aₙ:
`segments (A₁ :: A₂ :: ps)` are the sides A₁A₂, A₂A₃, …, Aₙ₋₁Aₙ, as in II.1, and each side
with A₀ makes a triangle, its corners not on one straight line. The parallelogram KFLM, its
angle at K equal to E, is equal to those triangles taken together, which is what this
statement means by the figure; it claims nothing of another division.

The parallelogram is built one triangle at a time: one for A₀A₁A₂ by I.42, then
`Prop45.append` for each triangle after it, in order. Euclid's ABCD with DB joined is the
figure with corners D, A, B, C, and its triangles DAB and DBC (the check below). -/
theorem Prop45.figure {A₀ A₁ A₂ E₁ E E₂ : Point} {ps : List Point}
    (htri : ∀ s ∈ segments (A₁ :: A₂ :: ps), Triangle A₀ s.1 s.2) (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M =
        Magnitude.sum ((segments (A₁ :: A₂ :: ps)).map fun s => △ A₀ s.1 s.2) := by
  /- One triangle after another: a parallelogram in the angle E equal to X, with the
     triangles on the sides from P onwards added one at a time by `Prop45.append`. -/
  have step : ∀ (rest : List Point) (P K F L M : Point) (X : Area),
      Parallelogram K F L M → ∠ F K M = ∠ E₁ E E₂ → quadArea K F L M = X →
      (∀ s ∈ segments (P :: rest), Triangle A₀ s.1 s.2) →
      ∃ K' F' L' M' : Point, Parallelogram K' F' L' M' ∧ ∠ F' K' M' = ∠ E₁ E E₂ ∧
        quadArea K' F' L' M' =
          X + Magnitude.sum ((segments (P :: rest)).map fun s => △ A₀ s.1 s.2) := by
    intro rest
    induction rest with
    | nil =>
      intro P K F L M X hp hang harea _
      refine ⟨K, F, L, M, hp, hang, ?_⟩
      rw [harea]
      exact (add_zero X).symm
    | cons Q rest ih =>
      intro P K F L M X hp hang harea hts
      have hPQ : Triangle A₀ P Q := hts (P, Q) (List.mem_cons_self ..)
      obtain ⟨K', F', L', M', hp', hang', harea'⟩ := Prop45.append hp hang hPQ hE
      obtain ⟨K'', F'', L'', M'', hp'', hang'', harea''⟩ :=
        ih Q K' F' L' M' (X + △ A₀ P Q) hp' hang' (by rw [harea', harea])
          (fun s hs => hts s (List.mem_cons_of_mem _ hs))
      refine ⟨K'', F'', L'', M'', hp'', hang'', ?_⟩
      rw [harea'']
      exact add_assoc X (△ A₀ P Q) _
  /- The first triangle, A₀A₁A₂, by I.42. Its parallelogram FGA₂H, with its angle at G
     equal to E, is named from G, as GFHA₂. -/
  have h₁ : Triangle A₀ A₁ A₂ := htri (A₁, A₂) (List.mem_cons_self ..)
  obtain ⟨G, F, H, -, -, hp, hang, harea⟩ := Prop42 h₁ hE
  have hFG : F ≠ G := hp.1.1
  have hGA₂ : G ≠ A₂ := hp.2.1
  obtain ⟨K, F', L, M, hp', hang', harea'⟩ :=
    step ps A₂ G F H A₂ (△ A₀ A₁ A₂) hp.reverse.rotate.rotate.rotate
      (by rw [angle_symm hFG hGA₂.symm]; exact hang)
      (by rw [quadArea_reverse G A₂ H F, hp.quadArea_rotate, harea])
      (fun s hs => htri s (List.mem_cons_of_mem _ hs))
  exact ⟨K, F', L, M, hp', hang', harea'⟩

/-- The check: today's statement of I.45, for the triangles ABD and DBC, follows from
`Prop45.figure` for the figure with corners D, A, B, C, whose triangles are DAB and DBC
(checked by Lean, up to unfolding definitions and naming the triangle ABD from D). -/
example : type_of% @Elements.BookI.Prop45 := by
  intro A B C D E₁ E E₂ hABD hDBC hE
  have htri : ∀ s ∈ segments [A, B, C], Triangle D s.1 s.2 := by
    intro s hs
    simp only [segments, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact hABD.cab
    · exact hDBC
  obtain ⟨K, F, L, M, hp, hang, harea⟩ := Prop45.figure (A₀ := D) htri hE
  refine ⟨K, F, L, M, hp, hang, ?_⟩
  rw [harea]
  simp only [segments, List.map, Magnitude.sum, add_zero]
  rw [area_bca D A B]

end Elements.BookI
