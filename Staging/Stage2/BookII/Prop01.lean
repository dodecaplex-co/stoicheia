import Staging.Stage2.Sums

/-!
# Staging: II.1 for any number of segments

Brief 0006, stage 2. Companions of `Elements.BookII.Prop1`, which stays as Euclid's worked
configuration: BC cut at the two points D, E into three segments. His enunciation says "any
number of segments whatever". `Prop1.two` is one cut, by II.1's own construction, and
`Prop1.general` any number, by repeating it. They move into `Elements/BookII/Prop01.lean`
when proved, as "II.1 two" and "II.1 general".
-/

namespace Elements.BookII

open Tacit

/-- **II.1, one cut** (companion of II.1). If the straight line BC is cut at D, the
rectangle contained by A₁A₂ and BC is equal to the rectangles contained by A₁A₂ and each
of BD, DC. II.1's construction, with one parallel drawn through D. The uncut straight line
A₁A₂ may be nothing, and then every rectangle is nothing. -/
theorem Prop1.two {A₁ A₂ B C D : Point} (h : Between B D C) :
    rect A₁ A₂ B C = rect A₁ A₂ B D + rect A₁ A₂ D C := by
  sorry

/-- **II.1, any number of segments** (companion of II.1). If the straight line from B to its
end is cut at any number of points in order, the rectangle contained by A₁A₂ and the whole
is equal to the rectangles contained by A₁A₂ and each of the segments. The list `ps` is
the points of section followed by the end; with no points of section it is the whole
straight line alone, and with no points at all the straight line is nothing and so is each
side. -/
theorem Prop1.general {A₁ A₂ B : Point} {ps : List Point} (h : InOrder (B :: ps)) :
    rect A₁ A₂ B (endOf B ps) =
      Magnitude.sum ((segments (B :: ps)).map fun s => rect A₁ A₂ s.1 s.2) := by
  sorry

/-- The check: today's statement of II.1, BC cut at D and E, is `Prop1.general` for the
points `[D, E, C]`, exactly. -/
example : type_of% @Elements.BookII.Prop1 := by
  intro A₁ A₂ B C D E _ hBDE hDEC
  have h : InOrder [B, D, E, C] :=
    ⟨ne_of_between hBDE, hBDE, ne_of_between hDEC, hDEC,
      (ne_of_between (between_symm hDEC)).symm⟩
  have hgen := Prop1.general (A₁ := A₁) (A₂ := A₂) h
  simp only [endOf, segments, List.map, Magnitude.sum, add_zero] at hgen
  rw [hgen, add_assoc]

end Elements.BookII
