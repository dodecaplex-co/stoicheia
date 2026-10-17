import Elements.Figure.Basics
import Elements.BookI.Prop02

/-!
# Book I, Proposition 3

Euclid's text, in Heath's translation: [`heath/I/03.md`](../../heath/I/03.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid names the lesser straight line by a single letter, C. In Lean it is the
finite straight line from C₁ to C₂.
-/

namespace Elements.BookI

open Tacit

/-- Given two unequal straight lines, to cut off from the greater a straight line equal to the
less. -/
theorem Prop3 {A B C₁ C₂ : Point} (hC : C₁ ≠ C₂) (h : ‖C₁ C₂‖ < ‖A B‖) :
    ∃ E : Point, Between A E B ∧ ‖A E‖ = ‖C₁ C₂‖ := by
  -- Let AB, C be the two given unequal straight lines, and let AB be the greater of them.
  have hAB : A ≠ B := ne_of_len_gt h
  -- Thus it is required to cut off from AB the greater a straight line equal to C the less.
  -- At the point A let AD be placed equal to the straight line C; [I. 2]
  obtain ⟨D, hAD⟩ := Prop2 A C₁ C₂ hC
  have hAD' : A ≠ D := ne_of_len_eq hAD hC
  -- and with centre A and distance AD let the circle DEF be described. [Post. 3]
  obtain ⟨DEF, hA_DEF, hD_DEF⟩ := Postulate3 A D hAD'
  /- Euclid does not say where the circle DEF meets AB. B lies outside it, since
     AB is the greater, and A, the centre, lies inside; so the straight line AB
     cuts the circle at a point E between A and B (System E, Intersections 4). -/
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  have hB_out : OutsideCircle B DEF := outside_of_len_gt hA_DEF hD_DEF (by rw [hAD]; exact h)
  obtain ⟨E, hE_DEF, -, hAEB⟩ := line_circle_between (centre_inside hA_DEF) hA_AB hB_out hB_AB
  -- Now, since the point A is the centre of the circle DEF,
  -- AE is equal to AD. [Def. 15]
  have hAE_AD : ‖A E‖ = ‖A D‖ := Definition15 hA_DEF hE_DEF hD_DEF
  -- But C is also equal to AD.
  have hC_AD : ‖C₁ C₂‖ = ‖A D‖ := hAD.symm
  -- Therefore each of the straight lines AE, C is equal to AD; so that AE is also equal to C.
  -- [C.N. 1]
  have hAE_C : ‖A E‖ = ‖C₁ C₂‖ := CommonNotion1 hAE_AD hC_AD
  -- Therefore, given the two straight lines AB, C, from AB the greater AE has been cut off
  -- equal to C the less.
  exact ⟨E, hAEB, hAE_C⟩
  -- (Being) what it was required to do.

end Elements.BookI
