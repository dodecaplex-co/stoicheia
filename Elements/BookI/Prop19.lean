import Elements.Figure.Basics
import Elements.BookI.Prop05
import Elements.BookI.Helpers
import Elements.BookI.Prop18

/-!
# Book I, Proposition 19

Euclid's text, in Heath's translation: [`heath/I/19.md`](../../heath/I/19.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

There is no figure to build here. Euclid divides the cases ("by means of
division", says Proclus): if AC is not greater than AB, it is equal to it or
less, and I.5 and I.18, already proved, each rule one of them out. The Lean
has no helper of its own; `Prop5.base` hands I.5 the produced sides its
statement asks for.
-/

namespace Elements.BookI

open Tacit

/-- In any triangle the greater angle is subtended by the greater side. -/
theorem Prop19 {A B C : Point} (hABC : Triangle A B C) (h : ∠ B C A < ∠ A B C) :
    ‖A B‖ < ‖A C‖ := by
  -- Let ABC be a triangle having the angle ABC greater than the angle BCA;
  /- Euclid names the less angle BCA here and ACB below. They are one angle,
     read from either arm (`angle_symm`, System E's Metric 4). -/
  have hBCA_ACB : ∠ B C A = ∠ A C B := angle_symm hABC.ne₂₃ hABC.ne₁₃
  have hACB_ABC : ∠ A C B < ∠ A B C := hBCA_ACB ▸ h
  -- I say that the side AC is also greater than the side AB.
  -- For, if not, AC is either equal to AB or less.
  /- That a length not greater than another is equal to it or less is the tacit
     rule of magnitude `lt_trichotomy` (System E §3.5). -/
  have either : ¬ ‖A B‖ < ‖A C‖ → ‖A C‖ = ‖A B‖ ∨ ‖A C‖ < ‖A B‖ := by
    intro hnot
    rcases lt_trichotomy ‖A C‖ ‖A B‖ with hlt | heq | hgt
    · exact Or.inr hlt
    · exact Or.inl heq
    · exact absurd hgt hnot
  -- Now AC is not equal to AB;
  have not_equal : ‖A C‖ ≠ ‖A B‖ := by
    intro hAC_AB
    -- for then the angle ABC would also have been equal to the angle ACB; [I. 5]
    have hABC_ACB : ∠ A B C = ∠ A C B := Prop5.base hABC hAC_AB.symm
    -- but it is not;
    /- It is greater: the hypothesis, with BCA read as ACB. -/
    have hne : ∠ A B C ≠ ∠ A C B := fun heq => Magnitude.ne_of_lt hACB_ABC heq.symm
    -- therefore AC is not equal to AB.
    exact hne hABC_ACB
  -- Neither is AC less than AB,
  have not_less : ¬ ‖A C‖ < ‖A B‖ := by
    intro hAC_AB
    -- for then the angle ABC would also have been less than the angle ACB; [I. 18]
    /- This is I.18 for the triangle ACB, whose side AB is the greater. It hands
       back the angle CBA, which is the angle ABC read from the other arm. -/
    have hABC_ACB : ∠ A B C < ∠ A C B := by
      have hI18 : ∠ C B A < ∠ A C B := Prop18 hABC.acb hAC_AB
      rw [angle_symm hABC.ne₂₃.symm hABC.ne₁₂] at hI18
      exact hI18
    -- but it is not;
    /- It is greater, and a magnitude cannot be both less and greater than
       another (`lt_trans`, `lt_irrefl`). -/
    have hnot : ¬ ∠ A B C < ∠ A C B := fun hlt => lt_irrefl _ (lt_trans hlt hACB_ABC)
    -- therefore AC is not less than AB.
    exact hnot hABC_ACB
  -- And it was proved that it is not equal either.
  /- Both ways out are closed; Euclid's division is complete. -/
  have neither : ¬ (‖A C‖ = ‖A B‖ ∨ ‖A C‖ < ‖A B‖) := fun hor =>
    hor.elim not_equal not_less
  -- Therefore AC is greater than AB.
  /- Reductio ad absurdum: were AC not greater, the division above would make it
     equal or less, and it is neither. -/
  exact Classical.byContradiction fun hnot => neither (either hnot)
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookI
