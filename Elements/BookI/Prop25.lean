import Elements.Figure.Basics
import Elements.BookI.Prop04
import Elements.BookI.Prop24

/-!
# Book I, Proposition 25

Euclid's text, in Heath's translation: [`heath/I/25.md`](../../heath/I/25.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

There is no figure to build here. As in I.19, Euclid divides the cases: if the
angle BAC is not greater than the angle EDF, it is equal to it or less, and
I.4 and I.24, already proved, each rule one of them out. I.24 is cited with the
triangles exchanged, DEF as its first triangle and ABC as its second. The
Lean has no helper of its own.
-/

namespace Elements.BookI

open Tacit

/-- If two triangles have the two sides equal to two sides respectively, but have the base greater
than the base, they will also have the one of the angles contained by the equal straight lines
greater than the other. -/
theorem Prop25 {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
    (hAB : ‖A B‖ = ‖D E‖) (hAC : ‖A C‖ = ‖D F‖) (h : ‖E F‖ < ‖B C‖) :
    ∠ E D F < ∠ B A C := by
  -- Let ABC, DEF be two triangles having the two sides AB, AC equal to the two sides DE, DF
  -- respectively, namely AB to DE, and AC to DF; and let the base BC be greater than the base
  -- EF;
  -- I say that the angle BAC is also greater than the angle EDF.
  -- For, if not, it is either equal to it or less.
  /- That an angle not greater than another is equal to it or less is the tacit
     rule of magnitude `lt_trichotomy` (System E §3.5). -/
  have either : ¬ ∠ E D F < ∠ B A C → ∠ B A C = ∠ E D F ∨ ∠ B A C < ∠ E D F := by
    intro hnot
    rcases lt_trichotomy (∠ B A C) (∠ E D F) with hlt | heq | hgt
    · exact Or.inr hlt
    · exact Or.inl heq
    · exact absurd hgt hnot
  -- Now the angle BAC is not equal to the angle EDF;
  have not_equal : ∠ B A C ≠ ∠ E D F := by
    intro hA
    -- for then the base BC would also have been equal to the base EF, [I. 4]
    /- I.4 gives the bases equal, the triangles equal and the remaining angles
       equal; only the first is wanted here. -/
    have hBC_EF : ‖B C‖ = ‖E F‖ := (Prop4 hABC hDEF hAB hAC hA).1
    -- but it is not;
    /- It is greater, and a magnitude is not equal to one it is greater than
       (`Magnitude.ne_of_lt`). -/
    have hne : ‖B C‖ ≠ ‖E F‖ := fun heq => Magnitude.ne_of_lt h heq.symm
    -- therefore the angle BAC is not equal to the angle EDF.
    exact hne hBC_EF
  -- Neither again is the angle BAC less than the angle EDF;
  have not_less : ¬ ∠ B A C < ∠ E D F := by
    intro hA
    -- for then the base BC would also have been less than the base EF, [I. 24]
    /- This is I.24 with the triangles exchanged: in DEF the angle at D is
       now the greater, and its sides DE, DF are equal to AB, AC, the
       equalities read the other way round. -/
    have hBC_EF : ‖B C‖ < ‖E F‖ := Prop24 hDEF hABC hAB.symm hAC.symm hA
    -- but it is not;
    /- It is greater, and a magnitude cannot be both less and greater than
       another (`lt_trans`, `lt_irrefl`). -/
    have hnot : ¬ ‖B C‖ < ‖E F‖ := fun hlt => lt_irrefl _ (lt_trans hlt h)
    -- therefore the angle BAC is not less than the angle EDF.
    exact hnot hBC_EF
  -- But it was proved that it is not equal either;
  /- Both ways out are closed; Euclid's division is complete. -/
  have neither : ¬ (∠ B A C = ∠ E D F ∨ ∠ B A C < ∠ E D F) := fun hor =>
    hor.elim not_equal not_less
  -- therefore the angle BAC is greater than the angle EDF.
  /- Reductio ad absurdum: were the angle BAC not greater, the division above
     would make it equal or less, and it is neither. -/
  exact Classical.byContradiction fun hnot => neither (either hnot)
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookI
