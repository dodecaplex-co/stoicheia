import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Prop02
import Elements.BookIII.Prop07
import Elements.BookIII.Prop08

/-!
# Book III: circles that cut one another, from two common points

Definition III.3 speaks of circles that cut one another, and our reading of it, `CirclesCut`
in `Elements/Foundations/DefinitionsIII.lean`, asks two things: that the circles meet at two
points, and that each passes within the other, a point of each being within the other. For
two different circles the first is enough, and here it is proved to give the second, with
no centre given (`CirclesCut.of_meet`). Euclid's III.10 supposes circles that cut; Heath
observes that its proof covers circles that only meet (vol. 2, p. 23), and so does our
statement. Its last step is III.5, which we state of circles that cut in this reading, and
this theorem is the step between.

A point of the circle α within β is found on the straight line through the centres, O of α
and O' of β, which the proof takes from the rule (`Tacit.exists_centre`). They are two
points, for one centre and a common point would make the circles one (`Tacit.circle_eq`).
The least straight line from O' to α lies along OO', by III.7 when O' is within α and by
III.8 when it is outside. Its end is neither common point, since both are on β and so
equally far from O'; it is nearer O' than they are, and so within β. When O' is on α, O'
itself is the point. So the step waits for III.7 and III.8, and comes before III.10, which
cites it. It cites III.2 as well, by `Prop2.within`, to order the points on the straight
line through the centres.
-/

namespace Elements

open Tacit BookIII

/-- Let B and C be distinct points common to two different circles α and β. A point of α
is within β. Take their centres O and O' from the rule; the end of α's diameter on the
line of the centres nearer O' supplies the point (III.7 when O' is within α, III.8 when
it is outside; O' itself when it is on α). -/
theorem CirclesCut.cut_point {α β : Circle} {B C : Point}
    (hne : α ≠ β) (hBC : B ≠ C) (hBα : OnCircle B α) (hBβ : OnCircle B β)
    (hCα : OnCircle C α) (hCβ : OnCircle C β) :
    ∃ P : Point, OnCircle P α ∧ InsideCircle P β := by
  obtain ⟨O, hO⟩ := exists_centre α
  obtain ⟨O', hO'⟩ := exists_centre β
  have hOO' : O ≠ O' := fun e => hne (circle_eq hO (e ▸ hO') hBα hBβ rfl)
  /- If the least line from O' to α ends at X, X is within β unless it is B; and if it is
     B, then C, also on α, is farther from O' than B, though both are on β. -/
  have finish : ∀ X : Point, OnCircle X α → (∀ K : Point, OnCircle K α → K ≠ X →
      ‖O' X‖ < ‖O' K‖) → ∃ P : Point, OnCircle P α ∧ InsideCircle P β := by
    intro X hX hleast
    by_cases hBX : B = X
    · subst hBX
      have h := hleast C hCα hBC.symm
      rw [Definition15 hO' hBβ hCβ] at h
      exact absurd h (lt_irrefl _)
    · exact ⟨X, hX, inside_of_len_lt hO' hBβ (hleast B hBα hBX)⟩
  by_cases hon : OnCircle O' α
  · exact ⟨O', hon, centre_inside hO'⟩
  by_cases hin : InsideCircle O' α
  · /- III.7 applies with O' on the diameter AD, between O and D. -/
    obtain ⟨L, hO_L, hO'_L⟩ := Postulate1 O O' hOO'
    obtain ⟨D, hD, -, hDO'O⟩ := line_circle_beyond hin hO'_L hO_L hOO'
    obtain ⟨A, hA, -, hAOO'⟩ := line_circle_beyond (centre_inside hO) hO_L hO'_L hOO'.symm
    have hOO'D : Between O O' D := between_symm hDO'O
    have hAOD : Between A O D := between_of_between_right hAOO' hOO'D
    exact finish D hD (Prop7 hO hA hD hAOD hOO'D).2.1
  · /- III.8 applies with O' outside α, G the nearer end of the diameter and A the farther. -/
    have hout : OutsideCircle O' α := ⟨hin, hon⟩
    obtain ⟨L, hO'_L, hO_L⟩ := Postulate1 O' O hOO'.symm
    obtain ⟨A, hA, hA_L, hAOO'⟩ := line_circle_beyond (centre_inside hO) hO_L hO'_L hOO'.symm
    have hAO : A ≠ O := ne_of_between hAOO'
    obtain ⟨G, hG, hG_L, hGOA⟩ := line_circle_beyond (centre_inside hO) hO_L hA_L hAO
    have hGO' : G ≠ O' := fun e => hon (e ▸ hG)
    have hGO : G ≠ O := ne_of_centre_of_on hO hG
    have hO'GO : Between O' G O := by
      rcases between_cases hGO'.symm hGO hOO'.symm hO'_L hG_L hO_L with h | h | h
      · exact h
      · exact absurd
          (Prop2.within (Or.inr hG) (Or.inl (centre_inside hO)) h) hin
      · exact absurd hGOA (not_between_of_between_between h (between_symm hAOO'))
    have hO'GA : Between O' G A := between_of_between_right hO'GO hGOA
    exact finish G hG (Prop8 hout hA hG hO'GA
      (fun M hM => centre_unique hM hO ▸ hGOA)).2.2.1

/-- Two different circles that meet at two points cut one another. -/
theorem CirclesCut.of_meet {α β : Circle}
    (hne : α ≠ β) (h : CirclesMeet α β) : CirclesCut α β := by
  obtain ⟨B, C, hBC, hBα, hBβ, hCα, hCβ⟩ := h
  exact ⟨⟨B, C, hBC, hBα, hBβ, hCα, hCβ⟩,
    cut_point hne hBC hBα hBβ hCα hCβ,
    cut_point (Ne.symm hne) hBC hBβ hBα hCβ hCα⟩

end Elements
