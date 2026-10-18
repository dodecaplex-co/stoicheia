import Elements.Figure.Basics
import Elements.BookI.Prop07

/-!
# Stage 3, staged: placement, only one place

Statements before proofs (brief 0006, stage 3). One file of `Elements/BookIII/Placement/`.

A point is fixed by its distances from C and D together with whether it is on F's side of
CD or on CD: on one side, by I.7; on the straight line, by the order of points on it. (A
point on the side and a point on the line cannot share both distances: that is
`Prop20.collinear_congr`, used in the assembly.)
-/

namespace Elements.BookIII

open Tacit

/-- **Only one place off the base.** Two points on F's side of CD, equally far from C and
equally far from D, are one point. This is I.7 itself. -/
theorem Placement.unique_off {C D F Q₁ Q₂ : Point} (hQ₁ : SameSideOf Q₁ F C D)
    (hQ₂ : SameSideOf Q₂ F C D) (hC : ‖C Q₁‖ = ‖C Q₂‖) (hD : ‖D Q₁‖ = ‖D Q₂‖) : Q₁ = Q₂ :=
  BookI.Prop7 (hQ₁.trans hQ₂.symm) (by rw [len_symm Q₁ C, hC, len_symm C Q₂])
    (by rw [len_symm Q₁ D, hD, len_symm D Q₂])

/-- **Only one place on the base.** Two points of the straight line CD, equally far from C
and equally far from D, are one point.

To be proved from the order of points on a straight line: on one ray from C only one point
lies at a given distance (`OnRay.eq_of_len_eq`), and two points on opposite rays from C at
the same distance are told apart by their distances from D (`len_add_of_between`). -/
theorem Placement.unique_on {C D Q₁ Q₂ : Point} (hCD : C ≠ D) (hQ₁ : Collinear C D Q₁)
    (hQ₂ : Collinear C D Q₂) (hC : ‖C Q₁‖ = ‖C Q₂‖) (hD : ‖D Q₁‖ = ‖D Q₂‖) : Q₁ = Q₂ := by
  /- If Q₁ is C, then CQ₂ is nothing, and Q₂ is C too. -/
  by_cases hQ₁C : Q₁ = C
  · subst Q₁
    exact eq_of_len_eq_zero (hC.symm.trans (len_self C))
  /- Otherwise neither point is C, and both lie on the one straight line CD. -/
  have hQ₂C : Q₂ ≠ C := (ne_of_len_eq hC.symm (Ne.symm hQ₁C)).symm
  obtain ⟨L, hCL, hDL, hQ₁L⟩ := hQ₁
  have hQ₂L : OnLine Q₂ L := by
    obtain ⟨M, hCM, hDM, hQ₂M⟩ := hQ₂
    exact line_unique hCD hCM hDM hCL hDL ▸ hQ₂M
  by_cases hbetween : Between Q₁ C Q₂
  · /- On the ray CD, DQ is less than DC and CQ together, wherever Q falls. -/
    have shorter {Q : Point} (hQ : OnRay Q C D) : ‖D Q‖ < ‖D C‖ + ‖C Q‖ := by
      by_cases hQD : Q = D
      · /- Q at D: DQ is nothing. -/
        subst Q
        rw [len_self]
        exact lt_trans (len_pos hCD.symm) (CommonNotion5 (len_pos hCD))
      have hQL : OnLine Q L := hQ.onLine hCL hDL
      rcases between_cases hQ.2.1.symm hQD hCD hCL hQL hDL with h | h | h
      · /- Q lies between C and D, so DQ is already less than DC. -/
        exact lt_trans (len_lt_of_between (between_symm h))
          (CommonNotion5 (len_pos hQ.2.1.symm))
      · /- C cannot lie between Q and D, for Q is on the ray CD. -/
        exact False.elim (hQ.2.2.2 h)
      · /- Q lies beyond D, so DQ is less than CQ. -/
        have hpart : ‖D Q‖ < ‖C Q‖ := by
          simpa only [len_symm Q D, len_symm Q C] using
            len_lt_of_between (between_symm h)
        have hwhole : ‖C Q‖ < ‖D C‖ + ‖C Q‖ := by
          rw [add_comm]
          exact CommonNotion5 (len_pos hCD.symm)
        exact lt_trans hpart hwhole
    /- D lies on one of the two rays. The distance to the point on the other
       ray is DC and CQ together, and is therefore the greater distance. -/
    rcases OnRay.cases_of_between hbetween hQ₁L hQ₂L hDL hCD.symm with hD₁ | hD₂
    · have hfar : Between D C Q₂ := between_symm (hD₁.between (between_symm hbetween))
      have hlt := shorter hD₁.symm
      rw [hC, len_add_of_between hfar] at hlt
      exact False.elim (Magnitude.ne_of_lt hlt hD)
    · have hfar : Between D C Q₁ := between_symm (hD₂.between hbetween)
      have hlt := shorter hD₂.symm
      rw [← hC, len_add_of_between hfar] at hlt
      exact False.elim (Magnitude.ne_of_lt hlt hD.symm)
  · /- On one ray from C, equal distances give the same point. -/
    exact OnRay.eq_of_len_eq ⟨hQ₂C.symm, hQ₁C, ⟨L, hCL, hQ₂L, hQ₁L⟩, hbetween⟩ hC

end Elements.BookIII
