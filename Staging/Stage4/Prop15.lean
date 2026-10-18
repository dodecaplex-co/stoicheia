import Staging.Stage4.Foot
import Staging.Stage4.Prop14

/-!
# Staging: III.15, its two clauses for every straight line in the circle

Brief 0006, stage 4. Companions of `Elements.BookIII.Prop15`, which stays as Euclid's
worked configuration: a diameter AD and two straight lines BC, FG, neither through the
centre. His enunciation has two clauses. "The diameter is greatest" is
`Prop15.le_diameter`, for every straight line in the circle, with its equality case: no
straight line is greater than the diameter, and only one through the centre is equal to it.
"Of the rest the nearer to the centre is always greater than the more remote" is
`Prop15.nearer`, with distances measured to the feet of the perpendiculars (`Foot`), so that
the nearer may be a diameter. They move into `Elements/BookIII/Prop15.lean` when proved, as
"III.15 le_diameter" and "III.15 nearer".
-/

namespace Elements.BookIII

open Tacit

/-- **III.15, the diameter is greatest** (companion of III.15). Of the straight lines in a
circle, none is greater than the diameter AD, and a straight line BC in it is equal to the
diameter exactly when it passes through the centre E: when it is a diameter too. If BC is
not through the centre, BE, EC together are greater than BC [I. 20], and they are equal to
AD. BC may be a point, and then it is nothing. -/
theorem Prop15.le_diameter {A B C D E : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hD : OnCircle D ABCD) (hAED : Between A E D)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) :
    ‖B C‖ ≤ ‖A D‖ ∧ (‖B C‖ = ‖A D‖ ↔ Between B E C) := by
  have hAD_sum : ‖A D‖ = ‖B E‖ + ‖E C‖ :=
    Prop14.diameter_sum hE hA hD hB hC hAED
  by_cases hBC : B = C
  · /- BC is a point: its length is nothing, and E cannot lie between its equal ends. -/
    subst C
    rw [len_self]
    refine ⟨not_lt_zero _, ?_⟩
    exact ⟨fun h => False.elim (len_ne_zero (ne_of_between_ends hAED) h.symm),
      fun h => False.elim (ne_of_between_ends h rfl)⟩
  · by_cases hE_BC : Collinear B C E
    · /- BC passes through E: it too is a diameter, equal to the same two radii. -/
      obtain ⟨L, hB_L, hC_L, hE_L⟩ := hE_BC
      have hBEC : Between B E C :=
        between_of_inside_chord hE_L hB_L hC_L (centre_inside hE) hB hC hBC
      have hBC_AD : ‖B C‖ = ‖A D‖ := (len_add_of_between hBEC).symm.trans hAD_sum.symm
      refine ⟨?_, ⟨fun _ => hBEC, fun _ => hBC_AD⟩⟩
      rw [hBC_AD]
      exact lt_irrefl _
    · /- BC does not pass through E: BE and EC together exceed BC by I.20. -/
      have hBC_AD : ‖B C‖ < ‖A D‖ := by
        rw [hAD_sum]
        exact (BookI.Prop20 (Triangle.cab hE_BC)).1
      have hnot_between : ¬ Between B E C := by
        intro hBEC
        obtain ⟨L, hB_L, hE_L, hC_L⟩ := collinear_of_between hBEC
        exact hE_BC ⟨L, hB_L, hC_L, hE_L⟩
      exact ⟨fun h => lt_irrefl _ (lt_trans hBC_AD h),
        ⟨fun h => False.elim (Magnitude.ne_of_lt hBC_AD h),
          fun h => False.elim (hnot_between h)⟩⟩

/-- **III.15, the nearer is greater** (companion of III.15). Of two straight lines BC, FG in
a circle, the one nearer to the centre E is the greater: if EH is less than EK, H and K being
the feet of the perpendiculars from E, then FG is less than BC. The nearer, BC, may be a
diameter, at no distance; the more remote cannot be. (Nor can FG be a point: its foot would
be E, and EK nothing.) -/
theorem Prop15.nearer {B C E F G H K : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hF : OnCircle F ABCD)
    (hG : OnCircle G ABCD) (hBC : B ≠ C) (hH : Foot E B C H) (hK : Foot E F G K)
    (hnearer : ‖E H‖ < ‖E K‖) :
    ‖F G‖ < ‖B C‖ := by
  /- FG cannot pass through E, even with coincident ends: its foot would be E. -/
  have hE_FG : ¬ Collinear F G E := by
    intro h
    have hK_E : K = E := hK.2.1 h
    rw [hK_E, len_self] at hnearer
    exact not_lt_zero _ hnearer
  by_cases hE_BC : Collinear B C E
  · /- BC is a diameter. The diameter bound is strict for FG, which does not pass through E. -/
    obtain ⟨L, hB_L, hC_L, hE_L⟩ := hE_BC
    have hBEC : Between B E C :=
      between_of_inside_chord hE_L hB_L hC_L (centre_inside hE) hB hC hBC
    obtain ⟨hbound, hequal⟩ := Prop15.le_diameter hE hB hC hBEC hF hG
    have hunequal : ‖F G‖ ≠ ‖B C‖ := by
      intro h
      obtain ⟨M, hF_M, hE_M, hG_M⟩ := collinear_of_between (hequal.mp h)
      exact hE_FG ⟨M, hF_M, hG_M, hE_M⟩
    rcases lt_trichotomy ‖F G‖ ‖B C‖ with h | h | h
    · exact h
    · exact False.elim (hunequal h)
    · exact False.elim (hbound h)
  · /- Neither straight line passes through E. Draw a diameter and use III.15's argument. -/
    have hB_E : B ≠ E := ne_of_centre_of_on hE hB
    obtain ⟨L, hE_L, hB_L⟩ := Postulate1 E B hB_E.symm
    obtain ⟨A, hA, -, hAEB⟩ := line_circle_beyond (centre_inside hE) hE_L hB_L hB_E
    exact (Prop15 hE hA hB hAEB hB hC hF hG hE_BC hE_FG
      hH.1 (hH.2.2 hE_BC) hK.1 (hK.2.2 hE_FG) hnearer).2

/-- The check: today's statement of III.15 follows from `Prop15.le_diameter` and
`Prop15.nearer` (checked by Lean). BC is not through the centre, so it is less than the
diameter. -/
example : type_of% @Elements.BookIII.Prop15 := by
  intro A B C D E F G H K ABCD hE hA hD hAED hB hC hF hG hE_BC hE_FG hH hEH hK hEK hnearer
  obtain ⟨hle, hiff⟩ := Prop15.le_diameter hE hA hD hAED hB hC
  refine ⟨?_, Prop15.nearer hE hB hC hF hG (Triangle.ne₁₂ hE_BC)
    ⟨hH, fun h => absurd h hE_BC, fun _ => hEH⟩ ⟨hK, fun h => absurd h hE_FG, fun _ => hEK⟩
    hnearer⟩
  have hne : ‖B C‖ ≠ ‖A D‖ := fun h => by
    obtain ⟨L, hB_L, hE_L, hC_L⟩ := collinear_of_between (hiff.mp h)
    exact hE_BC ⟨L, hB_L, hC_L, hE_L⟩
  rcases lt_trichotomy ‖B C‖ ‖A D‖ with h | h | h
  · exact h
  · exact absurd h hne
  · exact absurd h hle

end Elements.BookIII
