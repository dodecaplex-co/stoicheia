import Staging.Stage4.Foot

/-!
# Staging: III.14 with diameters

Brief 0006, stage 4. A companion of `Elements.BookIII.Prop14`, which stays as Euclid's
worked configuration: two straight lines in the circle, neither through the centre, each
with its perpendicular from the centre. His enunciation speaks of any straight lines in a
circle. `Prop14.general` takes each straight line's foot (`Foot`), so that a diameter, at
no distance from the centre, is included. It moves into `Elements/BookIII/Prop14.lean` when
proved, as "III.14 general".
-/

namespace Elements.BookIII

open Tacit

/-- A diameter is two radii together. This replaces its two parts by the radii to C and D
when comparing it with another straight line in the same circle. -/
theorem Prop14.diameter_sum {A B C D E : Point} {α : Circle} (hE : Centre E α)
    (hA : OnCircle A α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hD : OnCircle D α) (hAEB : Between A E B) :
    ‖A B‖ = ‖C E‖ + ‖E D‖ := by
  have hAE_CE : ‖A E‖ = ‖C E‖ :=
    (len_symm A E).trans ((Definition15 hE hA hC).trans (len_symm E C))
  have hEB_ED : ‖E B‖ = ‖E D‖ := Definition15 hE hB hD
  rw [← len_add_of_between hAEB, hAE_CE, hEB_ED]

/-- **III.14, general** (companion of III.14). In a circle, straight lines AB, CD are equal
exactly when they are equally distant from the centre E: EF and EG are equal, F and G being
the feet of the perpendiculars from E. Two straight lines not through the centre are
Euclid's case [III. 14]; two diameters are equal, and both at no distance; and of a diameter
and a straight line not through the centre, the diameter is the greater [I. 20], and the
other is at some distance from the centre. -/
theorem Prop14.general {A B C D E F G : Point} {ABDC : Circle} (hE : Centre E ABDC)
    (hA : OnCircle A ABDC) (hB : OnCircle B ABDC) (hC : OnCircle C ABDC)
    (hD : OnCircle D ABDC) (hAB : A ≠ B) (hCD : C ≠ D) (hF : Foot E A B F)
    (hG : Foot E C D G) :
    ‖A B‖ = ‖C D‖ ↔ ‖E F‖ = ‖E G‖ := by
  by_cases hE_AB : Collinear A B E
  · /- AB passes through E: its foot is E, and E lies between A and B, which are on the
       circle, so AB is a diameter, two radii together. -/
    have hF_E : F = E := hF.2.1 hE_AB
    obtain ⟨L, hA_L, hB_L, hE_L⟩ := hE_AB
    have hAEB : Between A E B :=
      between_of_inside_chord hE_L hA_L hB_L (centre_inside hE) hA hB hAB
    have hAB_sum : ‖A B‖ = ‖C E‖ + ‖E D‖ :=
      Prop14.diameter_sum hE hA hB hC hD hAEB
    by_cases hE_CD : Collinear C D E
    · /- Both straight lines are diameters: each is two radii, and both feet are E. -/
      have hG_E : G = E := hG.2.1 hE_CD
      obtain ⟨M, hC_M, hD_M, hE_M⟩ := hE_CD
      have hCED : Between C E D :=
        between_of_inside_chord hE_M hC_M hD_M (centre_inside hE) hC hD hCD
      have hAB_CD : ‖A B‖ = ‖C D‖ := hAB_sum.trans (len_add_of_between hCED)
      exact ⟨fun _ => by rw [hF_E, hG_E], fun _ => hAB_CD⟩
    · /- Only AB is a diameter: CD is shorter, and its foot is at some distance from E. -/
      have hCD_AB : ‖C D‖ < ‖A B‖ := by
        rw [hAB_sum]
        exact (BookI.Prop20 (Triangle.cab hE_CD)).1
      have hE_G : E ≠ G := fun h => hE_CD (h ▸ hG.1)
      have hdist : ‖E F‖ ≠ ‖E G‖ := by
        rw [hF_E, len_self]
        exact (len_ne_zero hE_G).symm
      exact ⟨fun h => False.elim (Magnitude.ne_of_lt hCD_AB h.symm),
        fun h => False.elim (hdist h)⟩
  · by_cases hE_CD : Collinear C D E
    · /- Only CD is a diameter: AB is shorter, and its foot is at some distance from E. -/
      have hG_E : G = E := hG.2.1 hE_CD
      obtain ⟨M, hC_M, hD_M, hE_M⟩ := hE_CD
      have hCED : Between C E D :=
        between_of_inside_chord hE_M hC_M hD_M (centre_inside hE) hC hD hCD
      have hCD_sum : ‖C D‖ = ‖A E‖ + ‖E B‖ :=
        Prop14.diameter_sum hE hC hD hA hB hCED
      have hAB_CD : ‖A B‖ < ‖C D‖ := by
        rw [hCD_sum]
        exact (BookI.Prop20 (Triangle.cab hE_AB)).1
      have hE_F : E ≠ F := fun h => hE_AB (h ▸ hF.1)
      have hdist : ‖E F‖ ≠ ‖E G‖ := by
        rw [hG_E, len_self]
        exact len_ne_zero hE_F
      exact ⟨fun h => False.elim (Magnitude.ne_of_lt hAB_CD h),
        fun h => False.elim (hdist h)⟩
    · /- Neither straight line passes through E: this is III.14's worked configuration. -/
      exact Prop14 hE hA hB hC hD hE_AB hE_CD hF.1 (hF.2.2 hE_AB)
        hG.1 (hG.2.2 hE_CD)

/-- The check: today's statement of III.14 follows from `Prop14.general` for two straight
lines not through the centre (checked by Lean). -/
example : type_of% @Elements.BookIII.Prop14 := by
  intro A B C D E F G ABDC hE hA hB hC hD hE_AB hE_CD hF hEF hG hEG
  exact Prop14.general hE hA hB hC hD (Triangle.ne₁₂ hE_AB) (Triangle.ne₁₂ hE_CD)
    ⟨hF, fun h => absurd h hE_AB, fun _ => hEF⟩ ⟨hG, fun h => absurd h hE_CD, fun _ => hEG⟩

end Elements.BookIII
