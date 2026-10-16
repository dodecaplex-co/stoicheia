import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop05
import Elements.BookI.Prop08
import Elements.BookI.Prop26
import Elements.BookI.Helpers

/-!
# Book III, Proposition 3

Euclid's text, in Heath's translation: [`heath/III/03.md`](../../heath/III/03.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If in a circle a straight line through the centre bisect a straight line not through the centre,
it also cuts it at right angles; and if it cut it at right angles, it also bisects it. -/
theorem Prop3 {A B E F : Point} {ABC : Circle} (hE : Centre E ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hAFB : Between A F B) (hE_AB : ¬ Collinear A B E) :
    (‖A F‖ = ‖F B‖ → ∠ A F E = ∟ ∧ ∠ B F E = ∟) ∧ (∠ A F E = ∟ → ‖A F‖ = ‖F B‖) := by
  -- Let ABC be a circle, and in it let a straight line CD through the centre bisect a straight
  -- line AB not through the centre at the point F;
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B (ne_of_between_ends hAFB)
  have hF_L : OnLine F L := on_line_of_between_ends hAFB hA_L hB_L
  have hE_L : ¬ OnLine E L := (show Triangle A B E from hE_AB).off_line hA_L hB_L
  -- I say that it also cuts it at right angles.
  -- For let the centre of the circle ABC be taken, and let it be E; let EA, EB be joined.
  have hFAE : Triangle F A E := Triangle.of_line hF_L hA_L (ne_of_between hAFB).symm hE_L
  have hFBE : Triangle F B E :=
    Triangle.of_line hF_L hB_L (ne_of_between (between_symm hAFB)).symm hE_L
  refine ⟨fun hAF => ?_, fun hAFE => ?_⟩
  · /- The first part. -/
    -- Then, since AF is equal to FB,
    -- and FE is common,
    have hFE : ‖F E‖ = ‖F E‖ := rfl
    -- two sides are equal to two sides;
    have hFA : ‖F A‖ = ‖F B‖ := by rw [len_symm F A, hAF]
    -- and the base EA is equal to the base EB;
    have hEA : ‖E A‖ = ‖E B‖ := Definition15 hE hA hB
    -- therefore the angle AFE is equal to the angle BFE. [I. 8]
    have h8 : ∠ A F E = ∠ B F E :=
      BookI.Prop8 hFAE hFBE hFA hFE (by rw [len_symm A E, len_symm B E, hEA])
    -- But, when a straight line set up on a straight line makes the adjacent angles equal to one
    -- another, each of the equal angles is right; [I. Def. 10]
    have hright : IsRightAngle A F E :=
      ⟨B, hAFB, hFAE.bac, h8.trans (angle_symm hFBE.ne₁₂.symm hFBE.ne₁₃.symm)⟩
    -- therefore each of the angles AFE, BFE is right.
    have hAFE : ∠ A F E = ∟ := Postulate4 hright
    -- Therefore CD, which is through the centre, and bisects AB which is not through the centre,
    -- also cuts it at right angles.
    exact ⟨hAFE, h8 ▸ hAFE⟩
  -- Again, let CD cut AB at right angles;
  -- I say that it also bisects it, that is, that AF is equal to FB.
  · /- The converse. -/
    -- For, with the same construction,
    -- since EA is equal to EB,
    have hEA : ‖E A‖ = ‖E B‖ := Definition15 hE hA hB
    -- the angle EAF is also equal to the angle EBF. [I. 5]
    have h5 : ∠ E A B = ∠ E B A :=
      BookI.Prop5.base (show Triangle A B E from hE_AB).cab hEA
    have hEAF : ∠ E A F = ∠ E B F := by
      rw [angle_onRay_right (OnRay.of_between hAFB) hFAE.ne₂₃.symm,
        angle_onRay_right (OnRay.of_between (between_symm hAFB)) hFBE.ne₂₃.symm]
      exact h5
    -- But the right angle AFE is equal to the right angle BFE,
    have hadj : ∠ A F E = ∠ E F B := adjacent_eq_of_right hA_L hB_L hAFB hE_L hAFE
    have hEFA : ∠ E F A = ∠ E F B :=
      (angle_symm hFAE.ne₁₃.symm hFAE.ne₁₂.symm).trans hadj
    -- therefore EAF, EBF are two triangles having two angles equal to two angles and one side
    -- equal to one side, namely EF, which is common to them, and subtends one of the equal
    -- angles;
    have hFAE_FBE : ∠ F A E = ∠ F B E := by
      rw [angle_symm hFAE.ne₁₂ hFAE.ne₂₃.symm,
        angle_symm hFBE.ne₁₂ hFBE.ne₂₃.symm]
      exact hEAF
    -- therefore they will also have the remaining sides equal to the remaining sides; [I. 26]
    have h26 := BookI.Prop26 hFAE.cab hFBE.cab hEFA hFAE_FBE (Or.inr rfl)
    -- therefore AF is equal to FB.
    exact (len_symm A F).trans h26.2.2.1
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
