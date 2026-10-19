import Elements.BookIII.Prop07

/-!
# Staging: III.7, nearer and more remote on either side of the diameter

Brief 0007, stage 4b. A companion of `Elements.BookIII.Prop7`, which stays as Euclid's
worked configuration: there the nearer and the more remote are compared only when both lie
on one side of the diameter AD. His enunciation says "of the rest the nearer to the
straight line through the centre is always greater than the more remote", of any two.
`Prop7.general` compares any two straight lines from F whose ends are off the diameter, on
one side or on opposite sides. "Nearer" is the less angle with the ray FA at F, the ray
through the centre E: the angle AFB, unsigned and less than two right angles, and an
obtuse angle is not exchanged for its acute supplement. The ends A and D on the diameter
are the greatest and the least clauses' business, and the comparison leaves them out.

F is taken strictly within the diameter, between the centre E and the end D, as in
today's statement: Euclid's words "a point … which is not the centre" are read of a point
inside the circle, since F at an end of the diameter would make the least straight line
nothing. The order E, F, D only names the ends: the end beyond F from the centre is D.

`Prop7.partner` is the step the route needs: a straight line from F and its equal partner
on the other side of the diameter are equally inclined to FA. Euclid's I.4 step, which
makes FH equal to FG, makes the angles at F equal too; Heath reads the comparison across
the diameter from it (vol. 2, p. 17). They move into `Elements/BookIII/Prop07.lean` when
proved, as "III.7 general", with `Prop7.partner` as a helper before it.
-/

namespace Elements.BookIII

open Tacit

/-- **III.7, the partner equally inclined** (a step of III.7 general). F is on the diameter
AD of the circle ABCD with centre E, between E and D; if G and H are points of the circle on
opposite sides of AD, and FH is equal to FG, then the angles AFH and AFG are equal, so the
partner of a straight line from F makes the same angle with the ray FA. Euclid's
construction of H, the angle FEH made equal to GEF (I.23), gives the equal angles at F by
I.4, and his last step shows that no other point is H. -/
theorem Prop7.partner {A D E F G H : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hD : OnCircle D ABCD) (hAED : Between A E D) (hEFD : Between E F D)
    (hG : OnCircle G ABCD) (hH : OnCircle H ABCD) (hHG : OppositeSidesOf H G A D)
    (hFH : ‖F H‖ = ‖F G‖) :
    ∠ A F H = ∠ A F G := by
  have hAD : A ≠ D := ne_of_between_ends hAED
  obtain ⟨L, hA_L, hD_L⟩ := Postulate1 A D hAD
  have hE_L : OnLine E L := on_line_of_between_ends hAED hA_L hD_L
  have hF_L : OnLine F L := on_line_of_between_ends hEFD hE_L hD_L
  have hEF : E ≠ F := ne_of_between hEFD
  have hG_L : ¬ OnLine G L := (hHG.oppositeSides hA_L hD_L).2.1
  have hEFG : Triangle E F G := Triangle.of_line hE_L hF_L hEF hG_L
  /- On EF at E make the angle FEH' equal to GEF, on the other side from G. -/
  obtain ⟨P, hPG, -⟩ := exists_point_opposite_side hG_L []
  have hP_EF : ¬ Collinear E F P := Triangle.of_line hE_L hF_L hEF hPG.1
  obtain ⟨X, F', hF', hX, hang⟩ := BookI.Prop23 hEF hEFG.cab hP_EF
  obtain ⟨N, hE_N, hX_N⟩ := Postulate1 E X hX.triangle.ne₁₃
  obtain ⟨Q, hXEQ⟩ := produce hX.triangle.ne₁₃.symm
  have hQ_N : OnLine Q N := on_line_of_between hXEQ hX_N hE_N
  obtain ⟨H', hH', -, hH'EQ⟩ :=
    line_circle_beyond (centre_inside hE) hE_N hQ_N
      (ne_of_between (between_symm hXEQ))
  have hH'_ray : OnRay H' E X :=
    OnRay.of_between_between (between_symm hXEQ) (between_symm hH'EQ)
  have hH'G_EF : OppositeSidesOf H' G E F :=
    (SameSideOf.of_onRay hH'_ray hX).trans_opposite
      (OppositeSidesOf.of_line hEF hE_L hF_L hPG)
  have hH'G : OppositeSidesOf H' G A D :=
    OppositeSidesOf.of_line hAD hA_L hD_L (hH'G_EF.oppositeSides hE_L hF_L)
  have hFEH' : ∠ F E H' = ∠ G E F :=
    (angle_eq_of_onRay hF'.symm hH'_ray).trans
      ((angle_symm hF'.2.1 hX.triangle.ne₁₃.symm).trans hang)
  have hEH'F : Triangle E H' F := hH'G_EF.triangle.acb
  have hGEF : ∠ G E F = ∠ H' E F :=
    hFEH'.symm.trans (angle_symm hEF.symm hEH'F.ne₁₂.symm)
  /- I.4 gives both the equal bases and the equal angles at F. -/
  have h4 := BookI.Prop4 hEFG.acb hEH'F (Definition15 hE hG hH') rfl hGEF
  have hFH' : ‖F H'‖ = ‖F G‖ := by
    rw [len_symm F H', len_symm F G]
    exact h4.1.symm
  have hEray : OnRay E F A := OnRay.of_between (between_symm (between_cut hAED hEFD))
  have hangle : ∠ A F H' = ∠ A F G := by
    rw [← angle_onRay_left hEray hEH'F.ne₂₃,
      ← angle_onRay_left hEray hEFG.ne₂₃.symm]
    exact h4.2.2.2.symm
  /- H and H' are both the unique partner of G on the other side of AD. -/
  obtain ⟨J, -, -, -, hunique⟩ := (Prop7 hE hA hD hAED hEFD).2.2.2 G hG hHG.symm.triangle
  have hHG_ne : H ≠ G := by
    intro e
    have hs := hHG.oppositeSides hA_L hD_L
    exact hs.2.2 (e ▸ same_side_refl hs.1)
  have hH'G_ne : H' ≠ G := by
    intro e
    have hs := hH'G.oppositeSides hA_L hD_L
    exact hs.2.2 (e ▸ same_side_refl hs.1)
  have hHJ : H = J := (hunique H hH hFH).resolve_left hHG_ne
  have hH'J : H' = J := (hunique H' hH' hFH').resolve_left hH'G_ne
  exact (hHJ.trans hH'J.symm) ▸ hangle

/-- **III.7, general** (companion of III.7). F is on the diameter AD of the circle ABCD with
centre E, strictly between E and D, so not the centre. Of the straight lines from F to the
circle, FA, the one through the centre, is greater than every other; FD, the rest of the
diameter, is less than every other. Of any two straight lines FB, FC whose ends B, C are off
the diameter, on one side of it or on opposite sides, the one making the less angle with the
ray FA at F is the greater: if the angle AFB is less than the angle AFC, then FC is less than
FB. Each point G of the circle off the diameter has one partner H on the other side with FH
equal to FG, and no third point of the circle is as far from F. -/
theorem Prop7.general {A D E F : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hD : OnCircle D ABCD) (hAED : Between A E D) (hEFD : Between E F D) :
    (∀ B : Point, OnCircle B ABCD → B ≠ A → ‖F B‖ < ‖F A‖) ∧
    (∀ G : Point, OnCircle G ABCD → G ≠ D → ‖F D‖ < ‖F G‖) ∧
    (∀ B C : Point, OnCircle B ABCD → OnCircle C ABCD → ¬ Collinear A D B →
      ¬ Collinear A D C → ∠ A F B < ∠ A F C → ‖F C‖ < ‖F B‖) ∧
    (∀ G : Point, OnCircle G ABCD → ¬ Collinear A D G → ∃ H : Point, OnCircle H ABCD ∧
      OppositeSidesOf H G A D ∧ ‖F H‖ = ‖F G‖ ∧
      ∀ K : Point, OnCircle K ABCD → ‖F K‖ = ‖F G‖ → K = G ∨ K = H) := by
  obtain ⟨hgreatest, hleast, hnearer, hpartner⟩ := Prop7 hE hA hD hAED hEFD
  refine ⟨hgreatest, hleast, ?_, hpartner⟩
  intro B C hB hC hB_AD hC_AD hlt
  by_cases hBC : SameSideOf B C A D
  · exact hnearer B C hB hC hBC hlt
  /- Move C to its partner H on B's side of AD. -/
  have hAD : A ≠ D := ne_of_between_ends hAED
  obtain ⟨L, hA_L, hD_L⟩ := Postulate1 A D hAD
  have hBC' : OppositeSidesOf B C A D :=
    OppositeSidesOf.of_line hAD hA_L hD_L
      ⟨fun h => hB_AD ⟨L, hA_L, hD_L, h⟩,
        fun h => hC_AD ⟨L, hA_L, hD_L, h⟩,
        fun hs => hBC (SameSideOf.of_line hAD hA_L hD_L hs)⟩
  obtain ⟨H, hH, hHC, hFH, -⟩ := hpartner C hC hC_AD
  have hBH : SameSideOf B H A D := OppositeSidesOf.sameSideOf hBC'.symm hHC.symm
  have hang : ∠ A F H = ∠ A F C := Prop7.partner hE hA hD hAED hEFD hC hH hHC hFH
  have hlt' : ∠ A F B < ∠ A F H := by rw [hang]; exact hlt
  have hless := hnearer B H hB hH hBH hlt'
  rwa [hFH] at hless

/-- The check: today's statement of III.7 follows from `Prop7.general` (checked by Lean).
Two points on one side of AD are off it. -/
example : type_of% @Elements.BookIII.Prop7 := by
  intro A D E F ABCD hE hA hD hAED hEFD
  obtain ⟨hgreatest, hleast, hnearer, hpartner⟩ := Prop7.general hE hA hD hAED hEFD
  exact ⟨hgreatest, hleast, fun B C hB hC hBC hlt =>
    hnearer B C hB hC hBC.triangle hBC.symm.triangle hlt, hpartner⟩

end Elements.BookIII
