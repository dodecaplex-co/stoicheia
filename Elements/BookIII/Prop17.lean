import Elements.Figure.Basics
import Elements.Figure.Circles
import Elements.BookIII.Squares
import Elements.BookI.Prop04
import Elements.BookI.Prop11
import Elements.BookIII.Prop01
import Elements.BookIII.Prop16
import Elements.BookI.Prop13

/-!
# Book III, Proposition 17

Euclid's text, in Heath's translation: [`heath/III/17.md`](../../heath/III/17.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

`Prop17` is Euclid's worked configuration: the given point A outside the circle, and B the
point of contact. His enunciation says "a given point"; from a point within the circle no
straight line touches it, and a point on the circumference Euclid leaves to III.16's porism,
as Heath explains (vol. 2, p. 44). The companion after it, `Prop17.general`, takes every
point not within the circle: outside it, by Euclid's construction, or on it, where the
straight line drawn at right angles to the radius touches by III.16's porism.

The companion concludes `∃ X, Touches A X BCD`: a straight line AX touching the circle.
`Prop17`'s form, a point B of the circle with `Touches A B BCD`, cannot hold for A on the
circle, since the point of contact is then A itself and `Touches` (Definition III.2) asks for
two different points to name its straight line. `Touches` already says that the straight
line meets the circle, and its witness is the point of contact, which may be A;
`Touches.contact` reads it off.

Not being within the circle is the condition for the problem to have a solution, and
`Prop17.inside`, a lemma beside the proposition, states the other half: from a point within
the circle, no straight line touches it.
-/

namespace Elements.BookIII

open Tacit

/-- From a given point to draw a straight line touching a given circle. -/
theorem Prop17 {A : Point} {BCD : Circle} (hA : OutsideCircle A BCD) :
    ∃ B : Point, OnCircle B BCD ∧ Touches A B BCD := by
  -- Let A be the given point, and BCD the given circle;
  -- thus it is required to draw from the point A a straight line touching the circle BCD.
  -- For let the centre E of the circle be taken; [III. 1]
  /- The centre is found by III.1's construction, on a straight line drawn through the
     circle at random (`Prop1.of_circle`), as Euclid finds it. The proof keeps the centre
     alone, which is what Euclid takes from III.1. -/
  obtain ⟨-, -, E, -, -, -, -, -, hE, -⟩ := Prop1.of_circle BCD
  -- let AE be joined, and with centre E and distance EA let the circle AFG be described;
  have hEA : E ≠ A := fun e => hA.1 (e ▸ centre_inside hE)
  obtain ⟨L, hE_L, hA_L⟩ := Postulate1 E A hEA
  obtain ⟨D, hD, hD_L, hEDA⟩ := line_circle_between (centre_inside hE) hE_L hA hA_L
  obtain ⟨AFG, hE_AFG, hA_AFG⟩ := Postulate3 E A hEA
  -- from D let DF be drawn at right angles to EA,
  /- I.11 draws the perpendicular through D. Its point F' need not be on AFG, so we take F
     where the perpendicular, produced beyond D, meets that circle. -/
  have hED : E ≠ D := (ne_of_centre_of_on hE hD).symm
  obtain ⟨Q, hQ, -⟩ := exists_off_line hEA []
  obtain ⟨F', hF'Q, hF'⟩ := BookI.Prop11 hEA ⟨L, hE_L, hA_L, hD_L⟩ hQ
  have hF'_L : ¬ OnLine F' L := hF'Q.triangle.off_line hE_L hA_L
  have hEDF' : ∠ E D F' = ∟ := hF' E ⟨L, hE_L, hA_L, hE_L⟩ hED
  have hDF' : D ≠ F' := fun e => hF'_L (e ▸ hD_L)
  obtain ⟨N, hD_N, hF'_N⟩ := Postulate1 D F' hDF'
  have hD_in : InsideCircle D AFG :=
    InsideCircle.of_between_centre hE_AFG hA_AFG hEDA
  obtain ⟨F, hF, hF_N, hFDF'⟩ :=
    line_circle_beyond hD_in hD_N hF'_N hDF'.symm
  have hE_N : ¬ OnLine E N := fun h =>
    hF'_L ((line_unique hED h hD_N hE_L hD_L) ▸ hF'_N)
  have hF_L : ¬ OnLine F L := fun h =>
    hF'_L ((line_unique (ne_of_between hFDF').symm hD_N hF_N hD_L h) ▸ hF'_N)
  -- and let EF, AB be joined;
  /- F is farther from E than D is, so EF leaves BCD at B between E and F. -/
  have hEF : E ≠ F := fun e => hE_N (e ▸ hF_N)
  have hED_EF : ‖E D‖ < ‖E F‖ := by
    rw [← Definition15 hE_AFG hA_AFG hF]
    exact len_lt_of_inside hE_AFG hA_AFG hD_in
  have hF_out : OutsideCircle F BCD := outside_of_len_gt hE hD hED_EF
  obtain ⟨M, hE_M, hF_M⟩ := Postulate1 E F hEF
  obtain ⟨B, hB, hB_M, hEBF⟩ :=
    line_circle_between (centre_inside hE) hE_M hF_out hF_M
  have hB_L : ¬ OnLine B L := fun h =>
    hF_L ((line_unique (ne_of_between hEBF) hE_M hB_M hE_L h) ▸ hF_M)
  have hEAB : Triangle E A B := Triangle.of_line hE_L hA_L hEA hB_L
  have hEFD : Triangle E F D := (Triangle.of_line hE_L hD_L hED hF_L).acb
  obtain ⟨K, hA_K, hB_K⟩ := Postulate1 A B hEAB.ne₂₃
  -- I say that AB has been drawn from the point A touching the circle BCD.
  -- For, since E is the centre of the circles BCD, AFG,
  -- EA is equal to EF, and ED to EB;
  have hEAEF : ‖E A‖ = ‖E F‖ := Definition15 hE_AFG hA_AFG hF
  have hEDEB : ‖E D‖ = ‖E B‖ := Definition15 hE hD hB
  -- therefore the two sides AE, EB are equal to the two sides FE, ED;
  have hEB_ED : ‖E B‖ = ‖E D‖ := hEDEB.symm
  -- and they contain a common angle, the angle at E;
  have hcommon : ∠ A E B = ∠ F E D := by
    rw [angle_onRay_right (OnRay.of_between hEBF) hEA.symm,
      angle_symm hEA.symm hEF.symm,
      angle_onRay_right (OnRay.of_between hEDA) hEF.symm]
  -- therefore the base DF is equal to the base AB,
  -- and the triangle DEF is equal to the triangle BEA,
  -- and the remaining angles to the remaining angles; [I. 4]
  obtain ⟨-, -, -, hEBA_EDF⟩ := BookI.Prop4 hEAB hEFD hEAEF hEB_ED hcommon
  -- therefore the angle EDF is equal to the angle EBA.
  have hEDF_EBA : ∠ E D F = ∠ E B A := hEBA_EDF.symm
  -- But the angle EDF is right;
  /- F lies on the other side of D from F'; the angle adjacent to a right angle
     is right (I.13, `adjacent_eq_of_right`). -/
  have hEDF : ∠ E D F = ∟ := by
    have hF'DE : ∠ F' D E = ∟ := by
      rw [angle_symm hDF'.symm hED]
      exact hEDF'
    rw [← adjacent_eq_of_right hF'_N hF_N (between_symm hFDF') hE_N hF'DE, hF'DE]
  -- therefore the angle EBA is also right.
  have hEBA : ∠ E B A = ∟ := hEDF_EBA.symm.trans hEDF
  -- Now EB is a radius;
  -- and the straight line drawn at right angles to the diameter of a circle, from its
  -- extremity, touches the circle; [III. 16, Por.]
  have hBA : Touches B A BCD := Prop16.porism hE hB hEAB.acb hEBA
  -- therefore AB touches the circle BCD.
  have hAB : Touches A B BCD :=
    hBA.of_collinear ⟨K, hB_K, hA_K, hA_K⟩ ⟨K, hB_K, hA_K, hB_K⟩ hEAB.ne₂₃
  -- Therefore from the given point A the straight line AB has been drawn touching the circle
  -- BCD.
  exact ⟨B, hB, hAB⟩
  -- Q. E. F.

/-- **III.17, general** (companion of III.17). Given a circle BCD and a point
A not within it, there is a point X such that the straight line AX touches the circle: it
meets the circle, and does not cut it. A may be outside the circle, and then the point of
contact is another point (Euclid's case, `Prop17`); or on it, and then the point of
contact is A itself: the proof draws AX at right angles to the radius EA (I.11), and it
touches by III.16's porism. Euclid leaves that case out, Heath explains, because III.16's
porism so directly indicates its construction (vol. 2, p. 44); the construction is not on
Euclid's page. -/
theorem Prop17.general {A : Point} {BCD : Circle}
    (hA : ¬ InsideCircle A BCD) :
    ∃ X : Point, Touches A X BCD := by
  by_cases hon : OnCircle A BCD
  · /- A is on the circle. Its centre E, found by III.1's construction as in `Prop17`
       (`Prop1.of_circle`), is within it, so E is not A. -/
    obtain ⟨-, -, E, -, -, -, -, -, hE, -⟩ := Prop1.of_circle BCD
    have hEA : E ≠ A := (ne_of_centre_of_on hE hon).symm
    obtain ⟨L, hE_L, hA_L⟩ := Postulate1 E A hEA
    /- Choose Q off EA, then draw AX at right angles to EA on Q's side by I.11. -/
    obtain ⟨Q, hQ, -⟩ := exists_off_line hEA []
    obtain ⟨X, hXQ, hX⟩ := BookI.Prop11 hEA ⟨L, hE_L, hA_L, hA_L⟩ hQ
    have hEAX : ∠ E A X = ∟ := hX E ⟨L, hE_L, hA_L, hE_L⟩ hEA
    /- X is off EA, since it lies on Q's side; AX touches the circle by III.16's porism. -/
    exact ⟨X, Prop16.porism hE hon hXQ.triangle hEAX⟩
  · /- A is outside the circle, so III.17 gives its point of contact B. -/
    obtain ⟨B, -, hB⟩ := Prop17 ⟨hA, hon⟩
    exact ⟨B, hB⟩

/-- **III.17, from a point within** (a lemma beside III.17). From a point A within the
circle BCD, no point X makes the straight line AX touch the circle, since a straight line
through a point within a circle cuts it (`Touches.not_inside`). So a point not within it is
exactly the condition under which `Prop17.general` draws a straight line touching it. -/
theorem Prop17.inside {A : Point} {BCD : Circle} (hA : InsideCircle A BCD) :
    ¬ ∃ X : Point, Touches A X BCD := by
  rintro ⟨X, hAX⟩
  /- A lies on AX, and no point of a straight line that touches a circle lies within it. -/
  obtain ⟨L, hA_L, hX_L⟩ := Postulate1 A X hAX.1
  exact hAX.not_inside ⟨L, hA_L, hX_L, hA_L⟩ hA

/-- The check: the statement of `Prop17` follows from `Prop17.general` (checked by Lean).
A is outside the circle, so the point where AX meets the circle is not A, and the straight
line it names with A is AX. -/
example : type_of% @Elements.BookIII.Prop17 := by
  intro A BCD hA
  obtain ⟨X, hAX, hX⟩ := Prop17.general hA.1
  obtain ⟨L, hA_L, hX_L⟩ := Postulate1 A X hAX
  obtain ⟨⟨B, hB_L, hB⟩, -⟩ := hX L hA_L hX_L
  have hAB : A ≠ B := fun e => hA.2 (e ▸ hB)
  refine ⟨B, hB, hAB, fun M hA_M hB_M => ?_⟩
  obtain rfl : L = M := line_unique hAB hA_L hB_L hA_M hB_M
  exact hX L hA_L hX_L

end Elements.BookIII
