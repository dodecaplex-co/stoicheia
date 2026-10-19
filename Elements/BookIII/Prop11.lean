import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop20
import Elements.BookIII.Prop02
import Elements.BookIII.Prop06

/-!
# Book III, Proposition 11

Euclid's text, in Heath's translation: [`heath/III/11.md`](../../heath/III/11.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- A point not outside a circle is within it or on it. Euclid reads the points of
the inner circle this way when placing its centre within the outer circle. -/
theorem Prop11.not_outside {P : Point} {α : Circle} (h : ¬ OutsideCircle P α) :
    InsideCircle P α ∨ OnCircle P α := by
  exact Classical.byContradiction fun h' =>
    h ⟨fun hi => h' (Or.inl hi), fun ho => h' (Or.inr ho)⟩

/-- If two circles touch one another internally, and their centres be taken, the straight line
joining their centres, if it be also produced, will fall on the point of contact of the circles. -/
theorem Prop11 {A F G : Point} {ABC ADE : Circle} (hF : Centre F ABC) (hG : Centre G ADE)
    (htouch : TouchesInternally ABC ADE A) :
    Between F G A := by
  -- For let the two circles ABC, ADE touch one another internally at the point A, and let the
  -- centre F of the circle ABC, and the centre G of ADE, be taken;
  /- By III.6 the centres differ, so FG is a straight line. -/
  have hFG : F ≠ G := fun e => Prop6 (Or.inl htouch) ⟨hF, e ▸ hG⟩
  obtain ⟨hA₁, hA₂, -, hwithin⟩ := htouch
  -- I say that the straight line joined from G to F and produced will fall on A.
  -- For suppose it does not, but, if possible, let it fall as FGH, and let AF, AG be joined.
  have hnot : ¬ ¬ Between F G A := by
    intro hFGA
    obtain ⟨L, hF_L, hG_L⟩ := Postulate1 F G hFG
    /- The inner centre is within the outer circle: it lies between two points
       of the inner circle, neither of which is outside the outer. -/
    have hGA : G ≠ A := (ne_of_centre_of_on hG hA₂).symm
    obtain ⟨M, hG_M, hA_M⟩ := Postulate1 G A hGA
    obtain ⟨Q, hQ, -, hQGA⟩ :=
      line_circle_beyond (centre_inside hG) hG_M hA_M hGA.symm
    have hG_in : InsideCircle G ABC :=
      Prop2.within ⟨F, hF⟩ (Prop11.not_outside (hwithin Q hQ)) (Or.inr hA₁) hQGA
    obtain ⟨H, hH, hH_L, hHGF⟩ := line_circle_beyond hG_in hG_L hF_L hFG
    have hFGH : Between F G H := between_symm hHGF
    have hAH : A ≠ H := fun e => hFGA (e ▸ hFGH)
    -- Then, since AG, GF are greater than FA, that is, than FH,
    have h20 : ‖F A‖ < ‖F G‖ + ‖G A‖ := by
      by_cases hA_L : OnLine A L
      · /- A lies on GF produced beyond F, a case Heath says Euclid would have left to
           the reader (vol. 2, p. 26). Here AG is AF and FG together, so it already
           exceeds AF. -/
        have hAFH : Between A F H :=
          between_of_inside_chord hF_L hA_L hH_L (centre_inside hF) hA₁ hH hAH
        have hAFG : Between A F G := between_cut hAFH hFGH
        have hFA_GA : ‖F A‖ < ‖G A‖ := by
          rw [len_symm F A, len_symm G A, ← len_add_of_between hAFG]
          exact CommonNotion5 (len_pos hFG)
        exact lt_trans hFA_GA (by rw [add_comm]; exact CommonNotion5 (len_pos hFG))
      · exact (BookI.Prop20 (Triangle.of_line hG_L hF_L hFG.symm hA_L)).1
    rw [Definition15 hF hA₁ hH] at h20
    -- let FG be subtracted from each;
    rw [← len_add_of_between hFGH] at h20
    -- therefore the remainder AG is greater than the remainder GH.
    have hGH_GA : ‖G H‖ < ‖G A‖ := Magnitude.lt_of_add_lt_add_left h20
    -- But AG is equal to GD;
    obtain ⟨D, hD, -, hDGF⟩ := line_circle_beyond (centre_inside hG) hG_L hF_L hFG
    have hGA_GD : ‖G A‖ = ‖G D‖ := Definition15 hG hA₂ hD
    -- therefore GD is also greater than GH,
    have hGH_GD : ‖G H‖ < ‖G D‖ := hGA_GD ▸ hGH_GA
    -- the less than the greater: which is impossible.
    /- GD greater than GH puts D beyond H, outside ABC, which internal contact forbids; and
       since GD is greater, D is not H itself. -/
    have hGHD : Between G H D :=
      OnRay.between_of_len_lt (OnRay.self (ne_of_between hHGF).symm)
        (OnRay.of_between_between hFGH (between_symm hDGF)) hGH_GD
    have hFGD : Between F G D := between_of_between_right hFGH hGHD
    have hFD : ‖F H‖ < ‖F D‖ := by
      rw [← len_add_of_between hFGH, ← len_add_of_between hFGD,
        add_comm (‖F G‖), add_comm (‖F G‖)]
      exact add_lt_add_right _ hGH_GD
    exact hwithin D hD (outside_of_len_gt hF hH hFD)
  -- Therefore the straight line joined from F to G will not fall outside;
  -- therefore it will fall at A on the point of contact.
  exact Classical.byContradiction hnot
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
