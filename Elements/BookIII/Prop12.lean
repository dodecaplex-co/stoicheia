import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop20
import Elements.BookIII.Prop06

/-!
# Book III, Proposition 12

Euclid's text, in Heath's translation: [`heath/III/12.md`](../../heath/III/12.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- Each centre is outside the other circle when no point is within both.
If the centre lay on the other circle, a point sufficiently near it towards
the other centre would be within both. -/
theorem Prop12.centre_outside {A F G : Point} {α β : Circle}
    (hF : Centre F α) (hG : Centre G β) (hA : OnCircle A α) (hFG : F ≠ G)
    (hout : ∀ P, InsideCircle P α → ¬ InsideCircle P β) : OutsideCircle F β := by
  refine ⟨hout F (centre_inside hF), ?_⟩
  intro hF_on
  obtain ⟨P, hFPG, hP⟩ := exists_between_nearer (O := F) (C := A) hFG (Or.inl rfl)
    (by rw [len_self]; exact len_pos (ne_of_centre_of_on hF hA).symm)
  exact hout P (inside_of_len_lt hF hA hP)
    (InsideCircle.of_between_centre hG hF_on (between_symm hFPG))

/-- If two circles touch one another externally, the straight line joining their centres will pass
through the point of contact. -/
theorem Prop12 {A F G : Point} {ABC ADE : Circle} (hF : Centre F ABC) (hG : Centre G ADE)
    (htouch : TouchesExternally ABC ADE A) :
    Between F A G := by
  -- For let the two circles ABC, ADE touch one another externally at the point A, and let the
  -- centre F of ABC, and the centre G of ADE, be taken;
  /- As in III.11, the centres differ by III.6, so FG is a straight line. -/
  have hFG : F ≠ G := fun e => Prop6 (Or.inr (Or.inr htouch)) ⟨hF, e ▸ hG⟩
  obtain ⟨hA₁, hA₂, hout⟩ := htouch
  have hFA : F ≠ A := (ne_of_centre_of_on hF hA₁).symm
  have hGA : G ≠ A := (ne_of_centre_of_on hG hA₂).symm
  obtain ⟨L, hF_L, hG_L⟩ := Postulate1 F G hFG
  -- I say that the straight line joined from F to G will pass through the point of contact at
  -- A.
  -- For suppose it does not, but, if possible, let it pass as FCDG, and let AF, AG be joined.
  have hnot : ¬ ¬ Between F A G := by
    intro hFAG
    /- If A lay on FG produced, one centre would be within both circles. -/
    have hA_L : ¬ OnLine A L := by
      intro hA_L
      rcases between_cases hFA hGA.symm hFG hF_L hA_L hG_L with h | h | h
      · exact hFAG h
      · exact hout F (centre_inside hF)
          (InsideCircle.of_between_centre hG hA₂ (between_symm h))
      · exact hout G (InsideCircle.of_between_centre hF hA₁ h)
          (centre_inside hG)
    obtain ⟨C, hC, -, hFCG⟩ := line_circle_between (centre_inside hF) hF_L
      (Prop12.centre_outside hG hF hA₂ hFG.symm (fun P h₁ h₂ => hout P h₂ h₁)) hG_L
    obtain ⟨D, hD, -, -⟩ := line_circle_between (centre_inside hG) hG_L
      (Prop12.centre_outside hF hG hA₁ hFG hout) hF_L
    -- Then, since the point F is the centre of the circle ABC,
    -- FA is equal to FC.
    have h1 : ‖F A‖ = ‖F C‖ := Definition15 hF hA₁ hC
    -- Again, since the point G is the centre of the circle ADE,
    -- GA is equal to GD.
    have h2 : ‖G A‖ = ‖G D‖ := Definition15 hG hA₂ hD
    -- But FA was also proved equal to FC;
    -- therefore FA, AG are equal to FC, GD,
    have h3 : ‖F A‖ + ‖A G‖ = ‖F C‖ + ‖G D‖ := by
      rw [h1, len_symm A G, h2]
    -- so that the whole FG is greater than FA, AG;
    /- C cannot be within ADE: a point of CF sufficiently near C would be
       within both circles. C and D may be one point, so "not less" suffices. -/
    have hC_out : ¬ ‖G C‖ < ‖G A‖ := by
      intro h
      obtain ⟨P, hCPF, hP⟩ :=
        exists_between_nearer (O := G) (C := A) (ne_of_between hFCG).symm
          (Or.inr (between_symm hFCG)) h
      exact hout P (InsideCircle.of_between_centre hF hC (between_symm hCPF))
        (inside_of_len_lt hG hA₂ hP)
    have h4 : ‖F A‖ + ‖A G‖ ≤ ‖F G‖ := by
      intro h
      rw [h3, ← len_add_of_between hFCG] at h
      have hlt := Magnitude.lt_of_add_lt_add_left h
      rw [len_symm C G, ← h2] at hlt
      exact hC_out hlt
    -- but it is also less [I. 20]: which is impossible.
    exact h4 (BookI.Prop20 (Triangle.of_line hF_L hG_L hFG hA_L).cab).1
  -- Therefore the straight line joined from F to G will not fail to pass through the point of
  -- contact at A;
  -- therefore it will pass through it.
  exact Classical.byContradiction hnot
  -- Therefore etc.
  -- Q. E. D.]

end Elements.BookIII
