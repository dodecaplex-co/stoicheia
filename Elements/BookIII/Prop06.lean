import Elements.Figure.Basics
import Elements.BookIII.Squares

/-!
# Book III, Proposition 6

Euclid's text, in Heath's translation: [`heath/III/06.md`](../../heath/III/06.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If two circles touch one another, they will not have the same centre. -/
theorem Prop6 {C F : Point} {ABC CDE : Circle} (htouch : CirclesTouch ABC CDE C) :
    ¬ (Centre F ABC ∧ Centre F CDE) := by
  -- For let the two circles ABC, CDE touch one another at the point C;
  have hC : OnCircle C ABC ∧ OnCircle C CDE := by
    rcases htouch with ⟨h₁, h₂, -⟩ | ⟨h₂, h₁, -⟩ | ⟨h₁, h₂, -⟩ <;> exact ⟨h₁, h₂⟩
  -- I say that they will not have the same centre.
  -- For, if possible, let it be F; let FC be joined, and let FEB be drawn through at random.
  rintro ⟨hF₁, hF₂⟩
  /- Contact without, which Euclid leaves to the reader, ends here: F would be within
     each circle, as a centre is (`centre_inside`), and circles touching without have no
     point within both. So the circles touch within, whichever is the inner, and are two. -/
  have hne : ABC ≠ CDE := by
    rcases htouch with ⟨-, -, hne, -⟩ | ⟨-, -, hne, -⟩ | ⟨-, -, hout⟩
    · exact hne
    · exact hne.symm
    · exact absurd (centre_inside hF₂) (hout F (centre_inside hF₁))
  /- FC is drawn for the eye; our proof uses only its ends. An unlettered point
     chooses the direction of FEB, which meets both circles beyond F. -/
  obtain ⟨X, hX⟩ := exists_point [F]
  have hXF : X ≠ F := fun h => hX (h ▸ List.mem_singleton_self F)
  obtain ⟨L, hF_L, hX_L⟩ := Postulate1 F X hXF.symm
  obtain ⟨B, hB, hB_L, hBFX⟩ := line_circle_beyond (centre_inside hF₁) hF_L hX_L hXF
  obtain ⟨E, hE, hE_L, hEFX⟩ := line_circle_beyond (centre_inside hF₂) hF_L hX_L hXF
  -- Then, since the point F is the centre of the circle ABC,
  -- FC is equal to FB.
  have hFB : ‖F C‖ = ‖F B‖ := Definition15 hF₁ hC.1 hB
  -- Again, since the point F is the centre of the circle CDE,
  -- FC is equal to FE.
  have hFE : ‖F C‖ = ‖F E‖ := Definition15 hF₂ hC.2 hE
  -- But FC was proved equal to FB;
  -- therefore FE is also equal to FB, the less to the greater: which is impossible.
  have hEB : ‖F E‖ = ‖F B‖ := hFE.symm.trans hFB
  /- That E and B are two points is the step Euclid leaves tacit, as in III.5. Were they
     one, the circles, about the one centre F, would pass through one point and be one
     circle (`circle_eq`); but circles touching within are two. -/
  have hEB_ne : E ≠ B := by
    rintro rfl
    exact hne (circle_eq hF₁ hF₂ hB hE rfl)
  /- E and B both lie beyond F from the unlettered point, so F is not between them, and
     one of them lies between F and the other. Euclid's figure has E the nearer; we take
     either order, and the nearer makes the less equal to the greater. -/
  have hnot : ¬ Between E F B :=
    not_between_of_between_between (between_symm hEFX) (between_symm hBFX)
  rcases between_cases (ne_of_between hEFX).symm hEB_ne (ne_of_between hBFX).symm
      hF_L hE_L hB_L with h | h | h
  · have hlt : ‖F E‖ < ‖F B‖ := len_lt_of_between h
    rw [hEB] at hlt
    exact lt_irrefl _ hlt
  · exact hnot h
  · have hlt : ‖F B‖ < ‖F E‖ := len_lt_of_between h
    rw [hEB] at hlt
    exact lt_irrefl _ hlt
  -- Therefore F is not the centre of the circles ABC, CDE.
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
