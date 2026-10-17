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
  /- A common centre and equal radii make one circle (System E, Diagram-segment 2).
     Contact within requires two circles; contact without forbids a point within both. -/
  have hsame : CDE = ABC := circle_eq hF₂ hF₁ hE hB hEB
  subst hsame
  rcases htouch with ⟨-, -, hne, -⟩ | ⟨-, -, hne, -⟩ | ⟨-, -, hout⟩
  · exact hne rfl
  · exact hne rfl
  · exact hout F (centre_inside hF₁) (centre_inside hF₁)
  -- Therefore F is not the centre of the circles ABC, CDE.
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
