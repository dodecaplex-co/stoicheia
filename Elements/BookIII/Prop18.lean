import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop12
import Elements.BookI.Prop17
import Elements.BookI.Prop19

/-!
# Book III, Proposition 18

Euclid's text, in Heath's translation: [`heath/III/18.md`](../../heath/III/18.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If a straight line touch a circle, and a straight line be joined from the centre to the point of
contact, the straight line so joined will be perpendicular to the tangent. -/
theorem Prop18 {C D E F : Point} {ABC : Circle} (hF : Centre F ABC) (hC : OnCircle C ABC)
    (hDE : Touches D E ABC) (hCDE : Collinear D E C) :
    ∀ P : Point, Collinear D E P → P ≠ C → ∠ F C P = ∟ := by
  -- For let a straight line DE touch the circle ABC at the point C, let the centre F of the
  -- circle ABC be taken, and let FC be joined from F to C;
  /- The centre is within the circle, and no point of DE is, so F is off DE. -/
  have hF_DE : ¬ Collinear D E F := fun h => hDE.not_inside h (centre_inside hF)
  obtain ⟨L, hD_L, hE_L⟩ := Postulate1 D E hDE.1
  have hC_L : OnLine C L := by
    obtain ⟨M, hD_M, hE_M, hC_M⟩ := hCDE
    exact (line_unique hDE.1 hD_M hE_M hD_L hE_L) ▸ hC_M
  have hF_L : ¬ OnLine F L := fun h => hF_DE ⟨L, hD_L, hE_L, h⟩
  -- I say that FC is perpendicular to DE.
  -- For, if not, let FG be drawn from F perpendicular to DE.
  obtain ⟨G, hG, hFG⟩ := BookI.Prop12 hDE.1 hF_DE
  have hG_L : OnLine G L := by
    obtain ⟨M, hD_M, hE_M, hG_M⟩ := hG
    exact (line_unique hDE.1 hD_M hE_M hD_L hE_L) ▸ hG_M
  have hGC : G = C := Classical.byContradiction fun hGC => by
    -- Then, since the angle FGC is right,
    have hFGC : ∠ F G C = ∟ := hFG C hCDE (Ne.symm hGC)
    -- the angle FCG is acute; [I. 17]
    have hT : Triangle F G C := (Triangle.of_line hG_L hC_L hGC hF_L).bca.bca
    have hacute : ∠ G C F < ∟ := by
      have h17 := (BookI.Prop17 hT).1
      rw [hFGC] at h17
      exact Magnitude.lt_of_add_lt_add_left h17
    -- and the greater angle is subtended by the greater side; [I. 19]
    -- therefore FC is greater than FG.
    have hFG_FC : ‖F G‖ < ‖F C‖ := BookI.Prop19 hT (by rw [hFGC]; exact hacute)
    -- But FC is equal to FB;
    /- B is where FG leaves the circle, for G is outside it: DE has no point within
       the circle (`Touches.not_inside`), and meets it at C alone. -/
    have hG_out : OutsideCircle G ABC :=
      ⟨hDE.not_inside hG, fun hG_on =>
        (hDE.2 L hD_L hE_L).2 ⟨C, G, Ne.symm hGC, hC_L, hC, hG_L, hG_on⟩⟩
    obtain ⟨M, hF_M, hG_M⟩ := Postulate1 F G (fun e => hF_L (e ▸ hG_L))
    obtain ⟨B, hB, -, hFBG⟩ := line_circle_between (centre_inside hF) hF_M hG_out hG_M
    have hFC_FB : ‖F C‖ = ‖F B‖ := Definition15 hF hC hB
    -- therefore FB is also greater than FG,
    have hFG_FB : ‖F G‖ < ‖F B‖ := hFC_FB ▸ hFG_FC
    -- the less than the greater: which is impossible.
    exact lt_irrefl _ (lt_trans hFG_FB (len_lt_of_between hFBG))
  -- Therefore FG is not perpendicular to DE.
  -- Similarly we can prove that neither is any other straight line except FC;
  -- therefore FC is perpendicular to DE.
  subst hGC
  exact hFG
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
