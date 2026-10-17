import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Prop01
import Elements.BookIII.Prop18

/-!
# Book III, Proposition 19

Euclid's text, in Heath's translation: [`heath/III/19.md`](../../heath/III/19.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If a straight line touch a circle, and from the point of contact a straight line be drawn at
right angles to the tangent, the centre of the circle will be on the straight line so drawn. -/
theorem Prop19 {A C D E : Point} {ABC : Circle} (hC : OnCircle C ABC) (hDE : Touches D E ABC)
    (hCDE : Collinear D E C) (hA : ¬ Collinear D E A)
    (hCA : ∀ P : Point, Collinear D E P → P ≠ C → ∠ A C P = ∟) :
    ∀ F : Point, Centre F ABC → Collinear A C F := by
  -- For let a straight line DE touch the circle ABC at the point C, and from C let CA be drawn
  -- at right angles to DE;
  obtain ⟨L, hD_L, hE_L⟩ := Postulate1 D E hDE.1
  have hC_L : OnLine C L := by
    obtain ⟨M, h1, h2, h3⟩ := hCDE
    exact (line_unique hDE.1 h1 h2 hD_L hE_L) ▸ h3
  have hA_L : ¬ OnLine A L := fun h => hA ⟨L, hD_L, hE_L, h⟩
  /- Euclid's E, in the angles FCE and ACE, is a point of DE other than C. Here it is
     `E₁`: E itself, or D when C is E. -/
  obtain ⟨E₁, hE₁_L, hE₁C⟩ : ∃ E₁ : Point, OnLine E₁ L ∧ E₁ ≠ C := by
    by_cases hCE : C = E
    · exact ⟨D, hD_L, fun e => hDE.1 (e.trans hCE)⟩
    · exact ⟨E, hE_L, Ne.symm hCE⟩
  -- I say that the centre of the circle is on AC.
  intro F hF
  -- For suppose it is not, but, if possible, let F be the centre,
  refine Classical.byContradiction fun hF_AC => ?_
  -- and let CF be joined.
  have hF_L : ¬ OnLine F L := fun h => hDE.not_inside ⟨L, hD_L, hE_L, h⟩ (centre_inside hF)
  -- Since a straight line DE touches the circle ABC,
  -- and FC has been joined from the centre to the point of contact,
  -- FC is perpendicular to DE; [III. 18]
  have h18 := Prop18 hF hC hDE hCDE
  -- therefore the angle FCE is right.
  have hFCE : ∠ F C E₁ = ∟ := h18 E₁ ⟨L, hD_L, hE_L, hE₁_L⟩ hE₁C
  -- But the angle ACE is also right;
  have hACE : ∠ A C E₁ = ∟ := hCA E₁ ⟨L, hD_L, hE_L, hE₁_L⟩ hE₁C
  -- therefore the angle FCE is equal to the angle ACE,
  have hFCE_ACE : ∠ F C E₁ = ∠ A C E₁ := hFCE.trans hACE.symm
  -- the less to the greater: which is impossible.
  /- At C only one straight line is at right angles to DE, as in III.1
     (`Prop1.perpendicular`), so F lies on CA, on whichever side of DE it falls. -/
  have hFC : F ≠ C := fun e => hF_L (e ▸ hC_L)
  have hAC : A ≠ C := fun e => hA_L (e ▸ hC_L)
  have hE₁CA : ∠ E₁ C A = ∟ := by rw [angle_symm hE₁C hAC]; exact hACE
  have hE₁CF : ∠ E₁ C F = ∟ := by rw [angle_symm hE₁C hFC, hFCE_ACE]; exact hACE
  obtain ⟨N, hC_N, hA_N, hF_N⟩ := Prop1.perpendicular (Triangle.of_line hE₁_L hC_L hE₁C hA_L)
    (Triangle.of_line hE₁_L hC_L hE₁C hF_L) hE₁CA hE₁CF
  exact hF_AC ⟨N, hA_N, hC_N, hF_N⟩
  -- Therefore F is not the centre of the circle ABC.
  -- Similarly we can prove that neither is any other point except a point on AC.
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
