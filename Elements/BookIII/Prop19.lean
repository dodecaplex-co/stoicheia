import Elements.Figure.Basics
import Elements.BookIII.Squares
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
  /- Euclid's `E` is a point of `DE` other than `C`: `E` itself, or `D` when `C` is `E`. -/
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
  have hEq : ∠ E₁ C F = ∠ E₁ C A := by
    have hFC : F ≠ C := fun e => hF_L (e ▸ hC_L)
    have hAC : A ≠ C := fun e => hA_L (e ▸ hC_L)
    rw [angle_symm hE₁C hFC, angle_symm hE₁C hAC, hFCE, hACE]
  -- the less to the greater: which is impossible.
  /- One ray from `C` on `F`'s side of `DE` makes a right angle with it (`onRay_of_angle_eq`).
     Euclid's figure has `F` on `A`'s side; on the other side, `AC` produced to `A₁`. -/
  have hAC : A ≠ C := fun e => hA_L (e ▸ hC_L)
  obtain ⟨M, hA_M, hC_M⟩ := Postulate1 A C hAC
  apply hF_AC
  by_cases hs : SameSide F A L
  · obtain ⟨-, -, ⟨N, hC_N, hA_N, hF_N⟩, -⟩ :=
      onRay_of_angle_eq (SameSideOf.of_line hE₁C.symm hC_L hE₁_L hs) hEq
    exact ⟨N, hA_N, hC_N, hF_N⟩
  · obtain ⟨A₁, hA₁_M, hCA₁, -⟩ := Postulate2 hA_M hC_M hAC []
    have hE₁_M : ¬ OnLine E₁ M := fun h =>
      hA_L ((line_unique hE₁C.symm hC_M h hC_L hE₁_L) ▸ hA_M)
    have hA₁_L : ¬ OnLine A₁ L := fun h =>
      hA_L (on_line_of_between (between_symm hCA₁) h hC_L)
    have hadj := adjacent_eq_of_right hA_M hA₁_M hCA₁ hE₁_M hACE
    have hEq₁ : ∠ E₁ C F = ∠ E₁ C A₁ := by
      rw [hEq, angle_symm hE₁C hAC, hadj]
    have hFA₁ : SameSide F A₁ L := same_side_of_opposite_sides
      ⟨hA_L, hF_L, fun h => hs (same_side_symm h)⟩ ⟨hA_L, hA₁_L, pasch3 hCA₁ hC_L⟩
    obtain ⟨-, -, ⟨N, hC_N, hA₁_N, hF_N⟩, -⟩ :=
      onRay_of_angle_eq (SameSideOf.of_line hE₁C.symm hC_L hE₁_L hFA₁) hEq₁
    have hNM : N = M := line_unique (ne_of_between (between_symm hCA₁)).symm hC_N hA₁_N hC_M hA₁_M
    subst hNM
    exact ⟨N, hA_M, hC_N, hF_N⟩
  -- Therefore F is not the centre of the circle ABC.
  -- Similarly we can prove that neither is any other point except a point on AC.
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
