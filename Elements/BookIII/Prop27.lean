import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop23
import Elements.BookIII.Prop02
import Elements.BookIII.Prop20
import Elements.BookIII.Prop26

/-!
# Book III, Proposition 27

Euclid's text, in Heath's translation: [`heath/III/27.md`](../../heath/III/27.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- In equal circles angles standing on equal circumferences are equal to one another, whether they
stand at the centres or at the circumferences. -/
theorem Prop27 {A B C D E F G H : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hF : OnCircle F DEF) (hBAC : Triangle B A C) (hEDF : Triangle E D F)
    (heq : standing ABC B A C = standing DEF E D F) :
    ∠ B A C = ∠ E D F ∧
      (SameSideOf G A B C → SameSideOf H D E F → ∠ B G C = ∠ E H F) := by
  -- For in equal circles ABC, DEF, on equal circumferences BC, EF, let the angles BGC, EHF
  -- stand at the centres G, H, and the angles BAC, EDF at the circumferences;
  -- I say that the angle BGC is equal to the angle EHF,
  -- and the angle BAC is equal to the angle EDF.
  have centres : SameSideOf G A B C → SameSideOf H D E F → ∠ B G C = ∠ E H F := by
    intro hGA hHD
    /- We name the circumferences BC, EF by points Q, R beyond them, across BC from A and
       across EF from D; the centres lie on the sides of A and D. -/
    obtain ⟨Q, hQA, -⟩ := exists_oppositeSidesOf hBAC.acb []
    obtain ⟨R, hRD, -⟩ := exists_oppositeSidesOf hEDF.acb []
    have hBC : circumference ABC B Q C = circumference DEF E R F := by
      rw [← standing_eq_circumference hQA.symm, ← standing_eq_circumference hRD.symm]
      exact heq
    have hGQ : OppositeSidesOf G Q B C := hGA.trans_opposite hQA.symm
    have hHR : OppositeSidesOf H R E F := hHD.trans_opposite hRD.symm
    -- For, if the angle BGC is unequal to the angle EHF,
    -- one of them is greater.
    /- Either circle may have the greater angle. As in I.26, we write the reductio once and
       use it with the circles named either way round. -/
    have greater : ∀ {B C E F G H Q R : Point} {ABC DEF : Circle}, EqualCircles ABC DEF →
        Centre G ABC → Centre H DEF → OnCircle B ABC → OnCircle C ABC → OnCircle E DEF →
        OnCircle F DEF → OppositeSidesOf G Q B C → OppositeSidesOf H R E F →
        circumference ABC B Q C = circumference DEF E R F → ∠ E H F < ∠ B G C → False := by
      intro B C E F G H Q R ABC DEF hcircles hG hH hB hC hE hF hGQ hHR hBC hlt
      -- Let the angle BGC be greater; and on the straight line BG, and at the point G on it, let
      -- the angle BGK be constructed equal to the angle EHF. [I. 23]
      have hGB : G ≠ B := (ne_of_centre_of_on hG hB).symm
      obtain ⟨K', B', hB', hK'C, hK'GB'⟩ := BookI.Prop23 hGB hHR.triangle.acb hGQ.triangle.cab
      /- I.23 gives only the direction of GK. We take K on that ray at the distance GB
         from G, and System E, Diagram-segment 3, puts it on the given circle. -/
      have hK'G : K' ≠ G := hK'C.triangle.ne₁₃.symm
      obtain ⟨K, hK_ray, hGK⟩ := OnRay.exists_len_eq hGB hK'G.symm
      have hK : OnCircle K ABC := on_circle_of_len_eq hG hB hGK
      have hBGK : ∠ B G K = ∠ E H F := by
        rw [angle_onRay_right hK_ray hGB.symm, ← angle_onRay_left hB' hK'G]
        exact (angle_symm hB'.2.1 hK'G).trans hK'GB'
      have hGBK : Triangle G B K := (SameSideOf.of_onRay hK_ray hK'C).triangle
      -- Now equal angles stand on equal circumferences, when they are at the centres; [III. 26]
      /- For III.26 we name the circumference BK by a point P beyond it, and take a point of
         each circle on the centre's side. -/
      obtain ⟨P, hPG, -⟩ := exists_oppositeSidesOf hGBK.bca []
      obtain ⟨X, hX, hXG⟩ := Prop2.sameSide hB hK hGBK.bca
      obtain ⟨Y, hY, hYH⟩ := Prop2.sameSide hE hF hHR.triangle
      -- therefore the circumference BK is equal to the circumference EF.
      have hBK : circumference ABC B P K = circumference DEF E R F :=
        ((Prop26 hcircles hG hH hX hB hK hY hE hF (hXG.trans_opposite hPG.symm)
          (hYH.trans_opposite hHR)).1 hPG.symm hHR hBGK).1
      -- But EF is equal to BC;
      have hEF_BC := hBC.symm
      -- therefore BK is also equal to BC, the less to the greater: which is impossible.
      have h := hBK.trans hEF_BC
      rw [Circumference.centre hG hB hK hPG.symm, Circumference.centre hG hB hC hGQ,
        hBGK] at h
      rw [h] at hlt
      exact lt_irrefl _ hlt
    -- Therefore the angle BGC is not unequal to the angle EHF;
    -- therefore it is equal to it.
    rcases lt_trichotomy (∠ B G C) (∠ E H F) with h | h | h
    · exact (greater hcircles.symm hH hG hE hF hB hC hHR hGQ hBC.symm h).elim
    · exact h
    · exact (greater hcircles hG hH hB hC hE hF hGQ hHR hBC h).elim
  have hAD : ∠ B A C = ∠ E D F := by
    by_cases hGH : SameSideOf G A B C ∧ SameSideOf H D E F
    rotate_left
    · /- Our statement also covers right and obtuse angles at the circumference,
         where no angle at the centre in Euclid's sense stands on the same
         circumference. There the circumference is twice the angle standing on it
         (`Circumference.standing`), and halves of equal things are equal. -/
      rw [Circumference.standing ⟨G, hG⟩ hA hB hC hBAC.acb,
        Circumference.standing ⟨H, hH⟩ hD hE hF hEDF.acb] at heq
      exact Magnitude.eq_of_add_self_eq heq
    -- And the angle at A is half of the angle BGC,
    have h20A := Prop20 hG hA hB hC hGH.1
    -- and the angle at D half of the angle EHF; [III. 20]
    have h20D := Prop20 hH hD hE hF hGH.2
    -- therefore the angle at A is also equal to the angle at D.
    exact Magnitude.eq_of_add_self_eq
      (h20A.symm.trans ((centres hGH.1 hGH.2).trans h20D))
  -- Therefore etc.
  exact ⟨hAD, centres⟩
  -- Q. E. D.

end Elements.BookIII
