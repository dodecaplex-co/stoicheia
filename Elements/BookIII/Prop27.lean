import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop23
import Elements.BookIII.Prop02
import Elements.BookIII.Prop20
import Elements.BookIII.Prop22
import Elements.BookIII.Prop24
import Elements.BookIII.Prop26

/-!
# Book III, Proposition 27

Euclid's text, in Heath's translation: [`heath/III/27.md`](../../heath/III/27.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

The proof is Euclid's: his reductio makes the angles at the centres equal, and his halving,
"the angle at A is half of the angle BGC" [III. 20], makes those at the circumferences equal.
It is written once, for any points of the circles on the centres' sides. Where the angles at
A and D are acute, as in his figure, it runs at A and D themselves. Where they are obtuse,
we pass to the circumferences that remain, as III.26 passes to "the circumference BKC which
remains". The angles standing on them at points of the circles on the centres' sides are
acute, and Euclid's argument makes those equal. Then III.22 leaves the angles at A and D as
what remains of two right angles, after Heath, who says that his remarks on III.26's cases
"apply here also" (vol. 2, p. 59). Where the angles are right, the centres lie
on BC and EF, and there are no angles BGC, EHF of ours, for our angles are never straight;
the angle at the centre is then two right angles (`angleAtCentre.semicircle`), but the
proof does not halve it: each angle is an angle in a semicircle, and right. `Prop24.angle_type` reads that off the measure of the circumference,
so in this case alone the angles are read off the measure. `Prop27.sides` sorts the three
cases: equal circumferences put the centres alike. Nothing here uses
`Circumference.standing`.
-/

namespace Elements.BookIII

open Tacit

/-- **Equal circumferences put the centres alike.** When the circumferences on which the
angles BAC, EDF stand are equal, the centres G, H lie both on the sides of A and D, or both
on BC and EF, or both beyond BC and EF from A and D. Euclid's figure has the first, in both
circles. Named by points Q, R beyond BC and EF from A and D, the circumferences are less
than semicircles when the centres lie on the sides of A and D, semicircles when the centres
are on BC and EF, and greater when the centres lie beyond BC and EF from A and D
(`Circumference.lt_semicircle`, `Circumference.semicircle`, `Circumference.gt_semicircle`);
so centres placed differently would make the equal circumferences unequal. The cases are sorted by `Prop24.angle_type`.
[I. 5, I. 32, III. 2, III. 20, III. 21, III. 22] -/
theorem Prop27.sides {A B C D E F G H : Point} {ABC DEF : Circle} (hG : Centre G ABC)
    (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hC : OnCircle C ABC)
    (hD : OnCircle D DEF) (hE : OnCircle E DEF) (hF : OnCircle F DEF)
    (hBCA : Triangle B C A) (hEFD : Triangle E F D)
    (heq : standing ABC B A C = standing DEF E D F) :
    (SameSideOf G A B C ∧ SameSideOf H D E F) ∨ (Between B G C ∧ Between E H F) ∨
      (OppositeSidesOf G A B C ∧ OppositeSidesOf H D E F) := by
  obtain ⟨Q, hQA, -⟩ := exists_oppositeSidesOf hBCA []
  obtain ⟨R, hRD, -⟩ := exists_oppositeSidesOf hEFD []
  have hBC : circumference ABC B Q C = circumference DEF E R F := by
    rw [← standing_eq_circumference hQA.symm, ← standing_eq_circumference hRD.symm]
    exact heq
  /- The size of the circumference BC, as G falls; and of EF, as H falls. -/
  have lt₁ : SameSideOf G A B C → circumference DEF E R F < ∟ + ∟ := fun h => by
    rw [← hBC]; exact Circumference.lt_semicircle hG hB hC (h.trans_opposite hQA.symm)
  have eq₁ : Between B G C → circumference DEF E R F = ∟ + ∟ := fun h => by
    rw [← hBC]; exact Circumference.semicircle hG hB hC h hQA.triangle
  have gt₁ : OppositeSidesOf G A B C → ∟ + ∟ < circumference DEF E R F := fun h => by
    rw [← hBC]
    exact Circumference.gt_semicircle hG hB hC (OppositeSidesOf.sameSideOf h.symm hQA.symm)
  have lt₂ : SameSideOf H D E F → circumference DEF E R F < ∟ + ∟ := fun h =>
    Circumference.lt_semicircle hH hE hF (h.trans_opposite hRD.symm)
  have eq₂ : Between E H F → circumference DEF E R F = ∟ + ∟ := fun h =>
    Circumference.semicircle hH hE hF h hRD.triangle
  have gt₂ : OppositeSidesOf H D E F → ∟ + ∟ < circumference DEF E R F := fun h =>
    Circumference.gt_semicircle hH hE hF (OppositeSidesOf.sameSideOf h.symm hRD.symm)
  rcases Prop24.angle_type hG hB hC hA hBCA with ⟨hGA, -⟩ | ⟨hBGC, -⟩ | ⟨hGA, -⟩ <;>
    rcases Prop24.angle_type hH hE hF hD hEFD with ⟨hHD, -⟩ | ⟨hEHF, -⟩ | ⟨hHD, -⟩
  · exact Or.inl ⟨hGA, hHD⟩
  · have h := lt₁ hGA; rw [eq₂ hEHF] at h; exact absurd h (lt_irrefl _)
  · exact absurd (lt_trans (lt₁ hGA) (gt₂ hHD)) (lt_irrefl _)
  · have h := lt₂ hHD; rw [eq₁ hBGC] at h; exact absurd h (lt_irrefl _)
  · exact Or.inr (Or.inl ⟨hBGC, hEHF⟩)
  · have h := gt₂ hHD; rw [eq₁ hBGC] at h; exact absurd h (lt_irrefl _)
  · exact absurd (lt_trans (lt₂ hHD) (gt₁ hGA)) (lt_irrefl _)
  · have h := gt₁ hGA; rw [eq₂ hEHF] at h; exact absurd h (lt_irrefl _)
  · exact Or.inr (Or.inr ⟨hGA, hHD⟩)

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
  /- In Euclid's figure the centres lie on the sides of A and D, and the angles at A and D
     are acute. We write his argument once, for any points A, D of the circles on the
     centres' sides whose angles stand on equal circumferences: it runs at A and D
     themselves, and again, below, where the angles at A and D are obtuse. -/
  have euclid : ∀ {A D : Point}, OnCircle A ABC → OnCircle D DEF → SameSideOf G A B C →
      SameSideOf H D E F → standing ABC B A C = standing DEF E D F →
      ∠ B G C = ∠ E H F ∧ ∠ B A C = ∠ E D F := by
    intro A D hA hD hGA hHD heq
    /- We name the circumferences BC, EF by points Q, R beyond them, across BC from A and
       across EF from D; the centres lie on the sides of A and D. -/
    obtain ⟨Q, hQA, -⟩ := exists_oppositeSidesOf hGA.symm.triangle []
    obtain ⟨R, hRD, -⟩ := exists_oppositeSidesOf hHD.symm.triangle []
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
      /- III.26 gives BK and EF equal in measure and congruent; the comparison with BC
         below is by measure, so we take the measures. -/
      have hBK : circumference ABC B P K = circumference DEF E R F :=
        ((Prop26 hcircles hG hH hX hB hK hY hE hF (hXG.trans_opposite hPG.symm)
          (hYH.trans_opposite hHR)).1 hPG.symm hHR hBGK).1
      -- But EF is equal to BC;
      have hEF_BC := hBC.symm
      -- therefore BK is also equal to BC, the less to the greater: which is impossible.
      /- Euclid takes BK to be less than BC as a part of it. We measure BK and BC by their
         angles at G (`Circumference.centre`): BK is the less because the angle BGK, equal
         to EHF, is less than BGC. -/
      have h := hBK.trans hEF_BC
      rw [Circumference.centre hG hB hK hPG.symm, Circumference.centre hG hB hC hGQ,
        hBGK] at h
      rw [h] at hlt
      exact lt_irrefl _ hlt
    -- Therefore the angle BGC is not unequal to the angle EHF;
    -- therefore it is equal to it.
    have centres : ∠ B G C = ∠ E H F := by
      rcases lt_trichotomy (∠ B G C) (∠ E H F) with h | h | h
      · exact (greater hcircles.symm hH hG hE hF hB hC hHR hGQ hBC.symm h).elim
      · exact h
      · exact (greater hcircles hG hH hB hC hE hF hGQ hHR hBC h).elim
    -- And the angle at A is half of the angle BGC,
    have h20A := Prop20.special hG hA hB hC hGA
    -- and the angle at D half of the angle EHF; [III. 20]
    have h20D := Prop20.special hH hD hE hF hHD
    -- therefore the angle at A is also equal to the angle at D.
    exact ⟨centres, Magnitude.eq_of_add_self_eq (h20A.symm.trans (centres.trans h20D))⟩
  /- Euclid's halving holds where the angles at A and D are acute. The right and obtuse
     cases are taken separately, as Heath notes on III.26, and under III.27 he writes that
     "the remarks about the method of treating the different cases apply here also"
     (vol. 2, p. 59). Equal circumferences put the centres alike (`Prop27.sides`), and we
     take the three cases in turn. -/
  have hAD : ∠ B A C = ∠ E D F := by
    rcases Prop27.sides hG hH hA hB hC hD hE hF hBAC.acb hEDF.acb heq with
      ⟨hGA, hHD⟩ | ⟨hBGC, hEHF⟩ | ⟨hGA, hHD⟩
    · /- The angles at A and D are acute, as in Euclid's figure, and his argument gives them
         equal. -/
      exact (euclid hA hD hGA hHD heq).2
    · /- The angles at A and D are right, a case Euclid's figure leaves aside. The centres
         lie on BC and EF, and our angles are never straight, so there is no angle BGC here;
         the angle at the centre is two right angles (`angleAtCentre.semicircle`), and we do
         not halve it. Each angle at A and D is an angle in a semicircle, and right
         (`Prop24.angle_type`, whose other two cases would put the centre off BC or EF); the
         two are each the one right angle, and so equal. This case still rests on the
         measure of the circumference: `Prop24.angle_type` reads the right angle off it, the
         semicircle being two right angles (`Circumference.semicircle`) and the angle in it
         half of that (`Circumference.eq`). -/
      have hrt : ∠ B A C = ∟ := by
        rcases Prop24.angle_type hG hB hC hA hBAC.acb with ⟨hGA, -⟩ | ⟨-, h⟩ | ⟨hGA, -⟩
        · exact (hGA.triangle.acb (collinear_of_between hBGC)).elim
        · exact h
        · exact (hGA.triangle.acb (collinear_of_between hBGC)).elim
      have hrt' : ∠ E D F = ∟ := by
        rcases Prop24.angle_type hH hE hF hD hEDF.acb with ⟨hHD, -⟩ | ⟨-, h⟩ | ⟨hHD, -⟩
        · exact (hHD.triangle.acb (collinear_of_between hEHF)).elim
        · exact h
        · exact (hHD.triangle.acb (collinear_of_between hEHF)).elim
      rw [hrt, hrt']
    · /- The angles at A and D are obtuse, the other case Euclid's figure leaves aside: the
         centres lie beyond BC and EF from A and D. We pass to the circumferences that
         remain, BAC and EDF, as III.26 passes to "the circumference BKC which remains", and
         to the angles BXC, EYF standing on them at points X, Y of the circles on the
         centres' sides. -/
      obtain ⟨X, hX, hXG⟩ := Prop2.sameSide hB hC hGA.triangle
      obtain ⟨Y, hY, hYH⟩ := Prop2.sameSide hE hF hHD.triangle
      have hXA : OppositeSidesOf X A B C := hXG.trans_opposite hGA
      have hYD : OppositeSidesOf Y D E F := hYH.trans_opposite hHD
      /- X and Y lie on the circumferences BC, EF, and the whole circles are four right
         angles each (`Circumference.whole`); so the circumferences BAC, EDF which remain
         are equal [C.N. 3]. -/
      have hst : standing ABC B X C = standing DEF E Y F := by
        have w₁ := Circumference.whole hB hC hXA.symm
        have w₂ := Circumference.whole hE hF hYD.symm
        rw [standing_eq_circumference hXA, standing_eq_circumference hYD]
        refine CommonNotion3 (c := circumference ABC B X C) (d := circumference DEF E Y F)
          ?_ ?_
        · rw [add_comm (circumference ABC B A C), w₁, add_comm (circumference DEF E D F), w₂]
        · rw [← standing_eq_circumference hXA.symm, ← standing_eq_circumference hYD.symm]
          exact heq
      /- The angles at X and Y are acute, the centres lying on their sides, and Euclid's
         argument above makes them equal. -/
      have hXY : ∠ B X C = ∠ E Y F := (euclid hX hY hXG.symm hYH.symm hst).2
      /- The angles at A and X are opposite angles of the quadrilateral ABXC in the circle,
         and those at D and Y of DEYF, so each pair is two right angles [III. 22]; when the
         equal angles at X and Y are taken away, the angles at A and D which remain are
         equal [C.N. 3]. -/
      have q₁ : ∠ B A C + ∠ B X C = ∟ + ∟ := by
        have := (Prop22 hA hB hX hC hXA.symm).2
        rwa [angle_symm hXA.triangle.ne₂₃ hXA.triangle.ne₁₃] at this
      have q₂ : ∠ E D F + ∠ E Y F = ∟ + ∟ := by
        have := (Prop22 hD hE hY hF hYD.symm).2
        rwa [angle_symm hYD.triangle.ne₂₃ hYD.triangle.ne₁₃] at this
      exact CommonNotion3 (c := ∠ B X C) (d := ∠ E Y F) (by rw [q₁, q₂]) hXY
  -- Therefore etc.
  exact ⟨hAD, fun hGA hHD => (euclid hA hD hGA hHD heq).1⟩
  -- Q. E. D.

end Elements.BookIII
