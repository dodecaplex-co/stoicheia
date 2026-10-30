import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop23
import Elements.BookIII.Prop02
import Elements.BookIII.Prop20
import Elements.BookIII.Prop24
import Elements.BookIII.Prop26

/-!
# Book III, Proposition 27

Euclid's text, in Heath's translation: [`heath/III/27.md`](../../heath/III/27.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

The proof is Euclid's: his reductio makes the angles at the centres equal, and his halving,
"the angle at A is half of the angle BGC" [III. 20], makes those at the circumferences equal.
The reductio is written once, for any circumferences beyond which the centres lie, where the
angles at the centres are the angles BGC, EHF. The halving takes three cases, for equal
circumferences put the centres alike (`Prop27.sides`). Where the angles at A and D are
acute, as in his figure, the centres lie on the sides of A and D, and III.20 halves the
angles BGC, EHF (`Prop20.special`). Elsewhere "the angle BGC" is the angle at the centre
standing on the circumference BC (`angleAtCentre`), which may be two right angles or more,
a reading made after Heath's notes on III.20 and III.21, and III.20 halves it as it stands
(`Prop20`). Where the angles at A and D are right, the centres lie on BC and EF, and the
angles at the centres are each two right angles (`angleAtCentre.semicircle`), and so equal
with no reductio. Where they are obtuse, the centres lie beyond BC and EF, and the angles at
the centres are greater than two right angles: I.23 constructs no such angle, and III.26's
statement speaks of none, so the reductio is taken on the angles BGC, EHF, which stand on
the circumferences that remain, and the angles at the centres are what remains when those
are taken from four right angles (`angleAtCentre.reflex`), as in III.26. Heath says that
his remarks on III.26's cases "apply here also" (vol. 2, p. 59). Nothing here uses
`Circumference.standing`.

`Prop27` reads Euclid's equal circumferences through Common Notion 4, as circumferences that
coincide when one is placed on the other (`Arc.Congruent`), as III.26 concludes them. The
reductio compares circumferences by measure, so its first step makes them equal in measure,
by III.24's companion `Prop24.equalMeasure`, where Heath gives no reference; the rest is the
argument above. The companion `Prop27.of_measure` states III.27 for circumferences equal in
measure, the form III.29's companion cites, and repeats the argument from those measures. It
is not proved from `Prop27`: that would need circumferences equal in measure to coincide,
which `Arc.congruent_iff` proves only after III.29, and from it.
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
theorem Prop27 {A B C D E F G H Q R : Point} {ABC DEF : Circle}
    (hcircles : EqualCircles ABC DEF) (hG : Centre G ABC) (hH : Centre H DEF)
    (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hC : OnCircle C ABC)
    (hD : OnCircle D DEF) (hE : OnCircle E DEF) (hF : OnCircle F DEF)
    (hAQ : OppositeSidesOf A Q B C) (hDR : OppositeSidesOf D R E F)
    (hcong : Arc.Congruent ⟨ABC, B, C, Q⟩ ⟨DEF, E, F, R⟩) :
    ∠ B A C = ∠ E D F ∧
      (SameSideOf G A B C → SameSideOf H D E F → ∠ B G C = ∠ E H F) := by
  -- For in equal circles ABC, DEF, on equal circumferences BC, EF, let the angles BGC, EHF
  -- stand at the centres G, H, and the angles BAC, EDF at the circumferences;
  -- I say that the angle BGC is equal to the angle EHF,
  -- and the angle BAC is equal to the angle EDF.
  /- The equal circumferences BC, EF are given as circumferences that coincide, named by
     points Q, R beyond them, across BC from A and across EF from D. The reductio compares
     circumferences by measure, so we take the measures first: circumferences that coincide
     are equal in measure, by III.24's companion (`Prop24.equalMeasure`), and these are the
     circumferences on which the angles at A and D stand. -/
  have hBC : circumference ABC B Q C = circumference DEF E R F :=
    Prop24.equalMeasure (a := ⟨ABC, B, C, Q⟩) (b := ⟨DEF, E, F, R⟩)
      ⟨hB, hC, hAQ.symm.triangle⟩ ⟨hE, hF, hDR.symm.triangle⟩ hcong
  have heq : standing ABC B A C = standing DEF E D F := by
    rw [standing_eq_circumference hAQ, standing_eq_circumference hDR]; exact hBC
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
  /- The reductio holds for any circumferences beyond which the centres lie, named by points
     across BC and EF from the centres: below it serves the circumferences BC, EF, and,
     where the angles at A and D are obtuse, the circumferences that remain. -/
  have centres : ∀ {Q R : Point}, OppositeSidesOf G Q B C → OppositeSidesOf H R E F →
      circumference ABC B Q C = circumference DEF E R F → ∠ B G C = ∠ E H F := by
    intro Q R hGQ hHR hBC
    rcases lt_trichotomy (∠ B G C) (∠ E H F) with h | h | h
    · exact (greater hcircles.symm hH hG hE hF hB hC hHR hGQ hBC.symm h).elim
    · exact h
    · exact (greater hcircles hG hH hB hC hE hF hGQ hHR hBC h).elim
  /- Euclid's figure has the centres on the sides of A and D, and the angles at A and D
     acute. Under III.27 Heath writes that "the remarks about the method of treating the
     different cases apply here also" (vol. 2, p. 59). Equal circumferences put the centres
     alike (`Prop27.sides`), and we take his halving in each case. -/
  -- And the angle at A is half of the angle BGC,
  -- and the angle at D half of the angle EHF; [III. 20]
  -- therefore the angle at A is also equal to the angle at D.
  have hAD : ∠ B A C = ∠ E D F := by
    rcases Prop27.sides hG hH hA hB hC hD hE hF hAQ.triangle hDR.triangle heq with
      ⟨hGA, hHD⟩ | hother
    · /- The angles at A and D are acute, as in Euclid's figure. The centres lie on the
         sides of A and D, the angles BGC, EHF at the centres are equal by the reductio, and
         III.20 halves them (`Prop20.special`). -/
      have hGH : ∠ B G C = ∠ E H F :=
        centres (hGA.trans_opposite hAQ) (hHD.trans_opposite hDR) hBC
      have h20A := Prop20.special hG hA hB hC hGA
      have h20D := Prop20.special hH hD hE hF hHD
      exact Magnitude.eq_of_add_self_eq (h20A.symm.trans (hGH.trans h20D))
    /- Elsewhere the angle at the centre standing on the circumference BC, on which the
       angle at A stands, is two right angles or more: in the right case B, G and C lie on
       one straight line, and in the obtuse case the angle at the centre is greater than the
       ordinary angle BGC. "The angle BGC" of Euclid's halving is then that
       angle at the centre (`angleAtCentre`), and "the angle EHF" the one standing on EF.
       They are equal, case by case, and III.20 halves them. -/
    have hGH : angleAtCentre ABC B Q C = angleAtCentre DEF E R F := by
      rcases hother with ⟨hBGC, hEHF⟩ | ⟨hGA, hHD⟩
      · /- The angles at A and D are right, a case Euclid's figure leaves aside. The centres
           lie on BC and EF, and each angle at the centre is two right angles
           (`angleAtCentre.semicircle`), so they are equal with no reductio. -/
        rw [angleAtCentre.semicircle hG hB hC hBGC hAQ.symm.triangle,
          angleAtCentre.semicircle hH hE hF hEHF hDR.symm.triangle]
      · /- The angles at A and D are obtuse, the other case Euclid's figure leaves aside: the
           centres lie beyond BC and EF from A and D, and the angles at the centres are
           greater than two right angles. I.23 constructs no such angle, and III.26's
           statement speaks of none, so we pass to the circumferences BAC, EDF that remain,
           as III.26 passes to "the circumference BKC which remains". The whole circles are
           four right angles each (`Circumference.whole`), so the circumferences that remain
           are equal [C.N. 3]. -/
        have w₁ := Circumference.whole hB hC hAQ
        have w₂ := Circumference.whole hE hF hDR
        have hrem : circumference ABC B A C = circumference DEF E D F :=
          CommonNotion3 (c := circumference ABC B Q C) (d := circumference DEF E R F)
            (by rw [add_comm (circumference ABC B A C), w₁, add_comm (circumference DEF E D F),
              w₂]) hBC
        /- The angles BGC, EHF stand on them, the centres lying beyond them, and the
           reductio makes those equal. The angles at the centres standing on BC and EF are
           what remains when the angles BGC, EHF are taken from four right angles
           (`angleAtCentre.reflex`), and so are equal [C.N. 3]. -/
        have hBGC : ∠ B G C = ∠ E H F := centres hGA hHD hrem
        exact CommonNotion3 (c := ∠ B G C) (d := ∠ E H F)
          (by rw [angleAtCentre.reflex hG hB hC (OppositeSidesOf.sameSideOf hGA.symm hAQ),
            angleAtCentre.reflex hH hE hF (OppositeSidesOf.sameSideOf hHD.symm hDR)])
          hBGC
    have h20A := Prop20 hA hB hC hAQ
    have h20D := Prop20 hD hE hF hDR
    exact Magnitude.eq_of_add_self_eq (h20A.symm.trans (hGH.trans h20D))
  -- Therefore etc.
  exact ⟨hAD, fun hGA hHD =>
    centres (hGA.trans_opposite hAQ) (hHD.trans_opposite hDR) hBC⟩
  -- Q. E. D.

/-- **III.27 with circumferences equal in measure** (companion of III.27,
"III.27 of_measure"). In equal circles, angles standing on circumferences equal in measure
are equal to one another, whether they stand at the centres or at the circumferences. Equal
circumferences are read here as equal in measure, each twice the angle standing on it
(`standing`), and the angles BAC, EDF at the circumferences are given by their triangles;
`Prop27` reads them through Common Notion 4 as circumferences that coincide
(`Arc.Congruent`), as III.26 concludes them. III.29's companion `Prop29.of_measure` cites
this form.

Proved by Euclid's argument again, as in `Prop27`, from the given measures: his reductio for
the angles at the centres, by I.23 and III.26, and his halving by III.20 in each case
(`Prop27.sides`). It is not proved from `Prop27`, which would need circumferences equal in
measure to coincide: `Arc.congruent_iff` proves that only after III.29, and from it. Our
measure carries no radius, so the conclusion holds without the equal circles; the hypothesis
keeps Euclid's setting, and the proof uses it through III.26. -/
theorem Prop27.of_measure {A B C D E F G H : Point} {ABC DEF : Circle}
    (hcircles : EqualCircles ABC DEF)
    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hF : OnCircle F DEF) (hBAC : Triangle B A C) (hEDF : Triangle E D F)
    (heq : standing ABC B A C = standing DEF E D F) :
    ∠ B A C = ∠ E D F ∧
      (SameSideOf G A B C → SameSideOf H D E F → ∠ B G C = ∠ E H F) := by
  /- Name the circumferences BC, EF on which the angles at A and D stand by points Q, R
     beyond them, across BC from A and across EF from D; their measures are given equal. -/
  obtain ⟨Q, hQA, -⟩ := exists_oppositeSidesOf hBAC.acb []
  obtain ⟨R, hRD, -⟩ := exists_oppositeSidesOf hEDF.acb []
  have hBC : circumference ABC B Q C = circumference DEF E R F := by
    rw [← standing_eq_circumference hQA.symm, ← standing_eq_circumference hRD.symm]
    exact heq
  /- The reductio, as in `Prop27`, written once and used with the circles named either way
     round: were the angle BGC greater than EHF, the angle BGK made equal to EHF would stand
     on a circumference BK equal to EF, and so to BC, the less to the greater. -/
  have greater : ∀ {B C E F G H Q R : Point} {ABC DEF : Circle}, EqualCircles ABC DEF →
      Centre G ABC → Centre H DEF → OnCircle B ABC → OnCircle C ABC → OnCircle E DEF →
      OnCircle F DEF → OppositeSidesOf G Q B C → OppositeSidesOf H R E F →
      circumference ABC B Q C = circumference DEF E R F → ∠ E H F < ∠ B G C → False := by
    intro B C E F G H Q R ABC DEF hcircles hG hH hB hC hE hF hGQ hHR hBC hlt
    /- We construct the angle BGK equal to EHF on BG at G [I. 23], then take K on that ray at
       distance GB from G, which puts it on the circle (System E, Diagram-segment 3). -/
    have hGB : G ≠ B := (ne_of_centre_of_on hG hB).symm
    obtain ⟨K', B', hB', hK'C, hK'GB'⟩ := BookI.Prop23 hGB hHR.triangle.acb hGQ.triangle.cab
    have hK'G : K' ≠ G := hK'C.triangle.ne₁₃.symm
    obtain ⟨K, hK_ray, hGK⟩ := OnRay.exists_len_eq hGB hK'G.symm
    have hK : OnCircle K ABC := on_circle_of_len_eq hG hB hGK
    have hBGK : ∠ B G K = ∠ E H F := by
      rw [angle_onRay_right hK_ray hGB.symm, ← angle_onRay_left hB' hK'G]
      exact (angle_symm hB'.2.1 hK'G).trans hK'GB'
    have hGBK : Triangle G B K := (SameSideOf.of_onRay hK_ray hK'C).triangle
    /- Equal angles at the centres stand on circumferences equal in measure [III. 26]: BK,
       named by a point P beyond it, is equal to EF. -/
    obtain ⟨P, hPG, -⟩ := exists_oppositeSidesOf hGBK.bca []
    obtain ⟨X, hX, hXG⟩ := Prop2.sameSide hB hK hGBK.bca
    obtain ⟨Y, hY, hYH⟩ := Prop2.sameSide hE hF hHR.triangle
    have hBK : circumference ABC B P K = circumference DEF E R F :=
      ((Prop26 hcircles hG hH hX hB hK hY hE hF (hXG.trans_opposite hPG.symm)
        (hYH.trans_opposite hHR)).1 hPG.symm hHR hBGK).1
    /- EF is equal to BC, so BK would be equal to BC. Measured by their angles at G
       (`Circumference.centre`), the less angle BGK would be equal to the greater, BGC. -/
    have hEF_BC := hBC.symm
    have h := hBK.trans hEF_BC
    rw [Circumference.centre hG hB hK hPG.symm, Circumference.centre hG hB hC hGQ,
      hBGK] at h
    rw [h] at hlt
    exact lt_irrefl _ hlt
  /- So the angles at the centres are equal, for any circumferences beyond which the centres
     lie, named by points across BC and EF from the centres. -/
  have centres : ∀ {Q R : Point}, OppositeSidesOf G Q B C → OppositeSidesOf H R E F →
      circumference ABC B Q C = circumference DEF E R F → ∠ B G C = ∠ E H F := by
    intro Q R hGQ hHR hBC
    rcases lt_trichotomy (∠ B G C) (∠ E H F) with h | h | h
    · exact (greater hcircles.symm hH hG hE hF hB hC hHR hGQ hBC.symm h).elim
    · exact h
    · exact (greater hcircles hG hH hB hC hE hF hGQ hHR hBC h).elim
  /- Euclid's halving by III.20, in each of the cases that equal circumferences allow
     (`Prop27.sides`), as in `Prop27`. -/
  have hAD : ∠ B A C = ∠ E D F := by
    rcases Prop27.sides hG hH hA hB hC hD hE hF hBAC.acb hEDF.acb heq with
      ⟨hGA, hHD⟩ | hother
    · /- The angles at A and D are acute: III.20 halves the angles BGC, EHF, equal by the
         reductio (`Prop20.special`). -/
      have hGH : ∠ B G C = ∠ E H F :=
        centres (hGA.trans_opposite hQA.symm) (hHD.trans_opposite hRD.symm) hBC
      have h20A := Prop20.special hG hA hB hC hGA
      have h20D := Prop20.special hH hD hE hF hHD
      exact Magnitude.eq_of_add_self_eq (h20A.symm.trans (hGH.trans h20D))
    /- Elsewhere III.20 halves the angles at the centres standing on BC and EF
       (`angleAtCentre`), equal case by case. -/
    have hGH : angleAtCentre ABC B Q C = angleAtCentre DEF E R F := by
      rcases hother with ⟨hBGC, hEHF⟩ | ⟨hGA, hHD⟩
      · /- The angles at A and D are right: each angle at the centre is two right angles
           (`angleAtCentre.semicircle`). -/
        rw [angleAtCentre.semicircle hG hB hC hBGC hQA.triangle,
          angleAtCentre.semicircle hH hE hF hEHF hRD.triangle]
      · /- The angles at A and D are obtuse: the circumferences BAC, EDF that remain are
           equal (`Circumference.whole`, C.N. 3), the reductio makes the angles BGC, EHF
           standing on them equal, and the angles at the centres are what remains when those
           are taken from four right angles (`angleAtCentre.reflex`, C.N. 3). -/
        have w₁ := Circumference.whole hB hC hQA.symm
        have w₂ := Circumference.whole hE hF hRD.symm
        have hrem : circumference ABC B A C = circumference DEF E D F :=
          CommonNotion3 (c := circumference ABC B Q C) (d := circumference DEF E R F)
            (by rw [add_comm (circumference ABC B A C), w₁, add_comm (circumference DEF E D F),
              w₂]) hBC
        have hBGC : ∠ B G C = ∠ E H F := centres hGA hHD hrem
        exact CommonNotion3 (c := ∠ B G C) (d := ∠ E H F)
          (by rw [angleAtCentre.reflex hG hB hC (OppositeSidesOf.sameSideOf hGA.symm hQA.symm),
            angleAtCentre.reflex hH hE hF (OppositeSidesOf.sameSideOf hHD.symm hRD.symm)])
          hBGC
    have h20A := Prop20 hA hB hC hQA.symm
    have h20D := Prop20 hD hE hF hRD.symm
    exact Magnitude.eq_of_add_self_eq (h20A.symm.trans (hGH.trans h20D))
  exact ⟨hAD, fun hGA hHD =>
    centres (hGA.trans_opposite hQA.symm) (hHD.trans_opposite hRD.symm) hBC⟩

end Elements.BookIII
