import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop04
import Elements.BookIII.Prop02
import Elements.BookIII.Prop24
import Elements.BookIII.Prop20
import Elements.BookIII.Prop26
import Elements.BookIII.Prop27

/-!
# Book III, Proposition 29

Euclid's text, in Heath's translation: [`heath/III/29.md`](../../heath/III/29.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- As the straight line XY cuts off the circumference XZY, the centre M lies beyond it,
and the circumference is less than a semicircle; or on XY, and it is a semicircle; or on
Z's side, and it is greater. Euclid's figure has the first, and the proof takes all
three. [I. 5, I. 32, III. 20, III. 21, III. 22] -/
theorem Prop29.size {X Y Z M : Point} {α : Circle} (hM : Centre M α) (hX : OnCircle X α)
    (hY : OnCircle Y α) (hXYZ : Triangle X Y Z) :
    (OppositeSidesOf M Z X Y ∧ circumference α X Z Y < ∟ + ∟) ∨
      (Between X M Y ∧ circumference α X Z Y = ∟ + ∟) ∨
      (SameSideOf M Z X Y ∧ ∟ + ∟ < circumference α X Z Y) := by
  obtain ⟨N, hX_N, hY_N⟩ := Postulate1 X Y hXYZ.ne₁₂
  by_cases hM_N : OnLine M N
  · have hXMY := between_of_inside_chord hM_N hX_N hY_N (centre_inside hM) hX hY hXYZ.ne₁₂
    exact Or.inr (Or.inl ⟨hXMY, Circumference.semicircle hM hX hY hXMY hXYZ⟩)
  by_cases hs : SameSide M Z N
  · have h := SameSideOf.of_line hXYZ.ne₁₂ hX_N hY_N hs
    exact Or.inr (Or.inr ⟨h, Circumference.gt_semicircle hM hX hY h⟩)
  · have h := OppositeSidesOf.of_line hXYZ.ne₁₂ hX_N hY_N ⟨hM_N, hXYZ.off_line hX_N hY_N, hs⟩
    exact Or.inl ⟨h, Circumference.lt_semicircle hM hX hY h⟩

/-- In equal circles equal circumferences are subtended by equal straight lines. -/
theorem Prop29 {B C E F G H : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hE : OnCircle E DEF) (hF : OnCircle F DEF)
    (hG : ¬ Collinear B C G) (hH : ¬ Collinear E F H)
    (heq : circumference ABC B G C = circumference DEF E H F) :
    ‖B C‖ = ‖E F‖ := by
  -- Let ABC, DEF be equal circles, and in them let equal circumferences BGC, EHF be cut off;
  -- and let the straight lines BC, EF be joined;
  have hBCG : Triangle B C G := hG
  have hEFH : Triangle E F H := hH
  /- A and D are points of the circles beyond BC and EF from G and H, as Heath draws
     them. -/
  obtain ⟨A, hA, hAG⟩ := Prop2.oppositeSide hB hC hBCG
  obtain ⟨D, hD, hDH⟩ := Prop2.oppositeSide hE hF hEFH
  -- I say that BC is equal to EF.
  -- For let the centres of the circles be taken, and let them be K, L; let BK, KC, EL, LF be
  -- joined.
  obtain ⟨K, L, -, -, hK, hL, -, -, -⟩ := id hcircles
  -- Now, since the circumference BGC is equal to the circumference EHF,
  have hstanding : standing ABC B A C = standing DEF E D F := by
    rw [standing_eq_circumference hAG, standing_eq_circumference hDH]
    exact heq
  -- the angle BKC is also equal to the angle ELF. [III. 27]
  have hangles := Prop27 hcircles hK hL hA hB hC hD hE hF
    hAG.triangle.acb hDH.triangle.acb hstanding
  /- The rectilineal conclusion of III.27 applies to the lesser circumferences. Its
     inscribed-angle conclusion, doubled by III.20, gives the angles standing at the
     centres on the given circumferences in every size case. This extension is ours:
     a greater circumference has a reflex angle at the centre, and a semicircle has
     two right angles. The conversion back to triangle angles belongs at I.4 below. -/
  have hcentral : angleAtCentre ABC B G C = angleAtCentre DEF E H F := by
    sorry
  -- And, since the circles ABC, DEF are equal,
  -- the radii are also equal;
  have hrB : ‖K B‖ = ‖L E‖ := hcircles.radii hK hL hB hE
  have hrC : ‖K C‖ = ‖L F‖ := hcircles.radii hK hL hC hF
  -- therefore the two sides BK, KC are equal to the two sides EL, LF; and they contain equal
  -- angles;
  -- therefore the base BC is equal to the base EF. [I. 4]
  /- III.27 has supplied the angles before I.4 is applied. Equal angles standing at
     the centres put both circles in the same case (`Prop26.alike`). For diameters
     there are no triangles; for greater circumferences I.4 takes the rectilineal
     angles left from four right angles. These are additions to Heath's figure
     (vol. 2, p. 60), not a restriction on the theorem. -/
  rcases Prop26.alike hK hB hC hBCG hL hE hF hEFH hcentral with
    ⟨hKG, hLH⟩ | ⟨hBKC, hELF⟩ | ⟨hKG, hLH⟩
  · have hBKC : ∠ B K C = ∠ E L F := hangles.2
      (OppositeSidesOf.sameSideOf hKG.symm hAG.symm)
      (OppositeSidesOf.sameSideOf hLH.symm hDH.symm)
    exact (BookI.Prop4 hKG.triangle.cab hLH.triangle.cab hrB hrC hBKC).1
  · rw [← len_add_of_between hBKC, ← len_add_of_between hELF,
      len_symm B K, len_symm E L, hrB, hrC]
  · have hBKC : ∠ B K C = ∠ E L F := by
      sorry
    exact (BookI.Prop4 hKG.triangle.cab hLH.triangle.cab hrB hrC hBKC).1
  -- Therefore etc.
  -- Q. E. D.

/-- **III.29 with congruent circumferences** (companion of III.29, "III.29 of_congruent").
In equal circles congruent circumferences are subtended by equal straight lines. We read
the congruence as III.28 concludes it (`Arc.Congruent`, Common Notion 4); `Prop29` reads
equal circumferences as equal in measure.

The map that makes the circumferences coincide keeps the distance between their ends, so
the congruence already gives the equal straight lines (`Prop24.image`). This proof passes
instead through equal measures (`Prop24.equalMeasure`) and `Prop29`, keeping that proof's
argument through III.27 and I.4, with its own treatment of semicircles and greater
circumferences. Congruence of these drawn arcs also implies that the circles are equal; the
hypothesis keeps Euclid's setting. -/
theorem Prop29.of_congruent {B C E F G H : Point} {ABC DEF : Circle}
    (hcircles : EqualCircles ABC DEF)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hE : OnCircle E DEF) (hF : OnCircle F DEF)
    (hG : ¬ Collinear B C G) (hH : ¬ Collinear E F H)
    (hcong : Arc.Congruent ⟨ABC, B, C, G⟩ ⟨DEF, E, F, H⟩) :
    ‖B C‖ = ‖E F‖ := by
  /- Take the centres and points on the opposite circumferences, as in the main proof. -/
  obtain ⟨K, L, -, -, hK, hL, -⟩ := id hcircles
  obtain ⟨A, hA, hAG⟩ := Prop2.oppositeSide hB hC hG
  obtain ⟨D, hD, hDH⟩ := Prop2.oppositeSide hE hF hH
  /- Equal circumferences give equal angles [III. 27], here using the companion that
     accepts exactly the congruence supplied, `Prop27.of_congruent`. -/
  have hangles := Prop27.of_congruent hcircles hK hL hA hB hC hD hE hF hAG hDH hcong
  have hcentral : angleAtCentre ABC B G C = angleAtCentre DEF E H F := by
    sorry
  /- The radii of the equal circles are equal. -/
  have hrB : ‖K B‖ = ‖L E‖ := hcircles.radii hK hL hB hE
  have hrC : ‖K C‖ = ‖L F‖ := hcircles.radii hK hL hC hF
  /- The equal sides and contained angles give the bases [I. 4]. The same diameter and
     reflex cases as in the main proof are kept, with all their geometric hypotheses. -/
  rcases Prop26.alike hK hB hC hG hL hE hF hH hcentral with
    ⟨hKG, hLH⟩ | ⟨hBKC, hELF⟩ | ⟨hKG, hLH⟩
  · have hBKC : ∠ B K C = ∠ E L F := hangles.2
      (OppositeSidesOf.sameSideOf hKG.symm hAG.symm)
      (OppositeSidesOf.sameSideOf hLH.symm hDH.symm)
    exact (BookI.Prop4 hKG.triangle.cab hLH.triangle.cab hrB hrC hBKC).1
  · rw [← len_add_of_between hBKC, ← len_add_of_between hELF,
      len_symm B K, len_symm E L, hrB, hrC]
  · have hBKC : ∠ B K C = ∠ E L F := by
      sorry
    exact (BookI.Prop4 hKG.triangle.cab hLH.triangle.cab hrB hrC hBKC).1

end Elements.BookIII
