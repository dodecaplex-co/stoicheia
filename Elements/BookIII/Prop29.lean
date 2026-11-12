import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop04
import Elements.BookIII.Prop02
import Elements.BookIII.Prop24
import Elements.BookIII.Prop27

/-!
# Book III, Proposition 29

Euclid's text, in Heath's translation: [`heath/III/29.md`](../../heath/III/29.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

`Prop29` takes coinciding circumferences (`Arc.Congruent`); `Prop24.equalMeasure` gives their
measures for the size split. III.27 and I.4 give equal bases in the lesser case.
The edition's own greater case rests on III.28's closing subtraction: taking equal circumferences
from equal whole circles leaves equal circumferences (Heath, vol. 2, p. 60). Here subtraction
by Common Notion 3 gives the equal lesser measures; `Prop27.of_measure`
and I.4 give the bases. `Prop29.of_measure` uses III.27's measure form in both cases.
The size split uses III.20's special case, III.21 and III.22; subtraction uses III.21 and
III.22. Semicircles give diameters, each two equal radii. III.27's argument rests on III.20.
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

/-- Equal circumference measures put the two centres alike with respect to BC and EF. -/
theorem Prop29.matchSizes {B C E F G H K L : Point} {ABC DEF : Circle}
    (hK : Centre K ABC) (hL : Centre L DEF)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC)
    (hE : OnCircle E DEF) (hF : OnCircle F DEF)
    (hG : ¬ Collinear B C G) (hH : ¬ Collinear E F H)
    (heq : circumference ABC B G C = circumference DEF E H F) :
    (OppositeSidesOf K G B C ∧ OppositeSidesOf L H E F) ∨
    (Between B K C ∧ Between E L F) ∨
    (SameSideOf K G B C ∧ SameSideOf L H E F) := by
  rcases Prop29.size hK hB hC hG with ⟨hk, h₁⟩ | ⟨hk, h₁⟩ | ⟨hk, h₁⟩ <;>
    rcases Prop29.size hL hE hF hH with ⟨hl, h₂⟩ | ⟨hl, h₂⟩ | ⟨hl, h₂⟩
  · exact Or.inl ⟨hk, hl⟩
  · rw [heq, h₂] at h₁; exact False.elim ((lt_irrefl _) h₁)
  · rw [heq] at h₁; exact False.elim ((lt_irrefl _) (lt_trans h₁ h₂))
  · rw [← heq, h₁] at h₂; exact False.elim ((lt_irrefl _) h₂)
  · exact Or.inr (Or.inl ⟨hk, hl⟩)
  · rw [← heq, h₁] at h₂; exact False.elim ((lt_irrefl _) h₂)
  · rw [heq] at h₁; exact False.elim ((lt_irrefl _) (lt_trans h₂ h₁))
  · rw [heq, h₂] at h₁; exact False.elim ((lt_irrefl _) h₁)
  · exact Or.inr (Or.inr ⟨hk, hl⟩)

/-- In equal circles equal circumferences are subtended by equal straight lines. -/
theorem Prop29 {B C E F G H : Point} {ABC DEF : Circle}
    (hcircles : EqualCircles ABC DEF)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hE : OnCircle E DEF) (hF : OnCircle F DEF)
    (hG : ¬ Collinear B C G) (hH : ¬ Collinear E F H)
    (hcong : Arc.Congruent ⟨ABC, B, C, G⟩ ⟨DEF, E, F, H⟩) :
    ‖B C‖ = ‖E F‖ := by
  -- Let ABC, DEF be equal circles, and in them let equal circumferences BGC, EHF be cut off;
  -- and let the straight lines BC, EF be joined;
  /- A and D are points of the circles beyond BC and EF from G and H, as Heath draws
     them. -/
  obtain ⟨A, hA, hAG⟩ := Prop2.oppositeSide hB hC hG
  obtain ⟨D, hD, hDH⟩ := Prop2.oppositeSide hE hF hH
  -- I say that BC is equal to EF.
  -- For let the centres of the circles be taken, and let them be K, L; let BK, KC, EL, LF be
  -- joined.
  obtain ⟨K, L, -, -, hK, hL, -⟩ := id hcircles
  -- Now, since the circumference BGC is equal to the circumference EHF,
  -- the angle BKC is also equal to the angle ELF. [III. 27]
  /- III.27 takes the given coinciding circumferences for the lesser case; below,
     III.24 also gives equal measures for the size split and the remainders. -/
  have hangles := Prop27 hcircles hK hL hA hB hC hD hE hF hAG hDH hcong
  /- Equal circumference measures put the centres alike: across BC and EF from G and H,
     on BC and EF, or on G's and H's sides. -/
  -- And, since the circles ABC, DEF are equal,
  -- the radii are also equal;
  have hrB : ‖K B‖ = ‖L E‖ := hcircles.radii hK hL hB hE
  have hrC : ‖K C‖ = ‖L F‖ := hcircles.radii hK hL hC hF
  -- therefore the two sides BK, KC are equal to the two sides EL, LF; and they contain equal
  -- angles;
  -- therefore the base BC is equal to the base EF. [I. 4]
  /- Equal measures align the sizes. Diameters are sums of equal radii; greater
     circumferences leave equal lesser remainders, where III.27 and I.4 apply. -/
  have heq : circumference ABC B G C = circumference DEF E H F :=
    Prop24.equalMeasure (a := ⟨ABC, B, C, G⟩) (b := ⟨DEF, E, F, H⟩)
      ⟨hB, hC, hG⟩ ⟨hE, hF, hH⟩ hcong
  rcases Prop29.matchSizes hK hL hB hC hE hF hG hH heq with
    ⟨hKG, hLH⟩ | ⟨hBKC, hELF⟩ | ⟨hKG, hLH⟩
  · have hBKC : ∠ B K C = ∠ E L F := hangles.2
      (OppositeSidesOf.sameSideOf hKG.symm hAG.symm)
      (OppositeSidesOf.sameSideOf hLH.symm hDH.symm)
    exact (BookI.Prop4 hKG.triangle.cab hLH.triangle.cab hrB hrC hBKC).1
  · rw [← len_add_of_between hBKC, ← len_add_of_between hELF,
      len_symm B K, len_symm E L, hrB, hrC]
  · have hw₁ := Circumference.whole hB hC hAG.symm
    have hw₂ := Circumference.whole hE hF hDH.symm
    have hwholes : circumference ABC B A C + circumference ABC B G C =
        circumference DEF E D F + circumference DEF E H F := hw₁.trans hw₂.symm
    have hrem : circumference ABC B A C = circumference DEF E D F :=
      CommonNotion3 hwholes heq
    obtain ⟨P, hP, hPK⟩ := Prop2.sameSide hB hC hKG.triangle
    obtain ⟨Q, hQ, hQL⟩ := Prop2.sameSide hE hF hLH.triangle
    have hPA : OppositeSidesOf P A B C := hPK.trans_opposite (hKG.trans_opposite hAG.symm)
    have hQD : OppositeSidesOf Q D E F := hQL.trans_opposite (hLH.trans_opposite hDH.symm)
    have hremaining : standing ABC B P C = standing DEF E Q F := by
      rw [standing_eq_circumference hPA, standing_eq_circumference hQD]
      exact hrem
    have hless := Prop27.of_measure hcircles hK hL hP hB hC hQ hE hF
      hPA.triangle.acb hQD.triangle.acb hremaining
    exact (BookI.Prop4 hKG.triangle.cab hLH.triangle.cab hrB hrC
      (hless.2 hPK.symm hQL.symm)).1
  -- Therefore etc.
  -- Q. E. D.

/-- **III.29 with circumferences equal in measure** (companion of III.29,
"III.29 of_measure"). In equal circles circumferences equal in measure are subtended by equal
straight lines. Equal circumferences are read here as equal in measure, each twice the angle
standing on it (`circumference`); `Prop29` reads them through Common Notion 4 as
circumferences that coincide (`Arc.Congruent`), as III.28 concludes them. `Arc.measure_eq_iff`,
after III.29, cites this form.

Proved with III.27's measure form: first express the given measures as those on which
the angles at A and D stand (`standing_eq_circumference`). Equal measures put the centres
alike (`Prop29.matchSizes`). In the lesser case III.27 gives the angles for I.4; in the
greater case subtract from the whole circle's measure, then apply III.27 and I.4 to the
lesser remainders. For semicircles the diameters are sums of equal radii. Equal circles
are needed here: equal measures in unequal circles need not give equal straight lines. -/
theorem Prop29.of_measure {B C E F G H : Point} {ABC DEF : Circle}
    (hcircles : EqualCircles ABC DEF)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hE : OnCircle E DEF) (hF : OnCircle F DEF)
    (hG : ¬ Collinear B C G) (hH : ¬ Collinear E F H)
    (heq : circumference ABC B G C = circumference DEF E H F) :
    ‖B C‖ = ‖E F‖ := by
  /- Take points on the opposite circumferences and the centres, as in the main proof. -/
  obtain ⟨A, hA, hAG⟩ := Prop2.oppositeSide hB hC hG
  obtain ⟨D, hD, hDH⟩ := Prop2.oppositeSide hE hF hH
  obtain ⟨K, L, -, -, hK, hL, -⟩ := id hcircles
  /- The given circumference measures are those on which the angles at A and D stand;
     III.27's measure form gives their angles. -/
  have hstanding : standing ABC B A C = standing DEF E D F := by
    rw [standing_eq_circumference hAG, standing_eq_circumference hDH]
    exact heq
  have hangles := Prop27.of_measure hcircles hK hL hA hB hC hD hE hF
    hAG.triangle.acb hDH.triangle.acb hstanding
  /- The radii of the equal circles are equal. -/
  have hrB : ‖K B‖ = ‖L E‖ := hcircles.radii hK hL hB hE
  have hrC : ‖K C‖ = ‖L F‖ := hcircles.radii hK hL hC hF
  /- Match the circumference sizes, then use I.4 directly or on the lesser remainders;
     diameters are sums of equal radii. -/
  rcases Prop29.matchSizes hK hL hB hC hE hF hG hH heq with
    ⟨hKG, hLH⟩ | ⟨hBKC, hELF⟩ | ⟨hKG, hLH⟩
  · have hBKC : ∠ B K C = ∠ E L F := hangles.2
      (OppositeSidesOf.sameSideOf hKG.symm hAG.symm)
      (OppositeSidesOf.sameSideOf hLH.symm hDH.symm)
    exact (BookI.Prop4 hKG.triangle.cab hLH.triangle.cab hrB hrC hBKC).1
  · rw [← len_add_of_between hBKC, ← len_add_of_between hELF,
      len_symm B K, len_symm E L, hrB, hrC]
  · have hw₁ := Circumference.whole hB hC hAG.symm
    have hw₂ := Circumference.whole hE hF hDH.symm
    have hwholes : circumference ABC B A C + circumference ABC B G C =
        circumference DEF E D F + circumference DEF E H F := hw₁.trans hw₂.symm
    have hrem : circumference ABC B A C = circumference DEF E D F :=
      CommonNotion3 hwholes heq
    obtain ⟨P, hP, hPK⟩ := Prop2.sameSide hB hC hKG.triangle
    obtain ⟨Q, hQ, hQL⟩ := Prop2.sameSide hE hF hLH.triangle
    have hPA : OppositeSidesOf P A B C := hPK.trans_opposite (hKG.trans_opposite hAG.symm)
    have hQD : OppositeSidesOf Q D E F := hQL.trans_opposite (hLH.trans_opposite hDH.symm)
    have hremaining : standing ABC B P C = standing DEF E Q F := by
      rw [standing_eq_circumference hPA, standing_eq_circumference hQD]
      exact hrem
    have hless := Prop27.of_measure hcircles hK hL hP hB hC hQ hE hF
      hPA.triangle.acb hQD.triangle.acb hremaining
    exact (BookI.Prop4 hKG.triangle.cab hLH.triangle.cab hrB hrC
      (hless.2 hPK.symm hQL.symm)).1

end Elements.BookIII
