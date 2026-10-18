import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Helpers
import Elements.BookI.Prop08
import Elements.BookI.Prop26
import Elements.BookI.Prop32
import Elements.BookIII.Prop20
import Elements.BookIII.Prop22

/-!
# Book III, Proposition 24

Euclid's text, in Heath's translation: [`heath/III/24.md`](../../heath/III/24.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- The halves of unequal things are unequal, the less to the less: if `a` and `a` together
are less than `b` and `b` together, then `a` is less than `b`. Were `a` equal to `b`, or
greater, the doubles would be equal, or the greater. -/
theorem Prop24.half_lt {k : Kind} {a b : Magnitude k} (h : a + a < b + b) : a < b := by
  rcases lt_trichotomy a b with h' | h' | h'
  · exact h'
  · subst h'; exact absurd h (lt_irrefl _)
  · exact absurd (lt_trans h (Magnitude.add_self_lt_add_self h')) (lt_irrefl _)

/-- The angle in a segment is acute, right or obtuse as the centre lies on its side of
the base, on the base, or beyond it. -/
theorem Prop24.angle_type {X Y Z M : Point} {α : Circle} (hM : Centre M α) (hX : OnCircle X α)
    (hY : OnCircle Y α) (hZ : OnCircle Z α) (hXYZ : Triangle X Y Z) :
    (SameSideOf M Z X Y ∧ ∠ X Z Y < ∟) ∨ (Between X M Y ∧ ∠ X Z Y = ∟) ∨
      (OppositeSidesOf M Z X Y ∧ ∟ < ∠ X Z Y) := by
  obtain ⟨W, hW, hWZ⟩ := exists_onCircle_oppositeSidesOf hX hY hXYZ
  have hm : circumference α X W Y = ∠ X Z Y + ∠ X Z Y := Circumference.eq ⟨M, hM⟩ hZ hX hY hWZ.symm
  obtain ⟨L, hX_L, hY_L⟩ := Postulate1 X Y hXYZ.ne₁₂
  by_cases hM_L : OnLine M L
  · have hXMY := between_of_inside_chord hM_L hX_L hY_L (centre_inside hM) hX hY hXYZ.ne₁₂
    have hs := Circumference.semicircle hM hX hY hXMY hWZ.triangle
    rw [hm] at hs
    exact Or.inr (Or.inl ⟨hXMY, Magnitude.eq_of_add_self_eq hs⟩)
  by_cases hs : SameSide M Z L
  · have hMZ : SameSideOf M Z X Y := SameSideOf.of_line hXYZ.ne₁₂ hX_L hY_L hs
    have hlt := Circumference.lt_semicircle hM hX hY (hMZ.trans_opposite hWZ.symm)
    rw [hm] at hlt
    exact Or.inl ⟨hMZ, Prop24.half_lt hlt⟩
  · have hMZ : OppositeSidesOf M Z X Y :=
      OppositeSidesOf.of_line hXYZ.ne₁₂ hX_L hY_L ⟨hM_L, hXYZ.off_line hX_L hY_L, hs⟩
    have hgt := Circumference.gt_semicircle hM hX hY (OppositeSidesOf.sameSideOf hMZ.symm hWZ.symm)
    rw [hm] at hgt
    exact Or.inr (Or.inr ⟨hMZ, Prop24.half_lt hgt⟩)

/-- Isosceles triangles on equal bases with equal angles at the vertex have equal sides. The
angles at the base are equal by I.5, the three angles make two right angles by I.32, and two
angles and the side between them give the equal sides by I.26. -/
theorem Prop24.isosceles {A B G C D H : Point} (hABG : Triangle A B G) (hCDH : Triangle C D H)
    (hG : ‖G A‖ = ‖G B‖) (hH : ‖H C‖ = ‖H D‖) (hAB : ‖A B‖ = ‖C D‖)
    (hang : ∠ A G B = ∠ C H D) : ‖G A‖ = ‖H C‖ := by
  have b₁ : ∠ G A B = ∠ G B A := BookI.Prop5.base hABG.cab hG
  have b₂ : ∠ H C D = ∠ H D C := BookI.Prop5.base hCDH.cab hH
  obtain ⟨P, hBGP⟩ := produce hABG.ne₂₃
  obtain ⟨-, s₁⟩ := BookI.Prop32 hABG hBGP
  obtain ⟨Q, hDHQ⟩ := produce hCDH.ne₂₃
  obtain ⟨-, s₂⟩ := BookI.Prop32 hCDH hDHQ
  have t₁ : ∠ G A B + ∠ G A B + ∠ A G B = ∟ + ∟ := by
    rw [← s₁, angle_symm hABG.ne₁₂ hABG.ne₂₃.symm, ← b₁, angle_symm hABG.ne₂₃ hABG.ne₁₃]
    ac_rfl
  have t₂ : ∠ H C D + ∠ H C D + ∠ C H D = ∟ + ∟ := by
    rw [← s₂, angle_symm hCDH.ne₁₂ hCDH.ne₂₃.symm, ← b₂, angle_symm hCDH.ne₂₃ hCDH.ne₁₃]
    ac_rfl
  have hA : ∠ G A B = ∠ H C D :=
    Magnitude.eq_of_add_self_eq (CommonNotion3 (by rw [t₁, t₂]) hang)
  have hB : ∠ A B G = ∠ C D H := by
    rw [angle_symm hABG.ne₁₂ hABG.ne₂₃.symm, ← b₁, hA, b₂, angle_symm hCDH.ne₂₃.symm hCDH.ne₁₂]
  exact (BookI.Prop26 hABG.cab hCDH.cab hA hB (Or.inl hAB)).1

/-- Similar segments of circles on equal straight lines are equal to one another. -/
theorem Prop24 {A B C D E F : Point} {AEB CFD : Circle} (hAEB : ∃ O : Point, Centre O AEB)
    (hCFD : ∃ O : Point, Centre O CFD) (hA : OnCircle A AEB) (hB : OnCircle B AEB)
    (hE : OnCircle E AEB) (hC : OnCircle C CFD) (hD : OnCircle D CFD)
    (hF : OnCircle F CFD) (hE_AB : ¬ Collinear A B E) (hF_CD : ¬ Collinear C D F)
    (hAB : ‖A B‖ = ‖C D‖) (hsim : ∠ A E B = ∠ C F D) :
    EqualCircles AEB CFD ∧ circumference AEB A E B = circumference CFD C F D := by
  -- For let AEB, CFD be similar segments of circles on equal straight lines AB, CD;
  obtain ⟨M, hM⟩ := hAEB
  obtain ⟨N, hN⟩ := hCFD
  have hABE : Triangle A B E := hE_AB
  have hCDF : Triangle C D F := hF_CD
  obtain ⟨X, hX, hXE⟩ := exists_onCircle_oppositeSidesOf hA hB hABE
  obtain ⟨Y, hY, hYF⟩ := exists_onCircle_oppositeSidesOf hC hD hCDF
  -- I say that the segment AEB is equal to the segment CFD.
  -- For, if the segment AEB be applied to CFD, and if the point A be placed on C and the
  -- straight line AB on CD,
  /- In place of applying the segment, we compare the circles by their radii MA, NC, from
     the centres M, N. -/
  have hMA : ‖M A‖ = ‖M B‖ := Definition15 hM hA hB
  have hNC : ‖N C‖ = ‖N D‖ := Definition15 hN hC hD
  -- the point B will also coincide with the point D, because AB is equal to CD;
  /- On the equal bases AB, CD, equal angles at the centres make the radii equal, by III.20
     and `Prop24.isosceles`; and so do two diameters, each the double of a radius. -/
  have central : ∀ {P Q : Point}, OnCircle P AEB → OnCircle Q CFD → SameSideOf M P A B →
      SameSideOf N Q C D → ∠ A P B = ∠ C Q D → ‖M A‖ = ‖N C‖ := by
    intro P Q hP hQ hMP hNQ hPQ
    exact Prop24.isosceles hMP.triangle hNQ.triangle hMA hNC hAB (by
      rw [Prop20 hM hP hA hB hMP, Prop20 hN hQ hC hD hNQ, hPQ])
  have diam : Between A M B → Between C N D → ‖M A‖ = ‖N C‖ := by
    intro hAMB hCND
    have d₁ : ‖A B‖ = ‖M A‖ + ‖M A‖ := by
      rw [← len_add_of_between hAMB, len_symm A M, ← hMA]
    have d₂ : ‖C D‖ = ‖N C‖ + ‖N C‖ := by
      rw [← len_add_of_between hCND, len_symm C N, ← hNC]
    exact Magnitude.eq_of_add_self_eq (d₁.symm.trans (hAB.trans d₂))
  -- and, AB coinciding with CD,
  /- The segments on the other sides of AB, CD, at X and Y, are similar too: the angle in
     each makes two right angles with the angle at E or F [III. 22]. -/
  have q₁ : ∠ A E B + ∠ A X B = ∟ + ∟ := by
    have := (Prop22 ⟨M, hM⟩ hE hA hX hB hXE.symm).2
    rwa [angle_symm hXE.triangle.ne₂₃ hXE.triangle.ne₁₃] at this
  have q₂ : ∠ C F D + ∠ C Y D = ∟ + ∟ := by
    have := (Prop22 ⟨N, hN⟩ hF hC hY hD hYF.symm).2
    rwa [angle_symm hYF.triangle.ne₂₃ hYF.triangle.ne₁₃] at this
  have hXY : ∠ A X B = ∠ C Y D := by
    apply CommonNotion3 (c := ∠ A E B) (d := ∠ C F D) _ hsim
    rw [add_comm (∠ A X B), q₁, add_comm (∠ C Y D), q₂]
  -- the segment AEB will also coincide with CFD.
  /- The circles are equal. The equal angles at E, F are both less than a right angle,
     both right, or both greater, so the centres lie alike: on the sides of E and F, on the
     bases, or beyond them, where X and Y serve. -/
  have hrad : ‖M A‖ = ‖N C‖ := by
    rcases Prop24.angle_type hM hA hB hE hABE with ⟨hME, hlt⟩ | ⟨hAMB, hrt⟩ | ⟨hME, hgt⟩ <;>
      rcases Prop24.angle_type hN hC hD hF hCDF with ⟨hNF, hlt'⟩ | ⟨hCND, hrt'⟩ | ⟨hNF, hgt'⟩
    · exact central hE hF hME hNF hsim
    · rw [hsim, hrt'] at hlt; exact absurd hlt (lt_irrefl _)
    · rw [hsim] at hlt; exact absurd (lt_trans hlt hgt') (lt_irrefl _)
    · rw [← hsim, hrt] at hlt'; exact absurd hlt' (lt_irrefl _)
    · exact diam hAMB hCND
    · rw [← hsim, hrt] at hgt'; exact absurd hgt' (lt_irrefl _)
    · rw [hsim] at hgt; exact absurd (lt_trans hlt' hgt) (lt_irrefl _)
    · rw [hsim, hrt'] at hgt; exact absurd hgt (lt_irrefl _)
    · exact central hX hY (OppositeSidesOf.sameSideOf hME.symm hXE.symm)
        (OppositeSidesOf.sameSideOf hNF.symm hYF.symm) hXY
  -- For, if the straight line AB coincide with CD but the segment AEB do not coincide with
  -- CFD,
  -- it will either fall within it, or outside it;
  -- or it will fall awry, as CGD, and a circle cuts a circle at more points than two: which is
  -- impossible. [III. 10]
  /- The radii are already equal, by the angles at the centres, so nothing is left for
     III.10 to refute. -/
  -- Therefore, if the straight line AB be applied to CD, the segment AEB will not fail to
  -- coincide with CFD also;
  refine ⟨⟨M, N, A, C, hM, hN, hA, hC, hrad⟩, ?_⟩
  -- therefore it will coincide with it and will be equal to it.
  /- Each circumference, with the one on the other side of its base, which is twice the
     angle at E or F, makes up the whole circle; so the remainders are equal [C.N. 3]. -/
  have w₁ := Circumference.whole ⟨M, hM⟩ hA hB hXE
  have w₂ := Circumference.whole ⟨N, hN⟩ hC hD hYF
  rw [Circumference.eq ⟨M, hM⟩ hE hA hB hXE.symm] at w₁
  rw [Circumference.eq ⟨N, hN⟩ hF hC hD hYF.symm, ← hsim] at w₂
  exact CommonNotion3 (w₁.trans w₂.symm) rfl
  -- Therefore etc.
  -- Q. E. D.

/-- **III.24, the circles and the measures** (companion of III.24, "III.24 equalCircles").
Similar segments on equal straight lines lie in equal circles, and their circumferences are
equal in measure. This is the proof by the radii (the angles at the centres, III.20 and
III.22, and isosceles triangles on the equal bases, `Prop24.isosceles`), an alternative to
Euclid's application of one segment to the other, and labelled so on the page, with
Euclid's text in full under the main proof. The measures follow from the equal angles
alone; the equal bases are needed for the circles. `Arc.congruent_iff` cites it for the
equal circles. -/
theorem Prop24.equalCircles {A B C D E F : Point} {AEB CFD : Circle}
    (hAEB : ∃ O : Point, Centre O AEB) (hCFD : ∃ O : Point, Centre O CFD)
    (hA : OnCircle A AEB) (hB : OnCircle B AEB) (hE : OnCircle E AEB) (hC : OnCircle C CFD)
    (hD : OnCircle D CFD) (hF : OnCircle F CFD) (hE_AB : ¬ Collinear A B E)
    (hF_CD : ¬ Collinear C D F) (hAB : ‖A B‖ = ‖C D‖) (hsim : ∠ A E B = ∠ C F D) :
    EqualCircles AEB CFD ∧ circumference AEB A E B = circumference CFD C F D := by
  obtain ⟨M, hM⟩ := hAEB
  obtain ⟨N, hN⟩ := hCFD
  have hABE : Triangle A B E := hE_AB
  have hCDF : Triangle C D F := hF_CD
  obtain ⟨X, hX, hXE⟩ := exists_onCircle_oppositeSidesOf hA hB hABE
  obtain ⟨Y, hY, hYF⟩ := exists_onCircle_oppositeSidesOf hC hD hCDF
  /- We compare the circles by their radii MA, NC, from the centres M, N. -/
  have hMA : ‖M A‖ = ‖M B‖ := Definition15 hM hA hB
  have hNC : ‖N C‖ = ‖N D‖ := Definition15 hN hC hD
  /- On the equal bases AB, CD, equal angles at the centres make the radii equal, by III.20
     and `Prop24.isosceles`; and so do two diameters, each the double of a radius. -/
  have central : ∀ {P Q : Point}, OnCircle P AEB → OnCircle Q CFD → SameSideOf M P A B →
      SameSideOf N Q C D → ∠ A P B = ∠ C Q D → ‖M A‖ = ‖N C‖ := by
    intro P Q hP hQ hMP hNQ hPQ
    exact Prop24.isosceles hMP.triangle hNQ.triangle hMA hNC hAB (by
      rw [Prop20 hM hP hA hB hMP, Prop20 hN hQ hC hD hNQ, hPQ])
  have diam : Between A M B → Between C N D → ‖M A‖ = ‖N C‖ := by
    intro hAMB hCND
    have d₁ : ‖A B‖ = ‖M A‖ + ‖M A‖ := by
      rw [← len_add_of_between hAMB, len_symm A M, ← hMA]
    have d₂ : ‖C D‖ = ‖N C‖ + ‖N C‖ := by
      rw [← len_add_of_between hCND, len_symm C N, ← hNC]
    exact Magnitude.eq_of_add_self_eq (d₁.symm.trans (hAB.trans d₂))
  /- The segments on the other sides of AB, CD, at X and Y, are similar too: the angle in
     each makes two right angles with the angle at E or F [III. 22]. -/
  have q₁ : ∠ A E B + ∠ A X B = ∟ + ∟ := by
    have := (Prop22 ⟨M, hM⟩ hE hA hX hB hXE.symm).2
    rwa [angle_symm hXE.triangle.ne₂₃ hXE.triangle.ne₁₃] at this
  have q₂ : ∠ C F D + ∠ C Y D = ∟ + ∟ := by
    have := (Prop22 ⟨N, hN⟩ hF hC hY hD hYF.symm).2
    rwa [angle_symm hYF.triangle.ne₂₃ hYF.triangle.ne₁₃] at this
  have hXY : ∠ A X B = ∠ C Y D := by
    apply CommonNotion3 (c := ∠ A E B) (d := ∠ C F D) _ hsim
    rw [add_comm (∠ A X B), q₁, add_comm (∠ C Y D), q₂]
  /- The circles are equal. The equal angles at E, F are both less than a right angle,
     both right, or both greater, so the centres lie alike: on the sides of E and F, on the
     bases, or beyond them, where X and Y serve. -/
  have hrad : ‖M A‖ = ‖N C‖ := by
    rcases Prop24.angle_type hM hA hB hE hABE with ⟨hME, hlt⟩ | ⟨hAMB, hrt⟩ | ⟨hME, hgt⟩ <;>
      rcases Prop24.angle_type hN hC hD hF hCDF with ⟨hNF, hlt'⟩ | ⟨hCND, hrt'⟩ | ⟨hNF, hgt'⟩
    · exact central hE hF hME hNF hsim
    · rw [hsim, hrt'] at hlt; exact absurd hlt (lt_irrefl _)
    · rw [hsim] at hlt; exact absurd (lt_trans hlt hgt') (lt_irrefl _)
    · rw [← hsim, hrt] at hlt'; exact absurd hlt' (lt_irrefl _)
    · exact diam hAMB hCND
    · rw [← hsim, hrt] at hgt'; exact absurd hgt' (lt_irrefl _)
    · rw [hsim] at hgt; exact absurd (lt_trans hlt' hgt) (lt_irrefl _)
    · rw [hsim, hrt'] at hgt; exact absurd hgt (lt_irrefl _)
    · exact central hX hY (OppositeSidesOf.sameSideOf hME.symm hXE.symm)
        (OppositeSidesOf.sameSideOf hNF.symm hYF.symm) hXY
  /- The equal radii MA, NC make the circles equal (Definition III.1). -/
  refine ⟨⟨M, N, A, C, hM, hN, hA, hC, hrad⟩, ?_⟩
  /- Each circumference, with the one on the other side of its base, which is twice the
     angle at E or F, makes up the whole circle; so the remainders are equal [C.N. 3]. -/
  have w₁ := Circumference.whole ⟨M, hM⟩ hA hB hXE
  have w₂ := Circumference.whole ⟨N, hN⟩ hC hD hYF
  rw [Circumference.eq ⟨M, hM⟩ hE hA hB hXE.symm] at w₁
  rw [Circumference.eq ⟨N, hN⟩ hF hC hD hYF.symm, ← hsim] at w₂
  exact CommonNotion3 (w₁.trans w₂.symm) rfl

/-- The check: `Prop24.equalCircles` has the statement of `Prop24` (checked by Lean, up to
unfolding definitions). -/
example : type_of% @Elements.BookIII.Prop24 := @Prop24.equalCircles

/-- **A point of the arc, and its image.** In two congruent drawn segments, the map carries a
point P of the first arc, off its base, to a point Q of the second arc, off its base, and the
bases are equal. The map keeps the base and the distances from P to its ends, so the triangles
on the bases with vertices P and Q have their three sides equal, and the base subtends equal
angles at P and Q [I. 8]: the segments are similar (Definition III.11). Q is off the base, for
a point of the circle on the base is one of its ends (`chord_cases`), and were Q an end, P
would be the corresponding end, being as far from it. `Prop24.equalMeasure` and
`Arc.congruent_iff` both take this step from a congruence. -/
theorem Prop24.image {a b : Arc} (ha : a.Drawn) (hb : b.Drawn)
    (h : Arc.Congruent a b) {P : Point} (hP : OnCircle P a.circle)
    (hPK : SameSideOf P a.K a.B a.C) :
    ‖a.B a.C‖ = ‖b.B b.C‖ ∧ ∃ Q : Point, OnCircle Q b.circle ∧
      SameSideOf Q b.K b.B b.C ∧ ∠ a.B P a.C = ∠ b.B Q b.C := by
  obtain ⟨-, hB, hC, -⟩ := ha
  obtain ⟨-, hD, hE, hL⟩ := hb
  obtain ⟨f, hfB, hfC, -, hinto, -, hdist⟩ := h
  /- The ends of the base are points of the arc, and so is P. -/
  obtain ⟨M, hB_M, hC_M⟩ := Postulate1 a.B a.C hPK.triangle.ne₁₂
  have hBa : OnArc a.B a := ⟨hB, Or.inr ⟨M, hB_M, hC_M, hB_M⟩⟩
  have hCa : OnArc a.C a := ⟨hC, Or.inr ⟨M, hB_M, hC_M, hC_M⟩⟩
  have hPa : OnArc P a := ⟨hP, Or.inl hPK⟩
  /- The map keeps the base, and the distances from P to its ends. -/
  have hBC : ‖a.B a.C‖ = ‖b.B b.C‖ := by
    rw [← hfB, ← hfC]; exact (hdist a.B a.C hBa hCa).symm
  have hPB : ‖P a.B‖ = ‖(f P) b.B‖ := by
    rw [← hfB]; exact (hdist P a.B hPa hBa).symm
  have hPC : ‖P a.C‖ = ‖(f P) b.C‖ := by
    rw [← hfC]; exact (hdist P a.C hPa hCa).symm
  /- The image of P is a point of the second arc, and off its base: there it would be an end
     (`chord_cases`), and P, as far from the corresponding end as its image is, would be that
     end. -/
  obtain ⟨hQ, hQside⟩ := hinto P hPa
  have hQBC : ¬ Collinear b.B b.C (f P) := by
    intro hcol
    rcases (chord_cases hD hE (show Triangle b.B b.C b.K from hL).ne₁₂ hcol).1.mp hQ with
      hQB | hQC
    · rw [hQB, len_self] at hPB
      exact len_ne_zero hPK.triangle.ne₁₃.symm hPB
    · rw [hQC, len_self] at hPC
      exact len_ne_zero hPK.triangle.ne₂₃.symm hPC
  have hQL : SameSideOf (f P) b.K b.B b.C := hQside.resolve_right hQBC
  /- The triangles on the bases with vertices P and its image have their three sides equal,
     so the angles at P and its image are equal [I. 8]. -/
  exact ⟨hBC, f P, hQ, hQL, BookI.Prop8 hPK.triangle.cab hQL.triangle.cab hPB hPC hBC⟩

/-- **Congruent segments have equal circumferences** (companion of III.24, "III.24
equalMeasure"). If two drawn segments are congruent, their circumferences are equal in
measure. III.26 cites it after III.24, where Euclid passes from the equal segments to the
equal circumferences [III. 24]; nothing before III.26 says it otherwise, for `Arc.congruent_iff`
comes after III.29.

Proved: take a point P of the first arc off its base [`exists_onCircle_sameSideOf`]; its
image is a point of the second arc, off its base (it is neither end, being as far from each
as P is, and `chord_cases`); the congruence keeps the distances from P to the ends, so the
angle at P is the angle at its image [I. 8] (these steps are `Prop24.image`); the
circumference on the other side of each base is twice that angle (`Circumference.eq`), and
with it each circumference makes up the whole circle (`Circumference.whole`); so the
circumferences are equal [C.N. 3]. -/
theorem Prop24.equalMeasure {a b : Arc} (ha : a.Drawn) (hb : b.Drawn)
    (h : Arc.Congruent a b) : a.measure = b.measure := by
  obtain ⟨hα, hB, hC, hK⟩ := id ha
  obtain ⟨hβ, hD, hE, hL⟩ := id hb
  /- Take a point P of the first arc off its base. Its image Q is a point of the second arc,
     off its base, and the bases subtend equal angles at P and Q (`Prop24.image`). -/
  obtain ⟨P, hP, hPK⟩ := exists_onCircle_sameSideOf hB hC hK
  obtain ⟨-, Q, hQ, hQL, hPQ⟩ := Prop24.image ha hb h hP hPK
  /- The circumferences on the other sides of the bases, named by points X and Y there, are
     twice those equal angles (`Circumference.eq`), and so are equal. -/
  obtain ⟨X, hXK, -⟩ := exists_oppositeSidesOf (show Triangle a.B a.C a.K from hK) []
  obtain ⟨Y, hYL, -⟩ := exists_oppositeSidesOf (show Triangle b.B b.C b.K from hL) []
  have hXY : circumference a.circle a.B X a.C = circumference b.circle b.B Y b.C := by
    rw [Circumference.eq hα hP hB hC (hPK.trans_opposite hXK.symm),
      Circumference.eq hβ hQ hD hE (hQL.trans_opposite hYL.symm), hPQ]
  /- Each given circumference, with the one on the other side of its base, makes up the
     whole circle (`Circumference.whole`); the remainders of the equal wholes are equal
     [C.N. 3]. -/
  exact CommonNotion3 ((Circumference.whole hα hB hC hXK).trans
    (Circumference.whole hβ hD hE hYL).symm) hXY

end Elements.BookIII
