import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop08
import Elements.BookI.Prop20
import Elements.BookIII.Prop02
import Elements.BookIII.Prop20
import Elements.BookIII.Prop24
import Elements.BookIII.Prop26

/-!
# Book III, Proposition 28

Euclid's text, in Heath's translation: [`heath/III/28.md`](../../heath/III/28.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Each clause concludes that the circumferences are equal in measure and congruent
(`Arc.Congruent`): equal circumferences are read as in III.26, which says more than Heath's
words. The proof follows Euclid's route where it can: the angles AKB, DLE at the centres are
equal [I. 8], so the less circumferences are equal in measure and congruent [III. 26], and
the greater are equal in measure as the remainders [C.N. 3]. Two steps depart from it, as
III.26's own congruence does. The congruence of the greater circumferences cannot come by
subtraction; it comes from III.24 applied to the greater segments, which are similar, the
angles in them being the halves of the equal angles at the centres [III. 20]. And when AB
passes through the centre, the four circumferences are semicircles. The angle at the centre
of each is two right angles (`angleAtCentre.semicircle`), but there are no triangle angles
AKB, DLE for III.26's central-angle clause to use; the angle in each semicircle is right
(`Prop28.right`, from `Prop24.angle_type`, since III.31 comes later), and III.24 gives the
congruence.
-/

namespace Elements.BookIII

open Tacit

/-- A point K lies on C's side of the straight line AB, on AB, or on the other side, for
a straight line has two sides. Here K is the centre. -/
theorem Prop28.sides {A B C K : Point} (hABC : Triangle A B C) :
    SameSideOf K C A B ∨ Collinear A B K ∨ OppositeSidesOf K C A B := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B hABC.ne₁₂
  have hC : ¬ OnLine C L := hABC.off_line hA hB
  by_cases hK : OnLine K L
  · exact Or.inr (Or.inl ⟨L, hA, hB, hK⟩)
  by_cases hs : SameSide K C L
  · exact Or.inl (SameSideOf.of_line hABC.ne₁₂ hA hB hs)
  · exact Or.inr (Or.inr (OppositeSidesOf.of_line hABC.ne₁₂ hA hB ⟨hK, hC, hs⟩))

/-- In equal circles, a straight line equal to a diameter of the one is a diameter of the
other: else, with the radii to its ends, it would be less than two radii. [I. 20] -/
theorem Prop28.diameter {A B D E K L : Point} {α β : Circle} (hK : Centre K α) (hL : Centre L β)
    (hA : OnCircle A α) (hB : OnCircle B α) (hD : OnCircle D β) (hE : OnCircle E β)
    (hr : ‖K A‖ = ‖L D‖) (hAKB : Between A K B) (hAB : ‖A B‖ = ‖D E‖) (hDE : D ≠ E) :
    Between D L E := by
  have hAB' : ‖A B‖ = ‖K A‖ + ‖K A‖ := by
    rw [← len_add_of_between hAKB, len_symm A K, Definition15 hK hB hA]
  by_cases hcol : Collinear D E L
  · obtain ⟨M, hD_M, hE_M, hL_M⟩ := hcol
    exact between_of_inside_chord hL_M hD_M hE_M (centre_inside hL) hD hE hDE
  · have h20 := (BookI.Prop20 (show Triangle D E L from hcol).cab).1
    rw [← hAB, hAB', len_symm D L, hr, Definition15 hL hE hD] at h20
    exact absurd h20 (lt_irrefl _)

/-- The centre does not lie on the side of the less circumference: the circumference
beyond the centre is less than a semicircle, and the one on its side greater. -/
theorem Prop28.beyond {X Y P Q M : Point} {α : Circle} (hM : Centre M α) (hX : OnCircle X α)
    (hY : OnCircle Y α) (hPQ : OppositeSidesOf P Q X Y)
    (hle : circumference α X Q Y ≤ circumference α X P Y) : ¬ SameSideOf M Q X Y := fun hMQ =>
  hle (lt_trans (Circumference.lt_semicircle hM hX hY (hMQ.trans_opposite hPQ.symm))
    (Circumference.gt_semicircle hM hX hY hMQ))

/-- In a semicircle the angle is right: for a diameter AB of a circle, through its centre K,
and a point X of the circle off AB, the angle AXB is a right angle. Of the three cases of
`Prop24.angle_type`, the acute and the obtuse put the centre off AB, so only the right angle
is left. Euclid proves this in III.31; III.28's case with AB through the centre, which his
figure leaves aside, needs it first. -/
theorem Prop28.right {A B X K : Point} {α : Circle} (hK : Centre K α)
    (hA : OnCircle A α) (hB : OnCircle B α) (hX : OnCircle X α)
    (hAKB : Between A K B) (hABX : Triangle A B X) : ∠ A X B = ∟ := by
  have hKAB : Collinear A B K := by
    obtain ⟨M, hA_M, hK_M, hB_M⟩ := collinear_of_between hAKB
    exact ⟨M, hA_M, hB_M, hK_M⟩
  rcases Prop24.angle_type hK hA hB hX hABX with ⟨hKX, -⟩ | ⟨-, hright⟩ | ⟨hKX, -⟩
  · exact False.elim (hKX.triangle hKAB)
  · exact hright
  · exact False.elim (hKX.triangle hKAB)

/-- In equal circles equal straight lines cut off equal circumferences, the greater equal to the
greater and the less to the less. -/
theorem Prop28 {A B C D E F G H : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hCG : OppositeSidesOf C G A B) (hFH : OppositeSidesOf F H D E) (hAB : ‖A B‖ = ‖D E‖)
    (hABC : circumference ABC A G B ≤ circumference ABC A C B)
    (hDEF : circumference DEF D H E ≤ circumference DEF D F E) :
    (circumference ABC A C B = circumference DEF D F E ∧
        Arc.Congruent ⟨ABC, A, B, C⟩ ⟨DEF, D, E, F⟩) ∧
      (circumference ABC A G B = circumference DEF D H E ∧
        Arc.Congruent ⟨ABC, A, B, G⟩ ⟨DEF, D, E, H⟩) := by
  -- Let ABC, DEF be equal circles, and in the circles let AB, DE be equal straight lines
  -- cutting off ACB, DFE as greater circumferences and AGB, DHE as lesser;
  -- I say that the greater circumference ACB is equal to the greater circumference DFE, and
  -- the less circumference AGB to DHE.
  -- For let the centres K, L of the circles be taken, and let AK, KB, DL, LE be joined.
  obtain ⟨K, L, -, -, hK, hL, -⟩ := id hcircles
  -- Now, since the circles are equal,
  -- the radii are also equal;
  have hr : ‖K A‖ = ‖L D‖ := hcircles.radii hK hL hA hD
  have hrB : ‖K B‖ = ‖L E‖ := hcircles.radii hK hL hB hE
  /- Euclid's figure has K beyond the less circumference AGB, on C's side of AB. If K is
     on AB, then AB is a diameter, and so is DE (`Prop28.diameter`), and the four
     circumferences are semicircles; and K is not on G's side (`Prop28.beyond`). -/
  rcases Prop28.sides (K := K) hCG.triangle with hKC | ⟨M, hA_M, hB_M, hK_M⟩ | hKC
  rotate_left
  · have hAKB := between_of_inside_chord hK_M hA_M hB_M (centre_inside hK) hA hB hCG.1
    have hDLE := Prop28.diameter hK hL hA hB hD hE hr hAKB hAB hFH.1
    /- Here the angle at the centre is two right angles (`angleAtCentre.semicircle`). We
       obtain congruence from the right angles in the semicircles (`Prop28.right`): the
       segments on matching sides are similar and, on the equal diameters, congruent
       [III. 24]. -/
    have hcongr : ∀ {P Q : Point}, Triangle A B P → Triangle D E Q →
        Arc.Congruent ⟨ABC, A, B, P⟩ ⟨DEF, D, E, Q⟩ := by
      intro P Q hABP hDEQ
      obtain ⟨X, hX, hXP⟩ := Prop2.sameSide hA hB hABP
      obtain ⟨Y, hY, hYQ⟩ := Prop2.sameSide hD hE hDEQ
      have hXrt : ∠ A X B = ∟ := Prop28.right hK hA hB hX hAKB hXP.triangle
      have hYrt : ∠ D Y E = ∟ := Prop28.right hL hD hE hY hDLE hYQ.triangle
      have hXY := Prop24 hA hB hX hD hE hY
        hXP.triangle hYQ.triangle hAB (hXrt.trans hYrt.symm)
      exact hXY.congr_side hXP hYQ
    refine ⟨⟨?_, hcongr hCG.triangle hFH.triangle⟩,
      ⟨?_, hcongr hCG.symm.triangle hFH.symm.triangle⟩⟩
    · rw [Circumference.semicircle hK hA hB hAKB hCG.triangle,
        Circumference.semicircle hL hD hE hDLE hFH.triangle]
    · rw [Circumference.semicircle hK hA hB hAKB hCG.symm.triangle,
        Circumference.semicircle hL hD hE hDLE hFH.symm.triangle]
  · exact absurd (OppositeSidesOf.sameSideOf hKC.symm hCG) (Prop28.beyond hK hA hB hCG hABC)
  /- Likewise L is on F's side of DE. Were L on DE, AB would be a diameter too, through
     K, which is off AB. -/
  rcases Prop28.sides (K := L) hFH.triangle with hLF | ⟨M, hD_M, hE_M, hL_M⟩ | hLF
  rotate_left
  · have hDLE := between_of_inside_chord hL_M hD_M hE_M (centre_inside hL) hD hE hFH.1
    have hAKB := Prop28.diameter hL hK hD hE hA hB hr.symm hDLE hAB.symm hCG.1
    exact False.elim (hKC.triangle.acb (collinear_of_between hAKB))
  · exact absurd (OppositeSidesOf.sameSideOf hLF.symm hFH) (Prop28.beyond hL hD hE hFH hDEF)
  have hKG : OppositeSidesOf K G A B := hKC.trans_opposite hCG
  have hLH : OppositeSidesOf L H D E := hLF.trans_opposite hFH
  -- therefore the two sides AK, KB are equal to the two sides DL, LE;
  -- and the base AB is equal to the base DE;
  -- therefore the angle AKB is equal to the angle DLE. [I. 8]
  have hAKB : ∠ A K B = ∠ D L E := BookI.Prop8 hKG.triangle.cab hLH.triangle.cab hr hrB hAB
  -- But equal angles stand on equal circumferences, when they are at the centres; [III. 26]
  /- C and F name sides, not necessarily points of the circles, so we take a point of each
     circle on that side for III.26. -/
  obtain ⟨X, hX, hXG⟩ := Prop2.oppositeSide hA hB hCG.symm.triangle
  obtain ⟨Y, hY, hYH⟩ := Prop2.oppositeSide hD hE hFH.symm.triangle
  -- therefore the circumference AGB is equal to DHE.
  have hless : circumference ABC A G B = circumference DEF D H E ∧
      Arc.Congruent ⟨ABC, A, B, G⟩ ⟨DEF, D, E, H⟩ :=
    (Prop26 hcircles hK hL hX hA hB hY hD hE hXG hYH).1 hKG hLH hAKB
  -- And the whole circle ABC is also equal to the whole circle DEF;
  have hw₁ := Circumference.whole hA hB hCG.symm
  have hw₂ := Circumference.whole hD hE hFH.symm
  -- therefore the circumference ACB which remains is also equal to the circumference DFE which
  -- remains.
  have hgreater : circumference ABC A C B = circumference DEF D F E :=
    CommonNotion3 (hw₁.trans hw₂.symm) hless.1
  /- The congruence of the greater circumferences cannot come by subtraction. X and Y lie on
     the greater arcs, and the angles AXB, DYE are the halves of the equal angles AKB, DLE at
     the centres [III. 20]; so the greater segments are similar, and on the equal straight
     lines AB, DE they are congruent [III. 24], named by C and F
     (`Arc.Congruent.congr_side`). -/
  have hKX : SameSideOf K X A B := OppositeSidesOf.sameSideOf hKG.symm hXG.symm
  have hLY : SameSideOf L Y D E := OppositeSidesOf.sameSideOf hLH.symm hYH.symm
  have hXY : ∠ A X B = ∠ D Y E := Magnitude.eq_of_add_self_eq
    ((Prop20.special hK hX hA hB hKX).symm.trans
      (hAKB.trans (Prop20.special hL hY hD hE hLY)))
  have hAXB := Prop24 hA hB hX hD hE hY
    hXG.triangle hYH.triangle hAB hXY
  have hACB : Arc.Congruent ⟨ABC, A, B, C⟩ ⟨DEF, D, E, F⟩ :=
    hAXB.congr_side (OppositeSidesOf.sameSideOf hXG.symm hCG.symm)
      (OppositeSidesOf.sameSideOf hYH.symm hFH.symm)
  -- Therefore etc.
  exact ⟨⟨hgreater, hACB⟩, hless⟩
  -- Q. E. D.

/-- The check: the equal measures alone follow from `Prop28` by the first conjunct of each of
its clauses (checked by Lean). -/
example {A B C D E F G H : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hCG : OppositeSidesOf C G A B) (hFH : OppositeSidesOf F H D E) (hAB : ‖A B‖ = ‖D E‖)
    (hABC : circumference ABC A G B ≤ circumference ABC A C B)
    (hDEF : circumference DEF D H E ≤ circumference DEF D F E) :
    circumference ABC A C B = circumference DEF D F E ∧
      circumference ABC A G B = circumference DEF D H E :=
  ⟨(Prop28 hcircles hA hB hD hE hCG hFH hAB hABC hDEF).1.1,
    (Prop28 hcircles hA hB hD hE hCG hFH hAB hABC hDEF).2.1⟩

end Elements.BookIII
