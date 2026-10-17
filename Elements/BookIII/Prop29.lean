import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop04
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
  obtain ⟨A, hA, hAG⟩ := exists_onCircle_oppositeSidesOf hB hC hBCG
  obtain ⟨D, hD, hDH⟩ := exists_onCircle_oppositeSidesOf hE hF hEFH
  -- I say that BC is equal to EF.
  -- For let the centres of the circles be taken, and let them be K, L; let BK, KC, EL, LF be
  -- joined.
  obtain ⟨K, L, -, -, hK, hL, -, -, -⟩ := id hcircles
  /- Euclid's figure has each centre off its straight line. When K is on BC, BGC is a
     semicircle, and so is EHF, so BC and EF are diameters of equal circles, each twice
     the radius. -/
  by_cases hKBC : Collinear B C K
  · obtain ⟨N, hB_N, hC_N, hK_N⟩ := hKBC
    have hBKC := between_of_inside_chord hK_N hB_N hC_N (centre_inside hK) hB hC hBCG.ne₁₂
    have hsemi := Circumference.semicircle hK hB hC hBKC hBCG
    rcases Prop29.size hL hE hF hEFH with ⟨-, hlt'⟩ | ⟨hELF, -⟩ | ⟨-, hgt'⟩
    · exact absurd (heq ▸ hsemi ▸ hlt') (lt_irrefl _)
    · rw [← len_add_of_between hBKC, ← len_add_of_between hELF, len_symm B K,
        hcircles.radii hK hL hB hE, hcircles.radii hK hL hC hF, len_symm E L]
    · exact absurd (heq ▸ hsemi ▸ hgt') (lt_irrefl _)
  -- Now, since the circumference BGC is equal to the circumference EHF,
  /- Otherwise the angle BKC stands on the circumference beyond BC from K. In Euclid's
     figure that is BGC, for K is beyond it; if not, it is BAC, the circumference which
     remains, and the remaining circumferences are equal, since the wholes are
     (`Circumference.whole`) [C.N. 3]. Equal circumferences are of one kind, so L's case
     matches K's. III.27 measures each at a point X, Y of its circle on the centre's
     side. -/
  obtain ⟨X, Y, hX, hY, hKX, hLY, hst⟩ : ∃ X Y : Point, OnCircle X ABC ∧ OnCircle Y DEF ∧
      SameSideOf K X B C ∧ SameSideOf L Y E F ∧ standing ABC B X C = standing DEF E Y F := by
    rcases Prop29.size hK hB hC hBCG with ⟨hKG, hlt⟩ | ⟨hBKC, -⟩ | ⟨hKG, hgt⟩
    · rcases Prop29.size hL hE hF hEFH with ⟨hLH, -⟩ | ⟨-, hsemi'⟩ | ⟨-, hgt'⟩
      · refine ⟨A, D, hA, hD, OppositeSidesOf.sameSideOf hKG.symm hAG.symm,
          OppositeSidesOf.sameSideOf hLH.symm hDH.symm, ?_⟩
        rw [standing_eq_circumference hAG, standing_eq_circumference hDH, heq]
      · exact absurd (hsemi' ▸ heq ▸ hlt) (lt_irrefl _)
      · exact absurd (lt_trans (heq ▸ hlt) hgt') (lt_irrefl _)
    · exact absurd (collinear_of_between hBKC) (fun h => hKBC (by
        obtain ⟨N, h1, h2, h3⟩ := h; exact ⟨N, h1, h3, h2⟩))
    · rcases Prop29.size hL hE hF hEFH with ⟨-, hlt'⟩ | ⟨-, hsemi'⟩ | ⟨hLH, -⟩
      · exact absurd (lt_trans hlt' (heq ▸ hgt)) (lt_irrefl _)
      · exact absurd (hsemi' ▸ heq ▸ hgt) (lt_irrefl _)
      · obtain ⟨X, hX, hXG⟩ := exists_onCircle_sameSideOf hB hC hBCG
        obtain ⟨Y, hY, hYH⟩ := exists_onCircle_sameSideOf hE hF hEFH
        refine ⟨X, Y, hX, hY, hKG.trans hXG.symm, hLH.trans hYH.symm, ?_⟩
        rw [standing_eq_circumference (hXG.trans_opposite hAG.symm),
          standing_eq_circumference (hYH.trans_opposite hDH.symm)]
        have hw₁ := Circumference.whole ⟨K, hK⟩ hB hC hAG
        have hw₂ := Circumference.whole ⟨L, hL⟩ hE hF hDH
        refine CommonNotion3 (c := circumference ABC B G C) (d := circumference DEF E H F) ?_ heq
        calc
          _ = circumference ABC B G C + circumference ABC B A C := by ac_rfl
          _ = circumference DEF E H F + circumference DEF E D F := hw₁.trans hw₂.symm
          _ = _ := by ac_rfl
  -- the angle BKC is also equal to the angle ELF. [III. 27]
  have hBKC : ∠ B K C = ∠ E L F :=
    (Prop27 hcircles hK hL hX hB hC hY hE hF hKX.symm.triangle.acb hLY.symm.triangle.acb
      hst).2 hKX hLY
  -- And, since the circles ABC, DEF are equal,
  -- the radii are also equal;
  have hrB : ‖K B‖ = ‖L E‖ := hcircles.radii hK hL hB hE
  have hrC : ‖K C‖ = ‖L F‖ := hcircles.radii hK hL hC hF
  -- therefore the two sides BK, KC are equal to the two sides EL, LF; and they contain equal
  -- angles;
  -- therefore the base BC is equal to the base EF. [I. 4]
  exact (BookI.Prop4 hKX.triangle.cab hLY.triangle.cab hrB hrC hBKC).1
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
