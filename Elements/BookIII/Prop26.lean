import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop04
import Elements.BookIII.Prop20
import Elements.BookIII.Prop22
import Elements.BookIII.Prop24

/-!
# Book III, Proposition 26

Euclid's text, in Heath's translation: [`heath/III/26.md`](../../heath/III/26.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- In equal circles equal angles stand on equal circumferences, whether they stand at the centres
or at the circumferences. -/
theorem Prop26 {A B C D E F G H K L : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hF : OnCircle F DEF) (hAK : OppositeSidesOf A K B C) (hDL : OppositeSidesOf D L E F) :
    (OppositeSidesOf G K B C → OppositeSidesOf H L E F → ∠ B G C = ∠ E H F →
      circumference ABC B K C = circumference DEF E L F) ∧
    (∠ B A C = ∠ E D F → circumference ABC B K C = circumference DEF E L F) := by
  -- Let ABC, DEF be equal circles, and in them let there be equal angles, namely at the
  -- centres the angles BGC, EHF, and at the circumferences the angles BAC, EDF;
  -- I say that the circumference BKC is equal to the circumference ELF.
  -- For let BC, EF be joined.
  have hBCA : Triangle B C A := hAK.triangle
  have hEFD : Triangle E F D := hDL.triangle
  -- Now, since the circles ABC, DEF are equal,
  -- the radii are equal.
  have hGB : ‖G B‖ = ‖H E‖ := hcircles.radii hG hH hB hE
  have hGC : ‖G C‖ = ‖H F‖ := hcircles.radii hG hH hC hF
  -- Thus the two straight lines BG, GC are equal to the two straight lines EH, HF;
  -- and the angle at G is equal to the angle at H;
  -- therefore the base BC is equal to the base EF. [I. 4]
  have base : Triangle G B C → Triangle H E F → ∠ B G C = ∠ E H F → ‖B C‖ = ‖E F‖ :=
    fun hGBC hHEF h => (BookI.Prop4 hGBC hHEF hGB hGC h).1
  /- When the angles are given at A and D, III.24 sorts them into Heath's three cases,
     acute, right and obtuse (`Prop24.angle_type`), and we take each in turn. -/
  have base' : ∠ B A C = ∠ E D F → ‖B C‖ = ‖E F‖ := by
    intro h
    rcases Prop24.angle_type hG hB hC hA hBCA with ⟨hGA, hlt⟩ | ⟨hBGC, hrt⟩ | ⟨hGA, hgt⟩ <;>
      rcases Prop24.angle_type hH hE hF hD hEFD with ⟨hHD, hlt'⟩ | ⟨hEHF, hrt'⟩ | ⟨hHD, hgt'⟩
    · exact base hGA.triangle.cab hHD.triangle.cab
        (by rw [Prop20 hG hA hB hC hGA, Prop20 hH hD hE hF hHD, h])
    · rw [h, hrt'] at hlt; exact absurd hlt (lt_irrefl _)
    · rw [h] at hlt; exact absurd (lt_trans hlt hgt') (lt_irrefl _)
    · rw [← h, hrt] at hlt'; exact absurd hlt' (lt_irrefl _)
    · rw [← len_add_of_between hBGC, ← len_add_of_between hEHF, len_symm B G, hGB, hGC,
        len_symm E H]
    · rw [← h, hrt] at hgt'; exact absurd hgt' (lt_irrefl _)
    · rw [h] at hgt; exact absurd (lt_trans hlt' hgt) (lt_irrefl _)
    · rw [h, hrt'] at hgt; exact absurd hgt (lt_irrefl _)
    · obtain ⟨X, hX, hXG⟩ := exists_onCircle_sameSideOf hB hC hGA.triangle
      obtain ⟨Y, hY, hYH⟩ := exists_onCircle_sameSideOf hE hF hHD.triangle
      have hXA : OppositeSidesOf X A B C := hXG.trans_opposite hGA
      have hYD : OppositeSidesOf Y D E F := hYH.trans_opposite hHD
      have q₁ : ∠ B A C + ∠ B X C = ∟ + ∟ := by
        have := (Prop22 ⟨G, hG⟩ hA hB hX hC hXA.symm).2
        rwa [angle_symm hXA.triangle.ne₂₃ hXA.triangle.ne₁₃] at this
      have q₂ : ∠ E D F + ∠ E Y F = ∟ + ∟ := by
        have := (Prop22 ⟨H, hH⟩ hD hE hY hF hYD.symm).2
        rwa [angle_symm hYD.triangle.ne₂₃ hYD.triangle.ne₁₃] at this
      have hXY : ∠ B X C = ∠ E Y F :=
        CommonNotion3 (c := ∠ B A C) (d := ∠ E D F)
          (by rw [add_comm (∠ B X C), q₁, add_comm (∠ E Y F), q₂]) h
      exact base hGA.triangle.cab hHD.triangle.cab
        (by rw [Prop20 hG hX hB hC hXG.symm, Prop20 hH hY hE hF hYH.symm, hXY])
  -- And, since the angle at A is equal to the angle at D,
  /- When the angles are given at the centres, the angles at A and D are their halves by
     III.20, and so equal. -/
  have atA : OppositeSidesOf G K B C → OppositeSidesOf H L E F → ∠ B G C = ∠ E H F →
      ∠ B A C = ∠ E D F := by
    intro hGK hHL h
    have h1 := Prop20 hG hA hB hC (OppositeSidesOf.sameSideOf hGK.symm hAK.symm)
    have h2 := Prop20 hH hD hE hF (OppositeSidesOf.sameSideOf hHL.symm hDL.symm)
    exact Magnitude.eq_of_add_self_eq (h1.symm.trans (h.trans h2))
  -- the segment BAC is similar to the segment EDF; [III. Def. 11]
  -- and they are upon equal straight lines.
  -- But similar segments of circles on equal straight lines are equal to one
  -- another; [III. 24]
  -- therefore the segment BAC is equal to EDF.
  have seg : ‖B C‖ = ‖E F‖ → ∠ B A C = ∠ E D F →
      circumference ABC B A C = circumference DEF E D F :=
    fun hBC h => (Prop24 ⟨G, hG⟩ ⟨H, hH⟩ hB hC hA hE hF hD hBCA hEFD hBC h).2
  -- But the whole circle ABC is also equal to the whole circle DEF;
  have w₁ := Circumference.whole ⟨G, hG⟩ hB hC hAK
  have w₂ := Circumference.whole ⟨H, hH⟩ hE hF hDL
  -- therefore the circumference BKC which remains is equal to the circumference ELF.
  have rest : ‖B C‖ = ‖E F‖ → ∠ B A C = ∠ E D F →
      circumference ABC B K C = circumference DEF E L F :=
    fun hBC h => CommonNotion3 (w₁.trans w₂.symm) (seg hBC h)
  -- Therefore etc.
  exact ⟨fun hGK hHL h => rest (base hGK.triangle.cab hHL.triangle.cab h) (atA hGK hHL h),
    fun h => rest (base' h) h⟩
  -- Q. E. D.

end Elements.BookIII
