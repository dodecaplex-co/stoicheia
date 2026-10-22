import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Prop02
import Elements.BookIII.Prop11

/-!
# Book III, Proposition 13

Euclid's text, in Heath's translation: [`heath/III/13.md`](../../heath/III/13.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- A circle does not touch a circle at more points than one, whether it touch it internally or
externally. -/
theorem Prop13 {A B C D : Point} {ABDC EBFD ACK : Circle} :
    ((TouchesInternally ABDC EBFD D ∨ TouchesInternally EBFD ABDC D) →
      OnCircle B ABDC → OnCircle B EBFD → B = D) ∧
    (TouchesExternally ACK ABDC A → OnCircle C ACK → OnCircle C ABDC → C = A) := by
  have within : ∀ {α β : Circle}, TouchesInternally α β D → OnCircle B α → OnCircle B β → B = D := by
    intro α β ht hBα hBβ
    -- For, if possible, let the circle ABDC touch the circle EBFD, first internally, at more
    -- points than one, namely D, B.
    refine Classical.byContradiction fun hBD => ?_
    have htB : TouchesInternally α β B := ⟨hBα, hBβ, ht.2.2.1, ht.2.2.2⟩
    -- Let the centre G of the circle ABDC, and the centre H of EBFD, be taken.
    obtain ⟨G, hG⟩ := exists_centre α
    obtain ⟨H, hH⟩ := exists_centre β
    -- Therefore the straight line joined from G to H will fall on B, D. [III. 11]
    have hGHD : Between G H D := Prop11 hG hH ht
    have hGHB : Between G H B := Prop11 hG hH htB
    obtain ⟨L, hG_L, hH_L⟩ := Postulate1 G H (ne_of_between hGHD)
    have hD_L : OnLine D L := on_line_of_between hGHD hG_L hH_L
    have hB_L : OnLine B L := on_line_of_between hGHB hG_L hH_L
    -- Let it so fall, as BGHD.
    have hBGD : Between B G D :=
      between_of_inside_chord hG_L hB_L hD_L (centre_inside hG) hBα ht.1 hBD
    have hBGH : Between B G H := between_cut hBGD hGHD
    -- Then, since the point G is the centre of the circle ABCD,
    -- BG is equal to GD;
    have hBG_GD : ‖B G‖ = ‖G D‖ := (len_symm B G).trans (Definition15 hG hBα ht.1)
    -- therefore BG is greater than HD;
    have hHD_BG : ‖H D‖ < ‖B G‖ := by
      rw [hBG_GD, len_symm H D, len_symm G D]
      exact len_lt_of_between (between_symm hGHD)
    -- therefore BH is much greater than HD.
    have hHD_BH : ‖H D‖ < ‖B H‖ := lt_trans hHD_BG (len_lt_of_between hBGH)
    -- Again, since the point H is the centre of the circle EBFD,
    -- BH is equal to HD;
    have hBH_HD : ‖B H‖ = ‖H D‖ := (len_symm B H).trans (Definition15 hH hBβ ht.2.1)
    -- but it was also proved much greater than it: which is impossible.
    rw [hBH_HD] at hHD_BH
    exact lt_irrefl _ hHD_BH
  -- Therefore a circle does not touch a circle internally at more points than one.
  have hinternal : (TouchesInternally ABDC EBFD D ∨ TouchesInternally EBFD ABDC D) →
      OnCircle B ABDC → OnCircle B EBFD → B = D := by
    intro h hB₁ hB₂
    /- The same argument serves with the circles' names exchanged. -/
    rcases h with h | h
    · exact within h hB₁ hB₂
    · exact within h hB₂ hB₁
  -- I say further that neither does it so touch it externally.
  have hexternal : TouchesExternally ACK ABDC A → OnCircle C ACK → OnCircle C ABDC →
      C = A := by
    intro h hC₁ hC₂
    -- For, if possible, let the circle ACK touch the circle ABDC at more points than one, namely
    -- A, C,
    obtain ⟨hA₁, hA₂, hout⟩ := h
    refine Classical.byContradiction fun hCA => ?_
    -- and let AC be joined.
    obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C (Ne.symm hCA)
    obtain ⟨P, -, hAPC, -⟩ := exists_point_between hA_AC hC_AC (Ne.symm hCA) []
    -- Then, since on the circumference of each of the circles ABDC, ACK two points A, C have
    -- been taken at random, the straight line joining the points will fall within each
    -- circle; [III. 2]
    have hP₂ : InsideCircle P ABDC := Prop2 hA₂ hC₂ P hAPC
    have hP₁ : InsideCircle P ACK := Prop2 hA₁ hC₁ P hAPC
    -- but it fell within the circle ABCD and outside ACK [III. Def. 3]: which is absurd.
    exact hout P hP₁ hP₂
  -- Therefore a circle does not touch a circle externally at more points than one.
  -- And it was proved that neither does it so touch it internally.
  -- Therefore etc.
  -- Q. E. D.
  exact ⟨hinternal, hexternal⟩

/-- **III.13 for circles touching within**, with only the two circles it speaks of: circles
touching within, either inside the other, have no common point but the point of contact.
A lemma beside III.13, its first clause alone; it rests on whatever III.13 rests on.
Without it, a citer of that clause names III.13's third circle, which the clause never
mentions. -/
theorem Prop13.internally {B D : Point} {α β : Circle}
    (h : TouchesInternally α β D ∨ TouchesInternally β α D) (hBα : OnCircle B α)
    (hBβ : OnCircle B β) : B = D :=
  (Prop13 (A := D) (C := D) (ACK := α)).1 h hBα hBβ

/-- **III.13 for circles touching without**, with only the two circles it speaks of: they
have no common point but the point of contact. A lemma beside III.13, its second clause
alone; it rests on whatever III.13 rests on. -/
theorem Prop13.externally {A C : Point} {α β : Circle} (h : TouchesExternally α β A)
    (hCα : OnCircle C α) (hCβ : OnCircle C β) : C = A :=
  (Prop13 (B := A) (D := A) (EBFD := β)).2 h hCα hCβ

end Elements.BookIII
