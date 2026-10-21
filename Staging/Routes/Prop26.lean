import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop04
import Elements.BookIII.Prop22
import Elements.BookIII.Prop24
import Staging.Routes.Prop20

/-!
# Book III, Proposition 26, by Euclid's proof for angles of every size

This file answers issue #129 for III.26. Heath: "As in III. 21, if Euclid's proof is to
cover all cases, it requires us to take cognisance of 'angles at the centre' which are
equal to or greater than two right angles. Otherwise we must deal separately with the
cases where the angle at the circumference is equal to or greater than a right angle"
(vol. 2, p. 57). The proof in `Elements/BookIII/Prop26.lean` deals with them separately:
it sorts the angles at A and D as acute, right or obtuse (`Prop24.angle_type`), and takes
Euclid's argument for the acute, the diameters for the right, and III.22 for the obtuse,
passing to the acute angles in the other segments.

Here the angles at the centres are `angleAtCentre`, staged with III.20 in
`Staging/Routes/Prop20.lean`, and may be two right angles or more, so Euclid's one
argument covers every case. Equal angles at the circumferences give equal angles at the
centres, their doubles (the general III.20); the bases are equal by I.4; the segments
are similar and on equal straight lines, so equal [III. 24]; and the circumferences that
remain are equal. The sorting of the angles, and the passage to the other segment by
III.22 for the bases, drop out. One division into cases stays, at I.4, labelled where it
stands: where the angles at the centres are two right angles, BC and EF are diameters, and
there are no triangles for I.4; where they are greater, I.4 applies to the angles BGC, EHF
that remain of four right angles. The whole circle is four right angles
(`Circumference.whole`), as before. Each clause also concludes that the circumferences
BKC, ELF are congruent (`Arc.Congruent`); as in `Elements/BookIII/Prop26.lean`, that
cannot come by subtraction, and comes from III.24 applied to the remaining segments, whose
angles make two right angles with the equal angles at A and D [III. 22], and so are equal.
The statement is that of `Elements.BookIII.Prop26`, exactly.

Status: staged to replace the proof in `Elements/BookIII/Prop26.lean` when Book III's
files are next moved, once the draft it stands on, `angleAtCentre` and the general
statement of `Routes.Prop20`, has the owner's approval; that draft is not approved.
-/

namespace Elements.BookIII.Routes

open Tacit

/-- **Equal angles at the centres lie alike.** If the angle at the centre G standing on
the circumference BKC is equal to the angle at the centre H standing on ELF, then G and H
lie alike: both on the other sides of BC and EF from K and L, both on BC and EF, or both
on K's and L's sides. For an angle at the centre is less than two right angles, two right
angles, or greater, as its centre lies (`angleAtCentre.size`). Euclid's figure draws the
first; this is the step that tells us which case we are in: I.4 on the angles at the
centres, no triangles at all, or I.4 on what remains of four right angles. -/
theorem Prop26.alike {B C E F G H K L : Point} {α β : Circle} (hG : Centre G α)
    (hB : OnCircle B α) (hC : OnCircle C α) (hK : Triangle B C K) (hH : Centre H β)
    (hE : OnCircle E β) (hF : OnCircle F β) (hL : Triangle E F L)
    (h : angleAtCentre α B K C = angleAtCentre β E L F) :
    (OppositeSidesOf G K B C ∧ OppositeSidesOf H L E F) ∨ (Between B G C ∧ Between E H F) ∨
      (SameSideOf G K B C ∧ SameSideOf H L E F) := by
  rcases angleAtCentre.size hG hB hC hK with ⟨hG', h₁⟩ | ⟨hG', h₁⟩ | ⟨hG', h₁⟩ <;>
    rcases angleAtCentre.size hH hE hF hL with ⟨hH', h₂⟩ | ⟨hH', h₂⟩ | ⟨hH', h₂⟩
  · exact Or.inl ⟨hG', hH'⟩
  · rw [h, h₂] at h₁; exact absurd h₁ (lt_irrefl _)
  · rw [h] at h₁; exact absurd (lt_trans h₁ h₂) (lt_irrefl _)
  · rw [← h, h₁] at h₂; exact absurd h₂ (lt_irrefl _)
  · exact Or.inr (Or.inl ⟨hG', hH'⟩)
  · rw [← h, h₁] at h₂; exact absurd h₂ (lt_irrefl _)
  · rw [h] at h₁; exact absurd (lt_trans h₁ h₂) (lt_irrefl _)
  · rw [h, h₂] at h₁; exact absurd h₁ (lt_irrefl _)
  · exact Or.inr (Or.inr ⟨hG', hH'⟩)

/-- In equal circles equal angles stand on equal circumferences, whether they stand at the centres
or at the circumferences. -/
theorem Prop26 {A B C D E F G H K L : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hF : OnCircle F DEF) (hAK : OppositeSidesOf A K B C) (hDL : OppositeSidesOf D L E F) :
    (OppositeSidesOf G K B C → OppositeSidesOf H L E F → ∠ B G C = ∠ E H F →
      circumference ABC B K C = circumference DEF E L F ∧
        Arc.Congruent ⟨ABC, B, C, K⟩ ⟨DEF, E, F, L⟩) ∧
    (∠ B A C = ∠ E D F →
      circumference ABC B K C = circumference DEF E L F ∧
        Arc.Congruent ⟨ABC, B, C, K⟩ ⟨DEF, E, F, L⟩) := by
  -- Let ABC, DEF be equal circles, and in them let there be equal angles, namely at the
  -- centres the angles BGC, EHF, and at the circumferences the angles BAC, EDF;
  -- I say that the circumference BKC is equal to the circumference ELF.
  /- As Euclid sets it out, we take both pairs of equal angles together. "The angles BGC,
     EHF" at the centres are the angles at the centres standing on the circumferences BKC
     and ELF (`angleAtCentre`), of any size: if Euclid's proof is to cover all cases, Heath
     says, "it requires us to take cognisance of 'angles at the centre' which are equal to
     or greater than two right angles" (vol. 2, p. 57). Our statement gives one pair at a
     time, and the other comes from III.20 at the end, under "Therefore etc." -/
  have euclid : angleAtCentre ABC B K C = angleAtCentre DEF E L F → ∠ B A C = ∠ E D F →
      circumference ABC B K C = circumference DEF E L F ∧
        Arc.Congruent ⟨ABC, B, C, K⟩ ⟨DEF, E, F, L⟩ := by
    intro hGH hAD
    -- For let BC, EF be joined.
    have hBCA : Triangle B C A := hAK.triangle
    have hEFD : Triangle E F D := hDL.triangle
    -- Now, since the circles ABC, DEF are equal,
    -- the radii are equal.
    have hGB : ‖G B‖ = ‖H E‖ := hcircles.radii hG hH hB hE
    have hGC : ‖G C‖ = ‖H F‖ := hcircles.radii hG hH hC hF
    -- Thus the two straight lines BG, GC are equal to the two straight lines EH, HF;
    -- and the angle at G is equal to the angle at H;
    /- "Thus …" gathers the radii just found, which I.4 uses below. The angles at G and
       H, being equal, are alike: both less than two right angles, both two right angles,
       or both greater, and so G and H lie alike (`Prop26.alike`). Euclid's figure has the
       first. -/
    have halike := Prop26.alike hG hB hC hAK.symm.triangle hH hE hF hDL.symm.triangle hGH
    -- therefore the base BC is equal to the base EF. [I. 4]
    have hBC : ‖B C‖ = ‖E F‖ := by
      rcases halike with ⟨hGK, hHL⟩ | ⟨hBGC, hEHF⟩ | ⟨hGK, hHL⟩
      · /- Euclid's figure: the angles at the centres are the angles BGC, EHF of the
           triangles GBC, HEF (`angleAtCentre.within`), and I.4 gives the bases. -/
        have hang : ∠ B G C = ∠ E H F := by
          rw [← angleAtCentre.within hG hB hC hGK, ← angleAtCentre.within hH hE hF hHL]
          exact hGH
        exact (BookI.Prop4 hGK.triangle.cab hHL.triangle.cab hGB hGC hang).1
      · /- A case Euclid's figure leaves aside: the angles at the centres are two right
           angles, G is on BC and H on EF, and there are no triangles for I.4. BC and EF
           are diameters, each two radii, and so equal. -/
        rw [← len_add_of_between hBGC, ← len_add_of_between hEHF, len_symm B G, hGB, hGC,
          len_symm E H]
      · /- A case Euclid's figure leaves aside: the angles at the centres are greater than
           two right angles, and G and H lie beyond BC and EF. The angles BGC, EHF of the
           triangles GBC, HEF are what remains when the angles at the centres are taken
           from four right angles (`angleAtCentre.reflex`), and so are equal [C.N. 3];
           I.4 applies to them. -/
        have hang : ∠ B G C = ∠ E H F :=
          CommonNotion3
            (by rw [add_comm (∠ B G C), angleAtCentre.reflex hG hB hC hGK,
              add_comm (∠ E H F), angleAtCentre.reflex hH hE hF hHL]) hGH
        exact (BookI.Prop4 hGK.triangle.cab hHL.triangle.cab hGB hGC hang).1
    -- And, since the angle at A is equal to the angle at D,
    -- the segment BAC is similar to the segment EDF; [III. Def. 11]
    -- and they are upon equal straight lines.
    -- But similar segments of circles on equal straight lines are equal to one
    -- another; [III. 24]
    -- therefore the segment BAC is equal to EDF.
    have seg : Arc.Congruent ⟨ABC, B, C, A⟩ ⟨DEF, E, F, D⟩ :=
      Prop24 hB hC hA hE hF hD hBCA hEFD hBC hAD
    /- So their circumferences are equal in measure (`Prop24.equalMeasure`). -/
    have hBAC : circumference ABC B A C = circumference DEF E D F :=
      Prop24.equalMeasure (a := ⟨ABC, B, C, A⟩) (b := ⟨DEF, E, F, D⟩)
        ⟨hB, hC, hBCA⟩
        ⟨hE, hF, hEFD⟩ seg
    -- But the whole circle ABC is also equal to the whole circle DEF;
    have w₁ := Circumference.whole hB hC hAK
    have w₂ := Circumference.whole hE hF hDL
    -- therefore the circumference BKC which remains is equal to the circumference ELF.
    have hKL : circumference ABC B K C = circumference DEF E L F :=
      CommonNotion3 (w₁.trans w₂.symm) hBAC
    /- Their congruence cannot come by subtraction, and comes from III.24 itself. At points
       X, Y of the circles on the sides of K and L, the angles make two right angles with
       the equal angles at A and D [III. 22], so they are equal, and the remaining segments
       are similar; on the equal bases BC, EF they are congruent [III. 24]. Only the side
       names a segment, so they are the segments on the sides of K and L
       (`Arc.Congruent.congr_side`). -/
    obtain ⟨X, hX, hXK⟩ := Prop2.sameSide hB hC hAK.symm.triangle
    obtain ⟨Y, hY, hYL⟩ := Prop2.sameSide hE hF hDL.symm.triangle
    have hXA : OppositeSidesOf X A B C := hXK.trans_opposite hAK.symm
    have hYD : OppositeSidesOf Y D E F := hYL.trans_opposite hDL.symm
    have hAX : ∠ B A C + ∠ B X C = ∟ + ∟ := by
      have hAX := (Prop22 hA hB hX hC hXA.symm).2
      rwa [angle_symm hXA.triangle.ne₂₃ hXA.triangle.ne₁₃] at hAX
    have hDY : ∠ E D F + ∠ E Y F = ∟ + ∟ := by
      have hDY := (Prop22 hD hE hY hF hYD.symm).2
      rwa [angle_symm hYD.triangle.ne₂₃ hYD.triangle.ne₁₃] at hDY
    have hXY : ∠ B X C = ∠ E Y F :=
      CommonNotion3 (c := ∠ B A C) (d := ∠ E D F)
        (by rw [add_comm (∠ B X C), hAX, add_comm (∠ E Y F), hDY]) hAD
    have hBXC := Prop24 hB hC hX hE hF hY
      hXK.triangle hYL.triangle hBC hXY
    exact ⟨hKL, hBXC.congr_side hXK hYL⟩
  -- Therefore etc.
  /- Our statement takes the two pairs of equal angles one at a time, as the enunciation's
     "whether they stand at the centres or at the circumferences" does, and III.20 gives
     the other pair: each angle at the centre is double of the angle at the circumference
     standing on the same circumference, whatever its size. Given at the centres, the
     circumferences BKC, ELF are less than semicircles, and the angles at the centres are
     the angles BGC, EHF themselves (`angleAtCentre.within`); the angles at A and D are
     their halves, and so equal. Given at the circumferences, the angles at the centres
     are their doubles, and so equal. -/
  have h₁ : angleAtCentre ABC B K C = ∠ B A C + ∠ B A C := Prop20 hA hB hC hAK
  have h₂ : angleAtCentre DEF E L F = ∠ E D F + ∠ E D F := Prop20 hD hE hF hDL
  refine ⟨fun hGK hHL h => ?_, fun h => euclid (by rw [h₁, h₂, h]) h⟩
  have hGH : angleAtCentre ABC B K C = angleAtCentre DEF E L F := by
    rw [angleAtCentre.within hG hB hC hGK, angleAtCentre.within hH hE hF hHL, h]
  exact euclid hGH (Magnitude.eq_of_add_self_eq (h₁.symm.trans (hGH.trans h₂)))
  -- Q. E. D.

end Elements.BookIII.Routes
