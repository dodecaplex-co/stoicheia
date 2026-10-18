import Elements.Figure.Basics
import Elements.BookI.Prop08
import Elements.BookIII.Circumferences
import Elements.BookIII.Prop24
import Staging.Stage3.Definitions
import Staging.Stage3.Chord
import Staging.Stage3.Placement
import Staging.Stage3.Prop23Point

/-!
# Stage 3, staged: III.24 restated

Statements before proofs (brief 0006, stage 3), and the spike's real test: III.24 restated to
conclude that the segments are congruent (`Arc.Congruent`), proved here from the stubbed
`placement` and `Prop23.point`. The proof keeps Euclid's application of one segment to the
other (`placement`: A on C, AB on CD, B on D), with the coincidence of the arcs argued by the
angles (`Prop23.point`, III.23's companion) in place of his reductio. Euclid refutes a segment
falling within the other, or outside it, by a tacit reference to III.23, as Heath notes
(vol. 2, p. 54), and one falling awry by III.10; the Lean settles every point of the arc
directly, and needs neither the reductio nor III.10. So the route is `modified`: the passage
"it will either fall within it, or outside it" and the sentence citing III.10 are argued
another way.

"Equal", in the enunciation and the last sentence, is read through Common Notion 4: the
segments coincide. No magnitude of a segment is defined (brief 0006).

When frozen, this statement replaces `Elements.BookIII.Prop24` in
`Elements/BookIII/Prop24.lean`. Today's statement and its proof by the radii stay beside it as
the labelled alternative (`Prop24.equalCircles`), and `Prop24.equalMeasure` gives the equal
measures that III.26 takes from III.24. Here it is `Elements.BookIII.Staging.Prop24`, so as
not to collide with the theorem it will replace; the `Staging` namespace is dropped when it
moves.

Euclid's text, in Heath's translation: [`heath/III/24.md`](../../heath/III/24.md). Below,
each of Euclid's sentences is a `--` comment, followed by the Lean that carries it out.
-/

namespace Elements.BookIII.Staging

open Tacit

/-- Similar segments of circles on equal straight lines are equal to one another. -/
theorem Prop24 {A B C D E F : Point} {AEB CFD : Circle} (hAEB : ∃ O : Point, Centre O AEB)
    (hCFD : ∃ O : Point, Centre O CFD) (hA : OnCircle A AEB) (hB : OnCircle B AEB)
    (hE : OnCircle E AEB) (hC : OnCircle C CFD) (hD : OnCircle D CFD)
    (hF : OnCircle F CFD) (hE_AB : ¬ Collinear A B E) (hF_CD : ¬ Collinear C D F)
    (hAB : ‖A B‖ = ‖C D‖) (hsim : ∠ A E B = ∠ C F D) :
    Arc.Congruent ⟨AEB, A, B, E⟩ ⟨CFD, C, D, F⟩ := by
  -- For let AEB, CFD be similar segments of circles on equal straight lines AB, CD;
  have hA_B : A ≠ B := (show Triangle A B E from hE_AB).ne₁₂
  have hC_D : C ≠ D := (show Triangle C D F from hF_CD).ne₁₂
  -- I say that the segment AEB is equal to the segment CFD.
  -- For, if the segment AEB be applied to CFD, and if the point A be placed on C and the
  -- straight line AB on CD,
  /- The application is `placement`: E's side of AB, with AB itself, is carried onto F's side
     of CD, with CD, keeping every distance, and A goes to C. -/
  obtain ⟨f, hAC, hBD, ⟨hinto, honto, hdist⟩, hf⟩ := placement hE_AB hF_CD hAB
  -- the point B will also coincide with the point D, because AB is equal to CD;
  /- `hBD`: the placement on the equal straight lines AB, CD puts B on D. -/
  -- and, AB coinciding with CD,
  /- The points of AB go to points of CD: a point of the base is an end, or between the ends,
     exactly when its image is. -/
  have hbase : ∀ P : Point, OnSideOrLine P E A B → Collinear A B P →
      Collinear C D (f P) ∧ (P = A ∨ P = B ↔ f P = C ∨ f P = D) ∧
        (Between A P B ↔ Between C (f P) D) := by
    intro P hP hPl
    obtain ⟨h₁, h₂, hside, hbet⟩ := hf P hP
    have hcol : Collinear C D (f P) := by
      rcases hinto P hP with h | h
      · exact absurd hPl (hside.mpr h).triangle
      · exact h
    refine ⟨hcol, ⟨?_, ?_⟩, hbet⟩
    · rintro (h | h)
      · left; rw [h]; exact hAC
      · right; rw [h]; exact hBD
    · rintro (h | h)
      · left; rw [h, len_self] at h₁; exact (eq_of_len_eq_zero h₁.symm).symm
      · right; rw [h, len_self] at h₂; exact (eq_of_len_eq_zero h₂.symm).symm
  -- the segment AEB will also coincide with CFD.
  /- The claim is shown by the sentences that follow; the Lean begins that argument here,
     with where the points off the base fall. A point P on E's side goes to a point on F's
     side, and the triangles APB, C(fP)D have their three sides equal, so the angle at P is
     the angle at its image [I. 8]. -/
  have hang : ∀ P : Point, SameSideOf P E A B →
      SameSideOf (f P) F C D ∧ ∠ A P B = ∠ C (f P) D := by
    intro P hPE
    obtain ⟨h₁, h₂, hside, -⟩ := hf P (Or.inl hPE)
    have hQF : SameSideOf (f P) F C D := hside.mp hPE
    exact ⟨hQF, BookI.Prop8 hPE.triangle.cab hQF.triangle.cab
      (by rw [len_symm P A, ← h₁, len_symm C (f P)])
      (by rw [len_symm P B, ← h₂, len_symm D (f P)]) hAB⟩
  -- For, if the straight line AB coincide with CD but the segment AEB do not coincide with
  -- CFD,
  -- it will either fall within it, or outside it;
  /- In place of Euclid's reductio, the Lean argues directly, point by point, by the angles.
     Euclid leaves these two cases to a tacit reference to III.23 (Heath, vol. 2, p. 54);
     here III.23's companion `Prop23.point` does that work. On F's side of CD a point is on
     the circle CFD exactly when the angle it subtends on CD is the angle at F, and within it
     exactly when that angle is greater; on E's side of AB, alike for AEB. The angle at each
     point is the angle at its image, and the angles at E and F are equal, the segments being
     similar; so no point of the arc AEB falls within CFD or outside it, and the points within
     AEB fall within CFD, and back again. -/
  have hoff : ∀ P : Point, SameSideOf P E A B →
      (OnCircle P AEB ↔ OnCircle (f P) CFD) ∧ (InsideCircle P AEB ↔ InsideCircle (f P) CFD) := by
    intro P hPE
    obtain ⟨hQF, hPQ⟩ := hang P hPE
    obtain ⟨on₁, in₁⟩ := Prop23.point hAEB hA hB hE hPE
    obtain ⟨on₂, in₂⟩ := Prop23.point hCFD hC hD hF hQF
    rw [on₁, on₂, in₁, in₂, hPQ, hsim]
    exact ⟨Iff.rfl, Iff.rfl⟩
  -- or it will fall awry, as CGD, and a circle cuts a circle at more points than two: which is
  -- impossible. [III. 10]
  /- III.10 is not needed: the angles have settled every point of the arc, so the arc cannot
     fall awry, and no third case is left to refute. -/
  -- Therefore, if the straight line AB be applied to CD, the segment AEB will not fail to
  -- coincide with CFD also;
  /- So every point of the half-plane is on the circle AEB, or within it, exactly when its
     image is on the circle CFD, or within it: off the base by the angles, on the base by its
     ends and their order (`chord_cases`). -/
  have hcirc : ∀ P : Point, OnSideOrLine P E A B →
      (OnCircle P AEB ↔ OnCircle (f P) CFD) ∧ (InsideCircle P AEB ↔ InsideCircle (f P) CFD) := by
    intro P hP
    rcases hP with hPE | hPl
    · exact hoff P hPE
    · obtain ⟨hQl, hends, hbet⟩ := hbase P (Or.inr hPl) hPl
      obtain ⟨on₁, in₁⟩ := chord_cases hA hB hA_B hPl
      obtain ⟨on₂, in₂⟩ := chord_cases hC hD hC_D hQl
      rw [on₁, on₂, in₁, in₂]
      exact ⟨hends, hbet⟩
  -- therefore it will coincide with it and will be equal to it.
  /- One map puts A on C and B on D, the segment AEB on the segment CFD and the arc on the
     arc, keeping every distance between their points: the segments coincide, and are equal
     [C.N. 4]. -/
  refine ⟨f, hAC, hBD, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rintro P ⟨hio, hP⟩
    refine ⟨?_, hinto P hP⟩
    rcases hio with h | h
    · exact Or.inl ((hcirc P hP).2.mp h)
    · exact Or.inr ((hcirc P hP).1.mp h)
  · rintro Q ⟨hio, hQ⟩
    obtain ⟨P, hP, rfl⟩ := honto Q hQ
    refine ⟨P, ⟨?_, hP⟩, rfl⟩
    rcases hio with h | h
    · exact Or.inl ((hcirc P hP).2.mpr h)
    · exact Or.inr ((hcirc P hP).1.mpr h)
  · intro P Q hP hQ
    exact hdist P Q hP.2 hQ.2
  · rintro P ⟨hon, hP⟩
    exact ⟨(hcirc P hP).1.mp hon, hinto P hP⟩
  · rintro Q ⟨hon, hQ⟩
    obtain ⟨P, hP, rfl⟩ := honto Q hQ
    exact ⟨P, ⟨(hcirc P hP).1.mpr hon, hP⟩, rfl⟩
  · intro P Q hP hQ
    exact hdist P Q hP.2 hQ.2
  -- Therefore etc.
  -- Q. E. D.

/-- **III.24, the circles and the measures** (companion of III.24, "III.24 equalCircles").
Today's statement of III.24: similar segments on equal straight lines lie in equal circles,
and their circumferences are equal in measure. It keeps today's proof by the radii (the
angles at the centres, III.20 and III.22, and isosceles triangles on the equal bases,
`Prop24.isosceles`), shown on the page as the labelled alternative proof, with Euclid's text
in full under the main one. `Arc.congruent_iff` cites it for the equal circles. -/
theorem Prop24.equalCircles {A B C D E F : Point} {AEB CFD : Circle}
    (hAEB : ∃ O : Point, Centre O AEB) (hCFD : ∃ O : Point, Centre O CFD)
    (hA : OnCircle A AEB) (hB : OnCircle B AEB) (hE : OnCircle E AEB) (hC : OnCircle C CFD)
    (hD : OnCircle D CFD) (hF : OnCircle F CFD) (hE_AB : ¬ Collinear A B E)
    (hF_CD : ¬ Collinear C D F) (hAB : ‖A B‖ = ‖C D‖) (hsim : ∠ A E B = ∠ C F D) :
    EqualCircles AEB CFD ∧ circumference AEB A E B = circumference CFD C F D := by
  sorry

/-- The check: `Prop24.equalCircles` has today's statement of III.24 (checked by Lean, up to
unfolding definitions). -/
example : type_of% @Elements.BookIII.Prop24 := @Prop24.equalCircles

/-- **Congruent segments have equal circumferences** (companion of III.24, "III.24
equalMeasure"). If two drawn segments are congruent, their circumferences are equal in
measure. III.26 cites it after III.24, where Euclid passes from the equal segments to the
equal circumferences [III. 24]; nothing before III.26 says it otherwise, for `Arc.congruent_iff`
comes after III.29.

To be proved: take a point P of the first arc off its base [`exists_onCircle_sameSideOf`]; its
image is a point of the second arc, off its base (it is neither end, being as far from each
as P is, and `chord_cases`); the congruence keeps the distances from P to the ends, so the
angle at P is the angle at its image [I. 8]; the circumference on the other side of each base
is twice that angle (`Circumference.eq`), and with it each circumference makes up the whole
circle (`Circumference.whole`); so the circumferences are equal [C.N. 3]. -/
theorem Prop24.equalMeasure {a b : Arc} (ha : a.Drawn) (hb : b.Drawn)
    (h : Arc.Congruent a b) : a.measure = b.measure := by
  sorry

end Elements.BookIII.Staging
