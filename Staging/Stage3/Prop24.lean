import Elements.Figure.Basics
import Elements.BookI.Prop08
import Staging.Stage3.Definitions
import Staging.Stage3.Chord
import Staging.Stage3.Placement
import Staging.Stage3.Prop23Point

/-!
# Stage 3, staged: III.24 restated

Statements before proofs (brief 0006, stage 3), and the spike's real test: III.24 restated to
conclude that the segments are congruent, proved here by Euclid's route from the stubbed
`placement` and `Prop23.point`.

When frozen, this statement replaces `Elements.BookIII.Prop24` in
`Elements/BookIII/Prop24.lean`, and today's proof by the radii stays beside it as the labelled
alternative (`Prop24.equalCircles`). Here it is `Elements.BookIII.Staging.Prop24`, so as not
to collide with the theorem it will replace; the `Staging` namespace is dropped when it moves.

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
  /- It remains to see where the points off the base fall. A point P on E's side goes to a
     point on F's side, and the triangles APB, C(fP)D have their three sides equal, so the
     angle at P is the angle at its image [I. 8]. -/
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
  /- Euclid's reductio is carried by the angles, point by point. On F's side of CD a point is
     on the circle CFD exactly when the angle it subtends on CD is the angle at F, and within
     it exactly when that angle is greater; on E's side of AB, alike for AEB (`Prop23.point`).
     The angle at each point is the angle at its image, and the angles at E and F are equal,
     the segments being similar; so no point of the arc AEB falls within CFD or outside it,
     and the points within AEB fall within CFD, and back again. -/
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
  /- Nothing is left for III.10: the angles have settled every point of the arc, so the arc
     cannot fall awry. -/
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
     arc, keeping every distance: the segments coincide, and are equal [C.N. 4]. -/
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

end Elements.BookIII.Staging
