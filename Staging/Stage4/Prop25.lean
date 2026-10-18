import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop04
import Elements.BookI.Prop06
import Elements.BookI.Prop10
import Elements.BookI.Prop11
import Elements.BookI.Prop17
import Elements.BookI.Prop23
import Elements.BookI.Prop24
import Elements.BookIII.Prop10
import Elements.BookIII.Prop25
import Elements.Foundations.DefinitionsIII
import Elements.Figure.Chords

/-!
# Stage 4, staged: III.25 restated

Statements before proofs (brief 0006, stage 4). It uses stage 3's arcs (`Arc`, `OnArc`,
`Arc.meets`).

Today III.25 is handed the circle whose segment it completes. Restated, its construction core
receives the segment only as a predicate `S` on points, with the meeting fact Euclid reads off
it (a straight line drawn from within the base into the segment meets its circumference), and
never sees a circle or a centre. It returns B, D, E and the circle γ described with centre E
(Postulate 3) through A, B and C. III.9 moves out: `Prop25.complete`, a separate theorem,
shows that for the arc of a circle α, γ is α, and every point of the arc is on γ.

**The statement is the pair.** The core's conclusion does not say that γ is the circle the
segment came from: S need not lie on any circle, and nothing in the conclusion puts S on γ.
Heath's "the complete circle of which it is a segment" is carried by `Prop25.complete`, for S
the arc of a given circle α. So the statement brief 0006 freezes for III.25 is the core
together with `Prop25.complete`: the record lists the companions, its scope describes the
main theorem together with them, and its note and the page say which declaration carries
which clause.

When frozen, the core replaces `Elements.BookIII.Prop25`; here it is
`Elements.BookIII.Staging.Prop25`. `Staging.Prop25.of_circle` checks the interfaces: from the
core, `Arc.meets` and `Prop25.complete`, today's statement follows. It stays, as the companion
"III.25 of_circle", so that today's statement keeps its certificate.
-/

namespace Elements.BookIII

open Tacit

/-- **III.25's circle is the segment's circle.** Let A, C be points of a circle α with a
centre, and B a point of its arc on P's side of AC (B on P's side). Any circle γ, with a
centre, through A, B and C is α, and every point of the arc AC on P's side is on γ.

To be proved: α and γ meet at the three points A, B, C, so they are one circle [III. 10] (or
E is the centre of α [III. 9], and `circle_eq`).

A companion of III.25 ("III.25 complete"): its correctness argument, kept apart from the
construction core. It carries Heath's "of which it is a segment". -/
theorem Prop25.complete {A C P B E : Point} {α γ : Circle} (hα : ∃ O : Point, Centre O α)
    (hA : OnCircle A α) (hC : OnCircle C α) (hB : OnArc B ⟨α, A, C, P⟩)
    (hBP : SameSideOf B P A C) (hE : Centre E γ) (hAγ : OnCircle A γ) (hBγ : OnCircle B γ)
    (hCγ : OnCircle C γ) :
    γ = α ∧ ∀ X : Point, OnArc X ⟨α, A, C, P⟩ → OnCircle X γ := by
  sorry

end Elements.BookIII

namespace Elements.BookIII.Staging

open Tacit

/-- Given a segment of a circle, to describe the complete circle of which it is a segment. -/
theorem Prop25 {A C P : Point} {S : Point → Prop} (hP : ¬ Collinear A C P)
    (hmeet : ∀ X Y : Point, Between A X C → SameSideOf Y P A C →
      ∃ B : Point, S B ∧ OnRay B X Y) :
    ∃ (B D E : Point) (γ : Circle), S B ∧ SameSideOf B P A C ∧ Between A D C ∧
      ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E γ ∧ OnCircle A γ ∧ OnCircle B γ ∧
      OnCircle C γ ∧ Collinear D B E ∧
      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧
      (∠ A B D < ∠ B A D → SameSideOf E B A C) := by
  sorry

/-- **Today's III.25, from the restated core.** Handed the circle ABC, the core run on the
points of its arc on P's side (which meet every straight line from within the base, by
`Arc.meets`) finds a circle that is ABC itself (`Prop25.complete`), so its centre E is the
centre of ABC. This is the statement III.25 has today (the `example` below checks it), and
it checks that the pieces fit. A companion of III.25 ("III.25 of_circle"), proved from the
core, `Arc.meets` and `Prop25.complete`. -/
theorem Prop25.of_circle {A C : Point} {ABC : Circle} (hABC : ∃ E : Point, Centre E ABC)
    (hA : OnCircle A ABC) (hC : OnCircle C ABC) :
    ∀ P : Point, ¬ Collinear A C P → ∃ B D E : Point, OnCircle B ABC ∧ SameSideOf B P A C ∧
      Between A D C ∧ ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E ABC ∧ Collinear D B E ∧
      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧
      (∠ A B D < ∠ B A D → SameSideOf E B A C) := by
  intro P hP
  have ha : Arc.Drawn ⟨ABC, A, C, P⟩ := ⟨hABC, hA, hC, hP⟩
  obtain ⟨B, D, E, γ, hSB, hBP, hADC, hAD, hADB, hE, hAγ, hBγ, hCγ, hDBE, k₁, k₂, k₃⟩ :=
    Prop25 (S := (OnArc · ⟨ABC, A, C, P⟩)) hP (fun _ _ hX hY => Arc.meets ha hX hY)
  obtain ⟨hγ, -⟩ := BookIII.Prop25.complete hABC hA hC hSB hBP hE hAγ hBγ hCγ
  rw [hγ] at hE
  exact ⟨B, D, E, hSB.1, hBP, hADC, hAD, hADB, hE, hDBE, k₁, k₂, k₃⟩

/-- The check: `Prop25.of_circle` has today's statement of III.25 (checked by Lean, up to
unfolding definitions). -/
example : type_of% @Elements.BookIII.Prop25 := @Prop25.of_circle

end Elements.BookIII.Staging
