import Elements.BookIII.Circumferences
import Elements.BookIII.Prop23
import Elements.BookIII.Prop24
import Elements.BookIII.Prop25
import Staging.Centre.Restated

/-!
# Staging: brief 0006's statements without `∃ O, Centre O α`

Brief 0008. Six statements that brief 0006 froze, four moved to `Elements/` with stage 3
and two with stage 4, ask that a circle have some centre, and its definition
of a drawn arc asks it too. The rule `exists_centre` is now present in `Elements`, so each
variant below loses that hypothesis; nothing else in it changes. This is a revision of
brief 0006, approved by the coordinator with brief 0008, at its freeze. All six original
statements now live in `Elements.BookIII`; their centre-removal variants remain staged here.

As in `Restated.lean`, each statement carries `sorry` and two checks (checked by Lean): given
the rule's content, taken as a hypothesis, brief 0006's statement gives the new one; and the
new one gives brief 0006's. Two more checks show that brief 0006's pattern survives: the
companions `Prop24.equalCircles` and `Prop25.of_circle` still have the statements of III.24
before stage 3 and of III.25 before stage 4, restated as `Restated.lean` restates them. The names
of the centre-removal variants sit in `Elements.BookIII.Staging.Centre.Stage3` and `.Stage4`.
-/

namespace Elements.BookIII.Staging.Centre.Stage3

open Tacit

/-- **Circumferences add** (brief 0006, ground for Book IV). Let B, C, D be points of a
circle, and C on K's side of BD. The circumference BC away from D and the circumference CD
away from B make up the circumference BKD. -/
theorem Circumference.add {B C D K X Y : Point} {α : Circle} (hB : OnCircle B α)
    (hC : OnCircle C α) (hD : OnCircle D α) (hCK : SameSideOf C K B D)
    (hX : OppositeSidesOf X D B C) (hY : OppositeSidesOf Y B C D) :
    circumference α B X C + circumference α C Y D = circumference α B K D := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) :
    type_of% @Stage3.Circumference.add :=
  Elements.BookIII.Circumference.add (exists_centre _)
example : type_of% @Elements.BookIII.Circumference.add := fun _ => Stage3.Circumference.add

/-- **III.23, point by point** (companion of III.23, "III.23 point"). Let A, B, E be points
of a circle, and P on E's side of AB. P is on the circle exactly when the angle APB is equal
to the angle AEB, and within it exactly when APB is the greater. -/
theorem Prop23.point {A B E P : Point} {α : Circle} (hA : OnCircle A α) (hB : OnCircle B α)
    (hE : OnCircle E α) (hPE : SameSideOf P E A B) :
    (OnCircle P α ↔ ∠ A P B = ∠ A E B) ∧ (InsideCircle P α ↔ ∠ A E B < ∠ A P B) := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) :
    type_of% @Stage3.Prop23.point :=
  Elements.BookIII.Prop23.point (exists_centre _)
example : type_of% @Elements.BookIII.Prop23.point := fun _ => Stage3.Prop23.point

/-- Similar segments of circles on equal straight lines are equal to one another.

III.24 as brief 0006 restates it: the segments are congruent. -/
theorem Prop24 {A B C D E F : Point} {AEB CFD : Circle} (hA : OnCircle A AEB)
    (hB : OnCircle B AEB) (hE : OnCircle E AEB) (hC : OnCircle C CFD) (hD : OnCircle D CFD)
    (hF : OnCircle F CFD) (hE_AB : ¬ Collinear A B E) (hF_CD : ¬ Collinear C D F)
    (hAB : ‖A B‖ = ‖C D‖) (hsim : ∠ A E B = ∠ C F D) :
    Arc.Congruent ⟨AEB, A, B, E⟩ ⟨CFD, C, D, F⟩ := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Stage3.Prop24 :=
  Elements.BookIII.Prop24 (exists_centre _) (exists_centre _)
example : type_of% @Elements.BookIII.Prop24 := fun _ _ => Stage3.Prop24

/-- **III.24, the circles and the measures** (companion of III.24, "III.24 equalCircles").
Similar segments on equal straight lines lie in equal circles, and their circumferences are
equal in measure. -/
theorem Prop24.equalCircles {A B C D E F : Point} {AEB CFD : Circle} (hA : OnCircle A AEB)
    (hB : OnCircle B AEB) (hE : OnCircle E AEB) (hC : OnCircle C CFD) (hD : OnCircle D CFD)
    (hF : OnCircle F CFD) (hE_AB : ¬ Collinear A B E) (hF_CD : ¬ Collinear C D F)
    (hAB : ‖A B‖ = ‖C D‖) (hsim : ∠ A E B = ∠ C F D) :
    EqualCircles AEB CFD ∧ circumference AEB A E B = circumference CFD C F D := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) :
    type_of% @Stage3.Prop24.equalCircles :=
  Elements.BookIII.Prop24.equalCircles (exists_centre _) (exists_centre _)
example : type_of% @Elements.BookIII.Prop24.equalCircles :=
  fun _ _ => Stage3.Prop24.equalCircles

/-- The check of brief 0006's pattern: `Prop24.equalCircles` has III.24's statement before
stage 3, restated without its centres (`Restated.lean`). -/
example : type_of% @Centre.Prop24 := @Stage3.Prop24.equalCircles

end Elements.BookIII.Staging.Centre.Stage3

namespace Elements.BookIII.Staging.Centre.Stage4

open Tacit

/-- **III.25's circle is the segment's circle** (companion of III.25, "III.25 complete").
Let A, C be points of a circle α, and B a point of its arc on P's side of AC. Any circle γ
through A, B and C is α, and every point of the arc AC on P's side is on γ.

Brief 0006's statement asks also that α have a centre, and that γ have one, E, which names
nothing else in the statement; both go. -/
theorem Prop25.complete {A C P B : Point} {α γ : Circle} (hA : OnCircle A α)
    (hC : OnCircle C α) (hB : OnArc B ⟨α, A, C, P⟩) (hBP : SameSideOf B P A C)
    (hAγ : OnCircle A γ) (hBγ : OnCircle B γ) (hCγ : OnCircle C γ) :
    γ = α ∧ ∀ X : Point, OnArc X ⟨α, A, C, P⟩ → OnCircle X γ := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) :
    type_of% @Stage4.Prop25.complete :=
  fun {_ _ _ _} {_ γ} hA hC hB hBP hAγ hBγ hCγ =>
    (exists_centre γ).elim fun _ hE =>
      Elements.BookIII.Prop25.complete (exists_centre _) hA hC hB hBP hE hAγ hBγ hCγ
example : type_of% @Elements.BookIII.Prop25.complete :=
  fun _ hA hC hB hBP _ hAγ hBγ hCγ => Stage4.Prop25.complete hA hC hB hBP hAγ hBγ hCγ

/-- **III.25, handed the whole circle** (companion of III.25, "III.25 of_circle").
Handed the circle ABC, the core finds a circle that is ABC itself, so its centre E is the
centre of ABC. -/
theorem Prop25.of_circle {A C : Point} {ABC : Circle} (hA : OnCircle A ABC)
    (hC : OnCircle C ABC) :
    ∀ P : Point, ¬ Collinear A C P → ∃ B D E : Point, OnCircle B ABC ∧ SameSideOf B P A C ∧
      Between A D C ∧ ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E ABC ∧ Collinear D B E ∧
      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧
      (∠ A B D < ∠ B A D → SameSideOf E B A C) := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) :
    type_of% @Stage4.Prop25.of_circle :=
  Elements.BookIII.Prop25.of_circle (exists_centre _)
example : type_of% @Elements.BookIII.Prop25.of_circle :=
  fun _ => Stage4.Prop25.of_circle

/-- The check of brief 0006's pattern: `Prop25.of_circle` has III.25's statement before
stage 4, restated without its centre (`Restated.lean`). -/
example : type_of% @Centre.Prop25 := @Stage4.Prop25.of_circle

end Elements.BookIII.Staging.Centre.Stage4

namespace Elements.Staging.Centre

/-- **A drawn arc** (brief 0006's `Arc.Drawn`, without its centre): its two ends are on the
circle, and the point naming its side is off the straight line joining them (so the ends
differ). Brief 0006's definition asks also that the circle have a centre, because
`Prop23.point` needed one; once every circle has a centre, the clause goes. -/
def Arc.Drawn (a : Arc) : Prop :=
  OnCircle a.B a.circle ∧ OnCircle a.C a.circle ∧ ¬ Collinear a.B a.C a.K

/-- Given the rule's content, the two definitions agree (checked by Lean). -/
example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) (a : Arc) :
    Centre.Arc.Drawn a ↔ a.Drawn :=
  ⟨fun h => ⟨exists_centre _, h⟩, fun h => h.2⟩

end Elements.Staging.Centre
