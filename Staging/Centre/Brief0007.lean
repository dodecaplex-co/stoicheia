import Staging.Stage4b.Prop08
import Staging.Stage4b.Prop17
import Staging.Centre.Restated

/-!
# Staging: brief 0007's companions without `∃ O, Centre O α`

Brief 0008. Three statements that brief 0007 froze, staged in `Stage4b/` (#85), ask that a
circle have some centre: `Prop8.partner` and `Prop8.general` (`hABC`) and `Prop17.general`
(`hBCD`). Once every circle has a centre (the rule `exists_centre`, approved, not yet
landed), each loses that hypothesis, as below; nothing else in them changes, and the
condition said of every centre, `hGA`, stays. This is a revision of brief 0007, for the
coordinator to approve with brief 0008, made in brief 0007's files by their owners, with
the restatements of III.8 and III.17.

As in `Brief0006.lean`, each statement carries `sorry` and two checks (checked by Lean):
given the rule's content, taken as a hypothesis, brief 0007's statement gives the new one;
and the new one gives brief 0007's. Two more checks show that brief 0007's pattern
survives: III.8 and III.17, restated as `Restated.lean` restates them, still follow from
the restated companions, as today's follow from brief 0007's. Brief 0007's own checks of
today's III.8 and III.17 break the moment those lose their hypotheses, so the companions
move with them. The names sit in `Elements.BookIII.Staging.Centre.Stage4b`, after brief
0007's folder.
-/

namespace Elements.BookIII.Staging.Centre.Stage4b

open Tacit

/-- **III.8, the partner equally inclined and in the same class** (brief 0007, a step of
III.8 general), without its centre. -/
theorem Prop8.partner {A D G K B : Point} {ABC : Circle}
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hG : OnCircle G ABC)
    (hDGA : Between D G A) (hGA : ∀ M : Point, Centre M ABC → Between G M A)
    (hK : OnCircle K ABC) (hB : OnCircle B ABC) (hBK : OppositeSidesOf B K D A)
    (hDB : ‖D B‖ = ‖D K‖) :
    ∠ A D B = ∠ A D K ∧
    ((∃ C : Point, OnCircle C ABC ∧ Between D B C) ↔
      (∃ C : Point, OnCircle C ABC ∧ Between D K C)) ∧
    ((∃ H : Point, OnCircle H ABC ∧ Between D H B) ↔
      (∃ H : Point, OnCircle H ABC ∧ Between D H K)) := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) :
    type_of% @Stage4b.Prop8.partner :=
  Elements.BookIII.Prop8.partner (exists_centre _)
example : type_of% @Elements.BookIII.Prop8.partner := fun _ => Stage4b.Prop8.partner

/-- **III.8, general** (brief 0007, companion of III.8), without its centre. -/
theorem Prop8.general {A D G : Point} {ABC : Circle}
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hG : OnCircle G ABC)
    (hDGA : Between D G A) (hGA : ∀ M : Point, Centre M ABC → Between G M A) :
    (∀ E : Point, OnCircle E ABC → E ≠ A → ‖D E‖ < ‖D A‖) ∧
    (∀ E F : Point, OnCircle E ABC → OnCircle F ABC →
      (∃ H : Point, OnCircle H ABC ∧ Between D H E) →
      (∃ L : Point, OnCircle L ABC ∧ Between D L F) →
      ¬ Collinear D A E → ¬ Collinear D A F → ∠ A D E < ∠ A D F → ‖D F‖ < ‖D E‖) ∧
    (∀ K : Point, OnCircle K ABC → K ≠ G → ‖D G‖ < ‖D K‖) ∧
    (∀ K L : Point, OnCircle K ABC → OnCircle L ABC →
      (∃ C : Point, OnCircle C ABC ∧ Between D K C) →
      (∃ F : Point, OnCircle F ABC ∧ Between D L F) →
      ¬ Collinear D A K → ¬ Collinear D A L → ∠ A D K < ∠ A D L → ‖D K‖ < ‖D L‖) ∧
    (∀ K : Point, OnCircle K ABC → ¬ Collinear D A K → ∃ B : Point, OnCircle B ABC ∧
      OppositeSidesOf B K D A ∧ ‖D B‖ = ‖D K‖ ∧
      ∀ N : Point, OnCircle N ABC → ‖D N‖ = ‖D K‖ → N = K ∨ N = B) := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) :
    type_of% @Stage4b.Prop8.general :=
  Elements.BookIII.Prop8.general (exists_centre _)
example : type_of% @Elements.BookIII.Prop8.general := fun _ => Stage4b.Prop8.general

/-- The check of brief 0007's pattern: III.8, restated without its centre (`Restated.lean`),
follows from `Prop8.general` restated, as today's III.8 follows from brief 0007's (checked
by Lean). Two points on one side of DA are off it. -/
example : type_of% @Centre.Prop8 := by
  intro A D G ABC hD hA hG hDGA hGA
  obtain ⟨hgreatest, hconcave, hleast, hconvex, hpartner⟩ :=
    Stage4b.Prop8.general hD hA hG hDGA hGA
  exact ⟨hgreatest,
    fun E F hE hF hHE hLF hEF hlt =>
      hconcave E F hE hF hHE hLF hEF.triangle hEF.symm.triangle hlt,
    hleast,
    fun K L hK hL hKC hLF hKL hlt =>
      hconvex K L hK hL hKC hLF hKL.triangle hKL.symm.triangle hlt,
    hpartner⟩

/-- **III.17, general** (brief 0007, companion of III.17), without its centre: from a point A
not within the circle BCD, a straight line AX touching it. -/
theorem Prop17.general {A : Point} {BCD : Circle} (hA : ¬ InsideCircle A BCD) :
    ∃ X : Point, Touches A X BCD := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) :
    type_of% @Stage4b.Prop17.general :=
  Elements.BookIII.Prop17.general (exists_centre _)
example : type_of% @Elements.BookIII.Prop17.general := fun _ => Stage4b.Prop17.general

/-- The check of brief 0007's pattern: III.17, restated without its centre (`Restated.lean`),
follows from `Prop17.general` restated, as today's III.17 follows from brief 0007's (checked
by Lean). A is outside the circle, so the point where AX meets the circle is not A, and the
straight line it names with A is AX. -/
example : type_of% @Centre.Prop17 := by
  intro A BCD hA
  obtain ⟨X, hAX, hX⟩ := Stage4b.Prop17.general hA.1
  obtain ⟨L, hA_L, hX_L⟩ := Postulate1 A X hAX
  obtain ⟨⟨B, hB_L, hB⟩, -⟩ := hX L hA_L hX_L
  have hAB : A ≠ B := fun e => hA.2 (e ▸ hB)
  refine ⟨B, hB, hAB, fun M hA_M hB_M => ?_⟩
  obtain rfl : L = M := line_unique hAB hA_L hB_L hA_M hB_M
  exact hX L hA_L hX_L

end Elements.BookIII.Staging.Centre.Stage4b
