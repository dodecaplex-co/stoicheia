import Elements.Figure.Circles
import Elements.Figure.CirclePoints
import Elements.Figure.Incidence
import Elements.Figure.RuleBase
import Elements.BookIII.Prop01

/-!
# Staging: III.1, once every circle has a centre

Brief 0008. The owner approved a rule that every circle has a centre, `exists_centre`, which
lands only in the coordinator's own pull request, now that the model's law names are data
(issue #40, landed) and this brief is frozen. Until it lands no such rule exists, and
nothing here declares one: where a check needs the rule, it takes the rule's content as a
hypothesis named `exists_centre`, so that, once the rule lands, the same words refer to it.

III.1 keeps its conclusion, the points of Euclid's construction with `Centre F ABC`, and
drops its hypothesis `∃ G, Centre G ABC`. Euclid's construction is kept apart from its
correctness:

* `Prop1.construction` finds D, C, E and F as Euclid does, for a circle given with two
  points A, B and nothing more. It is proved here with today's construction steps,
  unchanged: no centre of the circle is given to it, and no rule that a centre exists is
  used. It returns the right angles ADC and BDC, so that the reductio takes the angle CDB
  from it, as today's proof does.
* The restated `Prop1` adds the correctness: "let G be the centre" takes a centre from the
  rule, and Euclid's reductio shows that it is F. The first check below proves the restated
  statement this way, from `Prop1.construction`, the rule's content and today's reductio.
* `Prop1.of_circle` is the entry point for a circle alone: it takes two points of the
  circle (Points 7, `exists_point_on_circle`) and runs III.1 on the straight line through
  them, as Euclid draws AB "through it at random".

Once proved, the construction goes before `Elements.BookIII.Prop1` first, under
today's statement (the record shows it as a `grouped` passage naming it), the restated
theorem then replaces today's, and the entry point goes after the porism as a lemma; this
file is then deleted. The names here sit in `Elements.BookIII.Staging.Centre`,
not `Elements.BookIII.Staging`, which brief 0006's staged III.24 and III.25 already use.
-/

namespace Elements.BookIII.Staging.Centre

open Tacit

/-- **Euclid's construction for III.1**, for a circle given with two points A, B of it and
no centre. AB is bisected at D; DC is drawn at right angles to AB, the angles ADC and BDC
both right, and through to E, so that C and E are on the circle, either side of D, and C is
off AB; and CE is bisected at F. That F is the centre is not claimed here: that is the
correctness argument, in `Prop1`. This is the construction core of FORMALIZATION, section
4: it receives only what the problem gives, and carries Euclid's three sentences of
construction. -/
theorem Prop1.construction {A B : Point} {ABC : Circle} (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hAB : A ≠ B) :
    ∃ F C D E : Point, Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧
      OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ ∠ B D C = ∟ ∧ ¬ Collinear A B C ∧
      Between C F E ∧ ‖C F‖ = ‖F E‖ := by
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  obtain ⟨D, hADB, hAD⟩ := BookI.Prop10 hAB
  have hD_L := on_line_of_between_ends hADB hA_L hB_L
  obtain ⟨Q, hQ, -⟩ := exists_off_line hAB []
  obtain ⟨X, hXQ, hX⟩ := BookI.Prop11 hAB ⟨L, hA_L, hB_L, hD_L⟩ hQ
  have hD_in : InsideCircle D ABC := inside_of_between (Or.inr hA) (Or.inr hB) hADB
  have hX_L : ¬ OnLine X L := hXQ.triangle.off_line hA_L hB_L
  have hDX : D ≠ X := fun e => hX_L (e ▸ hD_L)
  obtain ⟨N, hD_N, hX_N⟩ := Postulate1 D X hDX
  obtain ⟨E, hE, hE_N, hEDX⟩ := line_circle_beyond hD_in hD_N hX_N hDX.symm
  obtain ⟨C, hC, hC_N, hCDE⟩ := line_circle_beyond hD_in hD_N hE_N (ne_of_between hEDX)
  have hCray : OnRay C D X := OnRay.of_between_between hEDX (between_symm hCDE)
  have hDA : D ≠ A := (ne_of_between hADB).symm
  have hDB : D ≠ B := (ne_of_between (between_symm hADB)).symm
  have hADC : ∠ A D C = ∟ := by
    rw [angle_onRay_right hCray hDA.symm]
    exact hX A ⟨L, hA_L, hB_L, hA_L⟩ hDA.symm
  have hBDC : ∠ B D C = ∟ := by
    rw [angle_onRay_right hCray hDB.symm]
    exact hX B ⟨L, hA_L, hB_L, hB_L⟩ hDB.symm
  have hCD : C ≠ D := ne_of_between hCDE
  have hC_L : ¬ OnLine C L := fun h => hX_L ((line_unique hCD hC_N hD_N h hD_L) ▸ hX_N)
  obtain ⟨F, hCFE, hCF⟩ := BookI.Prop10 (ne_of_between_ends hCDE)
  exact ⟨F, C, D, E, hADB, hAD, hC, hE, hCDE, hADC, hBDC, Triangle.of_line hA_L hB_L hAB hC_L,
    hCFE, hCF⟩

/-- To find the centre of a given circle. -/
theorem Prop1 {A B : Point} {ABC : Circle} (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hAB : A ≠ B) :
    ∃ F C D E : Point, Centre F ABC ∧ Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧
      OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ Between C F E ∧ ‖C F‖ = ‖F E‖ := by
  sorry

/-- The check that the construction and the correctness fit: given the rule's content, the
restated III.1 follows from `Prop1.construction` and Euclid's reductio, which is today's,
run on the construction's output alone (checked by Lean). The centre's existence enters only
at "let G be the centre". -/
example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop1 := by
  intro A B ABC hA hB hAB
  obtain ⟨F, C, D, E, hADB, hAD, hC, hE, hCDE, hADC, hBDC, hC_AB, hCFE, hCF⟩ :=
    Prop1.construction hA hB hAB
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hD_L := on_line_of_between_ends hADB hA_L hB_L
  have hCD : C ≠ D := ne_of_between hCDE
  obtain ⟨N, hC_N, hD_N⟩ := Postulate1 C D hCD
  have hE_N : OnLine E N := on_line_of_between hCDE hC_N hD_N
  have hDA : D ≠ A := (ne_of_between hADB).symm
  have hDB : D ≠ B := (ne_of_between (between_symm hADB)).symm
  have hC_L : ¬ OnLine C L := (show Triangle A B C from hC_AB).off_line hA_L hB_L
  /- "Let G be the centre": the rule gives one. -/
  obtain ⟨G, hG⟩ := exists_centre ABC
  have hG_N : OnLine G N := by
    refine Classical.byContradiction fun hG_N => ?_
    have hG_L : ¬ OnLine G L := fun hG_L =>
      hG_N ((Prop1.middle hADB hAD
        (between_of_inside_chord hG_L hA_L hB_L (centre_inside hG) hA hB hAB)
        (by rw [len_symm A G, Definition15 hG hA hB])) ▸ hD_N)
    have hDAG : Triangle D A G := Triangle.of_line hD_L hA_L hDA hG_L
    have hDBG : Triangle D B G := Triangle.of_line hD_L hB_L hDB hG_L
    have hDA_DB : ‖D A‖ = ‖D B‖ := by rw [len_symm D A, hAD]
    have h8 : ∠ A D G = ∠ G D B :=
      (BookI.Prop8 hDAG hDBG hDA_DB rfl
        (by rw [len_symm A G, len_symm B G, Definition15 hG hA hB])).trans
        (angle_symm hDBG.ne₁₂.symm hDBG.ne₁₃.symm)
    have hADG : ∠ A D G = ∟ := Postulate4 ⟨B, hADB, hDAG.bac, h8⟩
    have hGDB : ∠ G D B = ∟ := h8 ▸ hADG
    /- The angle CDB, right by construction, in place of FDB, as today. -/
    have hDBC : Triangle D B C := Triangle.of_line hD_L hB_L hDB hC_L
    obtain ⟨M, hD_M, hC_M, hG_M⟩ := Prop1.perpendicular hDBC.bac hDBG.bac hBDC
      ((angle_symm hDBG.ne₁₂.symm hDBG.ne₁₃.symm).trans hGDB)
    exact hG_N ((line_unique hCD hC_M hD_M hC_N hD_N) ▸ hG_M)
  have hCGE := between_of_inside_chord hG_N hC_N hE_N (centre_inside hG) hC hE
    (ne_of_between_ends hCDE)
  obtain rfl : G = F := Prop1.middle hCFE hCF hCGE (by rw [len_symm C G, Definition15 hG hC hE])
  exact ⟨G, C, D, E, hG, hADB, hAD, hC, hE, hCDE, hADC, hCFE, hCF⟩

/-- The check that nothing is lost: today's III.1 follows from the restated one, which asks
for less (checked by Lean). -/
example : type_of% @Elements.BookIII.Prop1 := fun _ => Centre.Prop1

/-- **III.1 for a circle alone.** Given only a circle, Euclid's construction finds its
centre: two points A, B of the circle are taken (Points 7), and III.1 runs on the straight
line AB, drawn "through it at random". It returns A and B with III.1's points; that A and B
differ follows from `Between A D B`. A lemma beside III.1, after its porism, with no
certificate entry: it rests on what III.1 rests on and on Points 7, which III.1 does not
use. For the bare existence of a centre, cite the rule itself. -/
theorem Prop1.of_circle (ABC : Circle) :
    ∃ A B F C D E : Point, OnCircle A ABC ∧ OnCircle B ABC ∧ Centre F ABC ∧
      Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧ OnCircle E ABC ∧ Between C D E ∧
      ∠ A D C = ∟ ∧ Between C F E ∧ ‖C F‖ = ‖F E‖ := by
  obtain ⟨A, hA, -⟩ := exists_point_on_circle ABC []
  obtain ⟨B, hB, hBA⟩ := exists_point_on_circle ABC [A]
  have hAB : A ≠ B := fun e => hBA (e ▸ List.mem_singleton_self A)
  obtain ⟨F, C, D, E, h⟩ := Centre.Prop1 hA hB hAB
  exact ⟨A, B, F, C, D, E, hA, hB, h⟩

end Elements.BookIII.Staging.Centre
