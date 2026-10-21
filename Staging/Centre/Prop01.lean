import Elements.Figure.Circles
import Elements.BookIII.Prop01

/-!
# Staging: III.1 without the centre hypothesis

Brief 0008. The rule `exists_centre` is now available. III.1 keeps its conclusion, the
points of Euclid's construction with `Centre F ABC`, and drops its hypothesis
`∃ G, Centre G ABC`. Euclid's construction is kept apart from its correctness:

* `Elements.BookIII.Prop1.construction` now lives before the main III.1. It receives a
  circle and two points A, B, with no centre supplied. It uses `exists_centre` only inside
  the proof that D is within the circle, through `Prop1.within`; that centre supplies none
  of the points returned. The construction returns both right angles ADC and BDC and that
  C is off AB.
* The restated `Prop1` adds the correctness: "let G be the centre" takes a centre from the
  rule, and Euclid's reductio shows that it is F. The first check below runs the reductio
  on the home construction's output. Its hypothesis supplies G for this correctness
  argument; the construction already uses the rule to prove D within.
* `Prop1.of_circle` takes two points of the circle (`exists_point_on_circle`) and runs
  III.1 on the straight line through them, as Euclid draws AB "through it at random".

The main III.1 still keeps its centre hypothesis and calls the home construction under
its three sentences. The restated theorem here will replace it later, and the entry
point will go after the porism. The remaining staged names sit in
`Elements.BookIII.Staging.Centre`.
-/

namespace Elements.BookIII.Staging.Centre

open Tacit

/-- To find the centre of a given circle. -/
theorem Prop1 {A B : Point} {ABC : Circle} (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hAB : A ≠ B) :
    ∃ F C D E : Point, Centre F ABC ∧ Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧
      OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ Between C F E ∧ ‖C F‖ = ‖F E‖ := by
  sorry

/-- The check that the construction and the correctness fit: given the rule's content, the
restated III.1 follows from the home construction and Euclid's reductio, run on the
construction's output (checked by Lean). The hypothesis supplies G at "let G be the centre";
the construction uses the rule itself only to prove D within. -/
example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop1 := by
  intro A B ABC hA hB hAB
  obtain ⟨F, C, D, E, hADB, hAD, hC, hE, hCDE, hADC, hBDC, hC_AB, hCFE, hCF⟩ :=
    Elements.BookIII.Prop1.construction hA hB hAB
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
      Prop1.equal_adjacent hDAG hDBG hDA_DB (Definition15 hG hA hB)
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
