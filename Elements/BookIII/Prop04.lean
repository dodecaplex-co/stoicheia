import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Prop01
import Elements.BookIII.Prop03

/-!
# Book III, Proposition 4

Euclid's text, in Heath's translation: [`heath/III/04.md`](../../heath/III/04.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If in a circle two straight lines cut one another which are not through the centre, they do not
bisect one another. -/
theorem Prop4 {A B C D E : Point} {ABCD : Circle}
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hD : OnCircle D ABCD) (hAEC : Between A E C) (hBED : Between B E D)
    (hB_AC : ¬ Collinear A C B) (hAC : ∀ F : Point, Centre F ABCD → ¬ Collinear A C F)
    (hBD : ∀ F : Point, Centre F ABCD → ¬ Collinear B D F) :
    ¬ (‖A E‖ = ‖E C‖ ∧ ‖B E‖ = ‖E D‖) := by
  -- Let ABCD be a circle, and in it let the two straight lines AC, BD, which are not through
  -- the centre, cut one another at E;
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C (ne_of_between_ends hAEC)
  have hE_L : OnLine E L := on_line_of_between_ends hAEC hA_L hC_L
  obtain ⟨N, hB_N, hD_N⟩ := Postulate1 B D (ne_of_between_ends hBED)
  have hE_N : OnLine E N := on_line_of_between_ends hBED hB_N hD_N
  -- I say that they do not bisect one another.
  -- For, if possible, let them bisect one another, so that AE is equal to EC, and BE to ED;
  rintro ⟨hAE, hBE⟩
  -- let the centre of the circle ABCD be taken [III. 1], and let it be F; let FE be joined.
  /- The centre is found by III.1's construction, on a straight line drawn through the
     circle at random (`Prop1.of_circle`), as Euclid finds it. The proof keeps the centre
     alone, which is what Euclid takes from III.1. -/
  obtain ⟨-, -, F, -, -, -, -, -, hF, -⟩ := Prop1.of_circle ABCD
  have hF_L : ¬ OnLine F L := (show Triangle A C F from hAC F hF).off_line hA_L hC_L
  have hF_N : ¬ OnLine F N := (show Triangle B D F from hBD F hF).off_line hB_N hD_N
  have hEF : E ≠ F := fun h => hF_L (h ▸ hE_L)
  obtain ⟨M, hE_M, hF_M⟩ := Postulate1 E F hEF
  -- Then, since a straight line FE through the centre bisects a straight line AC not through
  -- the centre,
  -- it also cuts it at right angles; [III. 3]
  have h₁ := (Prop3 hF hA hC hAEC (hAC F hF)).1 hAE
  -- therefore the angle FEA is right.
  have hFEA : ∠ F E A = ∟ := (angle_symm hEF.symm (ne_of_between hAEC)).trans h₁.1
  -- Again, since a straight line FE bisects a straight line BD,
  -- it also cuts it at right angles; [III. 3]
  have h₂ := (Prop3 hF hB hD hBED (hBD F hF)).1 hBE
  -- therefore the angle FEB is right.
  have hFEB : ∠ F E B = ∟ := (angle_symm hEF.symm (ne_of_between hBED)).trans h₂.1
  -- But the angle FEA was also proved right;
  -- therefore the angle FEA is equal to the angle FEB, the less to the greater: which is
  -- impossible.
  have hFEA_FEB : ∠ F E A = ∠ F E B := hFEA.trans hFEB.symm
  /- Whichever of B and D lies on A's side of FE (in Euclid's figure, B) makes with FE
     an angle equal to FEA, so it lies on the straight line EA (`onRay_of_angle_eq`, whose
     proof is the part equal to the whole); then BD would be AC. -/
  have hA_M : ¬ OnLine A M := fun h =>
    hF_L (line_unique (ne_of_between hAEC) hA_L hE_L h hE_M ▸ hF_M)
  have hB_M : ¬ OnLine B M := fun h =>
    hF_N (line_unique (ne_of_between hBED) hB_N hE_N h hE_M ▸ hF_M)
  have hD_M : ¬ OnLine D M := fun h =>
    hF_N (line_unique (ne_of_between (between_symm hBED)) hD_N hE_N h hE_M ▸ hF_M)
  have hless : ∀ P : Point, OnLine P N → SameSide P A M → ∠ F E A = ∠ F E P → False := by
    intro P hP_N hPA hFEP
    obtain ⟨-, hPE, hEAP, -⟩ :=
      onRay_of_angle_eq (SameSideOf.of_line hEF hE_M hF_M hPA) hFEP.symm
    obtain ⟨K, hE_K, hA_K, hP_K⟩ := hEAP
    have hKL : K = L := line_unique (ne_of_between hAEC).symm hE_K hA_K hE_L hA_L
    have hP_L : OnLine P L := hKL ▸ hP_K
    have hNL : N = L := line_unique hPE hP_N hE_N hP_L hE_L
    exact hB_AC ⟨L, hA_L, hC_L, hNL ▸ hB_N⟩
  by_cases hs : SameSide B A M
  · exact hless B hB_N hs hFEA_FEB
  · have hBA : OppositeSides B A M := ⟨hB_M, hA_M, hs⟩
    have hBD' : OppositeSides B D M := ⟨hB_M, hD_M, pasch3 hBED hE_M⟩
    have hFED : ∠ F E D = ∟ :=
      (angle_symm hEF.symm (ne_of_between (between_symm hBED))).trans h₂.2
    exact hless D hD_N (same_side_symm (same_side_of_opposite_sides hBA hBD'))
      (hFEA.trans hFED.symm)
  -- Therefore AC, BD do not bisect one another.
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
