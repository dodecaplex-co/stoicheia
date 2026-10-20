import Elements.Figure.Basics
import Elements.Figure.Circles
import Elements.BookIII.Squares
import Elements.BookI.Prop47
import Elements.BookIII.Prop01
import Elements.BookIII.Prop03

/-!
# Book III, Proposition 14

Euclid's text, in Heath's translation: [`heath/III/14.md`](../../heath/III/14.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- In a circle equal straight lines are equally distant from the centre, and those which are
equally distant from the centre are equal to one another. -/
theorem Prop14 {A B C D E F G : Point} {ABDC : Circle} (hE : Centre E ABDC) (hA : OnCircle A ABDC)
    (hB : OnCircle B ABDC) (hC : OnCircle C ABDC) (hD : OnCircle D ABDC)
    (hE_AB : ¬ Collinear A B E) (hE_CD : ¬ Collinear C D E) (hF : Collinear A B F)
    (hEF : ∀ P : Point, Collinear A B P → P ≠ F → ∠ E F P = ∟) (hG : Collinear C D G)
    (hEG : ∀ P : Point, Collinear C D P → P ≠ G → ∠ E G P = ∟) :
    ‖A B‖ = ‖C D‖ ↔ ‖E F‖ = ‖E G‖ := by
  -- Let ABDC be a circle, and let AB, CD be equal straight lines in it;
  -- I say that AB, CD are equally distant from the centre.
  -- For let the centre of the circle ABDC be taken [III. 1], and let it be E; from E let EF,
  -- EG be drawn perpendicular to AB, CD, and let AE, EC be joined.
  obtain ⟨E₀, -, -, -, hE₀, -⟩ := Prop1 ⟨E, hE⟩ hA hB (Triangle.ne₁₂ hE_AB)
  obtain rfl : E = E₀ := centre_unique hE hE₀
  /- The given perpendiculars fall between the ends of their straight lines. -/
  have hAFB : Between A F B := foot_between hE hA hB hE_AB hF hEF
  have hCGD : Between C G D := foot_between hE hC hD hE_CD hG hEG
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B (ne_of_between_ends hAFB)
  obtain ⟨M, hC_M, hD_M⟩ := Postulate1 C D (ne_of_between_ends hCGD)
  have hF_L : OnLine F L := on_line_of_between_ends hAFB hA_L hB_L
  have hG_M : OnLine G M := on_line_of_between_ends hCGD hC_M hD_M
  have hE_L : ¬ OnLine E L := Triangle.off_line hE_AB hA_L hB_L
  have hE_M : ¬ OnLine E M := Triangle.off_line hE_CD hC_M hD_M
  have hEF' : E ≠ F := fun e => hE_L (e ▸ hF_L)
  have hEG' : E ≠ G := fun e => hE_M (e ▸ hG_M)
  have hAFE : ∠ A F E = ∟ := by
    rw [angle_symm (ne_of_between hAFB) hEF']
    exact hEF A ⟨L, hA_L, hB_L, hA_L⟩ (ne_of_between hAFB)
  have hCGE : ∠ C G E = ∟ := by
    rw [angle_symm (ne_of_between hCGD) hEG']
    exact hEG C ⟨M, hC_M, hD_M, hC_M⟩ (ne_of_between hCGD)
  have tF : Triangle F A E :=
    Triangle.of_line hF_L hA_L (ne_of_between hAFB).symm hE_L
  have tG : Triangle G C E :=
    Triangle.of_line hG_M hC_M (ne_of_between hCGD).symm hE_M
  -- Then, since a straight line EF through the centre cuts a straight line AB not through the
  -- centre at right angles, it also bisects it. [III. 3]
  have hbisect := (Prop3 hE hA hB hAFB hE_AB).2 hAFE
  -- Therefore AF is equal to FB;
  have hAF : ‖A F‖ = ‖F B‖ := hbisect
  -- therefore AB is double of AF.
  have hAB : ‖A B‖ = ‖A F‖ + ‖A F‖ := by
    rw [← len_add_of_between hAFB, ← hAF]
  -- For the same reason
  have hCG : ‖C G‖ = ‖G D‖ := (Prop3 hE hC hD hCGD hE_CD).2 hCGE
  -- CD is also double of CG;
  have hCD : ‖C D‖ = ‖C G‖ + ‖C G‖ := by
    rw [← len_add_of_between hCGD, ← hCG]
  -- and AB is equal to CD;
  refine ⟨fun hABCD => ?_, fun hEFG => ?_⟩
  -- therefore AF is also equal to CG.
  · have hAFCG : ‖A F‖ = ‖C G‖ :=
      Magnitude.eq_of_add_self_eq (hAB.symm.trans (hABCD.trans hCD))
    -- And, since AE is equal to EC,
    have hAEEC : ‖A E‖ = ‖E C‖ := (len_symm A E).trans (Definition15 hE hA hC)
    -- the square on AE is also equal to the square on EC.
    have hsqAEEC : sq A E = sq E C := sq_congr hAEEC
    -- But the squares on AF, EF are equal to the square on AE, for the angle at F is right;
    have h47F : sq A E = sq A F + sq F E := BookI.Prop47.sq tF hAFE
    -- and the squares on EG, GC are equal to the square on EC, for the angle at G is
    -- right; [I. 47]
    have h47G : sq C E = sq C G + sq G E := BookI.Prop47.sq tG hCGE
    -- therefore the squares on AF, FE are equal to the squares on CG, GE,
    have hsums : sq F E + sq A F = sq E G + sq C G := by
      calc
        sq F E + sq A F = sq A F + sq F E := by ac_rfl
        _ = sq A E := h47F.symm
        _ = sq E C := hsqAEEC
        _ = sq C E := sq_symm E C
        _ = sq C G + sq G E := h47G
        _ = sq E G + sq C G := by rw [sq_symm G E]; ac_rfl
    -- of which the square on AF is equal to the square on CG, for AF is equal to CG;
    have hsides : sq A F = sq C G := sq_congr hAFCG
    -- therefore the square on FE which remains is equal to the square on EG,
    have hremain : sq F E = sq E G := CommonNotion3 hsums hsides
    -- therefore EF is equal to EG.
    have hequal : ‖E F‖ = ‖E G‖ := (len_symm E F).trans (BookI.Prop46.sq hremain)
    -- But in a circle straight lines are said to be equally distant from the centre when the
    -- perpendiculars drawn to them from the centre are equal; [III. Def. 4]
    -- therefore AB, CD are equally distant from the centre.
    exact hequal
  -- Next, let the straight lines AB, CD be equally distant from the centre; that is, let EF be
  -- equal to EG.
  -- I say that AB is also equal to CD.
  -- For, with the same construction, we can prove, similarly, that AB is double of AF, and CD
  -- of CG.
  /- The same construction has already shown that AB is double of AF, and CD of CG. -/
  -- And, since AE is equal to CE,
  · have hAECE : ‖A E‖ = ‖C E‖ :=
      (len_symm A E).trans ((Definition15 hE hA hC).trans (len_symm E C))
    -- the square on AE is equal to the square on CE.
    have hsqAECE : sq A E = sq C E := sq_congr hAECE
    -- But the squares on EF, FA are equal to the square on AE,
    have h47F : sq A E = sq A F + sq F E := BookI.Prop47.sq tF hAFE
    -- and the squares on EG, GC equal to the square on CE. [I. 47]
    have h47G : sq C E = sq C G + sq G E := BookI.Prop47.sq tG hCGE
    -- Therefore the squares on EF, FA are equal to the squares on EG, GC,
    have hsums : sq A F + sq E F = sq C G + sq E G := by
      rw [sq_symm E F, sq_symm E G, ← h47F, ← h47G]
      exact hsqAECE
    -- of which the square on EF is equal to the square on EG, for EF is equal to EG;
    have hfeet : sq E F = sq E G := sq_congr hEFG
    -- therefore the square on AF which remains is equal to the square on CG;
    have hremain : sq A F = sq C G := CommonNotion3 hsums hfeet
    -- therefore AF is equal to CG.
    have hAFCG : ‖A F‖ = ‖C G‖ := BookI.Prop46.sq hremain
    -- And AB is double of AF, and CD double of CG;
    have hdoubles : ‖A F‖ + ‖A F‖ = ‖C G‖ + ‖C G‖ := CommonNotion2 hAFCG hAFCG
    -- therefore AB is equal to CD.
    exact hAB.trans (hdoubles.trans hCD.symm)
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
