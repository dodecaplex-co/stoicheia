import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Feet
import Elements.BookIII.Circumferences
import Elements.BookI.Prop12
import Elements.BookI.Prop47
import Elements.BookII.Prop05
import Elements.BookIII.Prop03

/-!
# Book III, Proposition 35

Euclid's text, in Heath's translation: [`heath/III/35.md`](../../heath/III/35.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- This is Euclid's argument for one straight line AC through a point E other than the
centre F: the rectangle contained by AE, EC, together with the square on FE, is equal to the
square on FC. It serves as his "For the same reason" for DB, and covers the intermediate
cases, where one straight line passes through the centre or E is the foot of the
perpendicular. -/
theorem Prop35.cut {A C E F : Point} {α : Circle} (hF : Centre F α) (hA : OnCircle A α)
    (hC : OnCircle C α) (hAEC : Between A E C) (hEF : E ≠ F) :
    rect A E E C + sq F E = sq F C := by
  have hAC : A ≠ C := ne_of_between_ends hAEC
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hAC
  have hE_L : OnLine E L := on_line_of_between_ends hAEC hA_L hC_L
  by_cases hF_AC : Collinear A C F
  · /- When AC passes through the centre, F bisects it, and II.5 applies there. -/
    obtain ⟨M, hA_M, hC_M, hF_M⟩ := hF_AC
    have hAFC : Between A F C :=
      between_of_inside_chord hF_M hA_M hC_M (centre_inside hF) hA hC hAC
    have hAF : ‖A F‖ = ‖F C‖ := by
      rw [len_symm A F]
      exact Definition15 hF hA hC
    exact BookII.Prop5 hAFC hAF hAEC hEF
  · /- The perpendicular from F, drawn by I.12, falls within AC (`foot_between`). -/
    obtain ⟨G, hG, hFG⟩ := BookI.Prop12 hAC hF_AC
    have hAGC : Between A G C := foot_between hF hA hC hF_AC hG hFG
    have hG_L : OnLine G L := on_line_of_between_ends hAGC hA_L hC_L
    have hF_L : ¬ OnLine F L := Triangle.off_line hF_AC hA_L hC_L
    have hFG' : F ≠ G := fun e => hF_L (e ▸ hG_L)
    have hAGF : ∠ A G F = ∟ := by
      rw [angle_symm (ne_of_between hAGC) hFG']
      exact hFG A ⟨L, hA_L, hC_L, hA_L⟩ (ne_of_between hAGC)
    /- It bisects AC [III. 3]. -/
    have hAG : ‖A G‖ = ‖G C‖ := (Prop3 hF hA hC hAGC hF_AC).2 hAGF
    /- AC is cut into equal parts at G and unequal parts at E [II. 5]; if E is G, the
       square on EG is nothing. -/
    have h5 : rect A E E C + sq E G = sq G C := by
      by_cases hEG : E = G
      · subst hEG
        rw [sq_self, add_zero]
        exact rect_congr hAG rfl
      · rw [sq_symm E G]
        exact BookII.Prop5 hAGC hAG hAEC hEG
    /- The square on GF is added to each. -/
    have hadd : rect A E E C + sq E G + sq G F = sq G C + sq G F :=
      CommonNotion2 h5 rfl
    /- The two right triangles replace the pairs of squares [I. 47]. -/
    have hFE : sq F E = sq E G + sq G F := by
      by_cases hEG : E = G
      · subst hEG
        rw [sq_self, add_comm, add_zero, sq_symm]
      · have t : Triangle G F E :=
          (Triangle.of_line hG_L hE_L (Ne.symm hEG) hF_L).acb
        rw [BookI.Prop47.sq t (hFG E ⟨L, hA_L, hC_L, hE_L⟩ hEG),
          sq_symm G E, sq_symm F G]
        ac_rfl
    have hFC : sq F C = sq G C + sq G F := by
      have hCG : C ≠ G := ne_of_between (between_symm hAGC)
      have t : Triangle G F C :=
        (Triangle.of_line hG_L hC_L (Ne.symm hCG) hF_L).acb
      rw [BookI.Prop47.sq t (hFG C ⟨L, hA_L, hC_L, hC_L⟩ hCG), sq_symm F G]
      ac_rfl
    rw [hFE, hFC, ← add_assoc]
    exact hadd

/-- If in a circle two straight lines cut one another, the rectangle contained by the segments of
the one is equal to the rectangle contained by the segments of the other. -/
theorem Prop35 {A B C D E : Point} {ABCD : Circle} (hA : OnCircle A ABCD)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hD : OnCircle D ABCD)
    (hAEC : Between A E C) (hBED : Between B E D) :
    rect A E E C = rect D E E B := by
  -- For in the circle ABCD let the two straight lines AC, BD cut one another at the point E;
  -- I say that the rectangle contained by AE, EC is equal to the rectangle contained by DE,
  -- EB.
  -- If now AC, BD are through the centre, so that E is the centre of the circle ABCD,
  by_cases hE : Centre E ABCD
  -- it is manifest that, AE, EC, DE, EB being equal,
  · have h₁ : ‖A E‖ = ‖D E‖ := by
      rw [len_symm A E, Definition15 hE hA hD, len_symm]
    have h₂ : ‖E C‖ = ‖E B‖ := Definition15 hE hC hB
    -- the rectangle contained by AE, EC is also equal to the rectangle contained by DE, EB.
    exact rect_congr h₁ h₂
  -- Next let AC, DB not be through the centre;
  -- let the centre of ABCD be taken, and let it be F;
  obtain ⟨F, hF⟩ := exists_centre ABCD
  have hEF : E ≠ F := fun e => hE (e ▸ hF)
  have hAC : rect A E E C + sq F E = sq F C := by
    by_cases hF_AC : Collinear A C F
    · /- Robert Simson adds the intermediate cases, where AC passes through the centre
         and E does not. Then F bisects AC, and `Prop35.cut` gives the squares by II.5 at
         once. -/
      exact Prop35.cut hF hA hC hAEC hEF
    have hAC' : A ≠ C := ne_of_between_ends hAEC
    obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hAC'
    have hE_L : OnLine E L := on_line_of_between_ends hAEC hA_L hC_L
    -- from F let FG, FH be drawn perpendicular to the straight lines AC, DB, and let FB, FC, FE
    -- be joined.
    obtain ⟨G, hG, hFG⟩ := BookI.Prop12 hAC' hF_AC
    /- FH is drawn in `Prop35.cut`, applied to DB below. The straight lines joined need
       no construction in Lean. -/
    -- Then, since a straight line GF through the centre cuts a straight line AC not through the
    -- centre at right angles,
    have hAGC : Between A G C := foot_between hF hA hC hF_AC hG hFG
    have hG_L : OnLine G L := on_line_of_between_ends hAGC hA_L hC_L
    have hF_L : ¬ OnLine F L := Triangle.off_line hF_AC hA_L hC_L
    have hFG' : F ≠ G := fun e => hF_L (e ▸ hG_L)
    have hAGF : ∠ A G F = ∟ := by
      rw [angle_symm (ne_of_between hAGC) hFG']
      exact hFG A ⟨L, hA_L, hC_L, hA_L⟩ (ne_of_between hAGC)
    -- it also bisects it; [III. 3]
    have hbisect := (Prop3 hF hA hC hAGC hF_AC).2 hAGF
    -- therefore AG is equal to GC.
    have hAG : ‖A G‖ = ‖G C‖ := hbisect
    -- Since, then, the straight line AC has been cut into equal parts at G and into unequal
    -- parts at E,
    -- the rectangle contained by AE, EC together with the square on EG is equal to the square on
    -- GC; [II. 5]
    have h5 : rect A E E C + sq E G = sq G C := by
      by_cases hEG : E = G
      · /- If E is G, the square on EG is nothing, as in `Prop35.cut`. -/
        subst hEG
        rw [sq_self, add_zero]
        exact rect_congr hAG rfl
      · rw [sq_symm E G]
        exact BookII.Prop5 hAGC hAG hAEC hEG
    -- Let the square on GF be added;
    have hadd := CommonNotion2 h5 (rfl : sq G F = sq G F)
    -- therefore the rectangle AE, EC together with the squares on GE, GF is equal to the squares
    -- on CG, GF.
    have hsum : rect A E E C + (sq G E + sq G F) = sq C G + sq G F := by
      rw [sq_symm G E, sq_symm C G, ← add_assoc]
      exact hadd
    -- But the square on FE is equal to the squares on EG, GF,
    have hFE : sq F E = sq E G + sq G F := by
      by_cases hEG : E = G
      · subst hEG
        rw [sq_self, add_comm, add_zero, sq_symm]
      · have t : Triangle G F E :=
          (Triangle.of_line hG_L hE_L (Ne.symm hEG) hF_L).acb
        rw [BookI.Prop47.sq t (hFG E ⟨L, hA_L, hC_L, hE_L⟩ hEG),
          sq_symm G E, sq_symm F G]
        ac_rfl
    -- and the square on FC is equal to the squares on CG, GF; [I. 47]
    have hFC : sq F C = sq C G + sq G F := by
      have hCG : C ≠ G := ne_of_between (between_symm hAGC)
      have t : Triangle G F C :=
        (Triangle.of_line hG_L hC_L (Ne.symm hCG) hF_L).acb
      rw [BookI.Prop47.sq t (hFG C ⟨L, hA_L, hC_L, hC_L⟩ hCG),
        sq_symm F G, sq_symm G C]
      ac_rfl
    -- therefore the rectangle AE, EC together with the square on FE is equal to the square on
    -- FC.
    rw [hFE, hFC, sq_symm E G]
    exact hsum
  -- And FC is equal to FB;
  have hFC_FB : ‖F C‖ = ‖F B‖ := Definition15 hF hC hB
  -- therefore the rectangle AE, EC together with the square on EF is equal to the square on
  -- FB.
  rw [sq_congr hFC_FB] at hAC
  -- For the same reason, also,
  -- the rectangle DE, EB together with the square on FE is equal to the square on FB.
  have hDB : rect D E E B + sq F E = sq F B :=
    Prop35.cut hF hD hB (between_symm hBED) hEF
  -- But the rectangle AE, EC together with the square on FE was also proved equal to the
  -- square on FB;
  -- therefore the rectangle AE, EC together with the square on FE is equal to the rectangle
  -- DE, EB together with the square on FE.
  have hboth : rect A E E C + sq F E = rect D E E B + sq F E := hAC.trans hDB.symm
  -- Let the square on FE be subtracted from each;
  -- therefore the rectangle contained by AE, EC which remains is equal to the rectangle
  -- contained by DE, EB.
  exact CommonNotion3 hboth rfl
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
