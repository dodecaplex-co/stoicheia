import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Prop01
import Elements.BookI.Prop05
import Elements.BookI.Prop12
import Elements.BookI.Prop17
import Elements.BookI.Prop19
import Elements.BookI.Helpers

/-!
# Book III, Proposition 16

Euclid's text, in Heath's translation: [`heath/III/16.md`](../../heath/III/16.md).
Below, each of Euclid's sentences is a `--` comment, and the Lean beneath carries it
out, with one exception. The sentences on the angle of the semicircle and the
remaining, horn-like angle, each contained by a straight line and a circumference,
stand in Euclid's words with no Lean beneath them: our angles are made by two straight
lines, and the theorem leaves out that clause of the enunciation. What Euclid proves
them by, that no other straight line can be interposed, is the theorem's second part.
The Porism is proved after the theorem, as `Prop16.porism`.
-/

namespace Elements.BookIII

open Tacit

/-- The straight line drawn at right angles to the diameter of a circle from its extremity will fall
outside the circle, and into the space between the straight line and the circumference another
straight line cannot be interposed; further the angle of the semicircle is greater, and the
remaining angle less, than any acute rectilineal angle. -/
theorem Prop16 {A B D E : Point} {ABC : Circle} (hD : Centre D ABC) (hA : OnCircle A ABC)
    (hADB : Between A D B) (hE : ¬ Collinear A B E) (hBAE : ∠ B A E = ∟) :
    (∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC) ∧
    (∀ F : Point, ¬ Collinear A E F → ∃ G : Point, Collinear A F G ∧ InsideCircle G ABC) := by
  -- Let ABC be a circle about D as centre and AB as diameter;
  have hABE : Triangle A B E := hE
  have hDAE : ∠ D A E = ∟ := by
    rw [angle_onRay_left (OnRay.of_between hADB) hABE.ne₁₃.symm]; exact hBAE
  have hDAE' : Triangle D A E := by
    obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hABE.ne₁₂
    have hD_L : OnLine D L := on_line_of_between_ends hADB hA_L hB_L
    exact (Triangle.of_line hA_L hD_L (ne_of_between hADB) (hABE.off_line hA_L hB_L)).bac
  obtain ⟨L, hA_L, hE_L⟩ := Postulate1 A E hDAE'.ne₂₃
  have hD_L : ¬ OnLine D L := hDAE'.bca.off_line hA_L hE_L
  /- Every point of AE but A makes a right angle with AD: on E's ray the angle
     is unchanged; beyond A its adjacent angle is right (System E, Diagram-angle 3). -/
  have hright : ∀ {P : Point}, OnLine P L → P ≠ A → ∠ D A P = ∟ := by
    intro P hP_L hPA
    by_cases hb : Between P A E
    · have hEAD : ∠ E A D = ∟ := by
        rw [angle_symm hDAE'.ne₂₃.symm hDAE'.ne₁₂]; exact hDAE
      rw [← adjacent_eq_of_right hE_L hP_L (between_symm hb) hD_L hEAD, hEAD]
    · rw [angle_onRay_right ⟨hDAE'.ne₂₃, hPA, ⟨L, hA_L, hE_L, hP_L⟩, hb⟩ hDAE'.ne₁₂]
      exact hDAE
  -- I say that the straight line drawn from A at right angles to AB from its extremity will
  -- fall outside the circle.
  refine ⟨fun P hP hPA => ?_, fun F hF => ?_⟩
  · have hP_L : OnLine P L := by
      obtain ⟨M, h1, h2, h3⟩ := hP
      exact (line_unique hDAE'.ne₂₃ h1 h2 hA_L hE_L) ▸ h3
    -- For suppose it does not, but, if possible, let it fall within as CA, and let DC be joined.
    have key : ∀ C : Point, OnLine C L → C ≠ A → ¬ OnCircle C ABC := by
      intro C hC_L hCA hC
      have hACD : Triangle A C D := Triangle.of_line hA_L hC_L hCA.symm hD_L
      -- Since DA is equal to DC,
      have hDADC : ‖D A‖ = ‖D C‖ := Definition15 hD hA hC
      -- the angle DAC is also equal to the angle ACD. [I. 5]
      have h5 : ∠ D A C = ∠ A C D := by
        rw [BookI.Prop5.base hACD.cab hDADC]; exact angle_symm hACD.ne₂₃.symm hACD.ne₁₂
      -- But the angle DAC is right;
      have hDAC : ∠ D A C = ∟ := hright hC_L hCA
      -- therefore the angle ACD is also right:
      have hACD' : ∠ A C D = ∟ := h5 ▸ hDAC
      -- thus, in the triangle ACD, the two angles DAC, ACD are equal to two right angles; which is
      -- impossible. [I. 17]
      have h17 := (BookI.Prop17 hACD).2.2
      rw [hDAC, hACD'] at h17
      exact lt_irrefl _ h17
    -- Therefore the straight line drawn from the point A at right angles to BA will not fall
    -- within the circle.
    have hin : ¬ InsideCircle P ABC := by
      intro hin
      obtain ⟨C, hC, hC_L, hCPA⟩ := line_circle_beyond hin hP_L hA_L hPA.symm
      exact key C hC_L (ne_of_between_ends hCPA) hC
    -- Similarly we can prove that neither will it fall on the circumference;
    have hon : ¬ OnCircle P ABC := key P hP_L hPA
    -- therefore it will fall outside.
    exact ⟨hin, hon⟩
  -- Let it fall as AE;
  -- I say next that into the space between the straight line AE and the circumference CHA
  -- another straight line cannot be interposed.
  -- For, if possible, let another straight line be so interposed, as FA, and let DG be drawn
  -- from the point D perpendicular to FA.
  · refine Classical.byContradiction fun hFA => ?_
    have hAF : A ≠ F := by
      rintro rfl
      exact hF ⟨L, hA_L, hE_L, hA_L⟩
    /- If AF passes through the centre, D itself is already within the circle. -/
    have hDF : ¬ Collinear A F D := fun h => hFA ⟨D, h, centre_inside hD⟩
    /- Heath gives no bracket for drawing this perpendicular: it is I.12. -/
    obtain ⟨G, hG, hDG⟩ := BookI.Prop12 hAF hDF
    have hDAF : Triangle D A F := fun ⟨M, h1, h2, h3⟩ => hDF ⟨M, h2, h3, h1⟩
    /- Were G to be A, AF would be at right angles to AD at A, as AE is; but at A only
       one straight line is at right angles to AD, as in III.1 (`Prop1.perpendicular`). -/
    have hGA : G ≠ A := by
      rintro rfl
      obtain ⟨M, h1, h2⟩ := Postulate1 G F hAF
      exact hF (Prop1.perpendicular hDAE' hDAF hDAE (hDG F ⟨M, h1, h2, h2⟩ hAF.symm))
    obtain ⟨M, hA_M, hF_M, hG_M⟩ := hG
    have hD_M : ¬ OnLine D M := fun hD => hDF ⟨M, hA_M, hF_M, hD⟩
    have hDGA : Triangle D G A := (Triangle.of_line hG_M hA_M hGA hD_M).bca.bca
    -- Then, since the angle AGD is right,
    have hDGA' : ∠ D G A = ∟ := hDG A ⟨M, hA_M, hF_M, hA_M⟩ hGA.symm
    -- and the angle DAG is less than a right angle,
    have h17 := (BookI.Prop17 hDGA).1
    rw [hDGA'] at h17
    have hGAD : ∠ G A D < ∟ := Magnitude.lt_of_add_lt_add_left h17
    -- AD is greater than DG. [I. 19]
    have h19 : ‖D G‖ < ‖D A‖ := BookI.Prop19 hDGA (hDGA' ▸ hGAD)
    -- But DA is equal to DH;
    /- DA itself is a radius, equal to DH by Definition I.15. Comparing DG with DA
       therefore puts G within the circle, contradicting the supposed interposition. -/
    -- therefore DH is greater than DG, the less than the greater: which is impossible.
    exact hFA ⟨G, ⟨M, hA_M, hF_M, hG_M⟩, inside_of_len_lt hD hA h19⟩
  -- Therefore another straight line cannot be interposed into the space between the straight
  -- line and the circumference.
  /- Our angles are made by two straight lines, so the angle of the semicircle and the
     horn-like angle are left to Euclid's words below, with no Lean beneath them. What
     he proves them by, that every other straight line through A cuts the circle, is
     the second part above. -/
  -- I say further that the angle of the semicircle contained by the straight line BA and the
  -- circumference CHA is greater than any acute rectilineal angle,
  -- and the remaining angle contained by the circumference CHA and the straight line AE is
  -- less than any acute rectilineal angle.
  -- For, if there is any rectilineal angle greater than the angle contained by the straight
  -- line BA and the circumference CHA, and any rectilineal angle less than the angle contained
  -- by the circumference CHA and the straight line AE, then into the space between the
  -- circumference and the straight line AE a straight line will be interposed such as will
  -- make an angle contained by straight lines which is greater than the angle contained by the
  -- straight line BA and the circumference CHA, and another angle contained by straight lines
  -- which is less than the angle contained by the circumference CHA and the straight line AE.
  -- But such a straight line cannot be interposed;
  -- therefore there will not be any acute angle contained by straight lines which is greater
  -- than the angle contained by the straight line BA and the circumference CHA, nor yet any
  -- acute angle contained by straight lines which is less than the angle contained by the
  -- circumference CHA and the straight line AE.—
  /- The Porism is proved below, as `Prop16.porism`. -/
  -- PORISM. From this it is manifest that the straight line drawn at right angles to the
  -- diameter of a circle from its extremity touches the circle.
  -- Q. E. D.

/-- The Porism to III.16: "the straight line drawn at right angles to the diameter of a
circle from its extremity touches the circle." The diameter through A is the
straight line AD, D the centre, and AE is drawn at right angles to it. III.17,
III.33 and III.37 cite it, and Book IV after them. -/
theorem Prop16.porism {A D E : Point} {ABC : Circle} (hD : Centre D ABC) (hA : OnCircle A ABC)
    (hE : ¬ Collinear D A E) (hDAE : ∠ D A E = ∟) :
    Touches A E ABC := by
  have hDAE' : Triangle D A E := hE
  obtain ⟨B, hADB⟩ := produce hDAE'.ne₁₂.symm
  have hBAE : ∠ B A E = ∟ := by
    rw [← angle_onRay_left (OnRay.of_between hADB) hDAE'.ne₂₃.symm]; exact hDAE
  have hABE : ¬ Collinear A B E := by
    obtain ⟨L, hA_L, hD_L⟩ := Postulate1 A D hDAE'.ne₁₂.symm
    have hB_L : OnLine B L := on_line_of_between hADB hA_L hD_L
    exact Triangle.of_line hA_L hB_L (ne_of_between_ends hADB) (hDAE'.bac.off_line hA_L hD_L)
  have h := (Prop16 hD hA hADB hABE hBAE).1
  refine ⟨hDAE'.ne₂₃, fun L hA_L hE_L => ⟨⟨A, hA_L, hA⟩, ?_⟩⟩
  rintro ⟨X, Y, hXY, hX_L, hX, hY_L, hY⟩
  by_cases hXA : X = A
  · subst hXA
    exact (h Y ⟨L, hX_L, hE_L, hY_L⟩ (Ne.symm hXY)).2 hY
  · exact (h X ⟨L, hA_L, hE_L, hX_L⟩ hXA).2 hX

end Elements.BookIII
