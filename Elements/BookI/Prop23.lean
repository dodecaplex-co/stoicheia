import Elements.Figure.Basics
import Elements.BookI.Prop08
import Elements.BookI.Prop20
import Elements.BookI.Prop22

/-!
# Book I, Proposition 23

Euclid's text, in Heath's translation: [`heath/I/23.md`](../../heath/I/23.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

The angle is constructed on the ray from A through B (the point G is on it, as
in Heath's figure) and on the side of AB where the given point P is (the point F
is there), so that later propositions can place it: I.24 on the side where its
own F lies, I.31 on the side away from C.

I.22 builds the triangle AFG with its corner at A and AG along AB, from
lengths `A₁A₂ := CD`, `B₁B₂ := CE`, `C₁C₂ := DE`, in the order of Euclid's
sentence (so its G is our G, and its K our F). It asks that two of these taken
together be greater than the third; they are the sides of the triangle DCE, so
that is I.20, as Heath's reference in I.22's enunciation says.
-/

namespace Elements.BookI

open Tacit

/-- On a given straight line and at a point on it to construct a rectilineal angle equal to a given
rectilineal angle. -/
theorem Prop23 {A B C D E P : Point} (hAB : A ≠ B) (hDCE : Triangle D C E) (hP : ¬ Collinear A B P) :
    ∃ F G : Point, OnRay G A B ∧ SameSideOf F P A B ∧ ∠ F A G = ∠ D C E := by
  -- Let AB be the given straight line, A the point on it, and the angle DCE the given
  -- rectilineal angle;
  /- The given angle comes as the triangle DCE: its arms CD, CE are two straight
     lines through C, not one, so it is a true rectilineal angle. We shall need the
     straight line AB itself, to see that the angle we build is not flat either. -/
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  -- thus it is required to construct on the given straight line AB, and at the point A on it,
  -- a rectilineal angle equal to the given rectilineal angle DCE.
  /- We build the angle on the ray from A through B, and on the side of AB where P
     is, so that later propositions can place it where they need it (I.24, I.31, I.42
     and I.44, and Book III after them). -/
  -- On the straight lines CD, CE respectively let the points D, E be taken at random;
  /- The statement already names a point on each arm, D on CD and E on CE, so we
     take those. Any others would do as well: an angle depends only on its two rays
     (`angle_eq_of_onRay` in Book Zero). -/
  -- let DE be joined,
  /- Our proof uses only the points D and E; the straight line DE is drawn in the
     figure, for the eye. Joined, it closes the triangle DCE, whose three sides are
     the three straight lines that I.22 is about to take. -/
  -- and out of three straight lines which are equal to the three straight lines CD, DE, CE let
  -- the triangle AFG be constructed in such a way that CD is equal to AF, CE to AG, and
  -- further DE to FG. [I. 22]
  /- I.22 asks that two of the three taken together in any manner be greater than the
     remaining one, and Heath's reference there is I.20. The three are the sides of the
     triangle DCE, so I.20, applied to it named from C, says just that, once each sum
     is read in I.22's order. -/
  obtain ⟨hDE_lt, hCE_lt, hCD_lt⟩ := Prop20 hDCE.bac
  have h₁ : ‖D E‖ < ‖C D‖ + ‖C E‖ := by
    rw [← len_symm D C]
    exact hDE_lt
  have h₂ : ‖C E‖ < ‖C D‖ + ‖D E‖ := hCE_lt
  have h₃ : ‖C D‖ < ‖C E‖ + ‖D E‖ := by
    rw [add_comm, len_symm C E]
    exact hCD_lt
  /- I.22 puts the corner of its triangle at A, the side AG along the ray from A
     through B, and the third corner F on P's side of AB. Its lengths, in its own
     order and Euclid's, are CD, CE and DE. Heath notes that Euclid asks more of
     I.22 here than I.22, as Euclid gives it, provides: a triangle placed on a given
     straight line at a given point (vol. 1, p. 295). Our I.22 is stated so as to
     provide it. -/
  obtain ⟨G, F, hG, hF, hFA_CD, hAG_CE, hGF_DE⟩ :=
    Prop22 (A₁ := C) (A₂ := D) (B₁ := C) (B₂ := E) (C₁ := D) (C₂ := E) h₁ h₂ h₃ hAB hP
  /- Euclid calls AFG a triangle, and I.8 will need it to be one. G is on the
     straight line AB (a point of the ray from A through B, so not A itself), and F,
     being on one side of AB, is off it (`OnRay.onLine`, `SameSideOf.triangle`,
     `Triangle.off_line`, `Triangle.of_line` in Book Zero). -/
  have hG_AB : OnLine G AB := hG.onLine hA_AB hB_AB
  have hA_G : A ≠ G := hG.2.1.symm
  have hF_AB : ¬ OnLine F AB := hF.triangle.off_line hA_AB hB_AB
  have hAFG : Triangle A F G := (Triangle.of_line hA_AB hG_AB hA_G hF_AB).acb
  -- Then, since the two sides DC, CE are equal to the two sides FA, AG respectively,
  have hCD_AF : ‖C D‖ = ‖A F‖ := hFA_CD.symm.trans (len_symm F A)
  have hCE_AG : ‖C E‖ = ‖A G‖ := hAG_CE.symm
  -- and the base DE is equal to the base FG,
  have hDE_FG : ‖D E‖ = ‖F G‖ := hGF_DE.symm.trans (len_symm G F)
  -- the angle DCE is equal to the angle FAG. [I. 8]
  have hDCE_FAG : ∠ D C E = ∠ F A G := Prop8 hDCE.bac hAFG hCD_AF hCE_AG hDE_FG
  -- Therefore on the given straight line AB, and at the point A on it, the rectilineal angle
  -- FAG has been constructed equal to the given rectilineal angle DCE.
  exact ⟨F, G, hG, hF, hDCE_FAG.symm⟩
  -- Q. E. F.

end Elements.BookI
