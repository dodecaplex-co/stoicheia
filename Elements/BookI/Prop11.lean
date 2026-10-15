import Elements.Figure.Basics
import Elements.BookI.Prop01
import Elements.BookI.Prop03
import Elements.BookI.Prop08

/-!
# Book I, Proposition 11

Euclid's text, in Heath's translation: [`heath/I/11.md`](../../heath/I/11.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

"At right angles to AB" is said here of every point `P` of the straight line
`AB` other than `C`: the angle `PCF` is right, whichever way along `AB` from `C`
the point `P` lies. And the perpendicular is put on the side of `AB` where a
given point `Q` is, as I.46 and I.48 will need; I.1 lets the equilateral
triangle be built on that side.
-/

namespace Elements.BookI

open Tacit

/-! ## What Euclid reads off the figure -/

/-- Room to cut off `CE`. I.3 cuts a straight line off from a *greater* one, and
nothing says that `CB` is greater than `CD`; Postulate 2 produces a straight line
but says nothing of how far. So: with centre `C` and distance `CD` describe a
circle (Post. 3); the straight line `DC`, produced beyond the centre, cuts it
again at some `X` (System E, Intersections 5); and `CX` produced (Post. 2) is
greater than `CX`, that is, than `CD`. -/
theorem Prop11.produced {C D : Point} (hDC : D ≠ C) :
    ∃ G : Point, Between D C G ∧ ‖C D‖ < ‖C G‖ := by
  obtain ⟨L, hC, hD⟩ := Postulate1 C D hDC.symm
  obtain ⟨α, hCα, hDα⟩ := Postulate3 C D hDC.symm
  obtain ⟨X, hXα, -, hXCD⟩ := line_circle_beyond (centre_inside hCα) hC hD hDC
  obtain ⟨G, hCXG⟩ := produce (ne_of_between hXCD).symm
  refine ⟨G, between_of_between_right (between_symm hXCD) hCXG, ?_⟩
  rw [Definition15 hCα hDα hXα]
  exact len_lt_of_between hCXG

/-- The two halves of a straight line. If `C` lies between `D` and `E`, every
other point `P` of the straight line `DE` lies on the ray from `C` through `D` or
on the ray from `C` through `E`: either `C` is not between `P` and `D`, or it is,
and then it cannot also be between `P` and `E` (System E, Between 7). -/
theorem Prop11.either_ray {C D E P : Point} {L : Line} (hDCE : Between D C E)
    (hD : OnLine D L) (hC : OnLine C L) (hP : OnLine P L) (hPC : P ≠ C) :
    OnRay P C D ∨ OnRay P C E := by
  by_cases h : Between P C D
  · have hE : OnLine E L := on_line_of_between hDCE hD hC
    exact Or.inr ⟨(ne_of_between (between_symm hDCE)).symm, hPC, ⟨L, hC, hE, hP⟩,
      fun h' => not_between_of_between_between h h' hDCE⟩
  · exact Or.inl ⟨(ne_of_between hDCE).symm, hPC, ⟨L, hC, hD, hP⟩, h⟩

/-- To draw a straight line at right angles to a given straight line from a given point on it. -/
theorem Prop11 {A B C Q : Point} (hAB : A ≠ B) (hC : Collinear A B C) (hQ : ¬ Collinear A B Q) :
    ∃ F : Point, SameSideOf F Q A B ∧ ∀ P : Point, Collinear A B P → P ≠ C → ∠ P C F = ∟ := by
  -- Let AB be the given straight line, and C the given point on it.
  /- Lean needs the straight line AB by name (Post. 1), with C on it and Q off it. -/
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  have on_AB : ∀ {P : Point}, Collinear A B P → OnLine P AB := by
    rintro P ⟨M, hA_M, hB_M, hP_M⟩
    rw [line_unique hAB hA_AB hB_AB hA_M hB_M]
    exact hP_M
  have hC_AB : OnLine C AB := on_AB hC
  have hQ_AB : ¬ OnLine Q AB := fun h => hQ ⟨AB, hA_AB, hB_AB, h⟩
  -- Thus it is required to draw from the point C a straight line at right angles to the
  -- straight line AB.
  -- Let a point D be taken at random on AC;
  /- Euclid's figure has C between A and B. In Lean C may be any point of the
     straight line AB, even A itself, and then there is no AC to take D on: B
     will do. All the proof needs is a point D of AB other than C (System E,
     Points 3). -/
  obtain ⟨D, hD_AB, hDC⟩ : ∃ D : Point, OnLine D AB ∧ D ≠ C := by
    by_cases hCA : C = A
    · exact ⟨B, hB_AB, by rw [hCA]; exact hAB.symm⟩
    · obtain ⟨D, hD_AB, hADC, -⟩ := exists_point_between hA_AB hC_AB (Ne.symm hCA) []
      exact ⟨D, hD_AB, (ne_of_between (between_symm hADC)).symm⟩
  -- let CE be made equal to CD; [I. 3]
  /- CE is cut off from DC produced beyond C, far enough for I.3 to have a
     greater straight line to cut it from (`Prop11.produced`). So C lies between
     D and E: the figure's D, C, E in a row. -/
  obtain ⟨G, hDCG, hCD_CG⟩ := Prop11.produced hDC
  obtain ⟨E, hCEG, hCE_CD⟩ := Prop3 hDC.symm hCD_CG
  have hDCE : Between D C E := between_symm (between_inner (between_symm hCEG) (between_symm hDCG))
  have hE_AB : OnLine E AB := on_line_of_between hDCE hD_AB hC_AB
  have hDE : D ≠ E := ne_of_between_ends hDCE
  have hEC : E ≠ C := ne_of_between (between_symm hDCE)
  -- on DE let the equilateral triangle FDE be constructed, [I. 1]
  /- On Q's side of DE, which is Q's side of AB: one straight line passes
     through D and E. -/
  obtain ⟨F, ⟨-, hDE_EF, hEF_FD⟩, hFQ⟩ := Prop1 D E hDE Q
  have hF_Q : SameSide F Q AB :=
    (hFQ (Triangle.of_line hD_AB hE_AB hDE hQ_AB)).sameSide hD_AB hE_AB
  have hF_AB : ¬ OnLine F AB := not_on_line_of_same_side hF_Q
  -- and let FC be joined;
  have hFC : F ≠ C := fun h => hF_AB (h ▸ hC_AB)
  obtain ⟨FC, -, -⟩ := Postulate1 F C hFC
  -- I say that the straight line FC has been drawn at right angles to the given straight line
  -- AB from C the given point on it.
  -- For, since DC is equal to CE,
  have hDC_CE : ‖D C‖ = ‖C E‖ := (len_symm D C).trans hCE_CD.symm
  -- and CF is common,
  have hCF : ‖C F‖ = ‖C F‖ := rfl
  -- the two sides DC, CF are equal to the two sides EC, CF respectively;
  have hCD_CE : ‖C D‖ = ‖C E‖ := (len_symm C D).trans hDC_CE
  -- and the base DF is equal to the base FE;
  have hDF_EF : ‖D F‖ = ‖E F‖ := (len_symm D F).trans (hEF_FD.symm)
  -- therefore the angle DCF is equal to the angle ECF; [I. 8]
  have hCDF : Triangle C D F := Triangle.of_line hC_AB hD_AB hDC.symm hF_AB
  have hCEF : Triangle C E F := Triangle.of_line hC_AB hE_AB hEC.symm hF_AB
  have hDCF_ECF : ∠ D C F = ∠ E C F := Prop8 hCDF hCEF hCD_CE hCF hDF_EF
  -- and they are adjacent angles.
  /- Adjacent: C lies between D and E, and F is off the straight line DE. -/
  have hDCF_FCE : ∠ D C F = ∠ F C E := hDCF_ECF.trans (angle_symm hEC hFC)
  -- But, when a straight line set up on a straight line makes the adjacent angles equal to one
  -- another, each of the equal angles is right; [Def. 10]
  /- Definition 10 says what a right angle is, and Postulate 4 that every right
     angle is the right angle `∟`. -/
  have hDCF_right : IsRightAngle D C F := ⟨E, hDCE, hCDF.bac, hDCF_FCE⟩
  have hECF_right : IsRightAngle E C F :=
    ⟨D, between_symm hDCE, hCEF.bac, hDCF_ECF.symm.trans (angle_symm hDC hFC)⟩
  -- therefore each of the angles DCF, FCE is right.
  have hDCF : ∠ D C F = ∟ := Postulate4 hDCF_right
  have hFCE : ∠ F C E = ∟ := (angle_symm hFC hEC).trans (Postulate4 hECF_right)
  -- Therefore the straight line CF has been drawn at right angles to the given straight line
  -- AB from the given point C on it.
  /- Every other point P of AB lies on the ray from C through D, or on the ray
     from C through E (`Prop11.either_ray`), and the angle PCF is the angle DCF
     or the angle ECF (`angle_onRay_left` in Book Zero). -/
  refine ⟨F, SameSideOf.of_line hAB hA_AB hB_AB hF_Q, fun P hP hPC => ?_⟩
  rcases Prop11.either_ray hDCE hD_AB hC_AB (on_AB hP) hPC with hPD | hPE
  · rw [angle_onRay_left hPD hFC]
    exact hDCF
  · rw [angle_onRay_left hPE hFC, angle_symm hEC hFC]
    exact hFCE
  -- Q. E. F.

end Elements.BookI
