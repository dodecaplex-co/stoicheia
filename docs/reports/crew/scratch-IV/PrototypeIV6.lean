import Elements

/-!
# Book IV, scratch: the prototype of a figure inscribed in a circle (IV.6)

Brief 0012, section 9. The foundation under test is a figure given by its corners in
order (`Polygon`) and Definition IV.3 (`Polygon.InscribedIn`); the hard part every
inscribing proof meets is proving `Polygon` for the figure it builds, which
`Prop6.polygon_of_cross` does for four corners whose diagonals cross. Until brief 0008's
rule lands, the centre is a hypothesis (`hABCD`). Proved by a Codex sailor (OpenAI's
Codex, at its highest reasoning setting) on 19 October 2026, at `89c5da4`; nothing builds
this file, and `lake env lean` checks it.
-/

namespace Elements

/-! ## A figure given by its corners -/

/-- **The sides of a figure** given by its corners in order: each corner with the next,
and the last with the first. The sides of `[A, B, C, D]` are AB, BC, CD and DA. -/
def Polygon.sides (ps : List Point) : List (Point × Point) :=
  segments (ps ++ ps.take 1)

/-- **Each corner with its neighbours**: each corner of the figure with the next two, the
last corners wrapping round to the first. The triples of `[A, B, C, D]` are ABC, BCD, CDA
and DAB: the middle corner of each is a corner of the figure, between its two neighbours;
the first two are the ends of a side, and the third is the next corner. -/
def Polygon.cornerTriples (ps : List Point) : List (Point × Point × Point) :=
  triples (ps ++ ps.take 2)

/-- **A rectilineal figure**, given by its corners in order (Definition I.19's figure
"contained by straight lines", as Book IV uses it): at least three corners, no two the
same, and, for each side, every other corner on one and the same side of it. So the figure
is convex, its sides meet only at their ends, and no three corners in a row are on one
straight line. Every figure of Book IV is one; `Polygon [A, B, C]` says that ABC is a
triangle. -/
def Polygon (ps : List Point) : Prop :=
  (∃ A B C : Point, ∃ rest : List Point, ps = A :: B :: C :: rest) ∧ ps.Nodup ∧
    ∀ s ∈ Polygon.sides ps, ∀ P ∈ ps, ∀ Q ∈ ps,
      P ≠ s.1 → P ≠ s.2 → Q ≠ s.1 → Q ≠ s.2 → SameSideOf P Q s.1 s.2

/-- **Magnitudes all equal**: any two of the list are equal. -/
def AllEqual {k : Kind} (xs : List (Magnitude k)) : Prop :=
  ∀ a ∈ xs, ∀ b ∈ xs, a = b

/-- **The figure is equilateral**: its sides are all equal. -/
def Polygon.Equilateral (ps : List Point) : Prop :=
  AllEqual ((Polygon.sides ps).map fun s => len s.1 s.2)

/-- **The figure is equiangular**: its angles are all equal, the angle at each corner being
the one its two sides there contain. -/
def Polygon.Equiangular (ps : List Point) : Prop :=
  AllEqual ((Polygon.cornerTriples ps).map fun t => ∠ t.1 t.2.1 t.2.2)

/-! ## The Definitions of Book IV -/

/-- **Definition IV.3.** "A rectilineal figure is said to be inscribed in a circle when each
angle of the inscribed figure lies on the circumference of the circle": each corner of the
figure is on the circle. -/
def Polygon.InscribedIn (ps : List Point) (α : Circle) : Prop :=
  ∀ P ∈ ps, OnCircle P α

/-- **Definition IV.4.** "A rectilineal figure is said to be circumscribed about a circle,
when each side of the circumscribed figure touches the circumference of the circle": each
side, produced, touches the circle (Definition III.2, `Touches`), and the point of contact
is on the side itself, between its ends. -/
def Polygon.CircumscribedAbout (ps : List Point) (α : Circle) : Prop :=
  ∀ s ∈ Polygon.sides ps, Touches s.1 s.2 α ∧ ∃ T : Point, Between s.1 T s.2 ∧ OnCircle T α

/-- **Definition IV.5.** "A circle is said to be inscribed in a figure when the circumference
of the circle touches each side of the figure in which it is inscribed": Definition IV.4,
read from the circle. -/
def Circle.InscribedIn (α : Circle) (ps : List Point) : Prop :=
  Polygon.CircumscribedAbout ps α

/-- **Definition IV.6.** "A circle is said to be circumscribed about a figure when the
circumference of the circle passes through each angle of the figure about which it is
circumscribed": Definition IV.3, read from the circle. -/
def Circle.CircumscribedAbout (α : Circle) (ps : List Point) : Prop :=
  Polygon.InscribedIn ps α

/-! ## The circumferences a figure inscribed in a circle cuts off -/

/-- **The circumferences cut off by the sides** of a figure inscribed in the circle `α`, one
for each side, in order: the circumference on the far side of the side from the figure,
named as Definition III.9 names it, by the angle that stands on it at the next corner
(`standing α P R Q`, for the side PQ and the next corner R). For a figure inscribed in `α`
they make up the whole circle (the bridge `Polygon.arcs_sum` of brief 0012). -/
noncomputable def Polygon.arcs (ps : List Point) (α : Circle) : List Angle :=
  (Polygon.cornerTriples ps).map fun t => standing α t.1 t.2.2 t.2.1

end Elements

namespace Scratch.BookIV

open Elements Elements.Tacit

/-- Euclid takes for granted that a straight line through the centre meets the circle
in both directions. The first end lies on the given ray, and the centre lies between
the two ends (System E, Intersections 5). -/
theorem Prop6.diameter_on_ray {α : Circle} {E F : Point} (hE : Centre E α)
    (hEF : E ≠ F) :
    ∃ B D : Point, OnCircle B α ∧ OnCircle D α ∧ Between B E D ∧ OnRay B E F := by
  obtain ⟨L, hE_L, hF_L⟩ := Postulate1 E F hEF
  obtain ⟨D, hD, hD_L, hDEF⟩ :=
    line_circle_beyond (centre_inside hE) hE_L hF_L hEF.symm
  obtain ⟨B, hB, -, hBED⟩ :=
    line_circle_beyond (centre_inside hE) hE_L hD_L (ne_of_between hDEF)
  exact ⟨B, D, hB, hD, hBED,
    OnRay.of_between_between hDEF (between_symm hBED)⟩

/-- Euclid reads all four angles at the crossing as right. Across a straight line,
the angle adjacent to a right angle is equal to it (System E, Diagram-angle 3). -/
theorem Prop6.adjacent_right {A B D E : Point} (hEBA : Triangle E B A)
    (hBED : Between B E D) (hBEA : ∠ B E A = ∟) : ∠ A E D = ∟ := by
  obtain ⟨L, hB_L, hD_L⟩ := Postulate1 B D (ne_of_between_ends hBED)
  have hE_L := on_line_of_between_ends hBED hB_L hD_L
  exact (adjacent_eq_of_right hB_L hD_L hBED
    (hEBA.off_line hE_L hB_L) hBEA).symm.trans hBEA

/-- Euclid takes the order of the four corners from the crossing diameters. Book Zero's
`SameSideOf.of_cross`, read from each corner, puts the other two corners on one side of
each side. The finite list then records precisely those four conditions. -/
theorem Prop6.polygon_of_cross {A B C D E : Point} (hAEC : Between A E C)
    (hBED : Between B E D) (hABC : Triangle A B C) : Polygon [A, B, C, D] := by
  have hCD := SameSideOf.of_cross hAEC hBED hABC
  have hBC := SameSideOf.of_cross (between_symm hBED) hAEC hCD.symm.triangle.cab
  have hAB := SameSideOf.of_cross (between_symm hAEC) (between_symm hBED)
    hBC.symm.triangle.cab
  have hDA := SameSideOf.of_cross hBED (between_symm hAEC) hAB.symm.triangle.cab
  refine ⟨⟨A, B, C, [D], rfl⟩, ?_, ?_⟩
  · simp [hABC.ne₁₂, hABC.ne₁₃, hCD.symm.triangle.ne₁₃, hABC.ne₂₃,
      ne_of_between_ends hBED, hAB.1]
  · intro s hs P hP Q hQ hP₁ hP₂ hQ₁ hQ₂
    have hCC := hCD.trans hCD.symm
    have hDD := hCD.symm.trans hCD
    have hBB := hBC.trans hBC.symm
    have hCC' := hBC.symm.trans hBC
    have hAA := hAB.trans hAB.symm
    have hBB' := hAB.symm.trans hAB
    have hDD' := hDA.trans hDA.symm
    have hAA' := hDA.symm.trans hDA
    change s ∈ [(A, B), (B, C), (C, D), (D, A)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP hQ
    rcases hs with rfl | rfl | rfl | rfl <;>
      rcases hP with rfl | rfl | rfl | rfl <;>
      rcases hQ with rfl | rfl | rfl | rfl <;>
      simp_all only [ne_eq, not_true_eq_false]
    · exact hCD.symm
    · exact hDA.symm
    · exact hAB.symm
    · exact hBC.symm

/-- In a given circle to inscribe a square. -/
theorem Prop6 (ABCD : Circle) (hABCD : ∃ O : Point, Centre O ABCD) :
    ∃ A B C D : Point, Polygon [A, B, C, D] ∧ Polygon.InscribedIn [A, B, C, D] ABCD ∧
      Square A B C D := by
  -- Let ABCD be the given circle;
  obtain ⟨E, hE⟩ := hABCD
  -- thus it is required to inscribe a square in the circle ABCD.
  -- Let two diameters AC, BD of the circle ABCD be drawn at right angles to one another, and let AB, BC, CD, DA be joined.
  /- Take A on the circle and produce AE through its centre to C. I.11 draws EF
     perpendicular to AC; the two intersections on EF give B and D. -/
  obtain ⟨A, hA, -⟩ := exists_point_on_circle ABCD []
  have hAE := ne_of_centre_of_on hE hA
  obtain ⟨L, hA_L, hE_L⟩ := Postulate1 A E hAE
  obtain ⟨C, hC, hC_L, hCEA⟩ := line_circle_beyond (centre_inside hE) hE_L hA_L hAE
  have hAEC := between_symm hCEA
  have hAC := ne_of_between_ends hAEC
  obtain ⟨Q, hACQ, -⟩ := exists_off_line hAC []
  obtain ⟨F, hFQ, hperp⟩ := BookI.Prop11 hAC ⟨L, hA_L, hC_L, hE_L⟩ hACQ
  have hF_L := hFQ.triangle.off_line hA_L hC_L
  have hFE : F ≠ E := fun h => hF_L (h ▸ hE_L)
  obtain ⟨B, D, hB, hD, hBED, hBF⟩ := Prop6.diameter_on_ray hE hFE.symm
  obtain ⟨M, hE_M, hF_M⟩ := Postulate1 E F hFE.symm
  have hB_M := hBF.onLine hE_M hF_M
  have hD_M := on_line_of_between hBED hB_M hE_M
  have hBE := ne_of_between hBED
  have hDE := ne_of_between (between_symm hBED)
  have hCE := ne_of_between hCEA
  have hB_L : ¬ OnLine B L := fun h =>
    hF_L (line_unique hBE.symm hE_M hB_M hE_L h ▸ hF_M)
  have hD_L : ¬ OnLine D L := fun h =>
    hF_L (line_unique hDE.symm hE_M hD_M hE_L h ▸ hF_M)
  have hEAB := Triangle.of_line hE_L hA_L hAE.symm hB_L
  have hEAD := Triangle.of_line hE_L hA_L hAE.symm hD_L
  have hECB := Triangle.of_line hE_L hC_L hCE.symm hB_L
  have hECD := Triangle.of_line hE_L hC_L hCE.symm hD_L
  have hABC := (Triangle.of_line hA_L hC_L hAC hB_L).acb
  have hAB := hEAB.ne₂₃
  have hAD := hEAD.ne₂₃
  have hBC := hECB.ne₂₃.symm
  have hCD := hECD.ne₂₃
  /- Joining the successive corners gives a rectilineal figure: its diameters cross
     at E, and no two corners coincide. -/
  have hpolygon := Prop6.polygon_of_cross hAEC hBED hABC
  have hAEB : ∠ A E B = ∟ :=
    (angle_onRay_right hBF hAE).trans (hperp A ⟨L, hA_L, hC_L, hA_L⟩ hAE)
  have hCEB : ∠ C E B = ∟ :=
    (angle_onRay_right hBF hCE).trans (hperp C ⟨L, hA_L, hC_L, hC_L⟩ hCE)
  have hBEA : ∠ B E A = ∟ := (angle_symm hBE hAE).trans hAEB
  have hBEC : ∠ B E C = ∟ := (angle_symm hBE hCE).trans hCEB
  have hAED := Prop6.adjacent_right hEAB.acb hBED hBEA
  have hCED := Prop6.adjacent_right hECB.acb hBED hBEC
  -- Then, since BE is equal to ED, for E is the centre,
  have hEB_ED : len E B = len E D := Definition15 hE hB hD
  -- and EA is common and at right angles,
  have hEA : len E A = len E A := rfl
  have hAEB_AED : ∠ A E B = ∠ A E D := hAEB.trans hAED.symm
  -- therefore the base AB is equal to the base AD. [I. 4]
  have hAB_AD : len A B = len A D :=
    (BookI.Prop4 hEAB hEAD hEA hEB_ED hAEB_AED).1
  -- For the same reason
  -- each of the straight lines BC, CD is also equal to each of the straight lines AB, AD;
  have hEA_EC : len E A = len E C := Definition15 hE hA hC
  have hAB_CB : len A B = len C B :=
    (BookI.Prop4 hEAB hECB hEA_EC rfl (hAEB.trans hCEB.symm)).1
  have hCB_CD : len C B = len C D :=
    (BookI.Prop4 hECB hECD rfl hEB_ED (hCEB.trans hCED.symm)).1
  have hAB_BC : len A B = len B C := hAB_CB.trans (len_symm C B)
  have hBC_CD : len B C = len C D := (len_symm B C).trans hCB_CD
  have hCD_DA : len C D = len D A :=
    hCB_CD.symm.trans (hAB_CB.symm.trans (hAB_AD.trans (len_symm A D)))
  -- therefore the quadrilateral ABCD is equilateral.
  have hequilateral : len A B = len B C ∧ len B C = len C D ∧ len C D = len D A :=
    ⟨hAB_BC, hBC_CD, hCD_DA⟩
  -- I say next that it is also right-angled.
  -- For, since the straight line BD is a diameter of the circle ABCD,
  -- therefore BAD is a semicircle;
  /- B and D are on the circle, E lies between them, and A is a third point of
     the circle. These are the semicircle hypotheses of III.31. -/
  -- therefore the angle BAD is right. [III. 31]
  have hBAD : ∠ B A D = ∟ := (BookIII.Prop31 hE hA hB hD hBED hAB hAD).1
  -- For the same reason
  -- each of the angles ABC, BCD, CDA is also right;
  have hABC_right : ∠ A B C = ∟ :=
    (BookIII.Prop31 hE hB hA hC hAEC hAB.symm hBC).1
  have hBCD_right : ∠ B C D = ∟ :=
    (BookIII.Prop31 hE hC hB hD hBED hBC.symm hCD).1
  have hCDA_right : ∠ C D A = ∟ :=
    (BookIII.Prop31 hE hD hC hA hCEA hCD.symm hAD.symm).1
  -- therefore the quadrilateral ABCD is right-angled.
  have hright : ∠ D A B = ∟ ∧ ∠ A B C = ∟ ∧ ∠ B C D = ∟ ∧ ∠ C D A = ∟ :=
    ⟨(angle_symm hAD.symm hAB.symm).trans hBAD, hABC_right, hBCD_right, hCDA_right⟩
  -- But it was also proved equilateral;
  -- therefore it is a square; [I. Def. 22]
  have hsquare : Square A B C D :=
    ⟨hequilateral.1, hequilateral.2.1, hequilateral.2.2, hright⟩
  -- and it has been inscribed in the circle ABCD.
  have hinscribed : Polygon.InscribedIn [A, B, C, D] ABCD := by
    intro P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl
    · exact hA
    · exact hB
    · exact hC
    · exact hD
  -- Therefore in the given circle the square ABCD has been inscribed.
  exact ⟨A, B, C, D, hpolygon, hinscribed, hsquare⟩

end Scratch.BookIV
