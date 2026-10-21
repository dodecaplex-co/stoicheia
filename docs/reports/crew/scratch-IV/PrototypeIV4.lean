import Elements

/-!
# Book IV, scratch: the prototype of a circle inscribed in a figure (IV.4)

Brief 0012, section 9. The foundation under test is Definitions IV.4 and IV.5
(`Polygon.CircumscribedAbout`, `Circle.InscribedIn`): each side of the figure touches the
circle (`Touches`, Definition III.2) at a point between its ends. The helpers supply what
Euclid leaves tacit: that the bisectors meet within the triangle, that each half-angle is
acute, and that each point of contact falls within its side. Proved by a Codex sailor
(OpenAI's Codex, at its highest reasoning setting) on 19 October 2026, at `89c5da4`;
nothing builds this file, and `lake env lean` checks it.
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

/-- Euclid takes for granted that the two interior bisector rays meet within the
triangle. This is true of any two rays from B and C lying inside their angles:
use the crossbar theorem to put X on AC and Y on AB, then Pasch to cross BX with CY. -/
theorem interior_rays_meet {A B C U V : Point} (hABC : Triangle A B C)
    (hUC : SameSideOf U C B A) (hUA : SameSideOf U A B C)
    (hVA : SameSideOf V A C B) (hVB : SameSideOf V B C A) :
    ∃ D : Point, InsideTriangle D A B C ∧ OnRay D B U ∧ OnRay D C V := by
  obtain ⟨X, hAXC, hX⟩ := crossbar hUC hUA
  obtain ⟨Y, hBYA, hY⟩ := crossbar hVA hVB
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hABC.ne₁₂
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABC.ne₂₃
  obtain ⟨CA, hC_CA, hA_CA⟩ := Postulate1 C A hABC.ne₁₃.symm
  obtain ⟨BX, hB_BX, hX_BX⟩ := Postulate1 B X hX.2.1.symm
  have hX_CA := on_line_of_between_ends hAXC hA_CA hC_CA
  have hY_AB := on_line_of_between_ends hBYA hB_AB hA_AB
  have hA_BX : ¬ OnLine A BX := fun h =>
    hABC.cab.off_line hC_CA hA_CA
      (line_unique (ne_of_between hAXC) h hX_BX hA_CA hX_CA ▸ hB_BX)
  have hC_BX : ¬ OnLine C BX := fun h =>
    hABC.cab.off_line hC_CA hA_CA
      (line_unique (ne_of_between (between_symm hAXC)) h hX_BX hC_CA hX_CA ▸ hB_BX)
  have hY_BX : ¬ OnLine Y BX := fun h =>
    hA_BX (on_line_of_between hBYA hB_BX h)
  have hYA_BX := pasch2 hBYA hB_BX hY_BX
  have hYC_BX : OppositeSides Y C BX :=
    ⟨hY_BX, hC_BX, fun hs => pasch3 hAXC hX_BX (same_side_trans hYA_BX hs)⟩
  obtain ⟨D, hD_BX, hYDC⟩ := hYC_BX.exists_between
  have hY_BC : ¬ OnLine Y BC := fun h =>
    hABC.bca.off_line hB_BC hC_BC (on_line_of_between hBYA hB_BC h)
  have hD_BC : ¬ OnLine D BC := fun h =>
    hY_BC (on_line_of_between (between_symm hYDC) hC_BC h)
  have hDA_BC : SameSide D A BC :=
    same_side_trans (same_side_symm (pasch2 (between_symm hYDC) hC_BC hD_BC))
      (pasch2 hBYA hB_BC hY_BC)
  have hY_CA : ¬ OnLine Y CA := fun h =>
    hABC.cab.off_line hC_CA hA_CA
      (on_line_of_between (between_symm hBYA) hA_CA h)
  have hD_CA : ¬ OnLine D CA := fun h =>
    hY_CA (on_line_of_between (between_symm hYDC) hC_CA h)
  have hDB_CA : SameSide D B CA :=
    same_side_trans (same_side_symm (pasch2 (between_symm hYDC) hC_CA hD_CA))
      (pasch2 (between_symm hBYA) hA_CA hY_CA)
  have hD_AB : ¬ OnLine D AB := fun h =>
    hABC.off_line hA_AB hB_AB (on_line_of_between hYDC hY_AB h)
  have hDC_AB := pasch2 hYDC hY_AB hD_AB
  have hDA : SameSideOf D A B C := SameSideOf.of_line hABC.ne₂₃ hB_BC hC_BC hDA_BC
  have hDC : SameSideOf D C B A :=
    SameSideOf.of_line hABC.ne₁₂.symm hB_AB hA_AB hDC_AB
  have hDU : SameSideOf D U B C := hDA.trans hUA.symm
  have hDV : SameSideOf D V C B := hDA.swap.trans hVA.symm
  have hU_BX := hX.symm.onLine hB_BX hX_BX
  have hDCV : Collinear C V D := by
    obtain ⟨L, hC, hV, hYL⟩ := hY.2.2.1
    exact ⟨L, hC, hV, on_line_of_between_ends hYDC hYL hC⟩
  exact ⟨D, ⟨hDA, SameSideOf.of_line hABC.ne₁₃.symm hC_CA hA_CA hDB_CA, hDC.swap⟩,
    OnRay.of_sameSideOf hDU ⟨BX, hB_BX, hU_BX, hD_BX⟩
      (fun h => hD_AB (h ▸ hB_AB)),
    OnRay.of_sameSideOf hDV hDCV (fun h => hD_BC (h ▸ hC_BC))⟩

/-- Euclid takes for granted that either half of a triangle's angle is acute.
I.17 makes the whole angle less than two right angles, and comparison of doubles
makes its half less than one right angle. -/
theorem half_angle_acute {A B C : Point} {a : Angle} (hABC : Triangle A B C)
    (hsum : a + a = ∠ A B C) : a < ∟ := by
  have hwhole : ∠ A B C < ∟ + ∟ :=
    lt_trans (CommonNotion5 hABC.bca.angle_pos) (BookI.Prop17 hABC).1
  rw [← hsum] at hwhole
  rcases lt_trichotomy a ∟ with h | h | h
  · exact h
  · rw [h] at hwhole
    exact False.elim (lt_irrefl _ hwhole)
  · exact False.elim (lt_irrefl _ (lt_trans hwhole (Magnitude.add_self_lt_add_self h)))

/-- Euclid takes for granted that a perpendicular foot in an acute angle lies
forward on its arm. If it were the vertex the angle would be right; if it lay
behind the vertex, I.16 would make the acute angle greater than a right angle. -/
theorem foot_on_forward_ray {P Q D E : Point} (hPQD : Triangle P Q D)
    (hacute : ∠ D P Q < ∟) (hE : Collinear P Q E)
    (hperp : ∀ X : Point, Collinear P Q X → X ≠ E → ∠ D E X = ∟) :
    OnRay E P Q := by
  obtain ⟨L, hP, hQ, hEL⟩ := hE
  have hD : ¬ OnLine D L := hPQD.off_line hP hQ
  have hEP : E ≠ P := by
    intro h
    subst E
    have hr := hperp Q ⟨L, hP, hQ, hQ⟩ hPQD.ne₁₂.symm
    exact (Magnitude.ne_of_lt hacute) hr
  refine ⟨hPQD.ne₁₂, hEP, ⟨L, hP, hQ, hEL⟩, ?_⟩
  intro hb
  have hDEP := (Triangle.of_line hEL hP hEP hD).cab
  have hlt := (BookI.Prop16 hDEP hb).1
  rw [angle_symm hEP.symm hDEP.ne₁₂, hperp P ⟨L, hP, hQ, hP⟩ hEP.symm] at hlt
  exact lt_irrefl _ (lt_trans hacute hlt)

/-- Euclid takes for granted that a circle touching the two sides at a corner,
with its centre strictly within the angle, cannot pass through that corner.
Otherwise III.18 makes both parts of the angle right, contrary to I.17. -/
theorem vertex_not_on_circle {A B C D : Point} {α : Circle}
    (hABC : Triangle A B C) (hinside : InsideTriangle D A B C)
    (hD : Centre D α) (hAB : Touches A B α) (hCA : Touches C A α) :
    ¬ OnCircle A α := by
  intro hA
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hABC.ne₁₂
  obtain ⟨M, hCM, hAM⟩ := Postulate1 C A hABC.ne₁₃.symm
  have hrB := BookIII.Prop18 hD hA hAB ⟨L, hAL, hBL, hAL⟩
    B ⟨L, hAL, hBL, hBL⟩ hABC.ne₁₂.symm
  have hrC := BookIII.Prop18 hD hA hCA ⟨M, hCM, hAM, hAM⟩
    C ⟨M, hCM, hAM, hCM⟩ hABC.ne₁₃.symm
  have hDA : D ≠ A := hinside.2.2.triangle.ne₁₃.symm
  have hadd := angle_add_of_within hinside.2.2 hinside.2.1.swap
  rw [angle_symm hABC.ne₁₂.symm hDA, hrB, hrC] at hadd
  have hlt : ∠ B A C < ∟ + ∟ :=
    lt_trans (CommonNotion5 hABC.acb.angle_pos) (BookI.Prop17 hABC.bac).1
  rw [hadd] at hlt
  exact lt_irrefl _ hlt

/-- Euclid takes for granted that a circle lies on its centre's side of a tangent.
For a point of the circumference off that tangent, the other side would make the
straight line cut the circle (System E, Intersection 2), contrary to touching. -/
theorem circle_point_on_centre_side {A B D P : Point} {α : Circle} {L : Line}
    (hD : Centre D α) (ht : Touches A B α) (hA : OnLine A L) (hB : OnLine B L)
    (hP : OnCircle P α) (hPoff : ¬ OnLine P L) : SameSide P D L := by
  have hDoff : ¬ OnLine D L := fun hd =>
    ht.not_inside ⟨L, hA, hB, hd⟩ (centre_inside hD)
  exact Classical.byContradiction fun hs =>
    (ht.2 L hA hB).2
      (line_meets_circle_of_opposite_sides (Or.inr hP) (Or.inl (centre_inside hD))
        ⟨hPoff, hDoff, hs⟩)

/-- Euclid takes for granted that the contact is on the finite side, not on its
extension. With the centre inside the triangle, the other two tangents put the
contact on A's side of BC and B's side of CA. Neither endpoint is possible by
`vertex_not_on_circle`; Pasch then puts the contact strictly between A and B.
This proves only the position of a given contact, after the circle and its
three tangencies have been established. -/
theorem contact_between_corners {A B C D E : Point} {α : Circle}
    (hABC : Triangle A B C) (hinside : InsideTriangle D A B C) (hD : Centre D α)
    (hAB : Touches A B α) (hBC : Touches B C α) (hCA : Touches C A α)
    (hE : OnCircle E α) (hcol : Collinear A B E) : Between A E B := by
  obtain ⟨AB, hA_AB, hB_AB, hE_AB⟩ := hcol
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABC.ne₂₃
  obtain ⟨CA, hC_CA, hA_CA⟩ := Postulate1 C A hABC.ne₁₃.symm
  have hEA : E ≠ A := fun h =>
    vertex_not_on_circle hABC hinside hD hAB hCA (h ▸ hE)
  have hEB : E ≠ B := fun h =>
    vertex_not_on_circle hABC.bca ⟨hinside.2.1, hinside.2.2, hinside.1⟩
      hD hBC hAB (h ▸ hE)
  have hE_BC : ¬ OnLine E BC := fun h =>
    hABC.bca.off_line hB_BC hC_BC
      (line_unique hEB hE_AB hB_AB h hB_BC ▸ hA_AB)
  have hE_CA : ¬ OnLine E CA := fun h =>
    hABC.cab.off_line hC_CA hA_CA
      (line_unique hEA hE_AB hA_AB h hA_CA ▸ hB_AB)
  have hEA_BC : SameSide E A BC :=
    same_side_trans (same_side_symm
      (circle_point_on_centre_side hD hBC hB_BC hC_BC hE hE_BC))
      (hinside.1.sameSide hB_BC hC_BC)
  have hEB_CA : SameSide E B CA :=
    same_side_trans (same_side_symm
      (circle_point_on_centre_side hD hCA hC_CA hA_CA hE hE_CA))
      (hinside.2.1.sameSide hC_CA hA_CA)
  rcases between_cases hEA.symm hEB hABC.ne₁₂ hA_AB hE_AB hB_AB with h | h | h
  · exact h
  · exact False.elim (pasch3 h hA_CA hEB_CA)
  · exact False.elim (pasch3 h hB_BC (same_side_symm hEA_BC))

/-- In a given triangle to inscribe a circle. -/
theorem Prop4 {A B C : Point} (hABC : Triangle A B C) :
    ∃ (EFG : Circle) (D E F G : Point), Centre D EFG ∧ Circle.InscribedIn EFG [A, B, C] ∧
      Between A E B ∧ Between B F C ∧ Between C G A ∧
      OnCircle E EFG ∧ OnCircle F EFG ∧ OnCircle G EFG := by
  -- Let ABC be the given triangle;
  have hAB : A ≠ B := hABC.ne₁₂
  have hBC : B ≠ C := hABC.ne₂₃
  have hCA : C ≠ A := hABC.ne₁₃.symm
  -- thus it is required to inscribe a circle in the triangle ABC.
  show ∃ (EFG : Circle) (D E F G : Point), Centre D EFG ∧ Circle.InscribedIn EFG [A, B, C] ∧
    Between A E B ∧ Between B F C ∧ Between C G A ∧
    OnCircle E EFG ∧ OnCircle F EFG ∧ OnCircle G EFG
  -- Let the angles ABC, ACB be bisected by the straight lines BD, CD [I. 9], and let these meet one another at the point D;
  obtain ⟨U, hUC, hUA, hbisB, -⟩ := BookI.Prop9 hABC
  obtain ⟨V, hVA, hVB, hbisC, -⟩ := BookI.Prop9 hABC.bca
  obtain ⟨D, hinside, hDU, hDV⟩ := interior_rays_meet hABC hUC hUA hVA hVB
  have hBsplit : ∠ A B D = ∠ D B C := by
    rw [angle_onRay_right hDU hAB, angle_onRay_left hDU hBC.symm]
    exact hbisB
  have hCsplit : ∠ B C D = ∠ D C A := by
    rw [angle_onRay_right hDV hBC, angle_onRay_left hDV hCA.symm]
    exact hbisC
  -- from D let DE, DF, DG be drawn perpendicular to the straight lines AB, BC, CA.
  obtain ⟨E, hE, hDE⟩ := BookI.Prop12 hAB hinside.2.2.triangle
  obtain ⟨F, hF, hDF⟩ := BookI.Prop12 hBC hinside.1.triangle
  obtain ⟨G, hG, hDG⟩ := BookI.Prop12 hCA hinside.2.1.triangle
  obtain ⟨AB, hA_AB, hB_AB, hE_AB⟩ := hE
  obtain ⟨BC, hB_BC, hC_BC, hF_BC⟩ := hF
  obtain ⟨CA, hC_CA, hA_CA, hG_CA⟩ := hG
  /- Before I.26, the feet must lie on the forward arms of the bisected angles.
     Their strict positions within the finite sides are established after tangency,
     by `contact_between_corners`; nothing here assumes the angle at A bisected. -/
  have hBacute : ∠ D B C < ∟ := half_angle_acute hABC (by
    have h := (angle_add_of_within hinside.2.2.swap hinside.1).symm
    rwa [hBsplit] at h)
  have hCacute : ∠ B C D < ∟ := half_angle_acute hABC.bca (by
    have h := (angle_add_of_within hinside.1.swap hinside.2.1).symm
    rwa [← hCsplit] at h)
  have hDB : D ≠ B := hinside.1.triangle.ne₁₃.symm
  have hDC : D ≠ C := hinside.1.triangle.ne₂₃.symm
  have hEforward : OnRay E B A := foot_on_forward_ray hinside.2.2.triangle.bac
    (by rw [angle_symm hDB hAB, hBsplit]; exact hBacute)
    ⟨AB, hB_AB, hA_AB, hE_AB⟩ (by
      intro X hX hXE
      obtain ⟨L, hB, hA, hXL⟩ := hX
      exact hDE X ⟨L, hA, hB, hXL⟩ hXE)
  have hFforwardB : OnRay F B C := foot_on_forward_ray hinside.1.triangle hBacute
    ⟨BC, hB_BC, hC_BC, hF_BC⟩ hDF
  have hFforwardC : OnRay F C B := foot_on_forward_ray hinside.1.triangle.bac
    (by rw [angle_symm hDC hBC]; exact hCacute)
    ⟨BC, hC_BC, hB_BC, hF_BC⟩ (by
      intro X hX hXF
      obtain ⟨L, hC, hB, hXL⟩ := hX
      exact hDF X ⟨L, hB, hC, hXL⟩ hXF)
  have hGforward : OnRay G C A := foot_on_forward_ray hinside.2.1.triangle
    (by rw [← hCsplit]; exact hCacute) ⟨CA, hC_CA, hA_CA, hG_CA⟩ hDG
  have hD_AB := hinside.2.2.triangle.off_line hA_AB hB_AB
  have hD_BC := hinside.1.triangle.off_line hB_BC hC_BC
  have hD_CA := hinside.2.1.triangle.off_line hC_CA hA_CA
  have hEBD : Triangle E B D := Triangle.of_line hE_AB hB_AB hEforward.2.1 hD_AB
  have hFBD : Triangle F B D := Triangle.of_line hF_BC hB_BC hFforwardB.2.1 hD_BC
  have hGCD : Triangle G C D := Triangle.of_line hG_CA hC_CA hGforward.2.1 hD_CA
  have hFCD : Triangle F C D := Triangle.of_line hF_BC hC_BC hFforwardC.2.1 hD_BC
  -- Now, since the angle ABD is equal to the angle CBD,
  have hABD_CBD : ∠ A B D = ∠ C B D :=
    hBsplit.trans (angle_symm hDB hBC.symm)
  have hEBD_FBD : ∠ E B D = ∠ F B D := by
    rw [angle_onRay_left hEforward hDB, angle_onRay_left hFforwardB hDB]
    exact hABD_CBD
  -- and the right angle BED is also equal to the right angle BFD,
  have hBED : ∠ B E D = ∟ :=
    (angle_symm hEBD.ne₁₂.symm hEBD.ne₁₃.symm).trans
      (hDE B ⟨AB, hA_AB, hB_AB, hB_AB⟩ hEforward.2.1.symm)
  have hBFD : ∠ B F D = ∟ :=
    (angle_symm hFBD.ne₁₂.symm hFBD.ne₁₃.symm).trans
      (hDF B ⟨BC, hB_BC, hC_BC, hB_BC⟩ hFforwardB.2.1.symm)
  have hBED_BFD : ∠ B E D = ∠ B F D := hBED.trans hBFD.symm
  -- EBD, FBD are two triangles having two angles equal to two angles and one side equal to one side, namely that subtending one of the equal angles, which is BD common to the triangles;
  have hDBE_DBF : ∠ D B E = ∠ D B F :=
    (angle_symm hDB hEforward.2.1).trans
      (hEBD_FBD.trans (angle_symm hFforwardB.2.1 hDB))
  have hBDcommon : ‖D B‖ = ‖D B‖ := rfl
  -- therefore they will also have the remaining sides equal to the remaining sides; [I. 26]
  /- I.26's interface lists these same triangles from D, so that BD is its
     given side opposite the equal right angles at E and F. -/
  have hcongrB := BookI.Prop26 hEBD.cba hFBD.cba hDBE_DBF hBED_BFD (Or.inr hBDcommon)
  -- therefore DE is equal to DF.
  have hDE_DF : ‖D E‖ = ‖D F‖ := hcongrB.2.1
  -- For the same reason
  have hGCD_FCD : ∠ G C D = ∠ F C D := by
    rw [angle_onRay_left hGforward hDC, angle_onRay_left hFforwardC hDC]
    exact (angle_symm hCA.symm hDC).trans hCsplit.symm
  have hDCG_DCF : ∠ D C G = ∠ D C F :=
    (angle_symm hDC hGforward.2.1).trans
      (hGCD_FCD.trans (angle_symm hFforwardC.2.1 hDC))
  have hCGD : ∠ C G D = ∟ :=
    (angle_symm hGCD.ne₁₂.symm hGCD.ne₁₃.symm).trans
      (hDG C ⟨CA, hC_CA, hA_CA, hC_CA⟩ hGforward.2.1.symm)
  have hCFD : ∠ C F D = ∟ :=
    (angle_symm hFCD.ne₁₂.symm hFCD.ne₁₃.symm).trans
      (hDF C ⟨BC, hB_BC, hC_BC, hC_BC⟩ hFforwardC.2.1.symm)
  have hcongrC := BookI.Prop26 hGCD.cba hFCD.cba hDCG_DCF
    (hCGD.trans hCFD.symm) (Or.inr rfl)
  -- DG is also equal to DF.
  have hDG_DF : ‖D G‖ = ‖D F‖ := hcongrC.2.1
  -- Therefore the three straight lines DE, DF, DG are equal to one another;
  have hDG_DE : ‖D G‖ = ‖D E‖ := hDG_DF.trans hDE_DF.symm
  -- therefore the circle described with centre D and distance one of the straight lines DE, DF, DG will pass also through the remaining points, and will touch the straight lines AB, BC, CA, because the angles at the points E, F, G are right.
  obtain ⟨EFG, hD_EFG, hE_EFG⟩ := Postulate3 D E hEBD.ne₁₃.symm
  have hF_EFG : OnCircle F EFG := on_circle_of_len_eq hD_EFG hE_EFG hDE_DF.symm
  have hG_EFG : OnCircle G EFG := on_circle_of_len_eq hD_EFG hE_EFG hDG_DE
  /- The right angles give tangency by the III.16 argument in the next sentence. -/
  -- For, if it cuts them, the straight line drawn at right angles to the diameter of the circle from its extremity will be found to fall within the circle: which was proved absurd; [III. 16]
  have hEBtouch : Touches E B EFG := BookIII.Prop16.porism hD_EFG hE_EFG hEBD.cab
    (hDE B ⟨AB, hA_AB, hB_AB, hB_AB⟩ hEforward.2.1.symm)
  have hFBtouch : Touches F B EFG := BookIII.Prop16.porism hD_EFG hF_EFG hFBD.cab
    (hDF B ⟨BC, hB_BC, hC_BC, hB_BC⟩ hFforwardB.2.1.symm)
  have hGCtouch : Touches G C EFG := BookIII.Prop16.porism hD_EFG hG_EFG hGCD.cab
    (hDG C ⟨CA, hC_CA, hA_CA, hC_CA⟩ hGforward.2.1.symm)
  -- therefore the circle described with centre D and distance one of the straight lines DE, DF, DG will not cut the straight lines AB, BC, CA;
  have hnoAB : ∀ L : Line, OnLine A L → OnLine B L → ¬ LineMeetsCircle L EFG := by
    intro L hA hB
    exact (hEBtouch.2 L (hEforward.onLine hB hA) hB).2
  have hnoBC : ∀ L : Line, OnLine B L → OnLine C L → ¬ LineMeetsCircle L EFG := by
    intro L hB hC
    exact (hFBtouch.2 L (hFforwardB.onLine hB hC) hB).2
  have hnoCA : ∀ L : Line, OnLine C L → OnLine A L → ¬ LineMeetsCircle L EFG := by
    intro L hC hA
    exact (hGCtouch.2 L (hGforward.onLine hC hA) hC).2
  -- therefore it will touch them, and will be the circle inscribed in the triangle ABC. [IV. Def. 5]
  have hABtouch : Touches A B EFG := ⟨hAB, fun L hA hB =>
    ⟨⟨E, hEforward.onLine hB hA, hE_EFG⟩, hnoAB L hA hB⟩⟩
  have hBCtouch : Touches B C EFG := ⟨hBC, fun L hB hC =>
    ⟨⟨F, hFforwardB.onLine hB hC, hF_EFG⟩, hnoBC L hB hC⟩⟩
  have hCAtouch : Touches C A EFG := ⟨hCA, fun L hC hA =>
    ⟨⟨G, hGforward.onLine hC hA, hG_EFG⟩, hnoCA L hC hA⟩⟩
  have hAEB := contact_between_corners hABC hinside hD_EFG
    hABtouch hBCtouch hCAtouch hE_EFG ⟨AB, hA_AB, hB_AB, hE_AB⟩
  have hBFC := contact_between_corners hABC.bca ⟨hinside.2.1, hinside.2.2, hinside.1⟩
    hD_EFG hBCtouch hCAtouch hABtouch hF_EFG ⟨BC, hB_BC, hC_BC, hF_BC⟩
  have hCGA := contact_between_corners hABC.cab ⟨hinside.2.2, hinside.1, hinside.2.1⟩
    hD_EFG hCAtouch hABtouch hBCtouch hG_EFG ⟨CA, hC_CA, hA_CA, hG_CA⟩
  have hinscribed : Circle.InscribedIn EFG [A, B, C] := by
    intro s hs
    have hsides : s = (A, B) ∨ s = (B, C) ∨ s = (C, A) := by
      simpa [Polygon.sides, segments] using hs
    rcases hsides with rfl | rfl | rfl
    · exact ⟨hABtouch, E, hAEB, hE_EFG⟩
    · exact ⟨hBCtouch, F, hBFC, hF_EFG⟩
    · exact ⟨hCAtouch, G, hCGA, hG_EFG⟩
  -- Let it be inscribed, as FGE.
  refine ⟨EFG, D, E, F, G, hD_EFG, hinscribed, ?_⟩
  -- Therefore in the given triangle ABC the circle EFG has been inscribed.
  exact ⟨hAEB, hBFC, hCGA, hE_EFG, hF_EFG, hG_EFG⟩

end Scratch.BookIV
