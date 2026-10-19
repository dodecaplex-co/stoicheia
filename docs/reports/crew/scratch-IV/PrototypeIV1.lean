import Elements

/-!
# Book IV, scratch: the prototype of what a construction is given (IV.1)

Brief 0012, section 9. IV.1 receives a circle and a straight line, given by its two ends,
not greater than any diameter, and constructs everything else, as Euclid does. Until brief
0008's rule that every circle has a centre lands, the centre is a hypothesis (`hABC`),
which the final statement drops. Proved by a Codex sailor (OpenAI's Codex, at its
highest reasoning setting) on 19 October 2026, at `89c5da4`; nothing builds this file, and
`lake env lean` checks it.
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

/-- Euclid takes for granted that a diameter can be drawn. Take C on the circle and
join it to the centre O; the straight line, continued beyond O, meets the circle at B
(System E, Points 7 and Intersections 5). Thus O lies between its two ends. -/
theorem Prop1.draw_diameter {ABC : Circle} {O : Point} (hO : Centre O ABC) :
    ∃ B C : Point, OnCircle B ABC ∧ OnCircle C ABC ∧ Between B O C := by
  obtain ⟨C, hC, _⟩ := exists_point_on_circle ABC []
  have hCO : C ≠ O := ne_of_centre_of_on hO hC
  obtain ⟨CO, hC_CO, hO_CO⟩ := Postulate1 C O hCO
  obtain ⟨B, hB, _, hBOC⟩ := line_circle_beyond (centre_inside hO) hO_CO hC_CO hCO
  exact ⟨B, C, hB, hC, hBOC⟩

/-- Euclid takes for granted that the circle with centre C and distance CE meets ABC.
The point C of ABC is inside this new circle, and B is outside it, since CE is part of
CB. System E's corrected Intersection 4 supplies their meeting. -/
theorem Prop1.circles_intersect {ABC EAF : Circle} {B C E : Point}
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hCEB : Between C E B)
    (hC_EAF : Centre C EAF) (hE_EAF : OnCircle E EAF) :
    ∃ A : Point, OnCircle A ABC ∧ OnCircle A EAF := by
  have hB_out : OutsideCircle B EAF :=
    outside_of_len_gt hC_EAF hE_EAF (len_lt_of_between hCEB)
  obtain ⟨A, _, _, hA_ABC, hA_EAF, _, _⟩ :=
    circles_meet_of_on_inside_outside hC (Or.inr hB) (centre_inside hC_EAF) hB_out
  exact ⟨A, hA_ABC, hA_EAF⟩

/-- Into a given circle to fit a straight line equal to a given straight line which is not
greater than the diameter of the circle. -/
theorem Prop1 {D₁ D₂ : Point} (ABC : Circle) (hABC : ∃ O : Point, Centre O ABC)
    (hD : D₁ ≠ D₂)
    (hle : ∀ B C E : Point, Centre E ABC → OnCircle B ABC → OnCircle C ABC → Between B E C →
      len D₁ D₂ ≤ len B C) :
    ∃ C A : Point, OnCircle C ABC ∧ OnCircle A ABC ∧ len C A = len D₁ D₂ := by
  -- Let ABC be the given circle, and D the given straight line not greater than the diameter of the circle;
  obtain ⟨O, hO⟩ := hABC
  -- thus it is required to fit into the circle ABC a straight line equal to the straight line D.
  show ∃ C A : Point, OnCircle C ABC ∧ OnCircle A ABC ∧ len C A = len D₁ D₂
  -- Let a diameter BC of the circle ABC be drawn.
  obtain ⟨B, C, hB, hC, hBOC⟩ := Prop1.draw_diameter hO
  have hD_BC : len D₁ D₂ ≤ len B C := hle B C O hO hB hC hBOC
  -- Then, if BC is equal to D, that which was enjoined will have been done; for BC has been fitted into the circle ABC equal to the straight line D.
  by_cases heq : len B C = len D₁ D₂
  · exact ⟨B, C, hB, hC, heq⟩
  -- But, if BC is greater than D,
  have hlt : len D₁ D₂ < len B C := by
    rcases lt_trichotomy (len D₁ D₂) (len B C) with h | h | h
    · exact h
    · exact False.elim (heq h.symm)
    · exact False.elim (hD_BC h)
  -- let CE be made equal to D, and with centre C and distance CE let the circle EAF be described;
  obtain ⟨E, hE⟩ := BookI.Prop3 hD (show len D₁ D₂ < len C B by
    rw [len_symm C B]
    exact hlt)
  obtain ⟨EAF, hEAF⟩ := Postulate3 C E (ne_of_between hE.1)
  /- The meeting at A is tacit in this sentence: C is within EAF and B is outside it.
     The helper proves that the two circles meet, before any length CA is used. -/
  obtain ⟨A, hA_ABC, hA_EAF⟩ := Prop1.circles_intersect hB hC hE.1 hEAF.1 hEAF.2
  -- let CA be joined.
  obtain ⟨_, _, _⟩ := Postulate1 C A (ne_of_centre_of_on hEAF.1 hA_EAF).symm
  -- Then, since the point C is the centre of the circle EAF,
  have hC_EAF : Centre C EAF := hEAF.1
  -- CA is equal to CE.
  have hCA_CE : len C A = len C E := Definition15 hC_EAF hA_EAF hEAF.2
  -- But CE is equal to D;
  have hCE_D : len C E = len D₁ D₂ := hE.2
  -- therefore D is also equal to CA.
  have hD_CA : len D₁ D₂ = len C A := CommonNotion1 hCE_D.symm hCA_CE
  -- Therefore into the given circle ABC there has been fitted CA equal to the given straight line D.
  exact ⟨C, A, hC, hA_ABC, hD_CA.symm⟩

end Scratch.BookIV
