import Elements
import Staging.Stage3.CircumferenceAdd

/-!
# Book IV, scratch: the prototype of the circle divided (`Polygon.arcs_sum`)

Brief 0012, sections 7 and 9. The circumferences that the sides of a figure inscribed in a
circle cut off, each named by the angle standing on it at the next corner, make up the
whole circle, for any number of corners: by induction, taking away the second corner and
adding its two circumferences into one (`Circumference.add`, from stage 3, imported from
`Staging`). Until brief 0008's rule lands, the centre is a hypothesis (`hα`). Its own steps
take a point of a chord within the circle by III.2 (`BookIII.Prop2.within` and
`BookIII.Prop2.triangle`), not by Circle 2, which no proof of the edition rests on since
#60; it still rests on Circle 2 through the staged `Circumference.add`, which takes Book
Zero's `exists_onCircle_oppositeSidesOf` where III.2's `Prop2.oppositeSide` would serve
(stage 3's move, #25). Proved by a Codex sailor (OpenAI's Codex, at its highest reasoning
setting) on 19 October 2026, at `89c5da4`; a second sailor, working independently,
reported a complete proof too, and this one, the shorter, was kept. Its III.2 steps were
put in place of Circle 2 in review, the same day. Nothing builds this file, and
`lake env lean` checks it, once `Staging` is built.
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

/-- A point off a straight line is on its own side of that line. -/
theorem same_side_self {A B C : Point} (h : Triangle A B C) : SameSideOf C C A B := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B h.ne₁₂
  exact SameSideOf.of_line h.ne₁₂ hA hB (same_side_refl (h.off_line hA hB))

/-- A fourth point of the circle within the angle ABC is across AC from B. Euclid
reads this separation off an inscribed convex figure: otherwise the point would lie
inside triangle ABC and hence inside the circle. Each "within the circle" is III.2's
(`BookIII.Prop2.within`, `BookIII.Prop2.triangle`), not System E's Circle 2. -/
theorem circle_corner_across_diagonal {A B C D : Point} {α : Circle}
    (hα : ∃ O : Point, Centre O α)
    (hA : OnCircle A α) (hB : OnCircle B α) (hC : OnCircle C α) (hD : OnCircle D α)
    (hDC : SameSideOf D C A B) (hDA : SameSideOf D A B C) :
    OppositeSidesOf D B A C := by
  have hABC : Triangle A B C := hDC.symm.triangle
  have hACD : Triangle A C D := BookIII.Prop2.triangle hα hA hC hD hABC.ne₁₃
    hDA.triangle.ne₂₃ hDC.triangle.ne₁₃
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hABC.ne₁₃
  apply OppositeSidesOf.of_line hABC.ne₁₃ hA_L hC_L
  refine ⟨hACD.off_line hA_L hC_L, hABC.acb.off_line hA_L hC_L, ?_⟩
  intro hDB
  /- The ray BD meets AC within the circle. If D were on B's side of AC, D would
  lie between B and that meeting point, also within the circle. -/
  obtain ⟨X, hAXC, hXray⟩ := crossbar hDC.swap hDA
  have hX_L : OnLine X L := on_line_of_between_ends hAXC hA_L hC_L
  obtain ⟨M, hB_M, hA_M⟩ := Postulate1 B A hABC.ne₁₂.symm
  have hXD : SameSideOf X D B A := SameSideOf.of_onRay hXray
    (same_side_self hDC.triangle).swap
  have hBDX : Between B D X := Between.of_inside hB_M hX_L
    (by obtain ⟨N, hB_N, hD_N, hX_N⟩ := hXray.2.2.1
        exact ⟨N, hB_N, hD_N, hX_N⟩)
    (hXD.symm.sameSide hB_M hA_M) hDB
  have hX_in : InsideCircle X α := BookIII.Prop2.within hα (Or.inr hA) (Or.inr hC) hAXC
  exact inside_not_on (BookIII.Prop2.within hα (Or.inr hB) (Or.inl hX_in) hBDX) hD

/-- Deleting the second corner preserves the inscribed convex figure. The only new
side is AC; all remaining corners are across it from B, by the preceding separation. -/
theorem polygon_delete_second {A B C D : Point} {rest : List Point} {α : Circle}
    (hα : ∃ O : Point, Centre O α) (hps : Polygon (A :: B :: C :: D :: rest))
    (hin : Polygon.InscribedIn (A :: B :: C :: D :: rest) α) :
    Polygon (A :: C :: D :: rest) := by
  have sub : ∀ P ∈ A :: C :: D :: rest, P ∈ A :: B :: C :: D :: rest := by
    intro P hP
    rcases List.mem_cons.mp hP with h | h
    · exact List.mem_cons.mpr (Or.inl h)
    · exact List.mem_cons_of_mem A (List.mem_cons_of_mem B h)
  have hn := hps.2.1
  simp only [List.nodup_cons] at hn
  have hAC : A ≠ C := fun e => hn.1 (by simp [e])
  have hBC : B ≠ C := fun e => hn.2.1 (by simp [e])
  have hAB : A ≠ B := fun e => hn.1 (by simp [e])
  have across : ∀ P ∈ C :: D :: rest, P ≠ C → OppositeSidesOf P B A C := by
    intro P hP hPC
    have hPA : P ≠ A := fun e => hn.1 (List.mem_cons_of_mem B (e ▸ hP))
    have hPB : P ≠ B := fun e => hn.2.1 (e ▸ hP)
    have hPm : P ∈ A :: B :: C :: D :: rest := List.mem_cons_of_mem A (List.mem_cons_of_mem B hP)
    exact circle_corner_across_diagonal hα (hin A (by simp)) (hin B (by simp))
      (hin C (by simp)) (hin P hPm)
      (hps.2.2 (A, B) (by simp [Polygon.sides, segments]) P hPm C (by simp)
        hPA hPB hAC.symm hBC.symm)
      (hps.2.2 (B, C) (by simp [Polygon.sides, segments]) P hPm A (by simp)
        hPB hPC hAB hAC)
  refine ⟨⟨A, C, D, rest, rfl⟩, ?_, ?_⟩
  · simp only [List.nodup_cons]
    exact ⟨fun h => hn.1 (List.mem_cons_of_mem B h), hn.2.2⟩
  · intro s hs P hP Q hQ hP₁ hP₂ hQ₁ hQ₂
    change s ∈ (A, C) :: segments ((C :: D :: rest) ++ [A]) at hs
    rcases List.mem_cons.mp hs with rfl | hs
    · have hPtail : P ∈ C :: D :: rest := (List.mem_cons.mp hP).resolve_left hP₁
      have hQtail : Q ∈ C :: D :: rest := (List.mem_cons.mp hQ).resolve_left hQ₁
      exact OppositeSidesOf.sameSideOf (across P hPtail hP₂).symm
        (across Q hQtail hQ₂).symm
    · apply hps.2.2 s _ P (sub P hP) Q (sub Q hQ) hP₁ hP₂ hQ₁ hQ₂
      change s ∈ (A, B) :: (B, C) :: segments ((C :: D :: rest) ++ [A])
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs)

/-- The last corner of a nonempty chain is one of its corners. -/
theorem end_mem (P : Point) (ps : List Point) : endOf P ps ∈ P :: ps := by
  induction ps generalizing P with
  | nil => simp [endOf]
  | cons Q qs ih => exact List.mem_cons_of_mem P (ih Q)

/-- Closing a chain at A contributes the side from its last corner to A. -/
theorem closing_side_mem (P A : Point) (ps : List Point) :
    (endOf P ps, A) ∈ segments ((P :: ps) ++ [A]) := by
  induction ps generalizing P with
  | nil => simp [endOf, segments]
  | cons Q qs ih => exact List.mem_cons_of_mem (P, Q) (ih Q)

/-- Changing the second corner used to close the list changes only the witness of the
last side's circumference; a witness on the same side gives the same circumference. -/
theorem closing_witness_sum {A B C P : Point} {ps : List Point} {α : Circle}
    (h : SameSideOf B C (endOf P ps) A) :
    Magnitude.sum ((triples ((P :: ps) ++ [A, B])).map
      fun t => standing α t.1 t.2.2 t.2.1) =
    Magnitude.sum ((triples ((P :: ps) ++ [A, C])).map
      fun t => standing α t.1 t.2.2 t.2.1) := by
  induction ps generalizing P with
  | nil =>
      change standing α P B A + 0 = standing α P C A + 0
      rw [standing_congr (show SameSideOf B C P A from h)]
  | cons Q qs ih =>
      cases qs with
      | nil =>
          change standing α P A Q + (standing α Q B A + 0) =
            standing α P A Q + (standing α Q C A + 0)
          rw [standing_congr (show SameSideOf B C Q A from h)]
      | cons R rs =>
          change standing α P R Q + _ = standing α P R Q + _
          exact congrArg (fun x => standing α P R Q + x) (ih h)

/-- Reversing the ends names the same circumference: the measuring angle has the
same magnitude when its arms are named in the opposite order. -/
theorem standing_reverse (α : Circle) (A B C : Point) :
    standing α A B C = standing α C B A := by
  unfold standing
  congr 1
  funext x
  apply propext
  constructor
  · rintro ⟨X, hX, hXB, hx⟩
    refine ⟨X, hX, hXB.swap, ?_⟩
    rw [← angle_symm hXB.triangle.ne₁₃ hXB.triangle.ne₂₃]
    exact hx
  · rintro ⟨X, hX, hXB, hx⟩
    refine ⟨X, hX, hXB.swap, ?_⟩
    rw [← angle_symm hXB.triangle.ne₁₃ hXB.triangle.ne₂₃]
    exact hx

/-- The arcs AB away from C and BC away from A together form AC through B.
This is Book III's addition rule, with each part named by its standing angle. -/
theorem adjacent_arcs_add {A B C K : Point} {α : Circle}
    (hα : ∃ O : Point, Centre O α) (hA : OnCircle A α) (hB : OnCircle B α)
    (hC : OnCircle C α) (hBK : SameSideOf B K A C) :
    standing α A C B + standing α B A C = circumference α A K C := by
  obtain ⟨X, hXC, -⟩ := exists_oppositeSidesOf hBK.triangle.acb []
  obtain ⟨Y, hYA, -⟩ := exists_oppositeSidesOf hBK.triangle.cba []
  rw [standing_eq_circumference hXC.symm, standing_eq_circumference hYA.symm]
  exact BookIII.Circumference.add hα hA hB hC hBK hXC hYA

/-- The two arcs at a removed corner make up the new side's arc. The closing
side retains its arc even though its standing angle is now named at C instead of B. -/
theorem arcs_sum_delete_second {A B C D : Point} {rest : List Point} {α : Circle}
    (hα : ∃ O : Point, Centre O α)
    (hps : Polygon (A :: B :: C :: D :: rest))
    (hin : Polygon.InscribedIn (A :: B :: C :: D :: rest) α) :
    Magnitude.sum (Polygon.arcs (A :: B :: C :: D :: rest) α) =
    Magnitude.sum (Polygon.arcs (A :: C :: D :: rest) α) := by
  have hn := hps.2.1
  simp only [List.nodup_cons] at hn
  have hAB : A ≠ B := fun e => hn.1 (by simp [e])
  have hAC : A ≠ C := fun e => hn.1 (by simp [e])
  have hBC : B ≠ C := fun e => hn.2.1 (by simp [e])
  have hDA : D ≠ A := fun e => hn.1 (by simp [← e])
  have hDB : D ≠ B := fun e => hn.2.1 (by simp [← e])
  have hDC : D ≠ C := fun e => hn.2.2.1 (by simp [← e])
  have hD_C : SameSideOf D C A B := hps.2.2 (A, B)
    (by simp [Polygon.sides, segments]) D (by simp) C (by simp)
    hDA hDB hAC.symm hBC.symm
  have hD_A : SameSideOf D A B C := hps.2.2 (B, C)
    (by simp [Polygon.sides, segments]) D (by simp) A (by simp)
    hDB hDC hAB hAC
  have hD_B : OppositeSidesOf D B A C := circle_corner_across_diagonal hα
    (hin A (by simp)) (hin B (by simp)) (hin C (by simp)) (hin D (by simp)) hD_C hD_A
  /- Joining the first two arcs replaces AB and BC by AC away from D. -/
  have hadd : standing α A C B + standing α B D C = standing α A D C := by
    rw [standing_congr hD_A, standing_eq_circumference hD_B]
    exact adjacent_arcs_add hα (hin A (by simp)) (hin B (by simp)) (hin C (by simp))
      (same_side_self hD_B.symm.triangle)
  /- The last side is unchanged; B and C are both on the figure's side of it. -/
  have hlast : endOf D rest ∈ D :: rest := end_mem D rest
  have hlastB : endOf D rest ≠ B := fun e =>
    hn.2.1 (List.mem_cons_of_mem C (e ▸ hlast))
  have hlastC : endOf D rest ≠ C := fun e => hn.2.2.1 (e ▸ hlast)
  have hclose : SameSideOf B C (endOf D rest) A := hps.2.2 (endOf D rest, A)
    (by change (endOf D rest, A) ∈ (A, B) :: (B, C) :: (C, D) ::
          segments ((D :: rest) ++ [A])
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (closing_side_mem D A rest))))
    B (by simp) C (by simp) hlastB.symm hAB.symm hlastC.symm hAC.symm
  have htail := closing_witness_sum (α := α) (P := C) (ps := D :: rest) hclose
  change standing α A C B + (standing α B D C +
    Magnitude.sum ((triples ((C :: D :: rest) ++ [A, B])).map
      fun t => standing α t.1 t.2.2 t.2.1)) =
    standing α A D C + Magnitude.sum ((triples ((C :: D :: rest) ++ [A, C])).map
      fun t => standing α t.1 t.2.2 t.2.1)
  rw [← add_assoc, hadd, htail]

/-- **The circumferences cut off by the sides of an inscribed figure make up the whole
circle**: four right angles, the measure of the whole circle. -/
theorem Polygon.arcs_sum {ps : List Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hps : Polygon ps) (hin : Polygon.InscribedIn ps α) :
    Magnitude.sum (Polygon.arcs ps α) = ∟ + ∟ + ∟ + ∟ := by
  obtain ⟨A, B, C, rest, rfl⟩ := hps.1
  induction rest generalizing A B C with
  | nil =>
      /- For a triangle, AB and BC form AC through B. The remaining arc CA is
      on the other side of AC; these two circumferences make up the whole circle. -/
      have hn := hps.2.1
      simp only [List.nodup_cons] at hn
      have hABC : Triangle A B C := BookIII.Prop2.triangle hα (hin A (by simp))
        (hin B (by simp)) (hin C (by simp)) (fun e => hn.1 (by simp [e]))
        (fun e => hn.2.1 (by simp [e])) (fun e => hn.1 (by simp [e]))
      obtain ⟨K, hKB, -⟩ := exists_oppositeSidesOf hABC.acb []
      have hadd := adjacent_arcs_add hα (hin A (by simp)) (hin B (by simp))
        (hin C (by simp)) (same_side_self hABC.acb)
      have hwhole := BookIII.Circumference.whole hα (hin A (by simp)) (hin C (by simp)) hKB
      change standing α A C B + (standing α B A C + (standing α C B A + 0)) = _
      rw [add_zero, standing_reverse α C B A, standing_eq_circumference hKB.symm,
        ← add_assoc, hadd, hwhole, ← add_assoc]
  | cons D rest ih =>
      /- Remove B. Convexity survives, the new side's arc is the sum of the two
      removed arcs, and the other arcs retain their measures. -/
      rw [arcs_sum_delete_second hα hps hin]
      apply ih A C D (polygon_delete_second hα hps hin)
      intro P hP
      apply hin P
      rcases List.mem_cons.mp hP with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem A (List.mem_cons_of_mem B h)

end Scratch.BookIV
