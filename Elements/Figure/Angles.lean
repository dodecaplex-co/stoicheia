import Elements.Figure.Rays
import Elements.Figure.Sides

/-!
# Book Zero: angles

An angle, for Euclid, is made by two straight lines that meet, and he names it by
three letters without ever asking which points of its arms the letters stand
for. "The angle FAG is common to both triangles", "the angle DBC is the angle
ABC": an angle depends only on its two rays. He reads straight off the figure
when one angle is made up of two others, and when a straight line drawn within
an angle crosses the straight line joining its arms; and he takes for granted
that on one side of a straight line only one ray from a point of it makes a
given angle with it. These are those facts, from System E's diagram rules
(Avigad, Dean and Mumma, §3.4 and §3.6).
-/

namespace Elements

open Tacit

variable {A B C : Point} {L : Line}

/-! ## An angle depends only on its rays -/

/-- An angle doesn't change when its arms are traced through other points of the
same rays: if `B'` is on the ray from `A` through `B`, and `C'` on the ray from `A`
through `C`, the angle `B'AC'` is the angle `BAC`. (System E, Diagram-angle 4) -/
theorem angle_eq_of_onRay {B' C' : Point} (hB : OnRay B' A B) (hC : OnRay C' A C) :
    ∠ B' A C' = ∠ B A C := by
  obtain ⟨hAB, hB'A, ⟨L, hA, hBL, hB'L⟩, hB'⟩ := hB
  obtain ⟨hAC, hC'A, ⟨M, hAM, hCM, hC'M⟩, hC'⟩ := hC
  exact (angle_eq_of_same_rays hA hBL hB'L hAM hCM hC'M hAB.symm hB'A hAC.symm hC'A
    (fun h => hB' (between_symm h)) (fun h => hC' (between_symm h))).symm

/-- One arm traced through another point of its ray: if `B'` is on the ray from `A`
through `B`, the angle `B'AC` is the angle `BAC`. (System E, Diagram-angle 4) -/
theorem angle_onRay_left {B' : Point} (hB : OnRay B' A B) (hCA : C ≠ A) :
    ∠ B' A C = ∠ B A C :=
  angle_eq_of_onRay hB (OnRay.self hCA.symm)

/-- The other arm traced through another point of its ray: if `C'` is on the ray
from `A` through `C`, the angle `BAC'` is the angle `BAC`. (System E,
Diagram-angle 4) -/
theorem angle_onRay_right {C' : Point} (hC : OnRay C' A C) (hBA : B ≠ A) :
    ∠ B A C' = ∠ B A C :=
  angle_eq_of_onRay (OnRay.self hBA.symm) hC

/-! ## Adding angles -/

/-- If `R` lies between `P` and `Q`, and `V` is off the straight line `PQ`, then `VR`
falls within the angle `PVQ`, and that angle is made up of the angles `PVR` and
`RVQ`. (System E, Pasch 2 and Diagram-angle 2) -/
theorem angle_add_of_between {V P Q R : Point} (hPQV : Triangle P Q V) (h : Between P R Q) :
    ∠ P V Q = ∠ P V R + ∠ R V Q := by
  have hPQ : P ≠ Q := ne_of_between_ends h
  obtain ⟨N, hPN, hQN⟩ := Postulate1 P Q hPQ
  have hVN : ¬ OnLine V N := hPQV.off_line hPN hQN
  have hVP : V ≠ P := fun e => hVN (e ▸ hPN)
  have hVQ : V ≠ Q := fun e => hVN (e ▸ hQN)
  obtain ⟨L, hVL, hPL⟩ := Postulate1 V P hVP
  obtain ⟨M, hVM, hQM⟩ := Postulate1 V Q hVQ
  have hRN : OnLine R N := on_line_of_between_ends h hPN hQN
  have hPR : P ≠ R := ne_of_between h
  have hRQ : R ≠ Q := (ne_of_between (between_symm h)).symm
  have hLM : L ≠ M := by
    rintro rfl
    exact hVN (line_unique hPQ hPL hQM hPN hQN ▸ hVL)
  have hRL : ¬ OnLine R L := fun hR => hVN (line_unique hPR hPL hR hPN hRN ▸ hVL)
  have hRM : ¬ OnLine R M := fun hR => hVN (line_unique hRQ hR hQM hRN hQN ▸ hVM)
  exact angle_add_of_inside hVL hVM hPL hQM hVP hVQ hRL hRM hLM
    (same_side_symm (pasch2 (between_symm h) hQM hRM))
    (same_side_symm (pasch2 h hPL hRL))

/-! ## A straight line within an angle -/

/-- A straight line drawn from the corner of an angle through a point within it
crosses every finite straight line joining the two arms. If `D` lies within the
angle `BAC` (on `C`'s side of `AB` and on `B`'s side of `AC`), the ray from `A`
through `D` meets `BC` at a point `X` between `B` and `C`.

Euclid uses this without a word in I.10, where the bisector `CD` of the angle
`ACB` meets `AB` at `D`, and in I.21, where `BD` is "drawn through" to meet
`AC`. In Hilbert's geometry it is called the crossbar theorem. Here it follows
from System E: by Triple incidence 1 the straight line `AD` separates `B` from
`C`, so it crosses `BC` (Intersection 1, Pasch 4), and Pasch 2 and 3 put the
crossing on `D`'s side of `A`. -/
theorem crossbar {D : Point} (hDC : SameSideOf D C A B) (hDB : SameSideOf D B A C) :
    ∃ X : Point, Between B X C ∧ OnRay X A D := by
  have hBAC : Triangle B A C := hDB.symm.triangle.cab
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hBAC.ne₁₂.symm
  obtain ⟨M, hAM, hCM⟩ := Postulate1 A C hBAC.ne₂₃
  have hDCL : SameSide D C L := hDC.sameSide hAL hBL
  have hDBM : SameSide D B M := hDB.sameSide hAM hCM
  have hDL : ¬ OnLine D L := not_on_line_of_same_side hDCL
  have hAD : A ≠ D := fun e => hDL (e ▸ hAL)
  obtain ⟨N, hAN, hDN⟩ := Postulate1 A D hAD
  have hBN : ¬ OnLine B N := fun hB =>
    hDL ((line_unique hBAC.ne₁₂.symm hAN hB hAL hBL) ▸ hDN)
  have hCN : ¬ OnLine C N := fun hC =>
    (not_on_line_of_same_side hDBM) ((line_unique hBAC.ne₂₃ hAN hC hAM hCM) ▸ hDN)
  /- The straight line AD separates B from C (Triple incidence 1). -/
  have hBC_N : ¬ SameSide B C N := fun hBC =>
    triple_incidence1 hAL hAM hAN hBL hCM hDN (same_side_symm hDCL) hBC (same_side_symm hDBM)
  /- So it crosses BC, at a point X between B and C (Intersection 1, Pasch 4). -/
  obtain ⟨Q, hBQ, hCQ⟩ := Postulate1 B C hBAC.ne₁₃
  obtain ⟨hNQ, X, hXN, hXQ⟩ := lines_meet_of_opposite_sides ⟨hBN, hCN, hBC_N⟩ hBQ hCQ
  have hBXC : Between B X C :=
    pasch4 hNQ hXN hXQ hBQ hCQ hBAC.ne₁₃ (fun e => hBN (e ▸ hXN)) (fun e => hCN (e ▸ hXN))
      hBC_N
  /- X is on C's side of AB (Pasch 2), as D is, so not behind A (Pasch 3). -/
  have hXL : ¬ OnLine X L := fun hX =>
    hBAC.off_line hBL hAL ((line_unique (ne_of_between hBXC) hBL hX hBQ hXQ) ▸ hCQ)
  have hXC_L : SameSide X C L := pasch2 hBXC hBL hXL
  exact ⟨X, hBXC, hAD, fun e => hXL (e ▸ hAL), ⟨N, hAN, hDN, hXN⟩,
    fun hb => pasch3 hb hAL (same_side_trans (same_side_symm hXC_L) (same_side_symm hDCL))⟩

/-! ## One ray for one angle -/

/-- On one side of a straight line, only one ray from a point of it makes a given
angle with it. If `P` and `F` are on the same side of the straight line `DE`, and
the angle `EDP` is equal to the angle `EDF`, then `P` lies on the ray from `D`
through `F`.

Otherwise either `P` would lie within the angle `EDF`, or `F` within the angle
`EDP` (System E, Triple incidence 2 says which), and either way an angle would be
a part of an angle equal to it (Diagram-angle 1 and 2, with C.N. 5). Pasch 3
puts `P` on `F`'s side of `D` rather than behind it. -/
theorem onRay_of_angle_eq {D E F P : Point} (hPF : SameSideOf P F D E)
    (h : ∠ E D P = ∠ E D F) : OnRay P D F := by
  have hDE : D ≠ E := hPF.1
  obtain ⟨L, hD, hE⟩ := Postulate1 D E hDE
  have hPF' : SameSide P F L := hPF.2 L hD hE
  have hP_L : ¬ OnLine P L := not_on_line_of_same_side hPF'
  have hF_L : ¬ OnLine F L := not_on_line_of_same_side (same_side_symm hPF')
  have hDF : D ≠ F := fun e => hF_L (e ▸ hD)
  have hPD : P ≠ D := fun e => hP_L (e ▸ hD)
  obtain ⟨M, hD_M, hF_M⟩ := Postulate1 D F hDF
  have hLM : L ≠ M := fun e => hF_L (e ▸ hF_M)
  have hP_M : OnLine P M := by
    refine Classical.byContradiction fun hP_M => ?_
    /- Off the straight line `DF`, the point `P` makes some angle with `DF`
       (System E, Diagram-angle 1). -/
    have hFDP : 0 < ∠ F D P := Magnitude.pos_of_ne_zero fun h0 =>
      hP_M (same_ray_of_angle_eq_zero hDF hPD.symm hD_M hF_M h0).1
    by_cases hs : SameSide E P M
    · /- `P` lies within the angle `EDF`, so the angle `EDP` is a part of the
         angle `EDF` (Diagram-angle 2): the part would be equal to the whole. -/
      have hadd : ∠ E D F = ∠ E D P + ∠ P D F :=
        angle_add_of_inside hD hD_M hE hF_M hDE hDF hP_L hP_M hLM hs (same_side_symm hPF')
      rw [h, angle_symm hPD hDF.symm] at hadd
      have hlt := CommonNotion5 (a := ∠ E D F) hFDP
      rw [← hadd] at hlt
      exact lt_irrefl _ hlt
    · /- `F` lies within the angle `EDP` (Triple incidence 2), so the angle
         `EDF` is a part of the angle `EDP`: again the part would be equal to
         the whole. -/
      obtain ⟨N, hD_N, hP_N⟩ := Postulate1 D P hPD.symm
      have hEF_N : SameSide E F N :=
        triple_incidence2 hD hD_M hD_N hE hF_M hP_N (same_side_symm hPF') hs hP_M hDE.symm
      have hF_N : ¬ OnLine F N := fun hF_N =>
        hP_M (line_unique hDF hD_N hF_N hD_M hF_M ▸ hP_N)
      have hLN : L ≠ N := fun e => hP_L (e ▸ hP_N)
      have hadd : ∠ E D P = ∠ E D F + ∠ F D P :=
        angle_add_of_inside hD hD_N hE hP_N hDE hPD.symm hF_L hF_N hLN hEF_N hPF'
      rw [h] at hadd
      have hlt := CommonNotion5 (a := ∠ E D F) hFDP
      rw [← hadd] at hlt
      exact lt_irrefl _ hlt
  /- And `P` is on `F`'s side of `D`, not beyond `D`: a point between `P` and
     `F` would put them on opposite sides of `DE` (Pasch 3). -/
  exact ⟨hDF, hPD, ⟨M, hD_M, hF_M, hP_M⟩, fun hb => pasch3 hb hD hPF'⟩

end Elements
