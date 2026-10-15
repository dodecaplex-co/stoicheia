import Elements.Figure.Basics

/-!
# Book I, Proposition 4

Euclid's text, in Heath's translation: [`heath/I/04.md`](../../heath/I/04.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid picks up the triangle `ABC` and lays it on `DEF`. In Lean the triangle
as laid down is `DB'C'`: its corner `A` is on `D`, and `B'`, `C'` are where `B`
and `C` land. The proof shows that they land on `E` and `F`.
-/

namespace Elements.BookI

open Tacit

/-- What Euclid sees in the figure but never says, when "the point B will also
coincide with E, because AB is equal to DE": a point `P` on the ray from `D`
through `E`, as far from `D` as `E` is, is `E` itself. This is Sir Henry
Savile's argument, which Heath reports (vol. 1, p. 250): otherwise `P` falls
short of `E` or beyond it, and either way the less would be equal to the
greater. -/
theorem Prop4.coincide {D E P : Point} (hP : OnRay P D E) (h : ‖D P‖ = ‖D E‖) :
    P = E := by
  obtain ⟨hDE, hPD, ⟨L, hD, hE, hPL⟩, hPDE⟩ := hP
  refine Classical.byContradiction fun (hPE : P ≠ E) => ?_
  rcases between_cases hPD.symm hPE hDE hD hPL hE with h' | h' | h'
  · /- `P` falls short of `E`: then `DE` is `DP` and `PE` together, and so
       greater than `DP`, which is equal to it. -/
    have hsum : ‖D P‖ + ‖P E‖ = ‖D P‖ := (len_add_of_between h').trans h.symm
    have hlt := CommonNotion5 (a := ‖D P‖) (len_pos hPE)
    rw [hsum] at hlt
    exact lt_irrefl _ hlt
  · /- `P` is on the far side of `D`, off the ray altogether. -/
    exact hPDE h'
  · /- `P` falls beyond `E`: then `DP` is `DE` and `EP` together, and so
       greater than `DE`, which is equal to it. -/
    have hsum : ‖D E‖ + ‖E P‖ = ‖D E‖ := (len_add_of_between h').trans h
    have hlt := CommonNotion5 (a := ‖D E‖) (len_pos hPE.symm)
    rw [hsum] at hlt
    exact lt_irrefl _ hlt

/-- What Euclid sees in the figure but never says, when "the straight line AC
will also coincide with DF, because the angle BAC is equal to the angle EDF":
on one side of the straight line `DE`, only one ray from `D` makes a given
angle with `DE`. So a point `P` on the same side of `DE` as `F`, with the angle
`EDP` equal to the angle `EDF`, lies on the ray from `D` through `F`. -/
theorem Prop4.on_ray {D E F P : Point} {L : Line} (hDE : D ≠ E) (hDF : D ≠ F)
    (hD : OnLine D L) (hE : OnLine E L) (hPD : P ≠ D) (hPF : SameSide P F L)
    (h : ∠ E D P = ∠ E D F) : OnRay P D F := by
  obtain ⟨M, hD_M, hF_M⟩ := Postulate1 D F hDF
  have hP_L : ¬ OnLine P L := not_on_line_of_same_side hPF
  have hF_L : ¬ OnLine F L := not_on_line_of_same_side (same_side_symm hPF)
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
        angle_add_of_inside hD hD_M hE hF_M hDE hDF hP_L hP_M hLM hs (same_side_symm hPF)
      rw [h, angle_symm hPD hDF.symm] at hadd
      have hlt := CommonNotion5 (a := ∠ E D F) hFDP
      rw [← hadd] at hlt
      exact lt_irrefl _ hlt
    · /- `F` lies within the angle `EDP` (Triple incidence 2), so the angle
         `EDF` is a part of the angle `EDP`: again the part would be equal to
         the whole. -/
      obtain ⟨N, hD_N, hP_N⟩ := Postulate1 D P hPD.symm
      have hEF_N : SameSide E F N :=
        triple_incidence2 hD hD_M hD_N hE hF_M hP_N (same_side_symm hPF) hs hP_M hDE.symm
      have hF_N : ¬ OnLine F N := fun hF_N =>
        hP_M (line_unique hDF hD_N hF_N hD_M hF_M ▸ hP_N)
      have hLN : L ≠ N := fun e => hP_L (e ▸ hP_N)
      have hadd : ∠ E D P = ∠ E D F + ∠ F D P :=
        angle_add_of_inside hD hD_N hE hP_N hDE hPD.symm hF_L hF_N hLN hEF_N hPF
      rw [h] at hadd
      have hlt := CommonNotion5 (a := ∠ E D F) hFDP
      rw [← hadd] at hlt
      exact lt_irrefl _ hlt
  /- And `P` is on `F`'s side of `D`, not beyond `D`: a point between `P` and
     `F` would put them on opposite sides of `DE` (Pasch 3). -/
  exact ⟨hDF, hPD, ⟨M, hD_M, hF_M, hP_M⟩, fun hb => pasch3 hb hD hPF⟩

/-- If two triangles have the two sides equal to two sides respectively, and have the angles
contained by the equal straight lines equal, they will also have the base equal to the base, the
triangle will be equal to the triangle, and the remaining angles will be equal to the remaining
angles respectively, namely those which the equal sides subtend. -/
theorem Prop4 {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
    (hAB : ‖A B‖ = ‖D E‖) (hAC : ‖A C‖ = ‖D F‖) (hA : ∠ B A C = ∠ E D F) :
    ‖B C‖ = ‖E F‖ ∧ △ A B C = △ D E F ∧ ∠ A B C = ∠ D E F ∧ ∠ A C B = ∠ D F E := by
  -- Let ABC, DEF be two triangles having the two sides AB, AC equal to the two sides DE, DF
  -- respectively, namely AB to DE and AC to DF, and the angle BAC equal to the angle EDF.
  have hBA : B ≠ A := hABC.ne₁₂.symm
  have hCA : C ≠ A := hABC.ne₁₃.symm
  have hCB : C ≠ B := hABC.ne₂₃.symm
  have hDE : D ≠ E := hDEF.ne₁₂
  have hDF : D ≠ F := hDEF.ne₁₃
  have hFE : F ≠ E := hDEF.ne₂₃.symm
  -- I say that the base BC is also equal to the base EF, the triangle ABC will be equal to the
  -- triangle DEF, and the remaining angles will be equal to the remaining angles respectively,
  -- namely those which the equal sides subtend, that is, the angle ABC to the angle DEF, and
  -- the angle ACB to the angle DFE.
  -- For, if the triangle ABC be applied to the triangle DEF,
  /- Euclid lays the triangle along the straight line DE, on the side where F
     is. Lean needs that line by name, and F off it. -/
  obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hDE
  have hF_DE : ¬ OnLine F DE := fun hF => hDEF ⟨DE, hD_DE, hE_DE, hF⟩
  -- and if the point A be placed on the point D
  -- and the straight line AB on DE,
  /- This is superposition, the one rule that moves a figure (System E §3.7, in
     LeanEuclid's form). The triangle ABC, laid down with A on D, becomes the
     triangle DB'C': B' is on the ray from D through E, C' is on the same side
     of DE as F, and every side and angle is kept. -/
  obtain ⟨B', C', hB'_DE, hB'_ray, hC'_side, hDB', hB'C', hC'D, hB'DC', hDC'B', hC'B'D⟩ :=
    superposition hABC hD_DE hE_DE hDE hF_DE
  have hB'D : B' ≠ D := ne_of_len_eq ((len_symm B' D).trans hDB') hBA.symm
  have hC'D' : C' ≠ D := ne_of_len_eq hC'D hCA
  have hB'C'' : B' ≠ C' := ne_of_len_eq hB'C' hCB.symm
  -- then the point B will also coincide with E, because AB is equal to DE.
  have hDB'_DE : ‖D B'‖ = ‖D E‖ := hDB'.trans hAB
  have hB'E : B' = E :=
    Prop4.coincide ⟨hDE, hB'D, ⟨DE, hD_DE, hE_DE, hB'_DE⟩, hB'_ray⟩ hDB'_DE
  -- Again, AB coinciding with DE,
  have hEDC' : ∠ E D C' = ∠ B' D C' := CommonNotion4.angle hB'E.symm rfl rfl
  -- the straight line AC will also coincide with DF, because the angle BAC is equal to the
  -- angle EDF;
  have hEDC'_EDF : ∠ E D C' = ∠ E D F := hEDC'.trans (hB'DC'.trans hA)
  have hC'_ray : OnRay C' D F := Prop4.on_ray hDE hDF hD_DE hE_DE hC'D' hC'_side hEDC'_EDF
  -- hence the point C will also coincide with the point F, because AC is again equal to DF.
  have hDC'_DF : ‖D C'‖ = ‖D F‖ :=
    (len_symm D C').trans (hC'D.trans ((len_symm C A).trans hAC))
  have hC'F : C' = F := Prop4.coincide hC'_ray hDC'_DF
  -- But B also coincided with E;
  -- hence the base BC will coincide with the base EF.
  -- [For if, when B coincides with E and C with F, the base BC does not coincide with the base
  -- EF, two straight lines will enclose a space: which is impossible.
  /- Heiberg brackets this passage as an early scholium. Lean has no need of
     it: a finite straight line is fixed by its ends, so once B' is E and C'
     is F, the base B'C' simply is EF. -/
  -- Therefore the base BC will coincide with EF] and will be equal to it. [C.N. 4]
  have hBC : ‖B C‖ = ‖E F‖ := hB'C'.symm.trans (CommonNotion4 hB'E hC'F)
  -- Thus the whole triangle ABC will coincide with the whole triangle DEF,
  have hcoincide : △ D B' C' = △ D E F := CommonNotion4.triangle rfl hB'E hC'F
  -- and will be equal to it.
  /- Being moved does not change the triangle: DB'C' has the same sides and
     angles as ABC, so the same area (System E, Metric 9). -/
  have hmoved : △ A B C = △ D B' C' :=
    area_congruent hDB'.symm hB'C'.symm hC'D.symm
      ((angle_symm hBA.symm hCB).trans (hC'B'D.symm.trans (angle_symm hB'C''.symm hB'D.symm)))
      ((angle_symm hCB.symm hCA.symm).trans (hDC'B'.symm.trans (angle_symm hC'D'.symm hB'C'')))
      ((angle_symm hCA hBA).trans (hB'DC'.symm.trans (angle_symm hB'D hC'D')))
  have harea : △ A B C = △ D E F := hmoved.trans hcoincide
  -- And the remaining angles will also coincide with the remaining angles and will be equal to
  -- them,
  -- the angle ABC to the angle DEF,
  have hB : ∠ A B C = ∠ D E F :=
    (angle_symm hBA.symm hCB).trans
      (hC'B'D.symm.trans ((CommonNotion4.angle hC'F hB'E rfl).trans (angle_symm hFE hDE)))
  -- and the angle ACB to the angle DFE.
  have hC : ∠ A C B = ∠ D F E := hDC'B'.symm.trans (CommonNotion4.angle rfl hC'F hB'E)
  -- Therefore etc.
  exact ⟨hBC, harea, hB, hC⟩
  -- (Being) what it was required to prove.

end Elements.BookI
