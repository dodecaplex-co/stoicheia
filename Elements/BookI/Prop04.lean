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
  /- The converse of C.N. 4 that Heath points out: on the ray from D through E,
     the one point as far from D as E is, is E itself. This is Savile's argument,
     `OnRay.eq_of_len_eq` in Book Zero. -/
  have hDB'_DE : ‖D B'‖ = ‖D E‖ := hDB'.trans hAB
  have hB'E : B' = E :=
    OnRay.eq_of_len_eq ⟨hDE, hB'D, ⟨DE, hD_DE, hE_DE, hB'_DE⟩, hB'_ray⟩ hDB'_DE
  -- Again, AB coinciding with DE,
  have hEDC' : ∠ E D C' = ∠ B' D C' := CommonNotion4.angle hB'E.symm rfl rfl
  -- the straight line AC will also coincide with DF, because the angle BAC is equal to the
  -- angle EDF;
  have hEDC'_EDF : ∠ E D C' = ∠ E D F := hEDC'.trans (hB'DC'.trans hA)
  /- On F's side of DE only one ray from D makes this angle with DE
     (`onRay_of_angle_eq` in Book Zero), so C' lies on the ray from D through F. -/
  have hC'_ray : OnRay C' D F :=
    onRay_of_angle_eq (SameSideOf.of_line hDE hD_DE hE_DE hC'_side) hEDC'_EDF
  -- hence the point C will also coincide with the point F, because AC is again equal to DF.
  have hDC'_DF : ‖D C'‖ = ‖D F‖ :=
    (len_symm D C').trans (hC'D.trans ((len_symm C A).trans hAC))
  have hC'F : C' = F := OnRay.eq_of_len_eq hC'_ray hDC'_DF
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
