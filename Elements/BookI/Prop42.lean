import Elements.Figure.Basics
import Elements.BookI.Prop10
import Elements.BookI.Prop23
import Elements.BookI.Prop30
import Elements.BookI.Prop31
import Elements.BookI.Prop38
import Elements.BookI.Prop41
import Elements.BookI.HelpersParallels

/-!
# Book I, Proposition 42

Euclid's text, in Heath's translation: [`heath/I/42.md`](../../heath/I/42.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- To construct, in a given rectilineal angle, a parallelogram equal to a given triangle. -/
theorem Prop42 {A B C D₁ D D₂ : Point} (hABC : Triangle A B C) (hD : Triangle D₁ D D₂) :
    ∃ E F G : Point, Between B E C ∧ SameSideOf F A B C ∧ Parallelogram F E C G ∧
      ∠ C E F = ∠ D₁ D D₂ ∧ quadArea F E C G = △ A B C := by
  -- Let ABC be the given triangle, and D the given rectilineal angle; thus it is required to
  -- construct in the rectilineal angle D a parallelogram equal to the triangle ABC.
  -- Let BC be bisected at E,
  obtain ⟨E, hBEC, hBE⟩ := Prop10 hABC.ne₂₃
  obtain ⟨BC, hB, hC⟩ := Postulate1 B C hABC.ne₂₃
  have hA_BC : ¬ OnLine A BC := hABC.bca.off_line hB hC
  have hE : OnLine E BC := on_line_of_between_ends hBEC hB hC
  have hEC : E ≠ C := (ne_of_between (between_symm hBEC)).symm
  -- and let AE be joined;
  /- The triangles ABE and AEC are named by their corners; the join needs no
     further object in Lean. -/
  -- on the straight line EC, and at the point E on it, let the angle CEF be constructed equal
  -- to the angle D; [I. 23]
  have hECA : Triangle E C A := Triangle.of_line hE hC hEC hA_BC
  obtain ⟨F₁, C₁, hC₁, hF₁, hang⟩ := Prop23 hEC hD hECA
  /- C₁ lies on the ray EC, and F₁ on A's side of EC. The parallel through A
     will determine F on the ray from E through F₁. -/
  -- through A let AG be drawn parallel to EC, and [I. 31]
  obtain ⟨AG, hA_AG, hAG⟩ := Prop31.line hA_BC
  /- The straight line through E and F₁ meets AG by I.30. Both F and F₁ lie on
     A's side of BC, so F is on the constructed ray. -/
  have hEF₁ : E ≠ F₁ := hF₁.triangle.ne₁₃
  obtain ⟨EF, hE_EF, hF₁_EF⟩ := Postulate1 E F₁ hEF₁
  have hEF_BC : EF ≠ BC := fun e => (hF₁.triangle.off_line hE hC) (e ▸ hF₁_EF)
  obtain ⟨F, hF_EF, hF_AG⟩ := Prop30.meet hAG hE hE_EF hEF_BC
  have hFA : SameSide F A BC := hAG.sameSide hF_AG hA_AG
  have hFE : F ≠ E := fun e => hAG.not_onLine hF_AG (e ▸ hE)
  have hFray : OnRay F E F₁ :=
    OnRay.of_sameSideOf ((SameSideOf.of_line hEC hE hC hFA).trans hF₁.symm)
      ⟨EF, hE_EF, hF₁_EF, hF_EF⟩ hFE
  -- through C let CG be drawn parallel to EF.
  /- It meets AG at G (`Prop31.parallelogram`). -/
  obtain ⟨G, hG_AG, hpar⟩ := Prop31.parallelogram hAG hF_AG hE hC hEC
  -- Then FECG is a parallelogram.
  have hFECG : Parallelogram F E C G := hpar
  -- And, since BE is equal to EC, the triangle ABE is also equal to the triangle AEC, for they
  -- are on equal bases BE, EC and in the same parallels BC, AG; [I. 38]
  have hABE : Triangle A B E := (Triangle.of_line hB hE (ne_of_between hBEC) hA_BC).cab
  have hAEC : Triangle A E C := hECA.cab
  have h38 : △ A B E = △ A E C :=
    Prop38 hABE hAEC hBE ⟨AG, BC, hAG, hA_AG, hA_AG, hB, hE, hE, hC⟩
  -- therefore the triangle ABC is double of the triangle AEC.
  have hABC_double : △ A B C = △ A E C + △ A E C := by
    rw [← area_cut (A := A) hBEC, h38]
  -- But the parallelogram FECG is also double of the triangle AEC, for it has the same base
  -- with it and is in the same parallels with it; [I. 41]
  have h41 : quadArea F E C G = △ E A C + △ E A C :=
    Prop41 hFECG ⟨AG, hF_AG, hG_AG, hA_AG⟩
  have hFECG_double : quadArea F E C G = △ A E C + △ A E C := by
    rw [h41, ← area_bac A E C]
  -- therefore the parallelogram FECG is equal to the triangle ABC.
  have hequal : quadArea F E C G = △ A B C := CommonNotion1 hFECG_double hABC_double
  -- And it has the angle CEF equal to the given angle D.
  have hCEF : ∠ C E F = ∠ D₁ D D₂ :=
    (angle_eq_of_onRay hC₁.symm hFray).trans ((angle_symm hC₁.2.1 hEF₁.symm).trans hang)
  -- Therefore the parallelogram FECG has been constructed equal to the given triangle ABC, in
  -- the angle CEF which is equal to D.
  exact ⟨E, F, G, hBEC, SameSideOf.of_line hABC.ne₂₃ hB hC hFA, hFECG, hCEF, hequal⟩
  -- Q. E. F.

end Elements.BookI
