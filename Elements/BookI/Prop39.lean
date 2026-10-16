import Elements.Figure.Basics
import Elements.BookI.Prop30
import Elements.BookI.Prop31
import Elements.BookI.Prop37
import Elements.BookI.HelpersParallels

/-!
# Book I, Proposition 39

Euclid's text, in Heath's translation: [`heath/I/39.md`](../../heath/I/39.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- Equal triangles which are on the same base and on the same side are also in the same parallels. -/
theorem Prop39 {A B C D : Point} (hABC : Triangle A B C) (hDBC : Triangle D B C)
    (heq : △ A B C = △ D B C) (hside : SameSideOf A D B C) (hAD : A ≠ D) :
    AreParallel A D B C := by
  -- Let ABC, DBC be equal triangles which are on the same base BC and on the same side of it;
  obtain ⟨BC, hB, hC⟩ := Postulate1 B C hABC.ne₂₃
  -- [I say that they are also in the same parallels.]
  -- And [For] let AD be joined;
  /- The parallel drawn through A will pass through D, and so be AD. -/
  -- I say that AD is parallel to BC.
  -- For, if not, let AE be drawn through the point A parallel to the straight line BC, [I. 31]
  /- I.31 names two points of the parallel through A. They serve to name the
     straight line K, which Euclid calls AE once E has been found. -/
  obtain ⟨U, V, hUAV, hUV⟩ := Prop31 hABC.ne₂₃ hABC.bca
  obtain ⟨K, hU_K, hV_K⟩ := Postulate1 U V hUV.1
  have hA_K : OnLine A K := on_line_of_between_ends hUAV hU_K hV_K
  have hKBC : Parallel K BC := hUV.parallel hU_K hV_K hB hC
  -- and let EC be joined.
  /- E is where the parallel meets BD. That the meeting exists is I.30,
     through Prop30.meet. -/
  obtain ⟨BD, hB_BD, hD_BD⟩ := Postulate1 B D hDBC.ne₁₂.symm
  have hD_BC : ¬ OnLine D BC := hDBC.bca.off_line hB hC
  have hBD_BC : BD ≠ BC := fun e => hD_BC (e ▸ hD_BD)
  obtain ⟨E, hE_BD, hE_K⟩ := Prop30.meet hKBC hB hB_BD hBD_BC
  have hE_BC : ¬ OnLine E BC := hKBC.not_onLine hE_K
  have hEBC : Triangle E B C := (Triangle.of_line hB hC hABC.ne₂₃ hE_BC).cab
  obtain ⟨EC, hE_EC, hC_EC⟩ := Postulate1 E C hEBC.ne₁₃
  -- Therefore the triangle ABC is equal to the triangle EBC; for it is on the same base BC
  -- with it and in the same parallels. [I. 37]
  have h37 : △ A B C = △ E B C :=
    Prop37 hABC hEBC ⟨K, BC, hKBC, hA_K, hE_K, hB, hC⟩
  -- But ABC is equal to DBC; therefore DBC is also equal to EBC, [C.N. 1] the greater to the
  -- less: which is impossible.
  have h1 : △ D B C = △ E B C := CommonNotion1 heq.symm h37.symm
  /- The parallel puts E on A's side of BC, hence on D's side. Since E is on
     BD, it lies on the ray from B through D. -/
  have hEB : E ≠ B := fun e => hE_BC (e ▸ hB)
  have hED_side : SameSideOf E D B C :=
    (SameSideOf.of_line hABC.ne₂₃ hB hC (hKBC.sameSide hE_K hA_K)).trans hside
  have hray : OnRay E B D :=
    OnRay.of_sameSideOf hED_side ⟨BD, hB_BD, hD_BD, hE_BD⟩ hEB
  have hED : E = D := by
    rcases lt_trichotomy ‖B E‖ ‖B D‖ with hlt | hequal | hgt
    · /- Euclid's figure: E lies between B and D, so EBC is less than DBC. -/
      have hBED : Between B E D :=
        hray.between_of_len_lt (OnRay.self hDBC.ne₁₂.symm) hlt
      have hless := area_lt_of_cut hDBC.cba hBED
      rw [← area_cba E B C, ← area_cba D B C, h1] at hless
      exact absurd rfl (Magnitude.ne_of_lt hless)
    · exact hray.eq_of_len_eq hequal
    · /- Proclus' other case: E lies on BD produced beyond D, so DBC is less. -/
      have hBDE : Between B D E :=
        (OnRay.self hDBC.ne₁₂.symm).between_of_len_lt hray hgt
      have hless := area_lt_of_cut hEBC.cba hBDE
      rw [← area_cba E B C, ← area_cba D B C, h1] at hless
      exact absurd rfl (Magnitude.ne_of_lt hless)
  -- Therefore AE is not parallel to BC.
  /- A parallel meeting BD away from D has been excluded: the parallel
     through A must pass through D itself. -/
  have hD_K : OnLine D K := hED ▸ hE_K
  -- Similarly we can prove that neither is any other straight line except AD; therefore AD is
  -- parallel to BC.
  have hpar : AreParallel A D B C := AreParallel.of_parallel hAD hABC.ne₂₃ hA_K hD_K hB hC hKBC
  -- Therefore etc.
  exact hpar

end Elements.BookI
