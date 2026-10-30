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

`Prop39` takes the vertices A and D apart, as Euclid's "let AD be joined" needs. The
companion after it, `Prop39.general`, lets them be one point, and then the parallel is the
one through it (I.31).
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
  /- AD names the straight line through the distinct vertices A and D; that it is
     parallel to BC remains to be proved. -/
  -- I say that AD is parallel to BC.
  have hpar : AreParallel A D B C := by
    -- For, if not, let AE be drawn through the point A parallel to the straight line BC, [I. 31]
    refine Classical.byContradiction fun hnot => ?_
    /- The parallel through A is the straight line K (`Prop31.line`), which Euclid
       calls AE once E has been found. -/
    obtain ⟨K, hA_K, hKBC⟩ := Prop31.line (hABC.bca.off_line hB hC)
    -- and let EC be joined.
    /- E is where the parallel meets BD (`Prop30.meet`). EC is named by its ends,
       as a side of the triangle EBC, so nothing is drawn for the join. -/
    obtain ⟨BD, hB_BD, hD_BD⟩ := Postulate1 B D hDBC.ne₁₂.symm
    have hD_BC : ¬ OnLine D BC := hDBC.bca.off_line hB hC
    have hBD_BC : BD ≠ BC := fun e => hD_BC (e ▸ hD_BD)
    obtain ⟨E, hE_BD, hE_K⟩ := Prop30.meet hKBC hB hB_BD hBD_BC
    have hE_BC : ¬ OnLine E BC := hKBC.not_onLine hE_K
    have hEBC : Triangle E B C := (Triangle.of_line hB hC hABC.ne₂₃ hE_BC).cab
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
    /- If E were D, the parallel through A would be AD, contrary to the supposition. -/
    have hED : E ≠ D := fun e => hnot
      (AreParallel.of_parallel hAD hABC.ne₂₃ hA_K (e ▸ hE_K) hB hC hKBC)
    /- In Heath's figure E is between B and D, so EBC is the less. The same-side
       condition excludes B between E and D. If E is beyond D, DBC is the less:
       the other order gives the same contradiction by `area_lt_of_cut`. -/
    rcases between_cases hEB.symm hED hDBC.ne₁₂.symm hB_BD hE_BD hD_BD with h | h | h
    · have hless := area_lt_of_cut hDBC.cba h
      rw [← area_cba E B C, ← area_cba D B C] at hless
      exact Magnitude.ne_of_lt hless h1.symm
    · exact hray.2.2.2 h
    · have hless := area_lt_of_cut hEBC.cba h
      rw [← area_cba D B C, ← area_cba E B C] at hless
      exact Magnitude.ne_of_lt hless h1
  -- Therefore AE is not parallel to BC.
  -- Similarly we can prove that neither is any other straight line except AD; therefore AD is
  -- parallel to BC.
  /- The contradiction excludes a proposed parallel meeting BD away from D,
     and discharges the supposition that AD is not parallel to BC. -/
  -- Therefore etc.
  exact hpar

/-- **I.39, general** (companion of I.39). Equal triangles ABC, DBC on the same base BC of
the straight line L, and on the same side of it, are in the same parallels: A and D lie on
one straight line parallel to L. The vertices may be one point, and then the parallel is the
one through it (I.31). -/
theorem Prop39.general {A B C D : Point} {L : Line} (hABC : Triangle A B C)
    (hDBC : Triangle D B C) (hB : OnLine B L) (hC : OnLine C L)
    (heq : △ A B C = △ D B C) (hside : SameSide A D L) :
    ∃ M : Line, Parallel M L ∧ OnLine A M ∧ OnLine D M := by
  by_cases hAD : A = D
  · /- One vertex: ABC and DBC are one triangle, and the parallel to L through
       its vertex is the straight line I.31 draws (`Prop31.line`). -/
    obtain ⟨M, hA_M, hML⟩ := Prop31.line (hABC.bca.off_line hB hC)
    exact ⟨M, hML, hA_M, hAD ▸ hA_M⟩
  · /- Two vertices: L is the straight line BC, so D is on A's side of BC, and
       I.39 makes AD, which "let AD be joined" draws, parallel to BC. -/
    have hpar : AreParallel A D B C :=
      Prop39 hABC hDBC heq (SameSideOf.of_line hABC.ne₂₃ hB hC hside) hAD
    obtain ⟨M, hA_M, hD_M⟩ := Postulate1 A D hAD
    exact ⟨M, hpar.parallel hA_M hD_M hB hC, hA_M, hD_M⟩

end Elements.BookI
