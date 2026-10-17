import Elements.Figure.Basics
import Elements.BookI.Prop23
import Elements.BookI.Prop27

/-!
# Book I, Proposition 31

Euclid's text, in Heath's translation: [`heath/I/31.md`](../../heath/I/31.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid's point D, "taken at random on BC", is taken between B and C, as in his
figure. Then B and C lie on either side of AD, and I.23 can be asked to build
the angle DAE on B's side, away from C, so that EAD and ADC are alternate
angles, as I.27 needs.

After the proposition, `Prop31.line` says it of straight lines drawn and named: the
parallel through a point off a straight line, as one straight line. Proofs from
I.37 on cite it, directly or through `Prop31.parallelogram`.
-/

namespace Elements.BookI

open Tacit

/-- Through a given point to draw a straight line parallel to a given straight line. -/
theorem Prop31 {A B C : Point} (hBC : B ≠ C) (hA : ¬ Collinear B C A) :
    ∃ E F : Point, Between E A F ∧ AreParallel E F B C := by
  -- Let A be the given point, and BC the given straight line;
  /- The given point is off the given straight line: otherwise there would be no
     parallel through it. -/
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hBC
  have hA_BC : ¬ OnLine A BC := fun h => hA ⟨BC, hB_BC, hC_BC, h⟩
  -- thus it is required to draw through the point A a straight line parallel to the straight
  -- line BC.
  -- Let a point D be taken at random on BC,
  /- Taken between B and C, as Euclid's figure has it. -/
  obtain ⟨D, hD_BC, hBDC, -⟩ := exists_point_between hB_BC hC_BC hBC []
  -- and let AD be joined;
  /- Lean needs only that A and D are two points: D is on BC and A is not.
     Then ADC and ADB are triangles, and B and C lie on either side of AD,
     since D is between them (`OppositeSidesOf.of_between`). -/
  have hAD : A ≠ D := fun h => hA_BC (h ▸ hD_BC)
  have hADC : Triangle A D C :=
    (Triangle.of_line hD_BC hC_BC (ne_of_between (between_symm hBDC)).symm hA_BC).cab
  have hADB : Triangle A D B :=
    (Triangle.of_line hD_BC hB_BC (ne_of_between hBDC).symm hA_BC).cab
  have hBC_AD : OppositeSidesOf B C A D := OppositeSidesOf.of_between hADB hBDC
  -- on the straight line DA, and at the point A on it, let the angle DAE be constructed equal
  -- to the angle ADC [I. 23];
  /- I.23 builds the angle at A with one arm along the ray from A through D (it
     passes through a point D₁ of that ray) and the other through a point E on
     whichever side of AD we ask for. We ask for B's side, away from C. The angle
     D₁AE is the angle DAE, its arms being the same rays (`angle_onRay_left`). -/
  obtain ⟨D₁, E, hD₁, hEB, hD₁AE⟩ := Prop23 hAD hADC hADB
  have hAE : A ≠ E := hEB.triangle.ne₁₃
  have hDAE : ∠ D A E = ∠ A D C := (angle_onRay_left hD₁ hAE.symm).symm.trans hD₁AE
  -- and let the straight line AF be produced in a straight line with EA.
  obtain ⟨F, hEAF⟩ := produce hAE.symm
  -- Then, since the straight line AD falling on the two straight lines BC, EF has made the
  -- alternate angles EAD, ADC equal to one another,
  /- Alternate: E is on B's side of AD, and so on the other side from C
     (`SameSideOf.trans_opposite`). -/
  have hEC : OppositeSidesOf E C A D := hEB.trans_opposite hBC_AD
  have hEAD : ∠ E A D = ∠ A D C := (angle_symm hAE.symm hAD.symm).trans hDAE
  -- therefore EAF is parallel to BC. [I. 27]
  /- I.27 with EF for its AB, BC for its CD, and AD falling on them at A
     and D. -/
  have hpar : AreParallel E F B C := Prop27 hEAF hBDC hEC hEAD
  -- Therefore through the given point A the straight line EAF has been drawn parallel to the
  -- given straight line BC.
  exact ⟨E, F, hEAF, hpar⟩
  -- Q. E. F.

/-- I.31 said of straight lines drawn and named: through a point A off the
straight line L there is a straight line K parallel to L. I.31 gives two points
of it, one on either side of A, and Postulate 1 joins them. [I. 31] -/
theorem Prop31.line {A : Point} {L : Line} (hA : ¬ OnLine A L) :
    ∃ K : Line, OnLine A K ∧ Parallel K L := by
  obtain ⟨B, hB_L, -⟩ := exists_point_on_line L []
  obtain ⟨C, hC_L, hC⟩ := exists_point_on_line L [B]
  have hBC : B ≠ C := fun e => hC (e ▸ List.mem_singleton_self B)
  obtain ⟨E, F, hEAF, hpar⟩ := Prop31 hBC fun ⟨M, hB_M, hC_M, hA_M⟩ =>
    hA ((line_unique hBC hB_M hC_M hB_L hC_L) ▸ hA_M)
  obtain ⟨K, hE_K, hF_K⟩ := Postulate1 E F hpar.1
  exact ⟨K, on_line_of_between_ends hEAF hE_K hF_K, hpar.parallel hE_K hF_K hB_L hC_L⟩

end Elements.BookI
