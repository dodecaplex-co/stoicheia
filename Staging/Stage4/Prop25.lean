import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop04
import Elements.BookI.Prop06
import Elements.BookI.Prop10
import Elements.BookI.Prop11
import Elements.BookI.Prop17
import Elements.BookI.Prop23
import Elements.BookI.Prop24
import Elements.BookIII.Prop09
import Elements.BookIII.Prop10
import Elements.BookIII.Prop25
import Elements.Foundations.DefinitionsIII
import Elements.Figure.Chords

/-!
# Stage 4, staged: III.25 restated

Statements before proofs (brief 0006, stage 4). It uses stage 3's arcs (`Arc`, `OnArc`,
`Arc.meets`).

Today III.25 is handed the circle whose segment it completes. Restated, its construction core
receives the segment only as a predicate `S` on points, with the meeting fact Euclid reads off
it (a straight line drawn from within the base into the segment meets its circumference), and
never sees a circle or a centre. It returns B, D, E and the circle γ described with centre E
(Postulate 3) through A, B and C. III.9 moves out: `Prop25.complete`, a separate theorem,
shows that for the arc of a circle α, γ is α, and every point of the arc is on γ.

**The statement is the pair.** The core's conclusion does not say that γ is the circle the
segment came from: S need not lie on any circle, and nothing in the conclusion puts S on γ.
Heath's "the complete circle of which it is a segment" is carried by `Prop25.complete`, for S
the arc of a given circle α. So the statement brief 0006 freezes for III.25 is the core
together with `Prop25.complete`: the record lists the companions, its scope describes the
main theorem together with them, and its note and the page say which declaration carries
which clause.

When frozen, the core replaces `Elements.BookIII.Prop25`; here it is
`Elements.BookIII.Staging.Prop25`. `Staging.Prop25.of_circle` checks the interfaces: from the
core, `Arc.meets` and `Prop25.complete`, today's statement follows. It stays, as the companion
"III.25 of_circle", so that today's statement keeps its certificate.
-/

namespace Elements.BookIII

open Tacit

/-- **III.25's circle is the segment's circle.** Let A, C be points of a circle α with a
centre, and B a point of its arc on P's side of AC (B on P's side). Any circle γ, with a
centre, through A, B and C is α, and every point of the arc AC on P's side is on γ.

To be proved: α and γ meet at the three points A, B, C, so they are one circle [III. 10] (or
E is the centre of α [III. 9], and `circle_eq`).

A companion of III.25 ("III.25 complete"): its correctness argument, kept apart from the
construction core. It carries Heath's "of which it is a segment". -/
theorem Prop25.complete {A C P B E : Point} {α γ : Circle} (hα : ∃ O : Point, Centre O α)
    (hA : OnCircle A α) (hC : OnCircle C α) (hB : OnArc B ⟨α, A, C, P⟩)
    (hBP : SameSideOf B P A C) (hE : Centre E γ) (hAγ : OnCircle A γ) (hBγ : OnCircle B γ)
    (hCγ : OnCircle C γ) :
    γ = α ∧ ∀ X : Point, OnArc X ⟨α, A, C, P⟩ → OnCircle X γ := by
  /- B is on P's side of AC, so off the straight line AC: A, B and C are three different
     points of α. They are on γ too, so EA, EB and EC are equal, being radii of γ
     [I. Def. 15], and E is the centre of α [III. 9]. -/
  have hABC : Triangle A B C := hBP.triangle.acb
  have hEα : Centre E α := Prop9 hα hA hB.1 hC hABC.ne₁₂ hABC.ne₂₃ hABC.ne₁₃
    (Definition15 hE hAγ hBγ) (Definition15 hE hBγ hCγ)
  /- So γ and α have one centre, E, and one radius, EA: they are one circle. -/
  have hγ : γ = α := circle_eq hE hEα hAγ hA rfl
  /- Every point of the arc is on α, and so on γ. -/
  refine ⟨hγ, ?_⟩
  intro X hX
  rw [hγ]
  exact hX.1

end Elements.BookIII

namespace Elements.BookIII.Staging

open Tacit

/-- Given a segment of a circle, to describe the complete circle of which it is a segment. -/
theorem Prop25 {A C P : Point} {S : Point → Prop} (hP : ¬ Collinear A C P)
    (hmeet : ∀ X Y : Point, Between A X C → SameSideOf Y P A C →
      ∃ B : Point, S B ∧ OnRay B X Y) :
    ∃ (B D E : Point) (γ : Circle), S B ∧ SameSideOf B P A C ∧ Between A D C ∧
      ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E γ ∧ OnCircle A γ ∧ OnCircle B γ ∧
      OnCircle C γ ∧ Collinear D B E ∧
      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧
      (∠ A B D < ∠ B A D → SameSideOf E B A C) := by
  -- Let ABC be the given segment of a circle;
  have hAC : A ≠ C := (show Triangle A C P from hP).ne₁₂
  -- thus it is required to describe the complete circle belonging to the segment ABC, that is,
  -- of which it is a segment.
  -- For let AC be bisected at D, let DB be drawn from the point D at right angles to AC, and
  -- let AB be joined;
  obtain ⟨D, hADC, hAD⟩ := BookI.Prop10 hAC
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hAC
  have hD_L : OnLine D L := on_line_of_between_ends hADC hA_L hC_L
  obtain ⟨X, hXP, hX⟩ := BookI.Prop11 hAC ⟨L, hA_L, hC_L, hD_L⟩ hP
  /- The perpendicular meets the segment's circumference: the meeting fact, for D within the
     base and X on P's side, gives B, a point of S on the ray from D through X. -/
  obtain ⟨B, hB, hBray⟩ := hmeet D X hADC hXP
  have hAD' : A ≠ D := ne_of_between hADC
  have hCD' : C ≠ D := ne_of_between (between_symm hADC)
  /- The ray from D through X lies on P's side of AC, so B, on it, is on that side too. -/
  have hBP_DA : SameSideOf B P D A := SameSideOf.of_onRay hBray
    (SameSideOf.of_line hAD'.symm hD_L hA_L (hXP.sameSide hA_L hC_L))
  have hBP : SameSideOf B P A C :=
    SameSideOf.of_line hAC hA_L hC_L (hBP_DA.sameSide hD_L hA_L)
  have hB_L : ¬ OnLine B L := hBP.triangle.off_line hA_L hC_L
  have hBD : B ≠ D := hBray.2.1
  obtain ⟨N, hD_N, hX_N⟩ := Postulate1 D X hBray.1
  have hB_N : OnLine B N := hBray.onLine hD_N hX_N
  have hADB : ∠ A D B = ∟ := by
    rw [angle_onRay_right hBray hAD']
    exact hX A ⟨L, hA_L, hC_L, hA_L⟩ hAD'
  have hABD : Triangle A B D := (Triangle.of_line hA_L hD_L hAD' hB_L).acb
  have hAB : A ≠ B := hABD.ne₁₂
  have hA_N : ¬ OnLine A N := fun hA_N => hB_L ((line_unique hAD' hA_N hD_N hA_L hD_L) ▸ hB_N)
  -- the angle ABD is then greater than, equal to, or less than the angle BAD.
  rcases lt_trichotomy (∠ B A D) (∠ A B D) with h | h | h
  -- First let it be greater;
  -- and on the straight line BA, and at the point A on it, let the angle BAE be constructed
  -- equal to the angle ABD; let DB be drawn through to E, and let EC be joined.
  · obtain ⟨G, F, hF, hGD, hGAF⟩ := BookI.Prop23 hAB hABD hABD
    have hGA : G ≠ A := hGD.triangle.ne₁₃.symm
    have hBAG : ∠ B A G = ∠ A B D :=
      (angle_onRay_left hF hGA).symm.trans ((angle_symm hF.2.1 hGA).trans hGAF)
    obtain ⟨M, hA_M, hB_M⟩ := Postulate1 A B hAB
    obtain ⟨K, hA_K, hG_K⟩ := Postulate1 A G hGA.symm
    /- Postulate 5 makes AG and DB produced meet, for the angles GAB, ABD are less than two
       right angles, ABD being less than a right angle [I. 17]. -/
    have hABD_lt : ∠ A B D < ∟ := by
      have h17 := (BookI.Prop17 hABD).1
      rw [angle_symm hBD hAD', hADB] at h17
      exact Magnitude.lt_of_add_lt_add_right h17
    obtain ⟨E, hE_K, hE_N, hEG⟩ := Postulate5 hG_K hA_K hA_M hB_M hB_N hD_N hAB
      (hGD.sameSide hA_M hB_M)
      (by rw [angle_symm hGA hAB.symm, hBAG]; exact Magnitude.add_self_lt_add_self hABD_lt)
    have hEG' : SameSideOf E G A B := SameSideOf.of_line hAB hA_M hB_M hEG
    have hED' : SameSideOf E D A B := hEG'.trans hGD
    have hEA : E ≠ A := hEG'.triangle.ne₁₃.symm
    have hEB : E ≠ B := hEG'.triangle.ne₂₃.symm
    have hEray : OnRay E A G := OnRay.of_sameSideOf hEG' ⟨K, hA_K, hG_K, hE_K⟩ hEA
    have hBAE : ∠ B A E = ∠ A B D := (angle_onRay_right hEray hAB.symm).trans hBAG
    have hEray' : OnRay E B D := OnRay.of_sameSideOf hED'.swap ⟨N, hB_N, hD_N, hE_N⟩ hEB
    /- E is beyond D: were it D, or between B and D, the angle BAE would not be greater than
       BAD. -/
    have hED : E ≠ D := fun e => by rw [e] at hBAE; rw [hBAE] at h; exact lt_irrefl _ h
    have hBDE : Between B D E := by
      rcases between_cases hBD hED.symm hEB.symm hB_N hD_N hE_N with h' | h' | h'
      · exact h'
      · exact absurd (between_symm h') hEray'.2.2.2
      · have hlt := angle_lt_of_between (V := A) (Triangle.of_line hD_N hB_N hBD.symm hA_N)
          (between_symm h')
        rw [angle_symm hEA hAB.symm, angle_symm hAD'.symm hAB.symm, hBAE] at hlt
        exact absurd (lt_trans hlt h) (lt_irrefl _)
    -- Then, since the angle ABE is equal to the angle BAE,
    have hABE : ∠ A B E = ∠ B A E := by
      rw [angle_onRay_right hEray' hAB, hBAE]
    -- the straight line EB is also equal to EA. [I. 6]
    have hEBA : Triangle E B A := (Triangle.of_line hB_N hE_N hEB.symm hA_N).bac
    have hEB_EA : ‖E B‖ = ‖E A‖ := BookI.Prop6 hEBA (by
      rw [angle_symm hEB hAB, hABE, angle_symm hAB.symm hEA])
    -- And, since AD is equal to DC,
    have hDA_DC : ‖D A‖ = ‖D C‖ := (len_symm D A).trans hAD
    -- and DE is common,
    have hDE : ‖D E‖ = ‖D E‖ := rfl
    -- the two sides AD, DE are equal to the two sides CD, DE respectively;
    -- and the angle ADE is equal to the angle CDE, for each is right;
    have hADE : ∠ A D E = ∟ := by
      rw [← adjacent_eq_of_right hB_N hE_N hBDE hA_N (by rw [angle_symm hBD hAD']; exact hADB),
        angle_symm hBD hAD', hADB]
    have hE_L : ¬ OnLine E L := fun hE_L =>
      hB_L ((line_unique hED hE_N hD_N hE_L hD_L) ▸ hB_N)
    have hCDE : ∠ C D E = ∟ := by
      rw [angle_symm hCD' hED, ← adjacent_eq_of_right hA_L hC_L hADC hE_L hADE, hADE]
    -- therefore the base AE is equal to the base CE.
    have hAE : ‖A E‖ = ‖C E‖ :=
      (BookI.Prop4 (Triangle.of_line hD_L hA_L hAD'.symm hE_L)
        (Triangle.of_line hD_L hC_L hCD'.symm hE_L) hDA_DC hDE
        (hADE.trans hCDE.symm)).1
    -- But AE was proved equal to BE;
    have h1 : ‖E A‖ = ‖E B‖ := hEB_EA.symm
    -- therefore BE is also equal to CE;
    have h2 : ‖E B‖ = ‖E C‖ := by rw [hEB_EA, len_symm E A, hAE, len_symm C E]
    -- therefore the three straight lines AE, EB, EC are equal to one another.
    -- Therefore the circle drawn with centre E and distance one of the straight lines AE, EB, EC
    -- will also pass through the remaining points and will have been completed. [III. 9]
    /- Postulate 3 describes the circle γ with centre E through A; EB and EC are equal to
       EA, so B and C are on it too. That γ is the given circle, Heath's [III. 9] step, is
       carried by `Prop25.complete`. -/
    obtain ⟨γ, hE, hAγ⟩ := Postulate3 E A hEA
    have hBγ : OnCircle B γ := on_circle_of_len_eq hE hAγ h1.symm
    have hCγ : OnCircle C γ := on_circle_of_len_eq hE hAγ (h1.trans h2).symm
    -- Therefore, given a segment of a circle, the complete circle has been described.
    -- And it is manifest that the segment ABC is less than a semicircle, because the centre E
    -- happens to be outside it.
    have hEB_AC : OppositeSidesOf E B A C :=
      OppositeSidesOf.of_line hAC hA_L hC_L ⟨hE_L, hB_L, pasch3 (between_symm hBDE) hD_L⟩
    exact ⟨B, D, E, γ, hB, hBP, hADC, hAD, hADB, hE, hAγ, hBγ, hCγ,
      ⟨N, hD_N, hB_N, hE_N⟩, fun _ => hEB_AC,
      fun h' => absurd (h'.symm ▸ h) (lt_irrefl _),
      fun h' => absurd (lt_trans h h') (lt_irrefl _)⟩
  -- Similarly, even if the angle ABD be equal to the angle BAD,
  -- AD being equal to each of the two BD, DC,
  · have hDA_DB : ‖D A‖ = ‖D B‖ := BookI.Prop6 (Triangle.of_line hD_L hA_L hAD'.symm hB_L) (by
      rw [angle_symm hAD'.symm hAB.symm, h, angle_symm hAB hBD.symm])
    -- the three straight lines DA, DB, DC will be equal to one another,
    have hDB_DC : ‖D B‖ = ‖D C‖ := by rw [← hDA_DB, len_symm D A, hAD]
    -- D will be the centre of the completed circle,
    /- Postulate 3 describes the circle γ with centre D through A; DB and DC are equal to
       DA, so B and C are on it too. Heath gives no reference here: that γ is the given
       circle is III.9's step, as in the first case, and `Prop25.complete` carries it. -/
    obtain ⟨γ, hD, hAγ⟩ := Postulate3 D A hAD'.symm
    have hBγ : OnCircle B γ := on_circle_of_len_eq hD hAγ hDA_DB.symm
    have hCγ : OnCircle C γ := on_circle_of_len_eq hD hAγ (hDA_DB.trans hDB_DC).symm
    -- and ABC will clearly be a semicircle.
    exact ⟨B, D, D, γ, hB, hBP, hADC, hAD, hADB, hD, hAγ, hBγ, hCγ,
      ⟨N, hD_N, hB_N, hD_N⟩,
      fun h' => absurd (h ▸ h') (lt_irrefl _), fun _ => rfl,
      fun h' => absurd (h ▸ h') (lt_irrefl _)⟩
  -- But, if the angle ABD be less than the angle BAD,
  -- and if we construct, on the straight line BA and at the point A on it, an angle equal to
  -- the angle ABD, the centre will fall on DB within the segment ABC, and the segment ABC will
  -- clearly be greater than a semicircle.
  · obtain ⟨G, F, hF, hGD, hGAF⟩ := BookI.Prop23 hAB hABD hABD
    have hGA : G ≠ A := hGD.triangle.ne₁₃.symm
    have hBAG : ∠ B A G = ∠ A B D :=
      (angle_onRay_left hF hGA).symm.trans ((angle_symm hF.2.1 hGA).trans hGAF)
    /- The straight line AG falls within the angle BAD, and crosses BD at E. -/
    have hGB : SameSideOf G B A D := BookI.Prop24.within hGD.symm (by rw [hBAG]; exact h)
    obtain ⟨E, hBED, hEray⟩ := crossbar hGD hGB
    have hBAE : ∠ B A E = ∠ A B D := (angle_onRay_right hEray hAB.symm).trans hBAG
    have hE_N : OnLine E N := on_line_of_between_ends hBED hB_N hD_N
    have hED : E ≠ D := (ne_of_between (between_symm hBED)).symm
    have hEB : E ≠ B := (ne_of_between hBED).symm
    have hEA : E ≠ A := fun e => hA_N (e ▸ hE_N)
    /- As in the first case, EB is equal to EA [I. 6]. -/
    have hABE : ∠ A B E = ∠ B A E := by
      rw [angle_onRay_right (OnRay.of_between hBED) hAB, hBAE]
    have hEBA : Triangle E B A := (Triangle.of_line hB_N hE_N hEB.symm hA_N).bac
    have hEB_EA : ‖E B‖ = ‖E A‖ := BookI.Prop6 hEBA (by
      rw [angle_symm hEB hAB, hABE, angle_symm hAB.symm hEA])
    /- AE is equal to CE, for the angles at D are right [I. 4]. -/
    have hADE : ∠ A D E = ∟ := by
      rw [angle_onRay_right (OnRay.of_between (between_symm hBED)) hAD']; exact hADB
    have hE_L : ¬ OnLine E L := fun hE_L =>
      hB_L ((line_unique hED hE_N hD_N hE_L hD_L) ▸ hB_N)
    have hCDE : ∠ C D E = ∟ := by
      rw [angle_symm hCD' hED, ← adjacent_eq_of_right hA_L hC_L hADC hE_L hADE, hADE]
    have hAE : ‖A E‖ = ‖C E‖ :=
      (BookI.Prop4 (Triangle.of_line hD_L hA_L hAD'.symm hE_L)
        (Triangle.of_line hD_L hC_L hCD'.symm hE_L) (by rw [len_symm D A, hAD]) rfl
        (hADE.trans hCDE.symm)).1
    /- So the three straight lines AE, EB, EC are equal. -/
    have h1 : ‖E A‖ = ‖E B‖ := hEB_EA.symm
    have h2 : ‖E B‖ = ‖E C‖ := by rw [hEB_EA, len_symm E A, hAE, len_symm C E]
    /- Postulate 3 describes the circle γ with centre E through A; EB and EC are equal to
       EA, so B and C are on it too. Heath gives no reference here: that γ is the given
       circle is III.9's step, as in the first case, and `Prop25.complete` carries it. -/
    obtain ⟨γ, hE, hAγ⟩ := Postulate3 E A hEA
    have hBγ : OnCircle B γ := on_circle_of_len_eq hE hAγ h1.symm
    have hCγ : OnCircle C γ := on_circle_of_len_eq hE hAγ (h1.trans h2).symm
    /- E lies between B and D, and so on B's side of AC. -/
    have hEB_AC : SameSideOf E B A C :=
      SameSideOf.of_line hAC hA_L hC_L (pasch2 (between_symm hBED) hD_L hE_L)
    -- Therefore, given a segment of a circle, the complete circle has been described.
    exact ⟨B, D, E, γ, hB, hBP, hADC, hAD, hADB, hE, hAγ, hBγ, hCγ,
      ⟨N, hD_N, hB_N, hE_N⟩,
      fun h' => absurd (lt_trans h h') (lt_irrefl _),
      fun h' => absurd (h' ▸ h) (lt_irrefl _), fun _ => hEB_AC⟩
  -- Q. E. F.

/-- **Today's III.25, from the restated core.** Handed the circle ABC, the core run on the
points of its arc on P's side (which meet every straight line from within the base, by
`Arc.meets`) finds a circle that is ABC itself (`Prop25.complete`), so its centre E is the
centre of ABC. This is the statement III.25 has today (the `example` below checks it), and
it checks that the pieces fit. A companion of III.25 ("III.25 of_circle"), proved from the
core, `Arc.meets` and `Prop25.complete`. -/
theorem Prop25.of_circle {A C : Point} {ABC : Circle} (hABC : ∃ E : Point, Centre E ABC)
    (hA : OnCircle A ABC) (hC : OnCircle C ABC) :
    ∀ P : Point, ¬ Collinear A C P → ∃ B D E : Point, OnCircle B ABC ∧ SameSideOf B P A C ∧
      Between A D C ∧ ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E ABC ∧ Collinear D B E ∧
      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧
      (∠ A B D < ∠ B A D → SameSideOf E B A C) := by
  intro P hP
  have ha : Arc.Drawn ⟨ABC, A, C, P⟩ := ⟨hABC, hA, hC, hP⟩
  obtain ⟨B, D, E, γ, hSB, hBP, hADC, hAD, hADB, hE, hAγ, hBγ, hCγ, hDBE, k₁, k₂, k₃⟩ :=
    Prop25 (S := (OnArc · ⟨ABC, A, C, P⟩)) hP (fun _ _ hX hY => Arc.meets ha hX hY)
  obtain ⟨hγ, -⟩ := BookIII.Prop25.complete hABC hA hC hSB hBP hE hAγ hBγ hCγ
  rw [hγ] at hE
  exact ⟨B, D, E, hSB.1, hBP, hADC, hAD, hADB, hE, hDBE, k₁, k₂, k₃⟩

/-- The check: `Prop25.of_circle` has today's statement of III.25 (checked by Lean, up to
unfolding definitions). -/
example : type_of% @Elements.BookIII.Prop25 := @Prop25.of_circle

end Elements.BookIII.Staging
