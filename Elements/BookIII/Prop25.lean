import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop04
import Elements.BookI.Prop06
import Elements.BookI.Prop10
import Elements.BookI.Prop11
import Elements.BookI.Prop17
import Elements.BookI.Prop23
import Elements.BookI.Prop24
import Elements.BookIII.Prop02
import Elements.BookIII.Prop09

/-!
# Book III, Proposition 25

Euclid's text, in Heath's translation: [`heath/III/25.md`](../../heath/III/25.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

III.25 is a construction, and its statement keeps apart the construction core and the
argument that it is correct (FORMALIZATION, section 4, of which it is the pilot). `Prop25`,
the core, is given only the segment's base AC, a point P on its side, and its points as a
predicate `S`, with the fact Euclid reads off the figure: a straight line drawn from a point
within the base towards P's side meets the segment's circumference. It never sees a circle
or a centre. It returns B in `S`, the point D bisecting AC with the angle ADB right, and the
circle γ described with centre E through A (Postulate 3), which passes through B and C; E
lies beyond AC, at D, or on B's side, as the angles at A and B decide: Euclid's three cases.

**The statement is the pair.** The core does not say that γ is the circle the segment came
from: `S` need not lie on any circle, and nothing puts it on γ. Heath's "the complete circle
of which it is a segment" is carried by the companion `Prop25.complete`: for `S` the arc of
a circle α with a centre, any circle through A, B and C with a centre is α, and holds every
point of the arc. Euclid's step "[III. 9]", which finds the centre of the given circle, is
there.

The companion `Prop25.of_circle` keeps III.25's statement before brief 0006 restated it,
handed the whole circle: the core, run on the points of the arc, which meet every straight
line drawn from within the base (`Prop25.meets`, by III.2), finds a circle that is the given
one (`Prop25.complete`), so its centre is the given circle's.
-/

namespace Elements.BookIII

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

/-- **III.25's circle is the segment's circle.** Let A, C be points of a circle α with a
centre, and B a point of its arc on P's side of AC (B on P's side). Any circle γ, with a
centre, through A, B and C is α, and every point of the arc AC on P's side is on γ.

A companion of III.25 ("III.25 complete"): its correctness argument, kept apart from the
construction core. It carries Heath's "of which it is a segment", and Euclid's step
"[III. 9]": A, B and C are three points of α on γ, so EA, EB, EC are equal, E is the centre
of α, and one centre with one radius makes one circle (`circle_eq`). [III. 9] -/
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

/-- The centre's position in III.25 determines whether the segment is less than a
semicircle, a semicircle or greater, and compares its circumference with two right angles.
B is on P's side of AC, and D lies between A and C. The construction's three conclusions
place E across AC from B, at D, or on B's side. `Prop25.complete` identifies the constructed
circle with the given segment's circle, carrying these conclusions to that segment.
[I. 5, I. 32, III. 2, III. 20, III. 21, III. 22] -/
theorem Prop25.kind {A B C D E P : Point} {γ : Circle}
    (hBP : SameSideOf B P A C) (hADC : Between A D C)
    (hE : Centre E γ) (hAγ : OnCircle A γ) (hCγ : OnCircle C γ)
    (hless : ∠ B A D < ∠ A B D → OppositeSidesOf E B A C)
    (hequal : ∠ A B D = ∠ B A D → E = D)
    (hgreater : ∠ A B D < ∠ B A D → SameSideOf E B A C) :
    Arc.Drawn ⟨γ, A, C, P⟩ ∧
      (∠ B A D < ∠ A B D →
        Arc.Less ⟨γ, A, C, P⟩ ∧
          circumference γ A P C < ∟ + ∟) ∧
      (∠ A B D = ∠ B A D →
        Arc.Semicircle ⟨γ, A, C, P⟩ ∧
          circumference γ A P C = ∟ + ∟) ∧
      (∠ A B D < ∠ B A D →
        Arc.Greater ⟨γ, A, C, P⟩ ∧
          ∟ + ∟ < circumference γ A P C) := by
  /- B and P are on the same side of AC, so P is off AC and the arc is drawn. -/
  have hP : Triangle A C P := hBP.symm.triangle
  refine ⟨⟨⟨E, hE⟩, hAγ, hCγ, hP⟩, ?_, ?_, ?_⟩
  · intro h
    /- E is opposite B across AC, hence opposite P. -/
    have hEP : OppositeSidesOf E P A C := (hBP.symm.trans_opposite (hless h).symm).symm
    exact ⟨⟨E, hE, hEP⟩, Circumference.lt_semicircle hE hAγ hCγ hEP⟩
  · intro h
    /- E is D, between A and C, so AC is a diameter. -/
    have hAEC : Between A E C := by rw [hequal h]; exact hADC
    obtain ⟨L, hA_L, hE_L, hC_L⟩ := collinear_of_between hAEC
    exact ⟨⟨E, hE, ⟨L, hA_L, hC_L, hE_L⟩⟩,
      Circumference.semicircle hE hAγ hCγ hAEC hP⟩
  · intro h
    /- E is on B's side of AC, hence on P's side. -/
    have hEP : SameSideOf E P A C := (hgreater h).trans hBP
    exact ⟨⟨E, hE, hEP⟩, Circumference.gt_semicircle hE hAγ hCγ hEP⟩

/-- **A straight line from within the base meets the arc.** For a drawn arc, a ray from a point
X between the ends of the base, through a point Y on the arc's side, meets the arc. It is the
meeting fact that III.25's construction core reads off the segment it is given, for the
segment of a circle. Brief 0006 planned it for Book Zero, as `Arc.meets`; it rests on III.2,
and Book Zero cites no proposition, so it is here, beside the one proof that uses it.

Proved: X is within the circle [III. 2], so the straight line XY, produced beyond X backwards
and then forwards, meets the circle on Y's side (Intersections 5, with Pasch 3 for the side).
[III. 2] -/
theorem Prop25.meets {a : Arc} (ha : a.Drawn) {X Y : Point} (hX : Between a.B X a.C)
    (hY : SameSideOf Y a.K a.B a.C) : ∃ Q : Point, OnArc Q a ∧ OnRay Q X Y := by
  /- X lies within the circle, since it is between the ends of the base [III. 2], and Y is
     off the straight line BC. -/
  have hX_in : InsideCircle X a.circle := Prop2 ha.1 ha.2.1 ha.2.2.1 X hX
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 a.B a.C hY.1
  have hX_L : OnLine X L := on_line_of_between_ends hX hB_L hC_L
  have hY_L : ¬ OnLine Y L := hY.triangle.off_line hB_L hC_L
  have hXY : X ≠ Y := fun e => hY_L (e ▸ hX_L)
  /- Draw XY, and produce it backwards, beyond X away from Y, to meet the circle at A
     (Intersections 5). -/
  obtain ⟨N, hX_N, hY_N⟩ := Postulate1 X Y hXY
  obtain ⟨A, hA, hA_N, hAXY⟩ := line_circle_beyond hX_in hX_N hY_N hXY.symm
  /- A is off BC: otherwise XY and BC would share A and X, and Y would lie on BC. So BC,
     through X, separates A from Y (Pasch 3). -/
  have hAX : A ≠ X := fun e => inside_not_on hX_in (e ▸ hA)
  have hA_L : ¬ OnLine A L := fun hA_L =>
    hY_L ((line_unique hAX hA_N hX_N hA_L hX_L) ▸ hY_N)
  have hAY : OppositeSidesOf A Y a.B a.C :=
    OppositeSidesOf.of_line hY.1 hB_L hC_L ⟨hA_L, hY_L, pasch3 hAXY hX_L⟩
  /- Produce AX forwards, beyond X, to meet the circle at Q (Intersections 5). Q is off
     BC for the same reason. -/
  obtain ⟨Q, hQ, hQ_N, hQXA⟩ := line_circle_beyond hX_in hX_N hA_N hAX
  have hQX : Q ≠ X := fun e => inside_not_on hX_in (e ▸ hQ)
  have hQ_L : ¬ OnLine Q L := fun hQ_L =>
    hY_L ((line_unique hQX hQ_N hX_N hQ_L hX_L) ▸ hY_N)
  /- BC separates Q from A too (Pasch 3), so Q is on Y's side, hence on K's side. -/
  have hQA : OppositeSidesOf Q A a.B a.C :=
    OppositeSidesOf.of_line hY.1 hB_L hC_L ⟨hQ_L, hA_L, pasch3 hQXA hX_L⟩
  have hQY : SameSideOf Q Y a.B a.C := hQA.symm.sameSideOf hAY
  /- Q lies on the arc and on XY. X cannot lie between Q and Y, since they are on one
     side of BC (Pasch 3); so Q lies on the ray from X through Y. -/
  exact ⟨Q, ⟨hQ, Or.inl (hQY.trans hY)⟩,
    hXY, hQX, ⟨N, hX_N, hY_N, hQ_N⟩,
    fun hQXY => pasch3 hQXY hX_L (hQY.sameSide hB_L hC_L)⟩

/-- **III.25, handed the whole circle** (companion of III.25, "III.25 of_circle"). Handed
the circle ABC, the core run on the points of its arc on P's side (which meet every
straight line from within the base, by `Prop25.meets`) finds a circle that is ABC itself
(`Prop25.complete`), so its centre E is the centre of ABC. This is III.25's statement
before brief 0006 restated it, kept so that it keeps its certificate; proved from the core,
`Prop25.meets` and `Prop25.complete`, it checks that the pieces fit. -/
theorem Prop25.of_circle {A C : Point} {ABC : Circle} (hABC : ∃ E : Point, Centre E ABC)
    (hA : OnCircle A ABC) (hC : OnCircle C ABC) :
    ∀ P : Point, ¬ Collinear A C P → ∃ B D E : Point, OnCircle B ABC ∧ SameSideOf B P A C ∧
      Between A D C ∧ ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E ABC ∧ Collinear D B E ∧
      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧
      (∠ A B D < ∠ B A D → SameSideOf E B A C) := by
  intro P hP
  have ha : Arc.Drawn ⟨ABC, A, C, P⟩ := ⟨hABC, hA, hC, hP⟩
  obtain ⟨B, D, E, γ, hSB, hBP, hADC, hAD, hADB, hE, hAγ, hBγ, hCγ, hDBE, k₁, k₂, k₃⟩ :=
    Prop25 (S := (OnArc · ⟨ABC, A, C, P⟩)) hP (fun _ _ hX hY => Prop25.meets ha hX hY)
  obtain ⟨hγ, -⟩ := Prop25.complete hABC hA hC hSB hBP hE hAγ hBγ hCγ
  rw [hγ] at hE
  exact ⟨B, D, E, hSB.1, hBP, hADC, hAD, hADB, hE, hDBE, k₁, k₂, k₃⟩

end Elements.BookIII
