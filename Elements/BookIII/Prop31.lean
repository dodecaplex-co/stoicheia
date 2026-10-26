import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Helpers
import Elements.BookI.Prop05
import Elements.BookI.Prop17
import Elements.BookI.Prop32
import Elements.BookIII.Prop02
import Elements.BookIII.Prop22
import Elements.BookIII.MixedAngles

/-!
# Book III, Proposition 31

Euclid's text, in Heath's translation: [`heath/III/31.md`](../../heath/III/31.md).
Below, each of Euclid's sentences is a `--` comment, and the Lean beneath carries it
out, with one exception. The closing sentences on the angles of the greater and the
less segment, each contained by a circumference and a straight line, are proved after
the theorem, by the companions `Prop31.greater` and `Prop31.less`, where each of those
angles is a mixed angle (`MixedAngle`), compared with a right angle near A; the `exact`
that follows the sentences returns only the clauses the theorem states. The companions
take for every straight line in the circle not through the centre what Euclid finds in
his figure: near A the right angle BAC lies within the angle of the greater segment, and
the less segment lies within the right angle CAF.
-/

namespace Elements.BookIII

open Tacit

/-- In a circle the angle in the semicircle is right, that in a greater segment less than a right
angle, and that in a less segment greater than a right angle; and further the angle of the
greater segment is greater than a right angle, and the angle of the less segment less than a
right angle. -/
theorem Prop31 {A B C E : Point} {ABCD : Circle} (hE : Centre E ABCD) (hA : OnCircle A ABCD)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hBEC : Between B E C) (hAB : A ≠ B)
    (hAC : A ≠ C) :
    ∠ B A C = ∟ ∧
      (∀ X : Point, OnCircle X ABCD → SameSideOf X B A C → ∠ A X C < ∟) ∧
      ∀ D : Point, OnCircle D ABCD → OppositeSidesOf B D A C → ∟ < ∠ A D C := by
  -- Let ABCD be a circle, let BC be its diameter, and E its centre, and let BA, AC, AD, DC be
  -- joined;
  have hABC : Triangle A B C :=
    Prop2.triangle hA hB hC hAB (ne_of_between_ends hBEC) hAC
  -- I say that the angle BAC in the semicircle BAC is right,
  -- the angle ABC in the segment ABC greater than the semicircle is less than a right angle,
  -- and the angle ADC in the segment ADC less than the semicircle is greater than a right
  -- angle.
  -- Let AE be joined, and let BA be carried through to F.
  obtain ⟨F, hBAF⟩ := produce hAB.symm
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hABC.ne₂₃
  have hE_L : OnLine E L := on_line_of_between_ends hBEC hB_L hC_L
  have hA_L : ¬ OnLine A L := hABC.bca.off_line hB_L hC_L
  have hEBA : Triangle E B A := Triangle.of_line hE_L hB_L (ne_of_between hBEC).symm hA_L
  have hECA : Triangle E C A :=
    Triangle.of_line hE_L hC_L (ne_of_between (between_symm hBEC)).symm hA_L
  -- Then, since BE is equal to EA,
  have hBE : ‖E B‖ = ‖E A‖ := Definition15 hE hB hA
  -- the angle ABE is also equal to the angle BAE. [I. 5]
  have h₁ : ∠ A B E = ∠ B A E := by
    rw [angle_symm hAB hEBA.ne₁₂, BookI.Prop5.base hEBA hBE, angle_symm hEBA.ne₁₃ hAB.symm]
  -- Again, since CE is equal to EA,
  have hCE : ‖E C‖ = ‖E A‖ := Definition15 hE hC hA
  -- the angle ACE is also equal to the angle CAE. [I. 5]
  have h₂ : ∠ A C E = ∠ C A E := by
    rw [angle_symm hAC hECA.ne₁₂, BookI.Prop5.base hECA hCE, angle_symm hECA.ne₁₃ hAC.symm]
  -- Therefore the whole angle BAC is equal to the two angles ABC, ACB.
  have hwhole : ∠ B A C = ∠ A B C + ∠ A C B := by
    rw [angle_add_of_between hABC.bca hBEC, ← angle_onRay_right (OnRay.of_between hBEC) hAB,
      ← angle_onRay_right (OnRay.of_between (between_symm hBEC)) hAC, h₁, h₂,
      angle_symm hECA.ne₁₃ hAC.symm]
  -- But the angle FAC exterior to the triangle ABC is also equal to the two angles ABC,
  -- ACB; [I. 32]
  have hext : ∠ F A C = ∠ A B C + ∠ A C B := by
    obtain ⟨h32, -⟩ := BookI.Prop32 hABC.cba hBAF
    rw [angle_symm (ne_of_between (between_symm hBAF)) hAC.symm, h32, add_comm,
      angle_symm hABC.ne₂₃.symm hAB]
  -- therefore the angle BAC is also equal to the angle FAC;
  have heq : ∠ B A C = ∠ F A C := hwhole.trans hext.symm
  -- therefore each is right; [I. Def. 10]
  /- Definition I.10 says each is right, for they are equal adjacent angles on the
     straight line BF, and each is then `∟` (Post. 4, as in I.11). -/
  obtain ⟨M, hB_M, hA_M⟩ := Postulate1 B A hAB.symm
  have hF_M : OnLine F M := on_line_of_between hBAF hB_M hA_M
  have hC_M : ¬ OnLine C M := fun h => hABC ⟨M, hA_M, hB_M, h⟩
  have hFAC : Triangle F A C :=
    Triangle.of_line hF_M hA_M (ne_of_between (between_symm hBAF)) hC_M
  have hright : ∠ B A C = ∟ ∧ ∠ F A C = ∟ :=
    ⟨Postulate4 ⟨F, hBAF, hABC.bac, heq.trans (angle_symm hFAC.ne₁₂ hFAC.ne₂₃.symm)⟩,
     Postulate4 ⟨B, between_symm hBAF, hFAC,
       heq.symm.trans (angle_symm hAB.symm hAC.symm)⟩⟩
  -- therefore the angle BAC in the semicircle BAC is right.
  have hBAC : ∠ B A C = ∟ := hright.1
  -- Next, since in the triangle ABC the two angles ABC, BAC are less than two right
  -- angles, [I. 17]
  have h17 : ∠ C A B + ∠ A B C < ∟ + ∟ := (BookI.Prop17 hABC).2.2
  -- and the angle BAC is a right angle,
  rw [angle_symm hAC.symm hAB.symm, hBAC] at h17
  -- the angle ABC is less than a right angle;
  have hABC' : ∠ A B C < ∟ := Magnitude.lt_of_add_lt_add_left h17
  -- and it is the angle in the segment ABC greater than the semicircle.
  -- Next, since ABCD is a quadrilateral in a circle,
  -- and the opposite angles of quadrilaterals in circles are equal to two right
  -- angles, [III. 22]
  have hless : ∀ D : Point, OnCircle D ABCD → OppositeSidesOf B D A C → ∟ < ∠ A D C := by
    intro D hD hBD
    have h22 := (Prop22 hB hC hD hA hBD.swap).2
    rw [angle_symm hABC.ne₂₃.symm hAB] at h22
    -- while the angle ABC is less than a right angle,
    -- therefore the angle ADC which remains is greater than a right angle;
    rcases lt_trichotomy ∟ (∠ A D C) with h | h | h
    · exact h
    · rw [← h] at h22
      exact absurd (CommonNotion3 h22 rfl) (Magnitude.ne_of_lt hABC')
    · have := add_lt_add_right (∠ A D C) hABC'
      rw [h22] at this
      have h' := add_lt_add_right ∟ h
      rw [add_comm (∠ A D C) ∟] at h'
      exact absurd (lt_trans this h') (lt_irrefl _)
  -- and it is the angle in the segment ADC less than the semicircle.
  /- Our statement covers every point X of the greater segment. With a point D of the less
     segment, III.22 makes the angle at X less than a right angle. -/
  have hgreater : ∀ X : Point, OnCircle X ABCD → SameSideOf X B A C → ∠ A X C < ∟ := by
    intro X hX hXB
    obtain ⟨D, hD, hDB⟩ := Prop2.oppositeSide hA hC hABC.acb
    have hXD : OppositeSidesOf X D A C := hXB.trans_opposite hDB.symm
    have h22 := (Prop22 hX hA hD hC hXD).2
    have hDAC : Triangle A D C := hXD.symm.triangle.acb
    rw [angle_symm hDAC.ne₂₃.symm hDAC.ne₁₂] at h22
    have hobtuse : ∟ < ∠ A D C := hless D hD hDB.symm
    rcases lt_trichotomy (∠ A X C) ∟ with h | h | h
    · exact h
    · rw [h, add_comm] at h22
      exact absurd (CommonNotion3 h22 rfl).symm (Magnitude.ne_of_lt hobtuse)
    · /- Were the angle at X greater than a right angle too, the two angles together
         would be greater than two right angles. -/
      have h₁ : ∟ + ∟ < ∠ A X C + ∟ := add_lt_add_right ∟ h
      have h₂ : ∠ A X C + ∟ < ∠ A X C + ∠ A D C := by
        rw [add_comm (∠ A X C) ∟, add_comm (∠ A X C) (∠ A D C)]
        exact add_lt_add_right (∠ A X C) hobtuse
      exact absurd (h22 ▸ lt_trans h₁ h₂) (lt_irrefl _)
  /- The angles of the segments below are proved after the theorem, by the companions
     `Prop31.greater` and `Prop31.less`, from the right angle BAC that the theorem returns
     and the right angle CAF beside it; the `exact` at the end returns only the claims of
     the statement. -/
  -- I say further that the angle of the greater segment, namely that contained by the
  -- circumference ABC and the straight line AC, is greater than a right angle;
  -- and the angle of the less segment, namely that contained by the circumference ADC and the
  -- straight line AC, is less than a right angle.
  -- This is at once manifest.
  -- For, since the angle contained by the straight lines BA, AC is right,
  -- the angle contained by the circumference ABC and the straight line AC is greater than a
  -- right angle.
  -- Again, since the angle contained by the straight lines AC, AF is right,
  -- the angle contained by the straight line CA and the circumference ADC is less than a right
  -- angle.
  -- Therefore etc.
  exact ⟨hBAC, hgreater, hless⟩
  -- Q. E. D.

/-! ## The angles of the segments

In Heath's letters: the circle ABCD with the diameter BC and the centre E, A on it, and BA
carried through to F. The angle of the greater segment is `MixedAngle.ofSegment A C ABCD B`,
contained by the circumference ABC and the straight line AC; the angle of the less segment
is `MixedAngle.ofSegment A C ABCD D`, for a point D on the other side of AC, contained by the
circumference ADC and the straight line AC. A right angle placed along AC on B's side is the
angle CAB, and on D's side the angle CAF. The steps take the theorem's first part, that the
angle BAC is right, as a hypothesis; the companions `Prop31.greater` and `Prop31.less` take
it from the theorem, for every straight line in the circle not through the centre. -/

/-- **The angle of the greater segment exceeds every right angle placed on its side.** The
angle CAR, placed along AC on B's side, is the angle CAB, for on one side one ray makes a
given angle; near A it lies within the circle (`near_inside_of_angle`); and every circle
about A holds whole circles within the circle and within the angle between AB and CA
produced beyond A, which are in the angle of the greater segment and not in CAB. -/
theorem Prop31.greater_gt_right {A B C E R : Point} {ABCD : Circle} (_hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hBEC : Between B E C) (hAB : A ≠ B) (hAC : A ≠ C) (hBAC : ∠ B A C = ∟)
    (hR : SameSideOf R B A C) (hCAR : ∠ C A R = ∟) :
    (MixedAngle.ofSegment A C ABCD B).Exceeds C R := by
  refine ⟨hR.triangle.bac, ?_⟩
  show LocallyLess A (WithinAngle C A R) (MixedAngle.ofSegment A C ABCD B).region
  have hABC : Triangle A B C :=
    Triangle.of_onCircle_centre hA hB hC hAB (ne_of_between_ends hBEC) hAC
  have hCAB : ∠ C A B = ∟ := by
    rw [angle_symm hAC.symm hAB.symm]; exact hBAC
  have hRray : OnRay R A B := onRay_of_angle_eq hR (hCAR.trans hCAB.symm)
  refine (locallyLess_congr (fun P => WithinAngle.congr (OnRay.self hAC) hRray)
    (fun _ => Iff.rfl)).2 ?_
  obtain ⟨γ₀, hγ₀, hnear⟩ :=
    near_inside_of_angle (Or.inr hA) (Or.inr hC) (Or.inr hB) hABC.bac.cba
  refine ⟨⟨γ₀, hγ₀, fun P hPγ hP => MixedAngle.region_ofSegment.2
    ⟨hP.1, hnear P hPγ (Or.inl hP)⟩⟩, ?_⟩
  /- CA produced beyond A to C′: its points are without the circle. -/
  obtain ⟨C', hCAC'⟩ := produce hAC.symm
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hAC
  have hC'_L : OnLine C' L := on_line_of_between hCAC' hC_L hA_L
  have hB_L : ¬ OnLine B L := hABC.acb.off_line hA_L hC_L
  have hBAC' : Triangle B A C' :=
    (Triangle.of_line hA_L hC'_L (ne_of_between (between_symm hCAC')).symm hB_L).cab
  have hC'col : Collinear A C C' := ⟨L, hA_L, hC_L, hC'_L⟩
  have hopp : OppositeSidesOf C C' A B :=
    (OppositeSidesOf.of_between hABC.bac hCAC').swap
  obtain ⟨N, hA_N, hB_N⟩ := Postulate1 A B hAB
  refine (near_across hBAC' (near_inside_of_ray hA (Or.inr hB) hAB)
    (fun P hP => OutsideCircle.of_between (Or.inr hC) (fun h => inside_not_on h hA)
      (hP.between hCAC'))).1.mono fun P hP => ?_
  obtain ⟨hPw, hPα⟩ := hP
  refine ⟨MixedAngle.region_ofSegment.2
    ⟨(sameSideOf_congr_collinear hAC hBAC'.ne₂₃.symm hC'col).1 hPw.2, hPα⟩, fun h' => ?_⟩
  exact ((hopp.oppositeSides hA_N hB_N).2.2)
    (same_side_trans (h'.2.sameSide hA_N hB_N) (hPw.1.sameSide hA_N hB_N))

/-- **The angle of the less segment is something.** For a point D on the other side of AC
from B, every circle about A holds a whole circle within the angle of the less segment: BA
produced to F, the points of AC near A are within the circle, those of AF are without it,
and the circumference crosses between them, within the angle CAF, which is on D's side of
AC (`near_across`). -/
theorem Prop31.less_nearVertex {A B C D E : Point} {ABCD : Circle} (_hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hBEC : Between B E C) (hAB : A ≠ B) (hAC : A ≠ C) (hBD : OppositeSidesOf B D A C) :
    NearVertexOpen A (MixedAngle.ofSegment A C ABCD D).region := by
  have hABC : Triangle A B C :=
    Triangle.of_onCircle_centre hA hB hC hAB (ne_of_between_ends hBEC) hAC
  obtain ⟨F, hBAF⟩ := produce hAB.symm
  have hBF : OppositeSidesOf B F A C := (OppositeSidesOf.of_between hABC.cab hBAF).swap
  have hDF : SameSideOf D F A C := OppositeSidesOf.sameSideOf hBD hBF
  exact (near_across hBF.symm.triangle.bac (near_inside_of_ray hA (Or.inr hC) hAC)
    (fun P hP => OutsideCircle.of_between (Or.inr hB) (fun h => inside_not_on h hA)
      (hP.between hBAF))).1.mono fun P hP =>
        MixedAngle.region_ofSegment.2 ⟨hP.1.1.trans hDF.symm, hP.2⟩

/-- **The angle of the less segment falls short of every right angle placed on its side.**
For a point D on the other side of AC from B, the angle of the less segment comes as near A
as we please (`Prop31.less_nearVertex`), and falls short of every right angle CAR placed
along AC on D's side, which is the angle CAF, BA being produced to F. The less segment lies
wholly within the angle CAF: a point within the circle on F's side of AC, and on AB or beyond
it, would give a point within the circle on the straight line AB outside AB itself (System
E, Circle 1, Pasch 2 and 3). And every circle about A holds whole circles within the angle
CAF and without the circle, which are not in the angle of the less segment. -/
theorem Prop31.less_lt_right {A B C D E R : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hBEC : Between B E C) (hAB : A ≠ B) (hAC : A ≠ C) (hBAC : ∠ B A C = ∟)
    (hBD : OppositeSidesOf B D A C) (hR : SameSideOf R D A C) (hCAR : ∠ C A R = ∟) :
    (MixedAngle.ofSegment A C ABCD D).FallsShort C R := by
  refine ⟨hR.triangle.bac, less_nearVertex hE hA hB hC hBEC hAB hAC hBD, ?_⟩
  show LocallyLess A (MixedAngle.ofSegment A C ABCD D).region (WithinAngle C A R)
  have hABC : Triangle A B C :=
    Triangle.of_onCircle_centre hA hB hC hAB (ne_of_between_ends hBEC) hAC
  obtain ⟨F, hBAF⟩ := produce hAB.symm
  obtain ⟨N, hA_N, hB_N⟩ := Postulate1 A B hAB
  have hF_N : OnLine F N := on_line_of_between hBAF hB_N hA_N
  have hC_N : ¬ OnLine C N := hABC.off_line hA_N hB_N
  have hAF : A ≠ F := ne_of_between (between_symm hBAF) |>.symm
  have hBF : OppositeSidesOf B F A C := (OppositeSidesOf.of_between hABC.cab hBAF).swap
  have hDF : SameSideOf D F A C := OppositeSidesOf.sameSideOf hBD hBF
  /- The angle CAF is right, as its adjacent angle BAC is (I.13, `adjacent_eq_of_right`). -/
  have hCAF : ∠ C A F = ∟ := by
    rw [← (adjacent_eq_of_right hB_N hF_N hBAF hC_N hBAC), hBAC]
  have hRray : OnRay R A F := onRay_of_angle_eq (hR.trans hDF) (hCAR.trans hCAF.symm)
  refine (locallyLess_congr (fun _ => Iff.rfl)
    (fun P => WithinAngle.congr (OnRay.self hAC) hRray)).2 ?_
  have hFcol : Collinear A B F := ⟨N, hA_N, hB_N, hF_N⟩
  obtain ⟨M, hA_M, hC_M⟩ := Postulate1 A C hAC
  /- No point is on both B's side and D's side of AC. -/
  have hnotB : ∀ T : Point, SameSideOf T D A C → ¬ SameSideOf T B A C := fun T hTD hTB =>
    (hBD.oppositeSides hA_M hC_M).2.2 ((hTB.symm.trans hTD).sameSide hA_M hC_M)
  /- A point T within the circle on the straight line AB lies between A and B (System E,
     Circle 1), and so on B's side of AC (Pasch 2). -/
  have hseg : ∀ T : Point, OnLine T N → InsideCircle T ABCD → SameSideOf T B A C :=
    fun T hT hTα => SameSideOf.of_between_line ⟨M, hA_M, hC_M, hA_M⟩ (sameSideOf_self hABC.acb)
      (between_of_inside_chord hT hA_N hB_N hTα hA hB hAB)
  /- So a point within the circle on D's side of AC is on C's side of AB: were it on AB, it
     would be on B's side of AC; were it on the other side of AB, the straight line from it to
     C would cross AB within the circle (System E, Intersection 1, and III.2), at a point on
     D's side of AC (Pasch 2). -/
  have hside : ∀ P : Point, SameSideOf P D A C → InsideCircle P ABCD → SameSideOf P C A B := by
    intro P hPD hPα
    by_cases hP_N : OnLine P N
    · exact absurd (hseg P hP_N hPα) (hnotB P hPD)
    refine SameSideOf.of_line hAB hA_N hB_N (Classical.byContradiction fun hs => ?_)
    obtain ⟨T, hT_N, hPTC⟩ := OppositeSides.exists_between ⟨hP_N, hC_N, hs⟩
    have hTα : InsideCircle T ABCD :=
      InsideCircle.of_between (Or.inl hPα) (Or.inr hC) hPTC
    have hTD : SameSideOf T D A C :=
      SameSideOf.of_between_line ⟨M, hA_M, hC_M, hC_M⟩ hPD (between_symm hPTC)
    exact hnotB T hTD (hseg T hT_N hTα)
  obtain ⟨γ₀, hγ₀⟩ := exists_circle_about A
  refine ⟨⟨γ₀, hγ₀, fun P _ hP => ?_⟩, ?_⟩
  · obtain ⟨hPD, hPα⟩ := MixedAngle.region_ofSegment.1 hP
    exact ⟨hPD.trans hDF, (sameSideOf_congr_collinear hAB hAF.symm hFcol).2 (hside P hPD hPα)⟩
  · exact (near_across hBF.symm.triangle.bac
      (near_inside_of_ray hA (Or.inr hC) hAC)
      (fun P hP => OutsideCircle.of_between (Or.inr hB) (fun h => inside_not_on h hA)
        (hP.between hBAF))).2.mono fun P hP =>
          ⟨hP.1, fun h' => hP.2.1 (MixedAngle.region_ofSegment.1 h').2⟩

/-- For a straight line AC in a circle about E that does not pass through the centre, the
diameter through C ends at a point B of the circle, other than A, on the centre's side of AC
(System E, Intersections 5 and Pasch 2). -/
theorem Prop31.diameter_through {A C E : Point} {α : Circle} (hE : Centre E α)
    (hC : OnCircle C α) (hACE : ¬ Collinear A C E) :
    ∃ B : Point, OnCircle B α ∧ Between B E C ∧ A ≠ B ∧ SameSideOf E B A C := by
  have hCE : C ≠ E := ne_of_centre_of_on hE hC
  obtain ⟨L, hC_L, hE_L⟩ := Postulate1 C E hCE
  obtain ⟨B, hB, hB_L, hBEC⟩ := line_circle_beyond (centre_inside hE) hE_L hC_L hCE
  have hAB : A ≠ B := by
    rintro rfl
    exact hACE ⟨L, hB_L, hC_L, hE_L⟩
  have hACB : Triangle A C B := by
    rintro ⟨M, hA_M, hC_M, hB_M⟩
    have e : L = M := line_unique (ne_of_between_ends hBEC) hB_L hC_L hB_M hC_M
    exact hACE ⟨M, hA_M, hC_M, e ▸ hE_L⟩
  obtain ⟨M, hA_M, hC_M⟩ := Postulate1 A C hACB.ne₁₂
  exact ⟨B, hB, hBEC, hAB,
    SameSideOf.of_between_line ⟨M, hA_M, hC_M, hC_M⟩ (sameSideOf_self hACB) (between_symm hBEC)⟩

/-- **III.31: the angle of the greater segment is greater than a right angle.** For any
straight line AC in the circle ABCD about E, not through the centre, at either end A: the
angle of the segment on the centre's side, the greater segment, is a mixed angle as Euclid
draws it, and it exceeds every right angle CAR placed along AC on that side. Euclid's figure
is the case where B, the far end of the diameter through C, names the segment
(`Prop31.diameter_through`). -/
theorem Prop31.greater {A C E : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hC : OnCircle C ABCD) (hACE : ¬ Collinear A C E) :
    (MixedAngle.ofSegment A C ABCD E).WellFormed ∧
      ∀ R : Point, SameSideOf R E A C → ∠ C A R = ∟ →
        (MixedAngle.ofSegment A C ABCD E).Exceeds C R := by
  have hAC : A ≠ C := (show Triangle A C E from hACE).ne₁₂
  obtain ⟨B, hB, hBEC, hAB, hEB⟩ := diameter_through hE hC hACE
  have hBAC := (Prop31 hE hA hB hC hBEC hAB hAC).1
  refine ⟨MixedAngle.wellFormed_ofSegment hA hC hAC hACE, fun R hR hCAR => ?_⟩
  exact ⟨hR.triangle.bac, (locallyLess_congr (fun _ => Iff.rfl)
    (fun _ => MixedAngle.ofSegment_congr (OnRay.self hAC) hEB)).2
    (greater_gt_right hE hA hB hC hBEC hAB hAC hBAC (hR.trans hEB) hCAR).2⟩

/-- **III.31: the angle of the less segment is less than a right angle.** For any straight
line AC in the circle ABCD about E, not through the centre, at either end A, and a point D on
the other side of AC from the centre: the angle of the segment on D's side, the less segment,
is a mixed angle as Euclid draws it, and it falls short of every right angle CAR placed along
AC on that side. -/
theorem Prop31.less {A C D E : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hC : OnCircle C ABCD) (hACE : ¬ Collinear A C E)
    (hED : OppositeSidesOf E D A C) :
    (MixedAngle.ofSegment A C ABCD D).WellFormed ∧
      ∀ R : Point, SameSideOf R D A C → ∠ C A R = ∟ →
        (MixedAngle.ofSegment A C ABCD D).FallsShort C R := by
  have hAC : A ≠ C := (show Triangle A C E from hACE).ne₁₂
  obtain ⟨B, hB, hBEC, hAB, hEB⟩ := diameter_through hE hC hACE
  have hBAC := (Prop31 hE hA hB hC hBEC hAB hAC).1
  exact ⟨MixedAngle.wellFormed_ofSegment hA hC hAC hED.symm.triangle,
    fun R hR hCAR =>
      less_lt_right hE hA hB hC hBEC hAB hAC hBAC (hEB.symm.trans_opposite hED) hR hCAR⟩

end Elements.BookIII
