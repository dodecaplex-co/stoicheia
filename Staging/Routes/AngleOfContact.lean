import Elements.Figure.Basics
import Elements.BookI.Prop12
import Elements.BookI.Prop23
import Elements.BookIII.Prop02
import Elements.BookIII.Prop16
import Elements.BookIII.Prop18
import Staging.Stage4b.MixedAngles

/-!
# The angle of contact in general, after III.18

Issue #130. III.16 compares two angles contained by a straight line and a circumference with
rectilineal angles. In its figure, where the straight line AE is drawn at right angles to the
diameter AB from its extremity A, "the angle of the semicircle is greater, and the remaining
angle less, than any acute rectilineal angle". III.18 says that a straight line touching a
circle is perpendicular to the straight line joined from the centre to the point of contact.
So, after III.18, every touching straight line is III.16's, and III.16's angle of contact,
with its comparisons, belongs to every one of them. This file stages that, as new
statements:

* `Prop18.diameter` and `Prop18.parts`: let AE touch the circle about D at A, and let AD be
  produced beyond the centre to B, so that AB lies along the diameter through the point of
  contact. By III.18, AE is at right angles to AB, which is III.16's figure, and III.16's two
  parts hold for AE.
* `Prop18.branch`, the section's one helper: let AE touch the circle about D at A; a point B′
  that names a branch of the angle of contact along AE is on the diameter's side of AE, and
  near A the angle of contact it names is the diameter's.
* `Prop18.contact_locallyEqual`: the angle of contact, read near A, does not depend on the
  straight line from A into the circle that names its branch of the circumference.
* `Prop18.contact_lt`, `Prop18.semicircle_gt` and `Prop18.acute`: the angle of contact is
  less than every acute rectilineal angle placed at A along AE on the circle's side, and the
  angle of the semicircle greater than every acute rectilineal angle placed along the
  diameter on E's side; and every acute rectilineal angle can be so placed [I. 23]. For the
  angle of the semicircle, the touching straight line AE only names the side of AB, and the
  angle of the semicircle does not depend on it: on any side of the diameter its comparison
  follows from III.16, with the perpendicular to AB at A drawn on that side by I.11.

Main has none of these. The prototype of the mixed angles, `Staging/Stage4b/MixedAngles.lean`,
whose words, and those of its facts it needs that rest on neither Circle 2 nor Circle 3, this
file uses, proves III.16's comparisons in III.16's figure only, and says that for a touching
straight line in general the angle of contact is not proved there. The route is Euclid's
order: III.18 makes the touching straight line III.16's, and III.16's comparisons do the
rest. Nothing later is cited. Those comparisons are argued as the mixed angles argue them,
directly from III.16's second part, where Euclid argues by reductio: the straight line of an
acute angle falls within the circle, so near A the acute angle lies within the angle of the
semicircle, with room to spare, and the angle of contact within the acute angle.

Nothing here rests on Circle 2 or Circle 3. Many of the prototype's theorems do, through
Circle 2 or Circle 3 itself: among them its steps in a circle (`exists_onRay_inside`,
`near_inside_of_angle`, `exists_near_across`, `near_inside_of_ray` and
`Prop16.sameSideOf_of_inside`) and those built on them. So the first section proves again the
steps of III.16's comparisons that these statements need, following the move of the mixed
angles into `Elements` (issue #57), which proves them in `Elements/Figure/Regions.lean`,
`Elements/BookIII/MixedAngles.lean` and `Elements/BookIII/Prop16.lean`. Where the prototype
uses Circle 2 or 3, they argue by III.2 (`Prop2.within`), except `exists_onRay_inside`, which
replaces Circle 2 by comparing radii (`inside_of_len_lt`), as the move does. They keep the
names they have there. The steps in III.16's figure keep their statements as well. The
general steps that argue by III.2 take the circle's centre as a hypothesis, which main's
III.2 asks for; the move's III.2 takes none, and its steps cite III.2 as
`InsideCircle.of_between`, without a centre. That section goes when the move lands, and the
statements after it then cite the moved steps by the same names.

Status: the statements after III.18, and the section's one helper, are new, a draft for the
owner's approval; not approved. The steps before them are the prototype's and the move's,
proved again, and go when the move lands.
-/

namespace Elements.BookIII.Routes

open Tacit
open Elements.MixedAngles

/-! ## The steps of III.16's comparisons, by III.2

Each is proved as the move (issue #57) proves it, save for two things. Where the prototype
uses Circle 2 or 3, these steps cite III.2 as main states it (`Prop2.within`), with the
circle's centre, where the move cites `InsideCircle.of_between`, without one;
`exists_onRay_inside` cites neither, and compares radii (`inside_of_len_lt`), as in the move's
`Elements/Figure/Regions.lean`. And they use the prototype's facts where the move has its own:
`exists_centre` for `exists_circle_about`, and `surrounds_inside` and `surrounds_outside`,
which take the circle's centre. The general steps that cite III.2 take the circle's centre,
which main's III.2 asks for; the steps in III.16's figure have it already, as D. -/

/-- **A straight line that has left the circle does not come back.** If C, not within the
circle, lies between A, on or within it, and B, then B is without the circle: were B on or
within it, C would be within. [III. 2] -/
theorem OutsideCircle.of_between {A B C : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hA : InsideCircle A α ∨ OnCircle A α) (hC : ¬ InsideCircle C α) (h : Between A C B) :
    OutsideCircle B α :=
  ⟨fun hB => hC (Prop2.within hα hA (Or.inl hB) h),
    fun hB => hC (Prop2.within hα hA (Or.inr hB) h)⟩

/-- Every ray from the centre of a circle has points within the circle: between the centre
and the point where the ray meets the circumference, which are nearer the centre than it. -/
theorem exists_onRay_inside {A C : Point} {γ : Circle} (hγ : Centre A γ) (hAC : A ≠ C) :
    ∃ Y : Point, OnRay Y A C ∧ InsideCircle Y γ := by
  obtain ⟨K, hK, -⟩ := exists_point_on_circle γ []
  have hAK : A ≠ K := (ne_of_centre_of_on hγ hK).symm
  obtain ⟨G, hG, hAG⟩ := OnRay.exists_len_eq hAK hAC
  have hGγ : OnCircle G γ := on_circle_of_len_eq hγ hK hAG
  obtain ⟨L, hA, hG_L⟩ := Postulate1 A G hG.2.1.symm
  obtain ⟨Y, -, hAYG, -⟩ := exists_point_between hA hG_L hG.2.1.symm []
  exact ⟨Y, OnRay.of_sameRay (OnRay.of_between hAYG) hG.symm,
    inside_of_len_lt hγ hGγ (len_lt_of_between hAYG)⟩

/-- **An angle between two straight lines in a circle lies within it near its vertex.** If A,
B and C are on or within a circle, and BAC is a true angle, some circle about A holds no
point of the angle BAC, nor of its arms, that is not within the circle. The circle about A
passes through N, the foot of the perpendicular from A to BC; every other point X of the
straight line BC is farther from A. A point P of the angle within that circle lies on a ray
from A that crosses BC at some X, nearer A than X, and so between A and a point within the
circle. [I. 12, I. 17, I. 19, III. 2] -/
theorem near_inside_of_angle {A B C : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hA : InsideCircle A α ∨ OnCircle A α) (hB : InsideCircle B α ∨ OnCircle B α)
    (hC : InsideCircle C α ∨ OnCircle C α) (hBAC : Triangle B A C) :
    LocallyWithin A (fun P => WithinAngle B A C P ∨ OnRay P A B ∨ OnRay P A C)
      (fun P => InsideCircle P α) := by
  have hBC : B ≠ C := hBAC.ne₁₃
  have hA_BC : ¬ Collinear B C A := fun ⟨L, hB_L, hC_L, hA_L⟩ => hBAC ⟨L, hB_L, hA_L, hC_L⟩
  obtain ⟨N, hN, hright⟩ := BookI.Prop12 hBC hA_BC
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hBC
  have hA_L : ¬ OnLine A L := fun h => hA_BC ⟨L, hB_L, hC_L, h⟩
  have hN_L : OnLine N L := onLine_of_collinear hBC hN hB_L hC_L
  have hAN : A ≠ N := fun e => hA_L (e ▸ hN_L)
  have hfar := foot_nearest hBC hA_BC hN hright
  obtain ⟨γ, hγ, hNγ⟩ := Postulate3 A N hAN
  refine ⟨γ, hγ, fun P hPγ hP => ?_⟩
  have hAP : ‖A P‖ < ‖A N‖ := len_lt_of_inside hγ hNγ hPγ
  have hnear : ∀ X : Point, OnLine X L → OnRay P A X → Between A P X := by
    intro X hX hPX
    have hlt : ‖A P‖ < ‖A X‖ := by
      rcases hfar X ⟨L, hB_L, hC_L, hX⟩ with e | h
      · rw [e]; exact hAP
      · exact lt_trans hAP h
    exact OnRay.between_of_len_lt hPX (OnRay.self hPX.1) hlt
  rcases hP with hW | hPB | hPC
  · obtain ⟨X, hBXC, hXP⟩ := crossbar hW.1 hW.2
    have hXα : InsideCircle X α := Prop2.within hα hB hC hBXC
    exact Prop2.within hα hA (Or.inl hXα)
      (hnear X (on_line_of_between_ends hBXC hB_L hC_L) hXP.symm)
  · exact Prop2.within hα hA hB (hnear B hB_L hPB)
  · exact Prop2.within hα hA hC (hnear C hC_L hPC)

/-- **Points on either side of the circumference, near the vertex.** Let UAV be a true angle,
with the points of the ray AU near A within a circle, and every point of the ray AV without
it. Then every circle about A holds a point within the angle UAV and within the circle, and
another within the angle and without it: on the straight line from a point Y of AU to a point
W of AV, both near A, on either side of the point where it crosses the circumference (System
E, Intersections 4). [III. 2] -/
theorem exists_near_across {A U V : Point} {α γ : Circle} (hα : ∃ O : Point, Centre O α)
    (hUAV : Triangle U A V)
    (hU : LocallyWithin A (fun P => OnRay P A U) (fun P => InsideCircle P α))
    (hV : ∀ P : Point, OnRay P A V → OutsideCircle P α) (hγ : Centre A γ) :
    (∃ P : Point, InsideCircle P γ ∧ WithinAngle U A V P ∧ InsideCircle P α) ∧
      (∃ P : Point, InsideCircle P γ ∧ WithinAngle U A V P ∧ OutsideCircle P α) := by
  obtain ⟨γ₀, hγ₀, hU'⟩ := hU
  obtain ⟨γ', hγ', hboth⟩ := exists_inside_both hγ hγ₀
  obtain ⟨Y, hY, hYγ'⟩ := exists_onRay_inside hγ' hUAV.ne₁₂.symm
  obtain ⟨W, hW, hWγ'⟩ := exists_onRay_inside hγ' hUAV.ne₂₃
  have hYα : InsideCircle Y α := hU' Y (hboth Y hYγ').2 hY
  have hWα : OutsideCircle W α := hV W hW
  have hYW : Y ≠ W := fun e => hWα.1 (e ▸ hYα)
  obtain ⟨L, hY_L, hW_L⟩ := Postulate1 Y W hYW
  obtain ⟨X, hXα, hX_L, hYXW⟩ := line_circle_between hYα hY_L hWα hW_L
  obtain ⟨P₁, -, hYP₁X, -⟩ := exists_point_between hY_L hX_L (ne_of_between hYXW) []
  have hYP₁W : Between Y P₁ W := between_of_between_left hYXW hYP₁X
  obtain ⟨P₂, -, hXP₂W, -⟩ :=
    exists_point_between hX_L hW_L (ne_of_between (between_symm hYXW)).symm []
  have hYP₂W : Between Y P₂ W :=
    between_symm (between_of_between_left (between_symm hYXW) (between_symm hXP₂W))
  have hinγ : ∀ P : Point, Between Y P W → InsideCircle P γ := fun P h =>
    (hboth P (Prop2.within ⟨A, hγ'⟩ (Or.inl hYγ') (Or.inl hWγ') h)).1
  exact ⟨⟨P₁, hinγ P₁ hYP₁W, WithinAngle.of_between hUAV hY hW hYP₁W,
      Prop2.within hα (Or.inl hYα) (Or.inr hXα) hYP₁X⟩,
    ⟨P₂, hinγ P₂ hYP₂W, WithinAngle.of_between hUAV hY hW hYP₂W,
      OutsideCircle.of_between hα (Or.inl hYα) (fun h => inside_not_on h hXα)
        (between_cut hYXW hXP₂W)⟩⟩

/-- **Whole circles on either side of the circumference, near the vertex.** In the figure of
`exists_near_across`, for a circle about O, every circle about A holds a whole circle within
the angle UAV and within the circle, and another within the angle and without it.
[I. 12, I. 17, I. 19, I. 20, III. 2] -/
theorem near_across {A O U V : Point} {α : Circle} (hO : Centre O α) (hUAV : Triangle U A V)
    (hU : LocallyWithin A (fun P => OnRay P A U) (fun P => InsideCircle P α))
    (hV : ∀ P : Point, OnRay P A V → OutsideCircle P α) :
    NearVertexOpen A (fun P => WithinAngle U A V P ∧ InsideCircle P α) ∧
      NearVertexOpen A (fun P => WithinAngle U A V P ∧ OutsideCircle P α) :=
  ⟨NearVertexOpen.of_nearVertex (fun _ hP => hP.1.surrounds.and (surrounds_inside hO hP.2))
      (fun _ hγ => (exists_near_across ⟨O, hO⟩ hUAV hU hV hγ).1),
    NearVertexOpen.of_nearVertex (fun _ hP => hP.1.surrounds.and (surrounds_outside hO hP.2))
      (fun _ hγ => (exists_near_across ⟨O, hO⟩ hUAV hU hV hγ).2)⟩

/-- The points of a ray from a point A of a circle towards a point B on or within it are,
near A, within the circle: some circle about A holds no point of the ray that is not between
A and B. [III. 2] -/
theorem near_inside_of_ray {A B : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hA : OnCircle A α)
    (hB : InsideCircle B α ∨ OnCircle B α) (hAB : A ≠ B) :
    LocallyWithin A (fun P => OnRay P A B) (fun P => InsideCircle P α) := by
  obtain ⟨γ₀, hγ₀, hBγ₀⟩ := Postulate3 A B hAB
  exact ⟨γ₀, hγ₀, fun P hP hPB => Prop2.within hα (Or.inr hA) hB
    (OnRay.between_of_len_lt hPB (OnRay.self hAB) (len_lt_of_inside hγ₀ hBγ₀ hP))⟩

/-- The ray AC is, near A, within the circle if some point K of it is on or within the
circle: the ray AC is the ray AK. [III. 2] -/
theorem near_inside_of_onRay {A C K : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hA : OnCircle A α)
    (hK : OnRay K A C) (hKα : InsideCircle K α ∨ OnCircle K α) :
    LocallyWithin A (fun P => OnRay P A C) (fun P => InsideCircle P α) := by
  obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside_of_ray hα hA hKα hK.2.1.symm
  exact ⟨γ₀, hγ₀, fun P hP hPC => hnear P hP (OnRay.of_sameRay hPC hK)⟩

/-- **The circle lies on one side of the straight line AE.** Under III.16's first part, every
point within the circle, or on it other than A, is on the side of AE of any point K within
the circle: a point on AE, or across it, would put a point of AE within the circle, on the
way to K (System E, Intersection 1). [III. 2] -/
theorem Prop16.sameSideOf_of_inside {A E K Q : Point} {α : Circle}
    (hα : ∃ O : Point, Centre O α) (hA : OnCircle A α) (hAE_out : Prop16.Outside A E α)
    (hK : InsideCircle K α) (hQ : InsideCircle Q α ∨ OnCircle Q α) (hQA : Q ≠ A) :
    SameSideOf Q K A E := by
  have hAE : A ≠ E := Prop16.Outside.ne hA hK hAE_out
  obtain ⟨L, hA_L, hE_L⟩ := Postulate1 A E hAE
  have hoff : ∀ X : Point, InsideCircle X α → ¬ OnLine X L := fun X hX hX_L =>
    (hAE_out X ⟨L, hA_L, hE_L, hX_L⟩ (fun e => inside_not_on (e ▸ hX) hA)).1 hX
  have hQ_L : ¬ OnLine Q L := by
    intro hQ_L
    have hout := hAE_out Q ⟨L, hA_L, hE_L, hQ_L⟩ hQA
    rcases hQ with h | h
    · exact hout.1 h
    · exact hout.2 h
  refine SameSideOf.of_line hAE hA_L hE_L ?_
  refine Classical.byContradiction fun hs => ?_
  obtain ⟨X, hX_L, hQXK⟩ := OppositeSides.exists_between ⟨hQ_L, hoff K hK, hs⟩
  exact hoff X (Prop2.within hα hQ (Or.inl hK) hQXK) hX_L

/-- The points within the circle are on B's side of AE: on the centre's side
(`Prop16.sameSideOf_of_inside`), which is B's, since D is between A and B. [III. 2] -/
theorem Prop16.inside_sameSideOf {A B D E Q : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hAE_out : Prop16.Outside A E ABC) (hQ : InsideCircle Q ABC) : SameSideOf Q B A E :=
  (sameSideOf_of_inside ⟨D, hD⟩ hA hAE_out (centre_inside hD) (Or.inl hQ)
    (fun e => inside_not_on (e ▸ hQ) hA)).trans
    (SameSideOf.of_onRay (OnRay.of_between hADB)
      (sameSideOf_self (show Triangle A B E from hE).acb))

/-- **No straight line between, near A.** For a point F within the angle EAB, some circle
about A holds no point within the angle FAB, nor on the ray AF, that is not within the
circle. This is III.16's second part made local: the straight line AF falls within the circle
at some G, on F's side of A, since the circle lies on B's side of AE; and near A the angle
GAD lies within the circle (`near_inside_of_angle`). [I. 12, I. 17, I. 19, III. 2] -/
theorem Prop16.near_inside {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hAE_out : Prop16.Outside A E ABC) (hAE_in : Prop16.FallsWithin A E ABC)
    (hF : WithinAngle E A B F) :
    LocallyWithin A (fun P => WithinAngle F A B P ∨ OnRay P A F)
      (fun P => InsideCircle P ABC) := by
  obtain ⟨G, hG, hGα⟩ := hAE_in F hF.1.triangle
  have hGA : G ≠ A := fun e => inside_not_on (e ▸ hGα) hA
  have hGB : SameSideOf G B A E := inside_sameSideOf hD hA hADB hE hAE_out hGα
  have hGray : OnRay G A F := OnRay.of_sameSideOf (hGB.trans hF.1.symm) hG hGA
  have hDray : OnRay D A B := OnRay.of_between hADB
  have hGE : SameSideOf G E A B := SameSideOf.of_onRay hGray hF.2
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hDray.1
  have hD_L : OnLine D L := hDray.onLine hA_L hB_L
  have hG_L : ¬ OnLine G L := not_on_line_of_same_side (hGE.sameSide hA_L hB_L)
  have hGAD : Triangle G A D := (Triangle.of_line hA_L hD_L hDray.2.1.symm hG_L).cab
  obtain ⟨γ, hγ, hnear⟩ :=
    near_inside_of_angle ⟨D, hD⟩ (Or.inr hA) (Or.inl hGα) (Or.inl (centre_inside hD)) hGAD
  refine ⟨γ, hγ, fun P hPγ hP => hnear P hPγ ?_⟩
  rcases hP with hW | hR
  · exact Or.inl ((WithinAngle.congr hGray hDray).2 hW)
  · exact Or.inr (Or.inl (OnRay.of_sameRay hR hGray))

/-- **The horn-like angle is something.** Every circle about A, however small, holds a whole
circle within the remaining angle: within the angle EAB and without the circle. The points of
AB near A are within the circle, every point of AE but A is without it, and the circumference
crosses between them (`near_across`). [I. 12, I. 17, I. 19, I. 20, III. 2] -/
theorem Prop16.horn_nearVertex {A B D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hAE_out : Prop16.Outside A E ABC) :
    NearVertexOpen A (MixedAngle.ofContact A E ABC B).region :=
  (near_across hD (show Triangle A B E from hE).bac
    (near_inside_of_onRay ⟨D, hD⟩ hA (OnRay.of_between hADB) (Or.inl (centre_inside hD)))
    (Prop16.outside_of_onRay hAE_out)).2.mono fun _ hP =>
      MixedAngle.region_ofContact.2 ⟨WithinAngle.comm.1 hP.1, hP.2⟩

/-- **The horn lies within every angle EAF near A.** For a point F within the angle EAB, near
A a point of the remaining angle cannot be on AF or beyond it, for there the points are
within the circle (`Prop16.near_inside`). [I. 12, I. 17, I. 19, III. 2] -/
theorem Prop16.horn_within {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hAE_out : Prop16.Outside A E ABC) (hAE_in : Prop16.FallsWithin A E ABC)
    (hFw : WithinAngle E A B F) :
    LocallyWithin A (MixedAngle.ofContact A E ABC B).region (WithinAngle E A F) := by
  have hF : SameSideOf F B A E := hFw.1
  obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside hD hA hADB hE hAE_out hAE_in hFw
  refine ⟨γ₀, hγ₀, fun P hPγ hP => ?_⟩
  obtain ⟨hW, hout⟩ := MixedAngle.region_ofContact.1 hP
  have hPF : SameSideOf P F A E := hW.1.trans hF.symm
  refine ⟨hPF, ?_⟩
  have hAF : A ≠ F := hF.triangle.ne₁₃
  obtain ⟨M, hA_M, hF_M⟩ := Postulate1 A F hAF
  have hE_M : ¬ OnLine E M := fun h => hF.triangle ⟨M, hA_M, h, hF_M⟩
  have hB_M : ¬ OnLine B M := fun h => hFw.2.triangle ⟨M, hA_M, h, hF_M⟩
  have hPA : P ≠ A := hW.1.triangle.ne₁₃.symm
  by_cases hP_M : OnLine P M
  · exact absurd (hnear P hPγ (Or.inr (OnRay.of_sameSideOf hPF ⟨M, hA_M, hF_M, hP_M⟩ hPA)))
      hout.1
  have hEB_M : ¬ SameSide E B M := fun h =>
    hFw.not_sameSideOf (SameSideOf.of_line hAF hA_M hF_M h)
  rcases same_side_or hE_M hB_M hP_M hEB_M with h | h
  · exact SameSideOf.of_line hAF hA_M hF_M (same_side_symm h)
  · exact absurd (hnear P hPγ (Or.inl ⟨SameSideOf.of_line hAF hA_M hF_M (same_side_symm h),
      hW.2.trans hFw.2.symm⟩)) hout.1

/-- **The angle of contact does not depend on the straight line that names its branch**, in
III.16's figure, where AE is at right angles to the diameter AB. For any point B′ on B's side
of AE, the angle of contact named by B′ is locally equal to the one named by the diameter. If
B′ is on the ray AB, the regions are the same. If it is within the angle EAB, the one region
lies within the other, and the rest, between AB′ and AB, is within the circle near A. If it is
on the other side of AB, the same holds with AE produced beyond A to E′, which is at right
angles to AB as well. [I. 12, I. 17, I. 19, III. 2] -/
theorem Prop16.horn_locallyEqual {A B B' D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hAE_out : Prop16.Outside A E ABC) (hAE_in : Prop16.FallsWithin A E ABC)
    (hB' : SameSideOf B' B A E) :
    LocallyEqual A (MixedAngle.ofContact A E ABC B).region
      (MixedAngle.ofContact A E ABC B').region := by
  have hABE : Triangle A B E := hE
  have hAB : A ≠ B := hABE.ne₁₂
  have hAE : A ≠ E := hABE.ne₁₃
  have hB'A : B' ≠ A := hB'.triangle.ne₁₃.symm
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hE_L : ¬ OnLine E L := hABE.off_line hA_L hB_L
  by_cases hB'_L : OnLine B' L
  · /- B′ on the ray AB. -/
    have hray : OnRay B' A B := OnRay.of_sameSideOf hB' ⟨L, hA_L, hB_L, hB'_L⟩ hB'A
    exact LocallyEqual.of_iff fun P =>
      (MixedAngle.ofContact_congr (P := P) (α := ABC) (OnRay.self hAE) hray).symm
  by_cases hs : SameSide B' E L
  · /- B′ within the angle EAB. -/
    have hFw : WithinAngle E A B B' := ⟨hB', SameSideOf.of_line hAB hA_L hB_L hs⟩
    obtain ⟨γ₀, hγ₀⟩ := exists_centre A
    obtain ⟨γ, hγ, hW⟩ := horn_within hD hA hADB hE hAE_out hAE_in hFw
    exact ⟨⟨γ, hγ, fun P hPγ hP => MixedAngle.region_ofContact.2
        ⟨hW P hPγ hP, (MixedAngle.region_ofContact.1 hP).2⟩⟩,
      ⟨γ₀, hγ₀, fun P _ hP => MixedAngle.region_ofContact.2
        ⟨WithinAngle.mono_left hFw (MixedAngle.region_ofContact.1 hP).1,
          (MixedAngle.region_ofContact.1 hP).2⟩⟩⟩
  /- B′ on the other side of AB from E: AE is produced beyond A to E′. -/
  have hopp : OppositeSidesOf B' E A B :=
    OppositeSidesOf.of_line hAB hA_L hB_L ⟨hB'_L, hE_L, hs⟩
  obtain ⟨E', hEAE'⟩ := produce hAE.symm
  have hEE'_AB : OppositeSidesOf E E' A B := (OppositeSidesOf.of_between hABE.bac hEAE').swap
  have hB'E' : SameSideOf B' E' A B := OppositeSidesOf.sameSideOf hopp.symm hEE'_AB
  have hABE' : ¬ Collinear A B E' := hB'E'.symm.triangle
  have hAE' : A ≠ E' := (ne_of_between (between_symm hEAE')).symm
  obtain ⟨M, hE_M, hA_M⟩ := Postulate1 E A hAE.symm
  have hE'_M : OnLine E' M := on_line_of_between hEAE' hE_M hA_M
  have hcol : Collinear A E E' := ⟨M, hA_M, hE_M, hE'_M⟩
  have hcol' : Collinear A E' E := ⟨M, hA_M, hE'_M, hE_M⟩
  /- III.16's two parts hold for AE′, which is the straight line AE. -/
  have hAE'_out : Prop16.Outside A E' ABC :=
    fun P hP hPA => hAE_out P (Collinear.change_point hAE' hcol' hP) hPA
  have hAE'_in : Prop16.FallsWithin A E' ABC :=
    fun F hF => hAE_in F fun h => hF (Collinear.change_point hAE hcol h)
  have hFw' : WithinAngle E' A B B' :=
    ⟨(sameSideOf_congr_collinear hAE hAE'.symm hcol).2 hB', hB'E'⟩
  obtain ⟨γ₁, hγ₁, hnear₁⟩ := near_inside hD hA hADB hABE' hAE'_out hAE'_in hFw'
  have hDray : OnRay D A B := OnRay.of_between hADB
  obtain ⟨γ₂, hγ₂, hnear₂⟩ :=
    near_inside_of_ray ⟨D, hD⟩ hA (Or.inl (centre_inside hD)) hDray.2.1.symm
  obtain ⟨γ, hγ, hboth⟩ := exists_inside_both hγ₁ hγ₂
  /- E and B are on one side of AB′: AB′ separates E′ from B, and E from E′. -/
  have hAB'B : Triangle A B' B := by
    rintro ⟨N, hA_N, hB'_N, hB_N⟩
    exact hB'_L (onLine_of_collinear hAB ⟨N, hA_N, hB_N, hB'_N⟩ hA_L hB_L)
  have hEE'_AB' : OppositeSidesOf E E' A B' :=
    (OppositeSidesOf.of_between hB'.triangle.cab hEAE').swap
  have hE'B : OppositeSidesOf E' B A B' := by
    obtain ⟨N, hA_N, hB'_N⟩ := Postulate1 A B' hB'A.symm
    exact OppositeSidesOf.of_line hB'A.symm hA_N hB'_N
      ⟨(hEE'_AB'.oppositeSides hA_N hB'_N).2.1, hAB'B.off_line hA_N hB'_N,
        fun h => hFw'.not_sameSideOf (SameSideOf.of_line hB'A.symm hA_N hB'_N h)⟩
  have hEB : SameSideOf E B A B' := OppositeSidesOf.sameSideOf hEE'_AB'.symm hE'B
  have hBin : WithinAngle E A B' B := ⟨hB'.symm, hEB.symm⟩
  refine ⟨⟨γ, hγ, fun P _ hP => ?_⟩, ⟨γ, hγ, fun P hPγ hP => ?_⟩⟩
  · obtain ⟨hW, hout⟩ := MixedAngle.region_ofContact.1 hP
    exact MixedAngle.region_ofContact.2 ⟨WithinAngle.mono_left hBin hW, hout⟩
  · obtain ⟨hW, hout⟩ := MixedAngle.region_ofContact.1 hP
    have hPB : SameSideOf P B A E := hW.1.trans hB'
    have hPA : P ≠ A := hW.1.triangle.ne₁₃.symm
    refine MixedAngle.region_ofContact.2 ⟨⟨hPB, ?_⟩, hout⟩
    by_cases hP_L : OnLine P L
    · exact absurd (hnear₂ P (hboth P hPγ).2
        (OnRay.of_sameRay (OnRay.of_sameSideOf hPB ⟨L, hA_L, hB_L, hP_L⟩ hPA) hDray)) hout.1
    by_cases hsP : SameSide P E L
    · exact SameSideOf.of_line hAB hA_L hB_L hsP
    · exfalso
      have hPE : OppositeSidesOf E P A B :=
        OppositeSidesOf.of_line hAB hA_L hB_L ⟨hE_L, hP_L, fun h => hsP (same_side_symm h)⟩
      have hPB' : SameSideOf P B' A B := OppositeSidesOf.sameSideOf hPE hopp.symm
      exact hout.1 (hnear₁ P (hboth P hPγ).1 (Or.inl ⟨hW.2.trans hEB, hPB'⟩))

/-- **The remaining angle falls short of the acute angle EAF.** For F on the circle's side of
AE with the angle EAF acute, the remaining angle comes as near A as we please
(`Prop16.horn_nearVertex`); near A it lies within the angle EAF (`Prop16.horn_within`); and
every circle about A holds whole circles within the angle EAF and within the circle, which
are not in the horn. [I. 12, I. 17, I. 19, I. 20, III. 2] -/
theorem Prop16.horn_lt {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) (hAE_out : Prop16.Outside A E ABC)
    (hAE_in : Prop16.FallsWithin A E ABC) (hF : SameSideOf F B A E) (hEAF : ∠ E A F < ∟) :
    (MixedAngle.ofContact A E ABC B).FallsShort E F := by
  refine ⟨hF.triangle.bac, horn_nearVertex hD hA hADB hE hAE_out, ?_⟩
  show LocallyLess A (MixedAngle.ofContact A E ABC B).region (WithinAngle E A F)
  have hABE : Triangle A B E := hE
  have hlt : ∠ E A F < ∠ E A B := by
    rw [angle_symm hABE.ne₁₃.symm hABE.ne₁₂.symm, hBAE]; exact hEAF
  have hFw : WithinAngle E A B F := ⟨hF, sameSideOf_of_angle_lt hF hlt⟩
  refine ⟨horn_within hD hA hADB hE hAE_out hAE_in hFw, ?_⟩
  obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside hD hA hADB hE hAE_out hAE_in hFw
  exact (near_across hD hFw.1.triangle.cab ⟨γ₀, hγ₀, fun P hP hPF => hnear P hP (Or.inr hPF)⟩
    (Prop16.outside_of_onRay hAE_out)).1.mono fun P hP =>
      ⟨WithinAngle.comm.1 hP.1, fun h' => (MixedAngle.region_ofContact.1 h').2.1 hP.2⟩

/-- **The angle of the semicircle exceeds the acute angle BAF.** For F on E's side of the
diameter AB with the angle BAF acute, near A the angle BAF lies within the circle
(`Prop16.near_inside`), and every circle about A holds whole circles within the circle and
within the angle FAE, which are in the angle of the semicircle and not in BAF.
[I. 12, I. 17, I. 19, I. 20, III. 2] -/
theorem Prop16.semicircle_gt {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) (hAE_out : Prop16.Outside A E ABC)
    (hAE_in : Prop16.FallsWithin A E ABC) (hF : SameSideOf F E A B) (hBAF : ∠ B A F < ∟) :
    (MixedAngle.ofSegment A B ABC E).Exceeds B F := by
  refine ⟨hF.triangle.bac, ?_⟩
  show LocallyLess A (WithinAngle B A F) (MixedAngle.ofSegment A B ABC E).region
  have hlt : ∠ B A F < ∠ B A E := by rw [hBAE]; exact hBAF
  have hFw : WithinAngle E A B F := ⟨sameSideOf_of_angle_lt hF hlt, hF⟩
  obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside hD hA hADB hE hAE_out hAE_in hFw
  refine ⟨⟨γ₀, hγ₀, fun P hPγ hP => MixedAngle.region_ofSegment.2
    ⟨hP.1.trans hF, hnear P hPγ (Or.inl (WithinAngle.comm.1 hP))⟩⟩, ?_⟩
  refine (near_across hD hFw.1.triangle.cab ⟨γ₀, hγ₀, fun P hP hPF => hnear P hP (Or.inr hPF)⟩
    (Prop16.outside_of_onRay hAE_out)).1.mono fun P hP => ?_
  obtain ⟨hPw, hPα⟩ := hP
  refine ⟨MixedAngle.region_ofSegment.2
    ⟨(WithinAngle.mono_left hFw (WithinAngle.comm.1 hPw)).2, hPα⟩, fun h' => ?_⟩
  exact hFw.not_sameSideOf (hPw.1.symm.trans h'.2)

/-! ## After III.18: every touching straight line is III.16's

Let the straight line AE touch the circle ABC, about D, at A, and let AD be produced beyond
the centre to B, so that AB is the diameter through the point of contact (a point B beyond D
is all III.16 asks of its diameter). III.18 puts AE at right angles to AB; so AE is the
straight line of III.16, and III.16's two parts and its comparisons hold for it. -/

/-- **The touching straight line is at right angles to the diameter** [III. 18]. Let AE touch
the circle ABC, about D, at A, and let B be a point beyond the centre on AD produced. Then E
is off the straight line AB, and the angle BAE is right: AE is "the straight line drawn at
right angles to the diameter of a circle from its extremity" of III.16. -/
theorem Prop18.diameter {A B D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hAE : Touches A E ABC) (hADB : Between A D B) :
    ¬ Collinear A B E ∧ ∠ B A E = ∟ := by
  obtain ⟨L, hA_L, hE_L⟩ := Postulate1 A E hAE.1
  /- The centre is within the circle, and no point of AE is (`Touches.not_inside`), so D is
     off AE. -/
  have hD_L : ¬ OnLine D L := fun h => hAE.not_inside ⟨L, hA_L, hE_L, h⟩ (centre_inside hD)
  /- III.18, with Heath's F, C, DE as our D, A, AE: the radius DA is perpendicular to AE. -/
  have hDAE : ∠ D A E = ∟ :=
    Prop18 hD hA hAE ⟨L, hA_L, hE_L, hA_L⟩ E ⟨L, hA_L, hE_L, hE_L⟩ hAE.1.symm
  have hDray : OnRay D A B := OnRay.of_between hADB
  obtain ⟨M, hA_M, hD_M⟩ := Postulate1 A D hDray.2.1.symm
  have hB_M : OnLine B M := on_line_of_between hADB hA_M hD_M
  have hE_M : ¬ OnLine E M := fun h => hD_L (line_unique hAE.1 hA_M h hA_L hE_L ▸ hD_M)
  exact ⟨Triangle.of_line hA_M hB_M (ne_of_between_ends hADB) hE_M,
    (angle_onRay_left hDray hAE.1.symm).symm.trans hDAE⟩

/-- **III.16's two parts hold for every touching straight line** [III. 18, III. 16]. In the
figure of `Prop18.diameter`, every point of AE but A is without the circle, and every other
straight line through A falls within it. -/
theorem Prop18.parts {A B D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hAE : Touches A E ABC) (hADB : Between A D B) :
    Prop16.Outside A E ABC ∧ Prop16.FallsWithin A E ABC :=
  have h := Prop18.diameter hD hA hAE hADB
  Prop16 hD hA hADB h.1 h.2

/-- Let AE touch the circle about D at A, and AB be the diameter through A: **every straight
line from A into the circle names the diameter's angle of contact.** The touching is carried
by the hypothesis that the angle of contact named by B′ is as Euclid draws it
(`MixedAngle.WellFormed`): A is on the circle, AE touches it there, and B′, off AE, names a
branch, the ray AB′ passing within the circle. Then B′ is on B's side of AE, the side the
whole circle is on, and near A the angle of contact named by B′ is the one named by the
diameter (`Prop16.horn_locallyEqual`). [III. 18, III. 16] -/
theorem Prop18.branch {A B B' D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hADB : Between A D B) (hm : (MixedAngle.ofContact A E ABC B').WellFormed) :
    SameSideOf B' B A E ∧
      LocallyEqual A (MixedAngle.ofContact A E ABC B).region
        (MixedAngle.ofContact A E ABC B').region := by
  obtain ⟨hA, hAE, ⟨K, hK, hKα⟩, -⟩ := hm
  have hE := (Prop18.diameter hD hA hAE hADB).1
  obtain ⟨hout, hin⟩ := Prop18.parts hD hA hAE hADB
  have hB' : SameSideOf B' B A E :=
    SameSideOf.of_onRay hK.symm (Prop16.inside_sameSideOf hD hA hADB hE hout hKα)
  exact ⟨hB', Prop16.horn_locallyEqual hD hA hADB hE hout hin hB'⟩

/-- **The angle of contact does not depend on the straight line that names its branch.** Let
AE touch a circle about D at A. Any two angles of contact along AE, each with its branch
named by a straight line from A into the circle, are equal near A: each is, near A, the
angle of contact of III.16's figure, named by the diameter through A. -/
theorem Prop18.contact_locallyEqual {A B B' D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hm : (MixedAngle.ofContact A E ABC B).WellFormed)
    (hm' : (MixedAngle.ofContact A E ABC B').WellFormed) :
    LocallyEqual A (MixedAngle.ofContact A E ABC B).region
      (MixedAngle.ofContact A E ABC B').region := by
  /- The diameter through A: AD produced beyond the centre. -/
  obtain ⟨B₀, hADB₀⟩ := produce (ne_of_centre_of_on hD hm.1)
  exact (Prop18.branch hD hADB₀ hm).2.symm.trans (Prop18.branch hD hADB₀ hm').2

/-- **The angle of contact is less than any acute rectilineal angle**, for every straight line
touching a circle. Let AE touch a circle about D at A, and B name the branch of the angle of
contact by a straight line from A into the circle. For every acute angle EAF placed at A
along AE, on the circle's side, the angle of contact falls short of it. By III.18 the
diameter AB₀ through A is at right angles to AE, and III.16's remaining angle, named by B₀,
falls short of EAF (`Prop16.horn_lt`); the angle named by B is the same near A
(`Prop18.branch`). -/
theorem Prop18.contact_lt {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hm : (MixedAngle.ofContact A E ABC B).WellFormed) (hF : SameSideOf F B A E)
    (hEAF : ∠ E A F < ∟) : (MixedAngle.ofContact A E ABC B).FallsShort E F := by
  /- The diameter through A: AD produced beyond the centre to B₀. -/
  obtain ⟨B₀, hADB₀⟩ := produce (ne_of_centre_of_on hD hm.1)
  obtain ⟨hE, hB₀AE⟩ := Prop18.diameter hD hm.1 hm.2.1 hADB₀
  obtain ⟨hout, hin⟩ := Prop18.parts hD hm.1 hm.2.1 hADB₀
  obtain ⟨hBB₀, heq⟩ := Prop18.branch hD hADB₀ hm
  have h := Prop16.horn_lt hD hm.1 hADB₀ hE hB₀AE hout hin (hF.trans hBB₀) hEAF
  obtain ⟨γ₀, hγ₀, hwithin⟩ := heq.1
  exact ⟨h.1, h.2.1.mono_near hγ₀ hwithin, LocallyLess.congr_left heq h.2.2⟩

/-- **The angle of the semicircle is greater than any acute rectilineal angle**, on the side
of the diameter that a touching straight line names. Let AE touch the circle ABC, about D, at
A, and AB be the diameter through A. For every acute angle BAF placed at A along AB, on E's
side, the angle of the semicircle, contained by the straight line BA and the circumference on
E's side, exceeds it: by III.18 this is III.16's figure (`Prop16.semicircle_gt`). The
touching straight line AE only names the side of AB. The angle of the semicircle does not
depend on it, and on any side of the diameter the comparison follows from III.16, with the
perpendicular to AB at A drawn on that side by I.11. The move states that form, with AE at
right angles to AB, as `Prop16.semicircle`. -/
theorem Prop18.semicircle_gt {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hAE : Touches A E ABC) (hADB : Between A D B)
    (hF : SameSideOf F E A B) (hBAF : ∠ B A F < ∟) :
    (MixedAngle.ofSegment A B ABC E).Exceeds B F := by
  obtain ⟨hE, hBAE⟩ := Prop18.diameter hD hA hAE hADB
  obtain ⟨hout, hin⟩ := Prop18.parts hD hA hAE hADB
  exact Prop16.semicircle_gt hD hA hADB hE hBAE hout hin hF hBAF

/-- **III.16's last clause, for every straight line touching a circle.** Let AE touch the
circle ABC, about D, at A, and AB be the diameter through A; for the angle of the semicircle,
AE only names the side of AB (`Prop18.semicircle_gt`). The angle of the semicircle and
the angle of contact are angles as Euclid draws them, and every acute rectilineal angle XYZ
can be placed at A [I. 23]: along AB on E's side, where the angle of the semicircle exceeds
it, and along AE on the circle's side, where the angle of contact falls short of it. -/
theorem Prop18.acute {A B D E X Y Z : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hAE : Touches A E ABC) (hADB : Between A D B)
    (hXYZ : Triangle X Y Z) (hacute : ∠ X Y Z < ∟) :
    (MixedAngle.ofSegment A B ABC E).WellFormed ∧
      (MixedAngle.ofContact A E ABC B).WellFormed ∧
      (∃ F : Point, SameSideOf F E A B ∧ ∠ B A F = ∠ X Y Z ∧
        (MixedAngle.ofSegment A B ABC E).Exceeds B F) ∧
      ∃ F : Point, SameSideOf F B A E ∧ ∠ E A F = ∠ X Y Z ∧
        (MixedAngle.ofContact A E ABC B).FallsShort E F := by
  have hE := (Prop18.diameter hD hA hAE hADB).1
  have hABE : Triangle A B E := hE
  have hm : (MixedAngle.ofContact A E ABC B).WellFormed :=
    ⟨hA, hAE, ⟨D, OnRay.of_between hADB, centre_inside hD⟩, hABE.acb⟩
  refine ⟨⟨hA, ⟨D, OnRay.of_between hADB, centre_inside hD⟩, hE⟩, hm, ?_, ?_⟩
  · obtain ⟨F, G, hG, hF, hFAG⟩ := BookI.Prop23 hABE.ne₁₂ hXYZ hE
    have hFA : F ≠ A := hF.triangle.ne₁₃.symm
    have hBAF : ∠ B A F = ∠ X Y Z := by
      rw [angle_symm hABE.ne₁₂.symm hFA, ← angle_onRay_right hG hFA, hFAG]
    exact ⟨F, hF, hBAF, Prop18.semicircle_gt hD hA hAE hADB hF (hBAF ▸ hacute)⟩
  · obtain ⟨F, G, hG, hF, hFAG⟩ := BookI.Prop23 hABE.ne₁₃ hXYZ hABE.acb
    have hFA : F ≠ A := hF.triangle.ne₁₃.symm
    have hEAF : ∠ E A F = ∠ X Y Z := by
      rw [angle_symm hABE.ne₁₃.symm hFA, ← angle_onRay_right hG hFA, hFAG]
    exact ⟨F, hF, hEAF, Prop18.contact_lt hD hm hF (hEAF ▸ hacute)⟩

end Elements.BookIII.Routes
