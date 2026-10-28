import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop12
import Elements.BookI.Prop17
import Elements.BookI.Prop19
import Elements.BookI.Prop23
import Elements.BookIII.MixedAngles
import Elements.BookIII.Prop16

/-!
# Book III, Proposition 18

Euclid's text, in Heath's translation: [`heath/III/18.md`](../../heath/III/18.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

After the proof, III.16's angle of contact, with its comparisons, is carried to every
straight line touching a circle: by III.18 such a straight line is at right angles to the
diameter through the point of contact, and so it is III.16's. Three steps lead to the
companions `Prop18.contact_locallyEqual`, `Prop18.contact_lt`, `Prop18.semicircle_gt` and
`Prop18.acute`.
-/

namespace Elements.BookIII

open Tacit

/-- If a straight line touch a circle, and a straight line be joined from the centre to the point of
contact, the straight line so joined will be perpendicular to the tangent. -/
theorem Prop18 {C D E F : Point} {ABC : Circle} (hF : Centre F ABC) (hC : OnCircle C ABC)
    (hDE : Touches D E ABC) (hCDE : Collinear D E C) :
    ∀ P : Point, Collinear D E P → P ≠ C → ∠ F C P = ∟ := by
  -- For let a straight line DE touch the circle ABC at the point C, let the centre F of the
  -- circle ABC be taken, and let FC be joined from F to C;
  /- The centre is within the circle, and no point of DE is, so F is off DE. -/
  have hF_DE : ¬ Collinear D E F := fun h => hDE.not_inside h (centre_inside hF)
  obtain ⟨L, hD_L, hE_L⟩ := Postulate1 D E hDE.1
  have hC_L : OnLine C L := by
    obtain ⟨M, hD_M, hE_M, hC_M⟩ := hCDE
    exact (line_unique hDE.1 hD_M hE_M hD_L hE_L) ▸ hC_M
  have hF_L : ¬ OnLine F L := fun h => hF_DE ⟨L, hD_L, hE_L, h⟩
  -- I say that FC is perpendicular to DE.
  -- For, if not, let FG be drawn from F perpendicular to DE.
  obtain ⟨G, hG, hFG⟩ := BookI.Prop12 hDE.1 hF_DE
  have hG_L : OnLine G L := by
    obtain ⟨M, hD_M, hE_M, hG_M⟩ := hG
    exact (line_unique hDE.1 hD_M hE_M hD_L hE_L) ▸ hG_M
  have hGC : G = C := Classical.byContradiction fun hGC => by
    -- Then, since the angle FGC is right,
    have hFGC : ∠ F G C = ∟ := hFG C hCDE (Ne.symm hGC)
    -- the angle FCG is acute; [I. 17]
    have hT : Triangle F G C := (Triangle.of_line hG_L hC_L hGC hF_L).bca.bca
    have hacute : ∠ G C F < ∟ := by
      have h17 := (BookI.Prop17 hT).1
      rw [hFGC] at h17
      exact Magnitude.lt_of_add_lt_add_left h17
    -- and the greater angle is subtended by the greater side; [I. 19]
    -- therefore FC is greater than FG.
    have hFG_FC : ‖F G‖ < ‖F C‖ := BookI.Prop19 hT (by rw [hFGC]; exact hacute)
    -- But FC is equal to FB;
    /- B is where FG leaves the circle, for G is outside it: DE has no point within
       the circle (`Touches.not_inside`), and meets it at C alone. -/
    have hG_out : OutsideCircle G ABC :=
      ⟨hDE.not_inside hG, fun hG_on =>
        (hDE.2 L hD_L hE_L).2 ⟨C, G, Ne.symm hGC, hC_L, hC, hG_L, hG_on⟩⟩
    obtain ⟨M, hF_M, hG_M⟩ := Postulate1 F G (fun e => hF_L (e ▸ hG_L))
    obtain ⟨B, hB, -, hFBG⟩ := line_circle_between (centre_inside hF) hF_M hG_out hG_M
    have hFC_FB : ‖F C‖ = ‖F B‖ := Definition15 hF hC hB
    -- therefore FB is also greater than FG,
    have hFG_FB : ‖F G‖ < ‖F B‖ := hFC_FB ▸ hFG_FC
    -- the less than the greater: which is impossible.
    exact lt_irrefl _ (lt_trans hFG_FB (len_lt_of_between hFBG))
  -- Therefore FG is not perpendicular to DE.
  -- Similarly we can prove that neither is any other straight line except FC;
  -- therefore FC is perpendicular to DE.
  subst hGC
  exact hFG
  -- Therefore etc.
  -- Q. E. D.

/-! ## The angle of contact in general, after III.18

III.16 compares two angles contained by a straight line and a circumference with
rectilineal angles. In its figure, where the straight line AE is drawn at right angles to the
diameter AB from its extremity A, "the angle of the semicircle is greater, and the remaining
angle less, than any acute rectilineal angle". III.18 says that a straight line touching a
circle is perpendicular to the straight line joined from the centre to the point of contact.
So, after III.18, every touching straight line is III.16's, and III.16's angle of contact,
with its comparisons, belongs to every one of them. The declarations below state that:

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

III.16's companions (`Prop16.semicircle`, `Prop16.remaining` and `Prop16.acute`) prove its
comparisons in III.16's figure, where AE is drawn at right angles to the diameter; the
declarations below, which use the words and facts of the mixed angles, prove the angle of
contact's comparisons for a touching straight line in general. The route is Euclid's order:
III.18 makes the touching straight line III.16's, and III.16's comparisons do the rest.
Nothing later is cited. Those comparisons follow Euclid's reductio, in III.16's steps
(`Prop16.semicircle_gt`, `Prop16.horn_lt`): an acute angle that failed the comparison would
leave its straight line with no point within the circle, interposed between the touching
straight line and the circumference, which III.16's second part forbids; and a straight line
with a point within the circle puts, near A, the acute angle within the angle of the
semicircle, with room to spare, and the angle of contact within the acute angle.

Nothing here rests on Circle 2 or Circle 3. All but `Prop18.diameter` and `Prop18.parts` rest
on the rule that every circle has a centre (`Tacit.exists_centre`), through III.2 and the
steps they cite, and `Prop18.contact_locallyEqual` and `Prop18.contact_lt` take their centre
from it. The steps of III.16's comparisons that these statements need are cited from
`Elements/Figure/Regions.lean`, `Elements/BookIII/MixedAngles.lean` and
`Elements/BookIII/Prop16.lean`. In place of Circle 2 and Circle 3, they argue by III.2
(`InsideCircle.of_between`), and `exists_onRay_inside` by comparing radii
(`inside_of_len_lt`).
-/

/-! ### After III.18: every touching straight line is III.16's

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
AE touch a circle at A, and let D be its centre (`Tacit.exists_centre`). Any two angles of
contact along AE, each with its branch
named by a straight line from A into the circle, are equal near A: each is, near A, the
angle of contact of III.16's figure, named by the diameter through A. -/
theorem Prop18.contact_locallyEqual {A B B' E : Point} {ABC : Circle}
    (hm : (MixedAngle.ofContact A E ABC B).WellFormed)
    (hm' : (MixedAngle.ofContact A E ABC B').WellFormed) :
    LocallyEqual A (MixedAngle.ofContact A E ABC B).region
      (MixedAngle.ofContact A E ABC B').region := by
  obtain ⟨D, hD⟩ := exists_centre ABC
  /- The diameter through A: AD produced beyond the centre. -/
  obtain ⟨B₀, hADB₀⟩ := produce (ne_of_centre_of_on hD hm.1)
  exact (Prop18.branch hD hADB₀ hm).2.symm.trans (Prop18.branch hD hADB₀ hm').2

/-- **The angle of contact is less than any acute rectilineal angle**, for every straight line
touching a circle. Let AE touch a circle at A, let D be its centre (`Tacit.exists_centre`),
and let B name the branch of the angle of contact by a straight line from A into the circle.
For every acute angle EAF placed at A
along AE, on the circle's side, the angle of contact falls short of it. By III.18 the
diameter AB₀ through A is at right angles to AE, and III.16's remaining angle, named by B₀,
falls short of EAF (`Prop16.horn_lt`); the angle named by B is the same near A
(`Prop18.branch`). -/
theorem Prop18.contact_lt {A B E F : Point} {ABC : Circle}
    (hm : (MixedAngle.ofContact A E ABC B).WellFormed) (hF : SameSideOf F B A E)
    (hEAF : ∠ E A F < ∟) : (MixedAngle.ofContact A E ABC B).FallsShort E F := by
  obtain ⟨D, hD⟩ := exists_centre ABC
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
perpendicular to AB at A drawn on that side by I.11. III.16's companion `Prop16.semicircle`
states that form, with AE at right angles to AB. -/
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
it, and along AE on the circle's side, where the angle of contact falls short of it. Once
III.18 makes AE III.16's straight line (`Prop18.diameter`), the placing and the comparisons
are III.16's own, cited from its companion `Prop16.acute`. -/
theorem Prop18.acute {A B D E X Y Z : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hAE : Touches A E ABC) (hADB : Between A D B)
    (hXYZ : Triangle X Y Z) (hacute : ∠ X Y Z < ∟) :
    (MixedAngle.ofSegment A B ABC E).WellFormed ∧
      (MixedAngle.ofContact A E ABC B).WellFormed ∧
      (∃ F : Point, SameSideOf F E A B ∧ ∠ B A F = ∠ X Y Z ∧
        (MixedAngle.ofSegment A B ABC E).Exceeds B F) ∧
      ∃ F : Point, SameSideOf F B A E ∧ ∠ E A F = ∠ X Y Z ∧
        (MixedAngle.ofContact A E ABC B).FallsShort E F := by
  obtain ⟨hE, hBAE⟩ := Prop18.diameter hD hA hAE hADB
  have hABE : Triangle A B E := hE
  have hm : (MixedAngle.ofContact A E ABC B).WellFormed :=
    ⟨hA, hAE, ⟨D, OnRay.of_between hADB, centre_inside hD⟩, hABE.acb⟩
  exact ⟨Prop16.semicircle_wellFormed hD hA hADB hE, hm,
    Prop16.acute hD hA hADB hE hBAE hXYZ hacute⟩

end Elements.BookIII
