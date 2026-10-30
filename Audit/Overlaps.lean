import Elements
import Elements.Figure.CirclePoints
import Elements.Figure.Incidence
import Elements.Figure.RuleBase
import Elements.Figure.Circles
import Elements.BookI.Prop07
import Elements.BookI.Prop13

/-!
# Overlaps: propositions a rule already contains

Some of System E's rules, which we take as axioms, already say what Euclid later proves,
or give it in a few lines. Astra found the clearest case, III.2, in the outside review
(`docs/reports/outside-review-01.md`), and compiled its one-line proof; we are grateful.
The catalogue in `docs/reports/overlaps.md` lists every case we found, and this file
proves each "states it" or "gives it at once" row again, from the rules alone. The former
I.7 audit is kept as a circular derivation through Circle 4, now a corollary of I.7, and
the former III.2 audits likewise, through Circle 2 and Circle 3, corollaries of III.2 since
24 October 2026. After
III.6, `III_5_crossing` and `III_5_radius` give III.5 from Definition I.15 with
Diagram-segment 4 or Diagram-segment 3. Both rules have been theorems since the second
axiom retirement; through them each proof rested on Diagram-segment 2 as well until 26
October 2026, and rests now on our radius rule (`radius_ne_zero`) instead. A second
section proves the measure clauses of
III.24's companion `Prop24.equalCircles` and of III.26, and III.27's companion
`Prop27.of_measure` whole, without the hypotheses our measure of circumferences leaves idle,
the catalogue's near misses of representation.

A third section proves III.30 by the same measure, without III.28 (`III_30_measure`),
another near miss of representation.

Each theorem's type is the proposition's own (`type_of% @Elements.BookIII.Prop2`), so a
change to a statement shows up here too. At the end, `#guard_msgs` pins the axioms Lean
reports for each theorem. The last theorems repeat the derivation of Diagram-angle 3
from I.13, and derive Circle 2 from Circle 3 and Circle 3 from Circle 2. Both rules are
now proved from III.2, so each of these two reaches III.2 through the other rule, and
neither is independent of it.

Nothing imports this file, and it is not part of the default build. `lake build Audit`
checks it. If a statement or a rule changes so that one of these proofs fails, that is
the signal to bring the catalogue up to date.
-/

set_option warningAsError true

namespace Audit

open Elements Elements.Tacit

/-! ## Rules that state a proposition, give it at once, or supply its step -/

/-- **I.7 through its own corollary.** Until 19 October 2026 this was an overlap proof
from Circle 4, `not_same_side_of_circles_meet`, taken as an assumption. Circle 4 is now
proved from I.7, so this derivation uses I.7 and establishes no independent overlap.
Draw the circles about A and B through C (Postulate 3); D is on both by their equal
radii (Diagram-segment 3), and the circles differ by the proved `centre_unique`.
Circle 4 excludes C and D on the same side. The published I.7 follows Euclid through
I.5 and does not use this corollary. -/
theorem I_7 : type_of% @Elements.BookI.Prop7 := by
  intro A B C D hside hCA hCB
  refine Classical.byContradiction fun hCD => ?_
  obtain ⟨hAB, hall⟩ := hside
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hAB
  have hCD_L : SameSide C D L := hall L hAL hBL
  have hC_L : ¬ OnLine C L := not_on_line_of_same_side hCD_L
  have hAC : A ≠ C := by rintro rfl; exact hC_L hAL
  have hBC : B ≠ C := by rintro rfl; exact hC_L hBL
  obtain ⟨α, hAα, hCα⟩ := Postulate3 A C hAC
  obtain ⟨β, hBβ, hCβ⟩ := Postulate3 B C hBC
  have hDα : OnCircle D α :=
    on_circle_of_len_eq hAα hCα ((len_symm A D).trans (hCA.symm.trans (len_symm C A)))
  have hDβ : OnCircle D β :=
    on_circle_of_len_eq hBβ hCβ ((len_symm B D).trans (hCB.symm.trans (len_symm C B)))
  have hαβ : α ≠ β := by
    rintro rfl
    exact hAB (centre_unique hAα hBβ)
  exact not_same_side_of_circles_meet hαβ hCα hCβ hDα hDβ hCD hAα hBβ hAL hBL hCD_L

/-- **III.2 through its own corollary, Circle 2.** Between two points on or within a circle,
every point is within it (`inside_of_between`, Circle 2). With both points on the circle,
that is III.2. This is Astra's proof from the outside review. Until 24 October 2026 it was
an overlap proof, from Circle 2 proved from Circle 3, an assumption. Both rules are now
proved from III.2, after it, so this derivation uses III.2 and establishes no independent
overlap. Our III.2 follows Euclid, by I.5, I.16 and I.19, takes its centre by III.1's
construction (`Prop1.of_circle`), and uses neither Circle 2 nor Circle 3. -/
theorem III_2 : type_of% @Elements.BookIII.Prop2 :=
  fun hA hB _ hAEB => inside_of_between (Or.inr hA) (Or.inr hB) hAEB

/-- **III.2 through its own corollary, Circle 3.** A straight line that has left a circle
does not come back (`outside_of_between`, Circle 3): with one point on or within the circle
and a second point not within it, any point beyond the second is outside. It is Circle 2
turned round. Were a point between two points of the circle not within it, the second
point of the circle would be outside the circle, and so not on it. Circle 3 was an
assumption until 24 October 2026 and is now proved from III.2, so this derivation, too,
uses III.2. -/
theorem III_2_outside : type_of% @Elements.BookIII.Prop2 :=
  fun hA hB _ hAEB => Classical.byContradiction fun hE =>
    (outside_of_between (Or.inr hA) hE hAEB).2 hB

/-- **III.5 from Diagram-segment 2.** A circle is fixed by its centre and radius
(`circle_eq`, Diagram-segment 2). Two circles about one centre through one point are
one circle. A point of one within the other would then be both within that circle and on
it, which Generalities 4, proved since the second axiom retirement, forbids. Our III.5
takes Euclid's steps and cites neither Diagram-segment 2 nor Circle 4, now a theorem proved
from I.7 using Diagram-segment 2. Since 26 October 2026 it does not rest on Diagram-segment
2 either: Book Zero's lemmas beneath it, `ne_of_centre_of_on` and `len_lt_of_between`, rest
on our radius rule (`radius_ne_zero`), which gives neither III.5 nor III.6, for it says only
that a radius is something. -/
theorem III_5 : type_of% @Elements.BookIII.Prop5 :=
  fun ⟨⟨_, _, _, _, _, hC₁, hC₂⟩, ⟨_, hP₁, hP₂⟩, _⟩ ⟨hE₁, hE₂⟩ =>
    inside_not_on (circle_eq hE₁ hE₂ hC₁ hC₂ rfl ▸ hP₂) hP₁

/-- **III.6 from Diagram-segment 2 and Generalities 3 and 4.** A common centre and the
point of contact would make the circles one, so the point of the inner circle within the
outer would be both within that circle and on it, which Generalities 4 forbids. Circles
touching without have no point within both, and a common centre would be one, since a
centre is within its circle (`centre_inside`, Generalities 3). Our III.6 ends contact
without with Generalities 3, Definition I.15's placement of the centre within the figure.
For contact within it takes Euclid's steps. Neither case cites Diagram-segment 2, nor
Circle 4, whose proof uses it. Generalities 3 and 4 have been theorems since 19 October 2026
(`Elements/Figure/RuleBase.lean`). Generalities 3 rests on Postulate 3 and our radius rule
through its comparison of lengths, and so does our III.6; since 26 October 2026 neither
rests on Diagram-segment 2. The closure pinned below is that of their proofs with
Diagram-segment 2. -/
theorem III_6 : type_of% @Elements.BookIII.Prop6 := by
  rintro C F ABC CDE (⟨hC₁, hC₂, ⟨P, hP, hP_in⟩, -⟩ | ⟨hC₂, hC₁, ⟨P, hP, hP_in⟩, -⟩ |
    ⟨-, -, hout⟩) ⟨hF₁, hF₂⟩
  · exact inside_not_on (circle_eq hF₂ hF₁ hC₂ hC₁ rfl ▸ hP_in) hP
  · exact inside_not_on (circle_eq hF₁ hF₂ hC₁ hC₂ rfl ▸ hP_in) hP
  · exact hout F (centre_inside hF₁) (centre_inside hF₂)

/-- **III.5 from Diagram-segment 4.** If a point P of one circle is within the other, and the
two circles have a point C in common, they have no common centre: P is nearer the centre
than C is (`len_lt_of_inside`, Diagram-segment 4), and yet, both being on the one circle,
as far from it (Definition I.15). Our III.5 instead draws a straight line through the
point within and compares its parts, without citing Diagram-segment 4. The same short
proof gives III.6 for circles touching within, with the point of the inner circle within
the outer. Diagram-segment 4 has been a theorem since 19 October 2026
(`Elements/Figure/Incidence.lean`). Through it this proof rested on Diagram-segment 2 until
26 October 2026; it rests now on our radius rule instead, and so again gives a derivation
without that axiom, by a proved rule. -/
theorem III_5_crossing : type_of% @Elements.BookIII.Prop5 := by
  rintro E ABC CDG ⟨⟨_, C, _, _, _, hC₁, hC₂⟩, -, ⟨P, hP₂, hP₁⟩⟩ ⟨hE₁, hE₂⟩
  have h : ‖E P‖ < ‖E C‖ := len_lt_of_inside hE₁ hC₁ hP₁
  rw [Definition15 hE₂ hP₂ hC₂] at h
  exact lt_irrefl _ h

/-- **III.5 from Diagram-segment 3.** F, a point of ABC,
is as far from E as C is (Definition I.15); so it is on CDG (`on_circle_of_len_eq`, the
half of Diagram-segment 3 that Definition I.15 does not give), yet it is within CDG,
which Generalities 4 forbids. Both rules have been theorems since 19 October 2026. Until 26
October 2026 the proof of Diagram-segment 3's half took the circle about the centre through
the point to be the given one by Diagram-segment 2, so this proof rested on Diagram-segment 2
too; that proof now compares lengths on the straight line from the centre, by our radius
rule, and this one no longer rests on Diagram-segment 2. -/
theorem III_5_radius : type_of% @Elements.BookIII.Prop5 := by
  rintro E ABC CDG ⟨⟨_, C, _, _, _, hC₁, hC₂⟩, ⟨F, hF₁, hF₂⟩, -⟩ ⟨hE₁, hE₂⟩
  exact inside_not_on hF₂ (on_circle_of_len_eq hE₂ hC₂ (Definition15 hE₁ hF₁ hC₁))

/-! ## Hypotheses our measure of circumferences leaves idle

Not overlaps with a rule, but with a definition: a circumference is measured by twice the
angle standing on it (`circumference`, Definition III.9), a measure with no radius in it.
So the equal measures of III.26, and III.27's companion `Prop27.of_measure` whole, hold in
any two circles, and the second clause of III.24's companion `Prop24.equalCircles` follows
from its angle hypothesis alone (the catalogue's "Near misses"). Each theorem below states
the measures without the hypothesis; an `example` beneath it gives back the statement of
`Prop27.of_measure`, or of `Prop24.equalCircles`, so a change to either statement shows up
here. III.26 is no longer among them: it concludes that the circumferences are congruent
too, which in unequal circles equal angles do not give, so it is no longer provable for any
two circles. III.27 itself, `Prop27`, is not among them either: it takes its circumferences
congruent, and its equal circles are idle for another reason than the measure, since
congruent circumferences lie in equal circles already. -/

/-- **III.26's equal measures in any two circles.** Equal angles at the centres, or at the
circumferences, stand on circumferences of equal measure, whether or not the circles are
equal: each measure is the angle at the centre (`Circumference.centre`), or twice the angle
at the circumference (`Circumference.eq`). -/
theorem III_26_any {A B C D E F G H K L : Point} {ABC DEF : Circle}
    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hF : OnCircle F DEF) (hAK : OppositeSidesOf A K B C) (hDL : OppositeSidesOf D L E F) :
    (OppositeSidesOf G K B C → OppositeSidesOf H L E F → ∠ B G C = ∠ E H F →
      circumference ABC B K C = circumference DEF E L F) ∧
    (∠ B A C = ∠ E D F → circumference ABC B K C = circumference DEF E L F) :=
  ⟨fun hGK hHL h => by
      rw [BookIII.Circumference.centre hG hB hC hGK, BookIII.Circumference.centre hH hE hF hHL,
        h],
   fun h => by
      rw [BookIII.Circumference.eq hA hB hC hAK,
        BookIII.Circumference.eq hD hE hF hDL, h]⟩

/- III.26 itself does not follow from `III_26_any`, and no longer holds for any two circles:
it concludes that the circumferences are congruent as well as equal in measure, and in
unequal circles equal angles give no congruence. So its example has gone; the measures
above are the first conjunct of each of its clauses, and the check after III.26, in
`Elements/BookIII/Prop26.lean`, gives them back from it. -/

/-- **III.27's companion `Prop27.of_measure` in any two circles.** Angles standing on
circumferences of equal measure are equal, at the circumferences and at the centres,
whether or not the circles are equal:
each measure is twice the angle at the circumference (`Circumference.standing`), and the
angle at the centre is twice it again (III.20). -/
theorem III_27_any {A B C D E F G H : Point} {ABC DEF : Circle}
    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hF : OnCircle F DEF) (hBAC : Triangle B A C) (hEDF : Triangle E D F)
    (heq : standing ABC B A C = standing DEF E D F) :
    ∠ B A C = ∠ E D F ∧
      (SameSideOf G A B C → SameSideOf H D E F → ∠ B G C = ∠ E H F) := by
  rw [BookIII.Circumference.standing hA hB hC hBAC.acb,
    BookIII.Circumference.standing hD hE hF hEDF.acb] at heq
  have hangle : ∠ B A C = ∠ E D F := Magnitude.eq_of_add_self_eq heq
  refine ⟨hangle, fun hGA hHD => ?_⟩
  rw [BookIII.Prop20.special hG hA hB hC hGA, BookIII.Prop20.special hH hD hE hF hHD,
    hangle]

example : type_of% @Elements.BookIII.Prop27.of_measure :=
  fun _ hG hH hA hB hC hD hE hF hBAC hEDF heq => III_27_any hG hH hA hB hC hD hE hF hBAC hEDF heq

/-- **The second clause of III.24's companion from its angles alone.** Segments with equal
angles AEB, CFD have circumferences of equal measure, whatever their bases: each
circumference, with the one on the other side of its base, which is twice the angle at E or
F, makes up the whole circle (`Circumference.whole`). The first clause of
`Prop24.equalCircles`, that the circles are equal, needs the equal bases, and so does III.24
itself, which concludes that the segments are congruent. -/
theorem III_24_measure {A B C D E F : Point} {AEB CFD : Circle}
    (hA : OnCircle A AEB) (hB : OnCircle B AEB) (hE : OnCircle E AEB) (hC : OnCircle C CFD)
    (hD : OnCircle D CFD) (hF : OnCircle F CFD) (hE_AB : ¬ Collinear A B E)
    (hF_CD : ¬ Collinear C D F) (hsim : ∠ A E B = ∠ C F D) :
    circumference AEB A E B = circumference CFD C F D := by
  obtain ⟨X, hX, hXE⟩ := BookIII.Prop2.oppositeSide hA hB hE_AB
  obtain ⟨Y, hY, hYF⟩ := BookIII.Prop2.oppositeSide hC hD hF_CD
  have w₁ := BookIII.Circumference.whole hA hB hXE
  have w₂ := BookIII.Circumference.whole hC hD hYF
  rw [BookIII.Circumference.eq hE hA hB hXE.symm] at w₁
  rw [BookIII.Circumference.eq hF hC hD hYF.symm, ← hsim] at w₂
  exact CommonNotion3 (w₁.trans w₂.symm) rfl

example : type_of% @Elements.BookIII.Prop24.equalCircles :=
  fun hA hB hE hC hD hF hE_AB hF_CD hAB hsim =>
    ⟨(BookIII.Prop24.equalCircles hA hB hE hC hD hF hE_AB hF_CD hAB hsim).1,
     III_24_measure hA hB hE hC hD hF hE_AB hF_CD hsim⟩

/-! ## III.30 by the measure

The same measure saves III.30 a step. Its two halves are measured by the angles that stand
on them, each taken twice (`Circumference.standing`, by III.21), so they are equal once
those angles are, which I.4 gives. Euclid goes instead from the equal straight lines AD and
DB, by III.28, with his step that each half is less than a semicircle; his own III.26
would take him from the equal angles to equal halves without either. What the measure
saves is III.26's step at the circumference, which it reduces to its definition and
III.21. `III_30_measure` has III.30's own statement, which keeps the measure when arcs get
a meaning of their own (brief 0006, stage 3), so it stays. Our III.30 follows Euclid, by
III.28. -/

/-- **III.30 without III.28.** The halves AD and DB are measured by the angles ABD and DAB
that stand on them, each taken twice, so they are equal once those angles are. The
construction is Euclid's: AB is bisected at C (I.10), CD drawn at right angles to it (I.11)
meets the given circumference at D, C being within the circle (III.2), and I.4 makes the
angles at A and B equal. -/
theorem III_30_measure : type_of% @Elements.BookIII.Prop30 := by
  intro A B ADB hA hB P hP
  have hABP : Triangle A B P := hP
  have hAB : A ≠ B := hABP.ne₁₂
  /- C bisects AB; CX is at right angles to it, on P's side. -/
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  obtain ⟨C, hACB, hAC⟩ := BookI.Prop10 hAB
  have hC_L : OnLine C L := on_line_of_between_ends hACB hA_L hB_L
  obtain ⟨X, hXP, hX⟩ := BookI.Prop11 hAB ⟨L, hA_L, hB_L, hC_L⟩ hP
  /- C is within the circle (III.2), so XC produced beyond C to Y meets the circle at D,
     beyond C from Y, on X's side of AB. -/
  have hC_in : InsideCircle C ADB := BookIII.Prop2 hA hB C hACB
  have hX_L : ¬ OnLine X L := hXP.triangle.off_line hA_L hB_L
  have hCX : C ≠ X := fun e => hX_L (e ▸ hC_L)
  obtain ⟨N, hC_N, hX_N⟩ := Postulate1 C X hCX
  obtain ⟨Y, hY_N, hXCY, -⟩ := Postulate2 hX_N hC_N hCX.symm []
  obtain ⟨D, hD, hD_N, hDCY⟩ :=
    line_circle_beyond hC_in hC_N hY_N (ne_of_between (between_symm hXCY))
  have hDC : D ≠ C := fun e => inside_not_on hC_in (e ▸ hD)
  have hD_L : ¬ OnLine D L := fun hD_L =>
    hX_L ((line_unique hDC hD_N hC_N hD_L hC_L) ▸ hX_N)
  have hY_L : ¬ OnLine Y L := fun hY_L =>
    hX_L ((line_unique (ne_of_between (between_symm hXCY)) hY_N hC_N hY_L hC_L) ▸ hX_N)
  have hDX : SameSide D X L := same_side_of_opposite_sides
    ⟨hY_L, hD_L, fun h => pasch3 hDCY hC_L (same_side_symm h)⟩
    ⟨hY_L, hX_L, fun h => pasch3 hXCY hC_L (same_side_symm h)⟩
  refine ⟨D, hD, (SameSideOf.of_line hAB hA_L hB_L hDX).trans hXP, ?_⟩
  have hABD : Triangle A B D := Triangle.of_line hA_L hB_L hAB hD_L
  /- The triangles CAD, CBD have their sides about the right angles at C equal, so the
     angles at A and B are equal (I.4). -/
  have hCA : ‖C A‖ = ‖C B‖ := by rw [len_symm C A, hAC]
  have hDray : OnRay D C X := OnRay.of_between_between (between_symm hXCY) (between_symm hDCY)
  have hACD : ∠ A C D = ∟ := by
    rw [angle_onRay_right hDray (ne_of_between hACB)]
    exact hX A ⟨L, hA_L, hB_L, hA_L⟩ (ne_of_between hACB)
  have hBCD : ∠ B C D = ∟ := by
    rw [angle_onRay_right hDray (ne_of_between (between_symm hACB))]
    exact hX B ⟨L, hA_L, hB_L, hB_L⟩ (ne_of_between (between_symm hACB))
  have hCAD : Triangle C A D := Triangle.of_line hC_L hA_L (ne_of_between hACB).symm hD_L
  have hCBD : Triangle C B D :=
    Triangle.of_line hC_L hB_L (ne_of_between (between_symm hACB)).symm hD_L
  obtain ⟨-, -, hA₁, -⟩ := BookI.Prop4 hCAD hCBD hCA rfl (hACD.trans hBCD.symm)
  have hbase : ∠ D A B = ∠ A B D := by
    rw [angle_symm hABD.ne₁₃.symm hAB.symm,
      ← angle_onRay_left (OnRay.of_between hACB) hABD.ne₁₃.symm, hA₁,
      angle_onRay_left (OnRay.of_between (between_symm hACB)) hABD.ne₂₃.symm]
  /- Each half is twice the angle standing on it, and the angles are equal. -/
  rw [BookIII.Circumference.standing hB hA hD hABD.acb,
    BookIII.Circumference.standing hA hD hB hABD.cba, hbase]

/-! ## A rule that a proposition gives back -/

/-- **Diagram-angle 3 from I.13.** The angle beside a right angle is right
(`adjacent_eq_of_right`, Diagram-angle 3). I.13 makes the two angles together two right
angles, and Common Notion 3 takes the one right angle away. I.13 does not rest on the
rule. Since 19 October 2026 the library proves it after I.13 under the same name;
this audit repeats the derivation, and its guard pins the underlying assumptions. -/
theorem adjacent_eq_of_right : type_of% @Elements.Tacit.adjacent_eq_of_right := by
  intro A B C D L hA hB hACB hD hright
  have hAB : A ≠ B := ne_of_between_ends hACB
  have hABD : ¬ Collinear A B D := fun ⟨M, hAM, hBM, hDM⟩ =>
    hD (line_unique hAB hAM hBM hA hB ▸ hDM)
  have h13 : ∠ A C D + ∠ D C B = ∟ + ∟ := BookI.Prop13 hACB hABD
  rw [hright, add_comm ∟] at h13
  rw [hright]
  exact (CommonNotion3 h13 rfl).symm

/-! ## Circle 2 and Circle 3, one rule turned round -/

/-- **Circle 2 from Circle 3.** Were a point between two points on or within a circle not
within it, the straight line would have left the circle there, and the second point would
be outside it (`outside_of_between`, Circle 3), neither within the circle nor on it. The
library proved Circle 2 so from 19 to 24 October 2026. It now proves both rules from III.2,
so this derivation reaches III.2 through Circle 3. -/
theorem inside_of_between : type_of% @Elements.Tacit.inside_of_between :=
  fun hA hB h => Classical.byContradiction fun hC =>
    hB.elim (outside_of_between hA hC h).1 (outside_of_between hA hC h).2

/-- **Circle 3 from Circle 2.** Were the point beyond within the circle or on it, the point
between would be within the circle (`inside_of_between`, Circle 2), which it is not. The
library proves Circle 3 so since 24 October 2026, with Circle 2 as `Prop2.within`, III.2
for points on or within the circle; so this derivation reaches III.2 through Circle 2, as
the one above does through Circle 3. -/
theorem outside_of_between : type_of% @Elements.Tacit.outside_of_between :=
  fun hA hC h => ⟨fun hB => hC (Elements.Tacit.inside_of_between hA (Or.inl hB) h),
    fun hB => hC (Elements.Tacit.inside_of_between hA (Or.inr hB) h)⟩

end Audit

/-! ## What each proof rests on

Lean's own report, pinned. `Classical.choice` comes in with any rule that speaks of a
length, an angle or an area, for the magnitudes are chosen (`Foundations/Magnitudes.lean`);
`propext` and `Quot.sound` with the proofs that argue by cases. -/

/--
info: 'Audit.I_7' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_assoc,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_add_of_between,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_degenerate,
 Elements.Tacit.area_eq_zero_of_on_line,
 Elements.Tacit.area_rotate,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_symm,
 Elements.Tacit.circle_eq,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_inside_circle,
 Elements.Tacit.exists_point_on_line,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.pasch2,
 Elements.Tacit.radius_ne_zero,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.I_7

/--
info: 'Audit.III_2' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Elements.Postulate4,
 Quot.sound,
 Elements.Tacit.add_assoc,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_add_of_between,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_degenerate,
 Elements.Tacit.area_eq_zero_of_on_line,
 Elements.Tacit.area_rotate,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_symm,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_inside_circle,
 Elements.Tacit.exists_point_on_line,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.pasch2,
 Elements.Tacit.radius_ne_zero,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.III_2

/--
info: 'Audit.III_2_outside' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Elements.Postulate4,
 Quot.sound,
 Elements.Tacit.add_assoc,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_add_of_between,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_degenerate,
 Elements.Tacit.area_eq_zero_of_on_line,
 Elements.Tacit.area_rotate,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_symm,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_inside_circle,
 Elements.Tacit.exists_point_on_line,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.pasch2,
 Elements.Tacit.radius_ne_zero,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.III_2_outside

/--
info: 'Audit.III_5' depends on axioms: [Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate3,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.between_symm,
 Elements.Tacit.circle_eq,
 Elements.Tacit.exists_centre,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.radius_ne_zero]
-/
#guard_msgs in
#print axioms Audit.III_5

/--
info: 'Audit.III_6' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.between_symm,
 Elements.Tacit.circle_eq,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point_inside_circle,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.radius_ne_zero]
-/
#guard_msgs in
#print axioms Audit.III_6

/--
info: 'Audit.III_5_radius' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.between_symm,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point_inside_circle,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.radius_ne_zero]
-/
#guard_msgs in
#print axioms Audit.III_5_radius

/--
info: 'Audit.III_5_crossing' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.between_symm,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.radius_ne_zero]
-/
#guard_msgs in
#print axioms Audit.III_5_crossing

/--
info: 'Audit.III_26_any' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Elements.Postulate4,
 Elements.Postulate5,
 Quot.sound,
 Elements.Tacit.add_assoc,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_add_of_between,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_degenerate,
 Elements.Tacit.area_eq_zero_of_on_line,
 Elements.Tacit.area_rotate,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_symm,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_inside_circle,
 Elements.Tacit.exists_point_on_line,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.pasch2,
 Elements.Tacit.radius_ne_zero,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.III_26_any

/--
info: 'Audit.III_27_any' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Elements.Postulate4,
 Elements.Postulate5,
 Quot.sound,
 Elements.Tacit.add_assoc,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_add_of_between,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_degenerate,
 Elements.Tacit.area_eq_zero_of_on_line,
 Elements.Tacit.area_rotate,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_symm,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_inside_circle,
 Elements.Tacit.exists_point_on_line,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.pasch2,
 Elements.Tacit.radius_ne_zero,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.III_27_any

/--
info: 'Audit.III_24_measure' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Elements.Postulate4,
 Elements.Postulate5,
 Quot.sound,
 Elements.Tacit.add_assoc,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_add_of_between,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_degenerate,
 Elements.Tacit.area_eq_zero_of_on_line,
 Elements.Tacit.area_rotate,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_symm,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_inside_circle,
 Elements.Tacit.exists_point_on_line,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.pasch2,
 Elements.Tacit.radius_ne_zero,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.III_24_measure

/--
info: 'Audit.III_30_measure' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Elements.Postulate4,
 Elements.Postulate5,
 Quot.sound,
 Elements.Tacit.add_assoc,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_add_of_between,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_degenerate,
 Elements.Tacit.area_eq_zero_of_on_line,
 Elements.Tacit.area_rotate,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_symm,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_inside_circle,
 Elements.Tacit.exists_point_on_line,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.pasch2,
 Elements.Tacit.radius_ne_zero,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.III_30_measure

/--
info: 'Audit.adjacent_eq_of_right' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Elements.Postulate4,
 Quot.sound,
 Elements.Tacit.add_assoc,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_add_of_between,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_degenerate,
 Elements.Tacit.area_eq_zero_of_on_line,
 Elements.Tacit.area_rotate,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_symm,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_inside_circle,
 Elements.Tacit.exists_point_on_line,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.pasch2,
 Elements.Tacit.radius_ne_zero,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.adjacent_eq_of_right

/--
info: 'Audit.inside_of_between' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Elements.Postulate4,
 Quot.sound,
 Elements.Tacit.add_assoc,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_add_of_between,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_degenerate,
 Elements.Tacit.area_eq_zero_of_on_line,
 Elements.Tacit.area_rotate,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_symm,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_inside_circle,
 Elements.Tacit.exists_point_on_line,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.pasch2,
 Elements.Tacit.radius_ne_zero,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.inside_of_between

/--
info: 'Audit.outside_of_between' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Elements.Postulate4,
 Quot.sound,
 Elements.Tacit.add_assoc,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_add_of_between,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_degenerate,
 Elements.Tacit.area_eq_zero_of_on_line,
 Elements.Tacit.area_rotate,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_symm,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_inside_circle,
 Elements.Tacit.exists_point_on_line,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.pasch2,
 Elements.Tacit.radius_ne_zero,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.outside_of_between
