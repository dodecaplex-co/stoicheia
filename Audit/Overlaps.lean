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
proves each "states it" or "gives it at once" row again, from the rules alone, and I.2,
I.3 and I.23, whose rules supply their step in a longer proof. The former I.7 audit is
kept as a circular derivation through Circle 4, now a corollary of I.7. After III.6,
`III_5_crossing` proves III.5 when "cut" is read as crossing. It now rests on
Diagram-segment 2 through the proved radius comparison `len_lt_of_inside`.
A second section proves III.24, III.26 and III.27 without the hypotheses our
measure of circumferences leaves idle, the catalogue's near misses of representation.

Each theorem's type is the proposition's own (`type_of% @Elements.BookIII.Prop2`), so a
change to a statement shows up here too. At the end, `#guard_msgs` pins the axioms Lean
reports for each theorem. The last theorems repeat the derivations of Diagram-angle 3
from I.13 and Circle 2 from Circle 3. The reverse derivation of Circle 3 through the
derived Circle 2 is circular and retains Circle 3 in its axiom closure.

Nothing imports this file, and it is not part of the default build. `lake build Audit`
checks it. If a statement or a rule changes so that one of these proofs fails, that is
the signal to bring the catalogue up to date.
-/

set_option warningAsError true

namespace Audit

open Elements Elements.Tacit

/-! ## Rules that state a proposition, give it at once, or supply its step -/

/-- Draws a point X off the straight line through B and C, and with it the triangle BCX,
from the rules alone: superposition needs a triangle to lay down and a point to name the
side, and neither I.2 nor I.3 gives one. Book Zero's `exists_off_line` draws such a point
too, by two circles that cut one another and a comparison of lengths. The catalogue's
historical counts used this construction; after the rule retirements, I.2's audit
rests on 31 axioms, through the proofs of the rules it calls. The circle about B through
C meets the straight line again at C', beyond B
(Intersections 5); a third point X of the circle cannot be on the straight line, for B
would then lie between X and C, and between X and C' (Circle 1), and C and C' would lie
on one side of B (Between 7), where B lies between them. Book Zero's `Triangle.of_line`
makes BCX a triangle. -/
private theorem exists_point_off_line {B C : Point} {M : Line} (hBC : B ≠ C)
    (hB : OnLine B M) (hC : OnLine C M) : ∃ X : Point, ¬ OnLine X M ∧ Triangle B C X := by
  obtain ⟨α, hBα, hCα⟩ := Postulate3 B C hBC
  have hBin : InsideCircle B α := centre_inside hBα
  obtain ⟨C', hC'α, hC'M, hC'BC⟩ := line_circle_beyond hBin hB hC hBC.symm
  obtain ⟨X, hXα, hX⟩ := exists_point_on_circle α [C, C']
  have hXM : ¬ OnLine X M := fun hXM => by
    have hXC : X ≠ C := by rintro rfl; exact hX (by simp)
    have hXC' : X ≠ C' := by rintro rfl; exact hX (by simp)
    have h₁ : Between X B C := between_of_inside_chord hB hXM hC hBin hXα hCα hXC
    have h₂ : Between X B C' := between_of_inside_chord hB hXM hC'M hBin hXα hC'α hXC'
    exact not_between_of_between_between h₁ h₂ (between_symm hC'BC)
  exact ⟨X, hXM, Triangle.of_line hB hC hBC hXM⟩

/-- **I.2 from superposition.** The rule lays a triangle down with a corner on a given
point of a straight line and a side along a given ray, keeping its sides
(`superposition`). Laid down at A along AB, a triangle on BC carries the length of BC
to A: that is I.2, which a collapsing compass (Postulate 3) cannot do at once. Neither
the triangle nor a point off AB is given, so both are drawn (`exists_point_off_line`).
The certificate lets only I.4 and I.8 use superposition, though the rule, unlike System
E's, can itself construct points (#75); our I.2 is Euclid's construction, by I.1, and does not rest on the rule. -/
theorem I_2 : type_of% @Elements.BookI.Prop2 := by
  intro A B C hBC
  by_cases hAB : A = B
  · exact ⟨C, by rw [hAB]⟩
  obtain ⟨M, hBM, hCM⟩ := Postulate1 B C hBC
  obtain ⟨X, -, hBCX⟩ := exists_point_off_line hBC hBM hCM
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hAB
  obtain ⟨H, hH, -⟩ := exists_point_off_line hAB hAL hBL
  obtain ⟨L', -, -, -, -, hAL', -⟩ := superposition hBCX hAL hBL hAB hH
  exact ⟨L', hAL'⟩

/-- **I.3 from superposition.** Laid down at A along the ray from A through B, a
triangle on C₁C₂ carries the length of C₁C₂ onto that ray, at E. E is not A, for C₁ and
C₂ differ and AE is as long as C₁C₂; it lies on the ray from A through B, so A is not
between E and B; it is not B, for AB is the greater; nor is B between A and E, for then
AE would be greater than AB. So E lies between A and B (Between 6): that is I.3. Our
I.3 is Euclid's, by I.2, and does not rest on the rule. -/
theorem I_3 : type_of% @Elements.BookI.Prop3 := by
  intro A B C₁ C₂ hC h
  have hAB : A ≠ B := ne_of_len_gt h
  obtain ⟨M, hC₁M, hC₂M⟩ := Postulate1 C₁ C₂ hC
  obtain ⟨X, -, hCX⟩ := exists_point_off_line hC hC₁M hC₂M
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hAB
  obtain ⟨H, hH, -⟩ := exists_point_off_line hAB hAL hBL
  obtain ⟨E, -, hEL, hEAB, -, hAE, -⟩ := superposition hCX hAL hBL hAB hH
  refine ⟨E, ?_, hAE⟩
  have hAE_ne : A ≠ E := ne_of_len_eq hAE hC
  have hEB : E ≠ B := by
    rintro rfl
    exact lt_irrefl _ (hAE ▸ h)
  rcases between_cases hAE_ne hEB hAB hAL hEL hBL with h' | h' | h'
  · exact h'
  · exact absurd h' hEAB
  · exact absurd (lt_trans (hAE ▸ len_lt_of_between h') h) (lt_irrefl _)

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

/-- **I.23 from superposition.** The rule lays a triangle down with a corner on a given
point of a straight line and a side along a given ray, keeping its angles
(`superposition`, after LeanEuclid's form of System E's two superposition rules). Laid
down at A along AB, on P's side, the triangle DCE carries its angle at C to A: that is
I.23. The certificate lets only I.4 and I.8 use superposition, though the rule, unlike
System E's, can itself construct points (#75), so our I.23 is Euclid's construction, by I.22 and I.8. It rests on superposition all the same,
through I.8. -/
theorem I_23 : type_of% @Elements.BookI.Prop23 := by
  intro A B C D E P hAB hDCE hABP
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hAB
  have hP : ¬ OnLine P L := fun h => hABP ⟨L, hAL, hBL, h⟩
  have hCDE : Triangle C D E := fun ⟨M, hD, hC, hE⟩ => hDCE ⟨M, hC, hD, hE⟩
  obtain ⟨G, F, hG, hGAB, hF, hAG, -, -, hGAF, -, -⟩ := superposition hCDE hAL hBL hAB hP
  have hFA : F ≠ A := by rintro rfl; exact not_on_line_of_same_side hF hAL
  /- G is not A: AG is as long as CD, and C and D are two corners of a triangle. -/
  have hGA : G ≠ A := by
    rintro rfl
    have hCD : C = D := eq_of_len_eq_zero (hAG.symm.trans (len_self G))
    subst hCD
    obtain ⟨Q, hQ⟩ := exists_point [C]
    have hQC : Q ≠ C := fun h => hQ (h ▸ List.mem_singleton_self Q)
    by_cases hCE : C = E
    · subst hCE
      obtain ⟨M, hCM, -⟩ := Postulate1 C Q hQC.symm
      exact hCDE ⟨M, hCM, hCM, hCM⟩
    · obtain ⟨M, hCM, hEM⟩ := Postulate1 C E hCE
      exact hCDE ⟨M, hCM, hCM, hEM⟩
  refine ⟨F, G, ⟨hAB, hGA, ⟨L, hAL, hBL, hG⟩, hGAB⟩, ⟨hAB, fun M hAM hBM => ?_⟩, ?_⟩
  · rw [← line_unique hAB hAL hBL hAM hBM]
    exact hF
  · rw [angle_symm hFA hGA]
    exact hGAF

/-- **III.2 through Circle 2, from Circle 3.** Between two points on or within a circle, every point is
within it (`inside_of_between`, Circle 2). With both points on the circle, that is III.2.
This is Astra's proof from the outside review, now using Circle 2 as a theorem of
Circle 3. The overlap with Circle 3 remains. Our III.2 follows Euclid, by I.5, I.16
and I.19, and rests on neither Circle 2 nor Circle 3: III.1, which finds its centre, puts
the middle point of a straight line in the circle within it by III.2's own argument
(`Prop1.within`). -/
theorem III_2 : type_of% @Elements.BookIII.Prop2 :=
  fun _ hA hB _ hAEB => inside_of_between (Or.inr hA) (Or.inr hB) hAEB

/-- **III.2 from Circle 3.** A straight line that has left a circle does not come back
(`outside_of_between`, Circle 3): with one point on or within the circle and a second
point not within it, any point beyond the second is outside. It is Circle 2 turned round.
Were a point between two points of the circle not within it, the second point of the
circle would be outside the circle, and so not on it. -/
theorem III_2_outside : type_of% @Elements.BookIII.Prop2 :=
  fun _ hA hB _ hAEB => Classical.byContradiction fun hE =>
    (outside_of_between (Or.inr hA) hE hAEB).2 hB

/-- **III.5 from Diagram-segment 2.** A circle is fixed by its centre and radius
(`circle_eq`, Diagram-segment 2). Two circles about one centre through one point are
one circle, so two circles that cut one another cannot share a centre. Our III.5 takes
Euclid's steps, and names this rule to show that F and G are two points. It also rests
on the rule and Postulate 3 through proved rules such as `centre_inside`, whose proof
uses circles to compare lengths. -/
theorem III_5 : type_of% @Elements.BookIII.Prop5 :=
  fun hne ⟨_, _, _, hC₁, hC₂, _, _⟩ ⟨hE₁, hE₂⟩ => hne (circle_eq hE₁ hE₂ hC₁ hC₂ rfl)

/-- **III.6 from Diagram-segment 2 and Generalities 3.** Circles touching within are two
circles through one point, so Diagram-segment 2 again forbids a common centre. Circles
touching without have no point within both, and a common centre would be one, since a
centre is within its circle (`centre_inside`, Generalities 3). Our III.6 ends contact
without with Generalities 3, before drawing FEB; for contact within it takes Euclid's
steps, and names Diagram-segment 2 to show that E and B are two points. Generalities 3
has been a theorem since 19 October 2026 (`Elements/Figure/RuleBase.lean`), and itself
rests on Diagram-segment 2 and Postulate 3 through its comparison of lengths. The
closure pinned below is that of its proof with Diagram-segment 2. -/
theorem III_6 : type_of% @Elements.BookIII.Prop6 := by
  rintro C F ABC CDE (⟨hC₁, hC₂, hne, -⟩ | ⟨hC₂, hC₁, hne, -⟩ | ⟨-, -, hout⟩) ⟨hF₁, hF₂⟩
  · exact hne (circle_eq hF₁ hF₂ hC₁ hC₂ rfl)
  · exact hne (circle_eq hF₂ hF₁ hC₂ hC₁ rfl)
  · exact hout F (centre_inside hF₁) (centre_inside hF₂)

/-- **III.5 read with crossing.** If a point P of one circle is within the other, and the
two circles have a point C in common, they have no common centre: P is nearer the centre
than C is (`len_lt_of_inside`, Diagram-segment 4), and yet, both being on the one circle,
as far from it (Definition I.15). A circle and its copy, drawn twice over, do not cross
so, for neither has a point within the other. Our III.5 reads "cut" as meeting at two
points (`CirclesMeet`), which a circle and its copy do, and there the published proof
uses Diagram-segment 2 (the catalogue, under III.5). The crossing proof below also
rests on Diagram-segment 2, through the proved `len_lt_of_inside`; it no longer gives
an independent derivation without that axiom. Circle 4 is now proved using
Diagram-segment 2 as well. The same proof gives III.6 for circles
touching within, read with a point of the inner circle within the outer. -/
theorem III_5_crossing {C P E : Point} {ABC CDG : Circle} (hC₁ : OnCircle C ABC)
    (hC₂ : OnCircle C CDG) (hP₂ : OnCircle P CDG) (hP₁ : InsideCircle P ABC) :
    ¬ (Centre E ABC ∧ Centre E CDG) := by
  rintro ⟨hE₁, hE₂⟩
  have h : ‖E P‖ < ‖E C‖ := len_lt_of_inside hE₁ hC₁ hP₁
  rw [Definition15 hE₂ hP₂ hC₂] at h
  exact lt_irrefl _ h

/-! ## Hypotheses our measure of circumferences leaves idle

Not overlaps with a rule, but with a definition: a circumference is measured by twice the
angle standing on it (`circumference`, Definition III.9), a measure with no radius in it.
So III.26 and III.27 hold in any two circles, and III.24's second clause follows from its
angle hypothesis alone (the catalogue's "Near misses"). Each theorem below states the
proposition without the hypothesis, and an `example` beneath it gives back the
proposition's own statement from it, so a change to either statement shows up here. When
arcs get a meaning of their own (brief 0005, stage 3), these are meant to stop compiling. -/

/-- **III.26 in any two circles.** Equal angles at the centres, or at the circumferences,
stand on circumferences of equal measure, whether or not the circles are equal: each
measure is the angle at the centre (`Circumference.centre`), or twice the angle at the
circumference (`Circumference.eq`). -/
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
      rw [BookIII.Circumference.eq ⟨G, hG⟩ hA hB hC hAK,
        BookIII.Circumference.eq ⟨H, hH⟩ hD hE hF hDL, h]⟩

example : type_of% @Elements.BookIII.Prop26 :=
  fun _ hG hH hA hB hC hD hE hF hAK hDL => III_26_any hG hH hA hB hC hD hE hF hAK hDL

/-- **III.27 in any two circles.** Angles standing on circumferences of equal measure are
equal, at the circumferences and at the centres, whether or not the circles are equal:
each measure is twice the angle at the circumference (`Circumference.standing`), and the
angle at the centre is twice it again (III.20). -/
theorem III_27_any {A B C D E F G H : Point} {ABC DEF : Circle}
    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hF : OnCircle F DEF) (hBAC : Triangle B A C) (hEDF : Triangle E D F)
    (heq : standing ABC B A C = standing DEF E D F) :
    ∠ B A C = ∠ E D F ∧
      (SameSideOf G A B C → SameSideOf H D E F → ∠ B G C = ∠ E H F) := by
  rw [BookIII.Circumference.standing ⟨G, hG⟩ hA hB hC hBAC.acb,
    BookIII.Circumference.standing ⟨H, hH⟩ hD hE hF hEDF.acb] at heq
  have hangle : ∠ B A C = ∠ E D F := Magnitude.eq_of_add_self_eq heq
  refine ⟨hangle, fun hGA hHD => ?_⟩
  rw [BookIII.Prop20 hG hA hB hC hGA, BookIII.Prop20 hH hD hE hF hHD, hangle]

example : type_of% @Elements.BookIII.Prop27 :=
  fun _ hG hH hA hB hC hD hE hF hBAC hEDF heq => III_27_any hG hH hA hB hC hD hE hF hBAC hEDF heq

/-- **III.24's second clause from its angles alone.** Segments with equal angles AEB, CFD
have circumferences of equal measure, whatever their bases: each circumference, with the
one on the other side of its base, which is twice the angle at E or F, makes up the whole
circle (`Circumference.whole`). III.24's first clause, that the circles are equal, needs
the equal bases. -/
theorem III_24_measure {A B C D E F : Point} {AEB CFD : Circle}
    (hAEB : ∃ O : Point, Centre O AEB) (hCFD : ∃ O : Point, Centre O CFD)
    (hA : OnCircle A AEB) (hB : OnCircle B AEB) (hE : OnCircle E AEB) (hC : OnCircle C CFD)
    (hD : OnCircle D CFD) (hF : OnCircle F CFD) (hE_AB : ¬ Collinear A B E)
    (hF_CD : ¬ Collinear C D F) (hsim : ∠ A E B = ∠ C F D) :
    circumference AEB A E B = circumference CFD C F D := by
  obtain ⟨X, hX, hXE⟩ := BookIII.Prop2.oppositeSide hAEB hA hB hE_AB
  obtain ⟨Y, hY, hYF⟩ := BookIII.Prop2.oppositeSide hCFD hC hD hF_CD
  have w₁ := BookIII.Circumference.whole hAEB hA hB hXE
  have w₂ := BookIII.Circumference.whole hCFD hC hD hYF
  rw [BookIII.Circumference.eq hAEB hE hA hB hXE.symm] at w₁
  rw [BookIII.Circumference.eq hCFD hF hC hD hYF.symm, ← hsim] at w₂
  exact CommonNotion3 (w₁.trans w₂.symm) rfl

example : type_of% @Elements.BookIII.Prop24 :=
  fun hAEB hCFD hA hB hE hC hD hF hE_AB hF_CD hAB hsim =>
    ⟨(BookIII.Prop24 hAEB hCFD hA hB hE hC hD hF hE_AB hF_CD hAB hsim).1,
     III_24_measure hAEB hCFD hA hB hE hC hD hF hE_AB hF_CD hsim⟩

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
be outside it (`outside_of_between`, Circle 3), neither within the circle nor on it. -/
theorem inside_of_between : type_of% @Elements.Tacit.inside_of_between :=
  fun hA hB h => Classical.byContradiction fun hC =>
    hB.elim (outside_of_between hA hC h).1 (outside_of_between hA hC h).2

/-- **Circle 3 through its own consequence.** Were the point beyond within the circle or
on it, the point between would be within the circle (`inside_of_between`, Circle 2),
which it is not. Circle 2 is now proved from Circle 3, so this reverse derivation is
circular evidence and does not remove Circle 3 from the assumptions. -/
theorem outside_of_between : type_of% @Elements.Tacit.outside_of_between :=
  fun hA hC h => ⟨fun hB => hC (Elements.Tacit.inside_of_between hA (Or.inl hB) h),
    fun hB => hC (Elements.Tacit.inside_of_between hA (Or.inr hB) h)⟩

end Audit

/-! ## What each proof rests on

Lean's own report, pinned. `Classical.choice` comes in with any rule that speaks of a
length, an angle or an area, for the magnitudes are chosen (`Foundations/Magnitudes.lean`);
`propext` and `Quot.sound` with the proofs that argue by cases. -/

/--
info: 'Audit.I_2' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_of_inside_chord,
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
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.pasch2,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.I_2

/--
info: 'Audit.I_3' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_of_inside_chord,
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
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.pasch2,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.I_3

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
 Elements.Tacit.between_of_inside_chord,
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
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.I_7

/--
info: 'Audit.I_23' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_symm,
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.circle_eq,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_inside_circle,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.I_23

/--
info: 'Audit.III_2' depends on axioms: [propext, Classical.choice, Quot.sound, Elements.Tacit.outside_of_between]
-/
#guard_msgs in
#print axioms Audit.III_2

/--
info: 'Audit.III_2_outside' depends on axioms: [propext, Classical.choice, Quot.sound, Elements.Tacit.outside_of_between]
-/
#guard_msgs in
#print axioms Audit.III_2_outside

/--
info: 'Audit.III_5' depends on axioms: [Classical.choice, Elements.Tacit.circle_eq]
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
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.circle_eq,
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
 Elements.Tacit.not_lt_zero]
-/
#guard_msgs in
#print axioms Audit.III_6

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
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.between_symm,
 Elements.Tacit.circle_eq,
 Elements.Tacit.exists_point,
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
 Elements.Tacit.not_lt_zero]
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
 Elements.Tacit.between_of_inside_chord,
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
 Elements.Tacit.between_of_inside_chord,
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
 Elements.Tacit.between_of_inside_chord,
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
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.III_24_measure

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
 Elements.Tacit.between_of_inside_chord,
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
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.adjacent_eq_of_right

/--
info: 'Audit.inside_of_between' depends on axioms: [propext, Classical.choice, Quot.sound, Elements.Tacit.outside_of_between]
-/
#guard_msgs in
#print axioms Audit.inside_of_between

/--
info: 'Audit.outside_of_between' depends on axioms: [propext, Classical.choice, Quot.sound, Elements.Tacit.outside_of_between]
-/
#guard_msgs in
#print axioms Audit.outside_of_between
