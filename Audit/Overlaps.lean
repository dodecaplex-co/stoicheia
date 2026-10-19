import Elements

/-!
# Overlaps: propositions a rule already contains

Some of System E's rules, which we take as axioms, already say what Euclid later proves,
or give it in a few lines. Astra found the clearest case, III.2, in the outside review
(`docs/reports/outside-review-01.md`), and compiled its one-line proof; we are grateful.
The catalogue in `docs/reports/overlaps.md` lists every case we found, and this file
proves each "states it" or "gives it at once" row again, from the rules alone, and I.2,
I.3, I.7 and I.23, whose rules supply their step in a longer proof. After III.6,
`III_5_crossing` and `III_5_radius` give III.5 from Definition I.15 with Diagram-segment 4
or Diagram-segment 3. A second section proves the measure clauses of III.24's companion
`Prop24.equalCircles` and of III.26, and III.27 whole, without the hypotheses our measure of
circumferences leaves idle, the catalogue's near misses of representation.

Each theorem's type is the proposition's own (`type_of% @Elements.BookIII.Prop2`), so a
change to a statement shows up here too. At the end, `#guard_msgs` pins the axioms Lean
reports for each theorem: the rules named in the catalogue, and nothing else. The last
theorems run the other way: one proves a rule from a proposition, and two prove Circle 2
and Circle 3, each from the other.

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
too, by two circles that cut one another and a comparison of lengths, but would bring
I.2's audit proof from ten axioms to twenty-one; the catalogue's counts are made with
this one. The circle about B through C meets the straight line again at C', beyond B
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

/-- **I.7 from Circle 4.** Two circles that cut one another do so on opposite sides of
the straight line through their centres (`not_same_side_of_circles_meet`, Circle 4).
I.7 is that rule with its circles left undrawn. Draw the circle about A through C and
the circle about B through C (Postulate 3); D is on both, being as far from each centre
as C is (Diagram-segment 3); they are two circles, having two centres (Generalities 2);
so C and D cannot be two points on one side of AB. No proof in Stoicheia uses Circle 4:
our I.7 follows Euclid, by I.5. -/
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

/-- **III.2 from Circle 2.** Between two points on or within a circle, every point is
within it (`inside_of_between`, Circle 2). With both points on the circle, that is III.2.
This is Astra's proof, from the outside review. Our III.2 follows Euclid, by I.5, I.16
and I.19, and rests on neither this rule nor Circle 3: III.1, which finds its centre, puts
the middle point of a straight line in the circle within it by III.2's own argument
(`Prop1.within`). -/
theorem III_2 : type_of% @Elements.BookIII.Prop2 :=
  fun hA hB _ hAEB => inside_of_between (Or.inr hA) (Or.inr hB) hAEB

/-- **III.2 from Circle 3.** A straight line that has left a circle does not come back
(`outside_of_between`, Circle 3): with one point on or within the circle and a second
point not within it, any point beyond the second is outside. It is Circle 2 turned round.
Were a point between two points of the circle not within it, the second point of the
circle would be outside the circle, and so not on it. -/
theorem III_2_outside : type_of% @Elements.BookIII.Prop2 :=
  fun hA hB _ hAEB => Classical.byContradiction fun hE =>
    (outside_of_between (Or.inr hA) hE hAEB).2 hB

/-- **III.5 from Diagram-segment 2.** A circle is fixed by its centre and radius
(`circle_eq`, Diagram-segment 2). Two circles about one centre through one point are
one circle. A point of one within the other would then be both within that circle and on
it, which Generalities 4 forbids. Our III.5 takes Euclid's steps and uses neither
Diagram-segment 2 nor Circle 4. -/
theorem III_5 : type_of% @Elements.BookIII.Prop5 :=
  fun ⟨⟨_, _, _, _, _, hC₁, hC₂⟩, ⟨_, hP₁, hP₂⟩, _⟩ ⟨hE₁, hE₂⟩ =>
    inside_not_on (circle_eq hE₁ hE₂ hC₁ hC₂ rfl ▸ hP₂) hP₁

/-- **III.6 from Diagram-segment 2 and Generalities 3 and 4.** A common centre and the
point of contact would make the circles one, so the point of the inner circle within the
outer would be both within that circle and on it, which Generalities 4 forbids. Circles
touching without have no point within both, and a common centre would be one, since a
centre is within its circle (`centre_inside`, Generalities 3). Our III.6 ends contact
without with Generalities 3, Definition I.15's placement of the centre within the figure.
For contact within it takes Euclid's steps. Neither case uses Diagram-segment 2 or Circle 4. -/
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
point within and compares its parts, without Diagram-segment 4. The same short proof
gives III.6 for circles touching within, with the point of the inner circle within the
outer. -/
theorem III_5_crossing : type_of% @Elements.BookIII.Prop5 := by
  rintro E ABC CDG ⟨⟨_, C, _, _, _, hC₁, hC₂⟩, -, ⟨P, hP₂, hP₁⟩⟩ ⟨hE₁, hE₂⟩
  have h : ‖E P‖ < ‖E C‖ := len_lt_of_inside hE₁ hC₁ hP₁
  rw [Definition15 hE₂ hP₂ hC₂] at h
  exact lt_irrefl _ h

/-- **III.5 from Diagram-segment 3.** F, a point of ABC,
is as far from E as C is (Definition I.15); so it is on CDG (`on_circle_of_len_eq`, the
half of Diagram-segment 3 that Definition I.15 does not give), yet it is within CDG,
which Generalities 4 forbids. -/
theorem III_5_radius : type_of% @Elements.BookIII.Prop5 := by
  rintro E ABC CDG ⟨⟨_, C, _, _, _, hC₁, hC₂⟩, ⟨F, hF₁, hF₂⟩, -⟩ ⟨hE₁, hE₂⟩
  exact inside_not_on hF₂ (on_circle_of_len_eq hE₂ hC₂ (Definition15 hE₁ hF₁ hC₁))

/-! ## Hypotheses our measure of circumferences leaves idle

Not overlaps with a rule, but with a definition: a circumference is measured by twice the
angle standing on it (`circumference`, Definition III.9), a measure with no radius in it.
So the equal measures of III.26, and III.27 whole, hold in any two circles, and the second
clause of III.24's companion `Prop24.equalCircles` follows from its angle hypothesis alone
(the catalogue's "Near misses"). Each theorem below states the measures without the
hypothesis; an `example` beneath it gives back the statement of III.27, or of
`Prop24.equalCircles`, so a change to either statement shows up here. III.26 is no longer
among them: it concludes that the circumferences are congruent too, which in unequal circles
equal angles do not give, so it is no longer provable for any two circles. -/

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
  rw [BookIII.Circumference.standing hA hB hC hBAC.acb,
    BookIII.Circumference.standing hD hE hF hEDF.acb] at heq
  have hangle : ∠ B A C = ∠ E D F := Magnitude.eq_of_add_self_eq heq
  refine ⟨hangle, fun hGA hHD => ?_⟩
  rw [BookIII.Prop20 hG hA hB hC hGA, BookIII.Prop20 hH hD hE hF hHD, hangle]

example : type_of% @Elements.BookIII.Prop27 :=
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

/-! ## A rule that a proposition gives back -/

/-- **Diagram-angle 3 from I.13.** The angle beside a right angle is right
(`adjacent_eq_of_right`, Diagram-angle 3). I.13 makes the two angles together two right
angles, and Common Notion 3 takes the one right angle away. I.13 does not rest on the
rule, so the rule is a theorem of the others. Seventeen proofs from II.1 on, III.1's
porism among them, use it where I.13 would serve: sixteen call it themselves, and III.19
reaches it only through III.1's helper `Prop1.perpendicular`. -/
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

/-- **Circle 3 from Circle 2.** Were the point beyond within the circle or on it, the point
between would be within the circle (`inside_of_between`, Circle 2), which it is not. -/
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
 Elements.Postulate1,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.exists_point_on_circle,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.not_between_of_between_between,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.I_2

/--
info: 'Audit.I_3' depends on axioms: [propext,
 Classical.choice,
 Elements.Postulate1,
 Elements.Postulate3,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.exists_point_on_circle,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.ne_of_between,
 Elements.Tacit.not_between_of_between_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.I_3

/--
info: 'Audit.I_7' depends on axioms: [propext,
 Classical.choice,
 Elements.Postulate1,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.centre_unique,
 Elements.Tacit.len_symm,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.not_same_side_of_circles_meet,
 Elements.Tacit.on_circle_of_len_eq]
-/
#guard_msgs in
#print axioms Audit.I_7

/--
info: 'Audit.I_23' depends on axioms: [propext,
 Classical.choice,
 Elements.Postulate1,
 Quot.sound,
 Elements.Tacit.angle_symm,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.exists_point,
 Elements.Tacit.len_self,
 Elements.Tacit.line_unique,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.superposition]
-/
#guard_msgs in
#print axioms Audit.I_23

/-- info: 'Audit.III_2' depends on axioms: [Elements.Tacit.inside_of_between] -/
#guard_msgs in
#print axioms Audit.III_2

/--
info: 'Audit.III_2_outside' depends on axioms: [propext, Classical.choice, Quot.sound, Elements.Tacit.outside_of_between]
-/
#guard_msgs in
#print axioms Audit.III_2_outside

/--
info: 'Audit.III_5' depends on axioms: [Classical.choice, Elements.Tacit.circle_eq, Elements.Tacit.inside_not_on]
-/
#guard_msgs in
#print axioms Audit.III_5

/--
info: 'Audit.III_6' depends on axioms: [Classical.choice,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circle_eq,
 Elements.Tacit.inside_not_on]
-/
#guard_msgs in
#print axioms Audit.III_6

/--
info: 'Audit.III_5_radius' depends on axioms: [Classical.choice,
 Elements.Definition15,
 Elements.Tacit.inside_not_on,
 Elements.Tacit.on_circle_of_len_eq]
-/
#guard_msgs in
#print axioms Audit.III_5_radius

/--
info: 'Audit.III_5_crossing' depends on axioms: [Classical.choice,
 Elements.Definition15,
 Elements.Tacit.len_lt_of_inside,
 Elements.Tacit.lt_irrefl]
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
 Elements.Tacit.adjacent_eq_of_right,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_rotate,
 Elements.Tacit.area_swap,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_of_between_left,
 Elements.Tacit.between_of_between_right,
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_of_on_inside_outside,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_between,
 Elements.Tacit.exists_point_opposite_side,
 Elements.Tacit.exists_point_same_side,
 Elements.Tacit.inside_not_on,
 Elements.Tacit.inside_of_len_lt,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_lt_of_inside,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.ne_of_between,
 Elements.Tacit.ne_of_between_ends,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_between_of_between_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.on_line_of_between,
 Elements.Tacit.on_line_of_between_ends,
 Elements.Tacit.pasch2,
 Elements.Tacit.pasch3,
 Elements.Tacit.pasch4,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_or,
 Elements.Tacit.same_side_refl,
 Elements.Tacit.same_side_symm,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition,
 Elements.Tacit.triple_incidence1,
 Elements.Tacit.triple_incidence2]
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
 Elements.Tacit.adjacent_eq_of_right,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_rotate,
 Elements.Tacit.area_swap,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_of_between_left,
 Elements.Tacit.between_of_between_right,
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_of_on_inside_outside,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_between,
 Elements.Tacit.exists_point_opposite_side,
 Elements.Tacit.exists_point_same_side,
 Elements.Tacit.inside_not_on,
 Elements.Tacit.inside_of_len_lt,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_lt_of_inside,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.ne_of_between,
 Elements.Tacit.ne_of_between_ends,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_between_of_between_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.on_line_of_between,
 Elements.Tacit.on_line_of_between_ends,
 Elements.Tacit.pasch2,
 Elements.Tacit.pasch3,
 Elements.Tacit.pasch4,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_or,
 Elements.Tacit.same_side_refl,
 Elements.Tacit.same_side_symm,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition,
 Elements.Tacit.triple_incidence1,
 Elements.Tacit.triple_incidence2]
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
 Elements.Tacit.adjacent_eq_of_right,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_rotate,
 Elements.Tacit.area_swap,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_of_between_left,
 Elements.Tacit.between_of_between_right,
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_of_on_inside_outside,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_between,
 Elements.Tacit.exists_point_opposite_side,
 Elements.Tacit.exists_point_same_side,
 Elements.Tacit.inside_not_on,
 Elements.Tacit.inside_of_len_lt,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_lt_of_inside,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.ne_of_between,
 Elements.Tacit.ne_of_between_ends,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_between_of_between_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.on_line_of_between,
 Elements.Tacit.on_line_of_between_ends,
 Elements.Tacit.pasch2,
 Elements.Tacit.pasch3,
 Elements.Tacit.pasch4,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_or,
 Elements.Tacit.same_side_refl,
 Elements.Tacit.same_side_symm,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition,
 Elements.Tacit.triple_incidence1,
 Elements.Tacit.triple_incidence2]
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
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_rotate,
 Elements.Tacit.area_swap,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_of_between_left,
 Elements.Tacit.between_of_between_right,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_between,
 Elements.Tacit.inside_of_len_lt,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_lt_of_inside,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.ne_of_between,
 Elements.Tacit.ne_of_between_ends,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_between_of_between_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.on_line_of_between,
 Elements.Tacit.on_line_of_between_ends,
 Elements.Tacit.pasch2,
 Elements.Tacit.pasch3,
 Elements.Tacit.pasch4,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_or,
 Elements.Tacit.same_side_symm,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition,
 Elements.Tacit.triple_incidence1,
 Elements.Tacit.triple_incidence2]
-/
#guard_msgs in
#print axioms Audit.adjacent_eq_of_right

/--
info: 'Audit.inside_of_between' depends on axioms: [propext, Classical.choice, Quot.sound, Elements.Tacit.outside_of_between]
-/
#guard_msgs in
#print axioms Audit.inside_of_between

/-- info: 'Audit.outside_of_between' depends on axioms: [Elements.Tacit.inside_of_between] -/
#guard_msgs in
#print axioms Audit.outside_of_between
