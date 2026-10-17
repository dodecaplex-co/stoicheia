import Elements

/-!
# Overlaps: propositions a rule already contains

Some of System E's rules, which we take as axioms, already say what Euclid later proves,
or give it in a few lines. Astra found the clearest case, III.2, in the outside review
(`docs/reports/outside-review-01.md`), and compiled its one-line proof; we are grateful.
The catalogue in `docs/reports/overlaps.md` lists every case we found, and this file
proves each "states it" or "gives it at once" row again, from the rules alone.

Each theorem's type is the proposition's own (`type_of% @Elements.BookIII.Prop2`), so a
change to a statement shows up here too. At the end, `#guard_msgs` pins the axioms Lean
reports for each theorem: the rules named in the catalogue, and nothing else. The last
theorem runs the other way: it proves a rule from a proposition.

Nothing imports this file, and it is not part of the default build. `lake build Audit`
checks it. If a statement or a rule changes so that one of these proofs fails, that is
the signal to bring the catalogue up to date.
-/

set_option warningAsError true

namespace Audit

open Elements Elements.Tacit

/-! ## Rules that state a proposition, or give it at once -/

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
I.23. The certificate lets only I.4 and I.8 use superposition, as System E asks, so our
I.23 is Euclid's construction, by I.22 and I.8. It rests on superposition all the same,
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
and I.19, and never calls the rule; but III.1, which finds its centre, does, to put the
middle point of a chord within the circle. -/
theorem III_2 : type_of% @Elements.BookIII.Prop2 :=
  fun _ hA hB _ hAEB => inside_of_between (Or.inr hA) (Or.inr hB) hAEB

/-- **III.5 from Diagram-segment 2.** A circle is fixed by its centre and radius
(`circle_eq`, Diagram-segment 2). Two circles about one centre through one point are
one circle, so two circles that cut one another cannot share a centre. Our III.5 takes
Euclid's steps and ends with this rule. -/
theorem III_5 : type_of% @Elements.BookIII.Prop5 :=
  fun hne ⟨_, _, _, hC₁, hC₂, _, _⟩ ⟨hE₁, hE₂⟩ => hne (circle_eq hE₁ hE₂ hC₁ hC₂ rfl)

/-- **III.6 from Diagram-segment 2 and Generalities 3.** Circles touching within are two
circles through one point, so Diagram-segment 2 again forbids a common centre. Circles
touching without have no point within both, and a common centre would be one, since a
centre is within its circle (`centre_inside`, Generalities 3). Our III.6 takes Euclid's
steps and ends with these rules. -/
theorem III_6 : type_of% @Elements.BookIII.Prop6 := by
  rintro C F ABC CDE (⟨hC₁, hC₂, hne, -⟩ | ⟨hC₂, hC₁, hne, -⟩ | ⟨-, -, hout⟩) ⟨hF₁, hF₂⟩
  · exact hne (circle_eq hF₁ hF₂ hC₁ hC₂ rfl)
  · exact hne (circle_eq hF₂ hF₁ hC₂ hC₁ rfl)
  · exact hout F (centre_inside hF₁) (centre_inside hF₂)

/-! ## A rule that a proposition gives back -/

/-- **Diagram-angle 3 from I.13.** The angle beside a right angle is right
(`adjacent_eq_of_right`, Diagram-angle 3). I.13 makes the two angles together two right
angles, and Common Notion 3 takes the one right angle away. I.13 does not rest on the
rule, so the rule is a theorem of the others; sixteen proofs, from II.1 on, call it
where I.13 would serve. -/
theorem adjacent_eq_of_right : type_of% @Elements.Tacit.adjacent_eq_of_right := by
  intro A B C D L hA hB hACB hD hright
  have hAB : A ≠ B := ne_of_between_ends hACB
  have hABD : ¬ Collinear A B D := fun ⟨M, hAM, hBM, hDM⟩ =>
    hD (line_unique hAB hAM hBM hA hB ▸ hDM)
  have h13 : ∠ A C D + ∠ D C B = ∟ + ∟ := BookI.Prop13 hACB hABD
  rw [hright, add_comm ∟] at h13
  rw [hright]
  exact (CommonNotion3 h13 rfl).symm

end Audit

/-! ## What each proof rests on

Lean's own report, pinned. `Classical.choice` comes in with any rule that speaks of a
length, an angle or an area, for the magnitudes are chosen (`Foundations/Magnitudes.lean`);
`propext` and `Quot.sound` with the proofs that argue by cases. -/

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

/-- info: 'Audit.III_5' depends on axioms: [Classical.choice, Elements.Tacit.circle_eq] -/
#guard_msgs in
#print axioms Audit.III_5

/--
info: 'Audit.III_6' depends on axioms: [Classical.choice, Elements.Tacit.centre_inside, Elements.Tacit.circle_eq]
-/
#guard_msgs in
#print axioms Audit.III_6

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
 Elements.Tacit.inside_of_between,
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
