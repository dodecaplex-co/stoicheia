import Elements

/-!
# Cutting and contact within: the earlier statements recovered

Two different circles with centres that meet at two points each pass within the other.
Of two different circles with centres, if no point of the inner circle is outside the
outer, some point of it is within the outer. These bridges recover the statements of
III.5, III.6, III.11 and III.13 before the change to cutting and contact within in brief
0008, section 7. Here the names ending in `today`, and `TouchesInternallyToday`, refer to
those earlier statements, at `bd3b72a` on 19 October 2026.

The bridges use III.7, III.8 and III.10 and rest on Diagram-segment 2. They belong after
those propositions, and do not enter the proofs of III.5 and III.6. `lake build Audit`
checks this file, including the axiom lists pinned below; the certificate imports none
of it.
-/

set_option warningAsError true

namespace Audit

open Elements Elements.Tacit Elements.BookIII

/-- Let O and O' be the centres of two different circles α and β, and let B and C be
distinct points common to both circles. A point of α is within β: the end of α's diameter
on the line of the centres that is nearer O' (III.7 when O' is within α, III.8 when it is
outside; O' itself when it is on α). -/
theorem cut_point {α β : Circle} {O O' B C : Point} (hO : Centre O α) (hO' : Centre O' β)
    (hne : α ≠ β) (hBC : B ≠ C) (hBα : OnCircle B α) (hBβ : OnCircle B β)
    (hCα : OnCircle C α) (hCβ : OnCircle C β) :
    ∃ P : Point, OnCircle P α ∧ InsideCircle P β := by
  have hOO' : O ≠ O' := fun e => hne (circle_eq hO (e ▸ hO') hBα hBβ rfl)
  /- If the least line from O' to α ends at X, X is within β unless it is B; and if it is
     B, then C, also on α, is farther from O' than B, though both are on β. -/
  have finish : ∀ X : Point, OnCircle X α → (∀ K : Point, OnCircle K α → K ≠ X →
      ‖O' X‖ < ‖O' K‖) → ∃ P : Point, OnCircle P α ∧ InsideCircle P β := by
    intro X hX hleast
    by_cases hBX : B = X
    · subst hBX
      have h := hleast C hCα hBC.symm
      rw [Definition15 hO' hBβ hCβ] at h
      exact absurd h (lt_irrefl _)
    · exact ⟨X, hX, inside_of_len_lt hO' hBβ (hleast B hBα hBX)⟩
  by_cases hon : OnCircle O' α
  · exact ⟨O', hon, centre_inside hO'⟩
  by_cases hin : InsideCircle O' α
  · /- III.7 applies with O' on the diameter AD, between O and D. -/
    obtain ⟨L, hO_L, hO'_L⟩ := Postulate1 O O' hOO'
    obtain ⟨D, hD, -, hDO'O⟩ := line_circle_beyond hin hO'_L hO_L hOO'
    obtain ⟨A, hA, -, hAOO'⟩ := line_circle_beyond (centre_inside hO) hO_L hO'_L hOO'.symm
    have hOO'D : Between O O' D := between_symm hDO'O
    have hAOD : Between A O D := between_of_between_right hAOO' hOO'D
    exact finish D hD (Prop7 hO hA hD hAOD hOO'D).2.1
  · /- III.8 applies with O' outside α, G the nearer end of the diameter and A the farther. -/
    have hout : OutsideCircle O' α := ⟨hin, hon⟩
    obtain ⟨L, hO'_L, hO_L⟩ := Postulate1 O' O hOO'.symm
    obtain ⟨A, hA, hA_L, hAOO'⟩ := line_circle_beyond (centre_inside hO) hO_L hO'_L hOO'.symm
    have hAO : A ≠ O := ne_of_between hAOO'
    obtain ⟨G, hG, hG_L, hGOA⟩ := line_circle_beyond (centre_inside hO) hO_L hA_L hAO
    have hGO' : G ≠ O' := fun e => hon (e ▸ hG)
    have hGO : G ≠ O := ne_of_centre_of_on hO hG
    have hO'GO : Between O' G O := by
      rcases between_cases hGO'.symm hGO hOO'.symm hO'_L hG_L hO_L with h | h | h
      · exact h
      · exact absurd
          (Prop2.within ⟨O, hO⟩ (Or.inr hG) (Or.inl (centre_inside hO)) h) hin
      · exact absurd hGOA (not_between_of_between_between h (between_symm hAOO'))
    have hO'GA : Between O' G A := between_of_between_right hO'GO hGOA
    exact finish G hG (Prop8 ⟨O, hO⟩ hout hA hG hO'GA
      (fun M hM => centre_unique hM hO ▸ hGOA)).2.2.1

/-- Two different circles, each with a centre, that meet at two points cut one another. -/
theorem CirclesCut.of_meet {α β : Circle} (hα : ∃ O : Point, Centre O α)
    (hβ : ∃ O : Point, Centre O β) (hne : α ≠ β) (h : CirclesMeet α β) : CirclesCut α β := by
  obtain ⟨O, hO⟩ := hα
  obtain ⟨O', hO'⟩ := hβ
  obtain ⟨B, C, hBC, hBα, hBβ, hCα, hCβ⟩ := h
  exact ⟨⟨B, C, hBC, hBα, hBβ, hCα, hCβ⟩,
    cut_point hO hO' hne hBC hBα hBβ hCα hCβ,
    cut_point hO' hO (Ne.symm hne) hBC hBβ hBα hCβ hCα⟩

/-- For two different circles with centres, if no point of the inner circle is outside
the outer, some point of it is within the outer. Otherwise every point of it would be on
the outer, and three of them would make the circles one (III.10). -/
theorem within_point {α β : Circle} (hα : ∃ O : Point, Centre O α)
    (hβ : ∃ O : Point, Centre O β) (hne : α ≠ β)
    (hnot : ∀ P : Point, OnCircle P β → ¬ OutsideCircle P α) :
    ∃ P : Point, OnCircle P β ∧ InsideCircle P α := by
  refine Classical.byContradiction fun h => ?_
  have on : ∀ P : Point, OnCircle P β → OnCircle P α := fun P hP =>
    Classical.byContradiction fun hPα => hnot P hP ⟨fun hi => h ⟨P, hP, hi⟩, hPα⟩
  obtain ⟨X, hX, -⟩ := exists_point_on_circle β []
  obtain ⟨Y, hY, hYX⟩ := exists_point_on_circle β [X]
  obtain ⟨Z, hZ, hZXY⟩ := exists_point_on_circle β [X, Y]
  have hXY : X ≠ Y := fun e => hYX (e ▸ List.mem_singleton_self X)
  have hXZ : X ≠ Z := fun e => hZXY (e ▸ List.mem_cons_self)
  have hYZ : Y ≠ Z := fun e => hZXY (e ▸ List.mem_cons_of_mem _ (List.mem_singleton_self Y))
  exact hne (Prop10 hα hβ (on X hX) hX (on Y hY) hY (on Z hZ) hZ hXY hXZ hYZ)

/-- Two different circles ABC and CDG, each with a centre and meeting at two distinct
points, cannot have E as a common centre. This follows from the restated III.5. -/
example {E : Point} {ABC CDG : Circle} (hα : ∃ O : Point, Centre O ABC)
    (hβ : ∃ O : Point, Centre O CDG) (hne : ABC ≠ CDG) (hcut : CirclesMeet ABC CDG) :
    ¬ (Centre E ABC ∧ Centre E CDG) :=
  Prop5 (CirclesCut.of_meet hα hβ hne hcut)

/-- Two different circles ABC and CDG meeting at two distinct points cannot have E as a
common centre. This recovers the earlier III.5 without a further hypothesis: the supposed
common centre E is the centre each circle needs for the bridge. -/
theorem III_5_today {E : Point} {ABC CDG : Circle} (hne : ABC ≠ CDG)
    (hcut : CirclesMeet ABC CDG) : ¬ (Centre E ABC ∧ Centre E CDG) :=
  fun ⟨h₁, h₂⟩ => Prop5 (CirclesCut.of_meet ⟨E, h₁⟩ ⟨E, h₂⟩ hne hcut) ⟨h₁, h₂⟩

/-- The earlier contact within: the circles meet, are two, and no point of the inner
circle is outside the outer. -/
def TouchesInternallyToday (α β : Circle) (C : Point) : Prop :=
  OnCircle C α ∧ OnCircle C β ∧ α ≠ β ∧ ∀ P : Point, OnCircle P β → ¬ OutsideCircle P α

/-- If ABC and CDE touch at C under the earlier reading, either one within the other or
without, they cannot have F as a common centre. For contact within the circles are
different and no point of the inner is outside the outer; for contact without no point is
within both. The restated III.6 and the bridge recover this conclusion, with the supposed
common centre supplying a centre for each circle. -/
theorem III_6_today {C F : Point} {ABC CDE : Circle}
    (htouch : TouchesInternallyToday ABC CDE C ∨ TouchesInternallyToday CDE ABC C ∨
      TouchesExternally ABC CDE C) : ¬ (Centre F ABC ∧ Centre F CDE) := by
  rintro ⟨h₁, h₂⟩
  refine Prop6 (C := C) ?_ ⟨h₁, h₂⟩
  rcases htouch with ⟨hC₁, hC₂, hne, hnot⟩ | ⟨hC₂, hC₁, hne, hnot⟩ | h
  · exact Or.inl ⟨hC₁, hC₂, within_point ⟨F, h₁⟩ ⟨F, h₂⟩ hne hnot, hnot⟩
  · exact Or.inr (Or.inl ⟨hC₂, hC₁, within_point ⟨F, h₂⟩ ⟨F, h₁⟩ hne hnot, hnot⟩)
  · exact Or.inr (Or.inr h)

/-- Let F and G be the centres of ABC and ADE. If the circles are different, meet at A,
and no point of ADE is outside ABC, then G lies between F and A. This recovers the earlier
III.11 from III.11 read with the new contact within; the given centres supply those the
bridge needs. -/
theorem III_11_today {A F G : Point} {ABC ADE : Circle} (hF : Centre F ABC) (hG : Centre G ADE)
    (htouch : TouchesInternallyToday ABC ADE A) : Between F G A := by
  obtain ⟨hA₁, hA₂, hne, hnot⟩ := htouch
  exact Prop11 hF hG ⟨hA₁, hA₂, within_point ⟨F, hF⟩ ⟨G, hG⟩ hne hnot, hnot⟩

/-- Let ABDC, EBFD and ACK each have a centre. If ABDC and EBFD are different, meet at D,
and no point of one is outside the other, any common point B equals D. If ACK and ABDC
meet at A and no point is within both, any common point C equals A. This recovers the
earlier III.13 from the restated III.13: the given centres supply those the bridge needs,
and the conclusion about contact without is unchanged. -/
theorem III_13_today {A B C D : Point} {ABDC EBFD ACK : Circle}
    (hABDC : ∃ G : Point, Centre G ABDC) (hEBFD : ∃ H : Point, Centre H EBFD)
    (hACK : ∃ O : Point, Centre O ACK) :
    ((TouchesInternallyToday ABDC EBFD D ∨ TouchesInternallyToday EBFD ABDC D) →
      OnCircle B ABDC → OnCircle B EBFD → B = D) ∧
    (TouchesExternally ACK ABDC A → OnCircle C ACK → OnCircle C ABDC → C = A) := by
  obtain ⟨h₁, h₂⟩ := Prop13 (B := B) (C := C) hABDC hEBFD hACK
  refine ⟨fun h => h₁ ?_, h₂⟩
  rcases h with ⟨hD₁, hD₂, hne, hnot⟩ | ⟨hD₁, hD₂, hne, hnot⟩
  · exact Or.inl ⟨hD₁, hD₂, within_point hABDC hEBFD hne hnot, hnot⟩
  · exact Or.inr ⟨hD₁, hD₂, within_point hEBFD hABDC hne hnot, hnot⟩

/-- The recovered III.5 has exactly the earlier statement. -/
example : type_of% @III_5_today =
    ∀ {E : Point} {ABC CDG : Circle}, ABC ≠ CDG → CirclesMeet ABC CDG →
      ¬ (Centre E ABC ∧ Centre E CDG) := rfl

end Audit

/-! ## What the bridges rest on

These lists include Diagram-segment 2. They check the bridges' dependencies, separately
from the lists for III.5 and III.6 below, whose proofs use neither Diagram-segment 2 nor
Circle 4, which is now a theorem proved from I.7 using Diagram-segment 2 (19 October 2026).
The bridge through III.7 and III.8 uses III.2 (`Prop2.within`), with the given centre, to
order the points on the straight line through the centres. None of these lists includes
Circle 3, so no bridge uses Circle 2 either, which is now proved from Circle 3. All seven
bridge lists include `exists_centre` through III.1's construction. Nothing in this file
enters the certificate.
-/

/--
info: 'Audit.III_5_today' depends on axioms: [propext,
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
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circle_eq,
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
 Elements.Tacit.on_circle_of_len_eq,
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
#print axioms Audit.III_5_today

/--
info: 'Audit.III_6_today' depends on axioms: [propext,
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
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circle_eq,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_between,
 Elements.Tacit.exists_point_on_circle,
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
#print axioms Audit.III_6_today

/--
info: 'Audit.III_11_today' depends on axioms: [propext,
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
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circle_eq,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_between,
 Elements.Tacit.exists_point_on_circle,
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
#print axioms Audit.III_11_today

/--
info: 'Audit.III_13_today' depends on axioms: [propext,
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
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circle_eq,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_between,
 Elements.Tacit.exists_point_on_circle,
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
#print axioms Audit.III_13_today

/--
info: 'Audit.cut_point' depends on axioms: [propext,
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
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circle_eq,
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
 Elements.Tacit.on_circle_of_len_eq,
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
#print axioms Audit.cut_point

/--
info: 'Audit.CirclesCut.of_meet' depends on axioms: [propext,
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
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circle_eq,
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
 Elements.Tacit.on_circle_of_len_eq,
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
#print axioms Audit.CirclesCut.of_meet

/--
info: 'Audit.within_point' depends on axioms: [propext,
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
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circle_eq,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.exists_centre,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_between,
 Elements.Tacit.exists_point_on_circle,
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
#print axioms Audit.within_point

/-! ## What III.5 and III.6 rest on

The pins from the staged proofs follow them home: Definition I.15, Postulate 1 and
thirteen tacit rules, with Lean's choice. Neither Diagram-segment 2 (`circle_eq`) nor an
admitted proof is among them, and the build fails if one enters. Circle 4 is now a theorem
whose proof uses `circle_eq`, so the pins also exclude that route. Circle 3 does not
appear, so neither does Circle 2, now proved from it.
-/

/--
info: 'Elements.BookIII.Prop5' depends on axioms: [Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.inside_not_on,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.ne_of_between,
 Elements.Tacit.not_lt_zero]
-/
#guard_msgs in
#print axioms Elements.BookIII.Prop5

/--
info: 'Elements.BookIII.Prop6' depends on axioms: [Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.inside_not_on,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.ne_of_between,
 Elements.Tacit.not_lt_zero]
-/
#guard_msgs in
#print axioms Elements.BookIII.Prop6
