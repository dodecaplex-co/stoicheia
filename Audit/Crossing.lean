import Elements

/-!
# Cutting and contact within: the earlier statements recovered

Two different circles that meet at two points each pass within the other.
Of two different circles, if no point of the inner circle is outside the
outer, some point of it is within the outer. These bridges recover the statements of
III.5, III.6, III.11 and III.13 before the change to cutting and contact within in brief
0008, section 7. Here the names ending in `today`, and `TouchesInternallyToday`, refer to
those earlier statements, at `bd3b72a` on 19 October 2026.

The first bridge, `CirclesCut.of_meet`, with its step `CirclesCut.cut_point`, was proved
here; since 26 October 2026 it is proved in `Elements/BookIII/Cutting.lean`, after III.8,
for III.10's last step cites it with III.5. This file no longer proves a copy. It checks
that each of the two theorems there has exactly the statement proved here before, and pins
their axioms below with the others.

The bridges use III.7, III.8 and III.10 and rest on Diagram-segment 2. They belong after
those propositions, and do not enter the proofs of III.5 and III.6. `lake build Audit`
checks this file, including the axiom lists pinned below. The certificate imports none of
it; it reaches `CirclesCut.of_meet` through III.10, which cites it.
-/

set_option warningAsError true

namespace Audit

open Elements Elements.Tacit Elements.BookIII

/-- The step of the crossing bridge, proved in `Elements/BookIII/Cutting.lean`, has exactly
the statement this file proved before under the name cut_point. -/
example : type_of% @CirclesCut.cut_point =
    ∀ {α β : Circle} {B C : Point}, α ≠ β → B ≠ C → OnCircle B α → OnCircle B β →
      OnCircle C α → OnCircle C β → ∃ P : Point, OnCircle P α ∧ InsideCircle P β := rfl

/-- The crossing bridge, proved in `Elements/BookIII/Cutting.lean`, has exactly the
statement this file proved before under the same name in its own namespace. -/
example : type_of% @CirclesCut.of_meet =
    ∀ {α β : Circle}, α ≠ β → CirclesMeet α β → CirclesCut α β := rfl

/-- The earlier statement of the crossing bridge, proved by the theorem in `Elements`. -/
example {α β : Circle} (hne : α ≠ β) (h : CirclesMeet α β) : CirclesCut α β :=
  CirclesCut.of_meet hne h

/-- For two different circles, if no point of the inner circle is outside
the outer, some point of it is within the outer. Otherwise every point of it would be on
the outer, and three of them would make the circles one (III.10). -/
theorem within_point {α β : Circle} (hne : α ≠ β)
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
  exact hne (Prop10 (on X hX) hX (on Y hY) hY (on Z hZ) hZ hXY hXZ hYZ)

/-- Two different circles ABC and CDG meeting at two distinct points cannot have E
as a common centre. This follows from the restated III.5 through the bridge. -/
example {E : Point} {ABC CDG : Circle} (hne : ABC ≠ CDG) (hcut : CirclesMeet ABC CDG) :
    ¬ (Centre E ABC ∧ Centre E CDG) :=
  Prop5 (CirclesCut.of_meet hne hcut)

/-- Two different circles ABC and CDG meeting at two distinct points cannot have E as a
common centre. This recovers the earlier III.5 through the bridge, which obtains its
centres internally. -/
theorem III_5_today {E : Point} {ABC CDG : Circle} (hne : ABC ≠ CDG)
    (hcut : CirclesMeet ABC CDG) : ¬ (Centre E ABC ∧ Centre E CDG) :=
  fun ⟨h₁, h₂⟩ => Prop5 (CirclesCut.of_meet hne hcut) ⟨h₁, h₂⟩

/-- The earlier contact within: the circles meet, are two, and no point of the inner
circle is outside the outer. -/
def TouchesInternallyToday (α β : Circle) (C : Point) : Prop :=
  OnCircle C α ∧ OnCircle C β ∧ α ≠ β ∧ ∀ P : Point, OnCircle P β → ¬ OutsideCircle P α

/-- If ABC and CDE touch at C under the earlier reading, either one within the other or
without, they cannot have F as a common centre. For contact within the circles are
different and no point of the inner is outside the outer; for contact without no point is
within both. The restated III.6 and the bridge recover this conclusion; the bridge
obtains any required centres internally. -/
theorem III_6_today {C F : Point} {ABC CDE : Circle}
    (htouch : TouchesInternallyToday ABC CDE C ∨ TouchesInternallyToday CDE ABC C ∨
      TouchesExternally ABC CDE C) : ¬ (Centre F ABC ∧ Centre F CDE) := by
  rintro ⟨h₁, h₂⟩
  refine Prop6 (C := C) ?_ ⟨h₁, h₂⟩
  rcases htouch with ⟨hC₁, hC₂, hne, hnot⟩ | ⟨hC₂, hC₁, hne, hnot⟩ | h
  · exact Or.inl ⟨hC₁, hC₂, within_point hne hnot, hnot⟩
  · exact Or.inr (Or.inl ⟨hC₂, hC₁, within_point hne hnot, hnot⟩)
  · exact Or.inr (Or.inr h)

/-- Let F and G be the centres of ABC and ADE. If the circles are different, meet at A,
and no point of ADE is outside ABC, then G lies between F and A. This recovers the earlier
III.11 from III.11 read with the new contact within. F and G remain in the statement
because its conclusion orders them with A. -/
theorem III_11_today {A F G : Point} {ABC ADE : Circle} (hF : Centre F ABC) (hG : Centre G ADE)
    (htouch : TouchesInternallyToday ABC ADE A) : Between F G A := by
  obtain ⟨hA₁, hA₂, hne, hnot⟩ := htouch
  exact Prop11 hF hG ⟨hA₁, hA₂, within_point hne hnot, hnot⟩

/-- If ABDC and EBFD are different, meet at D, and no point of one is outside the other,
any common point B equals D. If ACK and ABDC meet at A and no point is within both, any
common point C equals A. This strengthens the earlier III.13 by obtaining centres
internally. It still implies the earlier form with three supplied centres, since that
form follows by ignoring those extra hypotheses. Contact without is unchanged. -/
theorem III_13_today {A B C D : Point} {ABDC EBFD ACK : Circle} :
    ((TouchesInternallyToday ABDC EBFD D ∨ TouchesInternallyToday EBFD ABDC D) →
      OnCircle B ABDC → OnCircle B EBFD → B = D) ∧
    (TouchesExternally ACK ABDC A → OnCircle C ACK → OnCircle C ABDC → C = A) := by
  obtain ⟨h₁, h₂⟩ := Prop13 (B := B) (C := C) (ABDC := ABDC) (EBFD := EBFD) (ACK := ACK)
  refine ⟨fun h => h₁ ?_, h₂⟩
  rcases h with ⟨hD₁, hD₂, hne, hnot⟩ | ⟨hD₁, hD₂, hne, hnot⟩
  · exact Or.inl ⟨hD₁, hD₂, within_point hne hnot, hnot⟩
  · exact Or.inr ⟨hD₁, hD₂, within_point hne hnot, hnot⟩

/-- The recovered III.5 has exactly the earlier statement. -/
example : type_of% @III_5_today =
    ∀ {E : Point} {ABC CDG : Circle}, ABC ≠ CDG → CirclesMeet ABC CDG →
      ¬ (Centre E ABC ∧ Centre E CDG) := rfl

end Audit

/-! ## What the bridges rest on

These lists include Diagram-segment 2. They check the bridges' dependencies, separately
from the lists for III.5 and III.6 below, whose proofs cite neither Diagram-segment 2 nor
Circle 4, which is now a theorem proved from I.7 using Diagram-segment 2 (19 October 2026),
and since 26 October 2026 rest on neither, through the proved rules they use or otherwise
(below). The bridge through III.7
and III.8 uses III.2 (`Prop2.within`) to order the points on the straight line through the
centres, which `CirclesCut.cut_point` takes from the rule. Two of the lists pin the
theorems `Elements.CirclesCut.cut_point` and `Elements.CirclesCut.of_meet`, which this file
proved until 26 October 2026; moving them into `Elements` changed no list. Circle 2 and
Circle 3 are theorems since 24 October 2026, and Circle 1 since 26 October 2026, all three
proved after III.2, so no list can show them; no bridge uses Circle 2 or Circle 3, and five
of the seven lists showed Circle 1 while it was an axiom. All seven bridge lists
include `exists_centre`, and each bridge reaches III.1 through III.8, which takes its centre
by III.1's construction (`Prop1.of_circle`) since 26 October 2026 (#547); every axiom
`Prop1.of_circle` rests on was in the lists already, so none changed. `centre_unique` is a
theorem since axiom wave one, so no list here shows a call to it. Nothing in this file
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
#print axioms Audit.III_13_today

/--
info: 'Elements.CirclesCut.cut_point' depends on axioms: [propext,
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
 Elements.Tacit.circle_eq,
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
#print axioms Elements.CirclesCut.cut_point

/--
info: 'Elements.CirclesCut.of_meet' depends on axioms: [propext,
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
 Elements.Tacit.circle_eq,
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
#print axioms Elements.CirclesCut.of_meet

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
#print axioms Audit.within_point

/-! ## What III.5 and III.6 rest on

The pins from the staged proofs followed them home. Since 26 October 2026 they list
Definition I.15, Postulates 1 and 3 and 12 tacit rules for III.5, and 16 for III.6, whose
`centre_inside`, for contact without, adds Points 8, Intersections 4, `len_symm` and
`lt_trans`. Our radius rule (`Elements.Tacit.radius_ne_zero`) is among them, and neither
Diagram-segment 2 (`Elements.Tacit.circle_eq`) nor Circle 1
(`Elements.Tacit.between_of_inside_chord`) is. From the second axiom retirement (proved on
19 October 2026) until then, the proved rules the proofs use, such as `centre_inside`
beneath Book Zero's `ne_of_centre_of_on`, rested on both, and on Postulate 3, to show that a
radius is never nothing (`RuleProofs.Circle.radius_ne_zero`); that lemma now takes it from
the radius rule, and Postulate 3 enters through Metric 1, proved from the rule, and, for
III.6, through `RuleProofs.Circle.length_pos` beneath `centre_inside`. So the pins
show again that the proofs avoid Circle 4, a theorem whose proof uses `circle_eq`. They
check the names of these two declarations' axioms, and the build fails if an admitted proof
(`sorry`) enters. Circle 2 and Circle 3, theorems since 24 October 2026, and Circle 1, a
theorem since 26 October 2026, all three proved after III.2, cannot appear here; the
certificate shows that neither proof uses them, for neither cites III.2, as a use of any of
them would make it.
-/

/--
info: 'Elements.BookIII.Prop5' depends on axioms: [propext,
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
#print axioms Elements.BookIII.Prop5

/--
info: 'Elements.BookIII.Prop6' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.between_symm,
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
#print axioms Elements.BookIII.Prop6
