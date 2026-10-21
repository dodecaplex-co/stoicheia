import Elements.BookI.Prop04
import Elements.BookI.Prop08
import Elements.Figure.Superposition

/-!
# Superposition: the proofs and their foundations

The first two pins record the complete dependencies of I.4 and I.8, including the
restricted axiom. The pure-calculus pins record soundness, reduction to placement
with its side, fixed-vocabulary derivations and the exportability of conclusions.
They also keep the satisfiability and valuation warnings, the two unrestricted
eliminator observations and the passage to numbered symbols visible. They use only
Lean's logical axioms; they establish no global non-derivability claim.

The geometric pins record each cited law and the named-lines proof used for I.4.
Their combined proof uses no construction rule. The last two pins distinguish
I.4's list of such laws from I.8's adapter of I.7, whose proof uses constructions
and inherits the restricted rule through I.4.
-/

/--
info: 'Elements.BookI.Prop4' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_congruent,
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
#print axioms Elements.BookI.Prop4

/--
info: 'Elements.BookI.Prop8' depends on axioms: [propext,
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
#print axioms Elements.BookI.Prop8

/--
info: 'Elements.Superposition.Derives.sound' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Elements.Superposition.Derives.sound

/--
info: 'Elements.Superposition.Rule.of_placement' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.Rule.of_placement

/--
info: 'Elements.Superposition.Derives.no_construction' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Elements.Superposition.Derives.no_construction

/--
info: 'Elements.Superposition.exportable_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.exportable_iff

/--
info: 'Elements.Superposition.not_exportable_second' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.not_exportable_second

/--
info: 'Elements.Superposition.not_exportable_third' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.not_exportable_third

/--
info: 'Elements.Superposition.Metric.holds_place' does not depend on any axioms
-/
#guard_msgs in
#print axioms Elements.Superposition.Metric.holds_place

/--
info: 'Elements.Superposition.Derives.map' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.Derives.map

/--
info: 'Elements.Superposition.Cited.holds_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_iff

/--
info: 'Elements.Superposition.Metric.holds_const' does not depend on any axioms
-/
#guard_msgs in
#print axioms Elements.Superposition.Metric.holds_const

/--
info: 'Elements.Superposition.valuation_encodes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.valuation_encodes

/--
info: 'Elements.Superposition.eliminator_iff_exists' does not depend on any axioms
-/
#guard_msgs in
#print axioms Elements.Superposition.eliminator_iff_exists

/--
info: 'Elements.Superposition.eliminator_false_gives_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.eliminator_false_gives_exists

/--
info: 'Elements.Superposition.Rule.apply' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.Rule.apply

/--
info: 'Elements.Superposition.onLine_of_angle_eq_named' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_symm,
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
 Elements.Tacit.same_side_trans]
-/
#guard_msgs in
#print axioms Elements.Superposition.onLine_of_angle_eq_named

/--
info: 'Elements.Superposition.Cited.holds_lenSymm' depends on axioms: [Classical.choice, Elements.Tacit.len_symm]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_lenSymm

/--
info: 'Elements.Superposition.Cited.holds_angleSymm' depends on axioms: [propext, Classical.choice, Elements.Tacit.angle_symm]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_angleSymm

/--
info: 'Elements.Superposition.Cited.holds_areaCongruent' depends on axioms: [propext,
 Classical.choice,
 Elements.Tacit.area_congruent]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_areaCongruent

/--
info: 'Elements.Superposition.Cited.holds_neOfLen' depends on axioms: [propext,
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
#print axioms Elements.Superposition.Cited.holds_neOfLen

/--
info: 'Elements.Superposition.Cited.holds_rayUnique' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_of_inside_chord,
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
#print axioms Elements.Superposition.Cited.holds_rayUnique

/--
info: 'Elements.Superposition.Cited.holds_rayOfAngle' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_symm,
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
 Elements.Tacit.same_side_trans]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_rayOfAngle

/--
info: 'Elements.Superposition.Cited.holds_rayOfAngleSide' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.between_of_inside_chord,
 Elements.Tacit.between_symm,
 Elements.Tacit.circle_eq,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
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
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_trans]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_rayOfAngleSide

/--
info: 'Elements.Superposition.Cited.holds_of_drawsNothing' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_congruent,
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
 Elements.Tacit.same_side_trans]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_of_drawsNothing

/--
info: 'Elements.BookI.Prop4.cites_drawNothing' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Elements.BookI.Prop4.cites_drawNothing

/--
info: 'Elements.BookI.Prop8.holds_prop7' depends on axioms: [propext,
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
#print axioms Elements.BookI.Prop8.holds_prop7
