import Elements

/-!
# III.1: the construction's type and axioms

The type fixture fixes what `Elements.BookIII.Prop1.construction` receives and returns:
a circle and two distinct points on it, and Euclid's bisections and perpendicular
straight line. The pin records the full axiom list Lean reports for that declaration.
Renaming the declaration, changing its type or changing its axioms fails `lake build Audit`.
This is step 4 of brief 0008, guarding the construction before the centre restatements.

At each renewal, read the whole list and check that `Tacit.inside_of_between`,
`Tacit.outside_of_between`, `Tacit.centre_unique` and `sorryAx` are absent.
`Tacit.exists_centre` is admitted, as the owner decided. The pin cannot show that its
centre is used only inside the proof that D is within the circle. A reader checks that
confinement in `Prop1.construction`, as well as how the construction follows Euclid.
-/

set_option warningAsError true

section
open Elements Elements.Tacit

/-- The construction receives a circle and two distinct points on it, with no centre
supplied, and returns the bisections and perpendicular straight line of III.1. -/
example : ∀ {A B : Point} {ABC : Circle}, OnCircle A ABC → OnCircle B ABC → A ≠ B →
    ∃ F C D E : Point, Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧
      OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ ∠ B D C = ∟ ∧ ¬ Collinear A B C ∧
      Between C F E ∧ ‖C F‖ = ‖F E‖ :=
  @Elements.BookIII.Prop1.construction

end

/--
info: 'Elements.BookIII.Prop1.construction' depends on axioms: [propext,
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
 Elements.Tacit.circles_meet,
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
#print axioms Elements.BookIII.Prop1.construction
