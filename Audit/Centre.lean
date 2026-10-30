import Elements

/-!
# III.1: the construction's type and axioms

The type fixture fixes what `Elements.BookIII.Prop1.construction` receives and returns:
a circle and two distinct points on it, and Euclid's bisections and perpendicular
straight line. The pin records the full axiom list Lean reports for that declaration.
Renaming the declaration, changing its type or changing its axioms fails `lake build Audit`.
This is step 4 of brief 0008, guarding the construction before the centre restatements.

At each renewal, read the whole list and check that `sorryAx` is absent. Circle 2
(`Tacit.inside_of_between`) and Circle 3 (`Tacit.outside_of_between`) are theorems, both
proved after III.2 in `Elements/BookIII/Prop02.lean` from its corollary `Prop2.within`, so
no axiom list can show them; the certificate's walk
from III.1 passes through the steps this construction also calls (`Prop1.midpoint_inside`,
`Prop1.perpendicular_chord`, I.10) and through the Tacit theorems, so a use of
either would make III.1 cite III.2, a later proposition, which the certificate refuses.
`Tacit.centre_unique` is a theorem since axiom wave one, and no axiom list shows a call
to it either.
`Tacit.exists_centre` is admitted by the owner's decision of 18 October 2026 on issue
#59, "approved, as Astra recommends". The pin cannot show that the construction uses its
centre only inside the proof that D is within the circle, nor that `centre_unique` is not
called. A reader checks both in `Prop1.construction` and the lemmas it calls; checks in
`Prop1`, whose reductio takes its supposed centre G from the rule too, that no centre the
rule gives is a point the theorem returns, and that `centre_unique` is not called there
either; and checks how the construction follows Euclid. A pin on the proved rules each
entry uses is #168's.
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
#print axioms Elements.BookIII.Prop1.construction
