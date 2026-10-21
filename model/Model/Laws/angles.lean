module

public import Model.Signature

/-!
# The angle laws, translated by hand

**This file is hand-translated.** It holds the ten laws about angles that the model proves
in the plane. The generator described in the [README](../../README.md) writes every
locked law from the library's elaborated declarations. `Check/Angles.lean` compares the
locked laws and the two hand-translated words with their generated counterparts.
`inside_of_angle_add` and `adjacent_eq_of_right` are now theorems in the library, so their
translations are compared directly with those declarations, including binder kinds.
Their concrete plane proofs remain as derived facts, with no generated assumption field.

The ten are the angle rules of the library:

* the two metric laws about angles, `angle_symm` and `angle_le_two_right`
  (`Elements/Foundations/Tacit/Metric.lean`);
* the diagram-angle transfer rules 1 to 4 of System E: an angle
  is nothing exactly when its arms lie on one ray (`angle_eq_zero_of_same_ray`,
  `same_ray_of_angle_eq_zero`); angle addition, in both directions (`angle_add_of_inside`,
  `inside_of_angle_add`); a right angle equals its neighbour (`adjacent_eq_of_right`); and
  an angle does not change when its arms are traced through other points of the same rays
  (`angle_eq_of_same_rays`);
* Postulate 4, with Definition 10's `IsRightAngle` and the `Collinear` it reaches, and
  Definition 15.

Each declaration is the library's, word for word, with `S.Point` for `Elements.Point`,
`S.ang` for `Elements.ang`, and so on; its printed statement is quoted above each.
Two words the laws reach, `Collinear` and `IsRightAngle`, are translated here too, in the
namespace `Model.Hand`, so that they do not meet the generated `Signature.Collinear` and
`Signature.IsRightAngle` when both are imported. Where angles are added or compared, the
statement names the type at which `+`, `≤` and `0` are taken, `S.Angle`, as in
`HAdd.hAdd (α := S.Angle) (β := S.Angle)` and `(0 : S.Angle)`: the signature's field writes
the type of `S.ang A B C` out as the carrier, and Lean finds the instances for `S.Angle`
only when it is told that type. This names what the library's statement already says, and
`Check/Angles.lean` asks the kernel, law by law and word by word, whether the library's own
words put in for `S` give back the library's declaration.
-/

@[expose] public section

namespace Model.Hand

variable (S : Signature)

/-! ## The words the laws reach -/

/-- `Elements.Collinear`, by hand. The lock prints it as `fun (A B C : Elements.Point) =>
Exists fun (L : Elements.Line) => And (Elements.OnLine A L) (And (Elements.OnLine B L)
(Elements.OnLine C L))`. -/
def Collinear (A B C : S.Point) : Prop :=
  ∃ L : S.Line, S.OnLine A L ∧ S.OnLine B L ∧ S.OnLine C L

/-- `Elements.IsRightAngle` (Definition 10), by hand. The lock prints it as
`fun (A B C : Elements.Point) => Exists fun (D : Elements.Point) => And (Elements.Between A B D)
(And (Not (Elements.Collinear A B C)) (Eq (Elements.ang A B C) (Elements.ang C B D)))`. -/
def IsRightAngle (A B C : S.Point) : Prop :=
  ∃ D : S.Point, S.Between A B D ∧ ¬ Collinear S A B C ∧ S.ang A B C = S.ang C B D

/-! ## Definition 15 and Postulate 4 -/

/-- `Elements.Definition15`, by hand. The lock prints it as `∀ {A B C : Elements.Point}
{α : Elements.Circle}, Elements.Centre A α → Elements.OnCircle B α → Elements.OnCircle C α →
Eq (Elements.len A B) (Elements.len A C)`. -/
def Definition15_angles : Prop :=
  ∀ {A B C : S.Point} {α : S.Circle}, S.Centre A α → S.OnCircle B α → S.OnCircle C α →
    S.len A B = S.len A C

/-- `Elements.Postulate4`, by hand. The lock prints it as `∀ {A B C : Elements.Point},
Elements.IsRightAngle A B C → Eq (Elements.ang A B C) Elements.rightAngle`. -/
def Postulate4 : Prop :=
  ∀ {A B C : S.Point}, IsRightAngle S A B C → S.ang A B C = S.rightAngle

/-! ## The metric laws about angles -/

/-- `Elements.Tacit.angle_symm` (Metric 4), by hand. The lock prints it as
`∀ {A B C : Elements.Point}, Ne A B → Ne C B → Eq (Elements.ang A B C) (Elements.ang C B A)`. -/
def angle_symm : Prop :=
  ∀ {A B C : S.Point}, A ≠ B → C ≠ B → S.ang A B C = S.ang C B A

/-- `Elements.Tacit.angle_le_two_right` (Metric 5), by hand. The lock prints it as
`∀ (A B C : Elements.Point), LE.le (Elements.ang A B C) (HAdd.hAdd Elements.rightAngle
Elements.rightAngle)`. -/
def angle_le_two_right : Prop :=
  ∀ (A B C : S.Point), LE.le (α := S.Angle) (S.ang A B C)
    (HAdd.hAdd (α := S.Angle) (β := S.Angle) S.rightAngle S.rightAngle)

/-! ## The diagram-angle transfer rules -/

/-- `Elements.Tacit.angle_eq_zero_of_same_ray` (Diagram-angle 1), by hand. The lock prints it
as `∀ {A B C : Elements.Point} {L : Elements.Line}, Ne A B → Ne A C → Elements.OnLine A L →
Elements.OnLine B L → Elements.OnLine C L → Not (Elements.Between B A C) →
Eq (Elements.ang B A C) 0`. -/
def angle_eq_zero_of_same_ray : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, A ≠ B → A ≠ C → S.OnLine A L → S.OnLine B L →
    S.OnLine C L → ¬ S.Between B A C → S.ang B A C = (0 : S.Angle)

/-- `Elements.Tacit.same_ray_of_angle_eq_zero` (Diagram-angle 1), by hand. The lock prints it
as `∀ {A B C : Elements.Point} {L : Elements.Line}, Ne A B → Ne A C → Elements.OnLine A L →
Elements.OnLine B L → Eq (Elements.ang B A C) 0 → And (Elements.OnLine C L)
(Not (Elements.Between B A C))`. -/
def same_ray_of_angle_eq_zero : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, A ≠ B → A ≠ C → S.OnLine A L → S.OnLine B L →
    S.ang B A C = (0 : S.Angle) → S.OnLine C L ∧ ¬ S.Between B A C

/-- `Elements.Tacit.angle_add_of_inside` (Diagram-angle 2), by hand. The lock prints it as
`∀ {A B C D : Elements.Point} {L M : Elements.Line}, Elements.OnLine A L → Elements.OnLine A M →
Elements.OnLine B L → Elements.OnLine C M → Ne A B → Ne A C → Not (Elements.OnLine D L) →
Not (Elements.OnLine D M) → Ne L M → Elements.SameSide B D M → Elements.SameSide C D L →
Eq (Elements.ang B A C) (HAdd.hAdd (Elements.ang B A D) (Elements.ang D A C))`. -/
def angle_add_of_inside : Prop :=
  ∀ {A B C D : S.Point} {L M : S.Line}, S.OnLine A L → S.OnLine A M → S.OnLine B L →
    S.OnLine C M → A ≠ B → A ≠ C → ¬ S.OnLine D L → ¬ S.OnLine D M → L ≠ M →
    S.SameSide B D M → S.SameSide C D L →
    S.ang B A C = HAdd.hAdd (α := S.Angle) (β := S.Angle) (S.ang B A D) (S.ang D A C)

/-- `Elements.Tacit.inside_of_angle_add` (Diagram-angle 2), by hand.
The theorem's unchanged type is
`∀ {A B C D : Elements.Point} {L M : Elements.Line}, Elements.OnLine A L → Elements.OnLine A M →
Elements.OnLine B L → Elements.OnLine C M → Ne A B → Ne A C → Not (Elements.OnLine D L) →
Not (Elements.OnLine D M) → Ne L M → Eq (Elements.ang B A C) (HAdd.hAdd (Elements.ang B A D)
(Elements.ang D A C)) → And (Elements.SameSide B D M) (Elements.SameSide C D L)`. -/
def inside_of_angle_add : Prop :=
  ∀ {A B C D : S.Point} {L M : S.Line}, S.OnLine A L → S.OnLine A M → S.OnLine B L →
    S.OnLine C M → A ≠ B → A ≠ C → ¬ S.OnLine D L → ¬ S.OnLine D M → L ≠ M →
    S.ang B A C = HAdd.hAdd (α := S.Angle) (β := S.Angle) (S.ang B A D) (S.ang D A C) →
    S.SameSide B D M ∧ S.SameSide C D L

/-- `Elements.Tacit.adjacent_eq_of_right` (Diagram-angle 3), by hand.
The theorem's unchanged type is
`∀ {A B C D : Elements.Point} {L : Elements.Line}, Elements.OnLine A L → Elements.OnLine B L →
Elements.Between A C B → Not (Elements.OnLine D L) → Eq (Elements.ang A C D)
Elements.rightAngle → Eq (Elements.ang A C D) (Elements.ang D C B)`. -/
def adjacent_eq_of_right : Prop :=
  ∀ {A B C D : S.Point} {L : S.Line}, S.OnLine A L → S.OnLine B L → S.Between A C B →
    ¬ S.OnLine D L → S.ang A C D = S.rightAngle → S.ang A C D = S.ang D C B

/-- `Elements.Tacit.angle_eq_of_same_rays` (Diagram-angle 4), by hand. The lock prints it as
`∀ {A B C : Elements.Point} {L M : Elements.Line} {B' C' : Elements.Point}, Elements.OnLine A L →
Elements.OnLine B L → Elements.OnLine B' L → Elements.OnLine A M → Elements.OnLine C M →
Elements.OnLine C' M → Ne B A → Ne B' A → Ne C A → Ne C' A → Not (Elements.Between B A B') →
Not (Elements.Between C A C') → Eq (Elements.ang B A C) (Elements.ang B' A C')`. -/
def angle_eq_of_same_rays : Prop :=
  ∀ {A B C : S.Point} {L M : S.Line} {B' C' : S.Point}, S.OnLine A L → S.OnLine B L →
    S.OnLine B' L → S.OnLine A M → S.OnLine C M → S.OnLine C' M → B ≠ A → B' ≠ A → C ≠ A →
    C' ≠ A → ¬ S.Between B A B' → ¬ S.Between C A C' → S.ang B A C = S.ang B' A C'

end Model.Hand
