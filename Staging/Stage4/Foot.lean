import Elements

/-!
# Staging: the foot of the perpendicular from the centre

Brief 0006, stage 4. Definitions III.4 and III.5 measure how far a straight line in a circle
is from the centre by the perpendicular drawn to it from the centre. Today's III.14 and
III.15 are given that perpendicular as a right angle at its foot, so a straight line through
the centre, which has no such right angle, is left out: a diameter. `Foot` gives every
straight line a foot, the centre itself when the straight line passes through it, so that a
diameter is at no distance from the centre.

`Foot` is a new word, and goes to the foundations (`DefinitionsIII.lean`) when adopted, with
the lock and a decisions entry (WORKFLOW, section 2). `Foot.exists` and `Foot.unique`
connect it with the perpendicular Euclid draws [I. 12, I. 17]; they cite propositions, and
so go to `Elements/BookIII/Squares.lean`, with Book III's other shared steps that cite
Book I.
-/

namespace Elements

/-- **The foot of the perpendicular** drawn from `E` to the straight line `AB`. `F` is on
the straight line `AB`; if `E` is not on it, every other point `P` of the straight line makes
the angle `EFP` right; and if `E` is on it, the foot is `E` itself. If `A` and `B` are one
point, every point is on a straight line with them, so the foot is `E`. `EF` is then the
distance of `AB` from `E` (Definitions III.4 and III.5, extended: it is nothing when `AB`
passes through `E`, a case Euclid's definitions do not take). -/
def Foot (E A B F : Point) : Prop :=
  Collinear A B F ∧ (Collinear A B E → F = E) ∧
    (¬ Collinear A B E → ∀ P : Point, Collinear A B P → P ≠ F → ∠ E F P = ∟)

/-- Every straight line has a foot of the perpendicular from any point: the perpendicular
drawn to it [I. 12], or the point itself when it is on the straight line (and when `A` and
`B` are one point). -/
theorem Foot.exists (E A B : Point) : ∃ F : Point, Foot E A B F := by
  sorry

/-- The foot of the perpendicular is one point: two perpendiculars from `E` to one straight
line would make a triangle with two right angles, and two angles of a triangle are less
than two right angles [I. 17]. -/
theorem Foot.unique {E A B F F' : Point} (hF : Foot E A B F) (hF' : Foot E A B F') :
    F = F' := by
  sorry

end Elements
