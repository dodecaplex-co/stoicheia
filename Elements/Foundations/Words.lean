/-!
# The words Euclid leaves undefined

Euclid opens Book I with twenty-three definitions, but the first few
("a point is that which has no part", "a line is breadthless length") are
descriptions rather than definitions in the modern sense. Nothing later in the
book ever *uses* them. What Euclid actually uses are the postulates, the common
notions, and a great deal that he reads off his figures.

So in Lean we take these words as given and say nothing about them here. Each one
is `opaque`: Lean knows only what the postulates, the definitions that carry
content, and the tacit rules in `Foundations/Tacit/` say about it. That's also
why `#print axioms` on a proposition lists exactly what the proof rests on.

The vocabulary follows the System E of Jeremy Avigad, Edward Dean and John
Mumma ("A formal system for Euclid's *Elements*", Review of Symbolic Logic,
2009), which was designed to match the way Euclid reasons from a diagram.

## The plane they describe

No proof uses numbers, but the axioms are read in a model, the ordinary plane: numerical
and exact finite tests support it (`tests/model/`), and Lean checks, in `model/` (#73),
that the plane satisfies every locked law, relative to Lean's logic and Mathlib's real
numbers. Read the words in the ordinary plane, and every postulate, Definition 15 and
every tacit rule holds, degenerate cases included:

* a `Point` is a point of the plane, a `Line` a whole straight line, and a `Circle`
  a circle of positive radius, with its `Centre`; `OnCircle` is lying on it and
  `InsideCircle` lying nearer the centre than the radius;
* `Between A B C` is strict betweenness, and `SameSide A B L` says that `A` and `B`
  lie in one open half-plane of `L`;
* the magnitudes are real numbers of at least 0, added and compared as usual
  (`Magnitudes.lean`): the length `‖A B‖` is the distance from `A` to `B`; the angle
  `∠ A B C` is the angle between the rays from `B`, in [0, π], and 0 when a point is
  repeated; the area `△ A B C` is the area of the triangle; and `∟` is π/2.

The plane stays a model of everything Lean knows only while the words stay `opaque`,
so that Lean knows nothing of them but what the axioms say; `scripts/check_fidelity.py`
checks that they do. The model is checked axiom by axiom, with the reason each holds
and the programs that test it, in [tests/model/MODEL.md](../../tests/model/MODEL.md).
-/

namespace Elements

/-- **Point.** "A point is that which has no part." (Def. 1) -/
opaque Point : Type

/-- **Straight line.** (Def. I.4) A `Line` is a whole straight line, extending
without end. Euclid's "finite straight line AB" is the pair of points `A`, `B`,
lying on such a line. Definitions I.2 and I.3, of a line in general and of its
ends, have no Lean word: the curved lines of Books I to III are the circumferences
of circles, given by `Circle` and `OnCircle`, and their arcs, `Arc` (Def. III.6). -/
opaque Line : Type

/-- **Circle.** (Def. 15) -/
opaque Circle : Type

/-- `OnLine A L`: the point `A` lies on the straight line `L`. -/
opaque OnLine : Point → Line → Prop

/-- `SameSide A B L`: the points `A` and `B` lie on the same side of the
straight line `L`. (Neither of them is on `L`.) -/
opaque SameSide : Point → Point → Line → Prop

/-- `Between A B C`: the point `B` lies on the straight line through `A` and `C`,
strictly between them. -/
opaque Between : Point → Point → Point → Prop

/-- `OnCircle A α`: the point `A` lies on the circumference of the circle `α`. -/
opaque OnCircle : Point → Circle → Prop

/-- `InsideCircle A α`: the point `A` lies inside the circle `α`. -/
opaque InsideCircle : Point → Circle → Prop

/-- `Centre A α`: the point `A` is the centre of the circle `α`. (Def. 16) -/
opaque Centre : Point → Circle → Prop

/-! ## Words built from those -/

/-- `A` and `B` lie on opposite sides of the straight line `L`. -/
def OppositeSides (A B : Point) (L : Line) : Prop :=
  ¬ OnLine A L ∧ ¬ OnLine B L ∧ ¬ SameSide A B L

/-- `A` lies outside the circle `α`: neither inside it nor on it. -/
def OutsideCircle (A : Point) (α : Circle) : Prop :=
  ¬ InsideCircle A α ∧ ¬ OnCircle A α

/-- `A`, `B`, `C` lie on one straight line. -/
def Collinear (A B C : Point) : Prop :=
  ∃ L : Line, OnLine A L ∧ OnLine B L ∧ OnLine C L

/-- Two different straight lines that cross. -/
def LinesMeet (L M : Line) : Prop :=
  L ≠ M ∧ ∃ A : Point, OnLine A L ∧ OnLine A M

/-- A straight line that cuts a circle (in two points). -/
def LineMeetsCircle (L : Line) (α : Circle) : Prop :=
  ∃ A B : Point, A ≠ B ∧ OnLine A L ∧ OnCircle A α ∧ OnLine B L ∧ OnCircle B α

/-- Two circles that meet at two points. Circles that cut one another are `CirclesCut`,
defined under Definition III.3. -/
def CirclesMeet (α β : Circle) : Prop :=
  ∃ A B : Point, A ≠ B ∧ OnCircle A α ∧ OnCircle A β ∧ OnCircle B α ∧ OnCircle B β

end Elements
