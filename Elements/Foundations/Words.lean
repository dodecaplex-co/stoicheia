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
-/

namespace Elements

/-- **Point.** "A point is that which has no part." (Def. 1) -/
opaque Point : Type

/-- **Straight line.** (Defs. 2–4) A `Line` is a whole straight line, extending
without end. Euclid's "finite straight line AB" is the pair of points `A`, `B`,
lying on such a line. -/
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

/-- Two circles that cut one another (in two points). -/
def CirclesMeet (α β : Circle) : Prop :=
  ∃ A B : Point, A ≠ B ∧ OnCircle A α ∧ OnCircle A β ∧ OnCircle B α ∧ OnCircle B β

end Elements
