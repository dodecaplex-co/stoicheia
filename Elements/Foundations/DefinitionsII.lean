import Elements.Foundations.Phrases

/-!
# The Definitions of Book II

> 1. Any rectangular parallelogram is said to be contained by the two straight lines
>    containing the right angle.
> 2. And in any parallelogrammic area let any one whatever of the parallelograms about
>    its diameter with the two complements be called a gnomon.

Book II reckons with rectangles and squares as magnitudes. "The rectangle contained
by AB, BC together with the rectangle contained by BA, AC is equal to the square on
AB" (II.2) speaks of two rectangles and a square that need not be drawn at all, and
compares them as areas. Here they are:

* `Rectangle A B C D`, the rectangular parallelogram `ABCD` (Definition 1);
* `rect A B C D`, the rectangle contained by `AB`, `CD`: the area of any rectangle
  whose two sides about a right angle are equal to `AB` and `CD`;
* `sq A B`, the square on `AB`: the rectangle contained by `AB`, `AB`.

Euclid never asks whether two rectangles contained by equal straight lines are
equal; he takes it for granted every time he says "BH is the rectangle A, BC, for it
is contained by GB, BC, and BG is equal to A" (II.1). So `rect` is defined by
choosing one of those areas, and the proof that they are all one area, so that the
choice makes no difference, is given once (`Rectangle.contained`, in
`Elements/BookII/Rectangles.lean`), from I.4 and I.34.

A rectangle with a side that is nothing is nothing, as the "triangle" with a
repeated corner is (System E, Metric 6).

Definition 2 needs no Lean word of its own. A gnomon is three parallelograms taken
together, so its area is written as their sum, as in "the gnomon NOP" of II.5; that
the gnomon and the remaining parallelogram make up the whole is
`Parallelogram.about_diameter`.

None of these is an assumption; they are only definitions.
-/

namespace Elements

/-- **Definition II.1.** A rectangular parallelogram: the parallelogram `ABCD`, its
corners taken in order, with all four of its angles right. Euclid says "rectangular",
as Definition 22 says "right-angled" of the square. -/
def Rectangle (A B C D : Point) : Prop :=
  Parallelogram A B C D ∧ ∠ D A B = ∟ ∧ ∠ A B C = ∟ ∧ ∠ B C D = ∟ ∧ ∠ C D A = ∟

/-- The lengths `a` and `b` contain the area `x`: some rectangle `PQRS` has `PQ` equal
to `a`, `PS` equal to `b`, and is equal to `x`; or one of `a`, `b` is nothing, and so
is `x`. -/
def Contain (a b : Length) (x : Area) : Prop :=
  ((a = 0 ∨ b = 0) ∧ x = 0) ∨
    ∃ P Q R S : Point, Rectangle P Q R S ∧ ‖P Q‖ = a ∧ ‖P S‖ = b ∧ quadArea P Q R S = x

/-- **The rectangle contained by `AB`, `CD`** (Definition II.1): the area of any
rectangle whose sides about a right angle are equal to `AB` and `CD`. Lean chooses one
such area (`Classical.epsilon`); `Rectangle.contained` shows that every such
rectangle is equal to it. -/
noncomputable def rect (A B C D : Point) : Area :=
  Classical.epsilon (Contain ‖A B‖ ‖C D‖)

/-- **The square on `AB`**: the rectangle contained by `AB`, `AB`, the area of any
square described on a straight line equal to `AB` (`Square.eq_sq`). -/
noncomputable def sq (A B : Point) : Area := rect A B A B

end Elements
