import Elements.Foundations.Tacit.Superposition
import Elements.Figure.Lengths
import Elements.Figure.Lines
import Elements.Figure.Circles
import Elements.Figure.Triangles
import Elements.Figure.Rays
import Elements.Figure.Sides
import Elements.Figure.Angles

/-!
# Book Zero: small facts every figure needs

Euclid never proves these, and nobody reading him would want him to. They are
proved here once, from the postulates and the tacit rules, so that the proofs
of the propositions can cite them by name and stay close to Euclid's words.
Every proposition file imports this one, and through it:

* `Lengths`: something added makes a thing greater; the part is less than the whole.
* `Lines`: order on a straight line; producing a finite straight line.
* `Circles`: points on, inside and outside a circle.
* `Triangles`: a triangle's corners, named in any order, and the straight lines
  through them.
* `Rays`: points on the half of a straight line that starts at a point, and the
  one point of a ray at a given distance from its start.
* `Sides`: "on the same side of AB" and "on the other side of AB".
* `Angles`: an angle depends only on its rays; adding angles; a straight line
  within an angle crosses its base; one ray for one angle.

Nothing in Book Zero cites a proposition of the *Elements*, and nothing in it is
an axiom.
-/
