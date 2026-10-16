import Elements.Foundations.Tacit.Superposition
import Elements.Figure.Lengths
import Elements.Figure.Lines
import Elements.Figure.Circles
import Elements.Figure.Triangles
import Elements.Figure.Rays
import Elements.Figure.Sides
import Elements.Figure.Angles
import Elements.Figure.Parallels
import Elements.Figure.Areas
import Elements.Figure.Parallelograms
import Elements.Figure.Rectangles

/-!
# Book Zero: small facts every figure needs

Euclid never proves these, and nobody reading him would want him to. They are
proved here once, from the postulates and the tacit rules, so that the proofs
of the propositions can cite them by name and stay close to Euclid's words.
Every proposition file imports this one, and through it:

* `Lengths`: something added makes a thing greater; the part is less than the
  whole; take the same thing from two unequal magnitudes, and the less remains
  the less.
* `Lines`: order on a straight line; producing a finite straight line, and
  producing it far enough to cut a given length from it.
* `Circles`: points on, inside and outside a circle; a point taken "at random"
  can be taken near enough.
* `Triangles`: a triangle's corners, named in any order, and the straight lines
  through them.
* `Rays`: points on the half of a straight line that starts at a point; a point
  cuts a straight line into two rays; a point of a ray lies beyond its start from
  any point behind it; on a ray, one point at a given distance from its start,
  and only one.
* `Sides`: "on the same side of AB" and "on the other side of AB"; a straight
  line has only two sides; a straight line crossing `GH` at `G` carries a point to
  the other side.
* `Angles`: an angle depends only on its rays; an angle of a triangle is
  something; adding angles, and the part less than the whole; a straight line
  within an angle crosses its base; a ray stays on one side of a straight line;
  one ray for one angle.
* `Parallels`: "AB is parallel to CD", said of any two points of each straight
  line, either way round; parallels do not meet, and straight lines that do not
  meet are parallel; a straight line falling on two parallels meets each in one
  point; one parallel lies wholly on one side of the other; a straight line
  joining two parallels in the same directions; and the figure of I.29 about any
  straight line falling on two parallels.
* `Areas`: a triangle named from any corner; a triangle is something, and a
  straight line from a corner cuts it into two which make up the whole; on a ray
  from a corner, one point only makes a triangle of a given area on a given base;
  the halves of equal things are equal; a four-sided figure whose diameters cross
  has the same area whichever diameter cuts it.
* `Parallelograms`: a parallelogram or a square named from another corner; a
  point between two parallels; parallels keep order; a four-sided figure between
  two parallels has crossing diameters or crossing sides; the diameters of a
  parallelogram cross; a parallelogram cut by a parallel is the two parallelograms
  it is cut into.
* `Rectangles`: the rectangle contained by two straight lines, and the square on
  one, follow their lengths, and read either way round are the same; a rectangle
  with a side that is nothing is nothing; a rectangle or a square named from
  another corner.

Nothing in Book Zero cites a proposition of the *Elements*, and nothing in it is
an axiom.
-/
