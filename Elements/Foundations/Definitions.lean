import Elements.Foundations.CommonNotions

/-!
# The Definitions of Book I

Most of Euclid's twenty-three definitions name things (a point, a line, a
surface, an angle, a figure). The ones that do real work in the proofs are
written out here. Definitions 1–9, 13, 14, 16 and 17–18 live as docstrings on
the words in `Words.lean` or are not needed until later books.

Definition 15 is special: it is a definition that carries content ("all the
straight lines falling upon it from one point ... are equal"), so it is an
`axiom`, and it shows up in `#print axioms` wherever a proof uses it.
-/

namespace Elements

/-- **Definition 10.** "When a straight line set up on a straight line makes the
adjacent angles equal to one another, each of the equal angles is right."

The angle `ABC` is right when, continuing `AB` beyond `B` to some `D`, the
straight line `BC` makes the adjacent angles `ABC` and `CBD` equal. -/
def IsRightAngle (A B C : Point) : Prop :=
  ∃ D : Point, Between A B D ∧ ¬ Collinear A B C ∧ ∠ A B C = ∠ C B D

/-- **Definition 11.** "An obtuse angle is an angle greater than a right angle." -/
def IsObtuse (A B C : Point) : Prop := ∟ < ∠ A B C

/-- **Definition 12.** "An acute angle is an angle less than a right angle." -/
def IsAcute (A B C : Point) : Prop := ∠ A B C < ∟

/-- **Definition 15.** "A circle is a plane figure contained by one line such
that all the straight lines falling upon it from one point among those lying
within the figure are equal to one another."

So any two radii of a circle are equal. -/
axiom Definition15 {A B C : Point} {α : Circle} (hA : Centre A α) (hB : OnCircle B α)
    (hC : OnCircle C α) : ‖A B‖ = ‖A C‖

/-- **Definition 19.** A trilateral figure: three points not on one straight
line, joined by three straight lines. -/
def Triangle (A B C : Point) : Prop := ¬ Collinear A B C

/-- **Definition 20.** "Of trilateral figures, an equilateral triangle is that
which has its three sides equal." -/
def Equilateral (A B C : Point) : Prop :=
  Triangle A B C ∧ ‖A B‖ = ‖B C‖ ∧ ‖B C‖ = ‖C A‖

/-- **Definition 20.** "... an isosceles triangle that which has two of its sides
alone equal." (Here the two equal sides meet at `A`.) Euclid's "alone" is not
kept: an equilateral triangle counts as isosceles here too. No proof in Book I
yet uses this definition by name; I.5 and I.6 speak of the two equal sides
directly. -/
def Isosceles (A B C : Point) : Prop :=
  Triangle A B C ∧ ‖A B‖ = ‖A C‖

/-- **Definition 21.** "... a right-angled triangle that which has a right
angle." (Here the right angle is at `A`.) -/
def RightAngledTriangle (A B C : Point) : Prop :=
  Triangle A B C ∧ ∠ B A C = ∟

/-- **Definition 22.** "Of quadrilateral figures, a square is that which is both
equilateral and right-angled." The corners are `A`, `B`, `C`, `D`, in order. -/
def Square (A B C D : Point) : Prop :=
  ‖A B‖ = ‖B C‖ ∧ ‖B C‖ = ‖C D‖ ∧ ‖C D‖ = ‖D A‖ ∧
    ∠ D A B = ∟ ∧ ∠ A B C = ∟ ∧ ∠ B C D = ∟ ∧ ∠ C D A = ∟

/-- **Definition 23.** "Parallel straight lines are straight lines which, being in
the same plane and being produced indefinitely in both directions, do not meet
one another in either direction." -/
def Parallel (L M : Line) : Prop :=
  L ≠ M ∧ ¬ ∃ P : Point, OnLine P L ∧ OnLine P M

end Elements
