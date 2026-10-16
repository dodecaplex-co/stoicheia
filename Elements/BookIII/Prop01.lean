import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop08

/-!
# Book III, Proposition 1

Euclid's text, in Heath's translation: [`heath/III/01.md`](../../heath/III/01.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- To find the centre of a given circle. -/
theorem Prop1 {A B : Point} {ABC : Circle} (hABC : ∃ G : Point, Centre G ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hAB : A ≠ B) :
    ∃ F C D E : Point, Centre F ABC ∧ Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧
      OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ Between C F E ∧ ‖C F‖ = ‖F E‖ := by
  -- Let ABC be the given circle;
  -- thus it is required to find the centre of the circle ABC.
  -- Let a straight line AB be drawn through it at random, and let it be bisected at the point
  -- D;
  -- from D let DC be drawn at right angles to AB and let it be drawn through to E;
  -- let CE be bisected at F;
  -- I say that F is the centre of the circle ABC.
  -- For suppose it is not, but, if possible, let G be the centre,
  -- and let GA, GD, GB be joined.
  -- Then, since AD is equal to DB,
  -- and DG is common,
  -- the two sides AD, DG are equal to the two sides BD, DG respectively;
  -- and the base GA is equal to the base GB, for they are radii;
  -- therefore the angle ADG is equal to the angle GDB. [I. 8]
  -- But, when a straight line set up on a straight line makes the adjacent angles equal to one
  -- another, each of the equal angles is right; [I. Def. 10]
  -- therefore the angle GDB is right.
  -- But the angle FDB is also right;
  -- therefore the angle FDB is equal to the angle GDB, the greater to the less: which is
  -- impossible.
  -- Therefore G is not the centre of the circle ABC.
  -- Similarly we can prove that neither is any other point except F.
  -- Therefore the point F is the centre of the circle ABC.
  -- PORISM. From this it is manifest that, if in a circle a straight line cut a straight line
  -- into two equal parts and at right angles, the centre of the circle is on the cutting
  -- straight line.
  -- Q. E. F.
  sorry

/-- The Porism to III.1: "if in a circle a straight line cut a straight line into two
equal parts and at right angles, the centre of the circle is on the cutting straight
line." The straight line `DC` cuts `AB`, a straight line in the circle, at its
middle point `D` and at right angles; the centre `G` is on `DC`. III.9 and III.10
cite it. -/
theorem Prop1.porism {A B C D G : Point} {ABC : Circle} (hG : Centre G ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hADB : Between A D B) (hAD : ‖A D‖ = ‖D B‖)
    (hC : ¬ Collinear A B C) (hADC : ∠ A D C = ∟) :
    Collinear D C G := by
  sorry

end Elements.BookIII
