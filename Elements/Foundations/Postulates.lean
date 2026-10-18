import Elements.Foundations.Definitions

/-!
# The Postulates

> Let the following be postulated:
> 1. To draw a straight line from any point to any point.
> 2. To produce a finite straight line continuously in a straight line.
> 3. To describe a circle with any centre and distance.
> 4. That all right angles are equal to one another.
> 5. That, if a straight line falling on two straight lines make the interior
>    angles on the same side less than two right angles, the two straight lines,
>    if produced indefinitely, meet on that side on which are the angles less
>    than the two right angles.

Each one is an `axiom`. The certificate reports exactly which proofs use which
postulates; most famously, no proof before I.29 uses Postulate 5.
-/

namespace Elements

/-- **Postulate 1.** To draw a straight line from any point to any point. -/
axiom Postulate1 (A B : Point) (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L

/-- **Postulate 2.** To produce a finite straight line continuously in a straight
line.

The finite straight line `BC`, lying on `L`, is produced beyond `C` to a new
point `A`. Because it can be produced as far as we please, we may also ask that
`A` avoid any finitely many points already in the figure (the list `avoid`):
System E §3.3, Points rule 4. -/
axiom Postulate2 {B C : Point} {L : Line} (hB : OnLine B L) (hC : OnLine C L) (hBC : B ≠ C)
    (avoid : List Point) : ∃ A : Point, OnLine A L ∧ Between B C A ∧ A ∉ avoid

/-- **Postulate 3.** To describe a circle with any centre and distance.

Like Euclid's own compass, this one "collapses": the circle has centre `A` and
passes through `B`. Carrying a distance from one place to another is
Proposition 2's job. -/
axiom Postulate3 (A B : Point) (h : A ≠ B) : ∃ α : Circle, Centre A α ∧ OnCircle B α

/-- **Postulate 4.** That all right angles are equal to one another: every right
angle (in the sense of Definition 10) is equal to `∟`. -/
axiom Postulate4 {A B C : Point} (h : IsRightAngle A B C) : ∠ A B C = ∟

/-- **Postulate 5.** If the straight line through `B` and `C` falls on the
straight lines `L` (through `A` and `B`) and `N` (through `C` and `D`), with `A`
and `D` on the same side of it, and the interior angles `ABC` and `BCD` together
are less than two right angles, then `L` and `N`, produced, meet on that side.

System E §3.6, diagram-angle transfer rule 5. -/
axiom Postulate5 {A B C D : Point} {L M N : Line}
    (hA : OnLine A L) (hBL : OnLine B L) (hBM : OnLine B M) (hCM : OnLine C M)
    (hCN : OnLine C N) (hD : OnLine D N) (hBC : B ≠ C) (hAD : SameSide A D M)
    (hsum : ∠ A B C + ∠ B C D < ∟ + ∟) :
    ∃ E : Point, OnLine E L ∧ OnLine E N ∧ SameSide E A M

end Elements
