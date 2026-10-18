import Elements.Figure.Basics
import Elements.BookI.Prop07
import Staging.Stage3.Definitions

/-!
# Stage 3, staged: arcs on one base

Statements before proofs (brief 0006, stage 3). A shared step that cites I.7 and nothing of
Book III, destined for `Elements/BookIII/Squares.lean`, the file of Book III's shared steps
that cite Books I and II.
-/

namespace Elements.BookIII

open Tacit

/-- **Arcs on one base, of one kind, in equal circles, are one arc.** Two drawn arcs with the
same ends, on the same side of their base, in equal circles and of the same kind, lie in one
circle, and have the same points and the same segment.

To be proved: the centres are equally far from the two ends (the radii are equal), and lie
alike, both on the arcs' side, both on the base, or both beyond it; so they are one point,
by I.7 off the base and by the order of points on it; and a circle is fixed by its centre and
radius (`circle_eq`).

A shared step, not a companion: its hypotheses (equal circles, the same kind) are not
III.23's (similar segments). Ground for the arcs (brief 0005, stage 3), for `Arcs.lean`
and their later uses. -/
theorem Arc.eq_of_aligned {a b : Arc} (ha : a.Drawn) (hb : b.Drawn) (hB : a.B = b.B)
    (hC : a.C = b.C) (hK : SameSideOf a.K b.K a.B a.C)
    (hcircles : EqualCircles a.circle b.circle) (hkind : Arc.SameKind a b) :
    a.circle = b.circle ∧ (∀ P : Point, OnArc P a ↔ OnArc P b) ∧
      (∀ P : Point, InSegment P a ↔ InSegment P b) := by
  sorry

end Elements.BookIII
