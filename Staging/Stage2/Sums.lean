import Elements

/-!
# Staging: sums of magnitudes, and points in order

Brief 0006, stage 2: the words that let a statement say "any number". II.1 cuts a straight
line "into any number of segments whatever", and I.45 and II.14 take "a given rectilineal
figure", of any number of sides, given with any number of triangles. Lean says "any number"
with a list, so it needs the sum of a list of magnitudes, the segments between successive
points of a list, and a way to say that a list of points lies in order along one straight
line. The segments are II.1's pieces of the straight line, and, in the companions of I.45
and II.14 for a checked fan (`Prop45.fan`, `Prop14.fan`), the sides on which the triangles
from one corner stand; the other companions of I.45 and II.14 take the figure as a list of
triangles (`Staging/Stage2/Rectilineal.lean`).

These are statements of brief 0006, approved and frozen (WORKFLOW, section 2), and each
is proved here from the rules of order and of magnitudes alone. Where they go when they
move:

* `Magnitude.sum`, `InOrder`, `segments` and `endOf` are new words that companion
  statements use, so each is a definition in the foundations, with the lock and a decisions
  entry (WORKFLOW, section 2), not in Book Zero as brief 0005 first placed them;
* `Magnitude.sum_singleton`, `Magnitude.sum_append` and `InOrder.between_end` are facts
  every figure may need, proved from the foundations alone, for Book Zero,
  `Elements/Figure/Sums.lean`;
* the fact that three points are on one straight line exactly when one distance among them
  is the sum of the other two, which III.14, III.15 and placement share, has one statement,
  `Prop20.collinear_iff` in `Staging/Stage3/Degenerate.lean`, bound for
  `Elements/BookI/HelpersTriangles.lean`.
-/

namespace Elements

open Tacit

/-! ## Sums of magnitudes -/

/-- **The sum of a list of magnitudes** of one kind: nothing for the empty list, and
otherwise the first added to the sum of the rest. So `Magnitude.sum [a, b, c]` is
`a + (b + (c + 0))`, which is `a + b + c`. -/
noncomputable def Magnitude.sum {k : Kind} : List (Magnitude k) → Magnitude k
  | [] => 0
  | a :: as => a + Magnitude.sum as

/-- The sum of one magnitude is that magnitude. -/
theorem Magnitude.sum_singleton {k : Kind} (a : Magnitude k) : Magnitude.sum [a] = a := by
  change a + 0 = a
  exact add_zero a

/-- The sum of two lists, one after the other, is the sum of the first added to the sum of
the second. -/
theorem Magnitude.sum_append {k : Kind} (l₁ l₂ : List (Magnitude k)) :
    Magnitude.sum (l₁ ++ l₂) = Magnitude.sum l₁ + Magnitude.sum l₂ := by
  induction l₁ with
  | nil =>
      /- Nothing added to a magnitude: the laws give `a + 0 = a`, so turn the sum round. -/
      change Magnitude.sum l₂ = 0 + Magnitude.sum l₂
      rw [add_comm 0, add_zero]
  | cons a as ih =>
      /- A first magnitude `a`: the induction, then the law for adding three in a row. -/
      change a + Magnitude.sum (as ++ l₂) = (a + Magnitude.sum as) + Magnitude.sum l₂
      rw [ih, add_assoc]

/-! ## Points in order on a straight line -/

/-- **Points in order.** `InOrder ps`: each point of the list `ps` differs from the next,
and of any three in a row the middle one lies between the other two. So the points lie on
one straight line, in the order listed: `InOrder [B, D, E, C]` is II.1's straight line BC
cut at the points D and E. A list of one point, or of none, is in order. -/
def InOrder : List Point → Prop
  | [] => True
  | [_] => True
  | [p, q] => p ≠ q
  | p :: q :: r :: rest => p ≠ q ∧ Between p q r ∧ InOrder (q :: r :: rest)

/-- **The segments** of a straight line cut at points in order: each point of the list with
the next, as the ends of one segment. The segments of `[B, D, E, C]` are BD, DE and EC. The
points need not be in order, or on one straight line: in the companions of I.45 and II.14
for a checked fan (`Prop45.fan`, `Prop14.fan`), the segments of a figure's corners A₁, A₂,
…, Aₙ are its sides A₁A₂, …, Aₙ₋₁Aₙ, those away from the corner A₀, and each side with A₀
makes one of the triangles into which the straight lines from A₀ divide the figure, when the
fan's conditions hold. -/
def segments : List Point → List (Point × Point)
  | p :: q :: rest => (p, q) :: segments (q :: rest)
  | _ => []

/-- **The end** of the straight line that starts at `B` and runs through the points `ps`:
the last of them, or `B` itself if there are none. `endOf B [D, E, C]` is C. -/
def endOf (B : Point) : List Point → Point
  | [] => B
  | p :: ps => endOf p ps

/-- Of three or more points in order, the second lies between the first and the last. -/
theorem InOrder.between_end {B P : Point} {ps : List Point} (h : InOrder (B :: P :: ps))
    (hps : ps ≠ []) : Between B P (endOf P ps) := by
  induction ps generalizing B P with
  | nil =>
      /- No point after P: `hps` rules this case out. -/
      exact absurd rfl hps
  | cons Q qs ih =>
      cases qs with
      | nil =>
          /- Three points B, P, Q: the last is Q, and P is between B and Q. -/
          exact h.2.1
      | cons R rest =>
          /- P is between B and Q; by the induction, Q is between P and the last point E;
          so, by Between 5, P is between B and E. -/
          have hQE : Between P Q (endOf Q (R :: rest)) := ih h.2.2 (List.cons_ne_nil R rest)
          exact between_of_between_right h.2.1 hQE

end Elements
