import Elements

/-!
# Staging: sums of magnitudes, and points in order

Brief 0006, stage 2: the words that let a statement say "any number". II.1 cuts a straight
line "into any number of segments whatever", and I.45 and II.14 take "a given rectilineal
figure", made of any number of triangles. Lean says "any number" with a list, so it needs
the sum of a list of magnitudes, and a way to say that a list of points lies in order along
one straight line.

These are statements awaiting approval (WORKFLOW, section 2): the definitions are complete,
and each theorem's proof is `sorry` until it is assigned. Where they go when adopted:

* `Magnitude.sum`, `InOrder`, `segments` and `endOf` are new words that companion
  statements use, so each is a definition in the foundations, with the lock and a decisions
  entry (WORKFLOW, section 2), not in Book Zero as brief 0005 first placed them;
* `Magnitude.sum_singleton`, `Magnitude.sum_append` and `InOrder.between_end` are facts
  every figure may need, proved from the foundations alone, for Book Zero,
  `Elements/Figure/Sums.lean`;
* `Prop20.collinear_iff` cites I.20, so it lives after I.20 in the dependency order: not in
  `Elements/BookI/Helpers.lean`, which I.20 itself imports, but in a file of shared steps
  after it.
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
  sorry

/-- The sum of two lists, one after the other, is the sum of the first added to the sum of
the second. -/
theorem Magnitude.sum_append {k : Kind} (l₁ l₂ : List (Magnitude k)) :
    Magnitude.sum (l₁ ++ l₂) = Magnitude.sum l₁ + Magnitude.sum l₂ := by
  sorry

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
the next, as the ends of one segment. The segments of `[B, D, E, C]` are BD, DE and EC. -/
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
  sorry

/-! ## When three points lie on one straight line -/

namespace BookI

/-- **Three points lie on one straight line exactly when one distance among them is the sum
of the other two**: when X is on CD (CX, XD together equal to CD), or D is on CX, or C is on
DX. One way is order on a straight line (System E, Between 6 and Diagram-segment 1); the
other is I.20, for if C, D, X made a triangle, any two of its sides would be greater than
the third. Later proofs share it: the diameters of III.14 and III.15, and placement in
stage 3. No hypothesis is needed: when C and D are one point, every X is on a straight line
with them, and CD, DX together equal CX. [I. 20] -/
theorem Prop20.collinear_iff {C D X : Point} :
    Collinear C D X ↔
      ‖C X‖ + ‖X D‖ = ‖C D‖ ∨ ‖C D‖ + ‖D X‖ = ‖C X‖ ∨ ‖D C‖ + ‖C X‖ = ‖D X‖ := by
  sorry

end BookI

end Elements
