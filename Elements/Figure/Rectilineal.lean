import Elements.Figure.Sides

/-!
# Book Zero: a rectilineal figure's triangles

A rectilineal figure is given with the triangles it is cut into, in a word of the
foundations (`Foundations/Phrases.lean`, which says why): as triangles that lie apart
(`Apart`), or, for a figure with one boundary, as triangles fitted together in a suitable
order (`Fitted`, `Rectilineal`). Here are the facts that follow from the gluing rule
itself: a figure has at least one triangle; each piece is a triangle, its corners not on one
straight line; and no point is inside two of the triangles, for each new triangle meets the
earlier ones only along the side it is glued to, and a point inside a triangle is off its
sides. The last pins the meaning of `Fitted`: the triangles do not overlap, so their sum is
the area of the figure they make up.

So a figure glued together is a figure whose triangles lie apart, the same triangles
(`Rectilineal.toApart`), with the same sum (`Rectilineal.area_toApart`): what is proved for
any figure given with triangles that lie apart is proved for a glued one in one step. That
Euclid's and Oliver Byrne's division of a figure from one corner is a fitted figure, under
two conditions, is `Fitted.fan`; its proof cites I.13, so it stands beside I.45, in
`Elements/BookI/Prop45.lean`, before the companion that uses it.

Nothing in Book Zero cites a proposition of the *Elements*.
-/

namespace Elements

/-- A figure has at least one triangle. -/
theorem Fitted.ne_nil {ps : List (Point × Point × Point)} (h : Fitted ps) : ps ≠ [] := by
  cases h with
  | single => exact List.cons_ne_nil _ _
  | glue => exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)

/-- Each piece of a figure is a triangle: its corners are not on one straight line. -/
theorem Fitted.triangle {ps : List (Point × Point × Point)} (h : Fitted ps) :
    ∀ t ∈ ps, Triangle t.1 t.2.1 t.2.2 := by
  induction h with
  | single h =>
    intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    exact h
  | glue _ _ _ hX _ ih =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact ih t ht
    · rw [List.mem_singleton] at ht
      subst ht
      exact hX.triangle

/-- **The triangles of a figure do not overlap**: no point is inside two of them. Each new
triangle meets the earlier ones only along the side it is glued to, and a point inside a
triangle is off its sides. This is what makes the sum of the triangles the area of the figure
they make up (`Rectilineal.area`), and it pins that meaning of `Fitted` against a later
change of the definition. -/
theorem Fitted.inside_pairwise {ps : List (Point × Point × Point)} (h : Fitted ps) :
    ps.Pairwise (fun s s' => ∀ Y : Point,
      InsideTriangle Y s.1 s.2.1 s.2.2 → ¬ InsideTriangle Y s'.1 s'.2.1 s'.2.2) := by
  induction h with
  | single _ => exact List.pairwise_singleton _ _
  | @glue ps t P Q R X hps ht hside hX hmeet ih =>
    rw [List.pairwise_append]
    refine ⟨ih, List.pairwise_singleton _ _, ?_⟩
    intro s hs s' hs' Y hYs hYn
    rw [List.mem_singleton] at hs'
    subst hs'
    have hY := hmeet Y (Or.inl hYn) s hs (Or.inl hYs)
    obtain ⟨L, hP, hQ⟩ := Postulate1 P Q hX.1
    have hoff : ¬ OnLine Y L := Tacit.not_on_line_of_same_side (hYn.2.2.sameSide hP hQ)
    rcases hY with rfl | rfl | hb
    · exact hoff hP
    · exact hoff hQ
    · exact hoff (Tacit.on_line_of_between_ends hb hP hQ)

/-- **A figure glued together, taken with triangles that lie apart**: the same triangles,
which lie apart by `Fitted.inside_pairwise`. A companion that takes `Apart` takes a glued
figure `R` as `R.toApart`: `Prop45.figure` and `Prop14.figure` are `Prop45.apart` and
`Prop14.apart` for it, and `Prop14.square R.toApart` draws its square. -/
def Rectilineal.toApart (R : Rectilineal) : Apart :=
  ⟨R.pieces, R.fitted.ne_nil, R.fitted.triangle, R.fitted.inside_pairwise⟩

/-- **The area is the same sum**: the area of a glued figure taken with triangles that lie
apart is its area as a glued figure. Lean checks it by unfolding, so the two definitions of
the sum, `Apart.area` and `Rectilineal.area`, cannot drift apart. -/
theorem Rectilineal.area_toApart (R : Rectilineal) : R.toApart.area = R.area := rfl

end Elements
