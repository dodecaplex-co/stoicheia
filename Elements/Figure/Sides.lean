import Elements.Figure.Triangles

/-!
# Book Zero: the sides of a straight line

"On the same side of AB", "on the other side of the straight line AB": Euclid
uses these phrases freely and reads from his figure which side a point is on.

Lean has two ways of saying them. `SameSide P Q L` speaks of a straight line `L`
that has been drawn and named; `SameSideOf P Q A B` (from
`Foundations/Phrases.lean`) speaks, as Euclid does, of "the straight line AB".
Since two points fix one straight line (System E, Generalities 1), these say the
same thing, and the lemmas here pass between them. They also record what
Euclid never doubts: that "the same side of AB" is "the same side of BA", that
if `P` is on `Q`'s side then `Q` is on `P`'s, that a point on either side of
`AB` is off it, that a straight line through a point of `AB` crosses to the other
side (so that the alternate angles of I.27 and I.29 lie on opposite sides of the
straight line falling on the two), and that a straight line has only two sides.
-/

namespace Elements

open Tacit

variable {A B P Q R : Point} {L : Line}

/-! ## The same side -/

/-- Two points on the same side of a straight line `L` through `A` and `B` are on
the same side of the straight line `AB`, however that line is named: two points
fix one straight line. -/
theorem SameSideOf.of_line (hAB : A ≠ B) (hA : OnLine A L) (hB : OnLine B L)
    (h : SameSide P Q L) : SameSideOf P Q A B := by
  refine ⟨hAB, fun M hAM hBM => ?_⟩
  rw [← line_unique hAB hA hB hAM hBM]
  exact h

/-- Two points on the same side of the straight line `AB` are on the same side of
any straight line drawn through `A` and `B`. -/
theorem SameSideOf.sameSide (h : SameSideOf P Q A B) (hA : OnLine A L) (hB : OnLine B L) :
    SameSide P Q L :=
  h.2 L hA hB

/-- "On the same side of `AB`" is the same as "on the same side of `BA`". -/
theorem SameSideOf.swap (h : SameSideOf P Q A B) : SameSideOf P Q B A :=
  ⟨h.1.symm, fun L hB hA => h.2 L hA hB⟩

/-- If `P` is on the same side of `AB` as `Q`, then `Q` is on the same side as `P`. -/
theorem SameSideOf.symm (h : SameSideOf P Q A B) : SameSideOf Q P A B :=
  ⟨h.1, fun L hA hB => same_side_symm (h.2 L hA hB)⟩

/-- Points on the same side as a third are on the same side as each other. -/
theorem SameSideOf.trans (h₁ : SameSideOf P Q A B) (h₂ : SameSideOf Q R A B) :
    SameSideOf P R A B :=
  ⟨h₁.1, fun L hA hB => same_side_trans (same_side_symm (h₁.2 L hA hB)) (h₂.2 L hA hB)⟩

/-- A point on one side of the straight line `AB` is not on it, so `ABP` is a
triangle. -/
theorem SameSideOf.triangle (h : SameSideOf P Q A B) : Triangle A B P := by
  rintro ⟨L, hA, hB, hP⟩
  exact not_on_line_of_same_side (h.2 L hA hB) hP

/-! ## Opposite sides -/

/-- Two points on opposite sides of a straight line `L` through `A` and `B` are on
opposite sides of the straight line `AB`, however that line is named. -/
theorem OppositeSidesOf.of_line (hAB : A ≠ B) (hA : OnLine A L) (hB : OnLine B L)
    (h : OppositeSides P Q L) : OppositeSidesOf P Q A B := by
  refine ⟨hAB, fun M hAM hBM => ?_⟩
  rw [← line_unique hAB hA hB hAM hBM]
  exact h

/-- Two points on opposite sides of the straight line `AB` are on opposite sides of
any straight line drawn through `A` and `B`. -/
theorem OppositeSidesOf.oppositeSides (h : OppositeSidesOf P Q A B) (hA : OnLine A L)
    (hB : OnLine B L) : OppositeSides P Q L :=
  h.2 L hA hB

/-- "On opposite sides of `AB`" is the same as "on opposite sides of `BA`". -/
theorem OppositeSidesOf.swap (h : OppositeSidesOf P Q A B) : OppositeSidesOf P Q B A :=
  ⟨h.1.symm, fun L hB hA => h.2 L hA hB⟩

/-- If `P` is on the other side of `AB` from `Q`, then `Q` is on the other side
from `P`. -/
theorem OppositeSidesOf.symm (h : OppositeSidesOf P Q A B) : OppositeSidesOf Q P A B :=
  ⟨h.1, fun L hA hB =>
    ⟨(h.2 L hA hB).2.1, (h.2 L hA hB).1, fun hs => (h.2 L hA hB).2.2 (same_side_symm hs)⟩⟩

/-- A point on either side of the straight line `AB` is not on it, so `ABP` is a
triangle. -/
theorem OppositeSidesOf.triangle (h : OppositeSidesOf P Q A B) : Triangle A B P := by
  rintro ⟨L, hA, hB, hP⟩
  exact (h.2 L hA hB).1 hP

/-- A straight line through a point of `AB`, from a point `C` off it, crosses to
the other side: if `B` lies between `C` and `E`, then `E` is on the other side
of the straight line `AB` from `C`. (System E, Pasch 3) -/
theorem OppositeSidesOf.of_between {C E : Point} (hABC : Triangle A B C)
    (h : Between C B E) : OppositeSidesOf C E A B := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B hABC.ne₁₂
  have hC : ¬ OnLine C L := hABC.off_line hA hB
  /- `E` is off `AB` too: a straight line through `E` and `B` goes on through `C`. -/
  have hE : ¬ OnLine E L := fun hE => hC (on_line_of_between (between_symm h) hE hB)
  exact OppositeSidesOf.of_line hABC.ne₁₂ hA hB ⟨hC, hE, pasch3 h hB⟩

/-! ## Only two sides -/

/-- A straight line has only two sides: two points, each on the other side of the
straight line `L` from `C`, are on the same side of `L` as each other. (System E,
Same side 5) -/
theorem same_side_of_opposite_sides {C D E : Point} (h₁ : OppositeSides C D L)
    (h₂ : OppositeSides C E L) : SameSide D E L :=
  (same_side_or h₁.1 h₁.2.1 h₂.2.1 h₁.2.2).resolve_left h₂.2.2

/-- A finite straight line joining two points on opposite sides of a straight line
`L` crosses `L`, at a point between them (System E, Intersection 1 and Pasch 4). -/
theorem OppositeSides.exists_between (h : OppositeSides P Q L) :
    ∃ X : Point, OnLine X L ∧ Between P X Q := by
  have hPQ : P ≠ Q := fun e => h.2.2 (e ▸ same_side_refl h.1)
  obtain ⟨M, hP, hQ⟩ := Postulate1 P Q hPQ
  obtain ⟨hLM, X, hXL, hXM⟩ := lines_meet_of_opposite_sides h hP hQ
  exact ⟨X, hXL, pasch4 hLM hXL hXM hP hQ hPQ (fun e => h.1 (e ▸ hXL))
    (fun e => h.2.1 (e ▸ hXL)) h.2.2⟩

/-- The same, said of "the straight line AB": two points, each on the other side of
`AB` from `C`, are on the same side of `AB` as each other. -/
theorem OppositeSidesOf.sameSideOf {C D E : Point} (h₁ : OppositeSidesOf C D A B)
    (h₂ : OppositeSidesOf C E A B) : SameSideOf D E A B :=
  ⟨h₁.1, fun L hA hB => same_side_of_opposite_sides (h₁.2 L hA hB) (h₂.2 L hA hB)⟩

/-- A point on `Q`'s side of the straight line `AB`, where `Q` is on the other side
from `R`, is itself on the other side from `R`. -/
theorem SameSideOf.trans_opposite (h₁ : SameSideOf P Q A B) (h₂ : OppositeSidesOf Q R A B) :
    OppositeSidesOf P R A B := by
  refine ⟨h₁.1, fun L hA hB => ?_⟩
  have hs : SameSide P Q L := h₁.2 L hA hB
  have ho : OppositeSides Q R L := h₂.2 L hA hB
  exact ⟨not_on_line_of_same_side hs, ho.2.1, fun h => ho.2.2 (same_side_trans hs h)⟩

/-! ## A straight line crossing at a point of `GH` -/

/-- The straight line `EF` is the straight line `GH`, when `G` and `H` lie between `E`
and `F` in that order, as where `EF` falls on two straight lines at `G` and `H`
(I.27–I.29): two points on the same side of `EF` are on the same side of `GH`. -/
theorem SameSideOf.inner {E F G H : Point} (h : SameSideOf P Q E F) (hEGH : Between E G H)
    (hGHF : Between G H F) : SameSideOf P Q G H := by
  have hEGF : Between E G F := between_of_between_right hEGH hGHF
  obtain ⟨L, hE, hF⟩ := Postulate1 E F h.1
  have hG : OnLine G L := on_line_of_between_ends hEGF hE hF
  have hH : OnLine H L := on_line_of_between hEGH hE hG
  exact SameSideOf.of_line (ne_of_between hGHF) hG hH (h.sameSide hE hF)

/-- Alternate sides. If `B` and `D` lie on the same side of the straight line `GH`,
and `A` lies on `BG` produced beyond `G`, then `A` and `D` lie on opposite sides
of `GH`. This is where the alternate angles `AGH`, `GHD` of I.27 and I.29 lie. (For a
straight line crossing at `H`, turn `GH` round with `.swap`.) -/
theorem SameSideOf.oppositeSidesOf_of_between {D G H : Point} (hBD : SameSideOf B D G H)
    (hAGB : Between A G B) : OppositeSidesOf A D G H := by
  /- `BA` crosses `GH` at `G`, so `A` is on the other side from `B`. -/
  have hBA : OppositeSidesOf B A G H :=
    (OppositeSidesOf.of_between hBD.triangle.bac (between_symm hAGB)).swap
  exact (hBD.symm.trans_opposite hBA).symm

/-- The other way round: if `A` and `D` lie on opposite sides of the straight line
`GH`, and `B` lies on `AG` produced beyond `G`, then `B` and `D` lie on the same
side of `GH`. -/
theorem OppositeSidesOf.sameSideOf_of_between {D G H : Point} (hAD : OppositeSidesOf A D G H)
    (hAGB : Between A G B) : SameSideOf B D G H := by
  have hA : Triangle G H A := hAD.triangle
  have hAB : OppositeSidesOf A B G H := (OppositeSidesOf.of_between hA.bac hAGB).swap
  exact OppositeSidesOf.sameSideOf hAB hAD

/-- "Let a point be taken at random on the other side of the straight line AB"
(I.12): if `P` is off the straight line `AB`, there is a point on the other side
of it from `P`, which may be chosen different from any points already in the
figure. (System E, Points 6) -/
theorem exists_oppositeSidesOf (hP : Triangle A B P) (avoid : List Point) :
    ∃ Q : Point, OppositeSidesOf Q P A B ∧ Q ∉ avoid := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B hP.ne₁₂
  obtain ⟨Q, hQ, hQa⟩ := exists_point_opposite_side (hP.off_line hA hB) avoid
  exact ⟨Q, OppositeSidesOf.of_line hP.ne₁₂ hA hB hQ, hQa⟩

end Elements
