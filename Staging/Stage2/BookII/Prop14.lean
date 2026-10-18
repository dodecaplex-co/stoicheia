import Staging.Stage2.BookI.Prop45

/-!
# Staging: II.14 for any rectilineal figure, with a drawn square

Brief 0006, stage 2. Companions of `Elements.BookII.Prop14`, which stays as Euclid's worked
configuration, I.45's figure of two triangles, and returns the side of the square. His
proof makes a rectangle equal to the figure [I. 45] and then a square equal to the
rectangle.

* `Prop14.rectangle` is that second part.
* `Prop14.sum` is the proof for any number of triangles, by I.45's `Prop45.sum`: the
  construction, which claims nothing of a figure.
* `Prop14.apart` is the proposition for any rectilineal figure, with any boundaries, given
  with any division into triangles that lie apart (`Apart`), as in I.45's `Prop45.apart`;
  the figure may have a hole. `Prop14.square` is the same with the square drawn.
* `Prop14.figure` is the proposition for a figure with one boundary, given with triangles
  fitted together in a suitable order (`Rectilineal`), as in I.45's `Prop45.figure`; it
  follows from `Prop14.apart`, since fitted triangles lie apart (`Fitted.inside_pairwise`).
* `Prop14.fan`, the main companion, is the proposition for a figure divided as Euclid and
  Oliver Byrne divide it, from one corner, with the division checked as in `Prop45.fan`. As
  there, it concludes that the triangles are fitted together into one figure (`Fitted.fan`),
  and the square is equal to that figure (`Prop14.figure`).

As in I.45, the square is equal to the triangles the figure is given with, taken together,
and nothing is claimed of another division. Today's II.14 is an area-sum theorem: it
follows from `Prop14.sum` (the check at the end), and its two triangles are not checked.
Its checked case is `Prop14.fan` for the corners D, A, B, C.

`Prop14.rectangle` is proved directly, by Euclid's second part, and never cites II.14:
otherwise the companions would rest on the two-triangle statement rather than on Euclid's
square construction, and the check that today's II.14 follows from `Prop14.sum` would prove
II.14 from II.14 (brief 0006). They move into `Elements/BookII/Prop14.lean` when proved, as
"II.14 rectangle", "II.14 sum", "II.14 apart", "II.14 figure", "II.14 square" and
"II.14 fan".
-/

namespace Elements.BookII

open Tacit

/-- **II.14, for a rectangle** (companion of II.14). To construct a square equal to a given
rectangle EBCD: the second part of Euclid's proof, with both of its cases. If BE is equal to
ED, the rectangle is a square already. If not, the greater, say BE, is produced to F with EF
equal to ED, BF is bisected at G, the semicircle BHF is described with centre G, and DE is
produced to H; then the rectangle BE, EF with the square on EG is the square on GF [II. 5],
which is the squares on HE, EG [I. 47], and the rectangle is the square on EH. This is
today's proof of II.14 after the rectangle is made. It does not cite II.14. The square is the
square on PQ. -/
theorem Prop14.rectangle {E B C D : Point} (h : Rectangle E B C D) :
    ∃ P Q : Point, sq P Q = quadArea E B C D := by
  /- If BE equals ED, the rectangle is already the square on EB. -/
  by_cases heq : ‖B E‖ = ‖E D‖
  · exact ⟨E, B, (h.eq_rect rfl ((len_symm E B).trans heq).symm).symm⟩
  /- Otherwise one side is greater. -/
  have hlt : ‖E D‖ < ‖E B‖ ∨ ‖E B‖ < ‖E D‖ := by
    rcases lt_trichotomy ‖E D‖ ‖E B‖ with h' | h' | h'
    · exact Or.inl h'
    · exact False.elim (heq ((len_symm B E).trans h'.symm))
    · exact Or.inr h'
  /- Euclid's figure has BE greater. The same construction serves when ED is
     greater, by reading the rectangle the other way round. -/
  have greater : ∀ {E B C D : Point}, Rectangle E B C D → ‖E D‖ < ‖E B‖ →
      ∃ P Q : Point, sq P Q = quadArea E B C D := by
    intro E B C D h hlt
    /- Produce BE beyond E, and take EF equal to ED on that ray. -/
    have hEB : E ≠ B := h.1.1.1
    have hDE : D ≠ E := h.1.2.2.1
    obtain ⟨X, hBEX⟩ := produce hEB.symm
    obtain ⟨F, hF, hEF⟩ :=
      OnRay.exists_len_eq hDE.symm (ne_of_between (between_symm hBEX)).symm
    have hBEF : Between B E F := hF.between hBEX
    /- Bisect BF at G [I. 10]. -/
    obtain ⟨G, hBGF, hBG⟩ := BookI.Prop10 (ne_of_between_ends hBEF)
    /- The circle with centre G through B also passes through F (Postulate 3).
       E is inside it, between the ends of its diameter BF. -/
    obtain ⟨BHF, hG_BHF, hB_BHF⟩ := Postulate3 G B (ne_of_between hBGF).symm
    have hF_BHF : OnCircle F BHF :=
      on_circle_of_len_eq hG_BHF hB_BHF (by rw [← hBG, len_symm G B])
    have hE_BHF : InsideCircle E BHF :=
      inside_of_between (Or.inr hB_BHF) (Or.inr hF_BHF) hBEF
    /- Produce DE to H beyond E, on the semicircle BHF away from the rectangle. -/
    obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hDE
    obtain ⟨H, hH_BHF, hH_DE, hHED⟩ := line_circle_beyond hE_BHF hE_DE hD_DE hDE
    /- G lies between B and E: the half BG of BF is less than BE, since BE is
       greater than the remaining part EF. Thus E is the unequal cut of BF that
       II.5 needs, distinct from the midpoint G. -/
    have hlt' : ‖E F‖ < ‖B E‖ := by rw [hEF, len_symm B E]; exact hlt
    have hBGE : Between B G E := by
      have hBF : ‖B F‖ = ‖B G‖ + ‖B G‖ := by
        rw [← len_add_of_between hBGF, ← hBG]
      have hBF' : ‖B F‖ = ‖B E‖ + ‖E F‖ := (len_add_of_between hBEF).symm
      refine OnRay.between_of_len_lt (OnRay.of_between hBGF) (OnRay.of_between hBEF) ?_
      rcases lt_trichotomy ‖B G‖ ‖B E‖ with h' | h' | h'
      · exact h'
      · exfalso
        rw [h', hBF'] at hBF
        have : ‖E F‖ = ‖B E‖ := CommonNotion3 (by rw [add_comm]; exact hBF) rfl
        exact lt_irrefl _ (this ▸ hlt')
      · exfalso
        have := Magnitude.add_self_lt_add_self h'
        rw [← hBF, hBF'] at this
        exact lt_irrefl _ (lt_trans hlt' (Magnitude.lt_of_add_lt_add_left this))
    have hEG : E ≠ G := ne_of_between (between_symm hBGE)
    /- BF is cut equally at G and unequally at E: the rectangle BE, EF with the
       square on GE equals the square on GF [II. 5]. -/
    have h5 : rect B E E F + sq G E = sq G F := Prop5 hBGF hBG hBEF hEG
    /- GF and GH are radii of the same circle (Definition 15), so the same sum
       equals the square on GH. -/
    have hGF_GH : ‖G F‖ = ‖G H‖ := Definition15 hG_BHF hF_BHF hH_BHF
    have hsum : rect B E E F + sq G E = sq G H := h5.trans (sq_congr hGF_GH)
    /- H is off BF: otherwise the straight line through H and E would be BF, and
       D on it, contrary to the rectangle's triangle DEB. So HEG is a triangle,
       with GH as its third side. -/
    obtain ⟨BF, hB_BF, hF_BF⟩ := Postulate1 B F (ne_of_between_ends hBEF)
    have hE_BF : OnLine E BF := on_line_of_between_ends hBEF hB_BF hF_BF
    have hG_BF : OnLine G BF := on_line_of_between_ends hBGF hB_BF hF_BF
    have hDEB : Triangle D E B := h.1.rotate.rotate.rotate.triangle
    have hD_BF : ¬ OnLine D BF := hDEB.bca.off_line hE_BF hB_BF
    have hHE : H ≠ E := ne_of_between hHED
    have hH_BF : ¬ OnLine H BF := fun hH =>
      hD_BF ((line_unique hHE hH_DE hE_DE hH hE_BF) ▸ hD_DE)
    /- HEG is right: HEB is adjacent to the rectangle's right angle DEB,
       and G lies on the ray EB. -/
    have hBEH : ∠ B E H = ∟ := by
      rw [← adjacent_eq_of_right hD_DE hH_DE (between_symm hHED)
        (hDEB.off_line hD_DE hE_DE) h.2.1]
      exact h.2.1
    have hHEG : ∠ H E G = ∟ := by
      rw [angle_symm hHE (Ne.symm hEG),
        angle_onRay_left (OnRay.of_between (between_symm hBGE)) hHE]
      exact hBEH
    /- The squares on HE and EG equal the square on GH [I. 47]. Thus they
       equal the rectangle BE, EF together with the square on GE. -/
    have h47 := BookI.Prop47.sq (Triangle.of_line hE_BF hG_BF hEG hH_BF).acb hHEG
    have hequal : rect B E E F + sq G E = sq H E + sq E G :=
      hsum.trans ((sq_symm G H).trans h47)
    /- Subtract the square on GE from each: the rectangle BE, EF is the square
       on HE, hence on EH (Common Notion 3). -/
    have hrem : rect B E E F = sq H E := CommonNotion3 hequal (sq_symm G E)
    have hEH : rect B E E F = sq E H := hrem.trans (sq_symm H E)
    /- EF equals ED, so the rectangle BE, EF is the given rectangle EBCD. -/
    have hrectangle : quadArea E B C D = rect B E E F :=
      h.eq_rect (len_symm E B) hEF.symm
    exact ⟨E, H, (hrectangle.trans hEH).symm⟩
  rcases hlt with hlt | hlt
  · exact greater h hlt
  · obtain ⟨P, Q, hPQ⟩ := greater h.reverse hlt
    exact ⟨P, Q, hPQ.trans (quadArea_reverse E B C D)⟩

/-- **II.14, any number of triangles** (companion of II.14). To construct a square equal to
any number of given triangles taken together, at least one: a rectangle equal to them
[I. 45, `Prop45.sum`, in a right angle from I.11 at a corner A of the first triangle ABC, on
AB], then a square equal to the rectangle (`Prop14.rectangle`). The triangles are any
triangles; they need not fit together into one figure, and the statement claims nothing of
a figure. The square is the square on PQ. -/
theorem Prop14.sum (ts : List (Point × Point × Point)) (hne : ts ≠ [])
    (hts : ∀ t ∈ ts, Triangle t.1 t.2.1 t.2.2) :
    ∃ P Q : Point, sq P Q = Magnitude.sum (ts.map fun t => △ t.1 t.2.1 t.2.2) := by
  match ts, hne, hts with
  | (A, B, C) :: rest, _, hts =>
    have hABC : Triangle A B C := hts (A, B, C) (List.mem_cons_self ..)
    obtain ⟨L, hA, hB⟩ := Postulate1 A B hABC.ne₁₂
    obtain ⟨X, hX, hright⟩ := BookI.Prop11 hABC.ne₁₂ ⟨L, hA, hB, hA⟩ hABC
    have hX' : ∠ B A X = ∟ := hright B ⟨L, hA, hB, hB⟩ hABC.ne₁₂.symm
    obtain ⟨E, F, G, H, hp, hang, harea⟩ :=
      BookI.Prop45.sum _ (List.cons_ne_nil _ _) hts hX.triangle.bac
    have hrect : Rectangle E F G H := by
      refine Rectangle.of_right hp ?_
      rw [angle_symm hp.2.2.1 hp.1.1.symm, hang, hX']
    obtain ⟨P, Q, hPQ⟩ := Prop14.rectangle hrect
    exact ⟨P, Q, hPQ.trans harea⟩

/-- **II.14, for any rectilineal figure, with any boundaries** (companion of II.14). To
construct a square equal to a given rectilineal figure, given with any division of it into
triangles, no point inside two of them (`Apart`), as in `Prop45.apart`: the square on PQ is
equal to those triangles taken together (`Apart.area`). The figure may have a hole, touch
itself at a corner, or be in more than one piece. It is `Prop14.sum` for the figure's
triangles. Nothing is claimed of another division of the figure. -/
theorem Prop14.apart (R : Apart) : ∃ P Q : Point, sq P Q = R.area :=
  Prop14.sum R.pieces R.ne R.triangle

/-- **II.14, for any rectilineal figure with one boundary** (companion of II.14). To
construct a square equal to a given rectilineal figure, given with triangles fitted together
in a suitable order, each glued across a side of an earlier one and meeting the earlier ones
only along it (`Rectilineal`), as in `Prop45.figure`: the square on PQ is equal to those
triangles taken together (`Rectilineal.area`). It is `Prop14.apart` for the figure's
triangles, which lie apart (`Fitted.inside_pairwise`, `Rectilineal.toApart`). Nothing is
claimed of another division of the figure. -/
theorem Prop14.figure (R : Rectilineal) : ∃ P Q : Point, sq P Q = R.area :=
  Prop14.apart R.toApart

/-- The figure's area is something: its first triangle has positive area, and adding
the rest cannot make it nothing. This makes the side found by `Prop14.apart` a straight
line, not a point, so I.46 can describe the square on it. -/
theorem Prop14.area_pos (R : Apart) : 0 < R.area := by
  unfold Apart.area
  match R.pieces, R.ne, R.triangle with
  | (A, B, C) :: rest, _, htri =>
    /- The sum is the first triangle together with the sum of the rest. -/
    have hfirst : 0 < △ A B C := (htri (A, B, C) (List.mem_cons_self ..)).area_pos
    change 0 < △ A B C + Magnitude.sum (rest.map fun t => △ t.1 t.2.1 t.2.2)
    /- Adding the first triangle makes the rest greater (Common Notion 5).
       If the whole were nothing, the rest would be less than nothing. -/
    have hwhole := CommonNotion5
      (a := Magnitude.sum (rest.map fun t => △ t.1 t.2.1 t.2.2)) hfirst
    rw [add_comm] at hwhole
    apply Magnitude.pos_of_ne_zero
    intro hzero
    rw [hzero] at hwhole
    exact not_lt_zero _ hwhole

/-- **II.14, with the square drawn** (companion of II.14). To construct a square PQST equal
to a given rectilineal figure, given with triangles that lie apart as in `Prop14.apart`: the
square on the side that `Prop14.apart` finds, described on it [I. 46]. The square is a
parallelogram, and it is equal to the figure's triangles taken together. A figure `R` given
by gluing (`Rectilineal`) is taken here as `R.toApart`, the same triangles, which lie apart,
with the same sum (`Rectilineal.area_toApart`); so is the glued figure that `Prop14.fan`
returns for a checked fan. -/
theorem Prop14.square (R : Apart) :
    ∃ P Q S T : Point, Square P Q S T ∧ Parallelogram P Q S T ∧ quadArea P Q S T = R.area := by
  /- Take the side whose square equals the given figure. Its ends differ because
     the figure has positive area, while the square on a point is nothing. -/
  obtain ⟨P, Q, hPQ⟩ := Prop14.apart R
  have hne : P ≠ Q := by
    intro heq
    subst Q
    rw [sq_self] at hPQ
    have hpos := Prop14.area_pos R
    rw [← hPQ] at hpos
    exact lt_irrefl 0 hpos
  /- Choose a point off PQ and describe the square on PQ [I. 46]. Its corners
     occur in the order P, S, T, Q. -/
  obtain ⟨X, hX, -⟩ := exists_off_line hne []
  obtain ⟨S, T, hsq, hS, hT⟩ := BookI.Prop46 hne hX
  /- The described square is a parallelogram with area sq P Q. -/
  obtain ⟨hp, harea⟩ := Square.described hsq hS hT
  exact ⟨P, S, T, Q, hsq, hp, harea.trans hPQ⟩

/-- **II.14, for a figure divided from one corner** (companion of II.14), as Euclid and
Oliver Byrne divide it. A figure with corners A₀, A₁, A₂, …, Aₙ, divided by the straight
lines from A₀ into the triangles A₀A₁A₂, …, A₀Aₙ₋₁Aₙ, with the division checked as in
`Prop45.fan`: each piece a triangle, each two neighbouring triangles on opposite sides of
the straight line A₀Aᵢ they share, and the angles at A₀ together less than four right
angles. Then those triangles, in that order, are fitted together into one figure
(`Fitted.fan`), and the square on PQ is equal to that figure, that is, to the triangles
taken together. The figure is read as the one with corners A₀, A₁, …, Aₙ in order round it
(that its boundary is that closed line is not stated in Lean). The square drawn is
`Prop14.square R.toApart`, for the glued figure `R` returned.

As in `Prop45.fan`, the first conclusion is what the two conditions are for; the square
alone would follow from each piece being a triangle, by `Prop14.sum`. -/
theorem Prop14.fan {A₀ A₁ A₂ : Point} {ps : List Point}
    (htri : ∀ s ∈ segments (A₁ :: A₂ :: ps), Triangle A₀ s.1 s.2)
    (hopp : ∀ t ∈ triples (A₁ :: A₂ :: ps), OppositeSidesOf t.1 t.2.2 A₀ t.2.1)
    (hA₀ : Magnitude.sum ((segments (A₁ :: A₂ :: ps)).map fun s => ∠ s.1 A₀ s.2) <
      ∟ + ∟ + (∟ + ∟)) :
    ∃ R : Rectilineal,
      R.pieces = (segments (A₁ :: A₂ :: ps)).map (fun s => (A₀, s.1, s.2)) ∧
      ∃ P Q : Point, sq P Q = R.area :=
  ⟨⟨_, Fitted.fan htri hopp hA₀⟩, rfl, Prop14.figure _⟩

/-- The check: today's statement of II.14, for I.45's two triangles A₁A₂A₄ and A₄A₂A₃ (ABD
and DBC), follows from `Prop14.sum` for the list of those two (checked by Lean, up to
unfolding definitions). -/
example : type_of% @Elements.BookII.Prop14 := by
  intro A₁ A₂ A₃ A₄ h₁ h₂
  have hts : ∀ t ∈ [(A₁, A₂, A₄), (A₄, A₂, A₃)], Triangle t.1 t.2.1 t.2.2 := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact h₁
    · exact h₂
  obtain ⟨P, Q, hPQ⟩ := Prop14.sum _ (List.cons_ne_nil _ _) hts
  refine ⟨P, Q, ?_⟩
  rw [hPQ]
  simp only [List.map, Magnitude.sum, add_zero]

end Elements.BookII
