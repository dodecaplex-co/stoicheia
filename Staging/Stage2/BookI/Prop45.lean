import Staging.Stage2.Rectilineal

/-!
# Staging: I.45 for any rectilineal figure

Brief 0006, stage 2. Companions of `Elements.BookI.Prop45`, which stays as Euclid's worked
configuration: the four-sided figure ABCD, cut by DB into the triangles ABD and DBC.
Euclid's proof makes a parallelogram for the first triangle [I. 42], applies one for the
second to its side [I. 44], and shows that the two make one parallelogram; a figure of more
triangles repeats the second step, as Oliver Byrne draws it for three (1847, p. 46).

* `Prop45.append` is that second step.
* `Prop45.sum` repeats it, for any number of triangles. It is the construction, and claims
  nothing of a figure: the triangles need not fit together.
* `Prop45.apart` is the proposition for any rectilineal figure, with any boundaries, given
  with any division into triangles that lie apart, no point inside two of them (`Apart`).
  The figure may have a hole (Definition I.14: "any boundary or boundaries").
* `Prop45.figure` is the proposition for a figure with one boundary, given with triangles
  fitted together in a suitable order (`Rectilineal`, `Fitted`). It follows from
  `Prop45.apart`, since fitted triangles lie apart (`Fitted.inside_pairwise`).
* `Prop45.fan`, the main companion, is the proposition for a figure divided as Euclid and
  Byrne divide it, by the straight lines from one corner A₀, with the two conditions that
  make those triangles a figure: neighbouring triangles on opposite sides of the straight
  line they share, and the angles at A₀ together less than four right angles. It concludes
  that the triangles are fitted together into one figure (`Fitted.fan`), and that the
  parallelogram is equal to that figure (`Prop45.figure`). The two conditions are what the
  first conclusion needs.

The names: `figure` is Euclid's word for what is given ("a given rectilineal figure"), so the
companion for a figure glued together has it; `apart` names the figure whose triangles lie
apart; `fan` names the division Euclid draws, from one corner, which not every figure
admits. A checked fan is a fitted figure, and a fitted figure's triangles lie apart, so the
three agree on the figures they share. They move into `Elements/BookI/Prop45.lean` when
proved, as "I.45 append", "I.45 sum", "I.45 apart", "I.45 figure" and "I.45 fan".

**What "equal to the figure" means here.** The parallelogram is equal to the triangles the
figure is given with, taken together. That sum is what Euclid adds up when he calls ABD and
DBC "the whole rectilineal figure ABCD". Nothing here says that another division of the
figure gives the same sum: Euclid takes that for granted, and David Hilbert proved it, for
his measure of area (brief 0006, for the gap catalogue). Today's I.45 is an area-sum
theorem: it follows from `Prop45.sum` (the check at the end), and its ABD and DBC need only
be triangles, which may overlap. It represents Euclid's pictured division when A and C lie
on opposite sides of DB, and that checked case is `Prop45.fan` for the corners D, A, B, C.
-/

namespace Elements.BookI

open Tacit

/-- **I.45, one more triangle** (companion of I.45). Given a parallelogram KFLM in the
given rectilineal angle E, and a triangle ABC, to construct a parallelogram in the same
angle equal to KFLM and ABC together: the second half of Euclid's proof, which applies a
parallelogram equal to the triangle to a side of the first [I. 44] and shows that the two
make one. -/
theorem Prop45.append {A B C K F L M E₁ E E₂ : Point} (hKFLM : Parallelogram K F L M)
    (hang : ∠ F K M = ∠ E₁ E E₂) (hABC : Triangle A B C) (hE : Triangle E₁ E E₂) :
    ∃ K' F' L' M' : Point, Parallelogram K' F' L' M' ∧ ∠ F' K' M' = ∠ E₁ E E₂ ∧
      quadArea K' F' L' M' = quadArea K F L M + △ A B C := by
  /- Here M is Euclid's H and L is G; the new corners L', M' are his L, M.
     Read the given parallelogram as FKML, and apply the new one to LM across
     that side from K, so that I.14 can join KM to MM'. -/
  have hFKML : Parallelogram F K M L := hKFLM.rotate.reverse
  have hLMK : Triangle L M K := hFKML.1.symm.swap_right.triangle.bac
  obtain ⟨P, hPK, -⟩ := exists_oppositeSidesOf hLMK []
  obtain ⟨L', M', hM'P, hLMM'L', hLMM', hadded⟩ :=
    Prop44 hLMK.ne₁₂ hABC hE hPK.triangle
  have hM'K : OppositeSidesOf M' K L M := hM'P.trans_opposite hPK
  have hKM : K ≠ M := hLMK.ne₂₃.symm
  have hLM : L ≠ M := hLMK.ne₁₂
  have hFK : F ≠ K := hFKML.1.1

  /- The angles FKM and LMM' both equal E. Add KML to each; I.29 makes
     the first pair two right angles, hence the second pair also. -/
  have hFKM_LMM' : ∠ F K M = ∠ L M M' := CommonNotion1 hang hLMM'
  have hsum₁ : ∠ F K M + ∠ K M L = ∠ K M L + ∠ L M M' := by
    rw [hFKM_LMM', add_comm]
  have hFL_KM : SameSideOf F L K M := hFKML.rotate.sameSideOf.symm
  have hFKM_KML : ∠ F K M + ∠ K M L = ∟ + ∟ :=
    Prop29.interior hFKML.1.swap_left hFL_KM
  have hKML_LMM' : ∠ K M L + ∠ L M M' = ∟ + ∟ :=
    hsum₁.symm.trans hFKM_KML

  /- K and M' lie on opposite sides of LM, and the angles KML, LMM' are two
     right angles, so I.14 puts KM in a straight line with MM', with M
     between K and M'. -/
  have hKMM' : Between K M M' := Prop14 hM'K.symm (by
    rw [angle_symm hLM hKM]
    exact hKML_LMM')

  /- ML falls on the parallels KM' and FL, so I.29 equates the alternate
     angles M'ML and MLF. -/
  have hFK_ML : SameSideOf F K M L := hFKML.rotate.rotate.sameSideOf
  have hM'M : M' ≠ M := ne_of_between (between_symm hKMM')
  obtain ⟨KM', hK_KM', hM'_KM'⟩ := Postulate1 K M' (ne_of_between_ends hKMM')
  have hM_KM' : OnLine M KM' := on_line_of_between_ends hKMM' hK_KM' hM'_KM'
  obtain ⟨FL, hF_FL, hL_FL⟩ := Postulate1 F L hFKML.2.2.1.symm
  have hKM'_FL : Parallel KM' FL := hFKML.2.parallel hK_KM' hM_KM' hL_FL hF_FL
  have hM'MLF : AreParallel M' M L F :=
    AreParallel.of_parallel hM'M hFKML.2.2.1 hM'_KM' hM_KM' hL_FL hF_FL hKM'_FL
  have hM'F : OppositeSidesOf M' F M L := (hFK_ML.trans_opposite hM'K.symm.swap).symm
  have hM'ML_MLF : ∠ M' M L = ∠ M L F := Prop29.alternate hM'MLF hM'F

  /- Add MLL' to each. I.29 makes M'ML and MLL' two right angles,
     so MLF and MLL' are two right angles too. -/
  have hsum₂ : ∠ M' M L + ∠ M L L' = ∠ M L F + ∠ M L L' :=
    CommonNotion2 hM'ML_MLF rfl
  have hM'L'_ML : SameSideOf M' L' M L := hLMM'L'.sameSideOf.swap
  have hM'ML_MLL' : ∠ M' M L + ∠ M L L' = ∟ + ∟ :=
    Prop29.interior hLMM'L'.2.swap_right hM'L'_ML
  have hMLF_MLL' : ∠ M L F + ∠ M L L' = ∟ + ∟ :=
    CommonNotion1 hsum₂.symm hM'ML_MLL'.symm

  /- F and L' lie on opposite sides of ML, so I.14 puts FL and LL'
     in one straight line. -/
  have hFL' : OppositeSidesOf F L' M L :=
    hFK_ML.trans_opposite (hM'L'_ML.symm.trans_opposite hM'K.swap).symm
  have hFLL' : Between F L L' := Prop14 hFL' hMLF_MLL'

  /- I.34 gives FK equal to LM and LM equal to L'M'. The outer sides FK
     and L'M' are parallel to LM; I.30 makes KF parallel to M'L'. -/
  obtain ⟨-, hFK_LM, -, -, -⟩ := Prop34 (A := F) (B := L) (C := K) (D := M) hFKML
  obtain ⟨-, hLM_L'M', -, -, -⟩ :=
    Prop34 (A := L) (B := L') (C := M) (D := M') hLMM'L'
  have hlen : ‖K F‖ = ‖M' L'‖ :=
    CommonNotion1 ((len_symm K F).trans hFK_LM) (hLM_L'M'.trans (len_symm L' M')).symm
  obtain ⟨KF, hK_KF, hF_KF⟩ := Postulate1 K F hFK.symm
  obtain ⟨M'L', hM'_M'L', hL'_M'L'⟩ := Postulate1 M' L' hLMM'L'.1.2.1
  obtain ⟨LM, hL_LM, hM_LM⟩ := Postulate1 L M hLM
  have hKF_LM : Parallel KF LM := hFKML.1.swap_left.parallel hK_KF hF_KF hM_LM hL_LM
  have hM'L'_LM : Parallel M'L' LM :=
    hLMM'L'.1.symm.parallel hM'_M'L' hL'_M'L' hL_LM hM_LM
  have hKF_M'L' : KF ≠ M'L' := fun e => by
    have hK_M'L' : OnLine K M'L' := e ▸ hK_KF
    have hline : M'L' = KM' :=
      line_unique (ne_of_between_ends hKMM') hK_M'L' hM'_M'L' hK_KM' hM'_KM'
    exact hM'L'_LM.not_onLine (hline ▸ hM_KM') hM_LM
  have hpar : AreParallel K F M' L' :=
    AreParallel.of_parallel hFK.symm hLMM'L'.1.2.1 hK_KF hF_KF hM'_M'L' hL'_M'L'
      (Prop30.parallel hKF_LM hM'L'_LM hKF_M'L')

  /- KM' and FL' join the equal parallels in the same direction. By I.33
     they too are parallel, completing the parallelogram KFL'M'. -/
  have hdir : SameSideOf F L' K M' := by
    have hF : SameSide F L KM' := hFL_KM.sameSide hK_KM' hM_KM'
    have hL' : SameSide L' L KM' := hLMM'L'.rotate.sameSideOf.sameSide hM_KM' hM'_KM'
    exact SameSideOf.of_line (ne_of_between_ends hKMM') hK_KM' hM'_KM'
      (same_side_trans (same_side_symm hF) (same_side_symm hL'))
  obtain ⟨-, h33⟩ := Prop33 hpar hlen hdir
  have hwhole : Parallelogram K F L' M' := ⟨hpar.swap_right, h33.symm.swap_right⟩

  /- The whole is the two parallelograms together, and the added one equals
     ABC. The ray KM' is the ray KM, so the angle at K remains E. -/
  have harea : quadArea K F L' M' = quadArea K F L M + △ A B C := by
    rw [quadArea_add_of_parallelograms hKFLM hLMM'L'.rotate.reverse hKMM' hFLL',
      quadArea_reverse M M' L' L, hLMM'L'.quadArea_rotate, hadded]
  refine ⟨K, F, L', M', hwhole, ?_, harea⟩
  rw [angle_onRay_right (OnRay.of_beyond hKMM') hFK]
  exact hang

/-- **I.45, any number of triangles** (companion of I.45). To construct, in a given
rectilineal angle E, a parallelogram equal to any number of given triangles taken together,
at least one: I.42 for the first, then `Prop45.append` for each of the rest, in order. The
triangles are any triangles, each with its corners off one straight line; they need not fit
together into one figure, and the statement claims nothing of a figure. -/
theorem Prop45.sum {E₁ E E₂ : Point} (ts : List (Point × Point × Point)) (hne : ts ≠ [])
    (hts : ∀ t ∈ ts, Triangle t.1 t.2.1 t.2.2) (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M = Magnitude.sum (ts.map fun t => △ t.1 t.2.1 t.2.2) := by
  /- One triangle after another: a parallelogram in the angle E equal to X, with the
     triangles of `rest` added one at a time by `Prop45.append`. -/
  have step : ∀ (rest : List (Point × Point × Point)) (K F L M : Point) (X : Area),
      Parallelogram K F L M → ∠ F K M = ∠ E₁ E E₂ → quadArea K F L M = X →
      (∀ t ∈ rest, Triangle t.1 t.2.1 t.2.2) →
      ∃ K' F' L' M' : Point, Parallelogram K' F' L' M' ∧ ∠ F' K' M' = ∠ E₁ E E₂ ∧
        quadArea K' F' L' M' = X + Magnitude.sum (rest.map fun t => △ t.1 t.2.1 t.2.2) := by
    intro rest
    induction rest with
    | nil =>
      intro K F L M X hp hang harea _
      refine ⟨K, F, L, M, hp, hang, ?_⟩
      rw [harea]
      exact (add_zero X).symm
    | cons t rest ih =>
      intro K F L M X hp hang harea hts
      obtain ⟨K', F', L', M', hp', hang', harea'⟩ :=
        Prop45.append hp hang (hts t (List.mem_cons_self ..)) hE
      obtain ⟨K'', F'', L'', M'', hp'', hang'', harea''⟩ :=
        ih K' F' L' M' (X + △ t.1 t.2.1 t.2.2) hp' hang' (by rw [harea', harea])
          (fun s hs => hts s (List.mem_cons_of_mem _ hs))
      refine ⟨K'', F'', L'', M'', hp'', hang'', ?_⟩
      rw [harea'']
      exact add_assoc X (△ t.1 t.2.1 t.2.2) _
  match ts, hne, hts with
  | (A, B, C) :: rest, _, hts =>
    /- The first triangle, ABC, by I.42. Its parallelogram FGCH, with its angle at G equal
       to E, is named from G, as GFHC. -/
    have h₁ : Triangle A B C := hts (A, B, C) (List.mem_cons_self ..)
    obtain ⟨G, F, H, -, -, hp, hang, harea⟩ := Prop42 h₁ hE
    have hFG : F ≠ G := hp.1.1
    have hGC : G ≠ C := hp.2.1
    obtain ⟨K, F', L, M, hp', hang', harea'⟩ :=
      step rest G F H C (△ A B C) hp.reverse.rotate.rotate.rotate
        (by rw [angle_symm hFG hGC.symm]; exact hang)
        (by rw [quadArea_reverse G C H F, hp.quadArea_rotate, harea])
        (fun s hs => hts s (List.mem_cons_of_mem _ hs))
    exact ⟨K, F', L, M, hp', hang', harea'⟩

/-- **I.45, for any rectilineal figure, with any boundaries** (companion of I.45). To
construct, in a given rectilineal angle E, a parallelogram KFLM, its angle at K equal to E,
equal to a given rectilineal figure: the figure given with any division of it into
triangles, no point inside two of them (`Apart`), and "equal to the figure" meaning equal
to those triangles taken together (`Apart.area`). The figure may have a hole, touch itself
at a corner, or be in more than one piece. It is `Prop45.sum` for the figure's triangles;
lying apart is what makes their sum the figure's. Nothing is claimed of another division of
the figure. -/
theorem Prop45.apart {E₁ E E₂ : Point} (R : Apart) (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M = R.area :=
  Prop45.sum R.pieces R.ne R.triangle hE

/-- **I.45, for any rectilineal figure with one boundary** (companion of I.45). To
construct, in a given rectilineal angle E, a parallelogram KFLM, its angle at K equal to E,
equal to a given rectilineal figure: the figure given with triangles fitted together in a
suitable order, each glued across a side of an earlier one and meeting the earlier ones only
along it (`Rectilineal`), and "equal to the figure" meaning equal to those triangles taken
together (`Rectilineal.area`). The figure may be convex or not, and need have no corner from
which the straight lines to the others divide it. It is `Prop45.apart` for the figure's
triangles, which lie apart (`Fitted.inside_pairwise`, `Rectilineal.toApart`). Nothing is
claimed of another division of the figure. -/
theorem Prop45.figure {E₁ E E₂ : Point} (R : Rectilineal) (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M = R.area :=
  Prop45.apart R.toApart hE

/-- **I.45, for a figure divided from one corner** (companion of I.45), as Euclid and Oliver
Byrne divide it. A figure with corners A₀, A₁, A₂, …, Aₙ, the list `ps` being A₃, …, Aₙ
(empty for a triangle), divided by the straight lines from A₀ into the triangles A₀A₁A₂,
A₀A₂A₃, …, A₀Aₙ₋₁Aₙ, one on each side `segments (A₁ :: A₂ :: ps)`. The division is checked:
each piece is a triangle; each two neighbouring triangles A₀Aᵢ₋₁Aᵢ and A₀AᵢAᵢ₊₁ lie on
opposite sides of the straight line A₀Aᵢ they share (one condition for each of
`triples (A₁ :: A₂ :: ps)`); and the angles A₁A₀A₂, …, Aₙ₋₁A₀Aₙ together are less than four
right angles. Then those triangles, in that order, are fitted together into one figure
(`Fitted.fan`); and, given a rectilineal angle E, there is a parallelogram KFLM, its angle
at K equal to E, equal to that figure, that is, to the triangles taken together. The figure
is read as the one with corners A₀, A₁, …, Aₙ in order round it; that its boundary is that
closed line is not stated in Lean. Nothing is claimed of another division.

The first conclusion is what the two conditions are for: without them the triangles from
A₀ may overlap, and need not be fitted. The parallelogram alone would follow from each
piece being a triangle, by `Prop45.sum`.

Euclid's ABCD with DB joined is the figure with corners D, A, B, C, its triangles DAB and
DBC: A and C lie on opposite sides of DB. Byrne's figure has its corners listed from its
re-entrant corner, from which both his straight lines are drawn. -/
theorem Prop45.fan {A₀ A₁ A₂ E₁ E E₂ : Point} {ps : List Point}
    (htri : ∀ s ∈ segments (A₁ :: A₂ :: ps), Triangle A₀ s.1 s.2)
    (hopp : ∀ t ∈ triples (A₁ :: A₂ :: ps), OppositeSidesOf t.1 t.2.2 A₀ t.2.1)
    (hA₀ : Magnitude.sum ((segments (A₁ :: A₂ :: ps)).map fun s => ∠ s.1 A₀ s.2) <
      ∟ + ∟ + (∟ + ∟))
    (hE : Triangle E₁ E E₂) :
    ∃ R : Rectilineal,
      R.pieces = (segments (A₁ :: A₂ :: ps)).map (fun s => (A₀, s.1, s.2)) ∧
      ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
        quadArea K F L M = R.area :=
  ⟨⟨_, Fitted.fan htri hopp hA₀⟩, rfl, Prop45.figure _ hE⟩

/-- The check: today's statement of I.45, for the two triangles ABD, DBC, follows from
`Prop45.sum` for the list of those two (checked by Lean, up to unfolding definitions). -/
example : type_of% @Elements.BookI.Prop45 := by
  intro A B C D E₁ E E₂ hABD hDBC hE
  have hts : ∀ t ∈ [(A, B, D), (D, B, C)], Triangle t.1 t.2.1 t.2.2 := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hABD
    · exact hDBC
  obtain ⟨K, F, L, M, hp, hang, harea⟩ := Prop45.sum _ (List.cons_ne_nil _ _) hts hE
  refine ⟨K, F, L, M, hp, hang, ?_⟩
  rw [harea]
  simp only [List.map, Magnitude.sum, add_zero]

end Elements.BookI
