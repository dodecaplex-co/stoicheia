import Elements.Figure.Basics
import Elements.BookI.Prop13
import Elements.BookI.Prop14
import Elements.BookI.Prop29
import Elements.BookI.Prop30
import Elements.BookI.Prop33
import Elements.BookI.Prop34
import Elements.BookI.Prop42
import Elements.BookI.Prop44
import Elements.BookI.HelpersParallels

/-!
# Book I, Proposition 45

Euclid's text, in Heath's translation: [`heath/I/45.md`](../../heath/I/45.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

`Prop45` is Euclid's worked configuration: the four-sided figure ABCD, divided by DB into the
triangles ABD and DBC. Euclid's proof makes a parallelogram for the first triangle [I. 42],
applies one for the second to its side [I. 44], and shows that the two make one
parallelogram; a figure of more triangles repeats the second step, as Oliver Byrne draws it
for three (1847, p. 46). The companions after it take a rectilineal figure given with its
triangles:

* `Prop45.append` is that second step.
* `Prop45.sum` repeats it, for any number of triangles. It is the construction, and claims
  nothing of a figure: the triangles need not fit together.
* `Prop45.apart` is the proposition for a figure given with triangles that do not overlap,
  no point inside two of them (`Apart`).
  The figure may have a hole (Definition I.14: "any boundary or boundaries").
* `Prop45.figure` is the proposition for a figure with one boundary, given with triangles
  fitted together in a suitable order (`Rectilineal`, `Fitted`). It follows from
  `Prop45.apart`, since fitted triangles lie apart (`Fitted.inside_pairwise`).
* `Prop45.fan`, the main companion, is the proposition for a figure divided as Euclid and
  Byrne divide it, by the straight lines from one corner A₀, with the two conditions that
  make those triangles a figure: neighbouring triangles on opposite sides of the straight
  line they share, and the angles at A₀ together less than four right angles. It concludes
  that the triangles are fitted together into one figure (`Fitted.fan`, just before it),
  and that the parallelogram is equal to that figure (`Prop45.figure`). The two conditions
  are what the first conclusion needs.

The names: `figure` is Euclid's word for what is given ("a given rectilineal figure"), so the
companion for a figure glued together has it; `apart` names the figure whose triangles lie
apart; `fan` names the division Euclid draws, from one corner, which not every figure
admits. A checked fan is a fitted figure, and a fitted figure's triangles lie apart, so the
three agree on the figures they share.

**What "equal to the figure" means here.** The parallelogram is equal to the triangles the
figure is given with, taken together. That sum is what Euclid adds up when he calls ABD and
DBC "the whole rectilineal figure ABCD". Nothing here says that another division of the
figure gives the same area: Euclid takes that for granted, and David Hilbert proved it, for
his measure of area (Book I's gap catalogue, under I.45). `Prop45` itself is an area-sum
theorem: it follows from `Prop45.sum` (the check at the end), and its ABD and DBC need only
be triangles, which may overlap. It represents Euclid's pictured division when A and C lie
on opposite sides of DB, and that checked case is `Prop45.fan` for the corners D, A, B, C.
-/

namespace Elements.BookI

open Tacit

/-- To construct, in a given rectilineal angle, a parallelogram equal to a given rectilineal figure. -/
theorem Prop45 {A B C D E₁ E E₂ : Point} (hABD : Triangle A B D) (hDBC : Triangle D B C)
    (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M = △ A B D + △ D B C := by
  -- Let ABCD be the given rectilineal figure and E the given rectilineal angle; thus it is
  -- required to construct, in the given angle E, a parallelogram equal to the rectilineal
  -- figure ABCD.
  -- Let DB be joined, and let the parallelogram FH be constructed equal to the triangle ABD,
  -- in the angle HKF which is equal to E; [I. 42] let the parallelogram GM equal to the
  -- triangle DBC be applied to the straight line GH, in the angle GHM which is equal to
  -- E. [I. 44]
  /- I.42 builds on half of the triangle's own base, so KH lies along BD and H
     falls on D: the Lean writes D wherever Euclid writes H, and in our figure KFLM
     overlaps ABCD. K lies between B and D, and F is on A's side of BD. -/
  obtain ⟨K, F, G, hBKD, hFA, hFKHG, hHKF, hFH⟩ := Prop42 hABD hE
  have hGHK : Triangle G D K := hFKHG.1.symm.swap_right.triangle.bac
  /- I.44's point for the side is taken across GH from K, so that KH and HM are
     "not lying on the same side", as I.14 will ask. -/
  obtain ⟨P, hPK, -⟩ := exists_oppositeSidesOf hGHK []
  obtain ⟨L, M, hMP, hGHML, hGHM, hGM⟩ := Prop44 hGHK.ne₁₂ hDBC hE hPK.triangle
  have hMK : OppositeSidesOf M K G D := hMP.trans_opposite hPK
  have hKD : K ≠ D := hGHK.ne₂₃.symm
  have hGD : G ≠ D := hGHK.ne₁₂
  have hFK : F ≠ K := hFKHG.1.1
  -- Then, since the angle E is equal to each of the angles HKF, GHM, the angle HKF is also
  -- equal to the angle GHM. [C.N. 1]
  have hHKF_GHM : ∠ D K F = ∠ G D M := CommonNotion1 hHKF hGHM
  -- Let the angle KHG be added to each; therefore the angles FKH, KHG are equal to the angles
  -- KHG, GHM.
  have hsum₁ : ∠ F K D + ∠ K D G = ∠ K D G + ∠ G D M := by
    rw [angle_symm hFK hKD.symm, hHKF_GHM, add_comm]
  -- But the angles FKH, KHG are equal to two right angles; [I. 29] therefore the angles KHG,
  -- GHM are also equal to two right angles.
  have hFG_KH : SameSideOf F G K D := hFKHG.rotate.sameSideOf.symm
  have h29a : ∠ F K D + ∠ K D G = ∟ + ∟ := Prop29.interior hFKHG.1.swap_left hFG_KH
  have hKHG_GHM : ∠ K D G + ∠ G D M = ∟ + ∟ := hsum₁.symm.trans h29a
  -- Thus, with a straight line GH, and at the point H on it, two straight lines KH, HM not
  -- lying on the same side make the adjacent angles equal to two right angles; therefore KH is
  -- in a straight line with HM. [I. 14]
  have hKHM : Between K D M := Prop14 hMK.symm (by
    rw [angle_symm hGD hKD]
    exact hKHG_GHM)
  -- And, since the straight line HG falls upon the parallels KM, FG, the alternate angles MHG,
  -- HGF are equal to one another. [I. 29]
  have hFK_HG : SameSideOf F K D G := hFKHG.rotate.rotate.sameSideOf
  have hMD : M ≠ D := ne_of_between (between_symm hKHM)
  obtain ⟨KM, hK_KM, hM_KM⟩ := Postulate1 K M (ne_of_between_ends hKHM)
  have hD_KM : OnLine D KM := on_line_of_between_ends hKHM hK_KM hM_KM
  obtain ⟨FG, hF_FG, hG_FG⟩ := Postulate1 F G hFKHG.2.2.1.symm
  have hKM_FG : Parallel KM FG := hFKHG.2.parallel hK_KM hD_KM hG_FG hF_FG
  have hMHGF : AreParallel M D G F :=
    AreParallel.of_parallel hMD hFKHG.2.2.1 hM_KM hD_KM hG_FG hF_FG hKM_FG
  have hMF : OppositeSidesOf M F D G := (hFK_HG.trans_opposite hMK.symm.swap).symm
  have hMHG_HGF : ∠ M D G = ∠ D G F := Prop29.alternate hMHGF hMF
  -- Let the angle HGL be added to each; therefore the angles MHG, HGL are equal to the angles
  -- HGF, HGL. [C.N. 2]
  have hsum₂ : ∠ M D G + ∠ D G L = ∠ D G F + ∠ D G L := CommonNotion2 hMHG_HGF rfl
  -- But the angles MHG, HGL are equal to two right angles; [I. 29] therefore the angles HGF,
  -- HGL are also equal to two right angles. [C.N. 1]
  have hML_HG : SameSideOf M L D G := hGHML.sameSideOf.swap
  have h29c : ∠ M D G + ∠ D G L = ∟ + ∟ := Prop29.interior hGHML.2.swap_right hML_HG
  have hHGF_HGL : ∠ D G F + ∠ D G L = ∟ + ∟ := CommonNotion1 hsum₂.symm h29c.symm
  -- Therefore FG is in a straight line with GL. [I. 14]
  have hFL : OppositeSidesOf F L D G :=
    hFK_HG.trans_opposite (hML_HG.symm.trans_opposite hMK.swap).symm
  have hFGL : Between F G L := Prop14 hFL hHGF_HGL
  -- And, since FK is equal and parallel to HG, [I. 34] and HG to ML also, KF is also equal and
  -- parallel to ML; [C.N. 1; I. 30] and the straight lines KM, FL join them (at their
  -- extremities); therefore KM, FL are also equal and parallel. [I. 33]
  obtain ⟨-, hFK_GH, -, -, -⟩ := Prop34 (A := F) (B := G) (C := K) (D := D) hFKHG
  obtain ⟨-, hGH_LM, -, -, -⟩ := Prop34 (A := G) (B := L) (C := D) (D := M) hGHML
  have hlen : ‖K F‖ = ‖M L‖ :=
    CommonNotion1 ((len_symm K F).trans hFK_GH) (hGH_LM.trans (len_symm L M)).symm
  obtain ⟨KF, hK_KF, hF_KF⟩ := Postulate1 K F hFK.symm
  obtain ⟨ML, hM_ML, hL_ML⟩ := Postulate1 M L hGHML.1.2.1
  obtain ⟨GD, hG_GD, hD_GD⟩ := Postulate1 G D hGD
  have hKF_GD : Parallel KF GD := hFKHG.1.swap_left.parallel hK_KF hF_KF hD_GD hG_GD
  have hML_GD : Parallel ML GD := hGHML.1.symm.parallel hM_ML hL_ML hG_GD hD_GD
  have hKF_ML : KF ≠ ML := fun e => by
    have hK_ML : OnLine K ML := e ▸ hK_KF
    have : ML = KM := line_unique (ne_of_between_ends hKHM) hK_ML hM_ML hK_KM hM_KM
    exact hML_GD.not_onLine (this ▸ hD_KM) hD_GD
  have hpar : AreParallel K F M L :=
    AreParallel.of_parallel hFK.symm hGHML.1.2.1 hK_KF hF_KF hM_ML hL_ML
      (Prop30.parallel hKF_GD hML_GD hKF_ML)
  have hdir : SameSideOf F L K M := by
    have hF : SameSide F G KM := hFG_KH.sameSide hK_KM hD_KM
    have hL : SameSide L G KM := hGHML.rotate.sameSideOf.sameSide hD_KM hM_KM
    exact SameSideOf.of_line (ne_of_between_ends hKHM) hK_KM hM_KM
      (same_side_trans (same_side_symm hF) (same_side_symm hL))
  obtain ⟨-, h33⟩ := Prop33 hpar hlen hdir
  -- Therefore KFLM is a parallelogram.
  have hKFLM : Parallelogram K F L M := ⟨hpar.swap_right, h33.symm.swap_right⟩
  -- And, since the triangle ABD is equal to the parallelogram FH, and DBC to GM, the whole
  -- rectilineal figure ABCD is equal to the whole parallelogram KFLM.
  have hwhole : quadArea K F L M = △ A B D + △ D B C := by
    rw [quadArea_add_of_parallelograms hFKHG.rotate.reverse hGHML.rotate.reverse hKHM hFGL,
      quadArea_reverse K D G F, hFKHG.quadArea_rotate, hFH,
      quadArea_reverse D M L G, hGHML.quadArea_rotate, hGM]
  -- Therefore the parallelogram KFLM has been constructed equal to the given rectilineal
  -- figure ABCD, in the angle FKM which is equal to the given angle E.
  refine ⟨K, F, L, M, hKFLM, ?_, hwhole⟩
  rw [angle_onRay_right (OnRay.of_beyond hKHM) hFK, angle_symm hFK hKD.symm]
  exact hHKF
  -- Q. E. F.

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
     and L'M' are parallel to LM, and are not one straight line, for that
     line would be KM', which meets LM at M; I.30 makes KF parallel to M'L'. -/
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

/-- **I.45, for a figure given with triangles that lie apart** (companion of I.45). To
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

/-- **I.45, for a figure with one boundary, given with triangles fitted together**
(companion of I.45). To construct, in a given rectilineal angle E, a parallelogram KFLM,
its angle at K equal to E,
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

end Elements.BookI

namespace Elements

/-! ## Euclid's and Byrne's division, checked

Euclid's DB, drawn from the corner D of ABCD, and Oliver Byrne's two straight lines from one
corner of his figure (1847, p. 46), divide it into triangles A₀A₁A₂, A₀A₂A₃, …, A₀Aₙ₋₁Aₙ from one
corner A₀. `Fitted.fan` says when those triangles are a figure in the sense of `Fitted`: each
two neighbouring triangles lie on opposite sides of the straight line A₀Aᵢ they share, and the
angles A₁A₀A₂, …, Aₙ₋₁A₀Aₙ together are less than four right angles. Without the two
conditions the triangles from A₀ may overlap or reach outside the figure, and their sum need
not equal the area of their union: a pentagon whose second and fourth corners lie on one side
of the straight line from the first corner to the third has three triangles from the first
corner together greater than it, and the first condition fails there. That the figure the
fan's triangles make is the one bounded by the closed line A₀A₁…AₙA₀, its corners in that
order, is a reading of the conditions, true in the plane, and is not stated in Lean:
`Fitted.fan` says only that the triangles fit together into one figure.

Its proof goes by induction along the corners, each new triangle glued to the one before it
along A₀Aᵢ. It carries the sector at A₀ swept from the ray A₀A₁, in the one orientation the
condition on neighbours fixes, in three cases as the sum of the angles so far is less than two
right angles, equal to two, or greater; the bound of four right angles does its work only in
the last. It cites I.13, so it stands here, beside I.45 and before `Prop45.fan`, which uses
it, rather than in Book Zero. The helpers before it, `Fitted.fan.<word>`, each supply one of
its steps, named in its docstring.
-/

/-- If x and y together are less than z, then x alone is less than z, being not greater than
the whole (C.N. 5). -/
theorem Fitted.fan.part {k : Kind} {x y z : Magnitude k} (h : x + y < z) : x < z := by
  by_cases hy : y = 0
  · simpa only [hy, Tacit.add_zero] using h
  · exact Tacit.lt_trans (CommonNotion5 (Magnitude.pos_of_ne_zero hy)) h

/-- "Not greater than" carries on: if x is not greater than y, nor y than z, then x is not
greater than z. -/
theorem Fitted.fan.weaken {k : Kind} {x y z : Magnitude k}
    (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  intro hzx
  rcases Tacit.lt_trichotomy x y with h | h | h
  · exact hyz (Tacit.lt_trans hzx h)
  · exact hyz (h ▸ hzx)
  · exact hxy h

/-- If x is not greater than y, and y is less than z, then x is less than z. -/
theorem Fitted.fan.bounded {k : Kind} {x y z : Magnitude k}
    (hxy : x ≤ y) (hyz : y < z) : x < z := by
  rcases Tacit.lt_trichotomy x y with h | h | h
  · exact Tacit.lt_trans h hyz
  · exact h ▸ hyz
  · exact False.elim (hxy h)

/-- Adding the same thing keeps "not greater than": if y is not greater than z, then x and y
together are not greater than x and z together. -/
theorem Fitted.fan.addition {k : Kind} (x : Magnitude k) {y z : Magnitude k}
    (hyz : y ≤ z) : x + y ≤ x + z := by
  intro h
  exact hyz (Magnitude.lt_of_add_lt_add_left h)

/-- Something added makes nothing less: x and y together are not less than x. -/
theorem Fitted.fan.growth {k : Kind} (x y : Magnitude k) : x ≤ x + y := by
  intro h
  have h' : x + y < x + 0 := by simpa only [Tacit.add_zero] using h
  exact Tacit.not_lt_zero y (Magnitude.lt_of_add_lt_add_left h')

/-- If B lies on the ray from O through A, every point of the ray from O through B
lies on it too. This carries positions along a boundary ray. -/
theorem Fitted.fan.ray {O A B Y : Point} (hY : OnRay Y O B) (hB : OnRay B O A) :
    OnRay Y O A := by
  obtain ⟨L, hO, hA, hBL⟩ := hB.2.2.1
  exact ⟨hB.1, hY.2.1, ⟨L, hO, hA, hY.onLine hO hBL⟩,
    hY.not_between hB.symm⟩

/-- If B is on the other side of OA from D, so is every point of the ray from O through B.
This carries positions along rays in the second half-plane. -/
theorem Fitted.fan.rayOpposite {O A B D Y : Point}
    (hY : OnRay Y O B) (hBD : OppositeSidesOf B D O A) :
    OppositeSidesOf Y D O A := by
  obtain ⟨L, hO, hA⟩ := Postulate1 O A hBD.1
  have hBB : SameSideOf B B O A :=
    SameSideOf.of_line hBD.1 hO hA (Tacit.same_side_refl (hBD.oppositeSides hO hA).1)
  exact (SameSideOf.of_onRay hY hBB).trans_opposite hBD

/-- A point between B and C is on C's side of OB (System E, Pasch 2): the side BC of the
triangle OBC, in `Fitted.fan.within`. -/
theorem Fitted.fan.base {O B C Y : Point} (hOBC : Triangle O B C)
    (hBYC : Between B Y C) : SameSideOf Y C O B := by
  obtain ⟨L, hO, hB⟩ := Postulate1 O B hOBC.ne₁₂
  have hY : ¬ OnLine Y L := fun hY =>
    hOBC.off_line hO hB (Tacit.on_line_of_between hBYC hB hY)
  exact SameSideOf.of_line hOBC.ne₁₂ hO hB (Tacit.pasch2 hBYC hB hY)

/-- **A point within or on the triangle OBC** lies on the finite straight line OB, or on C's
side of OB, making with OB an angle not greater than BOC. O itself, the corners and the
sides are among the cases. -/
theorem Fitted.fan.within {O B C Y : Point} (hOBC : Triangle O B C)
    (hY : OnOrInsideTriangle Y O B C) :
    OnFiniteLine Y O B ∨ (SameSideOf Y C O B ∧ ∠ B O Y ≤ ∠ B O C) := by
  have hCC : SameSideOf C C O B := by
    obtain ⟨L, hO, hB⟩ := Postulate1 O B hOBC.ne₁₂
    exact SameSideOf.of_line hOBC.ne₁₂ hO hB
      (Tacit.same_side_refl (hOBC.off_line hO hB))
  rcases hY with hY | hY | hY | hY | rfl | rfl | rfl
  · /- Within the triangle: on C's side of OB and on B's side of OC, so within the angle
       BOC, which is made up of BOY and YOC. -/
    refine Or.inr ⟨hY.2.2, ?_⟩
    rw [angle_add_of_within hY.2.2 hY.2.1.swap]
    exact fan.growth _ _
  · exact Or.inl (Or.inr (Or.inr hY))
  · /- On the side BC: on C's side of OB, and BOC is made up of BOY and YOC. -/
    refine Or.inr ⟨fan.base hOBC hY, ?_⟩
    rw [angle_add_of_between hOBC.bca hY]
    exact fan.growth _ _
  · /- On the side CO: on the ray from O through C, where the angle is BOC itself. -/
    have hYC : OnRay Y O C := OnRay.of_between (Tacit.between_symm hY)
    refine Or.inr ⟨SameSideOf.of_onRay hYC hCC, ?_⟩
    rw [angle_onRay_right hYC hOBC.ne₁₂.symm]
    exact Tacit.lt_irrefl _
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact Or.inr ⟨hCC, Tacit.lt_irrefl _⟩

/-- **The half turn.** Let AO be produced beyond O to A', let B be off the straight line AA',
and let C be on the other side of OB from A, so that the ray OC turns on from OB, away from
OA. Then OC stays on B's side of AA', B is within the angle AOC, on A's side of OC, and the
angles AOB and BOC make up AOC; or C lies on OA', and AOB and BOC make two right angles
(I.13); or C passes beyond, to the other side of AA', B is on the same side of OC as A',
and AOB and BOC make two right angles and the angle A'OC (I.13). Triple incidence places
the rays; no straight angle is measured. -/
theorem Fitted.fan.advance {O A A' B C : Point} (hAOA' : Between A O A')
    (hOAB : Triangle O A B) (hAC : OppositeSidesOf A C O B) :
    (SameSideOf B C O A ∧ SameSideOf B A O C ∧
      ∠ A O B + ∠ B O C = ∠ A O C) ∨
    (Between A O C ∧ ∠ A O B + ∠ B O C = ∟ + ∟) ∨
    (OppositeSidesOf B C O A ∧ SameSideOf B A' O C ∧
      ∠ A O B + ∠ B O C = ∟ + ∟ + ∠ A' O C) := by
  obtain ⟨L, hOL, hAL⟩ := Postulate1 O A hOAB.ne₁₂
  have hA'L : OnLine A' L := Tacit.on_line_of_between hAOA' hAL hOL
  have hBL : ¬ OnLine B L := hOAB.off_line hOL hAL
  obtain ⟨M, hOM, hBM⟩ := Postulate1 O B hOAB.ne₁₃
  have hACM := hAC.oppositeSides hOM hBM
  have hOC : O ≠ C := hAC.symm.triangle.ne₁₃
  obtain ⟨N, hON, hCN⟩ := Postulate1 O C hOC
  by_cases hCL : OnLine C L
  · /- On OA, the side condition puts C beyond O from A, on the ray through A'. -/
    have hAOA'C : SameSideOf A' C O B :=
      hAC.sameSideOf_of_between hAOA'
    have hCA' : OnRay C O A' := OnRay.of_sameSideOf hAOA'C.symm
      ⟨L, hOL, hA'L, hCL⟩ hOC.symm
    have hAOC : Between A O C := hCA'.between hAOA'
    have hACB : Triangle A C B := Triangle.of_line hAL hCL
      (Tacit.ne_of_between_ends hAOC) hBL
    exact Or.inr (Or.inl ⟨hAOC, BookI.Prop13 hAOC hACB⟩)
  by_cases hBC : SameSide B C L
  · /- In one half-plane, OB lies within AOC by Triple incidence 2. -/
    have hABN : SameSide A B N := Tacit.triple_incidence2
      hOL hOM hON hAL hBM hCN hBC hACM.2.2 hACM.2.1 hOAB.ne₁₂.symm
    have hBC' := SameSideOf.of_line hOAB.ne₁₂ hOL hAL hBC
    have hBA_OC := SameSideOf.of_line hOC hON hCN (Tacit.same_side_symm hABN)
    exact Or.inl ⟨hBC', hBA_OC, (angle_add_of_within hBC' hBA_OC).symm⟩
  · /- Across OA, the produced ray OA' lies within BOC. I.13 accounts for the
       angles from OA through OB to OA', leaving the angle A'OC. -/
    have hBC' : OppositeSidesOf B C O A :=
      OppositeSidesOf.of_line hOAB.ne₁₂ hOL hAL ⟨hBL, hCL, hBC⟩
    have hA'C : SameSideOf A' C O B := hAC.sameSideOf_of_between hAOA'
    have hBA'N : SameSide B A' N := Tacit.triple_incidence2
      hOM hOL hON hBM hA'L hCN (hA'C.sameSide hOM hBM) hBC hCL hOAB.ne₁₃.symm
    have hBA' : SameSideOf B A' O C := SameSideOf.of_line hOC hON hCN hBA'N
    have hAA'B : Triangle A A' B := Triangle.of_line hAL hA'L
      (Tacit.ne_of_between_ends hAOA') hBL
    refine Or.inr (Or.inr ⟨hBC', hBA', ?_⟩)
    rw [angle_add_of_within hA'C hBA'.symm, ← Tacit.add_assoc,
      BookI.Prop13 hAOA' hAA'B]

/-- **The position of a point round O.** There is a measure p of where each point lies
round O, starting from the ray OA and turning towards D's side of OA: nothing on the ray
OA; the angle AOY at a point Y on D's side; two right angles on the ray OA', which is AO
produced beyond O; and two right angles together with A'OY at a point Y on the other side.
The two rays are given their positions outright, so that no straight angle, and no angle
at a repeated point, is ever measured: the axioms fix the size of neither. The measure is
chosen by cases, and the proof uses only these four properties of it. -/
theorem Fitted.fan.positions {O A A' D : Point} (hAOA' : Between A O A')
    (hOAD : Triangle O A D) :
    ∃ p : Point → Angle, ∀ Y : Point,
      (OnRay Y O A → p Y = 0) ∧
      (SameSideOf Y D O A → p Y = ∠ A O Y) ∧
      (OnRay Y O A' → p Y = ∟ + ∟) ∧
      (OppositeSidesOf Y D O A → p Y = ∟ + ∟ + ∠ A' O Y) := by
  classical
  let p : Point → Angle := fun Y =>
    if SameSideOf Y D O A then ∠ A O Y
    else if OppositeSidesOf Y D O A then ∟ + ∟ + ∠ A' O Y
    else if OnRay Y O A then 0 else ∟ + ∟
  obtain ⟨L, hO, hA⟩ := Postulate1 O A hOAD.ne₁₂
  have hA' : OnLine A' L := Tacit.on_line_of_between hAOA' hA hO
  refine ⟨p, ?_⟩
  intro Y
  have hline : OnLine Y L → ¬ SameSideOf Y D O A ∧ ¬ OppositeSidesOf Y D O A := by
    intro hY
    exact ⟨fun h => Tacit.not_on_line_of_same_side (h.sameSide hO hA) hY,
      fun h => (h.oppositeSides hO hA).1 hY⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hY
    obtain ⟨hs, ho⟩ := hline (hY.onLine hO hA)
    simp only [p, ite_eq_right hs, ite_eq_right ho, ite_eq_left hY]
  · intro hY
    simp only [p, ite_eq_left hY]
  · intro hY
    obtain ⟨hs, ho⟩ := hline (hY.onLine hO hA')
    have hr : ¬ OnRay Y O A := fun h => h.2.2.2 (Tacit.between_symm (hY.between hAOA'))
    simp only [p, ite_eq_right hs, ite_eq_right ho, ite_eq_right hr]
  · intro hY
    have hs : ¬ SameSideOf Y D O A := fun h =>
      (hY.oppositeSides hO hA).2.2 (h.sameSide hO hA)
    simp only [p, ite_eq_right hs, ite_eq_left hY]

/-- Every point of the ray from O through B is at B's position, wherever B is: on D's side
of OA, on the ray OA', or on the other side. -/
theorem Fitted.fan.along {O A A' D B Y : Point} {p : Point → Angle}
    (hAOA' : Between A O A')
    (hposition : ∀ Y : Point,
      (OnRay Y O A → p Y = 0) ∧
      (SameSideOf Y D O A → p Y = ∠ A O Y) ∧
      (OnRay Y O A' → p Y = ∟ + ∟) ∧
      (OppositeSidesOf Y D O A → p Y = ∟ + ∟ + ∠ A' O Y))
    (hB : SameSideOf B D O A ∨ OnRay B O A' ∨ OppositeSidesOf B D O A)
    (hY : OnRay Y O B) : p Y = p B := by
  rcases hB with hBD | hBA' | hBD
  · rw [(hposition Y).2.1 (SameSideOf.of_onRay hY hBD), (hposition B).2.1 hBD]
    exact angle_onRay_right hY (Tacit.ne_of_between hAOA')
  · rw [(hposition Y).2.2.1 (fan.ray hY hBA'), (hposition B).2.2.1 hBA']
  · rw [(hposition Y).2.2.2 (fan.rayOpposite hY hBD), (hposition B).2.2.2 hBD,
      angle_onRay_right hY (Tacit.ne_of_between (Tacit.between_symm hAOA'))]

/-- **A step round O.** Let B be at position S, with the corner P before it behind B: on A's
side of OB when B is on D's side of OA, on D's side of OA when B is on the ray OA', and on
the same side of OB as A' when B is on the other side of OA. These are the three cases of
the running sum S: less than two right angles, exactly two, and more than two. If C is on the
other side of OB from P, and S together with the angle BOC is less than four right angles,
then C is at the position S together with BOC, and B is behind C in the same sense. In the
first case the step is the half turn from OA; in the second, OC leaves the ray OA' for the
other side; in the third, the half turn from OA', in which OC can neither come back to the
ray OA nor pass it, for the angles would make four right angles or more. That is the one
place the bound of four right angles is used. -/
theorem Fitted.fan.turn {O A A' D P B C : Point} {p : Point → Angle} {S : Angle}
    (hAOA' : Between A O A')
    (hposition : ∀ Y : Point,
      (OnRay Y O A → p Y = 0) ∧
      (SameSideOf Y D O A → p Y = ∠ A O Y) ∧
      (OnRay Y O A' → p Y = ∟ + ∟) ∧
      (OppositeSidesOf Y D O A → p Y = ∟ + ∟ + ∠ A' O Y))
    (hB : (SameSideOf B D O A ∧ SameSideOf P A O B) ∨
      (OnRay B O A' ∧ SameSideOf P D O A) ∨
      (OppositeSidesOf B D O A ∧ SameSideOf P A' O B))
    (hpB : p B = S) (hPC : OppositeSidesOf P C O B)
    (hS : S + ∠ B O C < ∟ + ∟ + (∟ + ∟)) :
    p C = S + ∠ B O C ∧
      ((SameSideOf C D O A ∧ SameSideOf B A O C) ∨
      (OnRay C O A' ∧ SameSideOf B D O A) ∨
      (OppositeSidesOf C D O A ∧ SameSideOf B A' O C)) := by
  obtain ⟨L, hOL, hAL⟩ := Postulate1 O A (Tacit.ne_of_between hAOA').symm
  have hA'L : OnLine A' L := Tacit.on_line_of_between hAOA' hAL hOL
  have hOA' : O ≠ A' := (Tacit.ne_of_between (Tacit.between_symm hAOA')).symm
  have hOBC : Triangle O B C := hPC.symm.triangle
  rcases hB with ⟨hBD, hPA⟩ | ⟨hBA', hPD⟩ | ⟨hBD, hPA'⟩
  · /- Less than two right angles: the position is the angle AOB. -/
    have hSB : S = ∠ A O B := hpB.symm.trans ((hposition B).2.1 hBD)
    have hAC : OppositeSidesOf A C O B := hPA.symm.trans_opposite hPC
    rcases fan.advance hAOA' hBD.triangle hAC with
      ⟨hBC, hBA, hsum⟩ | ⟨hAOC, hsum⟩ | ⟨hBC, hBA', hsum⟩
    · have hCD : SameSideOf C D O A := hBC.symm.trans hBD
      refine ⟨?_, Or.inl ⟨hCD, hBA⟩⟩
      rw [hSB, hsum]
      exact (hposition C).2.1 hCD
    · have hCA' : OnRay C O A' := OnRay.of_between_between hAOA' hAOC
      refine ⟨?_, Or.inr (Or.inl ⟨hCA', hBD⟩)⟩
      rw [hSB, hsum]
      exact (hposition C).2.2.1 hCA'
    · have hCD : OppositeSidesOf C D O A := (hBD.symm.trans_opposite hBC).symm
      refine ⟨?_, Or.inr (Or.inr ⟨hCD, hBA'⟩)⟩
      rw [hSB, hsum]
      exact (hposition C).2.2.2 hCD
  · /- Exactly two right angles: OB is the opposite ray from OA. -/
    have hSB : S = ∟ + ∟ := hpB.symm.trans ((hposition B).2.2.1 hBA')
    have hBL : OnLine B L := hBA'.onLine hOL hA'L
    have hPC' : OppositeSidesOf P C O A := OppositeSidesOf.of_line
      (Tacit.ne_of_between hAOA').symm hOL hAL (hPC.oppositeSides hOL hBL)
    have hCD : OppositeSidesOf C D O A := (hPD.symm.trans_opposite hPC').symm
    obtain ⟨N, hON, hCN⟩ := Postulate1 O C hOBC.ne₁₃
    have hA'N : ¬ OnLine A' N := fun h => hOBC.acb.off_line hON hCN (hBA'.onLine hON h)
    have hA'A' : SameSideOf A' A' O C := SameSideOf.of_line hOBC.ne₁₃ hON hCN
      (Tacit.same_side_refl hA'N)
    refine ⟨?_, Or.inr (Or.inr ⟨hCD, SameSideOf.of_onRay hBA' hA'A'⟩)⟩
    rw [hSB, angle_onRay_left hBA' hOBC.ne₁₃.symm]
    exact (hposition C).2.2.2 hCD
  · /- More than two right angles: measure the rest from OA produced through O. -/
    have hSB : S = ∟ + ∟ + ∠ A' O B := hpB.symm.trans ((hposition B).2.2.2 hBD)
    have hOA'B : Triangle O A' B := Triangle.of_line hOL hA'L hOA'
      (hBD.oppositeSides hOL hAL).1
    have hA'C : OppositeSidesOf A' C O B := hPA'.symm.trans_opposite hPC
    rcases fan.advance (Tacit.between_symm hAOA') hOA'B hA'C with
      ⟨hBC, hBA', hsum⟩ | ⟨_, hsum⟩ | ⟨_, _, hsum⟩
    · have hBC' : SameSideOf B C O A := SameSideOf.of_line
        (Tacit.ne_of_between hAOA').symm hOL hAL (hBC.sameSide hOL hA'L)
      have hCD : OppositeSidesOf C D O A := hBC'.symm.trans_opposite hBD
      refine ⟨?_, Or.inr (Or.inr ⟨hCD, hBA'⟩)⟩
      rw [hSB, Tacit.add_assoc, hsum]
      exact (hposition C).2.2.2 hCD
    · rw [hSB, Tacit.add_assoc, hsum] at hS
      exact False.elim (Tacit.lt_irrefl _ hS)
    · rw [hSB, Tacit.add_assoc, hsum, ← Tacit.add_assoc] at hS
      exact False.elim (Tacit.lt_irrefl _ (fan.part hS))

/-- **The new triangle lies beyond the region already swept**, save along its side OB. With
B at position S and P behind it, as in `Fitted.fan.turn`, every point within or on the
triangle OBC lies on the finite straight line OB, or is a point other than O at a position
greater than S and not greater than S together with the angle BOC. -/
theorem Fitted.fan.sweep {O A A' D P B C Y : Point} {p : Point → Angle} {S : Angle}
    (hAOA' : Between A O A')
    (hposition : ∀ Y : Point,
      (OnRay Y O A → p Y = 0) ∧
      (SameSideOf Y D O A → p Y = ∠ A O Y) ∧
      (OnRay Y O A' → p Y = ∟ + ∟) ∧
      (OppositeSidesOf Y D O A → p Y = ∟ + ∟ + ∠ A' O Y))
    (hB : (SameSideOf B D O A ∧ SameSideOf P A O B) ∨
      (OnRay B O A' ∧ SameSideOf P D O A) ∨
      (OppositeSidesOf B D O A ∧ SameSideOf P A' O B))
    (hpB : p B = S) (hPC : OppositeSidesOf P C O B)
    (hOBC : Triangle O B C) (hS : S + ∠ B O C < ∟ + ∟ + (∟ + ∟))
    (hY : OnOrInsideTriangle Y O B C) :
    OnFiniteLine Y O B ∨ (Y ≠ O ∧ S < p Y ∧ p Y ≤ S + ∠ B O C) := by
  rcases fan.within hOBC hY with hY | ⟨hYC, hBY⟩
  · exact Or.inl hY
  · /- Off OB, Y is on C's side of OB, and so on the other side from P: the step round O
       from B reaches Y at the position S together with BOY, which is greater than S,
       BOY being something, and not greater than S together with BOC. -/
    have hPY : OppositeSidesOf P Y O B := (hYC.trans_opposite hPC.symm).symm
    have hSY : S + ∠ B O Y ≤ S + ∠ B O C := fan.addition S hBY
    obtain ⟨hpY, _⟩ := fan.turn hAOA' hposition hB hpB hPY (fan.bounded hSY hS)
    refine Or.inr ⟨hYC.triangle.ne₁₃.symm, ?_, ?_⟩
    · rw [hpY]
      exact CommonNotion5 hYC.triangle.bac.angle_pos
    · rw [hpY]
      exact hSY

/-- **Euclid's and Oliver Byrne's division is a figure, when it is checked.** A figure given
by its corners A₀, A₁, A₂, …, Aₙ, the list `ps` being A₃, …, Aₙ, and divided by the straight
lines from A₀ into the triangles A₀A₁A₂, A₀A₂A₃, …, A₀Aₙ₋₁Aₙ, one on each side
`segments (A₁ :: A₂ :: ps)`. Suppose each is a triangle; each two neighbouring triangles,
A₀Aᵢ₋₁Aᵢ and A₀AᵢAᵢ₊₁, lie on opposite sides of the straight line A₀Aᵢ they share, that is,
Aᵢ₋₁ and Aᵢ₊₁ are on opposite sides of it (one condition for each of
`triples (A₁ :: A₂ :: ps)`); and the angles A₁A₀A₂, A₂A₀A₃, …, Aₙ₋₁A₀Aₙ at A₀ together are
less than four right angles. Then those triangles, in that order, are fitted together into
one figure: each is laid across the straight line A₀Aᵢ against the one before it, and meets
the earlier ones only along that straight line. The figure they make is read as the figure
with corners A₀, A₁, …, Aₙ in order round it; that its boundary is the closed line A₀A₁…AₙA₀
is not stated in Lean.

The two conditions are what make the triangles turn one way round A₀ and not come round on
themselves, so that they do not overlap. Euclid's ABCD, divided from D by DB, is the figure
with corners D, A, B, C: A and C are on opposite sides of DB, and the two angles at D,
each less than two right angles, are together less than four. -/
theorem Fitted.fan {A₀ A₁ A₂ : Point} {ps : List Point}
    (htri : ∀ s ∈ segments (A₁ :: A₂ :: ps), Triangle A₀ s.1 s.2)
    (hopp : ∀ t ∈ triples (A₁ :: A₂ :: ps), OppositeSidesOf t.1 t.2.2 A₀ t.2.1)
    (hA₀ : Magnitude.sum ((segments (A₁ :: A₂ :: ps)).map fun s => ∠ s.1 A₀ s.2) <
      ∟ + ∟ + (∟ + ∟)) :
    Fitted ((segments (A₁ :: A₂ :: ps)).map fun s => (A₀, s.1, s.2)) := by
  have hA₀A₁A₂ : Triangle A₀ A₁ A₂ := htri (A₁, A₂) (List.mem_cons_self ..)
  cases ps with
  | nil =>
    /- One triangle, A₀A₁A₂, is a figure. -/
    exact Fitted.single hA₀A₁A₂
  | cons C rest =>
    /- Produce A₁A₀ beyond A₀ to A₁', and measure the position of each point round A₀
       from the ray A₀A₁, turning towards A₂'s side (`Fitted.fan.positions`). -/
    obtain ⟨A₁', hA₁A₀A₁'⟩ := produce hA₀A₁A₂.ne₁₂.symm
    obtain ⟨p, hposition⟩ := fan.positions hA₁A₀A₁' hA₀A₁A₂
    /- The induction along the corners. Carry the triangles already fitted, `acc`; the
       last corner reached, B, at position S, the sum of their angles at A₀; and the
       corner P before it. Each point of the earlier triangles is A₀, or at a position
       not greater than S: it lies in the sector swept from the ray A₀A₁ to the ray A₀B,
       which is the closed angle A₁A₀B while S is less than two right angles, the closed
       half-plane on A₂'s side of A₁A₁' when S is two, and that half-plane together
       with the closed angle A₁'A₀B when S is more. P is behind B, and so fixes the side
       of A₀B on which the next corner lies. -/
    have step : ∀ (rest : List Point) (P B : Point)
        (acc : List (Point × Point × Point)) (S : Angle),
        Fitted acc → (A₀, P, B) ∈ acc →
        ((SameSideOf B A₂ A₀ A₁ ∧ SameSideOf P A₁ A₀ B) ∨
          (OnRay B A₀ A₁' ∧ SameSideOf P A₂ A₀ A₁) ∨
          (OppositeSidesOf B A₂ A₀ A₁ ∧ SameSideOf P A₁' A₀ B)) →
        p B = S →
        (∀ t ∈ acc, ∀ Y : Point, OnOrInsideTriangle Y t.1 t.2.1 t.2.2 →
          Y = A₀ ∨ p Y ≤ S) →
        (∀ s ∈ segments (B :: rest), Triangle A₀ s.1 s.2) →
        (∀ t ∈ triples (P :: B :: rest), OppositeSidesOf t.1 t.2.2 A₀ t.2.1) →
        S + Magnitude.sum ((segments (B :: rest)).map fun s => ∠ s.1 A₀ s.2) <
          ∟ + ∟ + (∟ + ∟) →
        Fitted (acc ++ (segments (B :: rest)).map fun s => (A₀, s.1, s.2)) := by
      intro rest
      induction rest with
      | nil =>
        /- No corner is left: the triangles fitted so far are the figure. -/
        intro P B acc S hacc _ _ _ _ _ _ _
        simpa only [segments, List.map, List.append_nil] using hacc
      | cons C rest ih =>
        intro P B acc S hacc hPB hB hpB hregion htri hopp hbound
        have hA₀BC : Triangle A₀ B C := htri (B, C) (List.mem_cons_self ..)
        have hPC : OppositeSidesOf P C A₀ B := hopp (P, B, C) (List.mem_cons_self ..)
        have hremaining : S + ∠ B A₀ C +
            Magnitude.sum ((segments (C :: rest)).map fun s => ∠ s.1 A₀ s.2) <
            ∟ + ∟ + (∟ + ∟) := by
          rw [Tacit.add_assoc]
          exact hbound
        have hSC : S + ∠ B A₀ C < ∟ + ∟ + (∟ + ∟) := fan.part hremaining
        obtain ⟨hpC, hC⟩ := fan.turn hA₁A₀A₁' hposition hB hpB hPC hSC
        /- The new triangle A₀BC meets the earlier ones only along A₀B: a point of
           it off the finite straight line A₀B is at a position greater than S
           (`Fitted.fan.sweep`, where the bound of four right angles does its work),
           while a point of an earlier triangle is A₀ or at a position not greater
           than S. -/
        have hmeet : ∀ Y : Point, OnOrInsideTriangle Y A₀ B C →
            ∀ t ∈ acc, OnOrInsideTriangle Y t.1 t.2.1 t.2.2 → OnFiniteLine Y A₀ B := by
          intro Y hY t ht hYt
          rcases fan.sweep hA₁A₀A₁' hposition hB hpB hPC hA₀BC hSC hY with
            hYB | ⟨hYA₀, hSY, _⟩
          · exact hYB
          · rcases hregion t ht Y hYt with hYA₀' | hYS
            · exact False.elim (hYA₀ hYA₀')
            · exact False.elim (hYS hSY)
        /- So A₀BC is glued to A₀PB along A₀B, C being on the other side of A₀B from
           P by the condition on neighbours. -/
        have hglue : Fitted (acc ++ [(A₀, B, C)]) :=
          Fitted.glue hacc hPB (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
            hPC.symm hmeet
        /- The region grows to the position of C. Old points keep their bound as S
           increases; on A₀B the position is S; the rest of the new triangle is at a
           position not greater than S together with the angle BA₀C. -/
        have hregion' : ∀ t ∈ acc ++ [(A₀, B, C)], ∀ Y : Point,
            OnOrInsideTriangle Y t.1 t.2.1 t.2.2 → Y = A₀ ∨ p Y ≤ S + ∠ B A₀ C := by
          intro t ht Y hY
          rcases List.mem_append.mp ht with ht | ht
          · rcases hregion t ht Y hY with hYA₀ | hYS
            · exact Or.inl hYA₀
            · exact Or.inr (fan.weaken hYS (fan.growth _ _))
          · rw [List.mem_singleton] at ht
            subst t
            rcases fan.sweep hA₁A₀A₁' hposition hB hpB hPC hA₀BC hSC hY with
              hYB | ⟨_, _, hYS⟩
            · rcases hYB with rfl | rfl | hA₀YB
              · exact Or.inl rfl
              · exact Or.inr (hpB ▸ fan.growth S (∠ Y A₀ C))
              · have hpY : p Y = S :=
                  (fan.along hA₁A₀A₁' hposition (Or.imp And.left (Or.imp And.left And.left) hB)
                    (OnRay.of_between hA₀YB)).trans hpB
                exact Or.inr (hpY ▸ fan.growth S (∠ B A₀ C))
            · exact Or.inr hYS
        have hnext := ih B C (acc ++ [(A₀, B, C)]) (S + ∠ B A₀ C) hglue
          (List.mem_append.mpr (Or.inr (List.mem_singleton_self _))) hC hpC hregion'
          (fun s hs => htri s (List.mem_cons_of_mem _ hs))
          (fun t ht => hopp t (List.mem_cons_of_mem _ ht)) hremaining
        simpa only [segments, List.map, List.append_assoc, List.cons_append,
          List.nil_append] using hnext
    /- The first triangle A₀A₁A₂ lies within the closed angle A₁A₀A₂, the region of
       positions not greater than the angle A₁A₀A₂, at which A₂ lies; A₁, on its own
       side of A₀A₂, is behind A₂. -/
    obtain ⟨L, hA₀L, hA₁L⟩ := Postulate1 A₀ A₁ hA₀A₁A₂.ne₁₂
    obtain ⟨M, hA₀M, hA₂M⟩ := Postulate1 A₀ A₂ hA₀A₁A₂.ne₁₃
    have hA₂A₂ : SameSideOf A₂ A₂ A₀ A₁ := SameSideOf.of_line
      hA₀A₁A₂.ne₁₂ hA₀L hA₁L (Tacit.same_side_refl (hA₀A₁A₂.off_line hA₀L hA₁L))
    have hA₁A₁ : SameSideOf A₁ A₁ A₀ A₂ := SameSideOf.of_line
      hA₀A₁A₂.ne₁₃ hA₀M hA₂M (Tacit.same_side_refl (hA₀A₁A₂.acb.off_line hA₀M hA₂M))
    have hfirst : ∀ t ∈ [(A₀, A₁, A₂)], ∀ Y : Point,
        OnOrInsideTriangle Y t.1 t.2.1 t.2.2 → Y = A₀ ∨ p Y ≤ ∠ A₁ A₀ A₂ := by
      intro t ht Y hY
      rw [List.mem_singleton] at ht
      subst t
      rcases fan.within hA₀A₁A₂ hY with hYA₁ | ⟨hYA₂, hYangle⟩
      · rcases hYA₁ with rfl | rfl | hA₀YA₁
        · exact Or.inl rfl
        · rw [(hposition Y).1 (OnRay.self hA₀A₁A₂.ne₁₂)]
          exact Or.inr (Tacit.not_lt_zero _)
        · rw [(hposition Y).1 (OnRay.of_between hA₀YA₁)]
          exact Or.inr (Tacit.not_lt_zero _)
      · rw [(hposition Y).2.1 hYA₂]
        exact Or.inr hYangle
    exact step (C :: rest) A₁ A₂ [(A₀, A₁, A₂)] (∠ A₁ A₀ A₂)
      (Fitted.single hA₀A₁A₂) (List.mem_singleton_self _) (Or.inl ⟨hA₂A₂, hA₁A₁⟩)
      ((hposition A₂).2.1 hA₂A₂) hfirst
      (fun s hs => htri s (List.mem_cons_of_mem _ hs)) hopp hA₀

end Elements

namespace Elements.BookI

open Tacit

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

/-- The check: the statement of `Prop45`, for the two triangles ABD, DBC, follows from
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
