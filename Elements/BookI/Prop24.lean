import Elements.Figure.Basics
import Elements.BookI.Prop04
import Elements.BookI.Prop05
import Elements.BookI.Prop16
import Elements.BookI.Prop19
import Elements.BookI.Prop21
import Elements.BookI.Prop23

/-!
# Book I, Proposition 24

Euclid's text, in Heath's translation: [`heath/I/24.md`](../../heath/I/24.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid draws one figure, with `F` below `EG`, and leaves the others to the reader.
Lean can't, so `Prop24.cases` sorts out where `F` can fall: on `EG`, within the
triangle `DEG`, or beyond `EG` as in Euclid's figure. The first two are the cases
Proclus supplies, and Heath reports (vol. 1, p. 297): when `F` is on `EG`, `EF` is a
part of `EG`; when it is within the triangle, I.21 does it.
-/

namespace Elements.BookI

open Tacit

/-! ## What Euclid reads off the figure -/

/-- "Let DG be made equal to DF." Euclid cites nothing here. On the ray from `D`
through any point `P` there is a point `G` with `DG` equal to `DF`: describe the circle
with centre `D` and distance `DF` (Post. 3); the straight line `DP`, which passes
through its centre, cuts it on `P`'s side of `D` (System E, Intersections 5, with a
point `Q` set out on the other side); and `DG` is a radius [Def. 15]. -/
theorem Prop24.made_equal {D F P : Point} (hDF : D ≠ F) (hDP : D ≠ P) :
    ∃ G : Point, OnRay G D P ∧ ‖D G‖ = ‖D F‖ := by
  obtain ⟨α, hD_α, hF_α⟩ := Postulate3 D F hDF
  obtain ⟨L, hD_L, hP_L⟩ := Postulate1 D P hDP
  /- A point `Q` behind `D`, so that the circle is cut on `P`'s side. -/
  obtain ⟨Q, hPDQ⟩ := produce hDP.symm
  have hQ_L : OnLine Q L := on_line_of_between hPDQ hP_L hD_L
  obtain ⟨G, hG_α, hG_L, hGDQ⟩ :=
    line_circle_beyond (centre_inside hD_α) hD_L hQ_L (ne_of_between (between_symm hPDQ))
  refine ⟨G, ⟨hDP, ne_of_between hGDQ, ⟨L, hD_L, hP_L, hG_L⟩, fun hGDP => ?_⟩,
    Definition15 hD_α hG_α hF_α⟩
  /- `G` and `P` are both on the far side of `D` from `Q`, so `D` is not between them. -/
  exact not_between_of_between_between hGDQ hGDP (between_symm hPDQ)

/-- A point `G` on the ray from `D` through `P` is on the same side of `DE` as `P`:
the ray leaves `DE` at `D` and never crosses it again (System E, Pasch 4). -/
theorem Prop24.side {D E F G P : Point} (hG : OnRay G D P) (hP : SameSideOf P F D E) :
    SameSideOf G F D E := by
  have hDE : D ≠ E := hP.1
  obtain ⟨L, hD_L, hE_L⟩ := Postulate1 D E hDE
  have hPF : SameSide P F L := hP.sameSide hD_L hE_L
  have hP_L : ¬ OnLine P L := not_on_line_of_same_side hPF
  obtain ⟨-, hGD, ⟨M, hD_M, hP_M, hG_M⟩, hGDP⟩ := hG
  have hLM : L ≠ M := fun e => hP_L (e ▸ hP_M)
  have hGP : SameSide G P L := by
    by_cases hGP : G = P
    · subst hGP
      exact same_side_refl hP_L
    · /- Were `G` and `P` on opposite sides of `DE`, `D` would lie between them. -/
      refine Classical.byContradiction fun hs => hGDP ?_
      exact pasch4 hLM hD_L hD_M hG_M hP_M hGP hGD (fun e => hP_L (e ▸ hD_L)) hs
  exact SameSideOf.of_line hDE hD_L hE_L (same_side_trans (same_side_symm hGP) hPF)

/-- `F` lies within the angle `EDG`. Both are on one side of `DE`, and the angle `EDF`
is the less. If `F` were on `DG`, the angle `EDF` would be the angle `EDG`
(`angle_onRay_right`); if it were beyond `DG`, then `G` would lie within the angle
`EDF` (System E, Triple incidence 2), and the angle `EDG` would be a part of it
(`Prop16.part`), so the greater would be less than the less. -/
theorem Prop24.within {D E F G : Point} (hGF : SameSideOf G F D E) (h : ∠ E D F < ∠ E D G) :
    SameSideOf F E D G := by
  have hDE : D ≠ E := hGF.1
  obtain ⟨L, hD_L, hE_L⟩ := Postulate1 D E hDE
  have hGF_L : SameSide G F L := hGF.sameSide hD_L hE_L
  have hG_L : ¬ OnLine G L := not_on_line_of_same_side hGF_L
  have hF_L : ¬ OnLine F L := not_on_line_of_same_side (same_side_symm hGF_L)
  have hDG : D ≠ G := fun e => hG_L (e ▸ hD_L)
  have hDF : D ≠ F := fun e => hF_L (e ▸ hD_L)
  obtain ⟨M, hD_M, hG_M⟩ := Postulate1 D G hDG
  refine SameSideOf.of_line hDG hD_M hG_M (Classical.byContradiction fun hs => ?_)
  by_cases hF_M : OnLine F M
  · /- `F` on `DG`, and on `G`'s side of `D`, since both are on one side of `DE`. -/
    have hF_ray : OnRay F D G :=
      ⟨hDG, hDF.symm, ⟨M, hD_M, hG_M, hF_M⟩, fun hb => pasch3 hb hD_L (same_side_symm hGF_L)⟩
    rw [angle_onRay_right hF_ray hDE.symm] at h
    exact lt_irrefl _ h
  · obtain ⟨N, hD_N, hF_N⟩ := Postulate1 D F hDF
    have hEG_N : SameSide E G N :=
      triple_incidence2 hD_L hD_M hD_N hE_L hG_M hF_N hGF_L
        (fun h' => hs (same_side_symm h')) hF_M hDE.symm
    obtain ⟨hadd, hpos⟩ :=
      Prop16.part hGF (SameSideOf.of_line hDF hD_N hF_N (same_side_symm hEG_N))
    have hlt := CommonNotion5 (a := ∠ E D G) hpos
    rw [← hadd] at hlt
    exact lt_irrefl _ (lt_trans hlt h)

/-- Where `F` falls. Since `F` lies within the angle `EDG`, the straight line `DF`,
drawn on, crosses `EG` at some point `X` (`crossbar`). Then either `F` is `X`, and lies
on `EG`; or `F` is short of `X`, within the triangle `DEG`; or `F` is beyond `X`, on
the far side of `EG` from `D`, and `EFG` is a triangle. The last is Euclid's figure. -/
theorem Prop24.cases {D E F G : Point} (hGF : SameSideOf G F D E) (hFE : SameSideOf F E D G) :
    Between E F G ∨ InsideTriangle F G D E ∨
      ∃ X : Point, Between E X G ∧ Between D X F ∧ Triangle E G F := by
  obtain ⟨X, hEXG, hX⟩ := crossbar hGF.symm hFE
  have hDEG : Triangle D E G := hGF.triangle
  obtain ⟨N, hE_N, hG_N⟩ := Postulate1 E G hDEG.ne₂₃
  have hX_N : OnLine X N := on_line_of_between_ends hEXG hE_N hG_N
  have hD_N : ¬ OnLine D N := hDEG.bca.off_line hE_N hG_N
  by_cases hXF : X = F
  · subst hXF
    exact Or.inl hEXG
  obtain ⟨hDF, hXD, ⟨L, hD_L, hF_L, hX_L⟩, hXDF⟩ := hX
  /- `F` is off `EG`: otherwise `DF` and `EG` would be one straight line, through `D`. -/
  have hF_N : ¬ OnLine F N := fun hF_N => hD_N (line_unique hXF hX_L hF_L hX_N hF_N ▸ hD_L)
  rcases between_cases hXD.symm hXF hDF hD_L hX_L hF_L with hDXF | hb | hDFX
  · exact Or.inr (Or.inr ⟨X, hEXG, hDXF, Triangle.of_line hE_N hG_N hDEG.ne₂₃ hF_N⟩)
  · exact absurd hb hXDF
  · /- `F` is on `D`'s side of `EG` (Pasch 2), and within the angle `EDG`. -/
    exact Or.inr (Or.inl ⟨hGF.symm,
      SameSideOf.of_line hDEG.ne₂₃ hE_N hG_N (pasch2 (between_symm hDFX) hX_N hF_N), hFE.swap⟩)

/-- The part is less than the whole, for angles: if `R` lies between `P` and `Q`, and
`V` is off `PQ`, the angle `RVQ` is less than the angle `PVQ`, for `PVQ` is made up of
`PVR` and `RVQ` (`angle_add_of_between`), and `PVR` is something, since `R` is off
`VP` (System E, Diagram-angle 1). [C.N. 5] -/
theorem Prop24.part {V P Q R : Point} (hPQV : Triangle P Q V) (h : Between P R Q) :
    ∠ R V Q < ∠ P V Q := by
  rw [angle_add_of_between hPQV h, add_comm]
  apply CommonNotion5
  obtain ⟨N, hP_N, hQ_N⟩ := Postulate1 P Q (ne_of_between_ends h)
  have hV_N : ¬ OnLine V N := hPQV.off_line hP_N hQ_N
  have hR_N : OnLine R N := on_line_of_between_ends h hP_N hQ_N
  have hVP : V ≠ P := fun e => hV_N (e ▸ hP_N)
  have hVR : V ≠ R := fun e => hV_N (e ▸ hR_N)
  obtain ⟨L, hV_L, hP_L⟩ := Postulate1 V P hVP
  refine Magnitude.pos_of_ne_zero fun h0 => ?_
  have hR_L : OnLine R L := (same_ray_of_angle_eq_zero hVP hVR hV_L hP_L h0).1
  exact hV_N (line_unique (ne_of_between h) hP_L hR_L hP_N hR_N ▸ hV_L)

/-- If `a` and `b` together are less than `a` and `c` together, then `b` is less than
`c`: take the common `a` away. Otherwise `c` would be equal to `b` or less, and adding
`a` to each would keep it so (System E §3.5, the laws of magnitudes). -/
theorem Prop24.less {k : Kind} {a b c : Magnitude k} (h : a + b < a + c) : b < c := by
  rcases lt_trichotomy b c with h' | h' | h'
  · exact h'
  · subst h'
    exact absurd h (lt_irrefl _)
  · have h'' := add_lt_add_right a h'
    rw [add_comm c a, add_comm b a] at h''
    exact absurd (lt_trans h h'') (lt_irrefl _)

/-- If two triangles have the two sides equal to two sides respectively, but have the one of the
angles contained by the equal straight lines greater than the other, they will also have the
base greater than the base. -/
theorem Prop24 {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
    (hAB : ‖A B‖ = ‖D E‖) (hAC : ‖A C‖ = ‖D F‖) (h : ∠ E D F < ∠ B A C) :
    ‖E F‖ < ‖B C‖ := by
  -- Let ABC, DEF be two triangles having the two sides AB, AC equal to the two sides DE, DF
  -- respectively, namely AB to DE, and AC to DF, and let the angle at A be greater than the
  -- angle at D;
  have hDE : D ≠ E := hDEF.ne₁₂
  have hDF : D ≠ F := hDEF.ne₁₃
  -- I say that the base BC is also greater than the base EF.
  -- For, since the angle BAC is greater than the angle EDF, let there be constructed, on the
  -- straight line DE, and at the point D on it, the angle EDG equal to the angle BAC; [I. 23]
  /- I.23 builds the angle at `D` with one arm along the ray from `D` through `E` (it
     passes through a point `E₁` of that ray) and the other through a point `G₁` on
     whichever side of `DE` we ask for. We ask for `F`'s side, as in Euclid's figure. -/
  obtain ⟨E₁, G₁, hE₁, hG₁F, hE₁DG₁⟩ := Prop23 hDE hABC.bac hDEF
  -- let DG be made equal to either of the two straight lines AC, DF, and let EG, FG be joined.
  /- `G` is laid along the arm `DG₁` with a circle about `D` (`Prop24.made_equal`). It is
     on `F`'s side of `DE`, as `G₁` is (`Prop24.side`), and the angle `EDG` is the angle
     `E₁DG₁`, its arms being the same rays (`angle_eq_of_onRay`). -/
  obtain ⟨G, hG, hDG_DF⟩ := Prop24.made_equal hDF hG₁F.triangle.ne₁₃
  have hGF : SameSideOf G F D E := Prop24.side hG hG₁F
  have hEDG : ∠ E D G = ∠ B A C := (angle_eq_of_onRay hE₁.symm hG).trans hE₁DG₁
  /- Joining needs different points. `G` is off `DE`; and `F`, the angle `EDF` being the
     less, lies within the angle `EDG` (`Prop24.within`), so it is off `DG`. -/
  have hFE : SameSideOf F E D G := Prop24.within hGF (by rw [hEDG]; exact h)
  have hDEG : Triangle D E G := hGF.triangle
  have hDFG : Triangle D F G := hFE.triangle.acb
  -- Then, since AB is equal to DE, and AC to DG,
  have hAC_DG : ‖A C‖ = ‖D G‖ := hAC.trans hDG_DF.symm
  -- the two sides BA, AC are equal to the two sides ED, DG, respectively;
  -- and the angle BAC is equal to the angle EDG;
  have hBAC : ∠ B A C = ∠ E D G := hEDG.symm
  -- therefore the base BC is equal to the base EG. [I. 4]
  have hBC_EG : ‖B C‖ = ‖E G‖ := (Prop4 hABC hDEG hAB hAC_DG hBAC).1
  -- Again, since DF is equal to DG,
  have hDF_DG : ‖D F‖ = ‖D G‖ := hDG_DF.symm
  -- the angle DGF is also equal to the angle DFG; [I. 5]
  /- Our I.5 is stated as Euclid states it, with the equal sides produced, so `DF` and
     `DG` are produced to `K` and `H` in order to cite it. Only the angles at the base
     are used. -/
  obtain ⟨K, hDFK⟩ := produce hDF
  obtain ⟨H, hDGH⟩ := produce hDEG.ne₁₃
  have hDGF : ∠ D G F = ∠ D F G := (Prop5 hDFG hDF_DG hDFK hDGH).1.symm
  /- Euclid's figure has `F` beyond `EG`. Lean must also take the two cases he leaves to
     the reader (`Prop24.cases`), and it takes them as Proclus does. -/
  have hEF_EG : ‖E F‖ < ‖E G‖ := by
    rcases Prop24.cases hGF hFE with hEFG | hF | ⟨X, hEXG, hDXF, hEGF⟩
    · /- `F` falls on `EG`: "it is then obvious that EG is greater than EF", the whole
         than the part. -/
      exact len_lt_of_between hEFG
    · /- `F` falls within the triangle `DEG`: "by I. 21, DF, FE are together less than
         DG, GE. But DF is equal to DG; therefore EF is less than EG." -/
      have hI21 : ‖D F‖ + ‖F E‖ < ‖D G‖ + ‖G E‖ := (Prop21 hDEG.cab hF).1
      rw [hDF_DG] at hI21
      rw [len_symm E F, len_symm E G]
      exact Prop24.less hI21
    · /- Euclid's figure: `F` beyond `EG`, which `DF` crosses at `X`. -/
      have hFG : F ≠ G := hDFG.ne₂₃
      have hEG : E ≠ G := hDEG.ne₂₃
      -- therefore the angle DFG is greater than the angle EGF.
      /- The angle `EGF` is the angle `XGF`, a part of the angle `DGF`, since `X` lies
         between `D` and `F` (`Prop24.part`). -/
      have hEGF_DGF : ∠ E G F < ∠ D G F := by
        rw [← angle_onRay_left (OnRay.of_between (between_symm hEXG)) hFG]
        exact Prop24.part hDFG hDXF
      have hEGF_DFG : ∠ E G F < ∠ D F G := by
        rw [← hDGF]
        exact hEGF_DGF
      -- Therefore the angle EFG is much greater than the angle EGF.
      /- The angle `DFG` is the angle `XFG`, a part of the angle `EFG`, since `X` lies
         between `E` and `G`. -/
      have hDFG_EFG : ∠ D F G < ∠ E F G := by
        rw [← angle_onRay_left (OnRay.of_between (between_symm hDXF)) hFG.symm]
        exact Prop24.part hEGF hEXG
      have hmuch : ∠ E G F < ∠ E F G := lt_trans hEGF_DFG hDFG_EFG
      -- And, since EFG is a triangle having the angle EFG greater than the angle EGF,
      have hEFG : Triangle E F G := hEGF.acb
      -- and the greater angle is subtended by the greater side, [I. 19]
      -- the side EG is also greater than EF.
      exact Prop19 hEFG (by rw [angle_symm hFG hEG]; exact hmuch)
  -- But EG is equal to BC.
  rw [hBC_EG]
  -- Therefore BC is also greater than EF.
  exact hEF_EG
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookI
