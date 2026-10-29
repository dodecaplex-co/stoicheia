import Elements.Figure.Basics
import Elements.BookI.Prop04
import Elements.BookI.Prop05
import Elements.BookI.Helpers
import Elements.BookI.Prop16
import Elements.BookI.Prop18
import Elements.BookI.Prop19
import Elements.BookI.Prop23

/-!
# Book I, Proposition 24

Euclid's text, in Heath's translation: [`heath/I/24.md`](../../heath/I/24.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid draws one figure, with F below EG, and leaves the other placings of F to the
reader. Robert Simson added a sentence that makes it the only figure, "Of the two
sides DE, DF let DE be the side which is not greater than the other" (Heath, vol. 1,
p. 297). Heath leaves it out of the text, and adds: "If however after all we prefer
to insert Simson's words and avoid the latter two cases, the proof is not complete
unless we show that, with his assumption, F must, in the figure of the proposition,
fall *below* EG" (vol. 1, pp. 297–298).

Our proof inserts Simson's words, and shows it. The statement is the same with B and
C, and E and F, exchanged, so Euclid's sentences stand inside one step that takes DE
not greater than DF, and the end applies it to the names as given or exchanged.
`Prop24.below` then puts F below EG, by the lemma Heath gives "by the method employed
by Pfleiderer, Lardner, and Todhunter" (vol. 1, p. 298), from I.16, I.18 and I.19;
and Euclid's own comparisons, each the whole greater than the part, carry every
placing of F. Heath prefers to leave Simson's words out, and with them the other two
cases, which Proclus supplies: F on EG, and F within the triangle DEG, by I.21. The
mishnah tells them.
-/

namespace Elements.BookI

open Tacit

/-! ## What Euclid reads off the figure -/

/-- F lies within the angle EDG. Both are on one side of DE, and the angle EDF
is the less. If F were on DG, the angle EDF would be the angle EDG
(`angle_onRay_right`); if it were beyond DG, then G would lie within the angle
EDF (System E, Triple incidence 2), and the angle EDG would be a part of it
(`angle_add_of_within`, with the angle GDF something, `Triangle.angle_pos`), so the
greater would be less than the less. -/
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
  · /- Were F on DG, it would lie on G's side of D, since both are on one side of DE. -/
    have hF_ray : OnRay F D G := OnRay.of_sameSideOf hGF.symm ⟨M, hD_M, hG_M, hF_M⟩ hDF.symm
    rw [angle_onRay_right hF_ray hDE.symm] at h
    exact lt_irrefl _ h
  · obtain ⟨N, hD_N, hF_N⟩ := Postulate1 D F hDF
    have hEG_N : SameSide E G N :=
      triple_incidence2 hD_L hD_M hD_N hE_L hG_M hF_N hGF_L
        (fun h' => hs (same_side_symm h')) hF_M hDE.symm
    have hGE : SameSideOf G E D F := SameSideOf.of_line hDF hD_N hF_N (same_side_symm hEG_N)
    have hlt := CommonNotion5 (a := ∠ E D G) hGE.triangle.cab.angle_pos
    rw [← angle_add_of_within hGF hGE] at hlt
    exact lt_irrefl _ (lt_trans hlt h)

/-- F falls below EG, on the far side of it from D, when DE is not greater than DG:
DF crosses EG at a point H between D and F, and EGF is a triangle. Euclid's figure
has F there, and his comparisons need it. This is the lemma Heath gives "by the method
employed by Pfleiderer, Lardner, and Todhunter" (vol. 1, p. 298). F lies within the
angle EDG, so DF, produced if need be, crosses EG at a point H (`crossbar`). The angle
DHG, outside the triangle DEH, is greater than the angle DEG [I. 16]; the angle DEG is
not less than the angle DGE [I. 18], or equal to it when DE is equal to DG [I. 5]; so
the angle DHG is greater than the angle DGH, and DH is less than DG [I. 19], which is
DF. So H, on the ray from D through F, is nearer D than F is. -/
theorem Prop24.below {D E F G : Point} (hGF : SameSideOf G F D E) (hFE : SameSideOf F E D G)
    (hDF_DG : ‖D F‖ = ‖D G‖) (hDE_DG : ‖D E‖ ≤ ‖D G‖) :
    ∃ H : Point, Between E H G ∧ Between D H F ∧ Triangle E G F := by
  have hDEG : Triangle D E G := hGF.triangle
  obtain ⟨N, hE_N, hG_N⟩ := Postulate1 E G hDEG.ne₂₃
  have hD_N : ¬ OnLine D N := hDEG.bca.off_line hE_N hG_N
  /- DF, produced if need be, crosses EG at H. -/
  obtain ⟨H, hEHG, hH⟩ := crossbar hGF.symm hFE
  have hH_N : OnLine H N := on_line_of_between_ends hEHG hE_N hG_N
  have hEH : E ≠ H := ne_of_between hEHG
  have hHG : H ≠ G := (ne_of_between (between_symm hEHG)).symm
  have hDEH : Triangle D E H := (Triangle.of_line hE_N hH_N hEH hD_N).cab
  have hDHG : Triangle D H G := (Triangle.of_line hH_N hG_N hHG hD_N).cab
  /- The angle DHG is greater than the angle DEH [I. 16], which is the angle DEG,
     since H is on EG. -/
  have hDEG_DHG : ∠ D E G < ∠ D H G := by
    have h16 : ∠ H E D < ∠ D H G := (Prop16 hDEH hEHG).1
    rwa [← angle_symm hDEG.ne₁₂ hEH.symm,
      angle_onRay_right (OnRay.of_between hEHG) hDEG.ne₁₂] at h16
  /- The angle DEG is not less than the angle DGE: greater, if DE is less than DG
     [I. 18], and equal, if DE is equal to DG [I. 5]. -/
  have hDGE_DEG : ∠ D G E ≤ ∠ D E G := by
    rcases lt_trichotomy ‖D E‖ ‖D G‖ with hlt | heq | hgt
    · have h18 : ∠ E G D < ∠ D E G := Prop18 hDEG hlt
      rw [angle_symm hDEG.ne₂₃ hDEG.ne₁₃] at h18
      exact fun h' => lt_irrefl _ (lt_trans h18 h')
    · rw [Prop5.base hDEG heq]
      exact lt_irrefl _
    · exact absurd hgt hDE_DG
  /- So the angle DHG is greater than the angle DGH, which is the angle DGE, since H
     is on GE. -/
  have hDGH_DHG : ∠ D G H < ∠ D H G := by
    rw [angle_onRay_right (OnRay.of_between (between_symm hEHG)) hDEG.ne₁₃]
    rcases lt_trichotomy (∠ D G E) (∠ D E G) with hl | he | hg
    · exact lt_trans hl hDEG_DHG
    · rw [he]
      exact hDEG_DHG
    · exact absurd hg hDGE_DEG
  /- Hence DH is less than DG [I. 19], and so less than DF. -/
  have hDH_DG : ‖D H‖ < ‖D G‖ :=
    Prop19 hDHG (by rw [angle_symm hHG hDEG.ne₁₃]; exact hDGH_DHG)
  have hDH_DF : ‖D H‖ < ‖D F‖ := by
    rw [hDF_DG]
    exact hDH_DG
  /- H and F are on one ray from D, and H is the nearer, so it is between D and F
     (`OnRay.between_of_len_lt`). Then F is off EG, for H is on it and D is not. -/
  have hDHF : Between D H F := hH.between_of_len_lt (OnRay.self hH.1) hDH_DF
  have hF_N : ¬ OnLine F N := fun hF_N =>
    hD_N (on_line_of_between (between_symm hDHF) hF_N hH_N)
  exact ⟨H, hEHG, hDHF, Triangle.of_line hE_N hG_N hDEG.ne₂₃ hF_N⟩

/-- Where does F fall? Since F lies within the angle EDG, the straight line DF,
drawn on, crosses EG at some point X (`crossbar`). Then either F is X, and lies
on EG; or F is short of X, within the triangle DEG; or F is beyond X, on
the far side of EG from D, and EFG is a triangle. The last is Euclid's figure.
I.24's proof no longer uses this: with Simson's words it needs only the last
placing, which `Prop24.below` gives. It stays, deprecated, for one release. -/
@[deprecated "I.24's proof no longer uses it; Prop24.below gives the placing it needs"
  (since := "2026-10-29")]
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
  /- F is off EG: otherwise DF and EG would be one straight line, through D. -/
  have hF_N : ¬ OnLine F N := fun hF_N => hD_N (line_unique hXF hX_L hF_L hX_N hF_N ▸ hD_L)
  rcases between_cases hXD.symm hXF hDF hD_L hX_L hF_L with hDXF | hb | hDFX
  · exact Or.inr (Or.inr ⟨X, hEXG, hDXF, Triangle.of_line hE_N hG_N hDEG.ne₂₃ hF_N⟩)
  · exact absurd hb hXDF
  · /- F is on D's side of EG (Pasch 2), and within the angle EDG. -/
    exact Or.inr (Or.inl ⟨hGF.symm,
      SameSideOf.of_line hDEG.ne₂₃ hE_N hG_N (pasch2 (between_symm hDFX) hX_N hF_N), hFE.swap⟩)

/-- If two triangles have the two sides equal to two sides respectively, but have the one of the
angles contained by the equal straight lines greater than the other, they will also have the
base greater than the base. -/
theorem Prop24 {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
    (hAB : ‖A B‖ = ‖D E‖) (hAC : ‖A C‖ = ‖D F‖) (h : ∠ E D F < ∠ B A C) :
    ‖E F‖ < ‖B C‖ := by
  -- Let ABC, DEF be two triangles having the two sides AB, AC equal to the two sides DE, DF
  -- respectively, namely AB to DE, and AC to DF, and let the angle at A be greater than the
  -- angle at D;
  -- I say that the base BC is also greater than the base EF.
  /- Simson's words, "Of the two sides DE, DF let DE be the side which is not greater
     than the other" (Heath, vol. 1, p. 297), are not Euclid's. With them F falls below
     EG, as in Euclid's figure (`Prop24.below`). So Euclid's sentences stand inside one
     step, `simson`, which proves his conclusion for any two triangles named so that DE
     is not greater than DF; at the end, it is applied to the names as given, or with
     them exchanged. -/
  have simson : ∀ {B C E F : Point}, Triangle A B C → Triangle D E F → ‖A B‖ = ‖D E‖ →
      ‖A C‖ = ‖D F‖ → ∠ E D F < ∠ B A C → ‖D E‖ ≤ ‖D F‖ → ‖E F‖ < ‖B C‖ := by
    intro B C E F hABC hDEF hAB hAC h hDE_DF
    -- For, since the angle BAC is greater than the angle EDF, let there be constructed, on the
    -- straight line DE, and at the point D on it, the angle EDG equal to the angle BAC; [I. 23]
    /- I.23 builds the angle at D with one arm along the ray from D through E (it
       passes through a point E₁ of that ray) and the other through a point G₁ on
       whichever side of DE we ask for. We ask for F's side, as in Euclid's figure. -/
    have hDE : D ≠ E := hDEF.ne₁₂
    obtain ⟨G₁, E₁, hE₁, hG₁F, hG₁DE₁⟩ := Prop23 hDE hABC.bac hDEF
    -- let DG be made equal to either of the two straight lines AC, DF, and let EG, FG be joined.
    /- G is laid along the arm DG₁ with a circle about D (`OnRay.exists_len_eq`). It is
       on F's side of DE, as G₁ is (`SameSideOf.of_onRay`), and the angle EDG is the angle
       E₁DG₁, its arms being the same rays (`angle_eq_of_onRay`). -/
    have hDF : D ≠ F := hDEF.ne₁₃
    obtain ⟨G, hG, hDG_DF⟩ := OnRay.exists_len_eq hDF hG₁F.triangle.ne₁₃
    have hGF : SameSideOf G F D E := SameSideOf.of_onRay hG hG₁F
    have hEDG : ∠ E D G = ∠ B A C :=
      (angle_eq_of_onRay hE₁.symm hG).trans
        ((angle_symm hE₁.2.1 hG₁F.triangle.ne₁₃.symm).trans hG₁DE₁)
    /- Joining needs different points. G is off DE; and F, the angle EDF being the
       less, lies within the angle EDG (`Prop24.within`), so it is off DG. -/
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
    have hDGF : ∠ D G F = ∠ D F G := (Prop5.base hDFG hDF_DG).symm
    /- Euclid's figure has F below EG, and his comparisons need it there. DE is not
       greater than DF, which is DG, so F is there (`Prop24.below`): DF crosses EG at a
       point H between D and F. -/
    obtain ⟨H, hEHG, hDHF, hEGF⟩ :=
      Prop24.below hGF hFE hDF_DG (by rw [← hDF_DG]; exact hDE_DF)
    have hFG : F ≠ G := hDFG.ne₂₃
    have hEG : E ≠ G := hDEG.ne₂₃
    -- therefore the angle DFG is greater than the angle EGF.
    /- The angle EGF is the angle HGF, a part of the angle DGF, since H lies
       between D and F (`angle_lt_of_between`). -/
    have hEGF_DGF : ∠ E G F < ∠ D G F := by
      rw [← angle_onRay_left (OnRay.of_between (between_symm hEHG)) hFG]
      exact angle_lt_of_between hDFG hDHF
    have hEGF_DFG : ∠ E G F < ∠ D F G := by
      rw [← hDGF]
      exact hEGF_DGF
    -- Therefore the angle EFG is much greater than the angle EGF.
    /- The angle DFG is the angle HFG, a part of the angle EFG, since H lies between
       E and G. -/
    have hDFG_EFG : ∠ D F G < ∠ E F G := by
      rw [← angle_onRay_left (OnRay.of_between (between_symm hDHF)) hFG.symm]
      exact angle_lt_of_between hEGF hEHG
    have hmuch : ∠ E G F < ∠ E F G := lt_trans hEGF_DFG hDFG_EFG
    -- And, since EFG is a triangle having the angle EFG greater than the angle EGF,
    have hEFG : Triangle E F G := hEGF.acb
    -- and the greater angle is subtended by the greater side, [I. 19]
    -- the side EG is also greater than EF.
    have hEF_EG : ‖E F‖ < ‖E G‖ := Prop19 hEFG (by rw [angle_symm hFG hEG]; exact hmuch)
    -- But EG is equal to BC.
    rw [hBC_EG]
    -- Therefore BC is also greater than EF.
    exact hEF_EG
  /- Simson's words choose the names, and the statement does not mind the choice:
     exchange B with C and E with F, and the hypotheses AB equal to DE and AC to DF
     exchange, the angles FDE and CAB are the angles EDF and BAC (`angle_symm`), and
     the bases FE and CB are EF and BC (`len_symm`). So when DE is greater than DF,
     `simson` applies to the triangles ACB and DFE. -/
  by_cases hDE_DF : ‖D E‖ ≤ ‖D F‖
  · exact simson hABC hDEF hAB hAC h hDE_DF
  · have hDF_DE : ‖D F‖ ≤ ‖D E‖ := fun hlt => hDE_DF fun hgt => lt_irrefl _ (lt_trans hlt hgt)
    have hFDE : ∠ F D E < ∠ C A B := by
      rw [angle_symm hDEF.ne₁₃.symm hDEF.ne₁₂.symm, angle_symm hABC.ne₁₃.symm hABC.ne₁₂.symm]
      exact h
    rw [len_symm E F, len_symm B C]
    exact simson hABC.acb hDEF.acb hAC hAB hFDE hDF_DE
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookI
