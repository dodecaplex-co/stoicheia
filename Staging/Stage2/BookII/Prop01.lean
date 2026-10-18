import Staging.Stage2.Sums

/-!
# Staging: II.1 for any number of segments

Brief 0006, stage 2. Companions of `Elements.BookII.Prop1`, which stays as Euclid's worked
configuration: BC cut at the two points D, E into three segments. His enunciation says "any
number of segments whatever". `Prop1.two` is one cut, by II.1's own construction, and
`Prop1.general` any number, by repeating it. They move into `Elements/BookII/Prop01.lean`
when proved, as "II.1 two" and "II.1 general".
-/

namespace Elements.BookII

open Tacit

/-- **II.1, one cut** (companion of II.1). If the straight line BC is cut at D, the
rectangle contained by A₁A₂ and BC is equal to the rectangles contained by A₁A₂ and each
of BD, DC. II.1's construction, with one parallel drawn through D. The uncut straight line
A₁A₂ may be nothing, and then every rectangle is nothing. -/
theorem Prop1.two {A₁ A₂ B C D : Point} (h : Between B D C) :
    rect A₁ A₂ B C = rect A₁ A₂ B D + rect A₁ A₂ D C := by
  /- If A₁A₂ is nothing, all three rectangles are nothing. -/
  by_cases hA : A₁ = A₂
  · subst A₂
    simp only [rect_self_left, add_zero]
  have hBC : B ≠ C := ne_of_between_ends h
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hBC
  have hD_BC : OnLine D BC := on_line_of_between_ends h hB_BC hC_BC
  /- Draw BF at right angles to BC by I.11. -/
  obtain ⟨Q, hQ, -⟩ := exists_off_line hBC []
  obtain ⟨F, hFQ, hright⟩ := BookI.Prop11 hBC ⟨BC, hB_BC, hC_BC, hB_BC⟩ hQ
  have hCBF : ∠ C B F = ∟ := hright C ⟨BC, hB_BC, hC_BC, hC_BC⟩ hBC.symm
  /- Place A₁A₂ at B by I.2 and produce BF far enough along its ray.
     I.3 then cuts off BG equal to A₁A₂. -/
  obtain ⟨P, hP⟩ := BookI.Prop2 B A₁ A₂ hA
  have hBP : B ≠ P := ne_of_len_eq hP hA
  have hBF : B ≠ F := hFQ.triangle.ne₁₃
  obtain ⟨Y, hFBY⟩ := produce hBF.symm
  obtain ⟨X, hYBX, hlt⟩ := produce_longer (ne_of_between (between_symm hFBY)) hBP
  have hX : OnRay X B F := OnRay.of_between_between (between_symm hFBY) hYBX
  obtain ⟨G, hBGX, hBG⟩ := BookI.Prop3 hA (hP ▸ hlt)
  have hCBG : ∠ C B G = ∟ := by
    rw [angle_onRay_right (OnRay.of_between hBGX) hBC.symm, angle_onRay_right hX hBC.symm]
    exact hCBF
  have hGQ : SameSideOf G Q B C :=
    SameSideOf.of_onRay (OnRay.of_between hBGX) (SameSideOf.of_onRay hX hFQ)
  have hG_BC : ¬ OnLine G BC := not_on_line_of_same_side (hGQ.sameSide hB_BC hC_BC)
  /- Draw GH parallel to BC, and DK and CH parallel to BG, by I.31. -/
  obtain ⟨GH, hG_GH, hGH_BC⟩ := BookI.Prop31.line hG_BC
  obtain ⟨K, hK_GH, hGBDK⟩ :=
    BookI.Prop31.parallelogram hGH_BC hG_GH hB_BC hD_BC (ne_of_between h)
  obtain ⟨H, hH_GH, hGBCH⟩ := BookI.Prop31.parallelogram hGH_BC hG_GH hB_BC hC_BC hBC
  obtain ⟨BG, hB_BG, hG_BG⟩ := Postulate1 B G (ne_of_between hBGX)
  obtain ⟨DK, hD_DK, hK_DK⟩ := Postulate1 D K hGBDK.1.2.1
  obtain ⟨CH, hC_CH, hH_CH⟩ := Postulate1 C H hGBCH.1.2.1
  have hDK_BG : Parallel DK BG := (hGBDK.1.parallel hG_BG hB_BG hD_DK hK_DK).symm
  have hCH_BG : Parallel CH BG := (hGBCH.1.parallel hG_BG hB_BG hC_CH hH_CH).symm
  have hDC : D ≠ C := (ne_of_between (between_symm h)).symm
  /- DK meets BC only at D. It is distinct from CH, and I.30 makes them parallel. -/
  have hC_DK : ¬ OnLine C DK :=
    hGH_BC.symm.off_transversal hD_BC hK_GH hD_DK hK_DK hC_BC hDC.symm
  have hDK_CH : Parallel DK CH :=
    BookI.Prop30.parallel hDK_BG hCH_BG (fun e => hC_DK (e.symm ▸ hC_CH))
  /- The parallels put K between G and H, so BH divides into BK and DH. -/
  have hGKH : Between G K H := Parallel.between hDK_BG.symm hDK_CH.symm hB_BG hD_DK hC_CH
    h hG_BG hK_DK hH_CH ⟨GH, hG_GH, hK_GH, hH_GH⟩
  have hBGKD : Parallelogram B G K D := hGBDK.reverse.rotate.rotate.rotate
  have hBGHC : Parallelogram B G H C := hGBCH.reverse.rotate.rotate.rotate
  have hDKHC : Parallelogram D K H C :=
    ⟨AreParallel.of_parallel hGBDK.1.2.1 hGBCH.1.2.1.symm hD_DK hK_DK hH_CH hC_CH hDK_CH,
      AreParallel.of_parallel (ne_of_between (between_symm hGKH)).symm hDC.symm
        hK_GH hH_GH hC_BC hD_BC hGH_BC⟩
  have hparts : quadArea B G H C = quadArea B G K D + quadArea D K H C :=
    quadArea_add_of_parallelograms hBGKD hDKHC h hGKH
  /- BH and BK are contained by BG with BC and BD, respectively. -/
  have hBH : quadArea B G H C = rect A₁ A₂ B C :=
    (Rectangle.of_right hBGHC hCBG).eq_rect hBG rfl
  have hBK_rect : Rectangle B G K D := by
    refine Rectangle.of_right hBGKD ?_
    rw [angle_onRay_left (OnRay.of_between h) (ne_of_between hBGX).symm]
    exact hCBG
  have hBK : quadArea B G K D = rect A₁ A₂ B D := hBK_rect.eq_rect hBG rfl
  /- By I.34, DK equals BG and hence A₁A₂. The adjacent angle CDK is right,
     so DH is the rectangle contained by A₁A₂ and DC. -/
  have hDK : ‖D K‖ = ‖A₁ A₂‖ := by
    rw [len_symm D K, ← (BookI.Prop34 hGBDK).2.1, len_symm G B]
    exact hBG
  have hK_BC : ¬ OnLine K BC := hGH_BC.not_onLine hK_GH
  have hCDK : ∠ C D K = ∟ := by
    have hBDK := hBK_rect.2.2.2.2
    rw [angle_symm hGBDK.1.2.1.symm (ne_of_between h)] at hBDK
    rw [angle_symm hDC.symm hGBDK.1.2.1.symm,
      ← adjacent_eq_of_right hB_BC hC_BC h hK_BC hBDK]
    exact hBDK
  have hDH : quadArea D K H C = rect A₁ A₂ D C :=
    (Rectangle.of_right hDKHC hCDK).eq_rect hDK rfl
  rw [← hBH, hparts, hBK, hDH]

/-- **II.1, any number of segments** (companion of II.1). If the straight line from B to its
end is cut at any number of points in order, the rectangle contained by A₁A₂ and the whole
is equal to the rectangles contained by A₁A₂ and each of the segments. The list `ps` is
the points of section followed by the end; with no points of section it is the whole
straight line alone, and with no points at all the straight line is nothing and so is each
side. -/
theorem Prop1.general {A₁ A₂ B : Point} {ps : List Point} (h : InOrder (B :: ps)) :
    rect A₁ A₂ B (endOf B ps) =
      Magnitude.sum ((segments (B :: ps)).map fun s => rect A₁ A₂ s.1 s.2) := by
  /- Repeat the one-cut construction, taking the first segment at each step. -/
  induction ps generalizing B with
  | nil =>
      /- With no end point, both the rectangle on BB and the sum are nothing. -/
      simp only [endOf, segments, List.map, Magnitude.sum, rect_self_right]
  | cons P ps ih =>
      cases ps with
      | nil =>
          /- With no cut, BP is the whole straight line and its only segment. -/
          simp only [endOf, segments, List.map, Magnitude.sum, add_zero]
      | cons Q rest =>
          /- Cut off BP, then apply the same argument to the remaining segments. -/
          have hBP : Between B P (endOf P (Q :: rest)) :=
            InOrder.between_end h (List.cons_ne_nil Q rest)
          have hrest := ih h.2.2
          calc
            rect A₁ A₂ B (endOf B (P :: Q :: rest)) =
                rect A₁ A₂ B P + rect A₁ A₂ P (endOf P (Q :: rest)) := Prop1.two hBP
            _ = rect A₁ A₂ B P +
                Magnitude.sum ((segments (P :: Q :: rest)).map fun s => rect A₁ A₂ s.1 s.2) := by
              rw [hrest]
            _ = Magnitude.sum
                ((segments (B :: P :: Q :: rest)).map fun s => rect A₁ A₂ s.1 s.2) := rfl

/-- The check: today's statement of II.1, BC cut at D and E, follows from `Prop1.general`
for the points `[D, E, C]` (checked by Lean). -/
example : type_of% @Elements.BookII.Prop1 := by
  intro A₁ A₂ B C D E _ hBDE hDEC
  have h : InOrder [B, D, E, C] :=
    ⟨ne_of_between hBDE, hBDE, ne_of_between hDEC, hDEC,
      (ne_of_between (between_symm hDEC)).symm⟩
  have hgen := Prop1.general (A₁ := A₁) (A₂ := A₂) h
  simp only [endOf, segments, List.map, Magnitude.sum, add_zero] at hgen
  rw [hgen, add_assoc]

end Elements.BookII
