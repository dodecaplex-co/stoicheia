import Elements
open Elements Elements.Tacit

namespace Scratch

theorem not_outside {P : Point} {α : Circle} (h : ¬ OutsideCircle P α) :
    InsideCircle P α ∨ OnCircle P α := by
  exact Classical.byContradiction fun h' => h ⟨fun hi => h' (Or.inl hi), fun ho => h' (Or.inr ho)⟩

/-- **III.11.** -/
theorem T11 {A F G : Point} {ABC ADE : Circle} (hF : Centre F ABC) (hG : Centre G ADE)
    (htouch : TouchesInternally ABC ADE A) : Between F G A := by
  obtain ⟨hA₁, hA₂, hne, hwithin⟩ := htouch
  /- The circles have different centres [III. 6]. -/
  have hFG : F ≠ G := by
    rintro rfl
    exact hne (circle_eq hF hG hA₁ hA₂ rfl)
  /- `G` is within `ABC`: it lies between two points of `ADE`. -/
  have hGA : G ≠ A := (ne_of_centre_of_on hG hA₂).symm
  obtain ⟨M, hG_M, hA_M⟩ := Postulate1 G A hGA
  obtain ⟨Q, hQ, -, hQGA⟩ := line_circle_beyond (centre_inside hG) hG_M hA_M hGA.symm
  have hG_in : InsideCircle G ABC :=
    inside_of_between (not_outside (hwithin Q hQ)) (not_outside (hwithin A hA₂)) hQGA
  /- `FG` produced meets `ABC` at `H`. -/
  obtain ⟨L, hF_L, hG_L⟩ := Postulate1 F G hFG
  obtain ⟨H, hH, hH_L, hHGF⟩ := line_circle_beyond hG_in hG_L hF_L hFG
  have hFGH : Between F G H := between_symm hHGF
  refine Classical.byContradiction fun hFGA => ?_
  have hAH : A ≠ H := fun e => hFGA (e ▸ hFGH)
  have hFH : ‖F H‖ = ‖F G‖ + ‖G H‖ := (len_add_of_between hFGH).symm
  /- `GH` is less than `GA`. -/
  have hlt : ‖G H‖ < ‖G A‖ := by
    by_cases hA_L : OnLine A L
    · have hAFH : Between A F H :=
        between_of_inside_chord hF_L hA_L hH_L (centre_inside hF) hA₁ hH hAH
      have hAFG : Between A F G := between_cut hAFH hFGH
      have h1 : ‖G H‖ < ‖A F‖ := by
        rw [len_symm G H, len_symm A F, Definition15 hF hA₁ hH, len_symm F H]
        exact len_lt_of_between (between_symm hFGH)
      rw [len_symm G A, ← len_add_of_between hAFG]
      exact lt_trans h1 (CommonNotion5 (len_pos hFG))
    · have h20 := (BookI.Prop20 (Triangle.of_line hG_L hF_L hFG.symm hA_L)).1
      rw [Definition15 hF hA₁ hH, hFH] at h20
      exact Magnitude.lt_of_add_lt_add_left h20
  /- The point `D` of `ADE` on `GH` produced, as far from `G` as `A` is, falls outside
     `ABC`. -/
  obtain ⟨D, hD, hGD⟩ := OnRay.exists_len_eq hGA (ne_of_between (between_symm hFGH)).symm
  have hD₂ : OnCircle D ADE := on_circle_of_len_eq hG hA₂ hGD
  have hGHD : Between G H D :=
    OnRay.between_of_len_lt (OnRay.self (ne_of_between (between_symm hFGH)).symm) hD (hGD ▸ hlt)
  have hFGD : Between F G D := between_of_between_right hFGH hGHD
  have hFD : ‖F H‖ < ‖F D‖ := by
    rw [hFH, ← len_add_of_between hFGD, add_comm (‖F G‖), add_comm (‖F G‖)]
    exact add_lt_add_right _ (hGD ▸ hlt)
  exact hwithin D hD₂ (outside_of_len_gt hF hH hFD)

/-- **III.13**: internally by III.11 (both points of contact lie on the straight line of
the centres, beyond the inner centre, at the outer radius); externally by III.2. -/
theorem T13 {A B C D : Point} {ABDC EBFD ACK : Circle} (hABDC : ∃ G : Point, Centre G ABDC)
    (hEBFD : ∃ H : Point, Centre H EBFD) (hACK : ∃ O : Point, Centre O ACK) :
    ((TouchesInternally ABDC EBFD D ∨ TouchesInternally EBFD ABDC D) →
      OnCircle B ABDC → OnCircle B EBFD → B = D) ∧
    (TouchesExternally ACK ABDC A → OnCircle C ACK → OnCircle C ABDC → C = A) := by
  obtain ⟨G, hG⟩ := id hABDC
  obtain ⟨H, hH⟩ := hEBFD
  refine ⟨fun h hB₁ hB₂ => ?_, fun h hC₁ hC₂ => ?_⟩
  · have key : ∀ {α β : Circle} {X Y : Point}, Centre X α → Centre Y β →
        TouchesInternally α β D → OnCircle B α → OnCircle B β → B = D := by
      intro α β X Y hX hY ht hBα hBβ
      have hD := BookIII.Prop11 hX hY ht
      have hB := BookIII.Prop11 hX hY ⟨hBα, hBβ, ht.2.2.1, ht.2.2.2⟩
      obtain ⟨L, hX_L, hY_L⟩ := Postulate1 X Y (ne_of_between hD)
      have hray : OnRay B X D := ⟨ne_of_between_ends hD, (ne_of_between_ends hB).symm,
        ⟨L, hX_L, on_line_of_between hD hX_L hY_L, on_line_of_between hB hX_L hY_L⟩,
        fun hb => not_between_of_between hB (between_symm (between_cut hb hD))⟩
      exact OnRay.eq_of_len_eq hray (Definition15 hX hBα ht.1)
    rcases h with h | h
    · exact key hG hH h hB₁ hB₂
    · exact key hH hG h hB₂ hB₁
  · obtain ⟨hA₁, hA₂, hout⟩ := h
    refine Classical.byContradiction fun hCA => ?_
    obtain ⟨P, -, hAPC, -⟩ := exists_point_between (Postulate1 A C (Ne.symm hCA)).choose_spec.1
      (Postulate1 A C (Ne.symm hCA)).choose_spec.2 (Ne.symm hCA) []
    exact hout P (BookIII.Prop2 hACK hA₁ hC₁ P hAPC) (BookIII.Prop2 hABDC hA₂ hC₂ P hAPC)

end Scratch
