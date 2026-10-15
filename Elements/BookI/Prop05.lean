import Elements.Figure.Basics
import Elements.BookI.Prop03
import Elements.BookI.Prop04

/-!
# Book I, Proposition 5

Euclid's text, in Heath's translation: [`heath/I/05.md`](../../heath/I/05.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-! ## What Euclid reads off the figure -/

/-- Order on a straight line: if `Y` is between `X` and `Z`, and `Z` is between `X` and
`W`, then `Z` is between `Y` and `W`. -/
theorem Prop5.between_inner {X Y Z W : Point} (h₁ : Between X Y Z) (h₂ : Between X Z W) :
    Between Y Z W := by
  obtain ⟨L, hX, hZ⟩ := Postulate1 X Z (ne_of_between_ends h₁)
  have hY : OnLine Y L := on_line_of_between_ends h₁ hX hZ
  have hW : OnLine W L := on_line_of_between h₂ hX hZ
  have hYZ : Y ≠ Z := (ne_of_between (between_symm h₁)).symm
  have hZW : Z ≠ W := (ne_of_between (between_symm h₂)).symm
  have hYW : Y ≠ W := by
    rintro rfl
    exact not_between_of_between (between_symm h₂) (between_symm h₁)
  /- Of the three points Y, Z, W one is between the other two; only Z can be. -/
  rcases between_cases hYZ hZW hYW hY hZ hW with h | h | h
  · exact h
  · exact absurd (between_of_between_left (between_symm h₂) (between_symm h))
      (not_between_of_between_between h (between_symm h₁))
  · exact absurd (between_of_between_left (between_symm h₁) (between_symm h))
      (not_between_of_between (between_symm h₂))

/-- Euclid's "chance point" `F` on `BD`. He takes it at random, but in the very next
breath calls `AE` "the greater" and `AF` "the less", so `F` must not lie too far out
along `BD`. A circle about `A`, larger than `AB` but smaller than `AE`, keeps it in:
`F` is taken on `BD` inside that circle, or where `BD` leaves it. -/
theorem Prop5.chance_point {A B C D E : Point} (hAB : ‖A B‖ = ‖A C‖) (hD : Between A B D)
    (hE : Between A C E) : ∃ F : Point, Between B F D ∧ ‖A F‖ < ‖A E‖ := by
  obtain ⟨AE, hA_AE, hE_AE⟩ := Postulate1 A E (ne_of_between_ends hE)
  have hC_AE : OnLine C AE := on_line_of_between_ends hE hA_AE hE_AE
  have hCE : C ≠ E := (ne_of_between (between_symm hE)).symm
  /- A point X between C and E: then AX is less than AE and greater than AC. -/
  obtain ⟨X, -, hCXE, -⟩ := exists_point_between hC_AE hE_AE hCE []
  have hAXE : Between A X E :=
    between_symm (between_of_between_left (between_symm hE) (between_symm hCXE))
  have hACX : Between A C X :=
    between_symm (Prop5.between_inner (between_symm hCXE) (between_symm hE))
  have hAX_AE : ‖A X‖ < ‖A E‖ := by
    rw [← len_add_of_between hAXE]
    exact CommonNotion5 (len_pos (ne_of_between (between_symm hAXE)).symm)
  have hAB_AX : ‖A B‖ < ‖A X‖ := by
    rw [hAB, ← len_add_of_between hACX]
    exact CommonNotion5 (len_pos (ne_of_between (between_symm hACX)).symm)
  obtain ⟨α, hA_α, hX_α⟩ := Postulate3 A X (ne_of_between hAXE)
  have hB_α : InsideCircle B α := inside_of_len_lt hA_α hX_α hAB_AX
  have hBD : B ≠ D := (ne_of_between (between_symm hD)).symm
  obtain ⟨BD, hB_BD, hD_BD⟩ := Postulate1 B D hBD
  by_cases hD_α : InsideCircle D α ∨ OnCircle D α
  · /- D is not outside the circle: any point between B and D is inside it. -/
    obtain ⟨F, -, hBFD, -⟩ := exists_point_between hB_BD hD_BD hBD []
    have hF_α : InsideCircle F α := inside_of_between (Or.inl hB_α) hD_α hBFD
    exact ⟨F, hBFD, lt_trans (len_lt_of_inside hA_α hX_α hF_α) hAX_AE⟩
  · /- D is outside: take F where BD crosses the circle (System E, Intersections 4). -/
    have hD_out : OutsideCircle D α := ⟨fun h => hD_α (Or.inl h), fun h => hD_α (Or.inr h)⟩
    obtain ⟨F, hF_α, -, hBFD⟩ := line_circle_between hB_α hB_BD hD_out hD_BD
    exact ⟨F, hBFD, by rw [Definition15 hA_α hF_α hX_α]; exact hAX_AE⟩

/-- `G` is cut off from `AE`, and `AG` is greater than `AC`; so `G` lies beyond `C`. -/
theorem Prop5.beyond {A C G E : Point} (hACE : Between A C E) (hAGE : Between A G E)
    (h : ‖A C‖ < ‖A G‖) : Between A C G := by
  obtain ⟨L, hA, hE⟩ := Postulate1 A E (ne_of_between_ends hACE)
  have hC : OnLine C L := on_line_of_between_ends hACE hA hE
  have hG : OnLine G L := on_line_of_between_ends hAGE hA hE
  have hCG : C ≠ G := by
    rintro rfl
    exact lt_irrefl _ h
  rcases between_cases (ne_of_between hACE) hCG (ne_of_between hAGE) hA hC hG with h' | h' | h'
  · exact h'
  · /- A between C and G: then A would be between C and E. -/
    exact absurd (between_of_between_right h' hAGE) (not_between_of_between hACE)
  · /- G between A and C: then AG would be only a part of AC. -/
    have hpart : ‖A G‖ < ‖A C‖ := by
      rw [← len_add_of_between h']
      exact CommonNotion5 (len_pos (ne_of_between (between_symm h')).symm)
    exact absurd (lt_trans h hpart) (lt_irrefl _)

/-- Two points of a straight line and a third point off it make a triangle. -/
theorem Prop5.triangle {P Q R : Point} {L : Line} (hP : OnLine P L) (hQ : OnLine Q L)
    (hPQ : P ≠ Q) (hR : ¬ OnLine R L) : Triangle P Q R := by
  rintro ⟨M, hPM, hQM, hRM⟩
  exact hR (line_unique hPQ hPM hQM hP hQ ▸ hRM)

/-- An angle is not changed when one of its arms is traced through another point of the
same ray: if `P` is between `V` and `P'`, the angle `P'VQ` is the angle `PVQ`.
(System E, diagram-angle transfer 4) -/
theorem Prop5.angle_along {V P P' Q : Point} (h : Between V P P') (hQV : Q ≠ V) :
    ∠ P' V Q = ∠ P V Q := by
  have hVP : V ≠ P := ne_of_between h
  obtain ⟨L, hV, hP⟩ := Postulate1 V P hVP
  obtain ⟨M, hVM, hQM⟩ := Postulate1 V Q hQV.symm
  have hP' : OnLine P' L := on_line_of_between h hV hP
  exact angle_eq_of_same_rays hV hP' hP hVM hQM hQM (ne_of_between_ends h).symm hVP.symm
    hQV hQV (fun h' => not_between_of_between h (between_symm h'))
    (fun h' => ne_of_between_ends h' rfl)

/-- If `R` lies between `P` and `Q`, and `V` is off the straight line `PQ`, then `VR`
falls within the angle `PVQ`, and that angle is made up of `PVR` and `RVQ`.
(System E, Pasch 2 and diagram-angle transfer 2) -/
theorem Prop5.angle_add {V P Q R : Point} {L M N : Line} (hVL : OnLine V L) (hPL : OnLine P L)
    (hVM : OnLine V M) (hQM : OnLine Q M) (hPN : OnLine P N) (hQN : OnLine Q N)
    (hVN : ¬ OnLine V N) (h : Between P R Q) : ∠ P V Q = ∠ P V R + ∠ R V Q := by
  have hRN : OnLine R N := on_line_of_between_ends h hPN hQN
  have hVP : V ≠ P := fun e => hVN (e ▸ hPN)
  have hVQ : V ≠ Q := fun e => hVN (e ▸ hQN)
  have hPQ : P ≠ Q := ne_of_between_ends h
  have hPR : P ≠ R := ne_of_between h
  have hRQ : R ≠ Q := (ne_of_between (between_symm h)).symm
  have hLM : L ≠ M := by
    rintro rfl
    exact hVN (line_unique hPQ hPL hQM hPN hQN ▸ hVL)
  have hRL : ¬ OnLine R L := fun hR => hVN (line_unique hPR hPL hR hPN hRN ▸ hVL)
  have hRM : ¬ OnLine R M := fun hR => hVN (line_unique hRQ hR hQM hRN hQN ▸ hVM)
  exact angle_add_of_inside hVL hVM hPL hQM hVP hVQ hRL hRM hLM
    (same_side_symm (pasch2 (between_symm h) hQM hRM))
    (same_side_symm (pasch2 h hPL hRL))

/-- In isosceles triangles the angles at the base are equal to one another, and, if the equal
straight lines be produced further, the angles under the base will be equal to one another. -/
theorem Prop5 {A B C D E : Point} (hABC : Triangle A B C) (hAB : ‖A B‖ = ‖A C‖)
    (hD : Between A B D) (hE : Between A C E) :
    ∠ A B C = ∠ A C B ∧ ∠ C B D = ∠ B C E := by
  -- Let ABC be an isosceles triangle having the side AB equal to the side AC;
  have hA_B : A ≠ B := hABC.ne₁₂
  have hB_C : B ≠ C := hABC.ne₂₃
  have hA_C : A ≠ C := hABC.ne₁₃
  -- and let the straight lines BD, CE be produced further in a straight line with AB,
  -- AC. [Post. 2]
  /- The statement hands us D and E already produced, so Lean needs no Postulate 2.
     It does need the straight lines AB and AC themselves, with D and E on them, and
     the fact that ABC is a triangle: C is off AB, and B is off AC. -/
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hA_B
  obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hA_C
  have hC_AB : ¬ OnLine C AB := fun h => hABC ⟨AB, hA_AB, hB_AB, h⟩
  have hB_AC : ¬ OnLine B AC := fun h => hABC ⟨AC, hA_AC, h, hC_AC⟩
  have hE_AC : OnLine E AC := on_line_of_between hE hA_AC hC_AC
  -- I say that the angle ABC is equal to the angle ACB, and the angle CBD to the angle BCE.
  -- Let a point F be taken at random on BD;
  /- At random, but not too far out: see `Prop5.chance_point`. Then F lies beyond B
     on the straight line AB. -/
  obtain ⟨F, hBFD, hAF_AE⟩ := Prop5.chance_point hAB hD hE
  have hABF : Between A B F :=
    between_symm (Prop5.between_inner (between_symm hBFD) (between_symm hD))
  have hF_AB : OnLine F AB := on_line_of_between hABF hA_AB hB_AB
  have hA_F : A ≠ F := ne_of_between_ends hABF
  -- from AE the greater let AG be cut off equal to AF the less; [I. 3]
  obtain ⟨G, hAGE, hAG_AF⟩ := Prop3 hA_F hAF_AE
  have hG_AC : OnLine G AC := on_line_of_between_ends hAGE hA_AC hE_AC
  have hA_G : A ≠ G := ne_of_between hAGE
  -- and let the straight lines FC, GB be joined. [Post. 1]
  have hF_C : F ≠ C := fun h => hC_AB (h ▸ hF_AB)
  have hG_B : G ≠ B := fun h => hB_AC (h ▸ hG_AC)
  obtain ⟨FC, hF_FC, hC_FC⟩ := Postulate1 F C hF_C
  obtain ⟨GB, hG_GB, hB_GB⟩ := Postulate1 G B hG_B
  -- Then, since AF is equal to AG and AB to AC,
  have hAF_AG : ‖A F‖ = ‖A G‖ := hAG_AF.symm
  -- the two sides FA, AC are equal to the two sides GA, AB, respectively;
  have hAC_AB : ‖A C‖ = ‖A B‖ := hAB.symm
  -- and they contain a common angle, the angle FAG.
  /- Common, because B lies on AF and C lies on AG. For C that takes a word Euclid
     doesn't say: AG, being equal to AF, is greater than AB, that is, than AC; so G
     lies beyond C. -/
  have hAB_AF : ‖A B‖ < ‖A F‖ := by
    rw [← len_add_of_between hABF]
    exact CommonNotion5 (len_pos (ne_of_between hBFD))
  have hACG : Between A C G :=
    Prop5.beyond hE hAGE (by rw [hAC_AB, ← hAF_AG]; exact hAB_AF)
  have hFAC_GAB : ∠ F A C = ∠ G A B := by
    rw [Prop5.angle_along hABF hA_C.symm, angle_symm hA_B.symm hA_C.symm,
      Prop5.angle_along hACG hA_B.symm]
  -- Therefore the base FC is equal to the base GB,
  have hAFC : Triangle A F C := Prop5.triangle hA_AB hF_AB hA_F hC_AB
  have hAGB : Triangle A G B := Prop5.triangle hA_AC hG_AC hA_G hB_AC
  have hI4 := Prop4 hAFC hAGB hAF_AG hAC_AB hFAC_GAB
  have hFC_GB : ‖F C‖ = ‖G B‖ := hI4.1
  -- and the triangle AFC is equal to the triangle AGB,
  have : △ A F C = △ A G B := hI4.2.1
  -- and the remaining angles will be equal to the remaining angles respectively, namely those
  -- which the equal sides subtend,
  -- that is, the angle ACF to the angle ABG,
  have hACF_ABG : ∠ A C F = ∠ A B G := hI4.2.2.2
  -- and the angle AFC to the angle AGB. [I. 4]
  have hAFC_AGB : ∠ A F C = ∠ A G B := hI4.2.2.1
  -- And, since the whole AF is equal to the whole AG,
  have hAB_BF : ‖A B‖ + ‖B F‖ = ‖A F‖ := len_add_of_between hABF
  have hAC_CG : ‖A C‖ + ‖C G‖ = ‖A G‖ := len_add_of_between hACG
  -- and in these AB is equal to AC,
  -- the remainder BF is equal to the remainder CG.
  have hBF_CG : ‖B F‖ = ‖C G‖ := by
    apply CommonNotion3 (c := ‖A B‖) (d := ‖A C‖) _ hAB
    rw [add_comm, hAB_BF, hAF_AG, ← hAC_CG, add_comm]
  -- But FC was also proved equal to GB;
  -- therefore the two sides BF, FC are equal to the two sides CG, GB respectively;
  have hFB_GC : ‖F B‖ = ‖G C‖ := by rw [len_symm F B, hBF_CG, len_symm C G]
  -- and the angle BFC is equal to the angle CGB,
  /- These are the angles AFC and AGB over again, since B lies on FA and C on GA. -/
  have hBFC_CGB : ∠ B F C = ∠ C G B := by
    rw [← Prop5.angle_along (between_symm hABF) hF_C.symm,
      ← Prop5.angle_along (between_symm hACG) hG_B.symm]
    exact hAFC_AGB
  -- while the base BC is common to them;
  /- Euclid is quoting I.4 ahead of time, as Heath explains: the bases are equal
     because they are one and the same base. -/
  -- therefore the triangle BFC is also equal to the triangle CGB,
  have hFBC : Triangle F B C :=
    Prop5.triangle hF_AB hB_AB (ne_of_between (between_symm hABF)) hC_AB
  have hGCB : Triangle G C B :=
    Prop5.triangle hG_AC hC_AC (ne_of_between (between_symm hACG)) hB_AC
  have hI4' := Prop4 hFBC hGCB hFB_GC hFC_GB hBFC_CGB
  have : △ B F C = △ C G B := by
    rw [← area_rotate F C B, ← area_swap F B C, hI4'.2.1, area_swap G C B, area_rotate G B C]
  -- and the remaining angles will be equal to the remaining angles respectively, namely those
  -- which the equal sides subtend;
  -- therefore the angle FBC is equal to the angle GCB,
  have hFBC_GCB : ∠ F B C = ∠ G C B := hI4'.2.2.1
  -- and the angle BCF to the angle CBG.
  have hBCF_CBG : ∠ B C F = ∠ C B G := by
    rw [angle_symm hB_C hF_C, angle_symm hB_C.symm hG_B]
    exact hI4'.2.2.2
  -- Accordingly, since the whole angle ABG was proved equal to the angle ACF,
  /- Whole, because C lies between A and G, so that BC falls within the angle ABG;
     likewise B lies between A and F, so that CB falls within the angle ACF. -/
  have hABG : ∠ A B G = ∠ A B C + ∠ C B G :=
    Prop5.angle_add hB_AB hA_AB hB_GB hG_GB hA_AC hG_AC hB_AC hACG
  have hACF : ∠ A C F = ∠ A C B + ∠ B C F :=
    Prop5.angle_add hC_AC hA_AC hC_FC hF_FC hA_AB hF_AB hC_AB hABF
  -- and in these the angle CBG is equal to the angle BCF,
  -- the remaining angle ABC is equal to the remaining angle ACB;
  have hbase : ∠ A B C = ∠ A C B := by
    apply CommonNotion3 (c := ∠ C B G) (d := ∠ B C F) _ hBCF_CBG.symm
    rw [← hABG, ← hACF, hACF_ABG]
  -- and they are at the base of the triangle ABC.
  -- But the angle FBC was also proved equal to the angle GCB;
  -- and they are under the base.
  /- Under the base: the angle CBD is the angle CBF, since F lies on BD, and the angle
     BCE is the angle BCG, since G lies between C and E. -/
  have hCGE : Between C G E := Prop5.between_inner hACG hAGE
  have hunder : ∠ C B D = ∠ B C E := by
    rw [angle_symm hB_C.symm (ne_of_between (between_symm hD)),
      Prop5.angle_along hBFD hB_C.symm, hFBC_GCB, ← Prop5.angle_along hCGE hB_C,
      angle_symm (ne_of_between (between_symm hE)) hB_C]
  -- Therefore etc.
  exact ⟨hbase, hunder⟩
  -- Q. E. D.

end Elements.BookI
