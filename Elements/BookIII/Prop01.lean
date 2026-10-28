import Elements.Figure.Basics
import Elements.Figure.Circles
import Elements.BookIII.Squares
import Elements.BookI.Helpers
import Elements.BookI.Prop08
import Elements.BookI.Prop10
import Elements.BookI.Prop11
import Elements.BookI.Prop13
import Elements.BookI.Prop16
import Elements.BookI.Prop19

/-!
# Book III, Proposition 1

Euclid's text, in Heath's translation: [`heath/III/01.md`](../../heath/III/01.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- A straight line has one middle point. Euclid takes this for granted when he
identifies the centre on CE with its middle point F. -/
theorem Prop1.middle {A B D G : Point} (hADB : Between A D B) (hAD : ‖A D‖ = ‖D B‖)
    (hAGB : Between A G B) (hAG : ‖A G‖ = ‖G B‖) : G = D := by
  have e₁ := len_add_of_between hAGB
  have e₂ := len_add_of_between hADB
  rw [← hAG] at e₁
  rw [← hAD] at e₂
  have hlen : ‖A G‖ = ‖A D‖ := Magnitude.eq_of_add_self_eq (e₁.trans e₂.symm)
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B (ne_of_between_ends hADB)
  have hray : OnRay G A D := ⟨ne_of_between hADB, (ne_of_between hAGB).symm,
    ⟨L, hA_L, on_line_of_between_ends hADB hA_L hB_L, on_line_of_between_ends hAGB hA_L hB_L⟩,
    fun hb => not_between_of_between hAGB (between_of_between_right hb hADB)⟩
  exact OnRay.eq_of_len_eq hray hlen

/-- The middle point D of AB, a straight line in the circle, is within the circle. Euclid
takes it from his figure when he draws DC through to E, "a fact which Euclid first
demonstrates in III. 2", as Isaac Todhunter observes (Heath, vol. 2, p. 7). We take it by
III.2's own argument, from the centre G that the hypothesis gives. If G is on AB, it is AB's
middle point D (`Prop1.middle`). If not, the angles GAD and GBD are equal [I. 5]; the angle
GDB, outside the triangle GAD, is greater than GAD [I. 16], and so than GBD; and the greater
angle is subtended by the greater side [I. 19], so GD is less than the radius GB. -/
theorem Prop1.within {A B D G : Point} {ABC : Circle} (hG : Centre G ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hADB : Between A D B) (hAD : ‖A D‖ = ‖D B‖) :
    InsideCircle D ABC := by
  have hAB : A ≠ B := ne_of_between_ends hADB
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hD_L := on_line_of_between_ends hADB hA_L hB_L
  by_cases hG_L : OnLine G L
  · obtain rfl : G = D := Prop1.middle hADB hAD
      (between_of_centre_chord hG_L hA_L hB_L hG hA hB hAB)
      (by rw [len_symm A G, Definition15 hG hA hB])
    exact centre_inside hG
  have hGAB : Triangle G A B := (Triangle.of_line hA_L hB_L hAB hG_L).cab
  have hGAD : Triangle G A D := (Triangle.of_line hA_L hD_L (ne_of_between hADB) hG_L).cab
  have hGDB : Triangle G D B :=
    (Triangle.of_line hD_L hB_L (ne_of_between (between_symm hADB)).symm hG_L).cab
  have h5 : ∠ G A D = ∠ G B D := by
    rw [angle_onRay_right (OnRay.of_between hADB) hGAB.ne₁₂,
      angle_onRay_right (OnRay.of_between (between_symm hADB)) hGAB.ne₁₃]
    exact BookI.Prop5.base hGAB (Definition15 hG hA hB)
  have h16 : ∠ G A D < ∠ G D B := by
    rw [angle_symm hGAD.ne₁₂ hGAD.ne₂₃.symm]
    exact (BookI.Prop16 hGAD hADB).1
  have h19 : ‖G D‖ < ‖G B‖ :=
    BookI.Prop19 hGDB (by rw [angle_symm hGDB.ne₂₃ hGDB.ne₁₃]; exact h5 ▸ h16)
  exact inside_of_len_lt hG hB h19

/-- At a point A of the straight line AD, only one straight line is at right
angles to it. Euclid takes this for granted in "the greater to the less". With E
and F on one side of AD, the equal right angles put F on AE; on opposite
sides, EA produced beyond A makes a right angle on F's side, since the two angles at
A with AD, one of them right, together make two right angles [I. 13]. -/
theorem Prop1.perpendicular {A D E F : Point} (hE : Triangle D A E) (hF : Triangle D A F)
    (hDAE : ∠ D A E = ∟) (hDAF : ∠ D A F = ∟) : Collinear A E F := by
  have hAD : A ≠ D := hE.ne₁₂.symm
  obtain ⟨L, hA_L, hD_L⟩ := Postulate1 A D hAD
  have hE_L : ¬ OnLine E L := hE.bac.off_line hA_L hD_L
  have hF_L : ¬ OnLine F L := hF.bac.off_line hA_L hD_L
  by_cases hs : SameSide F E L
  · exact (onRay_of_angle_eq (SameSideOf.of_line hAD hA_L hD_L hs) (hDAF.trans hDAE.symm)).2.2.1
  · obtain ⟨M, hE_M, hA_M⟩ := Postulate1 E A hE.ne₂₃.symm
    obtain ⟨E', hE'_M, hEAE', -⟩ := Postulate2 hE_M hA_M hE.ne₂₃.symm []
    have hD_M : ¬ OnLine D M := fun hD => hE ⟨M, hD, hA_M, hE_M⟩
    have hEAD : ∠ E A D = ∟ := by rw [angle_symm hE.ne₂₃.symm hE.ne₁₂]; exact hDAE
    /- The angles EAD, DAE' together make two right angles [I. 13]; EAD is right, so
       taking it away leaves DAE' right [C.N. 3]. -/
    have h13 : ∠ E A D + ∠ D A E' = ∟ + ∟ :=
      BookI.Prop13 hEAE' (Triangle.of_line hE_M hE'_M (ne_of_between_ends hEAE') hD_M)
    rw [hEAD, add_comm ∟] at h13
    have hDAE' : ∠ D A E' = ∟ := CommonNotion3 h13 rfl
    have hE'_L : ¬ OnLine E' L := fun h => hE_L (on_line_of_between (between_symm hEAE') h hA_L)
    have hFE' : SameSide F E' L := same_side_of_opposite_sides
      ⟨hE_L, hF_L, fun h => hs (same_side_symm h)⟩ ⟨hE_L, hE'_L, pasch3 hEAE' hA_L⟩
    obtain ⟨-, -, ⟨N, hA_N, hE'_N, hF_N⟩, -⟩ :=
      onRay_of_angle_eq (SameSideOf.of_line hAD hA_L hD_L hFE') (hDAF.trans hDAE'.symm)
    have hNM : N = M := line_unique (ne_of_between (between_symm hEAE')).symm hA_N hE'_N hA_M hE'_M
    subst hNM
    exact ⟨N, hA_N, hE_M, hF_N⟩

/-- With DA equal to DB and GA equal to GB, the triangles DAG and DBG have equal sides,
DG being common. I.8 makes the angles ADG and GDB equal, the comparison used in III.1 and
its porism before those adjacent angles are shown to be right. -/
theorem Prop1.equal_adjacent {A B D G : Point} (hDAG : Triangle D A G)
    (hDBG : Triangle D B G) (hDA_DB : ‖D A‖ = ‖D B‖) (hGA_GB : ‖G A‖ = ‖G B‖) :
    ∠ A D G = ∠ G D B :=
  (BookI.Prop8 hDAG hDBG hDA_DB rfl (by rw [len_symm A G, len_symm B G, hGA_GB])).trans
    (angle_symm hDBG.ne₁₂.symm hDBG.ne₁₃.symm)

/-- D must be within the circle before the perpendicular through it can be produced to
the circumference. This is the unproved obligation in the construction without a chosen
centre. `Prop1.within` proves it from a given centre, but obtaining that centre from
`exists_centre` would restore the construction's former dependence on that witness.
III.2 cannot supply the step: it obtains its centre from III.1. -/
theorem Prop1.midpoint_inside {A B D : Point} {ABC : Circle} (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hADB : Between A D B) (hAD : ‖A D‖ = ‖D B‖) :
    InsideCircle D ABC := by
  sorry

/-- From an interior point D of AB, draw DC at right angles to AB [I.11] and produce
it through to E (Intersections 5). This step receives the interior-point evidence;
it neither chooses a centre nor bisects CE. -/
theorem Prop1.perpendicular_chord {A B D : Point} {ABC : Circle}
    (hADB : Between A D B) (hD_in : InsideCircle D ABC) :
    ∃ C E : Point, OnCircle C ABC ∧ OnCircle E ABC ∧ Between C D E ∧
      ∠ A D C = ∟ ∧ ∠ B D C = ∟ ∧ ¬ Collinear A B C := by
  have hAB : A ≠ B := ne_of_between_ends hADB
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hD_L := on_line_of_between_ends hADB hA_L hB_L
  obtain ⟨Q, hQ, -⟩ := exists_off_line hAB []
  obtain ⟨X, hXQ, hX⟩ := BookI.Prop11 hAB ⟨L, hA_L, hB_L, hD_L⟩ hQ
  have hX_L : ¬ OnLine X L := hXQ.triangle.off_line hA_L hB_L
  have hDX : D ≠ X := fun e => hX_L (e ▸ hD_L)
  obtain ⟨N, hD_N, hX_N⟩ := Postulate1 D X hDX
  /- Produce XD beyond D so Intersections 5 finds C on the ray DX first. Then
     produce CD beyond D to meet the circle at E. -/
  obtain ⟨Y, hY_N, hXDY, -⟩ := Postulate2 hX_N hD_N hDX.symm []
  obtain ⟨C, hC, hC_N, hCDY⟩ :=
    line_circle_beyond hD_in hD_N hY_N (ne_of_between (between_symm hXDY))
  have hCray : OnRay C D X :=
    OnRay.of_between_between (between_symm hXDY) (between_symm hCDY)
  have hDA : D ≠ A := (ne_of_between hADB).symm
  have hDB : D ≠ B := (ne_of_between (between_symm hADB)).symm
  have hADC : ∠ A D C = ∟ := by
    rw [angle_onRay_right hCray hDA.symm]
    exact hX A ⟨L, hA_L, hB_L, hA_L⟩ hDA.symm
  have hBDC : ∠ B D C = ∟ := by
    rw [angle_onRay_right hCray hDB.symm]
    exact hX B ⟨L, hA_L, hB_L, hB_L⟩ hDB.symm
  obtain ⟨E, hE, -, hEDC⟩ := line_circle_beyond hD_in hD_N hC_N (ne_of_between hCDY)
  have hCDE : Between C D E := between_symm hEDC
  have hCD : C ≠ D := ne_of_between hCDE
  have hC_L : ¬ OnLine C L := fun h => hX_L ((line_unique hCD hC_N hD_N h hD_L) ▸ hX_N)
  exact ⟨C, E, hC, hE, hCDE, hADC, hBDC, Triangle.of_line hA_L hB_L hAB hC_L⟩

/-- Euclid's construction for III.1 receives a circle and two points A, B of it.
AB is bisected at D [I.10]; DC is drawn at right angles to AB and through to E;
and CE is bisected at F [I.10]. Its interior-point obligation is isolated in
`Prop1.midpoint_inside`, still unproved without choosing a centre. The same three
steps appear separately under Heath's sentences in `Prop1`. -/
theorem Prop1.construction {A B : Point} {ABC : Circle} (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hAB : A ≠ B) :
    ∃ F C D E : Point, Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧
      OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ ∠ B D C = ∟ ∧ ¬ Collinear A B C ∧
      Between C F E ∧ ‖C F‖ = ‖F E‖ := by
  obtain ⟨D, hADB, hAD⟩ := BookI.Prop10 hAB
  obtain ⟨C, E, hC, hE, hCDE, hADC, hBDC, hC_AB⟩ :=
    Prop1.perpendicular_chord hADB (Prop1.midpoint_inside hA hB hADB hAD)
  obtain ⟨F, hCFE, hCF⟩ := BookI.Prop10 (ne_of_between_ends hCDE)
  exact ⟨F, C, D, E, hADB, hAD, hC, hE, hCDE, hADC, hBDC, hC_AB, hCFE, hCF⟩

/-- To find the centre of a given circle. -/
theorem Prop1 {A B : Point} {ABC : Circle} (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hAB : A ≠ B) :
    ∃ F C D E : Point, Centre F ABC ∧ Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧
      OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ Between C F E ∧ ‖C F‖ = ‖F E‖ := by
  -- Let ABC be the given circle;
  -- thus it is required to find the centre of the circle ABC.
  -- Let a straight line AB be drawn through it at random, and let it be bisected at the point
  -- D;
  obtain ⟨D, hADB, hAD⟩ := BookI.Prop10 hAB
  -- from D let DC be drawn at right angles to AB and let it be drawn through to E;
  obtain ⟨C, E, hC, hE, hCDE, hADC, hBDC, hC_AB⟩ :=
    Prop1.perpendicular_chord hADB (Prop1.midpoint_inside hA hB hADB hAD)
  -- let CE be bisected at F;
  obtain ⟨F, hCFE, hCF⟩ := BookI.Prop10 (ne_of_between_ends hCDE)
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hD_L := on_line_of_between_ends hADB hA_L hB_L
  have hCD : C ≠ D := ne_of_between hCDE
  obtain ⟨N, hC_N, hD_N⟩ := Postulate1 C D hCD
  have hE_N : OnLine E N := on_line_of_between hCDE hC_N hD_N
  have hDA : D ≠ A := (ne_of_between hADB).symm
  have hDB : D ≠ B := (ne_of_between (between_symm hADB)).symm
  have hC_L : ¬ OnLine C L := (show Triangle A B C from hC_AB).off_line hA_L hB_L
  -- I say that F is the centre of the circle ABC.
  have hF : Centre F ABC := by
    -- For suppose it is not, but, if possible, let G be the centre,
    apply Classical.byContradiction
    intro hF
    /- Definitions I.15 and I.16 presuppose a centre of the given circle. Under the
       supposition that F is not it, that centre G differs from F. This supplies the
       reductio's witness, not the point returned by the construction. -/
    obtain ⟨G, hG⟩ := exists_centre ABC
    have hGF : G ≠ F := fun e => hF (e ▸ hG)
    have hG_N : OnLine G N := by
      refine Classical.byContradiction fun hG_N => ?_
      -- and let GA, GD, GB be joined.
      /- A centre on AB would be its middle point D, already on CE. We set that case aside, so
         that DAG and DBG are triangles for I.8. -/
      have hG_L : ¬ OnLine G L := fun hG_L =>
        hG_N ((Prop1.middle hADB hAD
          (between_of_centre_chord hG_L hA_L hB_L hG hA hB hAB)
          (by rw [len_symm A G, Definition15 hG hA hB])) ▸ hD_N)
      have hDAG : Triangle D A G := Triangle.of_line hD_L hA_L hDA hG_L
      have hDBG : Triangle D B G := Triangle.of_line hD_L hB_L hDB hG_L
      -- Then, since AD is equal to DB,
      have hDA_DB : ‖D A‖ = ‖D B‖ := by rw [len_symm D A, hAD]
      -- and DG is common,
      -- the two sides AD, DG are equal to the two sides BD, DG respectively;
      -- and the base GA is equal to the base GB, for they are radii;
      have hGA_GB : ‖G A‖ = ‖G B‖ := Definition15 hG hA hB
      -- therefore the angle ADG is equal to the angle GDB. [I. 8]
      have h8 : ∠ A D G = ∠ G D B :=
        Prop1.equal_adjacent hDAG hDBG hDA_DB hGA_GB
      -- But, when a straight line set up on a straight line makes the adjacent angles equal to one
      -- another, each of the equal angles is right; [I. Def. 10]
      /- Definition I.10 makes each of the equal adjacent angles right, and Postulate 4
         makes it `∟`, as in I.11. -/
      have hADG : ∠ A D G = ∟ := Postulate4 ⟨B, hADB, hDAG.bac, h8⟩
      -- therefore the angle GDB is right.
      have hGDB : ∠ G D B = ∟ := h8 ▸ hADG
      -- But the angle FDB is also right;
      /- If AB passes through the centre, F is D and there is no angle FDB. We take in its
         place the angle CDB, right by construction. -/
      have hCDB : ∠ C D B = ∟ :=
        (angle_symm hCD hDB.symm).trans hBDC
      -- therefore the angle FDB is equal to the angle GDB, the greater to the less: which is
      -- impossible.
      have hDBC : Triangle D B C := Triangle.of_line hD_L hB_L hDB hC_L
      obtain ⟨M, hD_M, hC_M, hG_M⟩ := Prop1.perpendicular hDBC.bac hDBG.bac
        ((angle_symm hDB.symm hCD).trans hCDB)
        ((angle_symm hDBG.ne₁₂.symm hDBG.ne₁₃.symm).trans hGDB)
      exact hG_N ((line_unique hCD hC_M hD_M hC_N hD_N) ▸ hG_M)
    -- Therefore G is not the centre of the circle ABC.
    /- The centre lies between C and E, since either other order would make one of its
       radii a part of the other (`between_of_centre_chord`). Its equal radii
       make it the middle point F, the step Heath says Euclid takes for granted
       (vol. 2, p. 8). -/
    have hCGE := between_of_centre_chord hG_N hC_N hE_N hG hC hE (ne_of_between_ends hCDE)
    have hmiddle : G = F :=
      Prop1.middle hCFE hCF hCGE (by rw [len_symm C G, Definition15 hG hC hE])
    -- Similarly we can prove that neither is any other point except F.
    /- Nothing in this contradiction restricted the centre G supplied by the definition. -/
    exact hGF hmiddle
  -- Therefore the point F is the centre of the circle ABC.
  exact ⟨F, C, D, E, hF, hADB, hAD, hC, hE, hCDE, hADC, hCFE, hCF⟩
  -- PORISM. From this it is manifest that, if in a circle a straight line cut a straight line
  -- into two equal parts and at right angles, the centre of the circle is on the cutting
  -- straight line.
  /- The same comparison of the adjacent angles proves `Prop1.porism` below. -/
  -- Q. E. F.

/-- The Porism to III.1: "if in a circle a straight line cut a straight line into two
equal parts and at right angles, the centre of the circle is on the cutting straight
line." The straight line DC cuts AB, a straight line in the circle, at its
middle point D and at right angles, and the centre G is on DC. III.9 and III.10
cite it. -/
theorem Prop1.porism {A B C D G : Point} {ABC : Circle} (hG : Centre G ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hADB : Between A D B) (hAD : ‖A D‖ = ‖D B‖)
    (hC : ¬ Collinear A B C) (hADC : ∠ A D C = ∟) :
    Collinear D C G := by
  have hAB : A ≠ B := ne_of_between_ends hADB
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hD_L := on_line_of_between_ends hADB hA_L hB_L
  have hC_L : ¬ OnLine C L := (show Triangle A B C from hC).off_line hA_L hB_L
  by_cases hG_L : OnLine G L
  · have hGD : G = D := Prop1.middle hADB hAD
      (between_of_centre_chord hG_L hA_L hB_L hG hA hB hAB)
      (by rw [len_symm A G, Definition15 hG hA hB])
    subst G
    obtain ⟨M, hD_M, hC_M⟩ := Postulate1 D C (fun e => hC_L (e ▸ hD_L))
    exact ⟨M, hD_M, hC_M, hD_M⟩
  have hDA : D ≠ A := (ne_of_between hADB).symm
  have hDB : D ≠ B := (ne_of_between (between_symm hADB)).symm
  have hDAG : Triangle D A G := Triangle.of_line hD_L hA_L hDA hG_L
  have hDBG : Triangle D B G := Triangle.of_line hD_L hB_L hDB hG_L
  have h8 : ∠ A D G = ∠ G D B := Prop1.equal_adjacent hDAG hDBG
    (by rw [len_symm D A, hAD]) (Definition15 hG hA hB)
  have hADG : ∠ A D G = ∟ := Postulate4 ⟨B, hADB, hDAG.bac, h8⟩
  have hDAC : Triangle D A C := Triangle.of_line hD_L hA_L hDA hC_L
  exact Prop1.perpendicular hDAC.bac hDAG.bac hADC hADG

/-- **III.1 for a circle alone** (companion of III.1, "III.1 of_circle"). Given only a
circle, Euclid's construction finds its centre: two points A, B of the circle are taken
(Points 7), and III.1 runs on the straight line AB, drawn "through it at random". It returns
A and B with III.1's points; that A and B differ follows from `Between A D B`. It stands
after III.1's porism, and rests on what III.1 rests on and on Points 7, which III.1 does
not use. Where Heath's "[III. 1]" stands, a proof that takes the centre takes it by
this companion; where Euclid takes a centre with no reference, cite the rule itself. -/
theorem Prop1.of_circle (ABC : Circle) :
    ∃ A B F C D E : Point, OnCircle A ABC ∧ OnCircle B ABC ∧ Centre F ABC ∧
      Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧ OnCircle E ABC ∧ Between C D E ∧
      ∠ A D C = ∟ ∧ Between C F E ∧ ‖C F‖ = ‖F E‖ := by
  obtain ⟨A, hA, -⟩ := exists_point_on_circle ABC []
  obtain ⟨B, hB, hBA⟩ := exists_point_on_circle ABC [A]
  have hAB : A ≠ B := fun e => hBA (e ▸ List.mem_singleton_self A)
  obtain ⟨F, C, D, E, h⟩ := Prop1 hA hB hAB
  exact ⟨A, B, F, C, D, E, hA, hB, h⟩

end Elements.BookIII
