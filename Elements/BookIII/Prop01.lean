import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop08
import Elements.BookI.Prop10
import Elements.BookI.Prop11

/-!
# Book III, Proposition 1

Euclid's text, in Heath's translation: [`heath/III/01.md`](../../heath/III/01.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- A straight line has one middle point. Euclid takes this for granted when he
identifies the centre on `CE` with its middle point `F`. -/
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

/-- At a point `A` of the straight line `AD`, only one straight line is at right
angles to it. Euclid takes this for granted in "the greater to the less". With `E`
and `F` on one side of `AD`, the equal right angles put `F` on `AE`; on opposite
sides, `EA` produced beyond `A` makes a right angle on `F`'s side. -/
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
    have hDAE' : ∠ D A E' = ∟ := (adjacent_eq_of_right hE_M hE'_M hEAE' hD_M hEAD).symm.trans hEAD
    have hE'_L : ¬ OnLine E' L := fun h => hE_L (on_line_of_between (between_symm hEAE') h hA_L)
    have hFE' : SameSide F E' L := same_side_of_opposite_sides
      ⟨hE_L, hF_L, fun h => hs (same_side_symm h)⟩ ⟨hE_L, hE'_L, pasch3 hEAE' hA_L⟩
    obtain ⟨-, -, ⟨N, hA_N, hE'_N, hF_N⟩, -⟩ :=
      onRay_of_angle_eq (SameSideOf.of_line hAD hA_L hD_L hFE') (hDAF.trans hDAE'.symm)
    have hNM : N = M := line_unique (ne_of_between (between_symm hEAE')).symm hA_N hE'_N hA_M hE'_M
    subst hNM
    exact ⟨N, hA_N, hE_M, hF_N⟩

/-- To find the centre of a given circle. -/
theorem Prop1 {A B : Point} {ABC : Circle} (hABC : ∃ G : Point, Centre G ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hAB : A ≠ B) :
    ∃ F C D E : Point, Centre F ABC ∧ Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧
      OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ Between C F E ∧ ‖C F‖ = ‖F E‖ := by
  -- Let ABC be the given circle;
  -- thus it is required to find the centre of the circle ABC.
  -- Let a straight line AB be drawn through it at random, and let it be bisected at the point
  -- D;
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  obtain ⟨D, hADB, hAD⟩ := BookI.Prop10 hAB
  have hD_L := on_line_of_between_ends hADB hA_L hB_L
  -- from D let DC be drawn at right angles to AB and let it be drawn through to E;
  obtain ⟨Q, hQ, -⟩ := exists_off_line hAB []
  obtain ⟨X, hXQ, hX⟩ := BookI.Prop11 hAB ⟨L, hA_L, hB_L, hD_L⟩ hQ
  have hD_in : InsideCircle D ABC := inside_of_between (Or.inr hA) (Or.inr hB) hADB
  have hX_L : ¬ OnLine X L := hXQ.triangle.off_line hA_L hB_L
  have hDX : D ≠ X := fun e => hX_L (e ▸ hD_L)
  obtain ⟨N, hD_N, hX_N⟩ := Postulate1 D X hDX
  obtain ⟨E, hE, hE_N, hEDX⟩ := line_circle_beyond hD_in hD_N hX_N hDX.symm
  obtain ⟨C, hC, hC_N, hCDE⟩ := line_circle_beyond hD_in hD_N hE_N (ne_of_between hEDX)
  have hCray : OnRay C D X := OnRay.of_between_between hEDX (between_symm hCDE)
  have hDA : D ≠ A := (ne_of_between hADB).symm
  have hDB : D ≠ B := (ne_of_between (between_symm hADB)).symm
  have hADC : ∠ A D C = ∟ := by
    rw [angle_onRay_right hCray hDA.symm]
    exact hX A ⟨L, hA_L, hB_L, hA_L⟩ hDA.symm
  have hCD : C ≠ D := ne_of_between hCDE
  have hC_L : ¬ OnLine C L := fun h => hX_L ((line_unique hCD hC_N hD_N h hD_L) ▸ hX_N)
  -- let CE be bisected at F;
  obtain ⟨F, hCFE, hCF⟩ := BookI.Prop10 (ne_of_between_ends hCDE)
  -- I say that F is the centre of the circle ABC.
  -- For suppose it is not, but, if possible, let G be the centre,
  obtain ⟨G, hG⟩ := hABC
  have hG_N : OnLine G N := by
    refine Classical.byContradiction fun hG_N => ?_
    -- and let GA, GD, GB be joined.
    /- A centre on AB would be its middle point D, already on CE. Excluding
       that case makes DAG and DBG triangles for I.8. -/
    have hG_L : ¬ OnLine G L := fun hG_L =>
      hG_N ((Prop1.middle hADB hAD
        (between_of_inside_chord hG_L hA_L hB_L (centre_inside hG) hA hB hAB)
        (by rw [len_symm A G, Definition15 hG hA hB])) ▸ hD_N)
    have hDAG : Triangle D A G := Triangle.of_line hD_L hA_L hDA hG_L
    have hDBG : Triangle D B G := Triangle.of_line hD_L hB_L hDB hG_L
    -- Then, since AD is equal to DB,
    have hDA_DB : ‖D A‖ = ‖D B‖ := by rw [len_symm D A, hAD]
    -- and DG is common,
    have hDG : ‖D G‖ = ‖D G‖ := rfl
    -- the two sides AD, DG are equal to the two sides BD, DG respectively;
    -- and the base GA is equal to the base GB, for they are radii;
    have hGA_GB : ‖G A‖ = ‖G B‖ := Definition15 hG hA hB
    -- therefore the angle ADG is equal to the angle GDB. [I. 8]
    have h8 : ∠ A D G = ∠ G D B :=
      (BookI.Prop8 hDAG hDBG hDA_DB hDG (by rw [len_symm A G, len_symm B G, hGA_GB])).trans
        (angle_symm hDBG.ne₁₂.symm hDBG.ne₁₃.symm)
    -- But, when a straight line set up on a straight line makes the adjacent angles equal to one
    -- another, each of the equal angles is right; [I. Def. 10]
    have hADG : ∠ A D G = ∟ := Postulate4 ⟨B, hADB, hDAG.bac, h8⟩
    -- therefore the angle GDB is right.
    have hGDB : ∠ G D B = ∟ := h8 ▸ hADG
    -- But the angle FDB is also right;
    /- If AB passes through the centre, F is D and there is no angle FDB. Lean
       takes in its place the angle CDB, right by construction. -/
    have hBDC : ∠ B D C = ∟ := by
      rw [angle_onRay_right hCray hDB.symm]
      exact hX B ⟨L, hA_L, hB_L, hB_L⟩ hDB.symm
    -- therefore the angle FDB is equal to the angle GDB, the greater to the less: which is
    -- impossible.
    have hDBC : Triangle D B C := Triangle.of_line hD_L hB_L hDB hC_L
    obtain ⟨M, hD_M, hC_M, hG_M⟩ := Prop1.perpendicular hDBC.bac hDBG.bac hBDC
      ((angle_symm hDBG.ne₁₂.symm hDBG.ne₁₃.symm).trans hGDB)
    exact hG_N ((line_unique hCD hC_M hD_M hC_N hD_N) ▸ hG_M)
  -- Therefore G is not the centre of the circle ABC.
  -- Similarly we can prove that neither is any other point except F.
  -- Therefore the point F is the centre of the circle ABC.
  /- The centre is within the circle, hence between C and E. Its equal radii
     make it the middle point F, the step Heath says Euclid takes for granted
     (vol. 2, p. 8). -/
  have hCGE := between_of_inside_chord hG_N hC_N hE_N (centre_inside hG) hC hE
    (ne_of_between_ends hCDE)
  obtain rfl : G = F := Prop1.middle hCFE hCF hCGE (by rw [len_symm C G, Definition15 hG hC hE])
  exact ⟨G, C, D, E, hG, hADB, hAD, hC, hE, hCDE, hADC, hCFE, hCF⟩
  -- PORISM. From this it is manifest that, if in a circle a straight line cut a straight line
  -- into two equal parts and at right angles, the centre of the circle is on the cutting
  -- straight line.
  /- The consequence is proved from this construction in `Prop1.porism` below. -/
  -- Q. E. F.

/-- The Porism to III.1: "if in a circle a straight line cut a straight line into two
equal parts and at right angles, the centre of the circle is on the cutting straight
line." The straight line `DC` cuts `AB`, a straight line in the circle, at its
middle point `D` and at right angles; the centre `G` is on `DC`. III.9 and III.10
cite it. -/
theorem Prop1.porism {A B C D G : Point} {ABC : Circle} (hG : Centre G ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hADB : Between A D B) (hAD : ‖A D‖ = ‖D B‖)
    (hC : ¬ Collinear A B C) (hADC : ∠ A D C = ∟) :
    Collinear D C G := by
  obtain ⟨F, C', D', E', hF, hAD'B, hAD', -, -, hC'D'E', hAD'C', hC'FE', -⟩ :=
    Prop1 ⟨G, hG⟩ hA hB (ne_of_between_ends hADB)
  have hD'D : D' = D := Prop1.middle hADB hAD hAD'B hAD'
  have hFG : F = G := centre_unique hF hG
  rw [hD'D] at hC'D'E' hAD'C'
  rw [hFG] at hC'FE'
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B (ne_of_between_ends hADB)
  have hD_L := on_line_of_between_ends hADB hA_L hB_L
  have hDA : D ≠ A := (ne_of_between hADB).symm
  have hC_L : ¬ OnLine C L := (show Triangle A B C from hC).off_line hA_L hB_L
  obtain ⟨N, hC'_N, hE'_N⟩ := Postulate1 C' E' (ne_of_between_ends hC'D'E')
  have hD_N := on_line_of_between_ends hC'D'E' hC'_N hE'_N
  have hG_N := on_line_of_between_ends hC'FE' hC'_N hE'_N
  have hC'D : C' ≠ D := ne_of_between hC'D'E'
  by_cases hGD : G = D
  · subst hGD
    obtain ⟨M, h1, h2⟩ := Postulate1 G C (fun e => hC_L (e ▸ hD_L))
    exact ⟨M, h1, h2, h1⟩
  have hC'_L : ¬ OnLine C' L := by
    intro h
    have hNL : N = L := line_unique hC'D hC'_N hD_N h hD_L
    have hG_L : OnLine G L := hNL ▸ hG_N
    exact hGD (Prop1.middle hADB hAD
      (between_of_inside_chord hG_L hA_L hB_L (centre_inside hG) hA hB (ne_of_between_ends hADB))
      (by rw [len_symm A G, Definition15 hG hA hB]))
  have hDAC : Triangle D A C := Triangle.of_line hD_L hA_L hDA hC_L
  have hDAC' : Triangle D A C' := Triangle.of_line hD_L hA_L hDA hC'_L
  obtain ⟨M, hD_M, hC'_M, hC_M⟩ := Prop1.perpendicular hDAC'.bac hDAC.bac hAD'C' hADC
  have hMN : M = N := line_unique hC'D hC'_M hD_M hC'_N hD_N
  subst hMN
  exact ⟨M, hD_M, hC_M, hG_N⟩

end Elements.BookIII
