import Elements.Figure.Parallels
import Elements.Figure.Areas

/-!
# Book Zero: parallelograms

"Let ABCD be a parallelogram": from I.34 on, Euclid reads off his figure where the
corners of a parallelogram lie, and where a straight line drawn across two
parallels falls. He never doubts that the parallelogram ABCD is the
parallelogram BCDA; that its two far corners lie on one side of each side; that
its diameters cross; that a point of a straight line joining two parallels, on the
inner side of each, lies between them; that parallels keep the order of the points
they pass through; that a four-sided figure between two parallels either has
crossing diameters or two sides that cross; or that a parallelogram cut by a
straight line parallel to two of its sides is the two parallelograms it is cut
into. These are those facts.

None of their proofs uses Postulate 5: they are read from System E's rules for
sides (Avigad, Dean and Mumma, §3.4) and its rules for areas (§3.6).
-/

namespace Elements

open Tacit

variable {A B C D E F X A' B' C' : Point} {L M N L₁ L₃ : Line}

/-! ## The parallelogram named from another corner -/

/-- The parallelogram ABCD, named from B, is the parallelogram BCDA. -/
theorem Parallelogram.rotate (h : Parallelogram A B C D) : Parallelogram B C D A :=
  ⟨h.2, h.1.symm⟩

/-- The parallelogram ABCD, read the other way round from A, is the
parallelogram ADCB. -/
theorem Parallelogram.reverse (h : Parallelogram A B C D) : Parallelogram A D C B :=
  ⟨h.2.symm.swap_left.swap_right, h.1.symm.swap_left.swap_right⟩

/-- In the parallelogram ABCD, the corner C is off the straight line AB, so
ABC is a triangle. -/
theorem Parallelogram.triangle (h : Parallelogram A B C D) : Triangle A B C :=
  h.1.triangle

/-- In the parallelogram ABCD, the far corners C and D lie on one side of the
side AB. (Named from another corner with `.rotate`, the same holds of every
side.) -/
theorem Parallelogram.sameSideOf (h : Parallelogram A B C D) : SameSideOf C D A B :=
  h.1.symm.sameSideOf

/-! ## Between two parallels -/

/-- A point on the straight line AC, on C's side of a straight line L through
A and on A's side of a straight line M through C, lies between A and C.
Were A between it and C, L would separate it from C; were C between it and
A, M would separate it from A (System E, Between 6 and Pasch 3). So a point
of a straight line joining two parallels, lying between the parallels, lies
between the points where it meets them. `Between.of_sameSide`, below, is another
matter: it carries the order of three points across a straight line. -/
theorem Between.of_inside (hA : OnLine A L) (hC : OnLine C M) (hX : Collinear A X C)
    (hXL : SameSide X C L) (hXM : SameSide X A M) : Between A X C := by
  have hX_L : ¬ OnLine X L := not_on_line_of_same_side hXL
  have hX_M : ¬ OnLine X M := not_on_line_of_same_side hXM
  have hC_L : ¬ OnLine C L := not_on_line_of_same_side (same_side_symm hXL)
  have hAX : A ≠ X := fun e => hX_L (e ▸ hA)
  have hXC : X ≠ C := fun e => hX_M (e ▸ hC)
  have hAC : A ≠ C := fun e => hC_L (e ▸ hA)
  obtain ⟨N, hA_N, hX_N, hC_N⟩ := hX
  rcases between_cases hAX hXC hAC hA_N hX_N hC_N with h | h | h
  · exact h
  · exact absurd hXL (pasch3 h hA)
  · exact absurd (same_side_symm hXM) (pasch3 h hC)

/-- Order kept across a straight line. If B, on the straight line L, lies
between A and C, and A', C' lie on the same sides of L as A, C, then a
point B' of L on one straight line with A' and C' lies between them: A' and
C' are on opposite sides of L, so the straight line joining them crosses L
between them, and it crosses L only once (System E, Pasch 3 and 4). -/
theorem Between.of_sameSide (hABC : Between A B C) (hB : OnLine B L) (hA : SameSide A' A L)
    (hC : SameSide C' C L) (hB' : OnLine B' L) (hcol : Collinear A' B' C') :
    Between A' B' C' := by
  have hA'L : ¬ OnLine A' L := not_on_line_of_same_side hA
  have hC'L : ¬ OnLine C' L := not_on_line_of_same_side hC
  have hAC : ¬ SameSide A C L := pasch3 hABC hB
  have hA'C' : ¬ SameSide A' C' L := fun hs =>
    hAC (same_side_trans (same_side_symm (same_side_trans hA hs)) hC)
  have hne : A' ≠ C' := fun e => hA'C' (e ▸ same_side_refl hA'L)
  obtain ⟨N, hA'N, hB'N, hC'N⟩ := hcol
  have hLN : L ≠ N := fun e => hA'L (e ▸ hA'N)
  exact pasch4 hLN hB' hB'N hA'N hC'N hne (fun e => hA'L (e ▸ hB')) (fun e => hC'L (e ▸ hB'))
    hA'C'

/-- Parallels keep order. Let three straight lines be crossed by two others: if B
lies between A and C on one crossing straight line, then B' lies between A'
and C' on the other, when A, A' lie on L₁, B, B' on L, and C, C' on
L₃, and L₁ and L₃ are each parallel to L. All of L₁ lies on one side of
L, and all of L₃ on the other (`Parallel.sameSide`). Book II's figures use it
(`Parallelogram.figure`), where the parallels through the points of section meet the
far side of the square in the same order. -/
theorem Parallel.between (h₁ : Parallel L₁ L) (h₃ : Parallel L₃ L) (hA : OnLine A L₁)
    (hB : OnLine B L) (hC : OnLine C L₃) (hABC : Between A B C) (hA' : OnLine A' L₁)
    (hB' : OnLine B' L) (hC' : OnLine C' L₃) (hcol : Collinear A' B' C') :
    Between A' B' C' :=
  hABC.of_sameSide hB (h₁.sameSide hA' hA) (h₃.sameSide hC' hC) hB' hcol

/-! ## A four-sided figure between two parallels -/

/-- A four-sided figure between two parallels. If AD is parallel to BC, then
either the diameters AC and BD of the figure ABCD cross, or its sides AB and
DC cross: AD runs the same way as BC, or the other way.

The straight line AC either separates B from D or it does not. If it does, BD
crosses it, between the parallels, and so between A and C. If it does not, D
lies within the angle ACB, and the straight line CD crosses AB (`crossbar`),
again between the parallels (`Between.of_inside`). -/
theorem AreParallel.cross_or (h : AreParallel A D B C) :
    (∃ X : Point, Between A X C ∧ Between B X D) ∨
      (∃ X : Point, Between A X B ∧ Between D X C) := by
  obtain ⟨L, hA, hD⟩ := Postulate1 A D h.1
  obtain ⟨M, hB, hC⟩ := Postulate1 B C h.2.1
  have hpar : Parallel L M := h.parallel hA hD hB hC
  have hAD_M : SameSide A D M := hpar.sameSide hA hD
  have hBC_L : SameSide B C L := hpar.symm.sameSide hB hC
  have hA_M : ¬ OnLine A M := hpar.not_onLine hA
  have hD_M : ¬ OnLine D M := hpar.not_onLine hD
  have hB_L : ¬ OnLine B L := hpar.symm.not_onLine hB
  have hC_L : ¬ OnLine C L := hpar.symm.not_onLine hC
  have hAC : A ≠ C := fun e => hA_M (e ▸ hC)
  obtain ⟨N, hA_N, hC_N⟩ := Postulate1 A C hAC
  have hB_N : ¬ OnLine B N := fun hB_N =>
    hA_M ((line_unique h.2.1 hB_N hC_N hB hC) ▸ hA_N)
  have hD_N : ¬ OnLine D N := fun hD_N =>
    hC_L ((line_unique h.1 hA_N hD_N hA hD) ▸ hC_N)
  by_cases hs : SameSide B D N
  · /- D lies within the angle ACB, so CD crosses AB. -/
    obtain ⟨X, hAXB, hX⟩ := crossbar
      (SameSideOf.of_line hAC.symm hC_N hA_N (same_side_symm hs))
      (SameSideOf.of_line h.2.1.symm hC hB (same_side_symm hAD_M))
    have hX_L : ¬ OnLine X L := fun hX_L =>
      hB_L (on_line_of_between hAXB hA hX_L)
    have hX_M : ¬ OnLine X M := fun hX_M =>
      hA_M (on_line_of_between (between_symm hAXB) hB hX_M)
    have hXB_L : SameSide X B L := pasch2 hAXB hA hX_L
    have hXA_M : SameSide X A M := pasch2 (between_symm hAXB) hB hX_M
    obtain ⟨-, -, ⟨P, hC_P, hD_P, hX_P⟩, -⟩ := hX
    refine Or.inr ⟨X, hAXB, Between.of_inside hD hC ⟨P, hD_P, hX_P, hC_P⟩
      (same_side_trans (same_side_symm hXB_L) hBC_L)
      (same_side_trans (same_side_symm hXA_M) hAD_M)⟩
  · /- AC separates B from D, so BD crosses it. -/
    obtain ⟨X, hX_N, hBXD⟩ := OppositeSides.exists_between ⟨hB_N, hD_N, hs⟩
    have hX_M : ¬ OnLine X M := fun hX_M =>
      hD_M (on_line_of_between hBXD hB hX_M)
    have hX_L : ¬ OnLine X L := fun hX_L =>
      hB_L (on_line_of_between (between_symm hBXD) hD hX_L)
    have hXD_M : SameSide X D M := pasch2 hBXD hB hX_M
    have hXB_L : SameSide X B L := pasch2 (between_symm hBXD) hD hX_L
    refine Or.inl ⟨X, Between.of_inside hA hC ⟨N, hA_N, hX_N, hC_N⟩
      (same_side_trans (same_side_symm hXB_L) hBC_L)
      (same_side_trans (same_side_symm hXD_M) (same_side_symm hAD_M)), hBXD⟩

/-- Diameters that cross make the figure convex: if the diameters AC and BD of
ABCD cross, then C and D lie on one side of AB. For the crossing point lies on
C's side of AB and on D's (System E, Pasch 2). -/
theorem SameSideOf.of_cross (hAXC : Between A X C) (hBXD : Between B X D)
    (hABC : Triangle A B C) : SameSideOf C D A B := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B hABC.ne₁₂
  have hX : ¬ OnLine X L := fun hX =>
    hABC.off_line hA hB (on_line_of_between hAXC hA hX)
  exact SameSideOf.of_line hABC.ne₁₂ hA hB
    (same_side_trans (pasch2 hAXC hA hX) (pasch2 hBXD hB hX))

/-- Which way two parallels run. If AD is parallel to BC, then either D lies on
C's side of AB (AD runs the same way as BC), or A lies on C's side of
DB (DA runs the same way as BC). This is `AreParallel.cross_or`, read with
`SameSideOf.of_cross`. -/
theorem AreParallel.sameSideOf_or (h : AreParallel A D B C) :
    SameSideOf C D A B ∨ SameSideOf C A D B := by
  have hABC : Triangle A B C := h.symm.triangle.cab
  rcases h.cross_or with ⟨X, hAXC, hBXD⟩ | ⟨X, hAXB, hDXC⟩
  · exact Or.inl (SameSideOf.of_cross hAXC hBXD hABC)
  · have hDBC : Triangle D B C := h.symm.swap_right.triangle.cab
    exact Or.inr (SameSideOf.of_cross hDXC (between_symm hAXB) hDBC)

/-! ## The diameters of a parallelogram -/

/-- The diameters of a parallelogram cross: in the parallelogram ABCD, some point
lies between A and C and between B and D. Its sides AB and DC are
parallel, so they do not cross, and `AreParallel.cross_or` leaves only the
diameters. -/
theorem Parallelogram.cross (h : Parallelogram A B C D) :
    ∃ X : Point, Between A X C ∧ Between B X D := by
  rcases h.2.symm.swap_left.cross_or with hX | ⟨X, hAXB, hDXC⟩
  · exact hX
  · obtain ⟨L, hA, hB⟩ := Postulate1 A B h.1.1
    obtain ⟨M, hC, hD⟩ := Postulate1 C D h.1.2.1
    exact absurd (on_line_of_between_ends hDXC hD hC)
      ((h.1.parallel hA hB hC hD).not_onLine (on_line_of_between_ends hAXB hA hB))

/-- A parallelogram has the same area whichever diameter cuts it: the parallelogram
ABCD measured by BD, as BCDA, is the same as measured by AC. -/
theorem Parallelogram.quadArea_rotate (h : Parallelogram A B C D) :
    quadArea B C D A = quadArea A B C D := by
  obtain ⟨X, hAXC, hBXD⟩ := h.cross
  exact quadArea_rotate_of_cross hAXC hBXD

/-! ## A parallelogram cut in two -/

/-- A parallelogram cut by a straight line parallel to two of its sides is the two
parallelograms it is cut into. If E lies between A and D, F between B and
C, and ABFE, EFCD are parallelograms, then the figure ABCD is ABFE and
EFCD together. Cut each piece and the whole into triangles from A and C; the
four-sided figure AFCE is measured by AC in the whole and by FE in the pieces,
and its diameters cross, for A and C lie on either side of EF. -/
theorem quadArea_add_of_parallelograms (h₁ : Parallelogram A B F E) (h₂ : Parallelogram E F C D)
    (hAED : Between A E D) (hBFC : Between B F C) :
    quadArea A B C D = quadArea A B F E + quadArea E F C D := by
  obtain ⟨L, hA, hD⟩ := Postulate1 A D (ne_of_between_ends hAED)
  have hE : OnLine E L := on_line_of_between_ends hAED hA hD
  obtain ⟨M, hF, hC⟩ := Postulate1 F C h₂.2.1
  have hLM : Parallel L M := (h₂.2.parallel hF hC hD hE).symm
  have hAFCE : AreParallel A E F C :=
    AreParallel.of_parallel (ne_of_between hAED) h₂.2.1 hA hE hF hC hLM
  /- A and C lie on either side of EF. -/
  obtain ⟨N, hE_N, hF_N⟩ := Postulate1 E F h₂.1.1
  have hAB : SameSide A B N := h₁.1.sameSideOf.swap.sameSide hE_N hF_N
  have hCD : SameSide C D N := h₂.1.symm.sameSideOf.sameSide hE_N hF_N
  have hA_N : ¬ OnLine A N := not_on_line_of_same_side hAB
  have hAC : ¬ SameSide A C N := fun hs =>
    pasch3 hAED hE_N (same_side_trans (same_side_symm hs) hCD)
  /- So the diameters AC and FE of AFCE cross. -/
  have hcross : ∃ Y : Point, Between A Y C ∧ Between F Y E := by
    rcases hAFCE.cross_or with hY | ⟨Y, hAYF, hEYC⟩
    · exact hY
    · have hY_N : ¬ OnLine Y N := fun hY =>
        hA_N (on_line_of_between (between_symm hAYF) hF_N hY)
      exact absurd (same_side_trans (pasch2 (between_symm hAYF) hF_N hY_N)
        (pasch2 hEYC hE_N hY_N)) hAC
  obtain ⟨Y, hAYC, hFYE⟩ := hcross
  have hq : quadArea F C E A = quadArea A F C E := quadArea_rotate_of_cross hAYC hFYE
  unfold quadArea at hq ⊢
  rw [← area_cut (A := A) hBFC, area_bac A C D, ← area_cut (A := C) hAED,
    area_bac C E D, area_bac C A E]
  rw [area_cab F C E, area_cab F E A] at hq
  calc △ A B F + △ A F C + (△ A C E + △ E C D)
      = △ A B F + (△ A F C + △ A C E) + △ E C D := by ac_rfl
    _ = △ A B F + (△ E F C + △ A F E) + △ E C D := by rw [hq]
    _ = △ A B F + △ A F E + (△ E F C + △ E C D) := by ac_rfl

/-! ## The square named from another corner -/

/-- The square ABCD, named from B, is the square BCDA. -/
theorem Square.rotate (h : Square A B C D) : Square B C D A :=
  ⟨h.2.1, h.2.2.1, (h.1.trans (h.2.1.trans h.2.2.1)).symm, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2, h.2.2.2.1⟩

end Elements
