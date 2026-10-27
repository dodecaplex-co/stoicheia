import Elements.Figure.Basics
import Elements.BookI.Prop11

/-!
# Book I, Proposition 13

Euclid's text, in Heath's translation: [`heath/I/13.md`](../../heath/I/13.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid draws one figure, in which AB leans towards C, so that BA falls within
the right angle CBE. If it leans towards D instead, the argument is his with
C and D exchanged; so the Lean makes the argument once, for either way of
naming the two ends of CD, and uses it whichever way AB leans
(`Prop13.cases`).
-/

namespace Elements.BookI

open Tacit

/-! ## What Euclid reads off the figure -/

/-- Euclid's figure, seen from the other end of CD. If BA falls within the angle
CBE (A on E's side of BC, and on C's side of BE), and CB is produced to
D, then BE falls within the angle DBA: E is on A's side of BD, and on
D's side of BA.

The first is the same side of the same straight line. For the second, the three
straight lines BC, BA, BE through B divide the plane into six regions, and
since A lies between C and E as seen from B, the straight line BA separates
C from E (System E, Triple incidence 1); it also separates C from D (Pasch 3),
and a straight line has only two sides (Same side 5). -/
theorem Prop13.within {A B C D E : Point} (hCBD : Between C B D) (hAE : SameSideOf A E B C)
    (hAC : SameSideOf A C B E) : SameSideOf E A B D ∧ SameSideOf E D B A := by
  have hBC : B ≠ C := hAE.1
  have hBD : B ≠ D := (ne_of_between (between_symm hCBD)).symm
  have hBE : B ≠ E := hAC.1
  have hBA : B ≠ A := hAC.triangle.ne₁₃
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hBC
  have hD_L : OnLine D L := on_line_of_between hCBD hC_L hB_L
  obtain ⟨M, hB_M, hE_M⟩ := Postulate1 B E hBE
  obtain ⟨N, hB_N, hA_N⟩ := Postulate1 B A hBA
  have hAE_L : SameSide A E L := hAE.sameSide hB_L hC_L
  have hAC_M : SameSide A C M := hAC.sameSide hB_M hE_M
  have hA_L : ¬ OnLine A L := not_on_line_of_same_side hAE_L
  have hA_M : ¬ OnLine A M := not_on_line_of_same_side hAC_M
  refine ⟨SameSideOf.of_line hBD hB_L hD_L (same_side_symm hAE_L), ?_⟩
  /- BA separates C from E (Triple incidence 1). -/
  have hCE_N : ¬ SameSide C E N :=
    triple_incidence1 hB_L hB_N hB_M hC_L hA_N hE_M hAE_L (same_side_symm hAC_M)
  /- It also separates C from D (Pasch 3). -/
  have hCD_N : ¬ SameSide C D N := pasch3 hCBD hB_N
  /- None of C, D, E is on BA: else BA would be BC, or BE, and A would be on it. -/
  have hC_N : ¬ OnLine C N := fun hC => hA_L (line_unique hBC hB_N hC hB_L hC_L ▸ hA_N)
  have hD_N : ¬ OnLine D N := fun hD => hA_L (line_unique hBD hB_N hD hB_L hD_L ▸ hA_N)
  have hE_N : ¬ OnLine E N := fun hE => hA_M (line_unique hBE hB_N hE hB_M hE_M ▸ hA_N)
  /- So E, not on C's side of BA, is on D's (Same side 5). -/
  have hDE_N : SameSide D E N :=
    same_side_of_opposite_sides ⟨hC_N, hD_N, hCD_N⟩ ⟨hC_N, hE_N, hCE_N⟩
  exact SameSideOf.of_line hBA hB_N hA_N (same_side_symm hDE_N)

/-- Which way AB leans. With BE at right angles to CD, on A's side of it, and
the angles CBA, ABD unequal, A lies on C's side of BE or on D's.

It is not on BE itself: being on E's side of CD, it would lie on the ray from
B through E, and then the angles CBA, ABD would be the right angles CBE,
EBD themselves, and equal (Diagram-angle 4). C and D are on opposite sides of
BE (Pasch 3), and a straight line has only two sides (Same side 5). -/
theorem Prop13.cases {A B C D E : Point} (hCBD : Between C B D) (hEA : SameSideOf E A C D)
    (hCBE : ∠ C B E = ∟) (hEBD : ∠ E B D = ∟) (hne : ∠ C B A ≠ ∠ A B D) :
    SameSideOf A C B E ∨ SameSideOf A D B E := by
  have hCB : C ≠ B := ne_of_between hCBD
  have hDB : D ≠ B := ne_of_between (between_symm hCBD)
  obtain ⟨L, hC_L, hD_L⟩ := Postulate1 C D hEA.1
  have hB_L : OnLine B L := on_line_of_between_ends hCBD hC_L hD_L
  have hEA_L : SameSide E A L := hEA.sameSide hC_L hD_L
  have hE_L : ¬ OnLine E L := not_on_line_of_same_side hEA_L
  have hBE : B ≠ E := fun e => hE_L (e ▸ hB_L)
  obtain ⟨M, hB_M, hE_M⟩ := Postulate1 B E hBE
  have hC_M : ¬ OnLine C M := fun hC => hE_L (line_unique hCB hC hB_M hC_L hB_L ▸ hE_M)
  have hD_M : ¬ OnLine D M := fun hD => hE_L (line_unique hDB hD hB_M hD_L hB_L ▸ hE_M)
  have hA_M : ¬ OnLine A M := by
    intro hA
    have hAB : A ≠ B := fun e => not_on_line_of_same_side (same_side_symm hEA_L) (e ▸ hB_L)
    /- A would be on the ray from B through E, not behind B (Pasch 3,
       `OnRay.of_sameSideOf`). -/
    have hA_ray : OnRay A B E :=
      OnRay.of_sameSideOf (SameSideOf.of_line hCB.symm hB_L hC_L (same_side_symm hEA_L))
        ⟨M, hB_M, hE_M, hA⟩ hAB
    apply hne
    rw [angle_onRay_right hA_ray hCB, angle_onRay_left hA_ray hDB, hCBE, hEBD]
  rcases same_side_or hC_M hD_M hA_M (pasch3 hCBD hB_M) with h | h
  · exact Or.inl (SameSideOf.of_line hBE hB_M hE_M (same_side_symm h))
  · exact Or.inr (SameSideOf.of_line hBE hB_M hE_M (same_side_symm h))

/-- If a straight line set up on a straight line make angles, it will make either two right angles
or angles equal to two right angles. -/
theorem Prop13 {A B C D : Point} (hCBD : Between C B D) (hA : ¬ Collinear C D A) :
    ∠ C B A + ∠ A B D = ∟ + ∟ := by
  -- For let any straight line AB set up on the straight line CD make the angles CBA, ABD;
  /- The straight line CD, with B on it between C and D, and A off it. -/
  have hCB : C ≠ B := ne_of_between hCBD
  have hDB : D ≠ B := ne_of_between (between_symm hCBD)
  have hCD : C ≠ D := ne_of_between_ends hCBD
  obtain ⟨CD, hC_CD, hD_CD⟩ := Postulate1 C D hCD
  have hB_CD : OnLine B CD := on_line_of_between_ends hCBD hC_CD hD_CD
  have hA_CD : ¬ OnLine A CD := fun h => hA ⟨CD, hC_CD, hD_CD, h⟩
  have hAB : A ≠ B := fun e => hA_CD (e ▸ hB_CD)
  -- I say that the angles CBA, ABD are either two right angles or equal to two right angles.
  /- "Two right angles": each of them is right. "Equal to two right angles": together
     they make two. Our Postulate 4 makes every right angle the one `∟`, as in I.11, so
     the first is a case of the second, and the statement asks only for the second. -/
  -- Now, if the angle CBA is equal to the angle ABD,
  by_cases heq : ∠ C B A = ∠ A B D
  -- they are two right angles. [Def. 10]
  /- Definition I.10 says each is right, for they are adjacent angles (A is off the
     straight line CD); each is then `∟` (Post. 4, as in I.11). -/
  · have hCBA : ∠ C B A = ∟ :=
      Postulate4 ⟨D, hCBD, Triangle.of_line hC_CD hB_CD hCB hA_CD, heq⟩
    have hABD : ∠ A B D = ∟ := heq.symm.trans hCBA
    rw [hCBA, hABD]
  -- But, if not, let BE be drawn from the point B at right angles to CD; [I. 11]
  /- I.11 draws BE on whichever side of CD we ask; we ask for A's side. -/
  obtain ⟨E, hEA, hperp⟩ := Prop11 (A := C) (B := D) (C := B) (Q := A) hCD
    ⟨CD, hC_CD, hD_CD, hB_CD⟩ hA
  have hEB : E ≠ B := fun e => hEA.triangle.off_line hC_CD hD_CD (e ▸ hB_CD)
  -- therefore the angles CBE, EBD are two right angles.
  have hCBE : ∠ C B E = ∟ := hperp C ⟨CD, hC_CD, hD_CD, hC_CD⟩ hCB
  have hDBE : ∠ D B E = ∟ := hperp D ⟨CD, hC_CD, hD_CD, hD_CD⟩ hDB
  have hEBD : ∠ E B D = ∟ := by rw [angle_symm hEB hDB]; exact hDBE
  have hEBC : ∠ E B C = ∟ := by rw [angle_symm hEB hCB]; exact hCBE
  /- In Euclid's figure BA falls within the angle CBE: A is on E's side of BC, and on
     C's side of BE. If A is on D's side of BE instead, the figure is Euclid's with C
     and D exchanged (`Prop13.cases`), so we give his argument for either naming of
     the ends of CD, and use it below. A is on E's side of CD, as I.11 put it, and so
     of BC and of BD, which are the same straight line. -/
  have hAE_BC : SameSideOf A E B C :=
    SameSideOf.of_line hCB.symm hB_CD hC_CD (same_side_symm (hEA.sameSide hC_CD hD_CD))
  have hAE_BD : SameSideOf A E B D :=
    SameSideOf.of_line hDB.symm hB_CD hD_CD (same_side_symm (hEA.sameSide hC_CD hD_CD))
  have two_right : ∀ {C D : Point}, Between C B D → ∠ C B E = ∟ → ∠ E B D = ∟ →
      SameSideOf A E B C → SameSideOf A C B E → ∠ D B A + ∠ A B C = ∟ + ∟ := by
    intro C D hCBD hCBE hEBD hAE hAC
    have hCB : C ≠ B := ne_of_between hCBD
    have hDB : D ≠ B := ne_of_between (between_symm hCBD)
    -- Then, since the angle CBE is equal to the two angles CBA, ABE,
    /- BA falls within the angle CBE. -/
    have hCBE_sum : ∠ C B E = ∠ C B A + ∠ A B E := angle_add_of_within hAE hAC
    -- let the angle EBD be added to each;
    -- therefore the angles CBE, EBD are equal to the three angles CBA, ABE, EBD. [C.N. 2]
    have hthree : ∠ C B E + ∠ E B D = ∠ C B A + ∠ A B E + ∠ E B D :=
      CommonNotion2 hCBE_sum rfl
    -- Again, since the angle DBA is equal to the two angles DBE, EBA,
    /- And so BE falls within the angle DBA (`Prop13.within`). -/
    obtain ⟨hEA', hED⟩ := Prop13.within hCBD hAE hAC
    have hDBA_sum : ∠ D B A = ∠ D B E + ∠ E B A := angle_add_of_within hEA' hED
    -- let the angle ABC be added to each;
    -- therefore the angles DBA, ABC are equal to the three angles DBE, EBA, ABC. [C.N. 2]
    have hthree' : ∠ D B A + ∠ A B C = ∠ D B E + ∠ E B A + ∠ A B C :=
      CommonNotion2 hDBA_sum rfl
    -- But the angles CBE, EBD were also proved equal to the same three angles;
    /- The same three, named from the other end and added in the other order: the
       angle CBA is the angle ABC (System E, Metric 4), and the order of adding does
       not matter (a tacit rule of magnitude). -/
    have hsame : ∠ C B E + ∠ E B D = ∠ D B E + ∠ E B A + ∠ A B C := by
      rw [hthree, angle_symm hCB hAB, angle_symm hAB hEB, angle_symm hEB hDB,
        add_comm (∠ A B C + ∠ E B A), add_comm (∠ A B C), ← add_assoc]
    -- and things which are equal to the same thing are also equal to one another; [C.N. 1]
    -- therefore the angles CBE, EBD are also equal to the angles DBA, ABC.
    have hequal : ∠ C B E + ∠ E B D = ∠ D B A + ∠ A B C := CommonNotion1 hsame hthree'
    -- But the angles CBE, EBD are two right angles;
    have hright : ∠ C B E + ∠ E B D = ∟ + ∟ := by rw [hCBE, hEBD]
    -- therefore the angles DBA, ABC are also equal to two right angles.
    exact hequal.symm.trans hright
  -- Therefore etc.
  rcases Prop13.cases hCBD hEA hCBE hEBD heq with hAC | hAD
  · /- This is Euclid's figure. -/
    rw [angle_symm hCB hAB, angle_symm hAB hDB, add_comm (∠ A B C)]
    exact two_right hCBD hCBE hEBD hAE_BC hAC
  · /- This is Euclid's figure with C and D exchanged. -/
    exact two_right (between_symm hCBD) hDBE hEBC hAE_BD hAD
  -- Q. E. D.

/-- A right angle is equal to the angle adjacent to it (System E, Diagram-angle 3).
We prove it from I.13 and Common Notion 3: the two adjacent angles together equal two
right angles, and taking the given right angle away leaves one right angle. -/
theorem _root_.Elements.Tacit.adjacent_eq_of_right
    {A B C D : Point} {L : Line}
    (hA : OnLine A L) (hB : OnLine B L) (h : Between A C B)
    (hD : ¬ OnLine D L) (hright : ∠ A C D = ∟) : ∠ A C D = ∠ D C B := by
  have hABD : Triangle A B D :=
    Triangle.of_line hA hB (ne_of_between_ends h) hD
  have h13 := Prop13 h hABD
  rw [hright, add_comm ∟] at h13
  rw [hright]
  exact (CommonNotion3 h13 rfl).symm

/-- When one side condition holds, so does the other. Were it to fail, C would lie within
the angle BAD; and since the angle DAC is greater than nothing, each of the angles BAC,
BAD would then be less than the other. -/
private theorem inside_of_angle_add_one_side {A B C D : Point} {L M : Line}
    (hAL : OnLine A L) (hAM : OnLine A M) (hB : OnLine B L)
    (hC : OnLine C M) (hAB : A ≠ B) (hAC : A ≠ C)
    (hDL : ¬ OnLine D L) (hDM : ¬ OnLine D M) (hLM : L ≠ M)
    (h : ∠ B A C = ∠ B A D + ∠ D A C) (hCD : SameSide C D L) :
    SameSide B D M := by
  apply Classical.byContradiction
  intro hn
  have hAD : A ≠ D := fun e => hDL (e ▸ hAL)
  obtain ⟨N, hAN, hDN⟩ := Postulate1 A D hAD
  have hCL : ¬ OnLine C L := fun hc => hLM (line_unique hAC hAL hc hAM hC)
  have hCN : ¬ OnLine C N := fun hc =>
    hDM (line_unique hAC hAN hc hAM hC ▸ hDN)
  have hLN : L ≠ N := fun e => hDL (e ▸ hDN)
  have hBC : SameSide B C N :=
    triple_incidence2 hAL hAM hAN hB hC hDN hCD hn hDM hAB.symm
  have hadd := angle_add_of_inside hAL hAN hB hDN hAB hAD hCL hCN hLN
    hBC (same_side_symm hCD)
  have hp : 0 < ∠ D A C := (Triangle.of_line hC hAM hAC.symm hDM).cba.angle_pos
  rw [angle_symm hAC.symm hAD.symm] at hadd
  have hlt := CommonNotion5 (a := ∠ B A C) hp
  rw [← hadd] at hlt
  have hlt' := CommonNotion5 (a := ∠ B A D) hp
  rw [← h] at hlt'
  exact lt_irrefl _ (lt_trans hlt hlt')

/-- An angle of a triangle is less than two right angles. Produce BA beyond A to E: by
I.13 the angles BAC, CAE make two right angles, and CAE is greater than nothing. -/
theorem Prop13.angle_lt_two_right {A B C : Point} (h : Triangle B A C) :
    ∠ B A C < ∟ + ∟ := by
  obtain ⟨L, hB, hA⟩ := Postulate1 B A h.ne₁₂
  obtain ⟨E, hE, hBAE, _⟩ := Postulate2 hB hA h.ne₁₂ []
  have hC := h.off_line hB hA
  have h13 := Prop13 hBAE
    (Triangle.of_line hB hE (ne_of_between_ends hBAE) hC)
  have hp : 0 < ∠ C A E :=
    (Triangle.of_line hE hA (ne_of_between (between_symm hBAE)) hC).cba.angle_pos
  have hlt := CommonNotion5 (a := ∠ B A C) hp
  rw [h13] at hlt
  exact hlt

/-- If the angle BAC is made up of BAD and DAC, then D lies within it (System E,
Diagram-angle 2, converse). We prove it from I.13, the adding of angles, the fact
that an angle of a triangle is greater than nothing, and the rules for the sides of a
straight line. If just one side condition fails, one angle would be less than itself.
If both fail, producing DA through A gives two decompositions whose sum forces BAC
to equal two right angles, contrary to I.13, for the angle adjacent to BAC is greater
than nothing. -/
theorem _root_.Elements.Tacit.inside_of_angle_add {A B C D : Point} {L M : Line}
    (hAL : OnLine A L) (hAM : OnLine A M) (hB : OnLine B L)
    (hC : OnLine C M) (hAB : A ≠ B) (hAC : A ≠ C) (hDL : ¬ OnLine D L) (hDM : ¬ OnLine D M)
    (hLM : L ≠ M) (h : ∠ B A C = ∠ B A D + ∠ D A C) : SameSide B D M ∧ SameSide C D L := by
  have hAD : A ≠ D := fun e => hDL (e ▸ hAL)
  have hflip : ∠ C A B = ∠ C A D + ∠ D A B := by
    rw [angle_symm hAC.symm hAB.symm, angle_symm hAC.symm hAD.symm,
      angle_symm hAD.symm hAB.symm, add_comm]
    exact h
  by_cases hCD : SameSide C D L
  · exact ⟨inside_of_angle_add_one_side hAL hAM hB hC hAB hAC hDL hDM hLM h hCD, hCD⟩
  by_cases hBD : SameSide B D M
  · exact ⟨hBD, inside_of_angle_add_one_side hAM hAL hC hB hAC hAB hDM hDL
      hLM.symm hflip hBD⟩
  have hCL : ¬ OnLine C L := fun hc => hLM (line_unique hAC hAL hc hAM hC)
  have hBM : ¬ OnLine B M := fun hb => hLM (line_unique hAB hAL hB hAM hb)
  obtain ⟨N, hAN, hDN⟩ := Postulate1 A D hAD
  obtain ⟨E, hEN, hDAE, _⟩ := Postulate2 hDN hAN hAD.symm []
  have hEL : ¬ OnLine E L := fun he =>
    hDL (on_line_of_between (between_symm hDAE) he hAL)
  have hEM : ¬ OnLine E M := fun he =>
    hDM (on_line_of_between (between_symm hDAE) he hAM)
  have hCE : SameSide C E L := by
    rcases same_side_or hCL hDL hEL hCD with hs | hs
    · exact hs
    · exact False.elim (pasch3 hDAE hAL hs)
  have hBE : SameSide B E M := by
    rcases same_side_or hBM hDM hEM hBD with hs | hs
    · exact hs
    · exact False.elim (pasch3 hDAE hAM hs)
  have he := angle_add_of_inside hAL hAM hB hC hAB hAC hEL hEM hLM hBE hCE
  have hBN : ¬ OnLine B N := fun hb =>
    hDL (line_unique hAB hAN hb hAL hB ▸ hDN)
  have hCN : ¬ OnLine C N := fun hc =>
    hDM (line_unique hAC hAN hc hAM hC ▸ hDN)
  have hb13 := Prop13 hDAE
    (Triangle.of_line hDN hEN (ne_of_between_ends hDAE) hBN)
  have hc13 := Prop13 hDAE
    (Triangle.of_line hDN hEN (ne_of_between_ends hDAE) hCN)
  rw [angle_symm hAD.symm hAB.symm] at hb13
  rw [angle_symm hAC.symm (ne_of_between (between_symm hDAE))] at hc13
  have heq : ∠ B A C + ∠ B A C = (∟ + ∟) + (∟ + ∟) := calc
    ∠ B A C + ∠ B A C =
        (∠ B A D + ∠ D A C) + (∠ B A E + ∠ E A C) := CommonNotion2 h he
    _ = (∠ B A D + ∠ B A E) + (∠ D A C + ∠ E A C) := by ac_rfl
    _ = (∟ + ∟) + (∟ + ∟) := CommonNotion2 hb13 hc13
  have hequal := Magnitude.eq_of_add_self_eq heq
  have hlt := Prop13.angle_lt_two_right (Triangle.of_line hB hAL hAB.symm hCL)
  exact False.elim (Magnitude.ne_of_lt hlt hequal)

end Elements.BookI
