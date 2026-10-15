import Elements.Figure.Basics
import Elements.BookI.Prop01
import Elements.BookI.Prop03
import Elements.BookI.Prop05
import Elements.BookI.Prop07
import Elements.BookI.Prop08

/-!
# Book I, Proposition 9

Euclid's text, in Heath's translation: [`heath/I/09.md`](../../heath/I/09.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

"Bisected by the straight line AF" says two things: `AF` falls within the angle
`BAC` (`F` is on `C`'s side of `AB` and on `B`'s side of `AC`), and it cuts the
angle into two equal angles `BAF`, `FAC`. I.10 needs the first: it is what makes
the bisector of the angle `ACB` meet `AB` between `A` and `B` (`crossbar` in
Book Zero).

For `AF` to fall within the angle, the equilateral triangle on `DE` must be put
on the side of `DE` away from `A`, which Euclid does not say; I.1 lets us choose
the side.

Even then, Euclid reads off his figure that `F` falls within the angle `BAC`.
Proclus imagined an objector who doubted it, and answered him with the second
part of I.5 (Heath, vol. 1, p. 265). The lemmas before the theorem answer the
same objector in Lean: `Prop9.crossing` finds where `AF` crosses `DE`, between
`D` and `E`, and `Prop9.side` reads off the sides of `AB` and `AC` from there.
-/

namespace Elements.BookI

open Tacit

/-! ## What Euclid reads off the figure -/

/-- Euclid's chance point `D` on `AB`. He takes it at random, but in the next breath
cuts off from `AC` a straight line equal to `AD` [I. 3], so `AD` must be less than
`AC`. A circle about `A` through `C` keeps `D` in: `D` is taken between `A` and `B`
if `B` is not outside that circle, or between `A` and the point where `AB` leaves
it if `B` is outside. -/
theorem Prop9.chance_point {A B C : Point} (hAB : A ≠ B) (hAC : A ≠ C) :
    ∃ D : Point, Between A D B ∧ ‖A D‖ < ‖A C‖ := by
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  obtain ⟨α, hA_α, hC_α⟩ := Postulate3 A C hAC
  have hA_in : InsideCircle A α ∨ OnCircle A α := Or.inl (centre_inside hA_α)
  by_cases hB_α : InsideCircle B α ∨ OnCircle B α
  · /- `B` is not outside the circle: any point between `A` and `B` is inside it
       (System E, Circle 2). -/
    obtain ⟨D, -, hADB, -⟩ := exists_point_between hA_AB hB_AB hAB []
    exact ⟨D, hADB, len_lt_of_inside hA_α hC_α (inside_of_between hA_in hB_α hADB)⟩
  · /- `B` is outside: `AB` leaves the circle at a point `X` between `A` and `B`
       (Intersections 4), and `D` is taken between `A` and `X`. -/
    have hB_out : OutsideCircle B α := ⟨fun h => hB_α (Or.inl h), fun h => hB_α (Or.inr h)⟩
    obtain ⟨X, hX_α, hX_AB, hAXB⟩ := line_circle_between (centre_inside hA_α) hA_AB hB_out hB_AB
    obtain ⟨D, -, hADX, -⟩ := exists_point_between hA_AB hX_AB (ne_of_between hAXB) []
    exact ⟨D, between_of_between_left hAXB hADX,
      len_lt_of_inside hA_α hC_α (inside_of_between hA_in (Or.inr hX_α) hADX)⟩

/-- Proclus' objector, first case: `F` might fall on `AB` itself, beyond `D`. Proclus
answers him with the second part of I.5 (Heath, vol. 1, p. 265). Since `FD` is equal
to `FE`, the angle `FDE` is equal to the angle `FED` [I. 5]. Since `AD` is equal to
`AE`, the angles `EDF`, `DEC` under the base of the triangle `ADE` are equal [I. 5].
So the angle `DEF` is equal to the angle `DEC`, with `F` and `C` on the same side of
`DE`; then `F` lies on the straight line `EC` (`onRay_of_angle_eq`), that is, on `AC`.
But `AB` and `AC` meet only at `A`. -/
theorem Prop9.not_on_arm {A B C D E F : Point} (hBAC : Triangle B A C) (hADB : Between A D B)
    (hAEC : Between A E C) (hAD_AE : ‖A D‖ = ‖A E‖) (hFD_FE : ‖F D‖ = ‖F E‖)
    (hF : OppositeSidesOf F A D E) : ¬ Between A D F := by
  intro hADF
  have hDE : D ≠ E := hF.1
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hBAC.ne₁₂.symm
  obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hBAC.ne₂₃
  obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hDE
  have hFA : OppositeSides F A DE := hF.2 DE hD_DE hE_DE
  have hD_AB : OnLine D AB := on_line_of_between_ends hADB hA_AB hB_AB
  have hE_AC : OnLine E AC := on_line_of_between_ends hAEC hA_AC hC_AC
  have hADE : Triangle A D E := hF.symm.triangle.cab
  have hFDE : Triangle F D E := hF.triangle.cab
  have hFD : F ≠ D := hFDE.ne₁₂
  have hFE : F ≠ E := hFDE.ne₁₃
  /- Since `FD` is equal to `FE`, the angle `FDE` is equal to the angle `FED`. [I. 5] -/
  obtain ⟨G, hFEG⟩ := produce hFE
  have hbase : ∠ F D E = ∠ F E D := (Prop5 hFDE hFD_FE (between_symm hADF) hFEG).1
  /- Since `AD` is equal to `AE`, and `AD`, `AE` are produced to `F`, `C`, the angles
     `EDF`, `DEC` under the base are equal. [I. 5] -/
  have hunder : ∠ E D F = ∠ D E C := (Prop5 hADE hAD_AE hADF hAEC).2
  have hDEC_DEF : ∠ D E C = ∠ D E F :=
    hunder.symm.trans ((angle_symm hDE.symm hFD).trans (hbase.trans (angle_symm hFE hDE)))
  /- `C`, beyond `E` from `A`, is on the other side of `DE` from `A` (Pasch 3), as `F` is;
     so `C` and `F` are on the same side of `DE`. -/
  have hCE : C ≠ E := ne_of_between (between_symm hAEC)
  have hC_DE : ¬ OnLine C DE := fun hC =>
    hFA.2.1 ((line_unique hCE hC hE_DE hC_AC hE_AC) ▸ hA_AC)
  have hCF : SameSide C F DE :=
    same_side_of_opposite_sides ⟨hFA.2.1, hC_DE, pasch3 hAEC hE_DE⟩
      (hF.symm.oppositeSides hD_DE hE_DE)
  have hray : OnRay C E F :=
    onRay_of_angle_eq (SameSideOf.of_line hDE.symm hE_DE hD_DE hCF) hDEC_DEF
  /- So `F` is on `AC`, and on `AB`; and these meet only at `A`. -/
  have hF_AC : OnLine F AC := hray.symm.onLine hE_AC hC_AC
  have hF_AB : OnLine F AB := on_line_of_between hADF hA_AB hD_AB
  have hAB_AC : AB = AC := line_unique (ne_of_between_ends hADF) hA_AB hF_AB hA_AC hF_AC
  exact hBAC.off_line hB_AB hA_AB (hAB_AC ▸ hC_AC)

/-- Where the straight line `AF` crosses `DE`. Since `F` is on the other side of `DE`
from `A`, the straight line `AF` crosses `DE` at a point `M` (Intersection 1, Pasch
4). And `M` falls between `D` and `E`. It is not `D` or `E`: that is Proclus' first
case, `Prop9.not_on_arm`. Nor is it beyond `D` or beyond `E`: then `D` and `E` would
be on the same side of `AF`, and I.7 would make them one point, since `AD` is equal
to `AE` and `FD` to `FE`. -/
theorem Prop9.crossing {A B C D E F : Point} (hBAC : Triangle B A C) (hADB : Between A D B)
    (hAEC : Between A E C) (hAD_AE : ‖A D‖ = ‖A E‖) (hFD_FE : ‖F D‖ = ‖F E‖)
    (hF : OppositeSidesOf F A D E) : ∃ M : Point, Between A M F ∧ Between D M E := by
  have hDE : D ≠ E := hF.1
  obtain ⟨L, hD_L, hE_L⟩ := Postulate1 D E hDE
  have hFA : OppositeSides F A L := hF.2 L hD_L hE_L
  have hAF : A ≠ F := by
    intro h
    subst h
    exact hFA.2.2 (same_side_refl hFA.2.1)
  obtain ⟨N, hA_N, hF_N⟩ := Postulate1 A F hAF
  obtain ⟨hLN, M, hM_L, hM_N⟩ := lines_meet_of_opposite_sides hFA hF_N hA_N
  have hMA : M ≠ A := fun h => hFA.2.1 (h ▸ hM_L)
  have hMF : M ≠ F := fun h => hFA.1 (h ▸ hM_L)
  have hAMF : Between A M F :=
    pasch4 hLN hM_L hM_N hA_N hF_N hAF hMA.symm hMF.symm (fun h => hFA.2.2 (same_side_symm h))
  refine ⟨M, hAMF, ?_⟩
  /- `M` is not `D`, nor `E`: Proclus' first case, on either arm. -/
  have hDM : D ≠ M := by
    intro h
    rw [← h] at hAMF
    exact Prop9.not_on_arm hBAC hADB hAEC hAD_AE hFD_FE hF hAMF
  have hME : M ≠ E := by
    intro h
    rw [h] at hAMF
    exact Prop9.not_on_arm hBAC.cba hAEC hADB hAD_AE.symm hFD_FE.symm hF.swap hAMF
  /- `D` and `E` are not on the same side of `AF`, or I.7 would make them one point. -/
  have hD_N : ¬ OnLine D N := fun hD => hLN (line_unique hDM hD_L hM_L hD hM_N)
  have hE_N : ¬ OnLine E N := fun hE => hLN (line_unique hME.symm hE_L hM_L hE hM_N)
  have hI7 : ¬ SameSide D E N := fun hs =>
    hDE (Prop7 (SameSideOf.of_line hAF hA_N hF_N hs)
      (by rw [len_symm D A, hAD_AE, len_symm A E]) (by rw [len_symm D F, hFD_FE, len_symm F E]))
  rcases between_cases hDM hME hDE hD_L hM_L hE_L with h | h | h
  · exact h
  · exact absurd (pasch2 h hM_N hD_N) hI7
  · exact absurd (same_side_symm (pasch2 (between_symm h) hM_N hE_N)) hI7

/-- From where `AF` crosses `DE`, the sides of `AB`: `M`, between `D` and `E`, is on
`E`'s side of `AB`, and `F`, beyond `M` from `A`, is on `M`'s side; and `E`, between
`A` and `C`, is on `C`'s side (Pasch 2). So `F` is on `C`'s side of `AB`. -/
theorem Prop9.side {A B C D E F M : Point} (hBAC : Triangle B A C) (hADB : Between A D B)
    (hAEC : Between A E C) (hDME : Between D M E) (hAMF : Between A M F) :
    SameSideOf F C A B := by
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hBAC.ne₁₂.symm
  have hD_AB : OnLine D AB := on_line_of_between_ends hADB hA_AB hB_AB
  have hC_AB : ¬ OnLine C AB := hBAC.off_line hB_AB hA_AB
  have hE_AB : ¬ OnLine E AB := fun h => hC_AB (on_line_of_between hAEC hA_AB h)
  have hM_AB : ¬ OnLine M AB := fun h => hE_AB (on_line_of_between hDME hD_AB h)
  have hME : SameSide M E AB := pasch2 hDME hD_AB hM_AB
  have hMF : SameSide M F AB := pasch2 hAMF hA_AB hM_AB
  have hEC : SameSide E C AB := pasch2 hAEC hA_AB hE_AB
  exact SameSideOf.of_line hBAC.ne₁₂.symm hA_AB hB_AB
    (same_side_trans (same_side_trans hME hMF) hEC)

/-- To bisect a given rectilineal angle. -/
theorem Prop9 {A B C : Point} (hBAC : Triangle B A C) :
    ∃ F : Point, SameSideOf F C A B ∧ SameSideOf F B A C ∧
      ∠ B A F = ∠ F A C ∧ ∠ B A F + ∠ F A C = ∠ B A C := by
  -- Let the angle BAC be the given rectilineal angle.
  have hAB : A ≠ B := hBAC.ne₁₂.symm
  have hAC : A ≠ C := hBAC.ne₂₃
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hAC
  have hC_AB : ¬ OnLine C AB := hBAC.off_line hB_AB hA_AB
  -- It is then required to bisect it.
  -- Let a point D be taken at random on AB;
  /- At random, but not too far out, since AD is about to be cut off from AC: see
     `Prop9.chance_point`. -/
  obtain ⟨D, hADB, hAD_AC⟩ := Prop9.chance_point hAB hAC
  have hAD : A ≠ D := ne_of_between hADB
  have hD_AB : OnLine D AB := on_line_of_between_ends hADB hA_AB hB_AB
  -- let AE be cut off from AC equal to AD; [I. 3]
  obtain ⟨E, hAEC, hAE_AD⟩ := Prop3 hAD hAD_AC
  have hAE : A ≠ E := ne_of_between hAEC
  have hE_AC : OnLine E AC := on_line_of_between_ends hAEC hA_AC hC_AC
  -- let DE be joined, and on DE let the equilateral triangle DEF be constructed;
  /- E is off AB, or C would be on it; so ADE is a triangle. The equilateral triangle
     goes on the side of DE away from A, which Euclid leaves to his figure: we take a
     point Q on that side (System E, Points 6) and ask I.1 for Q's side. -/
  have hE_AB : ¬ OnLine E AB := fun h => hC_AB (on_line_of_between hAEC hA_AB h)
  have hADE : Triangle A D E := Triangle.of_line hA_AB hD_AB hAD hE_AB
  have hDE : D ≠ E := hADE.ne₂₃
  obtain ⟨Q, hQA, -⟩ := exists_oppositeSidesOf hADE.bca []
  obtain ⟨F, ⟨-, -, hEF_FD⟩, hside⟩ := Prop1 D E hDE Q
  have hFA : OppositeSidesOf F A D E := (hside hQA.triangle).trans_opposite hQA
  -- let AF be joined.
  /- Joined, AF falls within the angle BAC. That is Proclus' objector answered: AF
     crosses DE between D and E (`Prop9.crossing`, by I.5 and I.7), and from there F is
     on C's side of AB and on B's side of AC (`Prop9.side`). -/
  have hFD_FE : ‖F D‖ = ‖F E‖ := hEF_FD.symm.trans (len_symm E F)
  obtain ⟨M, hAMF, hDME⟩ := Prop9.crossing hBAC hADB hAEC hAE_AD.symm hFD_FE hFA
  have hFC : SameSideOf F C A B := Prop9.side hBAC hADB hAEC hDME hAMF
  have hFB : SameSideOf F B A C := Prop9.side hBAC.cba hAEC hADB (between_symm hDME) hAMF
  have hF_AB : ¬ OnLine F AB := hFC.triangle.off_line hA_AB hB_AB
  have hF_AC : ¬ OnLine F AC := hFB.triangle.off_line hA_AC hC_AC
  have hAF : A ≠ F := fun h => hF_AB (h ▸ hA_AB)
  -- I say that the angle BAC has been bisected by the straight line AF.
  -- For, since AD is equal to AE,
  have hAD_AE : ‖A D‖ = ‖A E‖ := hAE_AD.symm
  -- and AF is common,
  have hAF_AF : ‖A F‖ = ‖A F‖ := rfl
  -- the two sides DA, AF are equal to the two sides EA, AF respectively.
  -- And the base DF is equal to the base EF;
  have hDF_EF : ‖D F‖ = ‖E F‖ := (len_symm D F).trans hEF_FD.symm
  -- therefore the angle DAF is equal to the angle EAF. [I. 8]
  /- ADF and AEF are triangles, since F is off AB and off AC. -/
  have hADF : Triangle A D F := Triangle.of_line hA_AB hD_AB hAD hF_AB
  have hAEF : Triangle A E F := Triangle.of_line hA_AC hE_AC hAE hF_AC
  have hDAF_EAF : ∠ D A F = ∠ E A F := Prop8 hADF hAEF hAD_AE hAF_AF hDF_EF
  -- Therefore the given rectilineal angle BAC has been bisected by the straight line AF.
  /- The angle DAF is the angle BAF, since D lies on AB, and the angle EAF is the angle
     CAF, that is, FAC, since E lies on AC (an angle depends only on its rays). And
     since F lies within the angle BAC, that angle is made up of BAF and FAC
     (System E, Diagram-angle 2). -/
  have hbisect : ∠ B A F = ∠ F A C := by
    rw [← angle_onRay_left (OnRay.of_between hADB) hAF.symm, hDAF_EAF,
      angle_onRay_left (OnRay.of_between hAEC) hAF.symm, angle_symm hAC.symm hAF.symm]
  have hAB_AC : AB ≠ AC := fun h => hC_AB (h ▸ hC_AC)
  have hwhole : ∠ B A C = ∠ B A F + ∠ F A C :=
    angle_add_of_inside hA_AB hA_AC hB_AB hC_AC hAB hAC hF_AB hF_AC hAB_AC
      (same_side_symm (hFB.2 AC hA_AC hC_AC)) (same_side_symm (hFC.2 AB hA_AB hB_AB))
  exact ⟨F, hFC, hFB, hbisect, hwhole.symm⟩
  -- Q. E. F.

end Elements.BookI
