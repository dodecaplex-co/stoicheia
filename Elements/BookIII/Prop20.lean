import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Helpers
import Elements.BookI.Prop05
import Elements.BookI.Prop13
import Elements.BookI.Prop32
import Elements.BookIII.Prop02

/-!
# Book III, Proposition 20

Euclid's text, in Heath's translation: [`heath/III/20.md`](../../heath/III/20.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Heath observes that Euclid "had no idea of III. 20 applying *in terms* … to the case where
the angle at the circumference, or the angle in the segment, is *obtuse*", and that III.21
and III.26, to cover every case, need "angles at the centre" equal to or greater than two
right angles (vol. 2, pp. 48–49, 57). Our angles, `∠ B E C`, are always less than two right
angles. So III.20 here speaks of the angle at the centre standing on a circumference, which
may be two right angles or more. That reading is ours, made after Heath's notes, and not
Euclid's.

* **The angle at the centre**, `angleAtCentre α B K C`, is a word of the foundations, with
  Book III's other definitions: the angle at the centre of the circle α standing on the
  circumference BKC. It is defined as Euclid draws it in III.20: a diameter AEF, with A and
  F on opposite sides of BC and F on K's side, divides it into the angles BEF and FEC, and
  it is the two together. It is a magnitude of the angle kind, and may be two right angles
  or more. It uses no new primitive and no axiom.
* **Its bridge**, below. It does not depend on the diameter chosen
  (`angleAtCentre.diameter`), on the centre (a circle has one), or on the point K naming the
  side (`angleAtCentre.congr`). It is the angle BEC when E lies on the other side of BC from
  K (`angleAtCentre.within`); two right angles when E is on BC
  (`angleAtCentre.semicircle`); and, when E lies on K's side, the angle that with BEC makes
  four right angles (`angleAtCentre.reflex`): BEF with AEB, and FEC with AEC, are each two
  right angles [I. 13], and AEB, AEC make up BEC. That angle is greater than two right
  angles (`angleAtCentre.reflex_gt`), so the angle at the centre is less than two right
  angles, two right angles, or greater, as the centre lies (`angleAtCentre.size`).
* **III.20 for every angle at the centre**, `Prop20`, by Euclid's own proof: the diameter
  AEF, the isosceles triangles and I.32, then the sum of BEF and FEC (his first figure,
  which now covers the centre within the angle BAC, on BC, or beyond it) or their
  difference (his second figure). Two companions follow it. `Prop20.special` is III.20
  with the centre given on A's side of BC, where the angle at the centre is the angle BEC:
  the statement III.20 had before, which the propositions that ask only for the angle BEC
  cite. `Prop20.circumference` shows that our measure of the circumference BKC is, in every
  case, the angle at the centre standing on it.

That BEF and FEC make up the angle at the centre, wherever the centre is, is the bridge's
work, done once. The proof cites I.13 and III.2, which Heath's brackets for III.20 do not
give: I.13 in the bridge, for the angles about the centre; III.2 in the bridge, and in the
first figure, where the crossing X of AF with BC is within the circle, so that F lies
across BC from A. It also writes out the case Euclid leaves out, the centre on AB or on AC.
-/

namespace Elements.BookIII

open Tacit

variable {A B C E F K : Point} {α : Circle}

/-- If E lies between A and F, and A and E are on opposite sides of BC, then F is on
E's side: AE crosses BC, and EF does not cross it again. -/
private theorem sameSideOf_beyond (hAEF : Between A E F) (hAE : OppositeSidesOf A E B C) :
    SameSideOf F E B C := by
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hAE.1
  have h := hAE.oppositeSides hB_L hC_L
  obtain ⟨X, hX_L, hAXE⟩ := h.exists_between
  have hXEF : Between X E F := between_inner hAXE hAEF
  exact (SameSideOf.of_line hAE.1 hB_L hC_L (pasch2 hXEF hX_L h.2.1)).symm

/-- **Where the centre lies, and what the diameter's two angles make.** Let AEF be a
diameter, A and F on opposite sides of BC, F on K's side. AF crosses BC at a point X
within the circle [III. 2], and so between B and C; the centre E is on A's side of X, at
X, or on F's side. On A's side, the angles BEF, FEC make up the angle BEC; at X, E is on
BC and they are two right angles [I. 13]; on F's side, with the angle BEC they make four
right angles, for each with the angle it makes with EA is two right angles [I. 13], and
EA falls within the angle BEC. [I. 13, III. 2] -/
private theorem diameter_cases (hE : Centre E α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hA : OnCircle A α) (hF : OnCircle F α) (hAEF : Between A E F)
    (hAK : OppositeSidesOf A K B C) (hFK : SameSideOf F K B C) :
    (OppositeSidesOf E K B C ∧ ∠ B E F + ∠ F E C = ∠ B E C) ∨
    (Between B E C ∧ ∠ B E F + ∠ F E C = ∟ + ∟) ∨
    (SameSideOf E K B C ∧ ∠ B E F + ∠ F E C + ∠ B E C = ∟ + ∟ + (∟ + ∟)) := by
  have hBC : B ≠ C := hAK.1
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hBC
  have hAF_L : OppositeSides A F L := (hFK.trans_opposite hAK.symm).symm.oppositeSides hB_L hC_L
  have hA_L : ¬ OnLine A L := hAF_L.1
  /- AF crosses BC at X, within the circle, and so between B and C. -/
  obtain ⟨X, hX_L, hAXF⟩ := hAF_L.exists_between
  have hBXC : Between B X C :=
    between_of_inside_chord hX_L hB_L hC_L (Prop2 hA hF X hAXF) hB hC hBC
  have hBE : B ≠ E := ne_of_centre_of_on hE hB
  have hCE : C ≠ E := ne_of_centre_of_on hE hC
  have hAE : A ≠ E := ne_of_between hAEF
  have hAX : A ≠ X := ne_of_between hAXF
  obtain ⟨N, hA_N, hF_N⟩ := Postulate1 A F (ne_of_between_ends hAEF)
  have hE_N : OnLine E N := on_line_of_between_ends hAEF hA_N hF_N
  have hX_N : OnLine X N := on_line_of_between_ends hAXF hA_N hF_N
  by_cases hEX : E = X
  · /- E is on BC. -/
    subst hEX
    exact Or.inr (Or.inl ⟨hBXC, BookI.Prop13 hBXC hFK.triangle⟩)
  rcases between_cases hAE hEX hAX hA_N hE_N hX_N with hAEX | hEAX | hAXE
  · /- E is on A's side of BC, and X on the ray from E through F. -/
    have hE_L : ¬ OnLine E L := fun h => hA_L (on_line_of_between (between_symm hAEX) hX_L h)
    have hEK : OppositeSidesOf E K B C :=
      (SameSideOf.of_line hBC hB_L hC_L (pasch2 (between_symm hAEX) hX_L hE_L)).trans_opposite hAK
    have hXray : OnRay X E F := OnRay.of_between (between_inner hAEX hAXF)
    refine Or.inl ⟨hEK, ?_⟩
    rw [angle_add_of_between hEK.triangle hBXC, angle_onRay_right hXray hBE,
      angle_onRay_left hXray hCE]
  · exact absurd hEAX (OnRay.not_between (OnRay.of_between hAEF) (OnRay.of_between hAXF))
  · /- E is on F's side of BC, and X on the ray from E through A. -/
    have hE_L : ¬ OnLine E L := fun h => hA_L (on_line_of_between (between_symm hAXE) h hX_L)
    have hEK : SameSideOf E K B C :=
      (SameSideOf.of_line hBC hB_L hC_L (pasch2 (between_inner hAXE hAEF) hX_L hE_L)).trans hFK
    have hXray : OnRay X E A := OnRay.of_between (between_symm hAXE)
    /- B and C are off the diameter AF, which meets BC only at X. -/
    have hB_N : ¬ OnLine B N := fun h =>
      hA_L (line_unique (ne_of_between hBXC) h hX_N hB_L hX_L ▸ hA_N)
    have hC_N : ¬ OnLine C N := fun h =>
      hA_L (line_unique (ne_of_between (between_symm hBXC)) h hX_N hC_L hX_L ▸ hA_N)
    have hAFB : Triangle A F B := Triangle.of_line hA_N hF_N (ne_of_between_ends hAEF) hB_N
    have hAFC : Triangle A F C := Triangle.of_line hA_N hF_N (ne_of_between_ends hAEF) hC_N
    have h13 : ∟ + ∟ + (∟ + ∟) = ∠ A E B + ∠ B E F + (∠ A E C + ∠ C E F) := by
      rw [BookI.Prop13 hAEF hAFB, BookI.Prop13 hAEF hAFC]
    refine Or.inr (Or.inr ⟨hEK, ?_⟩)
    rw [h13, angle_add_of_between hEK.triangle hBXC, angle_onRay_right hXray hBE,
      angle_onRay_left hXray hCE, angle_symm hBE hAE, angle_symm (ne_of_between (between_symm hAEF)) hCE]
    ac_rfl

/-- The centre on the other side of BC from K: the diameter's angles make up BEC. -/
private theorem diameter_within (hE : Centre E α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hA : OnCircle A α) (hF : OnCircle F α) (hAEF : Between A E F)
    (hAK : OppositeSidesOf A K B C) (hFK : SameSideOf F K B C) (hEK : OppositeSidesOf E K B C) :
    ∠ B E F + ∠ F E C = ∠ B E C := by
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hAK.1
  rcases diameter_cases hE hB hC hA hF hAEF hAK hFK with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · exact absurd (on_line_of_between_ends h hB_L hC_L) (hEK.triangle.off_line hB_L hC_L)
  · exact absurd (h.sameSide hB_L hC_L) (hEK.oppositeSides hB_L hC_L).2.2

/-- The centre on K's side of BC: with BEC, the diameter's angles make four right angles. -/
private theorem diameter_beyond (hE : Centre E α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hA : OnCircle A α) (hF : OnCircle F α) (hAEF : Between A E F)
    (hAK : OppositeSidesOf A K B C) (hFK : SameSideOf F K B C) (hEK : SameSideOf E K B C) :
    ∠ B E F + ∠ F E C + ∠ B E C = ∟ + ∟ + (∟ + ∟) := by
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hAK.1
  rcases diameter_cases hE hB hC hA hF hAEF hAK hFK with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd (hEK.sameSide hB_L hC_L) (h.oppositeSides hB_L hC_L).2.2
  · exact absurd (on_line_of_between_ends h hB_L hC_L) (hEK.triangle.off_line hB_L hC_L)
  · exact h

/-- **Any such diameter gives the same angle.** Two diameters through the centre E, each
with its ends on opposite sides of BC, divide the angle at the centre into angles whose
sums are equal: both are the angle BEC, or both two right angles, or both what with the
angle BEC makes four right angles, as E lies. [I. 13, III. 2, C.N. 3] -/
private theorem diameter_eq {A' F' : Point} (hE : Centre E α) (hB : OnCircle B α)
    (hC : OnCircle C α) (hA : OnCircle A α) (hF : OnCircle F α) (hAEF : Between A E F)
    (hAK : OppositeSidesOf A K B C) (hFK : SameSideOf F K B C) (hA' : OnCircle A' α)
    (hF' : OnCircle F' α) (hA'EF' : Between A' E F') (hA'K : OppositeSidesOf A' K B C)
    (hF'K : SameSideOf F' K B C) :
    ∠ B E F + ∠ F E C = ∠ B E F' + ∠ F' E C := by
  rcases diameter_cases hE hB hC hA hF hAEF hAK hFK with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩
  · rw [e, diameter_within hE hB hC hA' hF' hA'EF' hA'K hF'K h]
  · rw [e, BookI.Prop13 h hF'K.triangle]
  · exact CommonNotion3 (e.trans (diameter_beyond hE hB hC hA' hF' hA'EF' hA'K hF'K h).symm) rfl

/-- **The angle at the centre is made up of the angles of any such diameter.** For the
centre E, and any diameter AEF with A and F on opposite sides of BC, F on K's side, the
angle at the centre standing on the circumference BKC is the angles BEF, FEC together.
Lean's choice took some centre and some such diameter; the centre is E, for a circle has
one centre (`centre_unique`), and the diameter makes no difference (above).
[I. 13, III. 2] -/
theorem angleAtCentre.diameter (hE : Centre E α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hA : OnCircle A α) (hF : OnCircle F α) (hAEF : Between A E F)
    (hAK : OppositeSidesOf A K B C) (hFK : SameSideOf F K B C) :
    angleAtCentre α B K C = ∠ B E F + ∠ F E C := by
  obtain ⟨E', A', F', hE', hA', hF', hA'E'F', hA'K, hF'K, hx⟩ := Classical.epsilon_spec
    (p := fun x => ∃ E A F : Point, Centre E α ∧ OnCircle A α ∧ OnCircle F α ∧
      Between A E F ∧ OppositeSidesOf A K B C ∧ SameSideOf F K B C ∧
      x = ∠ B E F + ∠ F E C)
    ⟨_, E, A, F, hE, hA, hF, hAEF, hAK, hFK, rfl⟩
  obtain rfl := centre_unique hE' hE
  unfold angleAtCentre
  rw [hx]
  exact diameter_eq hE hB hC hA' hF' hA'E'F' hA'K hF'K hA hF hAEF hAK hFK

/-- **The circumference BKC is the circumference BK'C**, for any K' on K's side of BC, and
so is the angle at the centre standing on it: the diameters that measure them are the
same diameters. -/
theorem angleAtCentre.congr {K' : Point} (hK : SameSideOf K K' B C) :
    angleAtCentre α B K C = angleAtCentre α B K' C := by
  unfold angleAtCentre
  congr 1
  funext x
  apply propext
  constructor
  · rintro ⟨E, A, F, hE, hA, hF, hAEF, hAK, hFK, rfl⟩
    exact ⟨E, A, F, hE, hA, hF, hAEF, (hK.symm.trans_opposite hAK.symm).symm, hFK.trans hK, rfl⟩
  · rintro ⟨E, A, F, hE, hA, hF, hAEF, hAK', hFK', rfl⟩
    exact ⟨E, A, F, hE, hA, hF, hAEF, (hK.trans_opposite hAK'.symm).symm, hFK'.trans hK.symm, rfl⟩

/-- **The angle at the centre, the centre on the other side of BC from K,** is the angle
BEC itself: less than two right angles, as Euclid's angles at the centre are. A point P of
the circumference BKC (`Prop2.sameSide`, from III.2) and the diameter through it, ending
at Q on the centre's side, divide it into BEP and PEC. [I. 13, III. 2] -/
theorem angleAtCentre.within (hE : Centre E α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hEK : OppositeSidesOf E K B C) : angleAtCentre α B K C = ∠ B E C := by
  obtain ⟨P, hP, hPK⟩ := Prop2.sameSide hB hC hEK.symm.triangle
  have hPE : P ≠ E := ne_of_centre_of_on hE hP
  obtain ⟨N, hP_N, hE_N⟩ := Postulate1 P E hPE
  obtain ⟨Q, hQ, -, hQEP⟩ := line_circle_beyond (centre_inside hE) hE_N hP_N hPE
  have hQK : OppositeSidesOf Q K B C :=
    (sameSideOf_beyond (between_symm hQEP) (hPK.trans_opposite hEK.symm)).trans_opposite hEK
  rw [angleAtCentre.diameter hE hB hC hQ hP hQEP hQK hPK]
  exact diameter_within hE hB hC hQ hP hQEP hQK hPK hEK

/-- **The angle at the centre, the centre on BC,** standing on a semicircle, is two right
angles: the diameter through a point A of the other circumference (`Prop2.oppositeSide`,
from III.2) makes with BC two angles equal to two right angles. [I. 13, III. 2] -/
theorem angleAtCentre.semicircle (hE : Centre E α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hBEC : Between B E C) (hK : Triangle B C K) : angleAtCentre α B K C = ∟ + ∟ := by
  obtain ⟨A, hA, hAK⟩ := Prop2.oppositeSide hB hC hK
  have hAE : A ≠ E := ne_of_centre_of_on hE hA
  obtain ⟨N, hA_N, hE_N⟩ := Postulate1 A E hAE
  obtain ⟨F, hF, -, hFEA⟩ := line_circle_beyond (centre_inside hE) hE_N hA_N hAE
  have hAEF : Between A E F := between_symm hFEA
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hK.ne₁₂
  have hE_L : OnLine E L := on_line_of_between_ends hBEC hB_L hC_L
  have hA_L : ¬ OnLine A L := hAK.triangle.off_line hB_L hC_L
  have hF_L : ¬ OnLine F L := fun h => hA_L (on_line_of_between hFEA h hE_L)
  have hFK : SameSideOf F K B C :=
    OppositeSidesOf.sameSideOf
      (OppositeSidesOf.of_line hK.ne₁₂ hB_L hC_L ⟨hA_L, hF_L, pasch3 hAEF hE_L⟩) hAK
  rw [angleAtCentre.diameter hE hB hC hA hF hAEF hAK hFK]
  exact BookI.Prop13 hBEC hFK.triangle

/-- **The angle at the centre, the centre on K's side of BC,** standing on a circumference
greater than a semicircle, is the angle that with the angle BEC makes four right angles:
the diameter AEF divides it into BEF and FEC; BEF with AEB, and FEC with AEC, are each
two right angles [I. 13], and AEB, AEC make up BEC, for EA falls within the angle BEC.
The diameter from a point A of the other circumference (`Prop2.oppositeSide`, from
III.2) ends on K's side. [I. 13, III. 2] -/
theorem angleAtCentre.reflex (hE : Centre E α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hEK : SameSideOf E K B C) :
    angleAtCentre α B K C + ∠ B E C = ∟ + ∟ + (∟ + ∟) := by
  obtain ⟨A, hA, hAK⟩ := Prop2.oppositeSide hB hC hEK.symm.triangle
  have hAE : A ≠ E := ne_of_centre_of_on hE hA
  obtain ⟨N, hA_N, hE_N⟩ := Postulate1 A E hAE
  obtain ⟨F, hF, -, hFEA⟩ := line_circle_beyond (centre_inside hE) hE_N hA_N hAE
  have hAEF : Between A E F := between_symm hFEA
  have hFK : SameSideOf F K B C :=
    (sameSideOf_beyond hAEF (hEK.trans_opposite hAK.symm).symm).trans hEK
  rw [angleAtCentre.diameter hE hB hC hA hF hAEF hAK hFK]
  exact diameter_beyond hE hB hC hA hF hAEF hAK hFK hEK

/-- **The angle at the centre, the centre on K's side of BC, is greater than two right
angles.** With the angle BEC it makes four right angles (`angleAtCentre.reflex`), and the
angle BEC, an angle of a triangle, is less than two, as I.13's
`Prop13.angle_lt_two_right` proves. [I. 13, III. 2] -/
theorem angleAtCentre.reflex_gt (hE : Centre E α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hEK : SameSideOf E K B C) : ∟ + ∟ < angleAtCentre α B K C := by
  have hlt :=
    add_lt_add_right (∟ + ∟) (BookI.Prop13.angle_lt_two_right hEK.triangle.acb)
  rw [← angleAtCentre.reflex hE hB hC hEK, add_comm (∠ B E C)] at hlt
  exact Magnitude.lt_of_add_lt_add_right hlt

/-- **The angle at the centre against two right angles.** As the centre E lies on the
other side of BC from K, on BC, or on K's side, the angle at the centre standing on the
circumference BKC is less than two right angles (the angle BEC), two right angles, or
greater. The centre on the straight line BC is between B and C, for it is within the
circle (Circle 1). [I. 13, III. 2] -/
theorem angleAtCentre.size (hE : Centre E α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hK : Triangle B C K) :
    (OppositeSidesOf E K B C ∧ angleAtCentre α B K C < ∟ + ∟) ∨
    (Between B E C ∧ angleAtCentre α B K C = ∟ + ∟) ∨
    (SameSideOf E K B C ∧ ∟ + ∟ < angleAtCentre α B K C) := by
  obtain ⟨N, hB_N, hC_N⟩ := Postulate1 B C hK.ne₁₂
  by_cases hE_N : OnLine E N
  · have hBEC : Between B E C :=
      between_of_inside_chord hE_N hB_N hC_N (centre_inside hE) hB hC hK.ne₁₂
    exact Or.inr (Or.inl ⟨hBEC, angleAtCentre.semicircle hE hB hC hBEC hK⟩)
  by_cases hs : SameSide E K N
  · have hEK : SameSideOf E K B C := SameSideOf.of_line hK.ne₁₂ hB_N hC_N hs
    exact Or.inr (Or.inr ⟨hEK, angleAtCentre.reflex_gt hE hB hC hEK⟩)
  · have hEK : OppositeSidesOf E K B C :=
      OppositeSidesOf.of_line hK.ne₁₂ hB_N hC_N ⟨hE_N, hK.off_line hB_N hC_N, hs⟩
    refine Or.inl ⟨hEK, ?_⟩
    rw [angleAtCentre.within hE hB hC hEK]
    exact BookI.Prop13.angle_lt_two_right hEK.triangle.acb

/-- **The centre in Euclid's second figure.** When the centre E and the point C lie on
opposite sides of DB, E lies on D's side of BC, so that the angle at the centre is the
angle BEC (`angleAtCentre.within`). EC crosses DB at a point within the circle, between
the centre and C, and so between D and B; that point is on D's side of BC, and so is E.
Euclid reads it off his figure. -/
theorem Prop20.across_side {B C D E : Point} {ABC : Circle} (hE : Centre E ABC)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hD : OnCircle D ABC) (hBCD : Triangle B C D)
    (hEC : OppositeSidesOf E C D B) : SameSideOf E D B C := by
  have hDB : D ≠ B := hEC.1
  obtain ⟨L, hD_L, hB_L⟩ := Postulate1 D B hDB
  obtain ⟨Y, hY_L, hEYC⟩ := (hEC.2 L hD_L hB_L).exists_between
  have hY_in : InsideCircle Y ABC := InsideCircle.of_between_centre hE hC hEYC
  have hDYB : Between D Y B := between_of_inside_chord hY_L hD_L hB_L hY_in hD hB hDB
  obtain ⟨N, hB_N, hC_N⟩ := Postulate1 B C hBCD.ne₁₂
  have hD_N : ¬ OnLine D N := hBCD.off_line hB_N hC_N
  have hY_N : ¬ OnLine Y N := fun h => hD_N (on_line_of_between (between_symm hDYB) hB_N h)
  exact SameSideOf.of_line hBCD.ne₁₂ hB_N hC_N
    (same_side_trans (pasch2 (between_symm hEYC) hC_N hY_N) (pasch2 (between_symm hDYB) hB_N hY_N))

/-- In a circle the angle at the centre is double of the angle at the circumference, when the angles
have the same circumference as base. -/
theorem Prop20 {A B C K : Point} {ABC : Circle} (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hAK : OppositeSidesOf A K B C) :
    angleAtCentre ABC B K C = ∠ B A C + ∠ B A C := by
  -- Let ABC be a circle, let the angle BEC be an angle at its centre, and the angle BAC an
  -- angle at the circumference, and let them have the same circumference BC as base;
  -- I say that the angle BEC is double of the angle BAC.
  /- The point K names the circumference BC on which both angles stand, on the other side of
     BC from A. "The angle BEC" at the centre is the angle standing on it, `angleAtCentre`:
     the angle BEC itself when E is on A's side of BC, two right angles when E is on BC, and
     more when E lies beyond BC (`angleAtCentre.size`). -/
  obtain ⟨E, hE⟩ := exists_centre ABC
  have hBCA : Triangle B C A := hAK.triangle
  have hAE : A ≠ E := ne_of_centre_of_on hE hA
  have hAB : A ≠ B := hBCA.ne₁₃.symm
  have hAC : A ≠ C := hBCA.ne₂₃.symm
  -- For let AE be joined and drawn through to F.
  obtain ⟨AE, hA_AE, hE_AE⟩ := Postulate1 A E hAE
  obtain ⟨F, hF, hF_AE, hFEA⟩ := line_circle_beyond (centre_inside hE) hE_AE hA_AE hAE
  have hAEF : Between A E F := between_symm hFEA
  /- We write Euclid's isosceles-triangle argument once, for any letters, and use it again
     at C and at D. -/
  have double : ∀ {A B F : Point}, OnCircle A ABC → OnCircle B ABC → Between A E F →
      Triangle A E B → ∠ B E F = ∠ E A B + ∠ E A B := by
    intro A B F hA hB hAEF hAEB
    -- Then, since EA is equal to EB,
    have hEAEB : ‖E A‖ = ‖E B‖ := Definition15 hE hA hB
    -- the angle EAB is also equal to the angle EBA; [I. 5]
    have h5 : ∠ E A B = ∠ E B A := BookI.Prop5.base hAEB.bac hEAEB
    -- therefore the angles EAB, EBA are double of the angle EAB.
    have hdouble : ∠ E A B + ∠ E B A = ∠ E A B + ∠ E A B := by rw [← h5]
    -- But the angle BEF is equal to the angles EAB, EBA; [I. 32]
    have h32 : ∠ B E F = ∠ E A B + ∠ E B A := by
      rw [(BookI.Prop32 hAEB.cab hAEF).1, angle_symm hAEB.ne₁₃.symm hAEB.ne₁₂.symm]
      ac_rfl
    -- therefore the angle BEF is also double of the angle EAB.
    exact h32.trans hdouble
  have whole : SameSideOf E C A B → SameSideOf E B A C →
      angleAtCentre ABC B K C = ∠ B A C + ∠ B A C := by
    intro hEC hEB
    have hAEB : Triangle A E B := hEC.triangle.acb
    have hAEC : Triangle A E C := hEB.triangle.acb
    have hFEB : ∠ B E F = ∠ E A B + ∠ E A B := double hA hB hAEF hAEB
    -- For the same reason
    -- the angle FEC is also double of the angle EAC.
    have hFEC : ∠ C E F = ∠ E A C + ∠ E A C := double hA hC hAEF hAEC
    -- Therefore the whole angle BEC is double of the whole angle BAC.
    /- The straight line AF crosses BC at X, between B and C (`crossbar`). X is within the
       circle [III. 2], and so between A and F, and F lies across BC from A. So the angles
       BEF and FEC make up the whole angle at the centre (`angleAtCentre.diameter`), and AX
       divides the angle BAC into BAE and EAC. Euclid's first figure has E on A's side of
       BC; the same sentences now also cover E on BC, and E beyond it, where the angle at
       the centre is greater than two right angles (`angleAtCentre.reflex_gt`), the cases
       his angles at the centre could not reach. -/
    obtain ⟨X, hBXC, hX⟩ := crossbar hEC hEB
    have hAXF : Between A X F :=
      between_of_inside_chord (hX.onLine hA_AE hE_AE) hA_AE hF_AE (Prop2 hB hC X hBXC)
        hA hF (ne_of_between_ends hAEF)
    obtain ⟨N, hB_N, hC_N⟩ := Postulate1 B C hBCA.ne₁₂
    have hX_N : OnLine X N := on_line_of_between_ends hBXC hB_N hC_N
    have hA_N : ¬ OnLine A N := hBCA.off_line hB_N hC_N
    have hF_N : ¬ OnLine F N := fun h => hA_N (on_line_of_between (between_symm hAXF) h hX_N)
    have hFK : SameSideOf F K B C :=
      OppositeSidesOf.sameSideOf
        (OppositeSidesOf.of_line hBCA.ne₁₂ hB_N hC_N ⟨hA_N, hF_N, pasch3 hAXF hX_N⟩) hAK
    rw [angleAtCentre.diameter hE hB hC hA hF hAEF hAK hFK, angle_add_of_between hBCA hBXC,
      angle_onRay_right hX hAB.symm, angle_onRay_left hX hAC.symm,
      angle_symm (ne_of_between (between_symm hAEF)) (ne_of_centre_of_on hE hC), hFEB, hFEC,
      angle_symm hAE.symm hAB.symm]
    ac_rfl
  -- Again let another straight line be inflected, and let there be another angle BDC; let DE
  -- be joined and produced to G.
  have across : ∀ {B C D : Point}, OnCircle B ABC → OnCircle C ABC → OnCircle D ABC →
      OppositeSidesOf E C D B → ∠ B E C = ∠ B D C + ∠ B D C := by
    intro B C D hB hC hD hEC
    have hDE : D ≠ E := ne_of_centre_of_on hE hD
    obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hDE
    obtain ⟨G, -, -, hGED⟩ := line_circle_beyond (centre_inside hE) hE_DE hD_DE hDE
    have hDEG : Between D E G := between_symm hGED
    have hDB : D ≠ B := hEC.1
    obtain ⟨L, hD_L, hB_L⟩ := Postulate1 D B hDB
    obtain ⟨Y, hY_L, hEYC⟩ := (hEC.2 L hD_L hB_L).exists_between
    have hY_in : InsideCircle Y ABC :=
      InsideCircle.of_between_centre hE hC hEYC
    have hDYB : Between D Y B := between_of_inside_chord hY_L hD_L hB_L hY_in hD hB hDB
    have hDBE : Triangle D B E := hEC.triangle
    have hDBC : Triangle D B C := hEC.symm.triangle
    have hDY : D ≠ Y := ne_of_between hDYB
    have hECD : Triangle E C D := by
      rintro ⟨K, hE_K, hC_K, hD_K⟩
      have hY_K : OnLine Y K := on_line_of_between_ends hEYC hE_K hC_K
      exact hDBC.off_line hD_L hB_L ((line_unique hDY hD_K hY_K hD_L hY_L) ▸ hC_K)
    have hDEC : Triangle D E C := hECD.cab
    have hDEB : Triangle D E B := hDBE.acb
    -- Similarly then we can prove that the angle GEC is double of the angle EDC,
    have hGEC : ∠ C E G = ∠ E D C + ∠ E D C := double hD hC hDEG hDEC
    -- of which the angle GEB is double of the angle EDB;
    have hGEB : ∠ B E G = ∠ E D B + ∠ E D B := double hD hB hDEG hDEB
    -- therefore the angle BEC which remains is double of the angle BDC.
    /- B lies within the angle EDC, and within the angle GEC. -/
    have hsplitD : ∠ E D C = ∠ E D B + ∠ B D C := by
      rw [angle_add_of_between hECD hEYC, angle_onRay_right (OnRay.of_between hDYB) hDEC.ne₁₂.symm,
        angle_onRay_left (OnRay.of_between hDYB) hDBC.ne₁₃.symm]
    obtain ⟨K, hE_K, hG_K⟩ := Postulate1 E G (ne_of_between (between_symm hDEG)).symm
    have hD_K : OnLine D K := on_line_of_between (between_symm hDEG) hG_K hE_K
    have hY_K : ¬ OnLine Y K := fun hY_K =>
      hDBE.off_line hD_L hB_L ((line_unique hDY hD_K hY_K hD_L hY_L) ▸ hE_K)
    have hBC_EG : SameSideOf B C E G :=
      SameSideOf.of_line (ne_of_between (between_symm hDEG)).symm hE_K hG_K
        (same_side_trans (pasch2 hDYB hD_K hY_K) (pasch2 hEYC hE_K hY_K))
    have hBG_EC : SameSideOf B G E C := by
      have hDG : OppositeSidesOf D G E C := (OppositeSidesOf.of_between hECD.bac hDEG).swap
      obtain ⟨P, hE_P, hC_P⟩ := Postulate1 E C hECD.ne₁₂
      have hY_P : OnLine Y P := on_line_of_between_ends hEYC hE_P hC_P
      have hD_P : ¬ OnLine D P := hECD.off_line hE_P hC_P
      have hB_P : ¬ OnLine B P := fun hB_P =>
        hD_P (on_line_of_between (between_symm hDYB) hB_P hY_P)
      have hDB : OppositeSidesOf D B E C :=
        OppositeSidesOf.of_line hECD.ne₁₂ hE_P hC_P ⟨hD_P, hB_P, pasch3 hDYB hY_P⟩
      exact OppositeSidesOf.sameSideOf hDB hDG
    have hsplitE : ∠ G E C = ∠ G E B + ∠ B E C := angle_add_of_within hBC_EG hBG_EC
    have h := hsplitE
    rw [angle_symm (ne_of_between (between_symm hDEG)) hDEC.ne₂₃.symm, hGEC,
      angle_symm (ne_of_between (between_symm hDEG)) hDEB.ne₂₃.symm, hGEB, hsplitD] at h
    apply CommonNotion3 (c := ∠ E D B + ∠ E D B) (d := ∠ E D B + ∠ E D B) _ rfl
    rw [add_comm, ← h]
    ac_rfl
  -- Therefore etc.
  /- Now we find which of Euclid's figures we are in: E is on AB or on AC, within the
     angle BAC (on A's side of BC, on BC, or beyond it), or outside it. -/
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  obtain ⟨M, hA_M, hC_M⟩ := Postulate1 A C hAC
  obtain ⟨N, hB_N, hC_N⟩ := Postulate1 B C hBCA.ne₁₂
  have hC_L : ¬ OnLine C L := hBCA.cab.off_line hA_L hB_L
  have hB_M : ¬ OnLine B M := hBCA.cab.acb.off_line hA_M hC_M
  have hA_N : ¬ OnLine A N := hBCA.off_line hB_N hC_N
  by_cases hE_L : OnLine E L
  · /- E is on AB, the case Euclid leaves out. E lies between A and B, on A's side of BC, so
       the angle at the centre is the angle BEC, which is the angle FEC. -/
    have hAEB : Between A E B := between_of_inside_chord hE_L hA_L hB_L (centre_inside hE) hA hB hAB
    have hAEC : Triangle A E C := Triangle.of_line hA_L hE_L hAE hC_L
    have hE_N : ¬ OnLine E N := fun h => hA_N (on_line_of_between (between_symm hAEB) hB_N h)
    rw [angleAtCentre.within hE hB hC ((SameSideOf.of_line hBCA.ne₁₂ hB_N hC_N
        (pasch2 (between_symm hAEB) hB_N hE_N)).trans_opposite hAK),
      angle_onRay_left (OnRay.of_between_between hAEF hAEB) hAEC.ne₂₃.symm,
      angle_symm (ne_of_between (between_symm hAEF)) hAEC.ne₂₃.symm, double hA hC hAEF hAEC,
      angle_onRay_left (OnRay.of_between hAEB) hAC.symm]
  by_cases hE_M : OnLine E M
  · /- E is on AC: the same, with B and C exchanged. -/
    have hAEC : Between A E C := between_of_inside_chord hE_M hA_M hC_M (centre_inside hE) hA hC hAC
    have hAEB : Triangle A E B := Triangle.of_line hA_M hE_M hAE hB_M
    have hE_N : ¬ OnLine E N := fun h => hA_N (on_line_of_between (between_symm hAEC) hC_N h)
    rw [angleAtCentre.within hE hB hC ((SameSideOf.of_line hBCA.ne₁₂ hB_N hC_N
        (pasch2 (between_symm hAEC) hC_N hE_N)).trans_opposite hAK),
      angle_symm (ne_of_centre_of_on hE hB) (ne_of_centre_of_on hE hC),
      angle_onRay_left (OnRay.of_between_between hAEF hAEC) hAEB.ne₂₃.symm,
      angle_symm (ne_of_between (between_symm hAEF)) hAEB.ne₂₃.symm, double hA hB hAEF hAEB,
      angle_onRay_left (OnRay.of_between hAEC) hAB.symm, angle_symm hAC.symm hAB.symm]
  by_cases hs1 : SameSide E C L
  · by_cases hs2 : SameSide E B M
    · exact whole (SameSideOf.of_line hAB hA_L hB_L hs1) (SameSideOf.of_line hAC hA_M hC_M hs2)
    · /- Euclid's second figure, with B and C exchanged: the centre is on A's side of BC. -/
      have hEB : OppositeSidesOf E B A C := OppositeSidesOf.of_line hAC hA_M hC_M ⟨hE_M, hB_M, hs2⟩
      rw [angleAtCentre.within hE hB hC
          ((Prop20.across_side hE hC hB hA hBCA.bac hEB).swap.trans_opposite hAK),
        angle_symm (ne_of_centre_of_on hE hB) (ne_of_centre_of_on hE hC), across hC hB hA hEB,
        angle_symm hAC.symm hAB.symm]
  · /- Euclid's second figure: the centre is on A's side of BC. -/
    have hEC : OppositeSidesOf E C A B := OppositeSidesOf.of_line hAB hA_L hB_L ⟨hE_L, hC_L, hs1⟩
    rw [angleAtCentre.within hE hB hC ((Prop20.across_side hE hB hC hA hBCA hEC).trans_opposite hAK)]
    exact across hB hC hA hEC
  -- Q. E. D.

/-- **III.20, the centre on A's side of BC.** Then the angle BEC is double of the angle
BAC: the angle at the centre standing on the circumference on the other side is the angle
BEC itself (`angleAtCentre.within`), less than two right angles, as Euclid's angles at
the centre are. It follows from the general statement, for the propositions that ask
only for the angle BEC. -/
theorem Prop20.special {A B C E : Point} {ABC : Circle} (hE : Centre E ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hEA : SameSideOf E A B C) :
    ∠ B E C = ∠ B A C + ∠ B A C := by
  obtain ⟨K, hK, -⟩ := exists_oppositeSidesOf hEA.symm.triangle []
  rw [← angleAtCentre.within hE hB hC (hEA.trans_opposite hK.symm), Prop20 hA hB hC hK.symm]

/-- **The circumference is its angle at the centre.** Our measure of the circumference
BKC, `circumference`, is twice the angle at some point of the circle on the other side of
BC. That is the angle at the centre standing on it, in every case: less than a
semicircle, a semicircle, or greater. Of III.20–III.22 it needs III.20 alone, where
`Circumference.eq` needs III.21; `Circumference.centre`, for the circumference beyond
which the centre lies, is a case of it. [III. 2, III. 20] -/
theorem Prop20.circumference (hB : OnCircle B α) (hC : OnCircle C α)
    (hK : Triangle B C K) : circumference α B K C = angleAtCentre α B K C := by
  obtain ⟨A₀, hA₀, hA₀K⟩ := Prop2.oppositeSide hB hC hK
  obtain ⟨A, hA, hAK, hx⟩ := Classical.epsilon_spec
    (p := fun x => ∃ A : Point, OnCircle A α ∧ OppositeSidesOf A K B C ∧
      x = ∠ B A C + ∠ B A C) ⟨_, A₀, hA₀, hA₀K, rfl⟩
  unfold Elements.circumference
  rw [hx, Prop20 hA hB hC hAK]

end Elements.BookIII
