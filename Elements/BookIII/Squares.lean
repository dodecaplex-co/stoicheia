import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop12
import Elements.BookI.Prop17
import Elements.BookI.Prop19
import Elements.BookI.Prop07

/-!
# Book III: squares on straight lines, the perpendicular from the centre, and segments on one base

Book III borrows Book II's squares twice to compare straight lines, and passes from
equal squares to equal sides without a word: "therefore the square on FE which remains
is equal to the square on EG, therefore EF is equal to EG" (III.14); "the square on DE
is equal to the square on DB; therefore DE is equal to DB" (III.37). Book I proves it of
squares that are drawn (`Prop46.side_eq`); here it is said once of the squares on
straight lines, with the fact that the square on a straight line is something.

The propositions that compare those squares (III.14, III.35, III.36) draw a
perpendicular from the centre to a straight line in the circle, and read off the figure
that it falls within the straight line, between its ends, before III.3 bisects it there.
That is said once too (`foot_between`), after III.2, in `Elements/BookIII/Feet.lean`. And
every straight line has one foot of the perpendicular from a point, the point itself when
the straight line passes through it (`Foot.exists`, `Foot.unique`), so that `Foot`, by
which the companions of III.14 and III.15 measure a straight line's distance from the
centre, names one point.

Two segments on one base, on one side of it, in equal circles and of one kind, are one
segment of one circle: their centres are equally far from the ends of the base and lie
alike, so they are one point, by I.7 off the base and by the order of points on it
(`Arc.eq_of_aligned`). It cites nothing of Book III, so it is here, with its two helpers,
in Book III's namespace.

Each docstring ends with the propositions the step cites; the certificate walks through
it and records them.
-/

namespace Elements

open Tacit BookI

/-- The square on a straight line is something. Described on AB [I. 46], it is a
parallelogram (`Square.described`), and its diameter cuts it into two triangles, each of
which is something. [I. 4, I. 28, I. 34, I. 46] -/
theorem sq_pos {A B : Point} (hAB : A ≠ B) : 0 < sq A B := by
  obtain ⟨P, hP, -⟩ := exists_off_line hAB []
  obtain ⟨D, E, hsq, hD, hE⟩ := Prop46 hAB hP
  obtain ⟨hp, heq⟩ := Square.described hsq hD hE
  rw [← heq]
  have h₁ : 0 < △ A D E := hp.triangle.area_pos
  have h₂ : 0 < △ A E B := by
    rw [← area_rotate E B A]
    exact hp.rotate.rotate.triangle.area_pos
  exact lt_trans h₁ (CommonNotion5 h₂)

/-- **Equal squares are on equal straight lines.** If the square on AB is equal to the
square on CD, then AB is equal to CD. Each square is described [I. 46] and is the
square on its side (`Square.described`); then I.46's corollary for drawn squares,
`Prop46.side_eq`, compares them. If one of the straight lines is nothing, so is its
square, and so the other (`sq_pos`). [I. 3, I. 4, I. 28, I. 34, I. 46] -/
theorem BookI.Prop46.sq {A B C D : Point} (h : sq A B = sq C D) : ‖A B‖ = ‖C D‖ := by
  by_cases hAB : A = B
  · subst hAB
    by_cases hCD : C = D
    · subst hCD
      rw [len_self, len_self]
    · rw [sq_self] at h
      exact absurd h.symm (Magnitude.ne_of_lt (sq_pos hCD)).symm
  · by_cases hCD : C = D
    · subst hCD
      rw [sq_self] at h
      exact absurd h (Magnitude.ne_of_lt (sq_pos hAB)).symm
    /- We describe the squares on AB and on CD [I. 46], each read from its second corner. -/
    obtain ⟨P, hP, -⟩ := exists_off_line hAB []
    obtain ⟨D', E', hsq, hD', hE'⟩ := Prop46 hAB hP
    obtain ⟨hp, heq⟩ := Square.described hsq hD' hE'
    obtain ⟨Q, hQ, -⟩ := exists_off_line hCD []
    obtain ⟨G, H, hsq', hG, hH⟩ := Prop46 hCD hQ
    obtain ⟨hp', heq'⟩ := Square.described hsq' hG hH
    have e₁ : quadArea B A D' E' = Elements.sq A B := by
      rw [← heq, quadArea_rotate₂ D' E' B A, hp.quadArea_rotate]
    have e₂ : quadArea D C G H = Elements.sq C D := by
      rw [← heq', quadArea_rotate₂ G H D C, hp'.quadArea_rotate]
    have := Prop46.side_eq hsq.rotate.rotate.rotate (hD'.trans hE'.symm).swap
      hsq'.rotate.rotate.rotate (hG.trans hH.symm).swap (by rw [e₁, e₂, h])
    rw [len_symm A B, len_symm C D]
    exact this

/-- Every straight line has a foot of the perpendicular from any point (`Foot`, Definitions
III.4 and III.5): the perpendicular drawn to it, or the point itself when it is on the
straight line (and when A and B are one point). [I. 12] -/
theorem Foot.exists (E A B : Point) : ∃ F : Point, Foot E A B F := by
  by_cases hE_AB : Collinear A B E
  · /- E is on AB, including when A and B coincide: E itself is the foot. -/
    exact ⟨E, hE_AB, fun _ => rfl, fun h => False.elim (h hE_AB)⟩
  · /- E is off AB: I.12 draws the perpendicular to the whole straight line. -/
    obtain ⟨F, hF, hEF⟩ := BookI.Prop12 (Triangle.ne₁₂ hE_AB) hE_AB
    exact ⟨F, hF, fun h => False.elim (hE_AB h), fun _ => hEF⟩

/-- The foot of the perpendicular is one point: two perpendiculars from E to one straight
line would make a triangle with two right angles, and two angles of a triangle are less
than two right angles. So `Foot E A B F` may be read "F is the foot". [I. 17] -/
theorem Foot.unique {E A B F F' : Point} (hF : Foot E A B F) (hF' : Foot E A B F') :
    F = F' := by
  by_cases hE_AB : Collinear A B E
  · /- E is on AB, so both feet are E. -/
    exact (hF.2.1 hE_AB).trans (hF'.2.1 hE_AB).symm
  · /- E is off AB. Two different feet would make two right angles in EFF'. -/
    apply Classical.byContradiction
    intro (hFF' : F ≠ F')
    obtain ⟨L, hA_L, hB_L, hF_L⟩ := hF.1
    obtain ⟨M, hA_M, hB_M, hF'_M⟩ := hF'.1
    have hF'_L : OnLine F' L :=
      Tacit.line_unique (Triangle.ne₁₂ hE_AB) hA_M hB_M hA_L hB_L ▸ hF'_M
    have hE_L : ¬ OnLine E L := Triangle.off_line hE_AB hA_L hB_L
    have hEFF' : Triangle E F F' := (Triangle.of_line hF_L hF'_L hFF' hE_L).cab
    have hrightF : ∠ E F F' = ∟ := hF.2.2 hE_AB F' hF'.1 hFF'.symm
    have hrightF' : ∠ F F' E = ∟ :=
      (Tacit.angle_symm hFF' hEFF'.ne₁₃).trans (hF'.2.2 hE_AB F hF.1 hFF')
    have htwo := (BookI.Prop17 hEFF').1
    rw [hrightF, hrightF'] at htwo
    exact Tacit.lt_irrefl _ htwo

end Elements

namespace Elements.BookIII

open Tacit

/-- A centre on the straight line through two different points of its circle lies
between them: either other order would make one radius a part of the other
(`between_of_centre_chord`). In the semicircle case this puts each centre between the ends
of the base. -/
theorem Aligned.centre_between {B C O : Point} {α : Circle} (hBC : B ≠ C)
    (hO : Centre O α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hline : Collinear B C O) : Between B O C := by
  obtain ⟨L, hB_L, hC_L, hO_L⟩ := hline
  exact between_of_centre_chord hO_L hB_L hC_L hO hB hC hBC

/-- Two points between B and C, equally far from B, coincide. Both lie on the ray
from B through C, where a distance fixes one point. This identifies the two centres
in the semicircle case. -/
theorem Aligned.eq_on_base {B C O O' : Point} (hO : Between B O C)
    (hO' : Between B O' C) (hlen : ‖O B‖ = ‖O' B‖) : O = O' := by
  have hORay : OnRay O B C := OnRay.of_between hO
  have hO'Ray : OnRay O' B C := OnRay.of_between hO'
  obtain ⟨L, hB_L, hC_L, hO_L⟩ := hORay.2.2.1
  have hray : OnRay O B O' :=
    ⟨ne_of_between hO', (ne_of_between hO).symm,
      ⟨L, hB_L, hO'Ray.onLine hB_L hC_L, hO_L⟩, hORay.not_between hO'Ray⟩
  apply hray.eq_of_len_eq
  rw [len_symm B O, len_symm B O']
  exact hlen

/-- **Arcs on one base, of one kind, in equal circles, are one arc.** Two drawn arcs with the
same ends, on the same side of their base, in equal circles and of the same kind, lie in one
circle, and have the same points and the same segment.

Proved: the centres are equally far from the two ends (the radii are equal), and lie alike,
both on the arcs' side, both on the base, or both beyond it; so they are one point, by I.7 off
the base and by the order of points on it; and a circle is fixed by its centre and radius
(`circle_eq`).

A shared step, not a companion: its hypotheses (equal circles, the same kind) are not
III.23's (similar segments). Ground for the later uses of arcs. [I. 7] -/
theorem Arc.eq_of_aligned {a b : Arc} (ha : a.Drawn) (hb : b.Drawn) (hB : a.B = b.B)
    (hC : a.C = b.C) (hK : SameSideOf a.K b.K a.B a.C)
    (hcircles : EqualCircles a.circle b.circle) (hkind : Arc.SameKind a b) :
    a.circle = b.circle ∧ (∀ P : Point, OnArc P a ↔ OnArc P b) ∧
      (∀ P : Point, InSegment P a ↔ InSegment P b) := by
  obtain ⟨O, hO⟩ := exists_centre a.circle
  obtain ⟨O', hO'⟩ := exists_centre b.circle
  have hB_b : OnCircle a.B b.circle := hB.symm ▸ hb.1
  have hC_b : OnCircle a.C b.circle := hC.symm ▸ hb.2.1
  /- Equal circles have equal radii to each end of the common base. -/
  have hOB : ‖O a.B‖ = ‖O' a.B‖ := hcircles.radii hO hO' ha.1 hB_b
  have hOC : ‖O a.C‖ = ‖O' a.C‖ := hcircles.radii hO hO' ha.2.1 hC_b
  have hcentres : O = O' := by
    rcases hkind with ⟨⟨G, hG, hGK⟩, ⟨H, hH, hHK⟩⟩ | ⟨⟨G, hG, hGbase⟩, ⟨H, hH, hHbase⟩⟩ |
        ⟨⟨G, hG, hGK⟩, ⟨H, hH, hHK⟩⟩
    · /- Less than semicircles: each centre is beyond the base from its arc. The arcs
         lie on one side, so the centres lie on one side too, and I.7 makes them one. -/
      obtain rfl := centre_unique hO hG
      obtain rfl := centre_unique hO' hH
      rw [← hB, ← hC] at hHK
      have hKO' : OppositeSidesOf a.K O' a.B a.C := hK.trans_opposite hHK.symm
      exact BookI.Prop7 (hGK.symm.sameSideOf hKO') hOB hOC
    · /- Semicircles: both centres lie between the ends of the base, and their equal
         distances from B fix one point of the ray from B through C. -/
      obtain rfl := centre_unique hO hG
      obtain rfl := centre_unique hO' hH
      rw [← hB, ← hC] at hHbase
      have hBOC := Aligned.centre_between hK.1 hO ha.1 ha.2.1 hGbase
      have hBO'C := Aligned.centre_between hK.1 hO' hB_b hC_b hHbase
      exact Aligned.eq_on_base hBOC hBO'C hOB
    · /- Greater than semicircles: both centres lie on the arcs' side of the base, so
         I.7 again makes them one. -/
      obtain rfl := centre_unique hO hG
      obtain rfl := centre_unique hO' hH
      rw [← hB, ← hC] at hHK
      exact BookI.Prop7 ((hGK.trans hK).trans hHK.symm) hOB hOC
  /- The circles have one centre and the same radius to B. -/
  have hcircle : a.circle = b.circle :=
    circle_eq hO (hcentres.symm ▸ hO') ha.1 hB_b rfl
  /- Naming one side of the base by either K gives the same closed half-plane. -/
  have hside (P : Point) : OnSideOrLine P a.K a.B a.C ↔ OnSideOrLine P b.K b.B b.C := by
    rw [← hB, ← hC]
    constructor
    · rintro (hPK | hline)
      · exact Or.inl (hPK.trans hK)
      · exact Or.inr hline
    · rintro (hPK | hline)
      · exact Or.inl (hPK.trans hK.symm)
      · exact Or.inr hline
  refine ⟨hcircle, ?_, ?_⟩
  · intro P
    unfold OnArc
    rw [hcircle, hside P]
  · intro P
    unfold InSegment
    rw [hcircle, hside P]

end Elements.BookIII
