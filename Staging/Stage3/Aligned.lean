import Elements.Figure.Basics
import Elements.BookI.Prop07
import Staging.Stage3.Definitions

/-!
# Stage 3, staged: arcs on one base

Statements before proofs (brief 0006, stage 3). A shared step that cites I.7 and nothing of
Book III, destined for `Elements/BookIII/Squares.lean`, the file of Book III's shared steps
that cite Books I and II.
-/

namespace Elements.BookIII

open Tacit

/-- A centre on the straight line through two different points of its circle lies
between them: it differs from each, and if it lay beyond either, one of the equal radii
would be less than the other. This places the centre in the semicircle case. -/
theorem Aligned.centre_between {B C O : Point} {α : Circle} (hBC : B ≠ C)
    (hO : Centre O α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hline : Collinear B C O) : Between B O C := by
  obtain ⟨L, hB_L, hC_L, hO_L⟩ := hline
  have hBO : B ≠ O := ne_of_centre_of_on hO hB
  have hCO : C ≠ O := ne_of_centre_of_on hO hC
  have hradii : ‖O B‖ = ‖O C‖ := Definition15 hO hB hC
  rcases between_cases hBO hCO.symm hBC hB_L hO_L hC_L with h | h | h
  · exact h
  · exact False.elim ((Magnitude.ne_of_lt (len_lt_of_between h)) hradii)
  · exact False.elim ((Magnitude.ne_of_lt (len_lt_of_between (between_symm h))) hradii.symm)

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

To be proved: the centres are equally far from the two ends (the radii are equal), and lie
alike, both on the arcs' side, both on the base, or both beyond it; so they are one point,
by I.7 off the base and by the order of points on it; and a circle is fixed by its centre and
radius (`circle_eq`).

A shared step, not a companion: its hypotheses (equal circles, the same kind) are not
III.23's (similar segments). Ground for the arcs (brief 0005, stage 3), for `Arcs.lean`
and their later uses. -/
theorem Arc.eq_of_aligned {a b : Arc} (ha : a.Drawn) (hb : b.Drawn) (hB : a.B = b.B)
    (hC : a.C = b.C) (hK : SameSideOf a.K b.K a.B a.C)
    (hcircles : EqualCircles a.circle b.circle) (hkind : Arc.SameKind a b) :
    a.circle = b.circle ∧ (∀ P : Point, OnArc P a ↔ OnArc P b) ∧
      (∀ P : Point, InSegment P a ↔ InSegment P b) := by
  obtain ⟨O, hO⟩ := ha.1
  obtain ⟨O', hO'⟩ := hb.1
  have hB_b : OnCircle a.B b.circle := hB.symm ▸ hb.2.1
  have hC_b : OnCircle a.C b.circle := hC.symm ▸ hb.2.2.1
  /- Equal circles have equal radii to each end of the common base. -/
  have hOB : ‖O a.B‖ = ‖O' a.B‖ := hcircles.radii hO hO' ha.2.1 hB_b
  have hOC : ‖O a.C‖ = ‖O' a.C‖ := hcircles.radii hO hO' ha.2.2.1 hC_b
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
      have hBOC := Aligned.centre_between hK.1 hO ha.2.1 ha.2.2.1 hGbase
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
    circle_eq hO (hcentres.symm ▸ hO') ha.2.1 hB_b rfl
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
