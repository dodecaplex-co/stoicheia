import Elements.Figure.Basics
import Elements.Figure.Circles
import Staging.Stage3.Definitions

/-!
# Stage 3, staged: Book Zero facts for arcs

Statements frozen before their proofs (brief 0006, stage 3). Facts every arc needs, proved
from the foundations alone; destined for a new Book Zero file, `Elements/Figure/Chords.lean`,
which cites no proposition.

An arc is named by a point on its side, which need not be on the circle: III.26 and III.28
name their circumferences by such points. `Arc.congr_side` says that only the side matters,
and `Arc.Congruent.congr_side` carries a congruence from one naming point to another on the
same side.
-/

namespace Elements

open Tacit

/-- **A straight line in a circle, along its own line.** For two different points A, B of a
circle and a point P of the straight line AB: P is on the circle exactly when it is A or B,
and within the circle exactly when it lies between them. Proved from `Triangle.of_onCircle`
and Circle 1 with Circle 2, which is now proved from Circle 3. III.24 uses it for the
points of the base. -/
theorem chord_cases {A B P : Point} {α : Circle} (hA : OnCircle A α) (hB : OnCircle B α)
    (hAB : A ≠ B) (hP : Collinear A B P) :
    (OnCircle P α ↔ P = A ∨ P = B) ∧ (InsideCircle P α ↔ Between A P B) := by
  refine ⟨⟨fun hPα => Classical.byContradiction fun hne => ?_, ?_⟩,
    ⟨fun hin => ?_, fun h => inside_of_between (Or.inr hA) (Or.inr hB) h⟩⟩
  · exact Triangle.of_onCircle hA hB hPα hAB (fun e => hne (Or.inr e.symm))
      (fun e => hne (Or.inl e.symm)) hP
  · rintro (h | h)
    · rw [h]; exact hA
    · rw [h]; exact hB
  · obtain ⟨L, hA_L, hB_L, hP_L⟩ := hP
    exact between_of_inside_chord hP_L hA_L hB_L hin hA hB hAB

/-- **A straight line from within the base meets the arc.** For a drawn arc, a ray from a point
X between the ends of the base, through a point Y on the arc's side, meets the arc.

Proved: X is within the circle (Circle 2, proved from Circle 3), so the straight line XY, produced
beyond X backwards and then forwards, meets the circle on Y's side (Intersections 5, with
Pasch 3 for the side). III.25's construction core reads this off the segment it is given. -/
theorem Arc.meets {a : Arc} (ha : a.Drawn) {X Y : Point} (hX : Between a.B X a.C)
    (hY : SameSideOf Y a.K a.B a.C) : ∃ Q : Point, OnArc Q a ∧ OnRay Q X Y := by
  /- X lies within the circle, since it is between the ends of the base (Circle 2,
     proved from Circle 3), and Y is off the straight line BC. -/
  have hX_in : InsideCircle X a.circle :=
    inside_of_between (Or.inr ha.2.1) (Or.inr ha.2.2.1) hX
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 a.B a.C hY.1
  have hX_L : OnLine X L := on_line_of_between_ends hX hB_L hC_L
  have hY_L : ¬ OnLine Y L := hY.triangle.off_line hB_L hC_L
  have hXY : X ≠ Y := fun e => hY_L (e ▸ hX_L)
  /- Draw XY, and produce it backwards, beyond X away from Y, to meet the circle at A
     (Intersections 5). -/
  obtain ⟨N, hX_N, hY_N⟩ := Postulate1 X Y hXY
  obtain ⟨A, hA, hA_N, hAXY⟩ := line_circle_beyond hX_in hX_N hY_N hXY.symm
  /- A is off BC: otherwise XY and BC would share A and X, and Y would lie on BC. So BC,
     through X, separates A from Y (Pasch 3). -/
  have hAX : A ≠ X := fun e => inside_not_on hX_in (e ▸ hA)
  have hA_L : ¬ OnLine A L := fun hA_L =>
    hY_L ((line_unique hAX hA_N hX_N hA_L hX_L) ▸ hY_N)
  have hAY : OppositeSidesOf A Y a.B a.C :=
    OppositeSidesOf.of_line hY.1 hB_L hC_L ⟨hA_L, hY_L, pasch3 hAXY hX_L⟩
  /- Produce AX forwards, beyond X, to meet the circle at Q (Intersections 5). Q is off
     BC for the same reason. -/
  obtain ⟨Q, hQ, hQ_N, hQXA⟩ := line_circle_beyond hX_in hX_N hA_N hAX
  have hQX : Q ≠ X := fun e => inside_not_on hX_in (e ▸ hQ)
  have hQ_L : ¬ OnLine Q L := fun hQ_L =>
    hY_L ((line_unique hQX hQ_N hX_N hQ_L hX_L) ▸ hY_N)
  /- BC separates Q from A too (Pasch 3), so Q is on Y's side, hence on K's side. -/
  have hQA : OppositeSidesOf Q A a.B a.C :=
    OppositeSidesOf.of_line hY.1 hB_L hC_L ⟨hQ_L, hA_L, pasch3 hQXA hX_L⟩
  have hQY : SameSideOf Q Y a.B a.C := hQA.symm.sameSideOf hAY
  /- Q lies on the arc and on XY. X cannot lie between Q and Y, since they are on one
     side of BC (Pasch 3); so Q lies on the ray from X through Y. -/
  exact ⟨Q, ⟨hQ, Or.inl (hQY.trans hY)⟩,
    hXY, hQX, ⟨N, hX_N, hY_N, hQ_N⟩,
    fun hQXY => pasch3 hQXY hX_L (hQY.sameSide hB_L hC_L)⟩

/-- **Only the side names an arc.** If K and K' are on one side of BC, the arc of a circle
from B to C on the side of K has the same points as the arc on the side of K', and the
segment the same points as the segment. -/
theorem Arc.congr_side {α : Circle} {B C K K' : Point} (h : SameSideOf K K' B C) :
    (∀ P : Point, OnArc P ⟨α, B, C, K⟩ ↔ OnArc P ⟨α, B, C, K'⟩) ∧
      (∀ P : Point, InSegment P ⟨α, B, C, K⟩ ↔ InSegment P ⟨α, B, C, K'⟩) := by
  have hside : ∀ P : Point, OnSideOrLine P K B C ↔ OnSideOrLine P K' B C := fun P =>
    ⟨fun hP => hP.imp (fun hPK => hPK.trans h) id,
      fun hP => hP.imp (fun hPK => hPK.trans h.symm) id⟩
  exact ⟨fun P => and_congr Iff.rfl (hside P), fun P => and_congr Iff.rfl (hside P)⟩

/-- **A congruence does not depend on the naming points.** If the segment of α on BC on the
side of K is congruent to the segment of β on DE on the side of L, and K' is on the side of K
and L' on the side of L, the segments named by K' and L' are congruent, by the same map. -/
theorem Arc.Congruent.congr_side {α β : Circle} {B C K K' D E L L' : Point}
    (h : Arc.Congruent ⟨α, B, C, K⟩ ⟨β, D, E, L⟩) (hK : SameSideOf K K' B C)
    (hL : SameSideOf L L' D E) : Arc.Congruent ⟨α, B, C, K'⟩ ⟨β, D, E, L'⟩ := by
  obtain ⟨a₁, a₂⟩ := Arc.congr_side (α := α) hK
  obtain ⟨b₁, b₂⟩ := Arc.congr_side (α := β) hL
  obtain ⟨f, hB, hC, ⟨s₁, s₂, s₃⟩, ⟨t₁, t₂, t₃⟩⟩ := h
  refine ⟨f, hB, hC, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact fun P hP => (b₂ _).mp (s₁ P ((a₂ P).mpr hP))
  · intro Q hQ
    obtain ⟨P, hP, hPQ⟩ := s₂ Q ((b₂ Q).mpr hQ)
    exact ⟨P, (a₂ P).mp hP, hPQ⟩
  · exact fun P Q hP hQ => s₃ P Q ((a₂ P).mpr hP) ((a₂ Q).mpr hQ)
  · exact fun P hP => (b₁ _).mp (t₁ P ((a₁ P).mpr hP))
  · intro Q hQ
    obtain ⟨P, hP, hPQ⟩ := t₂ Q ((b₁ Q).mpr hQ)
    exact ⟨P, (a₁ P).mp hP, hPQ⟩
  · exact fun P Q hP hQ => t₃ P Q ((a₁ P).mpr hP) ((a₁ Q).mpr hQ)

end Elements
