import Elements.Figure.OnCircles

/-!
# Book Zero: the points of a segment

A segment of a circle is named by its circle, the two ends of its base and a point on the
side of its circumference (`Arc`, in `Foundations/DefinitionsIII.lean`, which says how).
Only the side names a segment: points on one side of the base name the same segment, and a
congruence carries over to them by the same map (`Arc.congr_side`,
`Arc.Congruent.congr_side`). III.26 and III.28 name their circumferences by points that need
not be on the circle; III.28 uses the last for two diameters, as `Arcs.lean` does.

The facts about the points of a segment that rest on III.2 come after it: that a point of
the straight line through two points of a circle is on the circle exactly when it is one of
them, and within it exactly when it lies between them, is `BookIII.Prop24.chord_cases`,
before III.24, which decides the points of the base by it.

Nothing in Book Zero cites a proposition of the *Elements*.
-/

namespace Elements

open Tacit

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
