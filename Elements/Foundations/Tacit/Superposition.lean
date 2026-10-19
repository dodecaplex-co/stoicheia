import Elements.Foundations.Tacit.Transfer

/-!
# Superposition

> "For, if the triangle ABC be applied to the triangle DEF, and if the point A
> be placed on the point D and the straight line AB on DE, then the point B will
> also coincide with E …" (I.4)

Twice in Book I (I.4 and I.8) Euclid picks a triangle up and lays it down on
another. Commentators from Proclus onward have worried about this, since moving
figures appears in none of the postulates. Hilbert simply made side–angle–side
an axiom. System E (§3.7) treats superposition as a rule that may be used only
to prove facts about the figure already drawn, never to build anything new.

Our superposition axiom asserts that a congruent triangle can be placed on a
given ray and side: A on D, AB along the ray from D toward G, C on H's side. We
take its form, one rule for System E's two, from LeanEuclid, by Logan Murphy,
Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and Xujie Si, with warm
thanks. The edition permits its direct use only in I.4 and I.8, where the
checks hold it. This axiom is stronger as a construction principle than System
E's restricted inference rule: a proof may build on the corners it places.
-/

namespace Elements.Tacit

/-- **Superposition.** The triangle ABC can be applied to the straight line L
with A on D, B on the ray from D through G, and C on the side of L
where H is, without changing any side or angle. -/
axiom superposition {A B C D G H : Point} {L : Line} (hABC : Triangle A B C)
    (hD : OnLine D L) (hG : OnLine G L) (hDG : D ≠ G) (hH : ¬ OnLine H L) :
    ∃ B' C' : Point, OnLine B' L ∧ ¬ Between B' D G ∧ SameSide C' H L ∧
      ‖D B'‖ = ‖A B‖ ∧ ‖B' C'‖ = ‖B C‖ ∧ ‖C' D‖ = ‖C A‖ ∧
      ∠ B' D C' = ∠ B A C ∧ ∠ D C' B' = ∠ A C B ∧ ∠ C' B' D = ∠ C B A

end Elements.Tacit
