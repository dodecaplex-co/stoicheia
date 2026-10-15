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

Here it is one rule: a triangle can be laid down with its corner `A` on a given
point `D` of a line, its side `AB` along the ray from `D` toward `G`, and its
third corner on the same side as `H`, keeping all its sides and angles. We
follow LeanEuclid's form of the rule, which combines System E's two
superposition rules into one. To respect System E's restriction, the
certificate's checks allow only I.4 and I.8 to cite it.
-/

namespace Elements.Tacit

/-- **Superposition.** The triangle `ABC` can be applied to the straight line `L`
with `A` on `D`, `B` on the ray from `D` through `G`, and `C` on the side of `L`
where `H` is, without changing any side or angle. -/
axiom superposition {A B C D G H : Point} {L : Line} (hABC : Triangle A B C)
    (hD : OnLine D L) (hG : OnLine G L) (hDG : D ≠ G) (hH : ¬ OnLine H L) :
    ∃ B' C' : Point, OnLine B' L ∧ ¬ Between B' D G ∧ SameSide C' H L ∧
      ‖D B'‖ = ‖A B‖ ∧ ‖B' C'‖ = ‖B C‖ ∧ ‖C' D‖ = ‖C A‖ ∧
      ∠ B' D C' = ∠ B A C ∧ ∠ D C' B' = ∠ A C B ∧ ∠ C' B' D = ∠ C B A

end Elements.Tacit
