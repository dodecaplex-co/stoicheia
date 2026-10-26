import Elements.Foundations.Tacit.Transfer
import Elements.Foundations.Superposition.Semantics

/-!
# Superposition

Twice in Book I, in I.4 and I.8, Euclid lays one triangle on another and reasons from
the coincidence of their parts. System E (§3.7) treats superposition as a restricted
inference: the hypothetical placement proves facts about the figure already given.

Our rule follows this style. A represented derivation may use the sides and angles
of the triangle laid down, together with its side AC, but introduces no further
objects. Its conclusion is an equality of lengths, angles or areas over the given
figure's symbols. The hypothetical corners cannot be returned as constructed points
by this rule. This restriction concerns represented derivations; it does not claim
that the full theory cannot prove a placement by later construction propositions.

The combined placement, keeping all three sides and all three angles, follows
LeanEuclid, by Logan Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar
and Xujie Si, with warm thanks. Our placement also keeps the side AC, as a straight
line through D and C′, which neither of System E's sets, Π₁ and Π₂, lists (§3.7,
p. 725). Beyond the placement, the side costs no more than the forms of Same side 3 and
Postulate 1, as the theorem `Rule.of_placement_of_join` shows. Equivalence with
System E's two-rule presentation is not claimed. The edition permits direct use of
this rule only in I.4 and I.8.
-/

namespace Elements

/-- The library's primitive words, read by the restricted calculus. -/
noncomputable def primitives : Superposition.Interpretation where
  Point := Point
  Line := Line
  OnLine := OnLine
  Between := Between
  SameSide := SameSide
  Length := Length
  Angle := Angle
  Area := Area
  len := len
  ang := ang
  area := area

end Elements

namespace Elements.Tacit

/-- **Superposition.** A hypothetical placement of a triangle on a given ray and
side permits a restricted derivation of metric equalities about the figure already
given. The derivation introduces no further objects, cites each geometric law it
uses, and exports no symbol of the placement. -/
axiom superposition : Superposition.Rule primitives

end Elements.Tacit
