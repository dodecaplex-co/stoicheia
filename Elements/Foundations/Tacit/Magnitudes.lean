import Elements.Foundations.Magnitudes

/-!
# Tacit rules: how magnitudes add and compare

Euclid's Common Notions are not quite enough to do the arithmetic of
magnitudes that Book I actually does. He silently assumes, for example, that it
doesn't matter in which order two angles are added, and that of two unequal
lengths one is the greater. These are those silent assumptions.

They say that each kind of magnitude behaves like the non-negative part of an
ordered sum of quantities: System E, §3.5, the "magnitude axioms" (Avigad,
Dean and Mumma, 2009). From them, all five of Euclid's Common Notions follow
as theorems (see `Foundations/CommonNotions.lean`).
-/

namespace Elements.Tacit

variable {k : Kind}

/-- Adding is associative. (System E §3.5) -/
axiom add_assoc (a b c : Magnitude k) : a + b + c = a + (b + c)

/-- The order of adding does not matter. (System E §3.5) -/
axiom add_comm (a b : Magnitude k) : a + b = b + a

/-- Adding nothing changes nothing. (System E §3.5) -/
axiom add_zero (a : Magnitude k) : a + 0 = a

/-- No magnitude is less than itself. (System E §3.5) -/
axiom lt_irrefl (a : Magnitude k) : ¬ a < a

/-- What is less than the less is less still. (System E §3.5) -/
axiom lt_trans {a b c : Magnitude k} : a < b → b < c → a < c

/-- Of two magnitudes, one is less, or they are equal, or the other is less.
(System E §3.5) -/
axiom lt_trichotomy (a b : Magnitude k) : a < b ∨ a = b ∨ b < a

/-- Nothing is less than zero. (System E §3.5) -/
axiom not_lt_zero (a : Magnitude k) : ¬ a < 0

/-- Adding the same thing to both sides keeps "less than". (System E §3.5) -/
axiom add_lt_add_right {a b : Magnitude k} (c : Magnitude k) : a < b → a + c < b + c

end Elements.Tacit
