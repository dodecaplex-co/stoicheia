module

public import Elements.Foundations.Superposition.Soundness

/-!
# Superposition, restricted: what the rule cannot do

The restriction theorem of [brief 0009](../../../docs/briefs/0009-superposition.md), for the
interpreted calculus. The represented derivation system cannot export the placement's
objects as witnesses, nor take construction steps inside the placement. Part 1 is in
`Syntax.lean`, parts 2 to 4 below, and part 5 in `Soundness.lean`. Parts 1, 2, 3 and 5 are
theorems; part 4 is read off the statement of `Rule.infer`, and its one theorem is
`Metric.holds_const`.

1. **No symbol of the placement is exported** (`exportable_iff`, `not_exportable_second`,
   `not_exportable_third`). The rule's conclusion is a `Metric` over the figure's symbols; a
   formula of the placement that names B′ or C′ is the image of none. A `Metric` names no
   straight line, so the side laid down is never exported either. The placement's symbols
   are fresh by their type: no symbol of the figure is one of them.
2. **The conclusion says nothing of where the placement's symbols went**
   (`Metric.holds_place`): an exported formula reads the same whatever points B′ and C′ and
   whatever straight line the side are taken to be.
3. **No construction step in the placement** (`Derives.no_construction`, `Derives.map`,
   `Cited.holds_iff`). The placement's symbols are fixed by its type: the figure's, and the
   three the placement lays down. No rule adds one: a logical rule names symbols already
   there, and citing a law puts symbols already there for its letters. Every derivation
   holds under every valuation of exactly those symbols that makes its context true, so no
   step needs a point or a straight line the symbols do not already stand for. Every law is
   a universal statement, with nothing to construct. What a law's own proof draws, outside
   the placement, is question 4 of brief 0009 (approved as prototyped on 20 October 2026;
   its finishing is tracked in #150): the rule asks only that each cited law hold, and the
   certificate records the construction rules beneath each law's proof (`cited_laws`).
4. **No hypothesis of the rule speaks of the placement.** The rule's hypotheses are the cited
   laws (from a fixed list, each a universal statement over its letters), the given facts
   and the conclusion (data over the figure's numbered symbols: no point, no straight line,
   no proposition), a derivation (over symbols, and before any valuation), and a valuation
   of the figure's symbols that satisfies the guards and the given facts. B′, C′ and the side
   occur only as symbols inside the derivation, and no hypothesis gives them a point or a
   straight line or quantifies over them; Astra's second observation needs a premise that
   does. This part is read off the statement of `Rule.infer`, not proved; its one theorem,
   `Metric.holds_const`, shows that no exported formula is unsatisfiable wherever a point
   and the required valuation of line symbols are given.

What part 4 does not say. A valuation can make a true given fact equivalent to any
proposition the proof can name, "no placement exists" among them (`valuation_encodes`): the
symbols carry nothing, but the points the valuation chooses can. The derivation cannot see
that, since it works on symbols and holds under every valuation (`Derives.sound`). Whether
such a premise could still recover the placement through what the rule asserts is the
non-derivability question, which these results do not claim to settle.

The two observations of Astra's answer are kept as theorems, as warnings for anyone who
tries a shorter road: a Prop-valued eliminator over every conclusion is the existential rule
itself (`eliminator_iff_exists`), and one allowed only `False` still gives the points back,
classically (`eliminator_false_gives_exists`). Astra checked both in Lean 4.35; they are
restated here with thanks.

What is not here: a non-derivability result, that the restricted rule with the other laws
cannot prove the existential placement principle. Astra's third kind of evidence asks for
one only if it is claimed, with the fragment of rules stated; none is claimed here (brief 0009,
"Evidence before landing").
-/

@[expose] public section

namespace Elements.Superposition

variable {I : Interpretation} {P L : Type}

/-! ## 2. The conclusion says nothing of where the placement's symbols went -/

/-- **An exported formula reads the same wherever B′, C′ and the side are.** Read in the
placement, with B′ and C′ at any points and the side along any straight line, an exported
formula says exactly what it says of the figure. -/
theorem Metric.holds_place (m : Metric P) (v : Val I P L) (B' C' : I.Point) (N : I.Line) :
    (m.map Name.given).Holds (v.place B' C' N) ↔ m.Holds v :=
  Metric.holds_map Name.given LineName.given _ m

/-! ## 3. No construction step -/

/-- **No construction step.** Whatever a derivation in the placement proves holds under every
valuation of the figure's symbols and the placement's three that makes the placement's
context true: the same valuation, not one extended by a new point or straight line. No step
needs an object the symbols do not already stand for. (`Derives.sound`, said of the
placement, so that a reader can find it.) -/
theorem Derives.no_construction {cites : List Cited} (hcites : ∀ c ∈ cites, c.Holds I)
    {Γ : List (Lit P L)} {a b c d g h : P} {l : L} (w : Val I (Name P) (LineName L))
    (hw : ∀ ℓ ∈ branch Γ a b c d g h l, ℓ.Holds w) {ℓ : Lit (Name P) (LineName L)}
    (dℓ : Derives cites (branch Γ a b c d g h l) ℓ) : ℓ.Holds w :=
  Derives.sound hcites w hw dℓ

/-! ## 4. No hypothesis speaks of the placement

Part 4 is a reading of the rule's statement, not a theorem; this section holds its one
theorem, `Metric.holds_const`, and the warning `valuation_encodes`. -/

/-- **Every exportable formula holds at a constant point valuation.** Given a point X and a
valuation of the line symbols, every equality of magnitudes holds when all the point symbols
stand for X. So, wherever such a valuation is available, no exported formula fails in every
figure. The rule never concludes `False` itself. Under a given valuation an exported formula
can still be false, and can contradict the given facts; see the module's note. -/
theorem Metric.holds_const (m : Metric P) (X : I.Point) (N : L → I.Line) :
    m.Holds (⟨fun _ => X, N⟩ : Val I P L) := by
  cases m <;> exact rfl

/-- **A valuation can make a literal say anything.** The literal "0 is 1", over two point
symbols, holds under the valuation that puts 0 at `if Q then X else Y` and 1 at Y exactly
when Q fails, for X other than Y. So a true given fact can be equivalent to any proposition
the proof can name, "no placement exists" among them. The symbols carry nothing; the points
the valuation chooses can. The derivation cannot see this, since it works on symbols and holds
under every valuation (`Derives.sound`); whether such a premise could recover the placement
through what the rule asserts is the non-derivability question (brief 0009). -/
theorem valuation_encodes (Q : Prop) {X Y : I.Point} (hXY : X ≠ Y) :
    (Lit.pos (.eq 0 1) : Lit (Fin 2) (Fin 0)).Holds
      (⟨fun i => if i = 0 then (haveI := Classical.propDecidable Q; if Q then X else Y) else Y,
       Fin.elim0⟩ : Val I (Fin 2) (Fin 0)) ↔ ¬ Q := by
  simp only [Lit.Holds, Atom.Holds]
  by_cases hQ : Q
  · simp [hQ, hXY]
  · simp [hQ]

/-! ## The shorter roads, and why they fail -/

/-- **Astra's first observation.** An eliminator that lets the placement prove any proposition
Q whatever is the existential rule itself: take Q to be "such points exist". This is why the
restricted rule is stated over derivations, not over propositions. -/
theorem eliminator_iff_exists (placed : I.Point → I.Point → Prop) :
    (∀ Q : Prop, (∀ B' C' : I.Point, placed B' C' → Q) → Q) ↔ ∃ B' C' : I.Point, placed B' C' :=
  ⟨fun h => h _ fun B' C' hp => ⟨B', C', hp⟩, fun ⟨B', C', hp⟩ _ hQ => hQ B' C' hp⟩

/-- **Astra's second observation.** Even an eliminator allowed only the conclusion `False`,
which names no point, gives the points back: it says their absence is absurd, and Lean's
classical logic turns that into existence. Its premise quantifies over the placed points and
says none of them is placed. No hypothesis of `Rule.infer` quantifies over the placement's
points, which are symbols in a derivation, and no rule of a derivation concludes anything
from a contradiction. -/
theorem eliminator_false_gives_exists (placed : I.Point → I.Point → Prop)
    (h : (∀ B' C' : I.Point, placed B' C' → False) → False) : ∃ B' C' : I.Point, placed B' C' :=
  Classical.byContradiction fun hne => h fun B' C' hp => hne ⟨B', C', hp⟩

end Elements.Superposition
