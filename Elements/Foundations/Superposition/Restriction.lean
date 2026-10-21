module

public import Elements.Foundations.Superposition.Soundness

/-!
# Superposition, restricted: what the rule cannot do

The restriction theorem of [brief 0009](../../../docs/briefs/0009-superposition.md), for the
interpreted calculus. The represented derivation system cannot export the placement's
objects as witnesses, nor take construction steps inside the placement. Part 1 is in
`Syntax.lean`; part 3 spans `Syntax.lean`, `Soundness.lean` and this file; parts 2 and 4 are
below, and part 5 is in `Soundness.lean`. All five parts are theorems.

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
   a universal statement, with nothing to construct. And every law I.4 cites is proved with
   no rule that constructs (`Cited.holds_of_drawsNothing`, `Prop4.cites_drawNothing`); I.8
   cites I.7, whose proof draws (brief 0009, question 4, approved as prototyped on
   20 October 2026; its finishing is tracked in #150).
4. **The rule's part about the figure asserts no placed point** (`Rule.Figure`,
   `Rule.iff_figure`, `Rule.Figure.restrict`). The rule's hypotheses are the cited laws
   (from a fixed list, each a universal statement over its letters), the given facts and the
   conclusion (data over the figure's numbered symbols: no point, no straight line, no
   proposition), a derivation (over symbols, and before any valuation), and a valuation of
   the figure's symbols that satisfies the guards and the given facts. B′, C′ and the side
   occur only as symbols inside the derivation, and no hypothesis gives them a point or a
   straight line. But two hypotheses range over every point or straight line of I, and so
   over wherever B′ and C′ might be: the cited-law hypothesis, `∀ c ∈ cites, c.Holds I`, and
   the `Triangle` guard, that no straight line passes through the three corners.
   `Rule.Figure I cites` is the statement of `Rule.infer` without the first, and `Rule I`
   holds exactly when it holds for every list of laws that hold in I (`Rule.iff_figure`).
   The theorem is that the part about the figure, if it holds in I, holds in every J
   that sits in I (`Interpretation.Embedding`), keeping incidence, betweenness, sides, the
   equalities of lengths, angles and areas, and the straight line through any two of its
   points (a straight line of I through two distinct points of J is one of J's, and a point
   of J on a straight line of I is on one of J's). The guards and the given facts pass from
   J to I, the `Triangle` guard by the kept straight line, and the conclusion comes back.
   Nothing asks that J have the points B′ and C′ would go to: the part about the figure
   asserts no placed point. The cited-law hypothesis contributes the laws, assumed of every
   point and straight line of I. It is the one hypothesis that does not pass from J to I,
   since a law true of every point of J need not be true of every point of I. That is why
   `Rule.Figure` leaves it out, and why `Rule I` gives the part about the figure in J only
   for laws that hold in I.

What part 4 does not say. A valuation can make a true given fact equivalent to any
proposition the proof can name, "no placement exists" among them (`valuation_encodes`): the
symbols carry nothing, but the points the valuation chooses can. The derivation cannot see
that, since it works on symbols and holds under every valuation (`Derives.sound`). Whether
such a premise could still recover the placement through what the rule asserts, with the
laws it cites, is the non-derivability question, which these results do not claim to settle.
`valuation_encodes` is kept as a warning of this, and so is `Metric.holds_const`: every
exported formula holds when all its point symbols stand for one point, but that valuation
never meets the guards, since it puts D and G at one point, so it shows nothing about the
rule's figures.

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

/-! ## 4. The rule's part about the figure asserts no placed point

`Rule.Figure I cites` is the statement of `Rule.infer` for the cited laws `cites`, without the
hypothesis that they hold (`Rule.iff_figure`). It passes from I to any part of I that
keeps the primitive relations and the straight line through any two of its points
(`Rule.Figure.restrict`), and such a part may lack every point a placement would use. The
section ends with two warnings, `Metric.holds_const` and `valuation_encodes`. -/

/-- **The rule's part about the figure.** The statement of `Rule.infer` for the cited laws
`cites`, without its hypothesis that they hold: a derivation of an equality over the figure's
symbols, from the given facts, the guards and what the placement keeps, gives that equality in
every figure of I that satisfies the guards and the given facts. -/
def Rule.Figure (I : Interpretation) (cites : List Cited) : Prop :=
  ∀ {n m : Nat} {Γ : List (Lit (Fin n) (Fin m))} {a b c d g h : Fin n} {l : Fin m}
    {φ : Metric (Fin n)},
    Derives cites (branch Γ a b c d g h l) (Lit.pos (φ.map Name.given).toAtom) →
    ∀ v : Val I (Fin n) (Fin m), Triangle I (v.pt a) (v.pt b) (v.pt c) →
      I.OnLine (v.pt d) (v.line l) → I.OnLine (v.pt g) (v.line l) → v.pt d ≠ v.pt g →
      ¬ I.OnLine (v.pt h) (v.line l) → (∀ ℓ ∈ Γ, ℓ.Holds v) → φ.Holds v

/-- **The rule is its part about the figure, for laws that hold.** Both directions hold by the
definitions alone, so `Rule.Figure` is the statement of `Rule.infer` without the cited-law
hypothesis, and a change to either breaks this proof. -/
theorem Rule.iff_figure :
    Rule I ↔ ∀ cites : List Cited, (∀ c ∈ cites, c.Holds I) → Rule.Figure I cites :=
  ⟨fun S _ hcites => S.infer hcites, fun h => ⟨fun hcites => h _ hcites⟩⟩

/-- **A part of an interpretation.** `J.Embedding I` puts each point and each straight line of
J at one of I, distinct points at distinct points. Incidence, betweenness, sides and the
equalities of lengths, angles and areas hold in J exactly when they hold of the images in I.
And J keeps the straight line through any two of its points: a straight line of I through
two distinct points of J is the image of one of J, and a point of J on a straight line of
I is on a straight line of J. Nothing asks that J have any further point. The points of
the plane with rational coordinates, with the straight lines through two of them, are such a
part of the plane (brief 0009, "Evidence before landing"). -/
structure Interpretation.Embedding (J I : Interpretation) where
  /-- The point of I that each point of J is. -/
  pt : J.Point → I.Point
  /-- The straight line of I that each straight line of J is. -/
  line : J.Line → I.Line
  /-- Two points of J that are one point of I are one point. -/
  pt_inj : ∀ {p q : J.Point}, pt p = pt q → p = q
  /-- A point lies on a straight line in I exactly when it does in J. -/
  onLine_iff : ∀ {p : J.Point} {L : J.Line}, I.OnLine (pt p) (line L) ↔ J.OnLine p L
  /-- A point lies between two others in I exactly when it does in J. -/
  between_iff : ∀ {p q r : J.Point}, I.Between (pt p) (pt q) (pt r) ↔ J.Between p q r
  /-- Two points lie on one side of a straight line in I exactly when they do in J. -/
  sameSide_iff : ∀ {p q : J.Point} {L : J.Line},
    I.SameSide (pt p) (pt q) (line L) ↔ J.SameSide p q L
  /-- Two lengths are equal in I exactly when they are in J. -/
  len_iff : ∀ {p q r s : J.Point},
    I.len (pt p) (pt q) = I.len (pt r) (pt s) ↔ J.len p q = J.len r s
  /-- Two angles are equal in I exactly when they are in J. -/
  ang_iff : ∀ {p q r s t u : J.Point},
    I.ang (pt p) (pt q) (pt r) = I.ang (pt s) (pt t) (pt u) ↔ J.ang p q r = J.ang s t u
  /-- Two triangles are equal in I exactly when they are in J. -/
  area_iff : ∀ {p q r s t u : J.Point},
    I.area (pt p) (pt q) (pt r) = I.area (pt s) (pt t) (pt u) ↔ J.area p q r = J.area s t u
  /-- **The straight line through two points is kept.** A straight line of I through two
  distinct points of J is the image of a straight line of J. -/
  line_through : ∀ {p q : J.Point} {N : I.Line}, p ≠ q → I.OnLine (pt p) N →
    I.OnLine (pt q) N → ∃ L : J.Line, line L = N
  /-- A point of J on a straight line of I is on a straight line of J. -/
  on_line : ∀ {p : J.Point} {N : I.Line}, I.OnLine (pt p) N → ∃ L : J.Line, J.OnLine p L

namespace Interpretation.Embedding

variable {J : Interpretation} (e : J.Embedding I)

/-- A figure of J, read in I: each symbol stands for the image of what it stands for in
J. -/
def val (v : Val J P L) : Val I P L := ⟨e.pt ∘ v.pt, e.line ∘ v.line⟩

/-- An atom says the same of a figure of J in I as in J. -/
theorem atom_holds (v : Val J P L) (a : Atom P L) : a.Holds (e.val v) ↔ a.Holds v := by
  cases a with
  | eq => exact ⟨e.pt_inj, congrArg e.pt⟩
  | onLine => exact e.onLine_iff
  | between => exact e.between_iff
  | sameSide => exact e.sameSide_iff
  | len => exact e.len_iff
  | angle => exact e.ang_iff
  | area => exact e.area_iff

/-- A literal says the same of a figure of J in I as in J. -/
theorem lit_holds (v : Val J P L) (ℓ : Lit P L) : ℓ.Holds (e.val v) ↔ ℓ.Holds v := by
  cases ℓ with
  | pos a => exact e.atom_holds v a
  | neg a => exact not_congr (e.atom_holds v a)

/-- A metric formula says the same of a figure of J in I as in J. -/
theorem metric_holds (v : Val J P L) (m : Metric P) : m.Holds (e.val v) ↔ m.Holds v :=
  e.atom_holds v m.toAtom

/-- **Three points of J on one straight line of I are on one straight line of J**, the
kept straight line through two of them, or, if they are one point, a straight line through it. -/
theorem collinear {A B C : J.Point} (h : Collinear I (e.pt A) (e.pt B) (e.pt C)) :
    Collinear J A B C := by
  obtain ⟨N, hA, hB, hC⟩ := h
  by_cases hAB : A = B
  · subst hAB
    by_cases hAC : A = C
    · subst hAC
      obtain ⟨L, hL⟩ := e.on_line hA
      exact ⟨L, hL, hL, hL⟩
    · obtain ⟨L, rfl⟩ := e.line_through hAC hA hC
      exact ⟨L, e.onLine_iff.1 hA, e.onLine_iff.1 hA, e.onLine_iff.1 hC⟩
  · obtain ⟨L, rfl⟩ := e.line_through hAB hA hB
    exact ⟨L, e.onLine_iff.1 hA, e.onLine_iff.1 hB, e.onLine_iff.1 hC⟩

/-- A triangle of J is a triangle of I. -/
theorem triangle {A B C : J.Point} (h : Triangle J A B C) :
    Triangle I (e.pt A) (e.pt B) (e.pt C) :=
  fun hc => h (e.collinear hc)

end Interpretation.Embedding

/-- **Part 4: the rule's part about the figure passes to any part of the interpretation.** If
it holds in I for the cited laws `cites`, it holds for the same laws in every J embedded in
I. Each hypothesis passes from J to I: the guards and the given facts by the embedding,
and the `Triangle` guard, which ranges over every straight line, by the straight line J
keeps through two distinct corners, or, if the corners are one point, by a straight line
of J through it; the conclusion comes back. Nothing asks that J have the points B′ and C′
or the straight line the side would go to, so the part about the figure asserts no placed
point. The cited-law hypothesis of `Rule.infer` is the one left out: it ranges over every
point and straight line of the interpretation, and a law true of every point of J need not
be true of every point of I. -/
theorem Rule.Figure.restrict {J : Interpretation} (e : J.Embedding I) {cites : List Cited}
    (hI : Rule.Figure I cites) : Rule.Figure J cites := by
  intro n m Γ a b c d g h l φ dφ v hT hd hg hdg hh hΓ
  refine (e.metric_holds v φ).1 (hI dφ (e.val v) (e.triangle hT) (e.onLine_iff.2 hd)
    (e.onLine_iff.2 hg) (fun hdg' => hdg (e.pt_inj hdg')) (fun hh' => hh (e.onLine_iff.1 hh'))
    fun ℓ hℓ => (e.lit_holds v ℓ).2 (hΓ ℓ hℓ))

/-! ### The warnings -/

/-- **Every exportable formula holds at a constant point valuation.** Given a point X and a
valuation of the line symbols, every equality of magnitudes holds when all the point symbols
stand for X. So, wherever such a valuation is available, no exported formula fails in every
figure. The rule never concludes `False` itself. Under a given valuation an exported formula
can still be false, and can contradict the given facts; see the module's note. A warning, not
part 4: the constant valuation never meets the guards, since it puts D and G at one point. -/
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
says none of them is placed. `Rule.infer` has no such premise. The placement's points are
symbols in a derivation, and no rule of a derivation concludes anything from a contradiction.
Two of its hypotheses range over every point or straight line, the cited-law hypothesis and
the `Triangle` guard; the rule without the first, the `Triangle` guard included, passes to
any part of the interpretation, even one that lacks the placed points
(`Rule.Figure.restrict`). -/
theorem eliminator_false_gives_exists (placed : I.Point → I.Point → Prop)
    (h : (∀ B' C' : I.Point, placed B' C' → False) → False) : ∃ B' C' : I.Point, placed B' C' :=
  Classical.byContradiction fun hne => h fun B' C' hp => hne ⟨B', C', hp⟩

end Elements.Superposition
