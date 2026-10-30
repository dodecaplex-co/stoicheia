# Brief 0009: a restricted rule of superposition

*29 October 2026: #150 no longer holds the release.* On 27 October 2026 the owner chose,
of the options put to them, "Defer (Recommended)" (decision 31), so that the rest of
superposition's work waits until after the release, and then "All five (Recommended)", by
which #150 no longer carries the label `blocks-release`. #150, the coordinator's record of
both choices, gives the deferral's condition: the work returns to the release if the
release's measurement puts Book I under 95. On 29 October 2026, as the release's cards
were sorted, the owner's decision was to "keep the 27 October deferral of #150" (the
coordinator's orders of that day). The replacement's issue, #75, is closed on its landed
work, and #150 stays open and carries the rest after the release
([the decision](../decisions/2026-10-29-superposition-deferred.md)). So round 4's words
below, that #150 "holds every release until it closes", record the plan of 20 October and
no longer hold; the decisions page's entry of 20 October that says the same stays as
written, as a dated record. The kept side's cost is no longer only read off the model's
proof: since 25 October 2026 it has been a theorem, `Rule.of_placement_of_join` in
`Soundness.lean` ([its decision](../decisions/2026-10-25-superposition-side-cost.md)),
whose pin in `Audit/Superposition.lean` #150 still tracks. The lines that said otherwise
in the present tense, in round 4's correction, under "The placement's fresh symbols and
retained facts" and "The model obligation, met", and in the answers to questions 5 and 7,
are corrected in place; what
they record of earlier revisions stands. No statement, definition, interface or lock
changes.

*22 October 2026, #312: I.4 and I.8 write no number. Where "A finite symbolic context"
below says that a proof names its symbols with an inductive type of its own "and numbers
them once", the numbering is now done for it: `Symbols.ofList`, in `Soundness.lean`, takes
the list of the figure's lettered points, or of its straight lines, and computes their count
and places, so that neither proof writes a count or a position
([the decision](../decisions/2026-10-22-superposition-symbols-from-list.md)). `Symbols`,
`Rule.apply`, the rule, the lock and every statement are unchanged.*

*21 October 2026: the second retirement wave lands, with the review of the cited laws'
proofs that round 4 ties to it (#150, question 4's reconciliation and question 5's credit
to the side).* Thirty-one more System E rules are theorems. Four of them, `same_side_symm`,
`pasch3`, `eq_of_len_eq_zero` and `triple_incidence2`, bring construction rules into the
proofs of four of the seven laws I.4 cites: `neOfLen` and `rayUnique`, through Metric 1,
which draws a circle, and `rayOfAngle` and `rayOfAngleSide`, through Same side 2, Triple
incidence 2 and Pasch 3. I.8 cites the first two as well. Only `lenSymm`, `angleSymm` and
`areaCongruent` are proved with none. The certificate's `cited_laws` lists each law's
construction rules, and the audit pins record each proof's axioms. The kept side AC serves
`rayOfAngle`, whose law names it as its third straight line; `rayOfAngleSide` uses no side.
Its law is Pasch 3, now proved by joining the law's point P to a point of the line
(`Postulate1` in `Elements/Figure/RuleBase.lean`), and `rayOfAngle`'s proof, through Same
side 5 inside Triple incidence 2, may join P to a point it produces. In I.4, P is the
placed corner C′, so round 1's defect, a straight line drawn through a point of the
placement, returns inside these proofs, outside the placement. Only question 4's
permissive reading admits it: each law asserts no existence, and citing it draws nothing in
the placement, whatever its proof draws. No retired axiom is restored to avoid it. The
table under "What the laws' proofs draw" and the lines that described the laws' proofs in
the present tense now give this revision's values; what they record of earlier revisions
stands.

*21 October 2026, #150, question 2: part 4 of the restriction is now a theorem.
`Rule.Figure` is the statement of `Rule.infer` without its cited-law hypothesis, tied to the
locked rule by `Rule.iff_figure`, and `Rule.Figure.restrict` proves that it passes to any part
of an interpretation that keeps the primitive relations, every straight line through two
distinct points, and, when one of its points lies on an ambient straight line, some straight
line through that point (`Interpretation.Embedding`), a part that may lack every point the
placement would use. `Cited.holds_all` gives every cited law in one statement. The
restriction's theorems are pinned by their statements as well as their axioms, in
[`Audit/Superposition.lean`](../../Audit/Superposition.lean). `Rule`, the lock and every
statement are unchanged, and non-derivability stays unclaimed. Where round 4 below calls
part 4 an inspection of `Rule.infer`, this note supersedes it; the lines that said so in
the present tense are corrected in place.*

*21 October 2026: for question 4 of #150, the coordinator takes route (b)
([decisions](0002-decisions.md#21-october-2026), 21 October 2026).* The hand-set flag
`Cited.drawsNothing`, the theorem `Cited.holds_of_drawsNothing` that proved the laws it
marked, and I.4's check of it, `Prop4.cites_drawNothing`, are retired. Under the permissive
reading the owner approved, `Rule` asks only that each cited law hold, so the flag carried
no logical weight; what it recorded was a judgement made by eye from the pinned axiom
closures, which no check confirmed. I.4 now proves its laws one by one, as I.8 does, and
the certificate computes, for I.4 and I.8, the construction rules beneath each cited law's
proof (`cited_laws` in `facts.json`), with "construction rule" defined in
[FORMALIZATION.md](../FORMALIZATION.md#construction-rules), section 9. The lines below that
spoke of the flag as present now record its retirement; what they record of earlier
revisions stands.

*20 October 2026, round 4: the replacement lands on the answers to questions 2, 4 and 5
that the owner approved "as prototyped", and their finishing is tracked in #150, which
holds every release until it closes. This revision of brief 0009 follows
[WORKFLOW.md](../WORKFLOW.md), section 2, "Correcting a frozen brief". It changes no
statement, definition or interface: it says where each approved answer still rests on a
reading, a flag set by hand or a sentence checked by eye, and it gives the landing order
with the two retirement waves. Round 3, the same day, recorded the owner's approval of the
restricted rule delivered on `lean/superposition-restricted`, with questions 2, 4 and 5
answered as prototyped, the model's import of the four pure modules and the page claim
"a restricted inference in System E's style". It records the replacement first delivered
at `aa96ab8`, from `origin/main` at `39ae65c`, and the approval after main was merged at
`bccc3f52`. The tooling pull requests have landed as #180 and #182. Landing remains
conditional on /no-mistakes and an independent Codex read of the model lane. The code
states what we formalised; the brief, the review records and the pages must agree with it
([FORMALIZATION.md](../FORMALIZATION.md), section 1).*

**Baseline update, 20 October 2026: A1 has landed.** The integration merge at
`bd86a7b6` has the restricted-rule revision `9fc4bdc9` as one parent and
`tooling/superposition-model-check` at `5a848389` as the other. The tooling parent carries
main at `7834e3a7`, A1 and both superposition tooling branches. A1's eight retired axioms
remain theorems: the foundation has 79 axioms, including 73 tacit rules, with
`Tacit.superposition` restated as `Elements.Superposition.Rule Elements.primitives`.
The regenerated vocabulary has 208 entries, and the certificate has 29 expectations.
Earlier 87-axiom and 206/208-word measurements below describe their named revisions before
this A1 integration.
The landed retirements also change the overlap catalogue: Circle 4 is a corollary of
I.7, Diagram-angle 3 follows I.13, and Generalities 2 is proved in Book Zero. Circle 2
is proved from Circle 3, which remains III.2's axiom overlap. The restricted rule
separately retires the construction shortcuts for I.2, I.3 and I.23. A2 has not landed.

**Baseline update, 21 October 2026: the second wave is integrated.** By the owner's
decision of 19 October ("Please do both. 79 is rather large with so many books in front
of us"), thirty-one more rules became theorems; the merge of `lean/retire-axioms-2` at
`d2c45450` with the wave's preparation, itself merged with this replacement (`bae3d09f`),
integrates them after it, and a later merge brings in #150's answers to questions 4 and 2.
The foundation has 48 axioms, including 42 tacit rules, with `Tacit.superposition` still
restated as `Elements.Superposition.Rule Elements.primitives`; the regenerated vocabulary
keeps its 208 entries, and the certificate has 41 expectations. The audit pins of
`Audit/Superposition.lean` that named retired rules now record what Lean prints. No
superposition statement changes here, and the review of the cited laws' proofs that round 4
ties to this landing is the note of 21 October on the second retirement wave above.

**Round 4's correction.** The owner approved questions 2, 4 and 5 "as prototyped", and
asked that the prototyped work be finished in an issue of its own, #150. There each answer
that is still a reading, a flag set by hand or an unchecked sentence becomes a theorem, a
computed check or a true record. Part 4 of the restriction was an inspection of
`Rule.infer` as locked in `Certificate/axioms.lock`, not a theorem, until it became one on
21 October 2026 (above); `Cited.drawsNothing` was
a classification set by hand, whose values `Prop4.cites_drawNothing` evaluated but whose
meaning was judged by eye from the audit's pinned axiom closures, until its retirement on
21 October 2026 (above); and the cost of the kept side was checked by reading the model's
proof, until it became the theorem `Rule.of_placement_of_join` on 25 October 2026 (the
note of 29 October above). Non-derivability stays unclaimed. "Landing" gives the order:
the first retirement wave, then this replacement, then the second wave, whose landing carries the review of the
cited laws' construction rules (`cited_laws`) and the audit pins.

**Round 3's correction.** Round 2 described a hypothesis in six prototype files; the branch
now declares `Tacit.superposition : Superposition.Rule primitives` in the foundations.
The old axiom returned `∃ B' C' : Point, …`, points with the placement's properties. Its
replacement permits only a represented derivation of an equality about the given figure.
The reason is the construction shortcut described below. I.4 and I.8 use the replacement
with their statements and Heath lines unchanged; their dependents rebuild, and 116 of the
122 certificate entries after the main merge rest on the restated rule. The model proves
its law in the plane.
The owner approved questions 2, 4 and 5 as prototyped on 20 October 2026: the branch
follows the five-part restriction, permits I.7 inside I.8's placement, and keeps the
side laid down. The model's import of the four pure modules and the page claim
"a restricted inference in System E's style" are approved too. Finishing the three
answers is tracked in #150.

**Prototype history.** `lean/superposition-prototype` began at `f17b427` and merged main at
`e04f318`. Its six files in `Staging/Superposition/` comprised 1,697 lines and passed
`lake build Staging`. They have moved to the production homes below; the staging directory
is deleted on this branch.

**Round 2.** The first prototype named points by Lean points. Its verification showed that
this let a given fact say "no placement exists", through a name such as `if Q then X else
Y`, so that one reason the brief gave for the restriction was false; and that two cited laws
did construction in their proofs that the brief did not disclose. Round 2 redesigned the
prototype on a finite symbolic context, as Astra advised and as open question 3 of round 1
proposed: names are symbols, the figure is a valuation given separately, cited laws are data
over letters, and the placement adds fresh symbols that no conclusion can mention. I.4 and
I.8 were proved again from the rule, and the restriction theorem for the new design; each
finding of the verification is answered below ("The reviews").

## The owner's decision

On 18 October 2026, after Astra's third answer, the owner decided on superposition
(#75): prototype a genuinely restricted rule now, as a checked inference over represented
derivations, with I.4 and I.8 proved from it, a restriction theorem and the model's
justification; land it only when complete; and meanwhile disclose that our rule is
stronger, as a construction principle, than System E's. The same day the owner decided
that every circle has a centre (#59) and that the formal model starts now in `model/` (#73).
The prerequisite #40, the model's law names as a pinned data file, is now met by
`tests/model/laws.toml`. Before A1, the replacement restated one axiom and kept the
total at 87; on the landed A1 baseline it restates that axiom and keeps the total at 79.

On 20 October 2026 the owner approved the completed replacement with questions 2, 4
and 5 answered as prototyped, the model's import of the four pure modules and the page
claim "a restricted inference in System E's style". The exact approval is recorded in
[the decisions entry](0002-decisions.md#20-october-2026); finishing the answers to
questions 2, 4 and 5 is tracked in #150. The tooling pull requests land
first; landing also requires /no-mistakes and an independent Codex read of the model
lane. The read at `cdcf3b9e` found no weakening and one older relative-path defect in
`model/Check/Generator.lean`. A second read, at `0085b443`, found that an escaped module
name such as `Model.«..».Check.Original` passed the Model import audit. Both are fixed on
`tooling/superposition-model-check`, which also checks the compiled import graph and
refuses a source whose extension is a case variant of `.lean`. The read owed before
landing is of the revision that lands.

## The problem

**The old rule handed back points.** Before this replacement, `Tacit.superposition` said
that the triangle ABC could be laid down with A on D, B on the ray from D through G and C
on H's side of the straight line L, keeping its sides and angles, and returned B′ and C′:
`∃ B' C' : Point, …`. The direct-use policy confined it to I.4 and I.8, but did not restrict
what it asserted. The former audit lemma `Audit.I_23` used it to copy an angle with seven
rules naming the ray and the side. That construction shortcut and those for I.2 and I.3
are retired on this branch ([overlaps](../reports/overlaps.md)).

**System E's rule does not.** Avigad, Dean and Mumma treat superposition as an elimination
rule (*A formal system for Euclid's Elements*, Review of Symbolic Logic 2 (2009), §3.7,
p. 725): "superposition is used as an elimination rule: if you can derive a conclusion
assuming the existence of some new objects, you can infer that the conclusion holds without
the additional assumption. In Euclid's case, one is barred, however, from using the
assumption to construct new objects." The section gives the rule as a sequent inference.
We read it so: if Γ ⇒ ∃x⃗. Δ, and Γ, Δ with the facts Π of the placement give Δ′, then
Γ ⇒ ∃x⃗. Δ, Δ′, where Δ′ speaks only of objects already present. The section says nothing
explicit about constructions inside the branch, or about the vocabulary of Δ′; those
readings are ours.

**Two shorter roads fail.** Astra's third answer (question 2) shows why the restriction
cannot be a Lean proposition about continuations:

- an eliminator `∀ Q : Prop, (∀ B' C', Placed B' C' → Q) → Q` is the existential rule
  itself: take Q to be "such points exist";
- an eliminator allowed only conclusions that name no new point is no better, for `False`
  names none: it says the points' absence is absurd, and Lean's classical logic turns that
  into existence.

Neither `Nonempty`, nor a conclusion in `Prop`, nor a restriction on the conclusion's free
variables solves this. What Astra recommends, and the owner decided to prototype, is a
checked inference over explicitly represented formulas and derivations.

## The design

### One calculus, two interpretations

The four pure modules are
[`Syntax.lean`](../../Elements/Foundations/Superposition/Syntax.lean),
[`Semantics.lean`](../../Elements/Foundations/Superposition/Semantics.lean),
[`Soundness.lean`](../../Elements/Foundations/Superposition/Soundness.lean) and
[`Restriction.lean`](../../Elements/Foundations/Superposition/Restriction.lean), all under
`Elements/Foundations/Superposition/`. Their import chain begins at `Init`; they import no
geometric word, project axiom or Book Zero lemma. Syntax is independent of any plane.
Semantics takes an `Interpretation`: carriers for points, straight lines, lengths, angles
and areas, with incidence, betweenness, sides and the three measures. It assumes no
geometric law.

[`Elements/Foundations/Tacit/Superposition.lean`](../../Elements/Foundations/Tacit/Superposition.lean)
defines `primitives`, the interpretation by the edition's words, and declares the one
restated axiom, `Tacit.superposition : Superposition.Rule primitives`. Book Zero's
[`Elements/Figure/Superposition.lean`](../../Elements/Figure/Superposition.lean) supplies the
geometric proofs of the cited laws, importing no proposition. I.7's adapter belongs to
I.8. The model interprets the same pure calculus with its own signature.

The four pure files use Lean's `module` format, `public import` and public sections. The
model already uses that format and cannot import legacy files from it. This format makes
the shared definitions available to both packages without importing the edition's geometry
into the model. It changes no mathematical declaration or proof.

### A finite symbolic context

[`Syntax.lean`](../../Elements/Foundations/Superposition/Syntax.lean) and
[`Semantics.lean`](../../Elements/Foundations/Superposition/Semantics.lean).

- A **symbol** is a member of a type the proof chooses: `P` for points, `L` for straight
  lines. The rule takes its symbols from `Fin n` and `Fin m`, so in the rule a symbol is a
  number and nothing else.
- An **`Atom`** is a primitive relation on symbols: equality of points, a point on a straight
  line, betweenness, the same side, and equality of two lengths, two angles or two
  triangles. A **`Lit`** is an atom or its denial. A literal holds no point, no straight line
  and no proposition: it says one primitive thing of the symbols it names.
- A **`Metric`** formula is an equality of lengths, of angles or of triangles, over point
  symbols only: the only conclusions the rule exports.
- A **valuation** (`Val I P L`) gives a point to each point symbol and a straight line to each
  line symbol. `Holds v` reads a formula under `v` in the interpretation `I`. The symbols
  are data; the valuation is the figure.

Two symbols are one symbol only when they are the same symbol, so a derivation, which works
on symbols, can never learn that two symbols stand for one point unless a step proves it. In
round 1 the names were Lean points, and two names were one whenever their points were equal.

**What symbols do not prevent.** A valuation chooses points, and a point can be chosen by
cases on any proposition. So a true given literal can still be equivalent to any proposition
the proof can name, "no placement exists" among them; `valuation_encodes` proves it, so that
no one claims otherwise. The derivation has no arbitrary proposition among its formulas;
`Derives.sound` gives its validity under every valuation satisfying its premises. The order
of the rule's quantifiers does not restrict how a Lean caller chooses arguments. What the
encoding could still do through the rule's content is the non-derivability question below,
which is not claimed.

**Ease of use.** A proof names its symbols with an inductive type of its own, and numbers
them once (`Symbols`, in `Soundness.lean`); `Rule.apply` uses the rule on the numbers. I.4's
symbols are `a`, …, `f` for the corners, `de` and `df` for two straight lines, and `b'`,
`c'`, `ac'` for what the placement lays down: lower case for symbols, upper case for
points, so that a reader can tell them apart at a glance.

### Laws as data, applied by one rule

[`Syntax.lean`](../../Elements/Foundations/Superposition/Syntax.lean) holds the law data and
derivations; [`Soundness.lean`](../../Elements/Foundations/Superposition/Soundness.lean)
proves their soundness, and
[`Elements/Figure/Superposition.lean`](../../Elements/Figure/Superposition.lean) proves the
geometric laws.

A **`Law`** is a list of premises and one conclusion, literals in a fixed alphabet of
letters (`Letter`: A, B, C, D, E, F, P; `LineLetter`: L, M, N). What it asserts
(`Law.Holds`) is that whatever points and straight lines the letters stand for, if the
premises hold so does the conclusion. A law has no field in which an existential claim
could be written, so it asserts no existence (`Cited.holds_iff`). In round 1 a law
was a Lean proposition, which a reviewer had to read to see that it constructed nothing; now
the datatype enforces it.

The list **`Cited`** is fixed, and `Cited.law` gives each law as data: Metric 3, Metric 4,
Metric 9, that a straight line equal to one with distinct ends has distinct ends, that on a
ray one point lies at a given distance from its start (Savile's argument), the two halves of
one ray for one angle (the point is on the ray's straight line; it is not behind the
corner), and I.7.

**Why the laws are cited rather than built in.** The rule assumes none of them; it asks
each law a derivation cites to hold, and the theorem that uses the rule supplies a proof of
each. There are two reasons.

1. *The certificate.* A derivation is data, and Lean records no dependency on the facts a
   datatype's constructors mention. Round 1's first draft built the laws in, and
   `#print axioms` for its I.4 listed Postulate 1 and one Points rule and nothing else:
   Metric 9, Savile's argument and the rest had vanished into the hypothesis, and the rule
   had silently grown to contain them. With the laws cited, the production I.4 retains
   its former axiom-name set, with `superposition` now naming the restricted rule (below).
2. *The order of the propositions.* Euclid's argument for I.8 uses I.7 inside the placement,
   and I.7 cites I.5, which rests on I.4. Were I.7 a rule of the derivation, the foundations
   would assume what Book I proves. Cited, it is supplied by the edition's I.7.

**Why the list is fixed.** A law whose premises can never hold together holds vacuously.
Were any law with any proof allowed, one whose premises describe a placement and whose
conclusion is false would hold exactly when no placement exists, and citing it would turn
that absence into a contradiction, which classical logic turns into points. A fixed list of
laws, each a specific geometric statement, cannot be chosen that way. A new law joins the
list by a revision of this brief.

### A restricted derivation judgement, with no construction steps

`Derives cites Γ ℓ` is an inductive judgement with seventeen constructors: the literal
`ℓ` follows from the literals `Γ`, all over the same symbols, by two kinds of rule.

- **Logic.** Point equality has reflexivity and symmetry rules, but no transitivity rule
  in `Derives`. Equality of lengths, angles and triangles has all three. Common Notion 4
  puts a point for one that coincides with it in a length, angle or triangle equality.
  Each of the three congruence constructors takes a `Coincidence` argument; the
  derivation supplies `Coincidence.step` when it takes that step. This proposition has
  one constructor and adds no axiom. Transformers pass the received marker along, so
  the certificate counts an actual congruence step without counting renaming alone.
- **Citing a law** (`Derives.cite`). A step names a law of `cites`, puts a symbol of the
  derivation for each letter, derives the law's premises and concludes its conclusion.

Neither kind introduces a symbol. There is no rule that constructs a point, draws a straight
line or a circle, splits cases, argues by contradiction or concludes anything from a
contradiction. That is enough for I.4 and I.8. For readable proofs, each law also has a
step of its own (`Derives.ray_unique` and the rest), proved from `cite`, with its premises
in order.

`Derives.sound` shows that whatever a derivation proves holds under every valuation that
makes its context true, once the cited laws hold: the same valuation, never one extended by
a new object. Its only axiom is `propext`, from Lean's logic: no project axiom. `Derives.map` shows that every rule is a scheme, carried along any renaming of the
symbols.

### The placement's fresh symbols and retained facts

[`Syntax.lean`](../../Elements/Foundations/Superposition/Syntax.lean) names the placement;
[`Semantics.lean`](../../Elements/Foundations/Superposition/Semantics.lean) reads it. Its
point symbols are `Name P`: the figure's (`Name.given p`), and `Name.second` (B′) and
`Name.third` (C′). Its line symbols are `LineName L`: the figure's, and `LineName.side`, the
side AC as it falls. These three are fresh by their type: no symbol of the figure is one of
them, and no valuation of the figure gives them anything. In the placement the triangle ABC
laid down with A on D is D B′ C′; "A on D" is carried by the symbol d itself. The placement
keeps (`kept`):

- B′ on L, with D not between B′ and G: B′ is on the ray from D through G;
- C′ on H's side of L;
- DB′, B′C′, C′D equal to AB, BC, CA;
- the angles at D, C′ and B′ equal to those at A, C and B;
- the side AC laid down, a straight line through D and C′.

The first four preserve the former existential rule's conclusion (`Placed I …`). The fifth
was added in round 2. It is Euclid's own object: "the straight line AC will also coincide with DF"
speaks of the side AC as it falls. With it, the law of one ray for one angle can name all
three of its straight lines and be proved without drawing any of them (below), and nothing
is drawn inside the placement. The side serves the law's first half, `rayOfAngle`; the
second, `rayOfAngleSide`, uses none. Since the second retirement, the proofs of both halves
draw other straight lines, outside the placement, one of them through the law's point P,
which in I.4 is C′ (the note of 21 October on the second retirement wave above); citing
the law still draws nothing in the placement. Its model obligation is now proved: wherever the triangle can be laid
down, the straight line through D and C′ must exist too, which Postulate 1 gives, since D is
not C′. The owner approved this kept side, as prototyped, under question 5 on 20 October
2026. That cost was checked by reading the model's proof until 25 October 2026; it is now
the theorem `Rule.of_placement_of_join`, in `Soundness.lean`, which the model's proof
applies (the note of 29 October above).

Astra asked that the incidence and nondegeneracy facts the arguments need be retained
explicitly. They are, as steps rather than as assumptions: that B′, C′ and D are three
points follows inside the placement from the kept sides, by the cited law that a straight
line equal to one with distinct ends has distinct ends. The guards that are literals are
available as they stand (`guards`): D and G on L, D not G, H off L. Whatever else a proof
needs, such as the corners of ABC being three points, it proves outside the placement and
lists among the given facts Γ, so that the certificate sees the proof.

### Exported conclusions

One `Metric (Fin n)`: an equality of lengths, angles or triangles over the figure's symbols.
For a first implementation Astra advised exactly this: the metric equalities I.4 and I.8
need. A proof that needs several uses the rule once for each.

### The rule

```lean
structure Rule (I : Interpretation) : Prop where
  infer : ∀ {cites : List Cited}, (∀ c ∈ cites, c.Holds I) →
    ∀ {n m : Nat} {Γ : List (Lit (Fin n) (Fin m))} {a b c d g h : Fin n} {l : Fin m}
      {φ : Metric (Fin n)},
      Derives cites (branch Γ a b c d g h l) (pos (φ.map Name.given).toAtom) →
      ∀ v : Val I (Fin n) (Fin m), Triangle I (v.pt a) (v.pt b) (v.pt c) →
        I.OnLine (v.pt d) (v.line l) → I.OnLine (v.pt g) (v.line l) → v.pt d ≠ v.pt g →
        ¬ I.OnLine (v.pt h) (v.line l) → (∀ ℓ ∈ Γ, ℓ.Holds v) → φ.Holds v
```

In words: given laws that hold, and a restricted derivation of an equality over the
figure's symbols from the given facts Γ, the guards and what the placement keeps, the
equality holds in every figure of `I` that satisfies the guards and Γ. `branch Γ …`
is that context. The derivation comes before the valuation: one derivation, over symbols,
serves every figure.

**Against System E.** System E states two rules (§3.7, p. 725, as printed): its Π₁ keeps
an angle, and its Π₂ the three sides. Our combined placement follows LeanEuclid, by Logan Murphy,
Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and Xujie Si, in combining them into
one that keeps all six sides and angles, and the kept facts above inherit that. In our
reading of the sequent form, our branch takes no construction step and our Δ′ is one
equality of magnitudes, where the paper's text leaves both more open. So `Rule` is an
inference in System E's style; we do not claim it equivalent to System E's
two-rule presentation, which would need an argument of its own (Astra).

## What the laws' proofs draw

Citing a law draws nothing in the placement: the step puts symbols already there for its
letters. The law's own proof is a universal statement proved outside the placement, and
Astra asked that such proofs be inspected rather than assumed admissible. `#print axioms`,
at this revision, for each law's proof (a construction rule as
[FORMALIZATION.md](../FORMALIZATION.md#construction-rules), section 9, defines it, and as
the certificate's `construction_rules` lists them; the restated `superposition` is not
one):

| Law | Proof | Construction rules it uses |
|---|---|---|
| Metric 3, Metric 4, Metric 9 | the axioms `len_symm`, `angle_symm`, `area_congruent` | none |
| Distinct ends | Book Zero's `ne_of_len_eq` | Postulates 1 and 3 and four other construction rules, through the proved Metric 1 (`eq_of_len_eq_zero`), which draws a circle |
| One point at one distance on a ray | Book Zero's `OnRay.eq_of_len_eq` | the same six, through Metric 1 |
| One ray for one angle, its straight line | `onLine_of_angle_eq_named` in `Elements/Figure/Superposition.lean`, with the side laid down as its third straight line | Postulates 1, 2 and 3 and eight other construction rules, through the proved Same side 2 and Triple incidence 2 |
| One ray for one angle, its side | Pasch 3, with no side | Postulates 1 and 3 and six other construction rules, through the proved Pasch 3, which joins the law's point P to a point of the line |
| I.7 | the edition's I.7, supplied by the theorem that cites it | Postulates 1, 2 and 3 and eight other construction rules; it also rests on the restricted superposition rule through I.5 and I.4 |

Before the second retirement the last column read "none" for every law but I.7, and I.7's
row "seven other construction rules".

*26 October 2026, #473: Book Zero now proves Metric 1 from our radius rule
(`Tacit.radius_ne_zero`) by Postulate 3 alone, and no proof beneath the laws of distinct
ends, of one point at one distance and of one ray's straight line uses Generalities 4
(`inside_not_on`) any more. So the last column of distinct ends now reads "Postulate 3
alone, through the proved Metric 1 (`eq_of_len_eq_zero`), which draws a circle", that of
one point at one distance "the same, through Metric 1", and that of one ray's straight line
"Postulates 1, 2 and 3 and seven other construction rules", without `exists_point`, which
reached it only through Generalities 4; the rows of one ray's side and of I.7 do not
change. Before 26 October 2026 the rows of distinct ends and of one point at one distance
read "Postulates 1 and 3 and four other construction rules" and "the same six", and that
of one ray's straight line "eight other".*

Each law but I.7 is proved by a theorem of its own in `Elements/Figure/Superposition.lean`,
and the certificate lists the construction rules beneath each law's proof (`cited_laws`);
before the second retirement it listed none for any law I.4 cites, and since it lists them
for four of the seven. In round 1, one ray for
one angle was proved through Book Zero's `onRay_of_angle_eq`, which draws the straight lines
DE, DF and DP (Postulate 1, and `exists_point` through `Triangle.angle_pos`): with P the
laid-down C′, that drew through a point of the placement. Round 2 states the law with its
three straight lines named, the third the side laid down, and proves it again with no
construction. Since the second retirement both halves are proved with constructions again,
through the proved rules beneath them, and each proof, in some case of its argument, joins
P to another point by a straight line, though the first still draws none of its three
named straight lines.

**I.7 remains.** Its proof, with its helpers, draws the six straight lines joining its four
points (Postulate 1), finds where AD and CB cross (an intersection rule), produces AC and AD
(Postulate 2), and cites I.5, which cuts off with I.3 and so uses its circles (Postulate 3).
Inside I.8's placement, I.7's point C is G, the laid-down corner. The I.7 *statement* asserts
no existence, and citing it draws nothing in the placement. Before the second retirement
every law I.4's derivation cites was proved with no construction rule; since it, four are
proved with construction rules, as `cited_laws` shows, and so are two of the three other
laws I.8's derivation cites. I.8's also cites I.7, where Euclid's argument uses it ("But
they cannot be so constructed. [I. 7]",
the reference Heath's). The owner approved this permissive reading, as prototyped, under
question 4 on 20 October 2026. `Cited.drawsNothing`, which classified the laws by hand,
was retired on 21 October 2026 (#150, route (b)): the certificate computes each law's
construction rules instead.

**A1 leaves these cited-law dependencies unchanged.** I.4's named-line ray proof uses
the retained `triple_incidence2` and `angle_add_of_inside`, not the retired
`triple_incidence3` and `inside_of_angle_add`; `eq_of_len_eq_zero`, `len_symm`,
`angle_symm` and `area_congruent` also remain axioms. I.8's adapter still cites I.7;
A1 proves Circle 4 after I.7, without using it to establish I.7. The existing pins are
therefore expected to remain unchanged, subject to the combined Audit build.

**When wave two lands.** The measured claim about the laws' proofs above is tied to
`aa96ab8`, before `lean/retire-axioms-2`. At `d2c45450`, that second wave proves four
axioms used by the cited laws with construction rules: `same_side_symm` uses
`exists_point_on_line`, Postulate 3 and circle intersections; `pasch3` uses
`exists_point_on_line` and Postulate 1; `eq_of_len_eq_zero` uses Postulate 3; and
`triple_incidence2` uses Postulate 2. The affected laws are `neOfLen`, `rayUnique`,
`rayOfAngle` and `rayOfAngleSide` in I.4; I.8 also cites the first two. Of I.4's
seven laws, only `lenSymm`, `angleSymm` and `areaCongruent` then have proofs without
construction rules. This describes that A2 revision, not this A1 merge, and its
dependencies must be checked again at A2's landing. The certificate's `cited_laws` will
show those construction rules law by law; the supporting prose and audit pins must be
reviewed again. Under the stricter reading of question 4, this would affect I.4 as well as I.8.
Retired axioms must not be restored to preserve the earlier classification. That review
belongs to the second wave's landing ("Landing"), and #150 tracks it. *Done at that
landing* (the note of 21 October on the second retirement wave above): the four laws are
as named here, `cited_laws` and the audit pins record their construction rules, and no
retired axiom is restored.

## How I.4 and I.8 keep Euclid's arguments

[`Elements/BookI/Prop04.lean`](../../Elements/BookI/Prop04.lean) and
[`Elements/BookI/Prop08.lean`](../../Elements/BookI/Prop08.lean) keep their original statements,
Heath's enunciations and every Heath `--` line. Each uses `Tacit.superposition` through
`Rule.apply`; I.8 supplies the rebuilt I.7 through `Prop8.holds_prop7`, with no extra
hypothesis in either proposition. Under each of Euclid's sentences is the derivation step
that carries it. Each proof draws its straight lines before the placement, gives the figure
as a valuation `v`, lists the given facts Γ, derives inside the placement, and exports only
metric equalities.

**I.4.** Before the placement the proof draws the straight line DE, along which the triangle
is laid, with F off it, and the straight line DF, along which AC will fall (Postulate 1
both). The given facts are the hypotheses, the two straight lines through their points, and
the distinctness of the corners of both triangles. Then, inside the placement, first a step
Euclid takes for granted: b′, c′ and d are three points, since db′, b′c′, c′d are AB, BC,
CA. Then Euclid's:

1. "the point B will also coincide with E, because AB is equal to DE": db′ is AB is DE, and
   on the ray from d through e one point lies at that distance (`ray_unique`), so b′ is e;
2. "the straight line AC will also coincide with DF, because the angle BAC is equal to the
   angle EDF": the angle e d c′ is b′ d c′, which is BAC, which is EDF; on f's side of de one
   ray from d makes that angle, and the side AC laid down runs from d through c′
   (`ray_of_angle`, `ray_of_angle_side`), so c′ lies on df, on f's side of d;
3. "hence the point C will also coincide with the point F": dc′ is CA is DF, so c′ is f;
4. the base: b′c′ is BC, and b′, c′ are e, f (Common Notion 4);
5. the triangle: d b′ c′ is DEF (Common Notion 4), and ABC is d b′ c′, being moved
   (Metric 9);
6. the remaining angles: c′ b′ d is CBA, and is FED; d c′ b′ is ACB, and is DFE.

Four equalities over the figure's symbols leave the placement: BC = EF, △ABC = △DEF,
∠ABC = ∠DEF and ∠ACB = ∠DFE, which is I.4's conclusion. b′, c′ and the side stay behind.

**I.8.** The triangle BCA is laid down with B on E and C along the ray from E through F, on
D's side; c′ is where C comes down and g where A comes down, Euclid's own letter.

1. "the point C will also coincide with F, because BC is equal to EF": ec′ is BC is EF, so
   c′ is f (`ray_unique`);
2. "BA, AC will also coincide with ED, DF": ge is AB is DE, and gf is gc′ is CA is DF;
3. "But they cannot be so constructed. [I. 7]": g and d are on one side of ef (kept), so
   I.7, cited inside the placement, makes g and d one point;
4. "so that the angle BAC will also coincide with the angle EDF": e g c′ is BAC (kept), and
   is EDF (Common Notion 4).

One equality leaves the placement: ∠BAC = ∠EDF, which is I.8's conclusion.

**What the proofs rest on.** Before the second retirement, the production I.4 had 26
axioms in its closure and I.8 had 56, Lean's three logical axioms included: exactly their
former axiom-name sets, with `Tacit.superposition` restated. I.4's construction rules,
Postulate 1 and `exists_point`, entered before the placement, in drawing DE and DF and
proving the corners distinct. Since that retirement I.4 has 39 and I.8 has 45. Postulate 1
and `exists_point` still enter before the placement; I.4's nine other construction rules,
Postulates 2 and 3 among them, enter only through the proofs of the four laws named under
"What the laws' proofs draw". I.8
cites I.7, which cites I.5 and so the rebuilt I.4. Every dependent proof has rebuilt against
the restricted axiom. Heath's 27 lines in I.4 and 24 in I.8, the enunciations and both
statements are unchanged against `39ae65c`.

**Common Notion 4 stays visible.** The pure soundness proof uses equality substitution for
`Derives.len_congr`, `angle_congr` and `area_congr`. Each now takes an explicit
`Coincidence` argument, supplied as `Coincidence.step` only where a derivation takes a
congruence step. `Derives.map` passes the received marker along; `Derives.sound` binds
it and proves the equality by substitution. Neither supplies a fresh marker.

The earlier certificate counted the congruence constructors themselves. Since
`Derives.map` rebuilds every constructor, that also counted C.N. 4 for any proof reaching
renaming, even one taking no congruence step. The tooling correction in
`Certificate/Facts.lean` counts `Elements.Superposition.Coincidence.step` instead.
I.4 names it at five congruence steps and I.8 at two. After integration with the tooling
on 20 October, 116 of the 122 entries reach the calculus and its marker, including
I.47's general companion. No real entry reaches the calculus without taking or inheriting
a congruence step, so no Common Notion list changes. Merely reaching `Derives.map` or
`Derives.sound` supplies no marker; the fixture tests cover that case. All 121
common-notion lists at the earlier revision matched `39ae65c`; all 122 lists at this
integration match the preceding branch revision. No dummy citation was added.

The regenerated lists for I.4, I.8, I.23 and the six entries not resting on the rule are:

| Entry | Common Notions |
|---|---|
| I.4 | C.N. 4, C.N. 5 |
| I.8 | C.N. 1, C.N. 3, C.N. 4, C.N. 5 |
| I.23 | C.N. 1, C.N. 2, C.N. 3, C.N. 4, C.N. 5 |
| I.1 | C.N. 1, C.N. 5 |
| I.2 | C.N. 1, C.N. 3, C.N. 5 |
| I.3 | C.N. 1, C.N. 3, C.N. 5 |
| I.22 | C.N. 1, C.N. 3, C.N. 5 |
| III.5 | C.N. 5 |
| III.6 | C.N. 5 |

Fourteen replacement expectations pin direct use, I.7 in I.8, I.23's construction and
inherited dependency, the six unaffected entries and C.N. 4 in both I.4 and I.8. The
eleven shared expectations retain A1's approved pin changes, and A1 adds four exclusions
of retired axiom names, making 29 in all. The III.1 and III.1 Por. tacit counts are both
55 on A1's baseline; the combined facts must confirm them without loosening the pins.

## The restriction theorem

[`Restriction.lean`](../../Elements/Foundations/Superposition/Restriction.lean), with the
syntax-only exportability results in
[`Syntax.lean`](../../Elements/Foundations/Superposition/Syntax.lean) and `Rule.of_placement`
in [`Soundness.lean`](../../Elements/Foundations/Superposition/Soundness.lean). The restriction is in five parts, each a
theorem. The owner approved this statement, as prototyped, under question 2 on 20 October
2026, when part 4 was read off the statement of `Rule.infer` as locked in
`Certificate/axioms.lock`; on 21 October 2026 part 4 became the theorem below (#150). Every
theorem this section names is pinned by its statement in
[`Audit/Superposition.lean`](../../Audit/Superposition.lean).

1. **No symbol of the placement is exported.** `exportable_iff`: a formula of the placement
   is the image of an exportable conclusion exactly when every symbol in it is the figure's.
   `not_exportable_second` and `not_exportable_third`: a formula naming B′ or C′ is the image
   of none. A `Metric` names no straight line, so the side laid down is never exported
   either. The placement's symbols are fresh by their type.
2. **The conclusion says nothing of where the placement's symbols went.**
   `Metric.holds_place`: an exported formula reads the same whatever points B′ and C′, and
   whatever straight line the side, are taken to be.
3. **No construction step in the placement.** The placement's vocabulary is fixed by its
   type: the figure's symbols and the three it lays down. No rule adds a symbol: a logical
   rule names symbols already there, and `cite` puts symbols already there for a law's
   letters. `Derives.no_construction`: whatever a derivation in the placement proves holds
   under every valuation of exactly those symbols that makes its context true, so no step
   needs an object the symbols do not stand for. `Derives.map`: every rule is a scheme.
   `Cited.holds_iff`: every law asserts no existence. The separate claim about what a cited
   law's proof constructs is tied to the revision above; the owner accepted that reading,
   as prototyped, under question 4 on 20 October 2026, and #150 tracks its check.
4. **The rule's part about the figure asserts no placed point.** The rule's hypotheses are
   the cited laws (a fixed list, each a universal statement over its letters), the given
   facts and the conclusion (data over the figure's numbered symbols, holding no point, no
   straight line and no proposition), a derivation (over symbols, and before any valuation),
   and a valuation of the figure's symbols that satisfies the guards and the given facts.
   B′, C′ and the side occur only as symbols inside the derivation; no hypothesis assigns
   those fresh symbols a point or a straight line. Two hypotheses range over every point or
   straight line of the interpretation, not only the given figure's, and so over wherever
   B′ and C′ might be: the cited-law hypothesis, `∀ c ∈ cites, c.Holds I`, and the triangle
   guard, that no straight line passes through the three corners. `Rule.Figure` is the
   statement of `Rule.infer` without the cited-law hypothesis: the rule's part about the
   figure. `Rule.iff_figure`: the rule holds in an interpretation exactly when its part
   about the figure holds there for every list of laws that hold there, by the definitions
   alone. `Rule.Figure.restrict`: if the part about the figure holds in an interpretation I,
   it holds in every interpretation J embedded in I (`Interpretation.Embedding`), keeping
   incidence, betweenness, sides and the equalities of lengths, angles and areas both ways,
   distinct points distinct, every straight line of I through two distinct points of J, and,
   when a point of J lies on a straight line of I, some straight line of J through that
   point. The guards and the given facts pass from J to I, the triangle guard by the kept
   straight lines, and the conclusion comes back. Nothing
   asks that J have the points B′ and C′ would go to, so the part about the figure asserts
   no placed point. The cited-law hypothesis is what the theorem leaves out. It contributes
   the laws, assumed of every point and straight line of I, and it is the one hypothesis
   that does not pass from J to I, since a law true of every point of J need not be true
   of every point of I. So the rule in I gives the part about the figure in J only for laws
   that hold in I. `Metric.holds_const` remains a warning: every metric formula holds when
   all its point symbols denote one supplied point, given a line valuation, but that
   valuation never meets the guards, since it puts D and G at one point, and it is no
   theorem against classical witness recovery.
5. **No stronger than laying a triangle down.** `Rule.of_placement`: if every triangle can be
   laid down with the former rule's properties and a straight line through D and C′ for
   its side AC, then `Rule I` holds. Its proof uses `propext` and `Quot.sound` alone.
   The prototype's example using the old axiom has been removed; the model now supplies
   the placement and side by proved geometry.

**What part 4 does not say.** It does not say that a given fact cannot encode the absence of
a placement: under a valuation that chooses its points by cases, it can (`valuation_encodes`).
Round 1 gave a different reason for part 4, that a derivation's premises are literals about
named points and so "no placement exists" is never one of them; the verification showed
that false, and it is withdrawn. Whether an encoded premise could recover the placement
through what the rule asserts is the non-derivability question, which is not claimed.

Astra's two observations are kept as theorems, as warnings: `eliminator_iff_exists` and
`eliminator_false_gives_exists`.

**What these do not say.** They do not say that the restricted rule, with the other laws,
cannot prove an existential placement. In the full theory it can, by the route Euclid takes:
I.4 and I.8 from the rule, then I.22 and I.23, as Astra observes ("A constructive placement
theorem may eventually be derived from the legitimate construction propositions"). The
restriction concerns the route by which construction becomes available, not the
independence of I.23 from a theory that proves it.

## The model obligation, met

The separate Lake package in [`model/`](../../model/README.md) proves the restricted law in
`EuclideanSpace ℝ (Fin 2)`. The main library remains plain Lean, without Mathlib.

**Translation.** `model/Check/Generator.lean` gives declarations from exactly the four pure
modules an identity translation. It checks their declaring modules, not just their
namespace, and audits their types, values, proof bodies, constructors and recursor rules
transitively. Only those modules and `Init` are admitted, with no geometric words, project
axioms or `sorryAx`. Universe arguments are preserved in both translation directions.
The shared words remain in the vocabulary report and the exact lock comparison.
`Elements.primitives` is translated normally over the model signature, giving the generated
law `Elements.Superposition.Rule S.primitives`. The hand translation and the generated law
are checked against the original declaration, with both definitional and syntactic
correspondence checks retained.

**Geometry.** In
[`model/Model/Euclidean/Superposition.lean`](../../model/Model/Euclidean/Superposition.lean),
`superposition_placement` retains the isometry and reflection proof: it takes A to D and
AB along the ray DG, choosing the side of L on which C falls, and preserves all three
lengths and all three angles. Since C′ is off L and D is on it, they are distinct.
The model's proved Postulate 1 supplies their straight line. The theorem `superposition`
then applies `Rule.of_placement_of_join` to that placement, to the model's Same side 3 and
to its Postulate 1, and that theorem applies `Rule.of_placement` (the note of 29 October
above). It uses no project axiom.
The assembled `model_exists : ∃ S : Signature, Laws S` remains unconditional, with all
79 locked laws proved; its pinned closure is `propext`, `Classical.choice` and
`Quot.sound`. Regeneration and the model build must confirm the assembly on this merge.

**Import boundary and regressions.** `Model` may import from `Elements` exactly the four
pure calculus modules named above, including transitive imports.
`Check.Generator.checkModelImports`, called from `model/Check/RoundTrip.lean`, checks
that boundary for every Model source and the four pure modules.
`model/Model/Audit.lean` retains the sentinel that `Elements.Point` is unknown, as well as
every existing axiom-closure pin. The generator retains its six original planted faults;
new cases reject a changed guard, swapped interpretation fields, a declaration in the
shared namespace from an unapproved module, a geometric dependency in a pure definition,
and a project axiom or `sorryAx` there. A positive recursor case checks universe arguments
in both directions.

**Numerical evidence.** The law row in [`MODEL.md`](../../tests/model/MODEL.md) now describes
placement with its kept side as sufficient evidence for the restricted rule. The Euclidean
and hyperbolic samplers retain their placement checks and also check the side's two
incidences and distinct endpoints. They sample that sufficient construction, not every
represented derivation. Both lock hashes are renewed against the restated axiom.

This proves the rule's law in the plane relative to Lean's logical foundations and
Mathlib's real numbers. It establishes neither equivalence with System E's two rules nor
whole-theory non-derivability of an existential placement.

## What it clears, and what it does not

**It clears the direct construction shortcut.** No conclusion of the restricted rule names a
symbol of the placement, so the temporary placement points can no longer be returned as the
answer to I.2, I.3 or I.23. The former Audit.I_2, Audit.I_3 and Audit.I_23 each took a point the
former rule returned. Those three audit lemmas and the three corresponding overlap rows
are retired; their history remains in the catalogue. I.2 and I.3 rest on no superposition.
I.23 still constructs through I.22 and rests on the restricted rule through I.8 and I.20.

**It does not:**

- make I.23, I.2 or I.3 unprovable, nor should it: I.2 and I.3 already rest on no
  superposition, and I.23 must stay provable through I.22 and I.8;
- remove the remaining axiom overlaps: Circle 3 and III.2, Diagram-segment 2 and III.5
  and III.6, Generalities 3 and III.6, and Metric 5's consequence of I.13 in I.47.
  A1 has already retired the former overlaps with Circle 4, Diagram-angle 3,
  Generalities 2 and Circle 2, as the catalogue's retirement table records;
- shrink the certificate: 116 of the 122 entries in `facts.json` after the main merge
  rest on the restricted rule, as they did on its predecessor. The six exceptions remain I.1, I.2, I.3, I.22,
  III.5 and III.6. The affected entries are 93 main propositions and 23 attached entries.

## The disclosure on the branch

The interim disclosure requested on 18 October concerned the old existential axiom, whose
construction strength exceeded System E's restricted inference. The branch now says what
replaces it: hypothetical placement in System E's style, with only metric equalities about
the given figure exported. The foundations comment, the overlap catalogue, Book I's brief
and introduction, and the pages for I.4, I.8 and I.23 describe that restriction.

`mishnah/I/04.md` describes the four equalities and the kept side. `mishnah/I/08.md` states
our reading that I.7 may be cited although its proof constructs. `mishnah/I/23.md` keeps
I.22's constructed points and I.8's angle equality distinct, and explains the inherited
rule through I.8 and I.20. I.44's comment describes its existing construction of the
parallelogram. The six records for I.2, I.3, I.4, I.8, I.23 and I.44 were read and
stamped independently before A1; all retain full coverage and Euclid's route.
The marker change made I.4's and I.8's records stale; an independent reader read both
again and stamped them at `0085b443`. An independent Codex reader then read all six in
full at `bd86a7b6`, the integration merge, found every item to pass or not to apply, and stamped them there
(run "brief 0009 stage full, ship S3 A1-integration re-read"); the pages show that commit.

## Evidence before landing

Astra names three kinds. Their state on the delivered branch:

1. **Positive proofs.** I.4 and I.8 compile from the rule with their statements and with
   their coincidence arguments visible, step under sentence. *Done in production*, with
   the restated axiom and the I.4, I.5, I.7, I.8 dependency chain rebuilt.
2. **A restriction theorem.** The represented system cannot export the placement's objects
   as witnesses, nor take construction steps in the placement. *Done in the five parts
   above*, for the symbolic calculus. The owner accepted this statement of the restriction,
   as prototyped, under question 2 on 20 October 2026, with part 4's limits retained;
   part 4 has been a theorem since 21 October 2026 (#150).
3. **A carefully scoped non-derivability result, if claimed.** *Not claimed.* A route, for
   whoever takes it up. Besides its hypotheses about the figure, an instance of `Rule`
   assumes that each cited law holds, `∀ c ∈ cites, c.Holds I`; that hypothesis quantifies
   over every point and straight line, not only the figure's, and in hypothesis position it
   is not a statement about the figure alone. But every law in `Cited` is true in the plane
   outright, I.7's included, so in the plane each instance of `Rule` reduces to its part
   about the figure (`Rule.iff_figure`). In the edition, `Cited.holds_all` proves every law
   in one statement, though through I.7 it rests on `Tacit.superposition` itself. That part
   speaks of the figure's points and straight lines, save that its only existential, "some
   straight line passes through A, B and C", stands negated, in the hypothesis that ABC is a
   triangle, which ranges over every straight line. So that part, true in the plane, stays
   true in any part of the plane that keeps every straight line through two distinct points,
   supplies some straight line through a point that lies on an ambient straight line, and
   keeps the same lengths, angles and areas: this half of the route is now a theorem,
   `Rule.Figure.restrict`, for any interpretation and any part of it in the sense of
   `Interpretation.Embedding`, which keeps incidence, betweenness and sides as well, and
   distinct points distinct. Take the points with
   rational coordinates, the straight lines through two of them, and real magnitudes: the
   laws that do not mention circles appear to hold there, and so does every instance of
   `Rule`; but the triangle with corners (0, 0), (1, 0), (0, 1) cannot be laid along the ray
   from (0, 0) through (1, 1), for B′ would be (1/√2, 1/√2). The other half remains: the
   laws that do not mention circles, checked law by law in that part, and the whole proved
   in `model/`. That would show the restricted rule does not give the placement from those
   laws. Until then, nothing is claimed.

A failed compilation of `Audit.I_23` against the new rule is a useful regression signal,
and establishes none of the third kind by itself (Astra).

The production evidence is pinned by 28 dependency checks in
[`Audit/Superposition.lean`](../../Audit/Superposition.lean), covering I.4 and I.8,
soundness, the placement reduction, restriction results, cited-law proofs, I.7's adapter
and every cited law in one statement. The restriction's theorems and warnings and
`Cited.holds_all` are pinned by their statements too, and part 4's two definitions whole.
The 13 surviving overlap proofs are retained with A1's revised axiom pins. The exact validation evidence
and remaining landing work are recorded below.

## The guards

The former rule's guards stay, as hypotheses of `Rule.infer`; those that are literals are
also in `guards`, where a derivation may use them, and a proof that needs more of them (the
corners of ABC distinct) proves it outside the placement.

- **A zero-length ray.** D and G must be two points, so that the ray from D through G has a
  direction. Without it B′ may be anywhere on L at the distance AB, and I.4's first
  coincidence, which needs D other than E, has nothing to stand on.
- **A collinear source.** ABC must be a triangle. For a flat triangle there is no point off
  L at the right distances; MODEL.md's mutation "superposition for a flat triangle" catches
  exactly this. It also keeps C′ other than D, so that the side AC laid down is a straight
  line.
- **H on L.** H must be off L, or no point is on H's side, and the placement would be
  impossible.
- **Reflections.** The model's proof permits a reflection in L: a rotation and a
  translation alone cannot always put C′ on H's side. The formal placement proof and
  MODEL.md's argument both include it.
- **Side equalities are not angle equalities.** Our placement keeps all six sides and
  angles, and the model justifies the angles by the rigid motion itself, not by deriving
  them from the sides. Were a placement carrying only the sides adopted (System E's Π₂), no
  step could use an angle equality from it.

## Staging and naming

The prototype's proofs were authorised in `Staging/` under WORKFLOW, section 2; the earlier
request for staging approval was already obsolete at the 19 October probe. The directory
`Staging/Superposition/` and its six files are now deleted. Their evidence survives in the
four pure modules, Book Zero and `Audit/Superposition.lean`; the proposition proofs live at
`Elements.BookI.Prop4` and `Elements.BookI.Prop8`. The old compatibility example using the
existential axiom has no production copy.

The forbidden-command policy and the trees its source scan reads are specified in
[FORMALIZATION](../FORMALIZATION.md), section 7. The scan covers `Staging/` and the four
pure modules in `Elements/`. The six prototype files declared no axiom and used none of
the forbidden commands. The four pure modules are also inside the vocabulary lock; their
freedom from geometric axioms is checked by the model. Review remains distinct from these
checks.

## What is delivered, and what is not claimed

The branch contains the symbolic language, generic interpretation, derivation soundness and
renaming, placement reduction, finite-symbol front end and restriction evidence. It proves
I.4 and I.8 from the restricted axiom, rebuilds their dependents, retires the three direct
construction shortcuts, and proves the restated law in the formal model. At `aa96ab8`,
the regenerated lock kept 87 axioms and grew its vocabulary from 91 to 206, adding
115 words and removing none. The certificate, model laws and both lock hashes were
regenerated at that revision.
At the certificate-tooling integration on 20 October, before A1 was brought into this
branch, the lock kept all 87 axiom statements unchanged and its vocabulary grew from
206 to 208. The added words were
`Superposition.Coincidence` and `Superposition.Coincidence.step`; the changed words are
`Superposition.Derives.len_congr`, `Superposition.Derives.angle_congr` and
`Superposition.Derives.area_congr`, each gaining the explicit marker argument. No word
was removed, and no other locked word changed in that integration. The lock, both hashes,
the model's three generated files and the edition were regenerated from those sources.
The certificate has 99 propositions, 3 porisms and 20 companions, 122 entries in all.
This A1 integration retains the restricted rule and the marker and removes the eight
retired axioms. Its regenerated results are 79 axioms, including 73 tacit rules, 208
vocabulary entries and 29 certificate expectations. The older measurements above do not
validate that result.

It does not prove equivalence with System E's two-rule presentation, or non-derivability of
placement in the whole theory. Part 4 of the restriction is a theorem about the rule
without its cited-law hypothesis; neither it nor `Metric.holds_const` settles classical
recovery of witnesses.
The owner approved questions 2, 4 and 5 as prototyped on 20 October 2026, together with the
four pure module imports and the page claim; finishing the three answers is tracked in
#150. Landing has the conditions below.

## Landing

The owner's approval of 20 October 2026 authorises the replacement subject to the
tooling pull requests landing first, /no-mistakes and an independent Codex read of the
model lane. The tooling pull requests have landed and the combined sources are
regenerated; the record of each condition is:

- **The tooling pull requests landed first.** The check changes in `Certificate/Facts.lean`,
  `scripts/heath.py` and `review/SCHEMA.md` reached main in #180, and the model checks
  reached main in #182. This branch has merged main at `64206ed3`, which contains both.
  WORKFLOW, section 10, forbids changing a check in the same pull request as that code.
  The certificate recognised `Coincidence.step` without requiring it to be present on main
  before this rule landed; the Heath self-test and the schema's
  example keep their outcomes while naming I.13's overlap in I.47 (Metric 5 in
  `Prop47.within`), which survives this rule and the axiom retirements. The model check
  changes, including the older relative-path defect fixed on
  `tooling/superposition-model-check`, landed in #182. No check may be loosened.
- **The landing order with the retirement waves (#119).** The first wave,
  `lean/retire-axioms` (A1), reduced 87 axioms to 79 and reached main on 20 October 2026.
  This merge reconciles that landed baseline's edits to the lock, model, numerical laws,
  audit and overlap catalogue. The replacement lands next.
  The second wave, `lean/retire-axioms-2`, which reduces 79 to 48, lands after the
  replacement. Its landing carries the review of the cited laws' construction rules
  (`cited_laws`) and of the audit pins once
  `same_side_symm`, `pasch3`, `eq_of_len_eq_zero` and `triple_incidence2` acquire the
  construction dependencies described above (#150). Review `neOfLen`, `rayUnique`,
  `rayOfAngle` and `rayOfAngleSide` in I.4 and the first two in I.8, with fresh per-law
  dependency evidence; question 4 permits cited laws whose proofs use constructions.
  Resolve its modify/delete conflict in
  `Staging/Superposition/Derivations.lean` by carrying needed geometric support into
  `Elements/Figure/Superposition.lean`, not by restoring the prototype. Preserve both
  waves' root imports, and restore no retired axiom. *Done at the second wave's landing*
  (the note of 21 October on the second retirement wave above).
- **The combined sources are regenerated.** The exact outputs and the six records read
  again at `bd86a7b6` are recorded in the
  [decisions entry](0002-decisions.md#20-october-2026). Regenerate and recheck them again
  if validation changes a source.
- **Finish validation and review on that revision.** Complete WORKFLOW, section 8, including
  the kernel replay, style tests, clean regeneration, negative suite, numerical model and
  formal-model build, and run /no-mistakes. The independent Codex reads of the model lane
  at `cdcf3b9e` and `0085b443` found the defects described above, now fixed.
  Verify the fix and complete the required code and protected-path security reviews on
  the revision to land. A successful earlier lane check is not a pass on the final
  merged revision.

## The reviews

**Round 1's adversarial review.** A separate Codex run reviewed the first prototype at
`d649437`, with Astra's answer and System E's section in hand, under orders to break it. It
found no way to get a laid-down point, a placement, `False` or a construction without
circles out of the rule, no step without support, no law false in the plane, no dropped
guard and no kept fact without justification. Its findings, all handled in round 1: the
kept facts then contained a consequence of Metric 1 (moved to a derived step); one law's
proof drew through C′ (scoped then; resolved in round 2, below); `Metric.holds_const` was
over-described (corrected); names were any points (open question 3 then; resolved in round
2); and the brief was missing (written).

**The verification of round 1.** A verifier read round 1 at `421fbce` in full and checked it
again: it ran `#print axioms` on all 43 theorems, compiled each staged file, ran the whole
build, the audit, the certificate, the fidelity and model checks, and confirmed the staged
statements, Heath's lines and the kept facts. It also fixed the list of overlap rows the
rule leaves, adding Generalities 3, in its own commit. Its findings, and what round 2 does:

1. *Part 4's reason was false:* a given fact could say "no placement exists" through a name
   chosen by cases. *Answered:* names are symbols now; the reason is withdrawn, part 4 states
   only what the rule's hypotheses are, and `valuation_encodes` records that a valuation can
   still encode a proposition.
2. *The cited laws did more construction than the brief said:* one ray for one angle drew
   DE, DF and DP; I.7 draws, produces and cites I.5. *Answered:* the ray law names its three
   straight lines, the placement supplies the side AC, and the law is proved again with no
   construction rule; I.7's construction is disclosed above, and question 4 states the
   consequence of the stricter reading for I.8.
3. *The interim disclosure was filed for later:* *Answered* in "The disclosure, now", with
   the four places and their owners.
4. *Claims about System E went beyond its text:* *Answered:* the sequent form, the branch's
   constructions and Δ′'s vocabulary are given as our reading.
5. *Staging scope and naming:* *Answered* in "Staging and naming".
6. *The landing plan gave no home for the evidence:* *Answered* in "Landing, when complete".
7. *Small points:* I.8's module text said I.7 is proved from I.5 and I.4; it now says that I.7
   cites I.5 and rests on I.4 through it. The branch's upstream is `origin/main`, so a bare
   push would target main; nothing was pushed, and the coordinator lands work only through
   `safe_push.py`.

**The review of round 2.** An independent review read round 2 at `08b218b` in full, under
orders to break it, and its findings are answered in `6aa4192`:

1. *`Audit.I_2` and `Audit.I_3` also take a point the present rule returns,* as `Audit.I_23`
   does. *Answered:* the landing plan retires all three audit lemmas and the rows for I.2
   and I.3, retires or rewrites the row for I.23, and names the catalogue's owner.
2. *The brief called all five parts of the restriction theorem proved.* *Answered:* parts 1,
   2, 3 and 5 are theorems, and part 4 is a reading of `Rule.infer`'s statement, with
   `Metric.holds_const` its one theorem (FORMALIZATION, section 9).
3. *The brief gave Euclid the citation of I.7,* when the bracketed [I. 7] is Heath's (STYLE,
   section 4). *Answered:* it says that Euclid's argument uses I.7.
4. *The disclosure left out I.8's page,* which the owner's decision names. *Answered:* it
   names `mishnah/I/08.md`.
5. *Small points:* a law "asserts no existence" (it read "asserts that nothing exists"); the
   catalogue's and the audit's places are named by section rather than by line numbers main
   had moved; I.7's proof draws the six straight lines joining its points and finds a
   crossing; `Symbols` is a class built on the rule; and the non-derivability route names
   the existential an instance contains.

It left staging approval and the interface questions to their owners. Staging approval was
subsequently recorded; the owner answered questions 2, 4 and 5 as prototyped on
20 October 2026, and #150 tracks their finishing. It hunted for escapes along the routes
that Astra's answer and round 1's verification name (a given fact encoding a proposition
through the valuation, an opaque predicate among the atoms, an argument by contradiction, a
cited law that constructs in its proof, a conclusion naming a placement symbol) and found
no way out of the restriction.

**Round 3's independent record reader.** At `bda0636`, a reader who had not written the
proofs checked the statements, Heath lines, represented derivations, I.7 adapter and page
text, and stamped I.2, I.3, I.4, I.8, I.23 and I.44. No blocking or material defect was
found. The one editorial finding was that this brief and `Syntax.lean` claimed a point
transitivity rule which `Derives` does not have; round 3 corrects both descriptions.

**Round 3's adversarial model reading.** The adversarial reading at `39ae65c` examined the
prototype and the proposed model correspondence. It found no concrete escape or false
cited law, but required a checked production translation, preserved rejection tests and an
unconditional `model_exists`. It also distinguished uniform validity from a restriction
on how callers choose arguments, and warned that `drawsNothing` must be reviewed after
axiom retirement. The branch now supplies the translation and model proof. The independent
Codex read of the model lane at `cdcf3b9e` found no weakening and one older relative-path
defect in `model/Check/Generator.lean`; the read at `0085b443` found the escaped module
name in the import audit. Both are fixed on `tooling/superposition-model-check`.
That reading is evidence for its named revision; it does not replace validation of the
final integrated revision.

The reviews' scratch files are not committed.

## Open questions for the owner and the coordinator

The owner answered questions 2, 4 and 5 as prototyped on 20 October 2026, and #150 tracks
their finishing; none of the three remains open for the owner. Their numbers are retained
from round 2. The other items record the delivered design or the continuing process.

1. **Cited laws.** The branch asks for a proof of each cited law, keeping its dependencies
   visible. Building laws into the derivation instead would hide those dependencies from
   the certificate. No extension of the fixed list is made here.
2. **The restriction theorem, approved 20 October 2026.** The owner accepted the five-part
   statement as prototyped: parts 1, 2, 3 and 5 are theorems; part 4 is a reading of
   `Rule.infer`, with `Metric.holds_const` its limited satisfiability theorem.
   No further formal statement or separating model is a condition of this approval;
   whole-theory non-derivability is not claimed. Part 4 has been a theorem since
   21 October 2026 (`Rule.Figure.restrict`, #150).
3. **The symbols' front end.** The delivered rule uses `Fin n` and `Fin m`; `Symbols` and
   `Rule.apply` let proofs name their letters. The alternative would quantify over any
   vocabulary with `Symbols` in the axiom itself. No such change is proposed here.
4. **Laws whose proofs draw, approved 20 October 2026.** The owner accepted the prototype's
   reading: a previously proved law whose statement asserts no existence may be cited
   inside the placement, whatever its proof constructs.
   Thus I.8 uses I.7 on its hypothetical corner, following Euclid's argument. The stricter
   alternative permits only laws proved without construction rules. The prototype's
   suggested test, `∀ c ∈ cites, c.drawsNothing = true`, expressed that only while the
   classification agreed with the actual proofs; with the flag retired, the stricter
   reading would ask that every cited law's `construction_rules` in `cited_laws` be
   empty. It would reject this I.8 route, requiring
   another argument labelled as such. At `aa96ab8` I.4's cited laws pass that classification;
   after `lean/retire-axioms-2`, the construction dependencies of `same_side_symm`,
   `pasch3`, `triple_incidence2` and `eq_of_len_eq_zero` bring I.4 within this decision
   too, in the four laws named under "What the laws' proofs draw". The
   classification, set by hand, was retired on 21 October 2026; the certificate's
   `cited_laws` gives each law's construction rules, and #150 tracks the review at the
   second wave's landing, recorded in the note of 21 October on the second retirement
   wave above.
5. **The side laid down, approved 20 October 2026.** The owner accepted the prototype's
   kept side AC as a straight line through D and C′, so the angle-to-ray argument draws no
   line inside the placement. The model proves
   that this side exists. The alternative draws the line inside the placement, which
   would require a construction step there, or changes the argument and its calculus to
   avoid that line. The approved design keeps it, and since 25 October 2026 its cost has
   been a theorem, `Rule.of_placement_of_join`, rather than a reading of the model's
   proof; #150 tracks its pin in the audit (the note of 29 October above).
6. **More citable propositions.** `Cited` holds I.7 alone among the propositions. Another
   joins only by a revision of this brief, with its reason.
7. **Timing.** On 20 October 2026 the replacement was approved and unlanded, and A1 had
   landed. The tooling pull requests were to land before the replacement, and A2 after it.
   Landing the replacement also required /no-mistakes and the independent Codex read of
   the model lane, with evidence tied to the revision delivered as described under
   "Landing". #150 was to stay open after the landing and hold every release until it
   closed. The replacement has landed, and its issue, #75, is closed on its landed work.
   #150 stays open, but since 27 October 2026 it no longer holds the release: the owner
   deferred superposition's remaining work until after the release (the note of
   29 October above).

## Checks

Evidence is tied to the revision that was checked. The handbacks report:

| Revision and scope | Checks and outcome |
|---|---|
| Round 2, `08b218b` | Staging build, theorem axiom checks, Heath comparison, style and links passed. |
| Library replacement, `24b6a9e` plus the delivered library files, integrated at `400f4ddf` | Library, Audit and Staging builds and certificate generation passed; statements, enunciations and Heath lines matched `39ae65c`. Fidelity then reported three stale records, and links reported six deleted staging targets. |
| Certificate work, `bda0636` plus its delivered files, integrated at `2a82add6` | Library build, certificate, all 24 expectations, Heath contracts, style tests and style passed. Seven positive and four negative constructor controls passed; all 121 common-notion lists matched the baseline. |
| Independent records, `bda0636` plus six records, integrated at `f5bccaa4` | Library and Audit builds, certificate, fidelity, Heath contracts and style passed. Six records were stamped with unchanged statement fingerprints. |
| Model implementation before integration | In an isolated copy with the module-format correction, all model and translation components passed except the then-stale lock comparison. The fast numerical suite passed with 130,652 Euclidean configurations, all 15 mutations and only the expected hyperbolic Postulate 5 failures. These are lane results, not validation of `aa96ab8`. |

The module-format correction is now committed at `453fbcbf`, the model at `d08417bb`, and
normal model regeneration and both lock hashes at `aa96ab8`. The earlier model blockers
have been addressed in the delivered sources; the final integrated build must still be
recorded against its exact revision. Round 3 replaces the six broken links and corrects
the point-equality description. On `aa96ab8` plus its three edited files, `lake build`
passes (142 jobs), `check_fidelity.py` passes all 99 propositions and records,
`check_style.py` passes S1–S21, and `check_links.py` resolves all 13,406 relative links and
anchors in 476 Markdown files.

No full negative suite, kernel replay, final formal-model build or clean page regeneration
is claimed by this editorial revision. Those belong to the integrated validation listed
under "Landing".

## Thanks

To Jeremy Avigad, Edward Dean and John Mumma, whose System E gives the rule and its
restriction; to Logan Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and
Xujie Si, whose LeanEuclid gives the one-rule form our present rule follows; to Sir Henry
Savile, through Heath, for the argument on a ray that carries I.4's coincidences; to Astra,
whose third answer set out this design, the two observations it guards against, and the
evidence it asks for; and to the reviewers of round 1, the adversarial run and the verifier,
and the reviewer of round 2, whose findings made round 2 and sharpened it. Thanks also to
the round 3 record reader for following the coincidences sentence by sentence, and to the
model readers for insisting that the rule proved in the plane is the rule declared in the
library, with its assumptions visible. We are grateful to them all.
