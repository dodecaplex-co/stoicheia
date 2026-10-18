# Brief 0009: a restricted rule of superposition

*18 October 2026, revised the same day (round 2). A design brief and a prototype for issue
#75, written to the owner's decision of 18 October after Astra's third answer. Nothing in
`Elements/` changes and no axiom is added: the restricted rule is a hypothesis, `Rule`,
which the prototype's theorems take as an argument, in `Staging/Superposition/`. The rule
lands only when it is complete; until then the edition keeps its present rule, with the
disclosure below, which is due now. The brief is for the coordinator's and the owner's
review. Once approved, a later change is a revision of this brief
([WORKFLOW.md](../WORKFLOW.md), section 2, "Correcting a frozen brief"). The code states
what we formalized; where the code and this brief disagree, the disagreement is recorded and
reconciled ([FORMALIZATION.md](../FORMALIZATION.md), section 1).*

Base: the branch `lean/superposition-prototype` was cut from main at `f17b427`, and main was
merged into it at `e04f318` (pull requests #79 to #86). The prototype is six files in
`Staging/Superposition/`, 1,691 lines, and `lake build Staging` passes with them.

**Round 2.** The first prototype named points by Lean points. Its verification showed that
this let a given fact say "no placement exists", through a name such as `if Q then X else
Y`, so that one reason the brief gave for the restriction was false; and that two cited laws
did construction in their proofs that the brief did not disclose. Round 2 redesigns the
prototype on a finite symbolic context, as Astra advised and as open question 3 of round 1
proposed: names are symbols, the figure is a valuation given separately, cited laws are data
over letters, and the placement adds fresh symbols that no conclusion can mention. I.4 and
I.8 are proved again from the rule, the restriction theorem is proved again for the new
design, and each finding of the verification is answered below ("The reviews").

## The owner's decision

On 18 October 2026, after Astra's third answer, Jack Challis decided on superposition
(#75): prototype a genuinely restricted rule now, as a checked inference over represented
derivations, with I.4 and I.8 proved from it, a restriction theorem and the model's
justification; land it only when complete; and meanwhile disclose that our rule is
stronger, as a construction principle, than System E's. The same day he decided that every
circle has a centre (#59) and that the formal model starts now in `model/` (#73). Any new
axiom waits for #40, the model's law names as a pinned data file. This brief answers the
decision on superposition, and depends on the one on the model for the model's part.

## The problem

**Our rule hands back points.** `Tacit.superposition` says that the triangle ABC can be
laid down with A on D, B on the ray from D through G and C on H's side of the straight
line L, keeping its sides and angles, and it returns the points B′ and C′ where B and C come
down: `∃ B' C' : Point, …`. The certificate lets only I.4 and I.8 cite it, which controls
where it is used, not what it says. As an axiom it is a construction principle: the overlap
catalogue's `Audit.I_23` proves I.23, the copying of an angle, from it and seven rules that
name the ray and the side ([overlaps](../reports/overlaps.md), row I.23).

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

### A finite symbolic context

[`Staging/Superposition/Formulas.lean`](../../Staging/Superposition/Formulas.lean).

- A **symbol** is a member of a type the proof chooses: `P` for points, `L` for straight
  lines. The rule takes its symbols from `Fin n` and `Fin m`, so in the rule a symbol is a
  number and nothing else.
- An **`Atom`** is a primitive relation on symbols: equality of points, a point on a straight
  line, betweenness, the same side, and equality of two lengths, two angles or two
  triangles. A **`Lit`** is an atom or its denial. A literal holds no point, no straight line
  and no proposition: it says one primitive thing of the symbols it names.
- A **`Metric`** formula is an equality of lengths, of angles or of triangles, over point
  symbols only: the only conclusions the rule exports.
- A **valuation** (`Val P L`) gives a point to each point symbol and a straight line to each
  line symbol. `Holds v` reads a formula in the plane under `v`. The symbols are data; the
  valuation is the figure.

Two symbols are one symbol only when they are the same symbol, so a derivation, which works
on symbols, can never learn that two symbols stand for one point unless a step proves it. In
round 1 the names were Lean points, and two names were one whenever their points were equal.

**What symbols do not prevent.** A valuation chooses points, and a point can be chosen by
cases on any proposition. So a true given literal can still be equivalent to any proposition
the proof can name, "no placement exists" among them; `valuation_encodes` proves it, so that
no one claims otherwise. The derivation cannot see this: it is fixed before the valuation,
and it holds under every valuation (`Derives.sound`). What the encoding could still do
through the rule's content is the non-derivability question below, which is not claimed.

**Ease of use.** A proof names its symbols with an inductive type of its own, and numbers
them once (`Symbols`, in `Rule.lean`); `Rule.apply` uses the rule on the numbers. I.4's
symbols are `a`, …, `f` for the corners, `de` and `df` for two straight lines, and `b'`,
`c'`, `ac'` for what the placement lays down: lower case for symbols, upper case for
points, so that a reader can tell them apart at a glance.

### Laws as data, applied by one rule

[`Staging/Superposition/Derivations.lean`](../../Staging/Superposition/Derivations.lean).

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
   had silently grown to contain them. With the laws cited, the staged I.4 rests on exactly
   the axioms of the edition's I.4, less `superposition` (below).
2. *The order of the propositions.* Euclid's argument for I.8 uses I.7 inside the placement,
   and I.7 cites I.5, which rests on I.4. Were I.7 a rule of the derivation, the foundations
   would assume what Book I proves. Cited, it is supplied by the edition's I.7.

**Why the list is fixed.** A law whose premises can never hold together holds vacuously.
Were any law with any proof allowed, one whose premises describe a placement and whose
conclusion is false would hold exactly when no placement exists, and citing it would turn
that absence into a contradiction, which classical logic turns into points. A fixed list of
laws, each a specific geometric statement, cannot be chosen that way. A new law joins the
list by a revision of this brief.

### A restricted derivation judgment, with no construction steps

`Derives cites Γ ℓ` is an inductive judgment: the literal `ℓ` follows from the literals `Γ`,
all over the same symbols, by two kinds of rule.

- **Logic.** Equality of points, lengths, angles and triangles is reflexive, symmetric and
  transitive, and Common Notion 4 puts a point for one that coincides with it.
- **Citing a law** (`Derives.cite`). A step names a law of `cites`, puts a symbol of the
  derivation for each letter, derives the law's premises and concludes its conclusion.

Neither kind introduces a symbol. There is no rule that constructs a point, draws a straight
line or a circle, splits cases, argues by contradiction or concludes anything from a
contradiction. That is enough for I.4 and I.8. For readable proofs, each law also has a
step of its own (`Derives.ray_unique` and the rest), proved from `cite`, with its premises
in order.

`Derives.sound` shows that whatever a derivation proves holds under every valuation that
makes its context true, once the cited laws hold: the same valuation, never one extended by
a new object. Its axioms are `propext` and `Classical.choice`, from Lean's logic: no project
axiom. `Derives.map` shows that every rule is a scheme, carried along any renaming of the
symbols.

### The placement's fresh symbols and retained facts

[`Staging/Superposition/Rule.lean`](../../Staging/Superposition/Rule.lean). The placement's
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

The first four are the present rule's conclusion word for word (`Placed`). The fifth is new
in round 2. It is Euclid's own object: "the straight line AC will also coincide with DF"
speaks of the side AC as it falls. With it, the law of one ray for one angle can name all
three of its straight lines and be proved without drawing any (below), and nothing is drawn
inside the placement. Its cost is in the model obligation: wherever the triangle can be laid
down, the straight line through D and C′ must exist too, which Postulate 1 gives, since D is
not C′. Open question 5 asks the owner to confirm it.

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
structure Rule : Prop where
  infer : ∀ {cites : List Cited}, (∀ c ∈ cites, c.Holds) →
    ∀ {n m : Nat} {Γ : List (Lit (Fin n) (Fin m))} {a b c d g h : Fin n} {l : Fin m}
      {φ : Metric (Fin n)},
      Derives cites (branch Γ a b c d g h l) (pos (φ.map Name.given).toAtom) →
      ∀ v : Val (Fin n) (Fin m), Triangle (v.pt a) (v.pt b) (v.pt c) →
        OnLine (v.pt d) (v.line l) → OnLine (v.pt g) (v.line l) → v.pt d ≠ v.pt g →
        ¬ OnLine (v.pt h) (v.line l) → (∀ ℓ ∈ Γ, ℓ.Holds v) → φ.Holds v
```

In words: given laws that hold, and a restricted derivation of an equality over the
figure's symbols from the given facts Γ, the guards and what the placement keeps, the
equality holds in every figure that satisfies the present rule's guards and Γ. `branch Γ …`
is that context. The derivation comes before the valuation: one derivation, over symbols,
serves every figure.

**Against System E.** System E states two rules (§3.7, p. 725, as printed): its Π₁ keeps
an angle, and its Π₂ the three sides. Our present rule follows LeanEuclid, by Logan Murphy,
Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and Xujie Si, in combining them into
one that keeps all six sides and angles, and the kept facts above inherit that. In our
reading of the sequent form, our branch takes no construction step and our Δ′ is one
equality of magnitudes, where the paper's text leaves both more open. So `Rule` is an
E-style restriction of the present rule; we do not claim it equivalent to System E's
two-rule presentation, which would need an argument of its own (Astra).

## What the laws' proofs draw

Citing a law draws nothing in the placement: the step puts symbols already there for its
letters. The law's own proof is a universal statement proved outside the placement, and
Astra asked that such proofs be inspected rather than assumed admissible. `#print axioms`,
at this revision, for each law's proof (a construction rule is an axiom whose conclusion
asserts that something exists: the Postulates 1, 2, 3 and 5, the `exists_point` rules, the
intersection rules and `superposition`):

| Law | Proof | Construction rules it uses |
|---|---|---|
| Metric 3, Metric 4, Metric 9 | the axioms `len_symm`, `angle_symm`, `area_congruent` | none |
| Distinct ends | Book Zero's `ne_of_len_eq` | none |
| One point at one distance on a ray | Book Zero's `OnRay.eq_of_len_eq` | none |
| One ray for one angle, both halves | `onLine_of_angle_eq_named`, new in `Derivations.lean` | none |
| I.7 | the edition's I.7, supplied by the theorem that cites it | Postulates 1, 2 and 3, seven other construction rules, and today `superposition`, through I.5 and I.4 |

`Cited.holds_of_drawsNothing` proves every law but I.7 in one theorem; its `#print axioms`
lists 23 axioms, Lean's three among them, and no construction rule. In round 1, one ray for
one angle was proved through Book Zero's `onRay_of_angle_eq`, which draws the straight lines
DE, DF and DP (Postulate 1, and `exists_point` through `Triangle.angle_pos`): with P the
laid-down C′, that drew through a point of the placement. Round 2 states the law with its
three straight lines named, the third the side laid down, and proves it again with no
construction.

**I.7 remains.** Its proof, with its helpers, draws the six straight lines joining its four
points (Postulate 1), finds where AD and CB cross (an intersection rule), produces AC and AD
(Postulate 2), and cites I.5, which cuts off with I.3 and so uses its circles (Postulate 3).
Inside I.8's placement, I.7's point C is G, the laid-down corner. The I.7 *statement* asserts
no existence, and citing it draws nothing in the placement. Every law I.4's derivation
cites draws nothing (`Prop4.cites_drawNothing`); I.8's cites I.7, where Euclid's argument
uses it ("But they cannot be so constructed. [I. 7]", the reference Heath's). Open question 4
asks which reading the rule adopts.

## How I.4 and I.8 keep Euclid's arguments

[`Staging/Superposition/Prop04.lean`](../../Staging/Superposition/Prop04.lean) and
[`Prop08.lean`](../../Staging/Superposition/Prop08.lean). Each states the proposition word for
word, with Heath's enunciation as its docstring and Heath's proof as its `--` lines in
order, and adds the rule as a hypothesis, `S : Rule`; I.8 also takes I.7's statement, `h7`.
Under each of Euclid's sentences is the step of the derivation that carries it. Each proof
draws its straight lines before the placement, gives the figure as a valuation `v` of its
symbols, lists the given facts Γ over those symbols, derives inside the placement, and
leaves it by `Rule.apply`.

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

**What the proofs rest on.** `#print axioms` for the staged I.4 lists 25 axioms, Lean's three
logical axioms among them: exactly the 26 of the edition's I.4, less `superposition`. Its two
construction rules, Postulate 1 and `exists_point`, enter before the placement, in drawing DE
and DF and in the corners' distinctness (`Triangle.ne₁₂` and its siblings). The staged I.8
lists 17, each among the edition's I.8's; with I.7's own, supplied as `h7`, they make
exactly the edition's I.8's set. Neither lists `Tacit.superposition`. Heath's `--` lines and
the docstrings are byte for byte the edition's: 27 lines in I.4 and 24 in I.8. At landing
the hypothesis becomes the axiom, `h7` becomes the edition's I.7, and both statements are
unchanged.

## The restriction theorem

[`Staging/Superposition/Restriction.lean`](../../Staging/Superposition/Restriction.lean),
with `Rule.of_placement` in `Rule.lean`. The restriction, in five parts: parts 1, 2, 3 and 5
are theorems; part 4 is read off the statement of `Rule.infer`, and its one theorem is
`Metric.holds_const`.

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
   `Cited.holds_iff`: every law asserts no existence. And every law I.4 cites is proved with
   no construction rule (above); I.8's citation of I.7 is open question 4.
4. **No hypothesis of the rule speaks of the placement.** The rule's hypotheses are the
   cited laws (a fixed list, each a universal statement over its letters), the given facts
   and the conclusion (data over the figure's numbered symbols, holding no point, no straight
   line and no proposition), a derivation (over symbols, and before any valuation), and a
   valuation of the figure's symbols that satisfies the guards and the given facts. B′, C′
   and the side occur only as symbols inside the derivation; no hypothesis gives them a point
   or a straight line, or quantifies over them. Astra's second observation needs a premise
   that quantifies over the placed points, so the rule's own hypotheses cannot instantiate
   it. `Metric.holds_const`: no exportable formula is unsatisfiable.
5. **No stronger than laying a triangle down.** `Rule.of_placement`: if every triangle can be
   laid down as the present rule says, with a straight line through D and C′ for its side AC,
   then `Rule` holds, and its proof rests on Lean's three logical axioms alone. An `example`
   in `Rule.lean` derives that hypothesis from today's `Tacit.superposition` and Postulate 1,
   so `Placed` is exactly the present rule's conclusion.

**What part 4 does not say.** It does not say that a given fact cannot encode the absence of
a placement: under a valuation that chooses its points by cases, it can (`valuation_encodes`).
Round 1 gave a different reason for part 4, that a derivation's premises are literals about
named points and so "no placement exists" is never one of them; the verification showed
that false, and it is withdrawn. Whether an encoded premise could recover the placement
through what the rule asserts is the non-derivability question, which is not claimed.

Astra's two observations are kept as theorems, as warnings: `eliminator_iff_exists` and
`eliminator_false_gives_exists`.

**What these do not say.** They do not say that the restricted rule, with the other laws,
cannot prove the present rule. In the full theory it can, by the route Euclid takes: I.4
and I.8 from the rule, then I.22 and I.23, as Astra observes ("A constructive placement
theorem may eventually be derived from the legitimate construction propositions"). The
restriction concerns the route by which construction becomes available, not the
independence of I.23 from a theory that proves it.

## The model obligation

`Rule.of_placement` reduces the rule to the placement with its side drawn, by logic alone:
its proof uses that placement and `Derives.sound`, which uses only the cited laws, assumed by
the rule, and it rests on no geometric axiom. So a model of the plane satisfies `Rule` once
triangles can be laid down there and straight lines drawn through two points. The obligation
is the present rule's row of [MODEL.md](../../tests/model/MODEL.md), with Postulate 1's:
move the plane rigidly, taking A to D and the ray from A through B onto the ray from D
through G, and reflect in L if C lands on the side away from H; rigid motions keep lengths
and angles, and the triangle being a triangle keeps C′ off L, and so other than D.

For the formal model (#73), in `model/` with Mathlib:

- the placement is proved in `EuclideanSpace ℝ (Fin 2)` by an explicit isometry, with the
  reflection when needed, and with angles kept as Astra's piecewise definition measures
  them (every arm here is nonzero, since the triangles are triangles), and the side through
  D and C′ by Postulate 1's model proof;
- the rule then follows by the argument of `Rule.of_placement`, instantiated at the model's
  signature; it needs no geometry beyond the placement;
- the rule's statement mentions `Fin`, `List` and the prototype's inductive types (`Atom`,
  `Lit`, `Metric`, `Val`, `Name`, `LineName`, `Letter`, `LineLetter`, `Law`, `Cited`,
  `Derives`), so the generator that translates the laws from their elaborated declarations
  must translate those too, or the model package must state the rule for its signature by
  hand with a checked correspondence. `Symbols` and `Rule.apply` are built on the rule and
  are not part of its statement, so they need no translation. This is new work for #73, and
  should be settled before the rule lands.

## What it clears, and what it does not

**It clears the direct construction shortcut.** No conclusion of the restricted rule names a
symbol of the placement, so the temporary placement points can no longer be returned as the
answer to I.2, I.3 or I.23. `Audit.I_2`, `Audit.I_3` and `Audit.I_23` each take a point the
present rule returns, and none of them can be written against it. The overlap rows for I.2
and I.3 would be retired, since neither proposition rests on superposition; the row for I.23
would be retired, or rewritten to say how the rule enters I.23's proof through I.8.

**It does not:**

- make I.23, I.2 or I.3 unprovable, nor should it: I.2 and I.3 already rest on no
  superposition, and I.23 must stay provable through I.22 and I.8;
- touch the other overlap rows: Circle 2 and III.2, Diagram-segment 2 and III.5 and III.6,
  Generalities 3 and III.6, Generalities 2 and III.1's porism, Diagram-angle 3 and I.13,
  Metric 5 and I.47, Circle 4 and I.7;
- shrink the certificate: 96 of the 102 entries in the committed `facts.json` rest on
  superposition today (all but I.1, I.2, I.3, I.22, III.5 and III.6), and after landing the
  same entries would rest on the restricted rule, which enters at I.4.

## The disclosure, now

The owner's decision asks that, until the rule is replaced, the edition say that our rule is
stronger, as a construction principle, than System E's. Round 1 filed this under landing; it
is present work. Four places say today, in effect, that the certificate's restriction meets
System E's:

- `Elements/Foundations/Tacit/Superposition.lean`, lines 21 and 22: "To respect System E's
  restriction, the certificate's checks allow only I.4 and I.8 to cite it." (the coordinator)
- `docs/reports/overlaps.md`, in the note under I.23, and `Audit/Overlaps.lean`, in the
  docstrings of `I_2` and `I_23`: "The certificate lets only I.4 and I.8 use superposition,
  as System E asks." (the catalogue's owner)
- `mishnah/I/04.md`, line 1: "the rule of System E §3.7, in the combined form LeanEuclid
  gives it, which only I.4 and I.8 may cite", which a reader may take to mean that our rule
  carries System E's restriction (the mishnah's owner; `book/I/04.md` follows from it, and
  the integrator regenerates it).

The owner's decision also names where the disclosure goes: "the overlap catalogue and the
I.4 and I.8 pages" (#75). I.8's mishnah (`mishnah/I/08.md`, line 1) says only that the
moving is our rule, and claims nothing of System E; it is to carry the disclosure too (the
mishnah's owner; `book/I/08.md` follows from it).

The text Astra proposes, for those owners to place: "Our superposition axiom asserts that a
congruent triangle can be placed on a given ray and side. The edition permits its direct use
only in I.4 and I.8. This axiom is stronger as a construction principle than System E's
restricted inference rule." Nothing is changed on this branch: each file has its owner.

## Evidence before landing

Astra names three kinds. Their state at round 2:

1. **Positive proofs.** I.4 and I.8 compile from the rule with their statements and with
   their coincidence arguments visible, step under sentence. *Done in the prototype*, as
   staged theorems taking the rule as a hypothesis, on the symbolic design.
2. **A restriction theorem.** The represented system cannot export the placement's objects
   as witnesses, nor take construction steps in the placement. *Done in the five parts
   above*, for the symbolic calculus. Whether these parts are the right statement of the
   restriction is open question 2.
3. **A carefully scoped non-derivability result, if claimed.** *Not claimed.* A route, for
   whoever takes it up. Besides its hypotheses about the figure, an instance of `Rule`
   assumes that each cited law holds, `∀ c ∈ cites, c.Holds`; that hypothesis quantifies
   over every point and straight line, not only the figure's, and in hypothesis position it
   is not a statement about the figure alone. But every law in `Cited` is true in the plane
   outright, I.7's included, so in the plane each instance of `Rule` reduces to its part
   about the figure. That part speaks only of the figure's points and straight lines, and
   its only existential, "some straight line passes through A, B and C", stands negated, in
   the hypothesis that ABC is a triangle. So that part, true in the plane, stays true in any
   part of the plane that keeps the straight line through any two of its points and the same
   lengths, angles and areas. Take the points with rational coordinates, the straight
   lines through two of them, and real magnitudes: the laws that do not mention circles
   appear to hold there, and so does every instance of `Rule`; but the triangle with corners
   (0, 0), (1, 0), (0, 1) cannot be laid along the ray from (0, 0) through (1, 1), for B′
   would be (1/√2, 1/√2). Checked law by law and proved in `model/`, that would show the
   restricted rule does not give the placement from the laws that do not mention circles.
   Until then, nothing is claimed.

A failed compilation of `Audit.I_23` against the new rule is a useful regression signal,
and establishes none of the third kind by itself (Astra).

**Still required before the rule lands:**

- a reading of the revision delivered for landing, wherever it has changed since `08b218b`,
  by a reader who did not write it, under orders to break it: round 2 was so read at
  `08b218b` ("The reviews");
- the owner's and Astra's answers to open questions 2, 4 and 5;
- #40, the model's law names as a pinned data file;
- the model's proof of the placement with its side, in `model/` (#73), and the decision on
  translating the rule's inductive types;
- the coordinator's approval of the prototype's proofs in `Staging/`, with a line in
  `Staging.lean` ("Staging and naming", below);
- a non-derivability result only if one is to be claimed;
- at landing, every check CI runs, with the new axiom planted in the negative test, and the
  records of I.4 and I.8 read again.

## The guards

The present rule's guards stay, as hypotheses of `Rule.infer`; those that are literals are
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
- **Reflections.** The model's proof must allow a reflection in L: a rotation and a
  translation alone cannot always put C′ on H's side. MODEL.md's argument does; the formal
  model must too.
- **Side equalities are not angle equalities.** Our placement keeps all six sides and
  angles, and the model justifies the angles by the rigid motion itself, not by deriving
  them from the sides. Were a placement carrying only the sides adopted (System E's Π₂), no
  step could use an angle equality from it.

## Staging and naming

The prototype departs from what [FORMALIZATION.md](../FORMALIZATION.md), section 6, and
`Staging.lean` describe, and says so here. It is not a stage of brief 0005; its files hold
proofs and no `sorry`; and its theorems are `Elements.Superposition.Prop4` and `Prop8`
rather than `Elements.BookI.Staging.Prop4`, because they belong to the rule's prototype and
take the rule as a hypothesis, not to a stage of Book I. WORKFLOW, section 2, allows "the
proofs of a prototype the coordinator has approved"; the owner directed this prototype on
18 October, and we ask the coordinator to approve it and to add a line to `Staging.lean`, as
the mixed-angle prototype has. `check_fidelity.py`'s scan for forbidden commands does not
cover `Staging/` (FORMALIZATION, section 7), so that the six files declare no axiom and use
none of the forbidden commands rests on review: a search of them finds no `axiom`
declaration, `sorry`, `native_decide`, `set_option`, `elab`, `macro`, `extern`, `unsafe`,
`opaque` or `implemented_by`.

## What the prototype proves, and what it does not

Proved, with no `sorry` and no axiom added (`lake build Staging`; `#print axioms` as above):

- the symbolic language, the laws as data, the derivation judgment and the rule, as
  described, with the front end for named symbols (`Rule.apply`);
- `Derives.sound`, on no project axiom; `Derives.map`;
- the laws cited, each from Book Zero and the foundations, without superposition and with no
  construction rule, and I.7's law from I.7's statement;
- `Rule.of_placement`, on Lean's logical axioms alone, and the check that the present rule
  with Postulate 1 satisfies its hypothesis;
- the restriction theorem's parts 1, 2, 3 and 5, part 4's `Metric.holds_const` (the rest of
  part 4 is read off the rule's statement), `valuation_encodes`, and Astra's two
  observations;
- I.4's whole conclusion and I.8's whole conclusion from the rule, by Euclid's coincidence
  arguments.

Not proved, and not claimed:

- a non-derivability result (above);
- that `Rule` is equivalent to System E's two rules;
- the model obligation in Lean (it waits for `model/`, #73);
- I.5 and I.7 from the staged I.4: the staged I.8 takes I.7's statement as a hypothesis.
  The edition's I.5 and I.7 cite I.4 by name and never cite superposition directly (the
  certificate's policy checks that), so once I.4's proof changes they rest on the
  restricted rule with no edit;
- anything about the pages, the records or the generated files, which do not change.

## Landing, when complete

Each step belongs to its owner (AGENTS.md, "Scope and ownership"); none is taken here.

- **Prerequisites.** #40, the model's law names as a pinned data file, which the owner made
  a prerequisite for any new axiom; and the model's proof of the placement with its side
  (#73).
- **The foundations (the coordinator).** `Elements/Foundations/Tacit/Superposition.lean`
  is replaced by the symbolic language, the letters, `Law`, `Cited` and `Cited.law`, the
  derivation judgment, the placement's symbols, the guards and kept facts, and one axiom,
  `superposition : Rule`. `Certificate/axioms.lock` is regenerated with
  `check_fidelity.py --write-lock`, with a decisions entry, `tests/model/lock.sha256`
  updated, and MODEL.md's superposition row rewritten to say that the rule reduces to the
  placement with its side by `Rule.of_placement`. One axiom replaces one, so the count does
  not change.
- **A home for the evidence (Book Zero, with its owner).** The theorems that make the rule
  usable and trustworthy must survive landing and stay built: `Derives.sound`,
  `Derives.map`, the laws' proofs (`Cited.holds_lenSymm` and the rest, and
  `onLine_of_angle_eq_named`), `Symbols`, `branch_map` and `Rule.apply`, `Rule.of_placement`,
  and the restriction theorems of `Restriction.lean`. We propose one Book Zero module,
  `Elements/Figure/Superposition.lean`, which I.4 and I.8 import, so that `lake build`
  builds it and MODEL.md's row cites a theorem the build checks; I.7's law, which needs
  I.7, goes to I.8's file.
- **The policy.** Only I.4 and I.8 cite the rule directly, as now; the negative test for
  superposition outside I.4 and I.8 plants the new axiom.
- **The proofs.** `Elements/BookI/Prop04.lean` and `Prop08.lean` take the prototype's proofs,
  with the rule as an axiom; their statements are unchanged. The staged copies are deleted
  in the same change.
- **The catalogue and the audit (the catalogue's owner).** `Audit.I_2`, `Audit.I_3` and
  `Audit.I_23`, which call the present rule and would no longer compile, are retired, with
  the rows for I.2 and I.3; the I.23 row is retired or rewritten.
- **Records made stale.** `review/I/04.toml` and `review/I/08.toml`, whose proofs change; the
  integrator regenerates the generated files, since the statement of the axiom that 96
  entries rest on changes.
- **The page text, after replacement**, as Astra proposes: "Superposition permits a
  hypothetical placement while proving facts about the triangles already given. The
  hypothetical vertices cannot be returned as constructed points."

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
   construction rule; I.7's construction is disclosed above, and open question 4 states the
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

Two items it left open stay open, for their owners: the coordinator's approval of the
prototype in `Staging/` and its names ("Staging and naming"), and open questions 2 to 5. It
hunted for escapes along the routes Astra names (a given fact encoding a proposition through
the valuation, an opaque predicate among the atoms, an argument by contradiction, a cited
law that constructs in its proof, a conclusion naming a placement symbol) and found no way
out of the restriction.

The reviews' scratch files are not committed.

## Open questions for the owner and the coordinator

1. **Cited laws.** The rule assumes no law, and every theorem using it supplies the laws its
   derivation cites, so that the certificate sees them. The alternative, laws built into the
   derivation, hides Metric 9 and the rest from every certificate. We recommend citing.
2. **The restriction theorem.** Are the five parts the statement wanted, or should the
   restriction be stated another way before landing (for instance, as a theorem that every
   instance of the rule is a universal statement of a fixed shape)?
3. **The symbols' front end.** The rule numbers its symbols (`Fin n`), and a proof names them
   with an inductive type and `Symbols`. This keeps the axiom simple and the proofs readable.
   The alternative states the rule for any vocabulary with `Symbols` directly; it is
   equivalent, and the axiom's statement would be longer. We recommend the numbered rule.
4. **Laws whose proofs draw.** Every law I.4 cites is proved with no construction rule. I.7's
   proof draws, produces and, through I.5 and I.3, uses circles, and I.8 cites I.7 inside the
   placement, where Euclid's argument uses it. The prototype's reading: a law whose statement
   asserts no existence may be cited in the placement, whatever its proof draws, as a
   proposition once proved is cited anywhere. The stricter reading: only laws proved with no
   construction rule may be cited there (`∀ c ∈ cites, c.drawsNothing = true`, added to the
   rule). Under it, I.4 stands as it is, and I.8 cannot follow Euclid's route, which uses I.7
   inside the placement: I.8 would need another argument, labelled as one. Which reading
   should the rule adopt?
5. **The side laid down.** Round 2 adds to the kept facts that the side AC laid down is a
   straight line through D and C′, Euclid's "the straight line AC", so that nothing is drawn
   inside the placement. The model obligation then includes Postulate 1 for that side. The
   alternative, drawing the line inside the placement, is a construction step there. We
   recommend the kept side.
6. **More citable propositions.** The list `Cited` holds I.7 alone among the propositions.
   Another joins only by a revision of this brief, with the reason.
7. **Timing.** Astra suggests landing before the consolidation review if the proofs, the
   restriction and the model's justification are complete, and otherwise keeping the
   present rule with the disclosure. The prototype does not change that advice.

## Checks

At the branch's head, on the files committed with this brief:

- `lake build Staging`: passes (173 jobs). The six files declare no axiom, use none of the
  forbidden commands and contain no `sorry`; the other staged files keep their own `sorry`s,
  as on main.
- `#print axioms` for each theorem named above, as reported in this brief.
- Heath's `--` lines and the docstrings of the staged I.4 and I.8 compared with the
  edition's: identical.
- `python3 scripts/check_style.py` and `python3 scripts/check_links.py`: pass.

## Thanks

To Jeremy Avigad, Edward Dean and John Mumma, whose System E gives the rule and its
restriction; to Logan Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and
Xujie Si, whose LeanEuclid gives the one-rule form our present rule follows; to Sir Henry
Savile, through Heath, for the argument on a ray that carries I.4's coincidences; to Astra,
whose third answer set out this design, the two observations it guards against, and the
evidence it asks for; and to the reviewers of round 1, the adversarial run and the verifier,
and the reviewer of round 2, whose findings made round 2 and sharpened it. We are grateful
to them all.
