# Brief 0009: a restricted rule of superposition

*18 October 2026. A design brief and a prototype for issue #75, written to the owner's
decision of 18 October after Astra's third answer. Nothing in `Elements/` changes and no
axiom is added: the restricted rule is a hypothesis, `Rule`, which the prototype's theorems
take as an argument, in `Staging/Superposition/`. The rule lands only when it is complete;
until then the edition keeps its present rule, with the disclosure below. The brief is for
the coordinator's and the owner's review. Once approved, a later change is a revision of
this brief ([WORKFLOW.md](../WORKFLOW.md), section 2, "Correcting a frozen brief"). The code
states what we formalized; where the code and this brief disagree, the disagreement is
recorded and reconciled ([FORMALIZATION.md](../FORMALIZATION.md), section 1).*

Base: the branch `lean/superposition-prototype` was cut from main at `f17b427`. The
prototype is six files in `Staging/Superposition/`, 1,201 lines, and `lake build Staging`
passes with them.

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
assumption to construct new objects." As a sequent inference: if Γ ⇒ ∃x⃗. Δ, and Γ, Δ with
the facts Π of the placement give Δ′, then Γ ⇒ ∃x⃗. Δ, Δ′, where Δ′ speaks only of objects
already present.

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

### Represented formulas over named objects

[`Staging/Superposition/Formulas.lean`](../../Staging/Superposition/Formulas.lean).

- A **`Name`** is a given point (`Name.given P`, written `P` by a coercion), or one of the
  two corners the placement lays down, `Name.second` (B′) and `Name.third` (C′). The
  laid-down corners are names in formulas and nothing else: Lean never holds them as points.
- An **`Atom`** is a primitive relation on named points and given straight lines: equality
  of points, a point on a straight line, betweenness, the same side, and equality of two
  lengths, two angles or two triangles. A **`Lit`** is an atom or its denial. None hides a
  quantifier, so none can carry an existential claim into a derivation; the phrases with
  hidden quantifiers (`OnRay`, `SameSideOf`, `Collinear`, `Triangle`) are not atoms, and the
  steps that use them name their straight lines instead.
- A **`Metric`** formula is an equality of lengths, of angles or of triangles: the only
  conclusions the rule exports.

`Holds σ` reads a formula in the plane once each name `n` stands for the point `σ n`.

### A restricted derivation judgment, with no construction steps

[`Staging/Superposition/Derivations.lean`](../../Staging/Superposition/Derivations.lean).
`Derives cites Γ ℓ` is an inductive judgment: the literal `ℓ` follows from the literals `Γ`
by fixed rules, citing only the laws in the list `cites`. Every rule has literals as
premises and one literal as conclusion, and none introduces a name. There is no rule that
constructs a point, draws a straight line or a circle, splits cases, argues by
contradiction or concludes anything from a contradiction. This is stricter than System E,
whose branch may construct, and it is enough for I.4 and I.8.

The rules are of two kinds.

- **Logic.** Equality of points, lengths, angles and triangles is reflexive, symmetric and
  transitive, and Common Notion 4 puts a point for one that coincides with it.
- **Cited laws.** Every other step cites one law of the fixed list `Cited`, stated exactly as
  the step uses it (`Cited.Law`): Metric 3, Metric 4, Metric 9, that a straight line equal
  to one with distinct ends has distinct ends, that on a ray one point lies at a given
  distance from its start (Savile's argument), that on one side of a straight line one ray
  from a point of it makes a given angle with it, and I.7. The two ray laws are stated with
  their straight lines named, as Astra advised, so that applying them inside the placement
  draws nothing.

**Why the laws are cited rather than built in.** The rule assumes none of them; it asks
each law a derivation cites to hold, and the theorem that uses the rule supplies a proof of
each (`Cited.law_lenSymm` and the rest, from Book Zero and the foundations). There are two
reasons.

1. *The certificate.* A derivation is data, and Lean records no dependency on the facts a
   datatype's constructors mention. The first draft of the prototype built the laws in, and
   `#print axioms` for its I.4 listed Postulate 1 and one Points rule and nothing else:
   Metric 9, Savile's argument and the rest had vanished into the hypothesis, and the rule
   had silently grown to contain them. With the laws cited, the staged I.4 rests on exactly
   the axioms of the edition's I.4, less `superposition` (below).
2. *The order of the propositions.* Euclid cites I.7 inside the placement of I.8, and I.7
   rests on I.5 and I.4. Were I.7 a rule of the derivation, the foundations would assume
   what Book I proves. Cited, it is supplied by the edition's I.7.

**Why the list is fixed.** A rule that accepted any law with any proof of soundness would
be stronger than System E's: a law whose premises include the placement's facts and whose
conclusion is false holds, vacuously, if no figure of that kind admits a placement, and the
rule would then turn that absence into a contradiction, which classical logic turns into
points. A fixed list of laws, each a specific geometric statement, cannot hold vacuously in
that way. A new law joins the list by a revision of this brief.

`Derives.sound` shows that whatever a derivation proves holds of the very points its names
stand for, under any assignment that makes its context true, once the cited laws hold. Its
only axiom is `Classical.choice`, from Lean's logic: no project axiom.

### The hypothetical placement's retained facts

[`Staging/Superposition/Rule.lean`](../../Staging/Superposition/Rule.lean). In the
placement the triangle ABC laid down with A on D is D B′ C′; "A on D" is carried by the
name D itself. The placement keeps (`kept`):

- B′ on L, with D not between B′ and G: B′ is on the ray from D through G;
- C′ on H's side of L;
- DB′, B′C′, C′D equal to AB, BC, CA;
- the angles at D, C′ and B′ equal to those at A, C and B.

That is the present rule's conclusion word for word (`Placed`), and nothing more. Astra
asked that the incidence and nondegeneracy facts the arguments need be retained
explicitly. They are, as steps rather than as assumptions: that B′, C′ and D are three
points follows inside the placement from the kept sides, by the cited law that a straight
line equal to one with distinct ends has distinct ends, and I.4 takes those steps by name.
A first version listed them among the kept facts; the adversarial review below found that
this made the rule contain a consequence of Metric 1 that no certificate showed, and they
were moved.

The guards that are literals are available as they stand (`guards`): D and G on L, D not
G, H off L. Whatever else a proof needs of the guards, such as the corners of ABC being
three points, it proves outside the placement and lists among the given facts Γ, so that
the certificate sees the proof.

### Exported conclusions

A list of `Metric Point`: equalities of lengths, angles and triangles among given points.
For a first implementation Astra advised exactly this: conjunctions of the metric equalities
I.4 and I.8 need.

### The rule

```lean
structure Rule : Prop where
  infer : ∀ {cites : List Cited}, (∀ c ∈ cites, c.Law) →
    ∀ {A B C D G H : Point} {L : Line}, Triangle A B C → OnLine D L → OnLine G L → D ≠ G →
    ¬ OnLine H L →
    ∀ {Γ : List (Lit Point)}, (∀ ℓ ∈ Γ, ℓ.Holds id) →
    ∀ {φ : List (Metric Point)},
      (∀ m ∈ φ, Derives cites (branch Γ A B C D G H L) (pos (m.map Name.given).toAtom)) →
      ∀ m ∈ φ, m.Holds id
```

In words: given the present rule's guards, true facts Γ about given points, and the laws
cited, every equality among given points that a restricted derivation proves from Γ, the
guards and what the placement keeps, holds. `branch Γ …` is that context.

**Against System E.** System E states two rules (§3.7, p. 725, as printed): its Π₁ keeps
an angle, and its Π₂ the three sides. Our present rule follows LeanEuclid, by Logan Murphy,
Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and Xujie Si, in combining them into
one that keeps all six sides and angles, and the kept facts above inherit that. Our branch
may not construct, where System E's may, and our Δ′ is a list of equalities of magnitudes,
where System E's is any set of literals. So `Rule` is an E-style restriction of the present
rule; we do not claim it equivalent to System E's two-rule presentation, which would need an
argument of its own (Astra).

## How I.4 and I.8 keep Euclid's arguments

[`Staging/Superposition/Prop04.lean`](../../Staging/Superposition/Prop04.lean) and
[`Prop08.lean`](../../Staging/Superposition/Prop08.lean). Each states the proposition word for
word, with Heath's enunciation as its docstring and Heath's proof as its `--` lines in
order, and adds the rule as a hypothesis, `S : Rule`; I.8 also takes I.7's statement, `h7`.
Under each of Euclid's sentences is the step of the derivation that carries it.

**I.4.** Before the placement the proof names the straight line DE, along which the triangle
is laid, with F off it, and the straight line DF, along which AC will fall (Postulate 1
both). Naming DF there is new: the edition's proof meets it inside `onRay_of_angle_eq`,
whose proof draws it. The given facts Γ are the hypotheses, the two straight lines, and
the distinctness of the corners of both triangles. Then, inside the placement, first a step
Euclid takes for granted: B′, C′ and D are three points, since DB′, B′C′, C′D are AB, BC,
CA. Then Euclid's:

1. "the point B will also coincide with E, because AB is equal to DE": DB′ is AB is DE, and
   on the ray from D through E one point lies at that distance (`ray_unique`), so B′ is E;
2. "the straight line AC will also coincide with DF, because the angle BAC is equal to the
   angle EDF": the angle EDC′ is B′DC′, which is BAC, which is EDF; on F's side of DE one ray
   from D makes that angle (`ray_of_angle`, `ray_of_angle_side`), so C′ lies on DF, on F's
   side of D;
3. "hence the point C will also coincide with the point F": DC′ is CA is DF, so C′ is F;
4. the base: B′C′ is BC, and B′, C′ are E, F (Common Notion 4);
5. the triangle: DB′C′ is DEF (Common Notion 4), and ABC is DB′C′, being moved (Metric 9);
6. the remaining angles: C′B′D is CBA, and is FED; DC′B′ is ACB, and is DFE.

Four equalities among the given points leave the placement: BC = EF, △ABC = △DEF, ∠ABC =
∠DEF and ∠ACB = ∠DFE, which is I.4's conclusion. B′ and C′ stay behind.

**I.8.** The triangle BCA is laid down with B on E and C along the ray from E through F, on
D's side; C′ is where C comes down and G where A comes down, Euclid's own letter.

1. "the point C will also coincide with F, because BC is equal to EF": EC′ is BC is EF, so
   C′ is F (`ray_unique`);
2. "BA, AC will also coincide with ED, DF": GE is AB is DE, and GF is GC′ is CA is DF;
3. "But they cannot be so constructed. [I. 7]": G and D are on one side of EF (kept), so
   I.7, cited inside the placement, makes G and D one point;
4. "so that the angle BAC will also coincide with the angle EDF": EGC′ is BAC (kept), and
   is EDF (Common Notion 4).

One equality leaves the placement: ∠BAC = ∠EDF, which is I.8's conclusion.

**What the proofs rest on.** `#print axioms` for the staged I.4 lists 25 axioms, Lean's
three logical axioms among them: exactly the 26 of the edition's I.4, less `superposition`.
The staged I.8 lists 17, each among the edition's I.8's; with I.7's own, supplied as `h7`,
they make exactly the edition's I.8's set. Neither lists `Tacit.superposition`. At landing
the hypothesis becomes the axiom, `h7` becomes the edition's I.7, and both statements are
unchanged.

## The restriction theorem

[`Staging/Superposition/Restriction.lean`](../../Staging/Superposition/Restriction.lean),
with `Rule.of_placement` in `Rule.lean`. What is proved, in five parts:

1. **No laid-down corner is exported.** `exportable_iff`: a formula of the placement is the
   image of an exportable conclusion exactly when every name in it is a given point.
   `not_exportable_second` and `not_exportable_third`: a formula naming B′ or C′ is the image
   of none.
2. **The conclusions say nothing of where the corners went.** `Metric.holds_lift`: an
   exported formula reads the same whatever points B′ and C′ are taken to be; and
   `Rule.conclusion` restates the rule's output as an equality of magnitudes among given
   points. The rule asserts the existence of no point.
3. **No construction step in the represented calculus.** `Derives.map`: every derivation is
   carried along any renaming of its names, even one that merges names, so every rule is a
   scheme and none supplies a fresh name. `Derives.sound`: whatever a derivation proves
   holds of the very points its names stand for, under any assignment satisfying its
   context, using only the cited laws. This is a fact about the calculus. A cited law is a
   universal statement proved outside the placement, and one proof draws a straight line
   through the arbitrary point the law speaks of, which inside I.4's placement is C′ (open
   question 4).
4. **No exportable formula is unsatisfiable, and absence is no premise.**
   `Metric.holds_const`: every exportable formula holds when all the points it names are
   one point, so neither `False` nor any formula false in every figure is a conclusion.
   That alone does not close Astra's second door: under the given points an exportable
   formula can contradict the given facts (AA equal to AB, with A not B), and since a name
   may be any point, a formula can be made to say any proposition the proof can name (the
   review below compiled one). What closes it is that a derivation's premises are literals
   about named points, so "no placement exists" is never one of them, and that every
   instance of the rule is a statement about given points with no existential over points.
   Astra's second observation needs exactly the premise the rule cannot take.
5. **No stronger than laying a triangle down.** `Rule.of_placement`: if every triangle can
   be laid down as the present rule says, `Rule` holds, and its proof rests on Lean's three
   logical axioms alone. An `example` in `Rule.lean` checks that the present rule satisfies
   its hypothesis, so `Placed` is exactly its conclusion.

Astra's two observations are kept as theorems, as warnings: `eliminator_iff_exists` and
`eliminator_false_gives_exists`.

**What these do not say.** They do not say that the restricted rule, with the other laws,
cannot prove the present rule. In the full theory it can, by the route Euclid takes: I.4
and I.8 from the rule, then I.22 and I.23, as Astra observes ("A constructive placement
theorem may eventually be derived from the legitimate construction propositions"). The
restriction concerns the route by which construction becomes available, not the
independence of I.23 from a theory that proves it. A claim of non-derivability is the third
kind of evidence below, and is not made.

## The model obligation

`Rule.of_placement` reduces the rule to the placement, by logic alone: its proof uses the
present rule's conclusion and `Derives.sound`, which uses only the cited laws, assumed by
the rule, and it rests on no geometric axiom. So a model of the plane satisfies `Rule` once
triangles can be laid down there. The obligation is the present rule's
row of [MODEL.md](../../tests/model/MODEL.md): move the plane rigidly, taking A to D and the
ray from A through B onto the ray from D through G, and reflect in L if C lands on the side
away from H; rigid motions keep lengths and angles, and the triangle being a triangle keeps
C′ off L.

For the formal model (#73), in `model/` with Mathlib:

- the placement is proved in `EuclideanSpace ℝ (Fin 2)` by an explicit isometry, with the
  reflection when needed, and with angles kept as Astra's piecewise definition measures
  them (every arm here is nonzero, since the triangles are triangles);
- the rule then follows by the argument of `Rule.of_placement`, instantiated at the model's
  signature; it needs no geometry beyond the placement;
- the law's statement mentions inductive types (`Name`, `Atom`, `Lit`, `Metric`, `Derives`,
  `Cited`), so the generator that translates the laws from their elaborated declarations
  must translate those types too, or the model package must state the rule for its
  signature by hand with a checked correspondence. This is new work for #73, and should be
  settled before the rule lands.

## What it clears, and what it does not

**It clears the direct construction shortcut.** No conclusion of the restricted rule names a
laid-down point, so the temporary placement points can no longer be returned as the answer
to I.2, I.3 or I.23. `Audit.I_23` cannot be written against it: the overlap row for I.23
would be retired, or rewritten to say how the rule enters I.23's proof through I.8.

**It does not:**

- make I.23, I.2 or I.3 unprovable, nor should it: I.2 and I.3 already rest on no
  superposition, and I.23 must stay provable through I.22 and I.8;
- touch the other overlap rows: Circle 2 and III.2, Diagram-segment 2 and III.5 and III.6,
  Generalities 2 and III.1's porism, Diagram-angle 3 and I.13, Metric 5 and I.47, Circle 4
  and I.7;
- shrink the certificate: 96 of the 102 entries in the committed `facts.json` rest on
  superposition today (all but I.1, I.2, I.3, I.22, III.5 and III.6), and after landing the
  same entries would rest on the restricted rule, which enters at I.4.

## Evidence before landing

Astra names three kinds. Their state:

1. **Positive proofs.** I.4 and I.8 compile from the rule with their statements and with
   their coincidence arguments visible, step under sentence. *Done in the prototype*, as
   staged theorems taking the rule as a hypothesis. At landing their proofs replace the
   edition's.
2. **A restriction theorem.** The represented system cannot export the laid-down points as
   witnesses, nor take construction steps in the placement. *Done in the five parts above*,
   for the prototype's language. Whether these parts are the right statement of the
   restriction is a question for review (open question 2).
3. **A carefully scoped non-derivability result, if claimed.** *Not claimed.* A route, for
   whoever takes it up: every instance of `Rule` speaks of given points only, with no
   existential over points, so, true in the plane, it stays true in any part of the plane
   that keeps the straight lines through two of its points and the same lengths, angles and
   areas. Take the points with rational coordinates, the straight lines through two of
   them, and real magnitudes: the laws that do not mention circles appear to hold there,
   and so does every instance of `Rule`, since each holds in the whole plane; but the
   triangle with corners (0, 0), (1, 0), (0, 1) cannot be laid along the ray from (0, 0)
   through (1, 1), for B′ would be (1/√2, 1/√2). Checked law by law and proved in `model/`,
   that would show the restricted rule does not give the placement from the laws that do not
   mention circles. Until then, nothing is claimed.

A failed compilation of `Audit.I_23` against the new rule is a useful regression signal,
and establishes none of the third kind by itself (Astra).

## The guards

The present rule's guards stay, as hypotheses of `Rule.infer`; those that are literals are
also in `guards`, where a derivation may use them, and a proof that needs more of them (the
corners of ABC distinct) proves it outside the placement.

- **A zero-length ray.** D and G must be two points, so that the ray from D through G has a
  direction (`D ≠ G`). Without it B′ may be anywhere on L at the distance AB, and I.4's first
  coincidence, which needs D other than E, has nothing to stand on.
- **A collinear source.** ABC must be a triangle (`Triangle A B C`). For a flat triangle
  there is no point off L at the right distances; MODEL.md's mutation "superposition for a
  flat triangle" catches exactly this.
- **H on L.** H must be off L (`¬ OnLine H L`), or no point is on H's side, and the
  placement would be impossible.
- **Reflections.** The model's proof must allow a reflection in L: a rotation and a
  translation alone cannot always put C′ on H's side. MODEL.md's argument does; the formal
  model must too.
- **Side equalities are not angle equalities.** Our placement keeps all six sides and
  angles, and the model justifies the angles by the rigid motion itself, not by deriving
  them from the sides. Were a placement carrying only the sides adopted (System E's Π₂), no
  step could use an angle equality from it.

## What the prototype proves, and what it does not

Proved, with no `sorry` and no axiom added (`lake build Staging`; `#print axioms` as above):

- the formula language, the derivation judgment and the rule, as described;
- `Derives.sound`, on no project axiom; `Derives.map`;
- the laws cited, each from Book Zero and the foundations, without superposition, and I.7's
  law from I.7's statement;
- `Rule.of_placement`, on Lean's logical axioms alone, and the check that the present rule
  satisfies `Rule`;
- the restriction theorem's five parts, and Astra's two observations;
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
  a prerequisite for any new axiom; and the model's proof of the placement (#73).
- **The foundations (the coordinator).** `Elements/Foundations/Tacit/Superposition.lean`
  is replaced by the formulas, the derivation judgment, the cited laws' statements, the
  guards and kept facts, and one axiom, `superposition : Rule`. The laws' proofs
  (`Cited.law_lenSymm` and the rest) move to Book Zero, and I.7's to I.8's file.
  `Certificate/axioms.lock` is regenerated with `check_fidelity.py --write-lock`, with a
  decisions entry, `tests/model/lock.sha256` updated, and MODEL.md's superposition row
  rewritten to say that the rule reduces to the placement by `Rule.of_placement`, the
  placement that the harness already tests. One axiom replaces one, so the count does not
  change.
- **The policy.** Only I.4 and I.8 cite the rule directly, as now; the negative test for
  superposition outside I.4 and I.8 plants the new axiom.
- **The proofs.** `Elements/BookI/Prop04.lean` and `Prop08.lean` take the prototype's proofs,
  with the rule as an axiom; their statements are unchanged. The staged copies are deleted
  in the same change.
- **The catalogue and the audit.** `Audit.I_23` and the I.23 row are retired or rewritten.
- **Records made stale.** `review/I/04.toml` and `review/I/08.toml`, whose proofs change; the
  integrator regenerates the generated files, since the statement of the axiom that 96
  entries rest on changes.
- **The page text.** Until replacement, as Astra proposes: "Our superposition axiom asserts
  that a congruent triangle can be placed on a given ray and side. The edition permits its
  direct use only in I.4 and I.8. This axiom is stronger as a construction principle than
  System E's restricted inference rule." After replacement: "Superposition permits a
  hypothetical placement while proving facts about the triangles already given. The
  hypothetical vertices cannot be returned as constructed points."

## The adversarial review

A separate Codex run reviewed the prototype at `d649437`, with Astra's answer and System
E's section in hand, under orders to break it. It found no way to get a laid-down point, a
placement, `False` or a construction without circles out of the rule: `Name.at` and
relifting do not recover the laid-down names, the given facts must be true, the fixed list
of laws admits no vacuous law, and a contradictory context does not let a derivation reach
an arbitrary equality (it compiled a check of that, for every list of citations). It found
no step without support, no law false in the plane, no dropped guard and no kept fact
without justification, and it confirmed that the `--` lines and the docstrings of the
staged I.4 and I.8 are the edition's, 27 lines and 24. It made three findings that should
be fixed, and two minor ones:

1. The kept facts then included the distinctness of the laid-down corners, which follows by
   Metric 1, and the staged I.4's certificate lacked `len_self`. *Fixed:* the kept facts are
   the present rule's conclusion alone, the distinctness is derived in the placement by a
   cited law, the corners of ABC being distinct is a given fact, the staged I.4's
   certificate is the edition's less superposition, and `Rule.of_placement` rests on logic
   alone.
2. The proof of one cited law draws a straight line through C′. *Scoped:* the restriction
   theorem is stated for the calculus, and the choice of reading is open question 4.
3. `Metric.holds_const` was described as excluding `False` in disguise, which it does not
   under the given points. *Corrected:* part 4 of the restriction theorem, here and in the
   Lean, says what it shows and what closes Astra's second door.
4. (Minor.) Names are any points, not a checked inventory of the figure. *Recorded* as open
   question 3; the docstring of `Name.given` no longer says "already drawn".
5. (Minor.) The brief was missing at that revision. It is this file.

The review's scratch files are not committed.

## Open questions for the owner and the coordinator

1. **Cited laws.** The rule assumes no law, and every theorem using it supplies the laws its
   derivation cites, so that the certificate sees them. The alternative, laws built into the
   derivation, hides Metric 9 and the rest from every certificate. We recommend citing.
2. **The restriction theorem.** Are the five parts the statement wanted, or should the
   restriction be stated another way before landing (for instance, as a theorem that every
   instance of the rule is a statement about given points of a fixed shape)?
3. **Names as points.** The given facts Γ are literals whose names are Lean points, so the
   language has a name for every point, and two names are one name when their points are
   equal. Naming a point the proof holds builds nothing, and a derivation cannot reach a
   point it is not given; but a name may be any point term, so a formula can encode any
   proposition the proof can name (`if Q then A else B` as a name; the review below), and
   the given facts are not a checked inventory of the figure. A finite symbolic context with
   a valuation would make the separation plainer, at some cost in ease of use. Which do the
   owner and Astra prefer?
4. **What the laws' proofs draw.** `Cited.law_rayOfAngle` is proved from Book Zero's
   `onRay_of_angle_eq`, whose proof draws the straight line from D to the point P it speaks
   of (Postulate 1); read inside I.4's placement, P is C′. No step of the calculus draws
   anything, and the law, applied to straight lines already named, is a universal statement
   proved outside the placement. That is the reading the prototype takes, and the
   restriction theorem is stated for the calculus accordingly. Astra asked that such
   helpers be inspected, and a stricter reading is possible: then the calculus would need
   straight lines through two named points as names of its own, drawn by an explicit step
   that constructs no point, and the law would be restated to take the line DP as given.
   Which reading should the rule adopt before landing?
5. **More citable propositions.** The list `Cited` holds I.7 alone among the propositions.
   Another joins only by a revision of this brief, with the reason.
6. **Timing.** Astra suggests landing before the consolidation review if the proofs, the
   restriction and the model's justification are complete, and otherwise keeping the
   present rule with the disclosure. The prototype does not change that advice.

## Checks

At the branch's head, on the files committed with this brief:

- `lake build Staging`: passes. The new files declare no axiom, use none of the forbidden
  commands and contain no `sorry`; the other staged files keep their own `sorry`s, as on
  main.
- `#print axioms` for each theorem named above, as reported in this brief.
- `python3 scripts/check_style.py` and `python3 scripts/check_links.py`: pass.

## Thanks

To Jeremy Avigad, Edward Dean and John Mumma, whose System E gives the rule and its
restriction; to Logan Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and
Xujie Si, whose LeanEuclid gives the one-rule form our present rule follows; to Sir Henry
Savile, through Heath, for the argument on a ray that carries I.4's coincidences; and to
Astra, whose third answer set out this design, the two observations it guards against, and
the evidence it asks for. We are grateful to them all.
