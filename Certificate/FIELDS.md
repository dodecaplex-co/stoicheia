# facts.json: the fields

`lake env lean Certificate/Facts.lean` writes `facts.json` from Lean's own environment.
`scripts/check_fidelity.py` checks it, `scripts/render.py` turns it into the pages, and
the review records (`review/SCHEMA.md`) are stamped from it. This page is the contract
between them. A field changes here first, and then in the code on both sides.

Brief 0005 (stage 1a-1c) adds porisms and companions as entries of their own, a printed
statement for every entry, and the axioms' exact statements. Every key that existed
before keeps its name and its form, and for the 99 propositions its meaning, except
where a cell below says otherwise.

## References

Every entry has a `ref`, written one way:

| Ref | Names | Lean declaration |
|---|---|---|
| `"I.15"` | the proposition | `Elements.BookI.Prop15` |
| `"I.15 Por."` | its porism | `Elements.BookI.Prop15.porism` |
| `"I.40 general"` | a companion theorem beside it (stage 2 on) | `Elements.BookI.Prop40.general` |

`heath.parse_ref` takes a reference apart into `(book, n, kind, name)`, and
`heath.prop_key` sorts references: by book, then number, then the proposition, its
porism, its companions. Heath's porisms are the paragraphs `heath.heath_porisms()` finds;
in Books I-III, I.15, III.1 and III.16.

## The top level

| Key | Type | Meaning |
|---|---|---|
| `lean_version` | string | The Lean that computed the certificate. |
| `propositions` | list of entries | One entry for every proposition, porism and companion (below). |
| `axiom_modules` | object, name to module | Every axiom this project declares, and every other axiom an entry rests on, with the module that declares it. Lean's `propext`, `Classical.choice`, `Quot.sound` and `sorryAx` are not listed. |
| `opaque` | list of names | Every `opaque` constant this project declares. |
| `axiom_types` | object, name to string | **New.** The printed statement of every axiom in `axiom_modules`, with exactly the same keys. 87 at commit d040117. |
| `vocabulary` | object, name to string | **New.** Every definition, instance, structure, inductive type and opaque of this project that the statement of an axiom, or of an entry, reaches (below). |
| `proved_rules` | object, name to list of names | **New** (20 October 2026). Every theorem this project declares in `Elements.Tacit`, found in Lean's environment, with the axioms `collectAxioms` finds beneath it. Names omit the leading `Elements.`; Lean's three foundations and `sorryAx` are left out, as in an entry's `axioms`. Each list is sorted by string. Each entry's own `proved_rules` (below) names those it rests on. |
| `proved_rule_cites` | object, name to list of refs | **New** (23 October 2026, [#294](https://github.com/jackChallis/stoicheia/issues/294)). For every theorem in `proved_rules`, with the same keys, the entries its proof cites, found by the walk that finds an entry's `cites`, as `["I.13"]` for `Tacit.inside_of_angle_add`: an entry whose proof uses a proved rule is found to cite every entry in the rule's list. Refs as an entry's `cites` writes them, each list sorted by string. `scripts/check_fidelity.py` accepts a forbidden circle rule missing from the lock as a theorem whose list holds `"III.2"`, with III.2 proved and resting on neither rule ([FORMALIZATION](../docs/FORMALIZATION.md), section 7, "Circle 2 and Circle 3"). |
| `construction_rules` | list of names | **New** (21 October 2026, [#150](https://github.com/jackChallis/stoicheia/issues/150)). The axioms in `axiom_modules` that are [construction rules](../docs/FORMALIZATION.md#construction-rules), found from Lean's statements of them (below). Sorted by string. |

Names here are Lean's full names without the leading `Elements.`, as `axiom_modules`
has always written them: `"Postulate1"`, `"Tacit.circle_eq"`, `"Magnitude.add"`.
`Certificate/axioms.lock` is compared with `axiom_types` and `vocabulary` in both
directions (stage 1c).

## Each entry

The entries come in three groups: the propositions of every book, in order; then the
porisms; then the companions, each group in `prop_key` order. Read an entry by its
`ref`, not its place.

| Key | Type | Meaning |
|---|---|---|
| `ref` | string | As above. |
| `name` | string | The declaration, without `Elements.`: `"BookIII.Prop1"`, `"BookIII.Prop1.porism"`. |
| `kind` | `"proposition"`, `"porism"` or `"companion"` | **New.** What the entry is. |
| `of` | string | **New**, on porisms and companions only: the parent's ref, `"III.1"`. A proposition has no `of`. |
| `attached` | list of refs | **New**, on propositions only: its porism, then its companions, in `prop_key` order; `[]` when it has none. |
| `status` | `"proved"`, `"proved-pending"` or `"sketched"` | `"sketched"` if a `sorry` is in the declaration's own proof (through its helpers and shared steps); `"proved-pending"` if it rests on one only through what it cites; `"proved"` otherwise. A proposition, as before, also takes its porism's: it is not finished until its porism is. A companion's status is its own, and changes no other entry's. |
| `cites` | list of refs | The entries the proof uses directly. **Changed**: a use of a porism is now recorded as the porism, `"III.1 Por."`, where it was recorded as `"III.1"`, and a use of a companion by its own ref. Sorted by string, as before. |
| `common_notions` | list of strings | Every Common Notion beneath the proof, through what it cites too: `"C.N. 1"` and so on. A walked local declaration's value that names `Elements.Superposition.Coincidence.step` records `"C.N. 4"`, the restricted calculus's coincidence step. |
| `axioms` | list of names | Lean's `collectAxioms` of this declaration alone, without Lean's three foundations and `sorryAx`. `Tacit.centre_unique` is now a theorem, proved in `Elements/Figure/Circles.lean` from circle intersections, equal radii (Definition I.15) and the order of lengths; where a proof rests on it, its list holds the axioms beneath it. The list follows each proof's dependencies; `tests/certificate_expectations.json` pins what III.1's and its porism's lists must hold. |
| `proved_rules` | list of names | **New** (26 October 2026, [#168](https://github.com/jackChallis/stoicheia/issues/168)). Every proved rule the entry rests on: each name of the top-level `proved_rules`, a tacit rule that is a theorem now, that its statement or its proof reaches, through what it cites, its Common Notions, its shared steps and the proved rules themselves, wherever `collectAxioms` goes. A proved rule leaves only its own axioms in `axioms`, never its name, so this list is where a use of one shows. Names omit `Elements.`; sorted by string. On 26 October 2026 III.1's held 24 names and III.3's 25, the one more being `Tacit.adjacent_eq_of_right`, I.13's corollary. Four pins of `tests/certificate_expectations.json` read it, since 26 October 2026: those of III.1, III.1 Por., III.2 and II.14, each excluding all eight tacit rules that the retirement of #119 made theorems (the stronger pins #168 calls for). The pins on those entries' `axioms` that exclude the same eight can no longer fail. `scripts/negative/retired_rule_used.py` plants a use of `Tacit.centre_unique` in III.2's proof, which leaves III.2's `axioms` and `cites` as they are, and of the expectations only the pin on III.2's `proved_rules` refuses it, beside III.2's review stamp, which any edit to the file trips. |
| `direct_axioms` | list of names | The axioms the proof uses itself, through its helpers and shared steps, but not through another entry it cites or a Common Notion: exactly `own_axioms` together with the keys of `inherited`, besides any of Lean's own foundations it lists (`propext`, in II.2, II.5, III.27, III.29 and III.30), which those two leave out, as `axioms` does. The policy on superposition reads it, so a proof may not reach that rule through a lemma either. |
| `own_axioms` | list of names | **New** (18 October 2026, [#65](https://github.com/jackChallis/stoicheia/issues/65)). The axioms the proof's own Lean names: in the declaration itself, in a helper written for its proposition (in the proposition's namespace: `Prop7.figure`; for a porism or companion, its proposition's, as `Prop1.middle` is III.1 Por.'s), or in Lean's auxiliary declarations for them; Lean's three foundations and `sorryAx` left out, as in `axioms`. Sorted by string. III.2's has 12 at commit 95b7491. Circle 2 (`Tacit.inside_of_between`) and Circle 3 (`Tacit.outside_of_between`) are not axioms: Circle 2 has been a theorem since 19 October 2026 and Circle 3 since 24 October, and both are now proved after III.2, in `Elements/BookIII/Prop02.lean`, from its corollary `Prop2.within`, so neither occurs in any entry's `axioms`, and a proof that used either would cite III.2 (`proved_rule_cites`, above). |
| `inherited` | object, name to list of objects | **New** (18 October 2026, #65). The rest of `direct_axioms`, Lean's foundations aside: each axiom the proof's own Lean does not name but reaches through a lemma it calls, of Book Zero (`Elements/Figure/`) or a shared step (`Prop5.base`, or another proposition's helper, as `Prop1.perpendicular` is for III.19), with each such lemma: `name`, `file`, `line`, as in `shared_steps`, sorted by name. An axiom the proof's own Lean names is in `own_axioms` alone, even when a lemma brings it in too. An excerpt from I.5's entry is `"Postulate3": [{"name": "exists_between_nearer", "file": "Elements/Figure/Circles.lean", …}]`: its own Lean draws no circle, and the lemma that keeps a point taken at random near enough does. A proposition it cites may bring the same axiom in as well, as I.3 brings Postulate 3 into I.5. |
| `lean_foundations` | list of names | Which of `propext`, `Classical.choice` and `Quot.sound` it rests on. |
| `shared_steps` | list of objects | The project's own lemmas outside the declaration's namespace that bring in at least one proposition: `name`, `brings_in` (refs), `file`, `line`. For a porism or companion, the parent's own helpers (`Prop1.middle`) count as its own, not as shared steps. A proved rule that the proof's own Lean calls is listed when it brings in a proposition, as Circle 2, Circle 3 and Intersection 2 bring in III.2, and `tests/certificate_expectations.json` pins that no entry lists any of those three (#429). Such a rule called only through another shared step is not listed: that step is, for what it brings in includes what the rule does. |
| `enunciation` | string | The declaration's docstring. For a proposition it is Heath's enunciation (check_fidelity insists on it); for a porism, our docstring, which quotes Heath's porism; for a companion, our docstring saying what it adds. |
| `statement` | string | **New.** The declaration's type, printed as below. Review records are fingerprinted from it (`heath.review_fingerprint`). |
| `cited_laws` | list of objects | **New** (21 October 2026, #150), only on an entry whose own declarations, as `own_axioms` reads them, name a law of `Elements.Superposition.Cited`: today I.4 and I.8. One object for each law they name, in the order of the `Cited` type: `law`, the constructor's name (`"lenSymm"`); `proofs`, the theorems that prove it, each stating exactly `Cited.Holds primitives` of that law (below): `name`, `file`, `line`, as in `shared_steps`, sorted by name; and `construction_rules`, every [construction rule](../docs/FORMALIZATION.md#construction-rules) that `collectAxioms` finds beneath any proof of that law the entry reaches (below), sorted by string. The laws are read from the constants the entry's own Lean names, not through `Derives.map`. A law named with no proof reached fails the run, since an empty list would read as a law proved with no construction rule. |

Every walk of a proof reads a declaration through `mentions`, and these walks give `cites`,
`direct_axioms`, `own_axioms`, `inherited`, `common_notions`, `shared_steps` and
`proved_rules`: `mentions` reads each declaration's type and value, opaque values
included, and an inductive type's constructors. For
`common_notions`, each local declaration visited is also checked for
`Elements.Superposition.Coincidence.step` named in its value. Like `#print axioms`, this
records what the proof term names, through the local declarations it names, without
evaluating it. Each of `Derives.len_congr`, `Derives.angle_congr` and `Derives.area_congr`
takes a first explicit argument of type `Coincidence`. A derivation taking the step
supplies `Coincidence.step` (`.step` and `⟨⟩` elaborate to that constant too). A transformer
such as `Derives.map` or `Derives.sound` that only passes a derivation's own marker along
as a bound variable adds no step. If a helper itself names the constant, it counts even
when evaluation would not take that branch. Merely reaching an inductive type's constructor
list counts neither its congruence constructors nor the marker. No transformer is skipped.

Every walk checks the declaring module of each constant it reaches, before stopping at
an entry, axiom, Common Notion or shared step. A declaration in `Elements` or a module
below it is local, as is a declaration in the emitter itself. Only declarations from
Lean's own modules may be treated as external leaves: modules under the roots `Init`,
`Std` and `Lean` whose `.olean`, as Lean's search path finds it for the import, lies in
the library directory of the running `lean`, both paths resolved. These are exactly the
roots, besides `Elements`, imported by the environment that Facts.lean loads with Lean
4.35. Any other reached module fails the certificate before it writes `facts.json`, with
a message naming the declaration and its module. The module comes from Lean's
environment, regardless of the declaration's namespace: a helper named
`Elements.Hidden.step` in `Staging.Hidden` is refused. Nor is a module's root evidence
of its origin: a separately compiled `Lean.Hidden` is refused too. This applies to
dependencies in types as well as values, and to the vocabulary walk. An imported helper
that no walk reaches does not fail the certificate.

`own_axioms` comes from the walk that gives `direct_axioms`, stopped at each lemma
the proof's own declarations call, as the walk for `shared_steps` is; what a lemma brings
in is found by the walk for `direct_axioms`, started from the lemma. Facts.lean checks
itself against Lean: each entry's `axioms` are exactly its `direct_axioms`, the axioms of
its Common Notions and the `axioms` of every entry in `cites`; and its `direct_axioms`,
Lean's foundations aside, are exactly its `own_axioms` and the keys of its `inherited`.
So its `axioms` are its own, those it inherits, its Common Notions' and those of what it
cites. `proved_rules` comes from a walk of its own, `beneath`, which reads through
`mentions` as the others do and goes wherever `collectAxioms` goes: through the entries
cited, the Common Notions, the shared steps and the proved rules, recording each axiom
and each proved rule it meets. Facts.lean checks that this walk finds exactly the
entry's `axioms`, so its proved rules are those of the walk that finds them. The Common
Notions named as theorems count even though `collectAxioms` cannot see them, and some
rest on tacit rules (C.N. 3 and C.N. 5 use `Tacit.add_lt_add_right`). The restricted
calculus's marked coincidence steps count as C.N. 4; equality substitution justifies
them, as it does the three `CommonNotion4` theorems. The marker adds no axiom and
changes no axiom field.

`construction_rules` reads statements, not proofs. For each axiom in `axiom_modules` it
takes the statement's conclusion and reads it as the definition of a construction rule
says, with its polarities: a definition of this project at the head of a term is unfolded
there, a `let` there is substituted into its body, and a projection of a structure that a
definition of this project gives (the `≤` of an instance, inherited through another
structure or not) is read through that definition. Everything else is a leaf that asserts
no existence: an opaque word, an axiom, a theorem, a constructor, a `match` or recursor
that is not reduced, Lean's own definitions, and every structure or inductive type but the
connectives the polarities read (`And`, `Or`, `Iff`, `Exists`), of this project or Lean's,
which is read as a word and never unfolded: its fields and constructors are not read.
That is why `Tacit.superposition`, whose statement is the structure `Superposition.Rule`,
is not a construction rule: the rule's one field assumes a triangle, and `Triangle`, the
negation of `Collinear`'s `∃`, assumed would put that `∃` in positive position if the
structure were unfolded. A statement read deeper than 1000 steps, an
unfolding counting as one, fails the run instead of being followed.

`cited_laws` walks twice. The walk for `own_axioms` gives the entry's own declarations,
whose `mentions` name the laws, and the lemmas they call on. A second walk from the entry,
through every declaration of this project and stopping at the other entries, finds every
proof of each law that the entry reaches. `proofs` lists the proofs the entry's own Lean
names directly, among its own declarations and the lemmas they call on, when there are any
and every proof reached lies beneath one of them; otherwise (when the entry's own Lean
names only a theorem that proves a list of laws, say) it lists every proof reached. Either
way the proofs listed have every proof reached beneath them, and `construction_rules` is
what `collectAxioms` finds beneath every proof reached: the run checks that the proofs
listed have exactly those construction rules beneath them, and fails if they ever differ.
The field reads theorems, not the term that discharges a law. A law discharged in place, by
a term that is not such a theorem, while such a theorem is reached elsewhere, would be shown
with that theorem's proofs and rules, not the term's. Each law I.4 and I.8 cite is
discharged by a theorem of its own.

## Printing a statement

`statement`, `axiom_types` and the types and values in `vocabulary` are printed by
`ppExpr` with these options, so that every name is written out and nothing hides behind
notation:

```lean
pp.notation false
pp.fullNames true
pp.funBinderTypes true
pp.fieldNotation false
pp.structureInstances false
format.width 100000
```

and then every run of whitespace is made one space, and the ends trimmed: one line each.

At commit d040117 this gives, for III.1's porism,

```text
∀ {A B C D G : Elements.Point} {ABC : Elements.Circle}, Elements.Centre G ABC → Elements.OnCircle A ABC → Elements.OnCircle B ABC → Elements.Between A D B → Eq (Elements.len A D) (Elements.len D B) → Not (Elements.Collinear A B C) → Eq (Elements.ang A D C) Elements.rightAngle → Elements.Collinear D C G
```

and for `axiom_types["Postulate1"]`,

```text
∀ (A B : Elements.Point), Ne A B → Exists fun (L : Elements.Line) => And (Elements.OnLine A L) (Elements.OnLine B L)
```

`heath.fingerprint` of III.16's statement followed by III.16 Por.'s is
`sha256:9fd59073303dbcdc`, and of I.40's `sha256:5ea666d96871b7f8`; an implementation
can be checked against these.

## The vocabulary

Start from the statements of the axioms in `axiom_modules` and the `statement` of every
entry: the propositions, the porisms and the companions. Take every constant they
mention; for each word found, every constant in its type; for a definition or instance,
also every constant in its value; and for an inductive type or structure, its
constructors; and go on until nothing new appears. Keep what this project declares, apart
from the axioms themselves (they are in `axiom_types`). Stop at Lean's own constants
(`Eq`, `Exists`, `HAdd.hAdd`), fixed by the toolchain, under `Init`, `Std` and `Lean`.
Refuse a reached declaration from any other module outside `Elements`, as above.

So the vocabulary holds the words the assumptions are stated in and the words the claims
are stated in. A word that only the entries' statements use, as `Touches`,
`EqualCircles`, `circumference`, `rect` or `Parallel`, appears in them by name alone, so a
change to what it means would leave the printed statements, and every review
fingerprint, as they were. The lock catches it instead: `Certificate/axioms.lock` holds
every word, and a changed word fails `check_fidelity.py` until the change is a decision.

Each value is `"<kind> : <type>"`, with `" := <value>"` after it for a `def` or
`instance`. The kinds are `def` (abbreviations and noncomputable definitions included),
`instance`, `theorem`, `opaque`, `inductive`, `structure` and `constructor`. An opaque's
value is not printed: that Lean cannot see it is the point. An inductive type's or a
structure's constructors are entries of their own.

At commit d040117 there were 37, all reached from the axioms; with the entries'
statements, from 17 October 2026, there are <!-- count:vocabulary -->263<!-- /count -->. Among them:

```text
"Collinear": "def : Elements.Point → Elements.Point → Elements.Point → Prop := fun (A B C : Elements.Point) => Exists fun (L : Elements.Line) => And (Elements.OnLine A L) (And (Elements.OnLine B L) (Elements.OnLine C L))"
"Kind.angle": "constructor : Elements.Kind"
"Magnitude": "def : Elements.Kind → Type := fun (k : Elements.Kind) => NonemptyType.type (Elements.MagnitudeImpl k)"
"Point": "opaque : Type"
"instAddMagnitude": "instance : {k : Elements.Kind} → Add (Elements.Magnitude k) := fun {k : Elements.Kind} => Add.mk Elements.Magnitude.add"
"sq": "def : Elements.Point → Elements.Point → Elements.Area := fun (A B : Elements.Point) => Elements.rect A B A B"
```

The instances matter even though the printed statements do not show them: `a + b` in an
axiom is `HAdd.hAdd a b`, and which addition it is lives in `instAddMagnitude`.

## What reads it

- `scripts/check_fidelity.py`: the policies, for every entry; that the porism entries are
  exactly Heath's porisms; that every attached entry of a complete book is proved; the
  axiom lock; the review stamps; and the facts pinned in
  `tests/certificate_expectations.json`, among them I.4's and I.8's `cited_laws`, the
  top-level `construction_rules`, every entry's `shared_steps`, read by each step's
  `name`, and the `proved_rules` of III.1, III.1 Por., III.2 and II.14.
- `scripts/render.py`: the pages, CERTIFICATE.md and GRAPH.md. A page's table splits
  what the proof uses itself by `own_axioms` and `inherited`, and its list of tacit
  rules marks each, with the lemmas an inherited rule comes in through; CERTIFICATE.md
  counts both. On I.4's and I.8's pages a table gives each law of `cited_laws`, its
  proofs, linked where Lean declares them, and the construction rules beneath them.
- `scripts/review_stamp.py` and `heath.review_fingerprint`: the review records' stamps.
