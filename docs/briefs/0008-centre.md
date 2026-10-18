# Brief 0008: every circle has a centre

*18 October 2026. A draft, revised after its challenge, for the coordinator to freeze. It
settles, before any proof work and as [WORKFLOW.md](../WORKFLOW.md), section 2, requires,
the rule the owner approved, that every circle has a centre, and every statement the rule
changes. Each new statement is written with `sorry` in the `Staging` library, in
`Staging/Centre/`, and checked by Lean against today's statement, given the rule's content.
Once approved the brief is frozen: others write against these statements, and a later
change is a revision of this brief (WORKFLOW, section 2, "Correcting a frozen brief"), never
a quiet edit. Nothing lands from it until issue #40 has landed and the brief is frozen; the
rule itself lands only in the coordinator's own pull request.*

*The challenge. The draft at `afe0ee9` was read by two challengers who did not write it:
Astra (GPT Pro, through Codex, read-only), which found no mathematical error in the 30
staged restatements and returned the draft for revision of its overlap display, the order in
which the construction's guard lands, its list of consumers and its plan for the formal
model; and a Claude challenger (Claude Opus 5.5), whose one blocking finding was that the
tag could not leave the records as planned. This revision answers every finding of both,
and Appendix B gives each, with its source and what was done. Warm thanks to both.*

*Brought up to main at `e04f318` (#79 to #86) on 18 October, for the freeze: brief 0007's
companions, now on main, are staged without their centre; the mixed-angle prototype's
theorem `exists_centre` is listed, with the pull request that renames it; the line
references are renewed and the prose list completed. Each open question of section 7 is
marked for the coordinator, who decides it at the freeze.*

Base: main at `f17b427`, merged with main at `e04f318`. `lake build Staging` passes there
with the files in `Staging/Centre/`: 33 statements with `sorry`, one definition, five proved
declarations (the construction of III.1; its circle-only entry point, from the staged III.1;
III.13's two clauses as lemmas, from the staged III.13; and `Centre.every`), and 73 checks.
Nothing in `Elements/` changes, so main's records, lock and CI are untouched.

The reading is Astra's. Asked by the owner, Astra answered three foundation questions at
`f17b427`, the first of them this one, with a precise account of what the rule adds, which
statements it changes and which it must leave alone; the answer is posted on
[issue #59](https://github.com/jackChallis/stoicheia/issues/59). This brief follows it
throughout, and owes it a great deal: warm thanks to Astra. The question itself came from
the fresh outside review (#47), which found the `centre-given` hypothesis across Book III.

## 1. The decision

Jack Challis decided on 18 October 2026, on issue #59 (the words below checked against his
comment there, on 18 October):

> **The owner's decision (18 October): approved, as Astra recommends.** `axiom exists_centre
> (α : Circle) : ∃ O, Centre O α`; III.1 keeps its construction-rich conclusion and drops the
> existence hypothesis, with a circle-only entry point for users; the statements that only
> assume a centre exists drop that hypothesis, those that name the centre keep it; III.1
> gains an overlap note for bare existence; its page says the foundations assume a centre and
> the proposition proves that Euclid's construction finds it. The order: #40 first (a new
> axiom needs the model's law names pinned as data), then a short brief with every statement
> changed, challenged and frozen, then the axiom with its lock entry, model law and decisions
> entry, then the restatements and their records.

On the same day he decided to start the formal model now (#73): in `model/`, a Lake package
of its own in this repository with a pinned Mathlib and its own CI job, the main library
staying plain Lean, its laws generated from the elaborated declarations with translation
checks, the hardest first. Section 2 says what that means for this rule.

Astra's words that the decision rests on:

- "This is a real addition to the present theory." A plane with one extra circle object,
  with the circumference and interior of an ordinary circle and no point its centre, keeps
  every one of the 87 laws: the rules that need a centre never apply to it, and `circle_eq`
  cannot identify it with an ordinary circle. That is Astra's hand argument, "not a
  completed Lean countermodel", and it shows that the rule does not follow from the others.
- "System E does allow a circle to be given without its centre being supplied." So the rule
  is ours, not System E's. Euclid's own definition gives every circle its centre (Definitions
  I.15 and I.16), and that is where its content comes from.
- "Uniqueness already has its own axiom": the rule asserts existence only, not `∃!`.
- III.1 "remains substantially stronger than `exists_centre`: it certifies the specified
  bisections and perpendicular chord." Its construction is to be kept apart from its
  correctness, "against a future shortcut through `Classical.choose`".
- "Do not mechanically delete existential centre clauses inside definitions such as
  `EqualCircles`: those witnesses participate in the radius comparison." And "removing centre
  existence does not resolve III.25's construction-input problem".

## 2. The rule

```lean
/-! ## The centre of a circle (ours)

Euclid's definitions give every circle a centre: in a circle "all the straight lines
falling upon it from one point among those lying within the figure are equal to one
another" (Definition I.15), "And the point is called the centre of the circle" (Definition
I.16). System E lets a circle be given without its centre, and reads III.1 as finding one
(Avigad, Dean and Mumma, 2009, §4.2), so this rule is ours. It says that a centre exists,
and no more: that there is only one is Generalities 2 (`centre_unique`), and III.1 finds
it by Euclid's construction. -/

/-- Every circle has a centre. A rule of our own, not one of System E's: its content is
Euclid's Definitions I.15 and I.16. -/
axiom exists_centre (α : Circle) : ∃ O : Point, Centre O α
```

- **Where.** `Elements/Foundations/Tacit/Constructions.lean`, in `Elements.Tacit`, under the
  heading above, after System E's Points rules, whose last three take a point on, inside and
  outside a circle; `centre_unique` and `centre_inside` (Generalities 2 and 3) are next door,
  in `Diagram.lean`. Its full name is `Elements.Tacit.exists_centre`, `Tacit.exists_centre`
  in the lock and the certificate, and every proposition file reaches it as `exists_centre`
  through its `open Tacit`, provided no declaration of `Elements` or of its proposition
  namespaces takes the same name (question 12). Question 1 weighs a home beside Definition
  15, as the challenge asked, and keeps this one; the opening note of `Definitions.lean`,
  which says that Definition 15 carries content, gains a sentence pointing to the rule, so
  that a reader who looks for it among the definitions finds it.
- **Its family.** The first tacit rule that is neither a rule of System E nor LeanEuclid's
  correction of one. The docstring says so without brackets, since the page's key to the
  list of tacit rules says that "the names in brackets are System E's"; the file's opening
  note gains a sentence saying that one rule in it is ours.
- **The lock.** One line joins `[axioms]`, which goes from 87 to 88; the vocabulary does not
  change, since `Circle`, `Point` and `Centre` are there already. As Lean prints it, checked
  against the printing of Points 7 in the lock:

  ```toml
  "Tacit.exists_centre" = "∀ (α : Elements.Circle), Exists fun (O : Elements.Point) => Elements.Centre O α"
  ```

  It is written by `python3 scripts/check_fidelity.py --write-lock`, never by hand, and
  `tests/model/lock.sha256` is renewed in the same change, with a comment line saying why.
- **The numerical model.** In the plane of [MODEL.md](../../tests/model/MODEL.md) a circle
  is a centre and a positive radius and `Centre A α` says that A is its centre, so the
  witness is the circle's own centre; the same holds in the hyperbolic plane. The law joins
  #40's `tests/model/laws.toml` under the lock's name, and the harness checks the witness as
  it checks Points 7: in `search.py`, `is_centre(centre(al), al)`; in `hyperbolic.py`, the
  same with `in_disc(centre(al))`. MODEL.md gains a row in "Taking points, and where lines
  and circles cross" (`exists_centre` | every circle has a centre | a circle of the plane is
  its centre and a radius; its centre is the witness), its counts from `run.py --full
  --write`, never inferred from the old totals, its 87 and 81 made 88 and 82, and, with
  thanks, Astra's argument that the law is independent of the other 87, as an informal
  countermodel argument. The rule has no guard, so no mutation goes with it.
- **The formal model.** On `lean/model-skeleton` (at `57f1454`; Astra read `40dfa3c`),
  `model/Model/Euclidean/Centre.lean` already proves the law, `⟨α.1.center, rfl⟩`, since a
  circle there is a sphere of positive radius, a subtype. Its translation, `Hand.exists_centre`
  in `model/Model/Hand.lean`, is by hand: nothing is generated yet, from the lock or from the
  declarations. What the rule's pull request does about the model depends on whether #73
  lands first (section 6, step 5).
- **The decisions entry,** in the pull request that adds the rule, quotes the owner's
  approval (section 1), says that the rule is ours and from Definitions I.15 and I.16, gives
  the counts (88 axioms, 82 tacit rules, the vocabulary unchanged), and names each protected
  file it changes, as [WORKFLOW.md](../WORKFLOW.md), section 10, requires.

## 3. III.1

`Staging/Centre/Prop01.lean`.

```lean
theorem Prop1.construction {A B : Point} {ABC : Circle} (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hAB : A ≠ B) :
    ∃ F C D E : Point, Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧
      OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ ∠ B D C = ∟ ∧ ¬ Collinear A B C ∧
      Between C F E ∧ ‖C F‖ = ‖F E‖

/-- To find the centre of a given circle. -/
theorem Prop1 {A B : Point} {ABC : Circle} (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hAB : A ≠ B) :
    ∃ F C D E : Point, Centre F ABC ∧ Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧
      OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ Between C F E ∧ ‖C F‖ = ‖F E‖

theorem Prop1.of_circle (ABC : Circle) :
    ∃ A B F C D E : Point, OnCircle A ABC ∧ OnCircle B ABC ∧ Centre F ABC ∧
      Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧ OnCircle E ABC ∧ Between C D E ∧
      ∠ A D C = ∟ ∧ Between C F E ∧ ‖C F‖ = ‖F E‖
```

- **The statement** is Astra's signature: today's, with `hABC : ∃ G, Centre G ABC` dropped
  and nothing else changed. A citer that passed `hABC` passes nothing.
- **The construction, apart.** `Prop1.construction` takes a circle and two points of it,
  and nothing else: no centre of the circle, and no rule that one exists. It returns
  Euclid's D, C, E and F, the right angles ADC and BDC, and that C is off AB, which the
  reductio uses; today's proof takes the same facts from the same steps. Its warrant is
  [FORMALIZATION.md](../FORMALIZATION.md), section 4, which keeps a construction core,
  receiving only the data the problem gives, apart from the correctness argument. It is not
  a helper in section 5's sense, which supplies a step Euclid takes for granted, since it
  carries three sentences he writes; and it hides no conclusion, since that F is the centre
  is argued in `Prop1`, under his sentences. So the record shows it as a `grouped` passage
  that names it, which the schema allows today (the page reads "Carried together, by
  `Prop1.construction`"). For the coordinator's approval (question 14), FORMALIZATION section
  5, "Helpers", gains one sentence, with step 3 of section 6, where the construction first
  lands: "A construction core kept apart under section 4, as III.1's `Prop1.construction`,
  carries Euclid's sentences of construction, not a step he takes for granted; the record
  shows it as a `grouped` passage naming it, and the proposition keeps the correctness
  argument under his sentences." It is proved in the staged file by today's construction
  steps, unchanged (question 13).
- **The correctness, with the rule.** In `Prop1`, the three sentences of the construction
  are carried by one call of `Prop1.construction`; "let G be the centre" takes
  `obtain ⟨G, hG⟩ := exists_centre ABC`; and Euclid's reductio follows under his sentences,
  as today, with the angle CDB right by construction. The staged file's first check proves
  the restated III.1 in exactly this way, from the construction, the rule's content as a
  hypothesis and today's reductio. Its axioms are today's III.1's exactly, 56 tacit rules
  (compared by Lean with today's `Prop1` at this revision); `Prop1.construction`'s are 54 of
  them, without `centre_unique` or `sorryAx`. With the rule, III.1's certificate has 57,
  still without `centre_unique`.
- **The guard Astra asks for** (question 7) is a new file, `Audit/Centre.lean`, imported by
  `Audit.lean`. It fixes the construction's type, a circle and two points of it in and
  Euclid's points out, and fails `lake build Audit` if `Tacit.exists_centre`,
  `Tacit.centre_unique` or `sorryAx` is among the construction's axioms, or if the
  construction is not declared. Tried at this revision against the staged construction, it
  passes; a planted `sorry` and a renamed construction each fail it.

  ```lean
  import Lean
  import Elements

  open Elements Elements.Tacit

  /- The construction of III.1 is given a circle and two points of it, and nothing more. -/
  example : ∀ {A B : Point} {ABC : Circle}, OnCircle A ABC → OnCircle B ABC → A ≠ B →
      ∃ F C D E : Point, Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧
        OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ ∠ B D C = ∟ ∧ ¬ Collinear A B C ∧
        Between C F E ∧ ‖C F‖ = ‖F E‖ :=
    @Elements.BookIII.Prop1.construction

  /- And it uses no rule that a circle has a centre, nor that it has only one, nor an
     admitted proof. -/
  open Lean Elab Command in
  #eval show CommandElabM Unit from do
    let n := `Elements.BookIII.Prop1.construction
    unless (← getEnv).contains n do throwError m!"`{n}` is not declared"
    let axs ← collectAxioms n
    let bad := [`Elements.Tacit.exists_centre, `Elements.Tacit.centre_unique, ``sorryAx].filter
      axs.contains
    unless bad.isEmpty do throwError m!"`{n}` rests on {bad}"
  ```

  It is a regression check, and shows no more than that: not that the steps are Euclid's,
  which the record's passage and its reviewer say, nor by itself that no other route to a
  centre exists, which Astra's informal countermodel argument says. It needs no renewal when
  Book I's proofs change, and lands on its own, after the construction and before the
  restatements (section 6).
- **The entry point for a circle alone.** `Prop1.of_circle` takes two points of the circle
  by Points 7 (`exists_point_on_circle`, the second avoiding the first) and runs III.1 on
  the straight line through them, as Euclid draws AB "through it at random". It returns A and
  B with III.1's points; `A ≠ B` follows from `Between A D B`, and is not repeated. It adds
  one rule to III.1's: Points 7, which III.1's closure lacks, so with the proofs above it
  rests on 58 tacit rules, against III.1's 57. It goes after the porism, as a lemma with no
  certificate entry, as brief 0007 settled for `Prop17.inside` (question 6); III.1's
  certificate therefore does not certify it, and its docstring says what it rests on. III.1's
  page names both ways to the centre, in the overlap note below: the rule, for bare
  existence; `Prop1.of_circle`, for Euclid's construction and its correctness from a circle
  alone. Neither is an executable algorithm (FORMALIZATION, section 4). In the staged file it
  is proved from the staged `Prop1`, so its closure there is provisional.
- **The porism** keeps its statement, which names its centre G. Its proof calls the
  restated `Prop1`, which drops `⟨G, hG⟩`, and keeps `centre_unique`, which identifies the F
  that III.1 finds with G. Its certificate gains the rule through III.1: 58 tacit rules.
- **The overlap note.** The record gains:

  ```toml
  [overlap]
  rule = "Tacit.exists_centre"
  kind = "step"
  note = "Our foundations assume that every circle has a centre (`exists_centre`, a rule of our own, from Definitions I.15 and I.16), and the rule supplies one step of Euclid's reductio, \"let G be the centre\". It asserts bare existence, and no more. The construction of F (`Prop1.construction`), which is given no centre of the circle and uses no rule that one exists, and the proof that F is that centre are III.1's own. For the centre of a circle given alone, `Prop1.of_circle` takes two points of it and runs Euclid's construction; for bare existence, cite the rule."
  ```

- **The line and the summary.** With `kind = "step"` (question 3), the line under the
  enunciation reads "one of our tacit rules supplies a step of it (see Overlap)", and Book
  III's summary, which also heads its index, its section of CERTIFICATE.md and its README
  row, says "In III.1 one of our tacit rules supplies a step of the proof, but does not
  contain the proposition". Without the key, `render.py` writes "already contains" in both
  places (`in_lean_line`, and `overlap_sentences` at `render.py:1179`, which Astra's probe
  showed ignores any such key today), which is exactly what Astra says must not be said of
  III.1.
- **The catalogue.** [overlaps.md](../reports/overlaps.md) gains the row "III.1's centre,
  in III.1" (rule `exists_centre`, ours; kind: supplies a step, the bare existence of the
  centre that the reductio supposes; first enters: III.1; audit: none, and the guard above
  shows that the construction does without the rule), and its opening says that one rule is
  ours.
- **The page text** is Astra's, word for word, in the mishnah's second paragraph, in place
  of its last sentence ("In our foundations too a circle has a centre only when a hypothesis
  gives one, …"), where it follows Heath's "unless we assume some point to be the centre":

  > Our foundations assume that every circle has a centre. This proposition proves that
  > Euclid's construction finds it: bisecting the perpendicular chord gives the centre F.
- **The record.** Its statement note becomes "Given a circle and two points A, B of it, the
  ends of the straight line Euclid draws through it at random, constructs D, C, E and F as
  Euclid does and proves that F is the centre. The porism names its centre G." Its
  `[representation]` goes, since `centre-given` was its only tag and the statement note now
  says the rest (section 4). It gains a first passage, at "Let a straight line AB be drawn
  through it at random", `kind = "grouped"`, `helper = "Prop1.construction"`, whose note
  says that one call carries Euclid's three sentences of construction, given the circle and
  A, B and no centre of it, and that the proof that F is the centre follows under his
  sentences. The passage on "But the angle FDB is also right" stands as it is, since the
  angle CDB is still right by construction; the porism's passage adds that it rests on the
  rule through III.1. `tests/certificate_expectations.json` moves with it, as values pinned
  to the edition: III.1 57, its `includes` gaining `Tacit.exists_centre`, and its porism
  58, each `why` saying so.

## 4. Every other statement that changes

**How the list was found.** Not by searching the text: a Lean script, run at `f17b427` on
the elaborated declarations of `Elements`, `Staging` and `Audit`, listed every hypothesis
of exactly the form `∃ x : Point, Centre x α`, every hypothesis `Centre E α` with E a
variable, with whether E occurs anywhere else in the statement, every conclusion and
definition with such an existential inside, and every declaration that cites one of the
statements changed. The branches `docs/brief-0007` and `lean/i45-ii14-full` were read
against main. Astra's count holds: of the 31 records tagged `centre-given`, 19 main
statements have an existence hypothesis and 12 name their centre and use it. Main has since
gained #79 to #86, read against this list at `e04f318`. Two of them bring consumers, and
the count of records stands: brief 0007's staged companions (#85), three of whose
statements take an existence hypothesis (below); and the mixed-angle prototype (#86), whose
theorem named `exists_centre` must be renamed before the rule lands (question 12), and six
of whose facts take a centre that nothing else in their statements mentions (section 6,
"Other branches"). The rest add no centre clause.

**The rule for each.** An existence hypothesis is dropped. A named centre that appears
elsewhere in the statement is kept: existence of some centre does not identify it. A named
centre that appears nowhere else in the statement is dropped, as an existence hypothesis in
substance; that is a reading of the owner's words by their substance, not their letter, set
out for approval in question 2. An existential inside a definition is kept where its witness
takes part in the definition, as in `EqualCircles`. The old statement of each is today's,
in its file; the new one is the same with the hypotheses named below removed, and is staged
in full, in `Staging/Centre/`, with two checks: given the rule's content, today's statement
gives the new one; and the new one gives today's. So, given the rule, each says exactly what
today's says, and each new proof is today's with the centre taken another way.

### The nineteen propositions, and their shared steps

Each drops the hypotheses named and nothing else, save III.34, whose circle becomes
explicit, `(ABC : Circle)`: its old hypothesis was the only input from which Lean could
infer the circle, which the conclusion also mentions. Where Heath's bracket gives III.1 for
the centre, the proof cites III.1, now without the hypothesis; where Euclid takes the centre
with no bracket, the proof takes the rule. Today's III.35 to III.37 cite III.1 with no
bracket (Heath, `heath/III/35.md`, `36.md` and `37.md`); under one rule they take the rule
too, and Book III's introduction loses its exception.

| Statement | Dropped | How the proof takes the centre, after |
|---|---|---|
| III.1 | `hABC : ∃ G, Centre G ABC` | section 3 |
| III.2 | `hABC : ∃ D, Centre D ABC` | III.1, under "[III. 1]" |
| III.4 | `hABCD : ∃ F, Centre F ABCD` | III.1, under "[III. 1]"; `hAC`, `hBD`, said of every centre, stay |
| III.8 | `hABC : ∃ M, Centre M ABC` | III.1, under "[III. 1]"; `hGA`, said of every centre, stays |
| III.9 | `hABC : ∃ O, Centre O ABC` | the rule, for the centre the porism to III.1 places |
| III.10 | `hABC`, `hDEF : ∃ P, Centre P …` | the rule, for each circle |
| III.13 | `hABDC`, `hEBFD`, `hACK` | the rule, in its step for touching within ("let the centre G … be taken", no bracket); passed on to III.2. Its two clauses also become lemmas (below) |
| III.17 | `hBCD : ∃ E, Centre E BCD` | `Prop1.of_circle`, under "[III. 1]" (question 8) |
| III.21 | `hABCD : ∃ F, Centre F ABCD` | the rule ("let the centre … be taken", no bracket) |
| III.22 | `hABCD : ∃ O, Centre O ABCD` | passed on to III.21: nothing to take |
| III.23 | `hACB`, `hADB : ∃ O, Centre O …` | passed on to III.10 and III.21 |
| III.24 | `hAEB`, `hCFD : ∃ O, Centre O …` | the rule, for each circle |
| III.25 | `hABC : ∃ E, Centre E ABC` | passed on to III.9; still handed the whole circle |
| III.30 | `hADB : ∃ O, Centre O ADB` | the rule |
| III.32 | `hABCD : ∃ O, Centre O ABCD` | the rule |
| III.34 | `hABC : ∃ O, Centre O ABC` | the rule; the circle explicit |
| III.35 | `hABCD : ∃ F, Centre F ABCD` | the rule (no bracket); today's call of III.1 goes |
| III.36 | `hABC : ∃ F, Centre F ABC` | the rule (no bracket), in each case; today's calls of III.1 go |
| III.37 | `hABC : ∃ F, Centre F ABC` | the rule (no bracket); today's call of III.1 goes, and III.17 and III.36 need nothing passed on |
| `Circumference.eq`, `.standing`, `.whole` | `hα : ∃ O, Centre O α` | passed on to III.21 and III.22 |

### For Lean users: three lemmas, for approval

Once III.13 loses its hypotheses, nothing names its three circles, and a citer of one clause
must name a circle the clause never mentions (`(ACK := α)`), as Astra and the Claude
challenger each reproduced in Lean. Conditions said of every centre, as III.4's and III.8's
are and stay, ask a citer who holds a named centre to go through `centre_unique`. Three
lemmas, each one line, take those burdens away; they are new statements, so they are
proposed here for approval (question 11), and are proved in `Staging/Centre/Restated.lean`:

```lean
theorem Prop13.internally {B D : Point} {α β : Circle}
    (h : TouchesInternally α β D ∨ TouchesInternally β α D) (hBα : OnCircle B α)
    (hBβ : OnCircle B β) : B = D

theorem Prop13.externally {A C : Point} {α β : Circle} (h : TouchesExternally α β A)
    (hCα : OnCircle C α) (hCβ : OnCircle C β) : C = A

theorem Centre.every {O : Point} {α : Circle} {p : Point → Prop}
    (hO : Centre O α) (h : p O) : ∀ F : Point, Centre F α → p F
```

The first two are III.13's clauses, each with only the two circles it speaks of, lemmas
after III.13 with no certificate entry, resting on what III.13 rests on; a check shows that
together they give III.13 back, which keeps its paired statement as Astra recommends. Making
III.13's circles explicit alone would not do: its points A and C, of the second clause only,
would still be left for a citer of the first. `Centre.every`, in Book Zero beside
`EqualCircles.refl` (`Elements/Figure/OnCircles.lean`), lets a citer holding `hO : Centre O
α` pass `hO.every h` for III.4's `hAC`; a check does exactly that against the restated III.4.

### Statements beyond the nineteen

| Statement | Where | Change |
|---|---|---|
| `EqualCircles.refl` | `Elements/Figure/OnCircles.lean` (Book Zero) | `(hG : Centre G α) (hP : OnCircle P α)`, which name nothing in the conclusion, go: `EqualCircles.refl (α : Circle) : EqualCircles α α`, from the rule and Points 7 (question 2) |
| III.33 | `Elements/BookIII/Prop33.lean` | the conclusion's clause `∃ O, Centre O AEB` goes; the circle and E stay (question 4) |
| `Circumference.add`, `Prop23.point`, III.24 restated, `Prop24.equalCircles`, `Prop25.of_circle` | brief 0006, `Staging/Stage3/`, `Stage4/` | each drops its existence hypotheses |
| `Prop25.complete` | brief 0006, `Staging/Stage4/Prop25.lean` | drops `hα : ∃ O, Centre O α`, and `hE : Centre E γ`, whose E names nothing else: any circle through A, B and C is α (question 2) |
| `Arc.Drawn` | brief 0006, `Staging/Stage3/Definitions.lean` | the clause "its circle has a centre" goes; it was there because `Prop23.point` needed one (question 5) |
| `Arc.eq_of_aligned`, `Arc.meets`, `Arc.measure_eq_iff`, `Arc.congruent_iff`, `Prop24.equalMeasure` | brief 0006, `Staging/Stage3/Aligned.lean`, `Chord.lean`, `Arcs.lean`, `Prop24.lean` | their text does not change, but their `Drawn` hypotheses ask less, so each statement says more; all are `sorry` today, and their proofs must not use the clause that goes |
| `Prop25.of_circle`'s proof | brief 0006, `Staging/Stage4/Prop25.lean:92` | `⟨hABC, hA, hC, hP⟩ : Arc.Drawn …` becomes `⟨hA, hC, hP⟩` |
| `Prop8.partner`, `Prop8.general` | brief 0007, `Staging/Stage4b/Prop08.lean` (#85) | drop `hABC : ∃ M, Centre M ABC`; `hGA` stays |
| `Prop17.general` | brief 0007, `Staging/Stage4b/Prop17.lean` (#85) | drops `hBCD : ∃ E, Centre E BCD`; its condition "not within" stays |
| the prototype's `exists_centre` | `Staging/Stage4b/MixedAngles.lean` (#86) | renamed, for instance `exists_circle_about`, with its fifteen uses; its statement, `∃ γ, Centre A γ`, does not change (question 12) |
| `Audit.III_2`, `Audit.III_24_measure` | `Audit/Overlaps.lean` | `III_2`'s type is III.2's, and its proof loses one argument; `III_24_measure` drops `hAEB`, `hCFD`, as III.24 does |

`lean/i45-ii14-full` (#80) adds no centre clause. Brief 0006's and brief 0007's statements
are frozen, so this is a revision of each, for the coordinator to approve with this brief,
made in their files by their owners, after the rule lands. Some of the changes are forced,
not chosen: brief 0006's staged checks show that `Prop24.equalCircles` and
`Prop25.of_circle` have today's III.24 and III.25, and brief 0007's that `Prop8.general`
and `Prop17.general` have today's III.8 and III.17; each check breaks the moment its
proposition loses its hypotheses, so each companion moves with its proposition.
`Staging/Centre/Brief0006.lean` and `Staging/Centre/Brief0007.lean` stage the two briefs'
new statements, and check that each pattern survives.

### The twelve that name their centre, and stay

III.3 (E), III.7 (E), III.11 (F, G), III.12 (F, G), III.14 (E), III.15 (E), III.16 (D),
III.18 (F), III.20 (E), III.26 (G, H), III.27 (G, H) and III.31 (E). Each named centre
occurs elsewhere in its statement: the straight line through it, the perpendiculars from it,
the angles at it. Their statements do not change. Nor do those of 22 helpers and porisms
that name a centre and use it (`Prop1.porism`, `Prop16.porism`, `Prop8.outside`,
`Prop8.within`, `Prop9.centre_on`, `Prop12.centre_outside`, `Prop15.half`, `Prop24.angle_type`,
`Prop28.beyond`, `Prop28.diameter`, `Prop29.size`, `Prop35.cut`, `Prop37.triangle`,
`Circumference.centre`, `.semicircle`, `.lt_semicircle`, `.gt_semicircle`,
`EqualCircles.radii`, `foot_between`, `ne_of_centre_of_on`, `outside_of_len_gt`,
`BookI.Prop22.meet`), nor of brief 0006's and brief 0007's staged statements that name one.
Nor does III.19's, which was never tagged: its conclusion, `∀ F, Centre F ABC → Collinear A
C F`, speaks of every centre through the anonymous binder of a universal, and the rule makes
it say something of the one there is.

Five of the twelve, and III.1's porism, come to rest on the rule through what they cite,
not through their statements, and their records say so: III.14 through its call of III.1
(`Prop1 ⟨E, hE⟩` becomes `Prop1`), whose centre `centre_unique` then identifies with E;
III.15 through III.14; III.26 and III.27 through `Circumference.eq`, `.standing` and `.whole`
(and with them `Audit.III_26_any` and `Audit.III_27_any`); III.31 through III.22; and the
porism through III.1. III.3, III.7, III.11, III.12, III.16, III.18 and III.20 do not reach
the rule, nor do III.5, III.6 and III.19.

### Records, Lean files and pages

- **The tag.** `centre-given` says that "a circle in Lean has a centre only when a
  hypothesis or Postulate 3 gives it one", which the rule makes false, so it leaves all 31
  records. A named centre is Euclid's own object and needs no tag, and the tag is not given
  a new meaning, since a tag marks a way our Lean differs from Euclid's words
  (`review/terms.toml`). The schema requires a tag in every `[representation]` (`heath.py`
  refuses an empty list), and that check stays as it is. In 19 records `centre-given` is the
  only tag, so each note's other content goes where it needs no tag, or keeps a tag that
  says what it is (question 9):

  | Records | Their note, beyond the centre | After |
  |---|---|---|
  | III.2, 4, 17, 21, 22, 32, 35, 36, 37 | nothing but the centre's coming with the circle, and what the proof does with it | the section goes |
  | III.1, 3, 7, 8, 15, 18, 20 | III.1's two points of the straight line drawn at random; III.3's CD through the centre, which is FE; how "nearer" is read in III.7 and III.15; III.8's convex and concave circumferences; III.18's F off DE; and the named centre, "given, as Euclid's setting-out takes it" (III.3, 7, 15, 18, 20) | the section goes, and these sentences join the record's statement note |
  | III.11, 12, 13 | touching read of the whole circles, and III.11's and III.12's named centres | the section stays, with a new tag, `touching-whole-circles`; III.13's note loses "Each circle comes with a centre" |

  The new tag is a representation, not a centre: "Circles touching one another are read of
  the whole circles: touching within, no point of the inner is outside the outer; touching
  without, no point is within both; so touching circles cross nowhere, the reading Heath
  reports as Todhunter's (III.6, III.11–III.13)." It gives FORMALIZATION section 3's row for
  circles touching the tag it lacks, and lands in `review/terms.toml` before any record uses
  it, in a pull request of its own (section 6). III.6, whose statement reads touching the
  same way, takes it too, from the owner of its record, once `lean/iii5-iii6-ending` or
  `lean/iii5-iii6-euclid` has landed. In the 12 records with other tags, `centre-given`
  leaves the list and the notes lose only what is false.
- **Records whose Lean changes, read again and stamped by their reviewer** (26): the
  nineteen; III.14, III.26, III.27, III.31 and III.33, which cite a changed statement or
  change themselves; and III.28 and III.29, which cite `Circumference.whole`.
- **Records whose Lean does not change** (8): III.3, III.7, III.11, III.12, III.15, III.16,
  III.18 and III.20. They lose the tag, and their notes move as the table says; no stamp goes
  stale, and a reviewer reads each change.
- **Notes that change,** beyond the representation notes above: the statement notes of III.1
  (section 3), III.21, III.22, III.32, III.34, III.35, III.36 and III.37, each of which loses
  "the circle comes with a centre"; III.25's hypothesis and short form, which become "the
  whole circle is given, not only the segment" and "handed the whole circle", keeping its
  scope, `restricted`, and its `segment-with-circle`; III.33's statement note, which loses
  "with its centre"; and III.10's passage note at "therefore the point P is the centre",
  whose "The statement gives ABC its centre" becomes "The rule gives ABC its centre". Only
  III.5, III.6 (until it takes the new tag) and III.19 are untouched.
- **Certificates.** With the proofs as above, 27 propositions and III.1's porism rest on the
  rule: III.1, 2, 4, 8, 9, 10, 13, 14, 15, 17, 21 to 37, read from the proof terms at
  `f17b427`. The pins of `Audit.III_26_any`, `Audit.III_27_any` and `Audit.III_24_measure`
  gain the rule.
- **Prose, and the scripts that describe the old setup,** by the pull request that changes
  each (section 6):
  - *With the rule:* [FORMALIZATION.md](../FORMALIZATION.md) section 7 (its count, and
    "each tacit rule from System E", which now has one exception) and section 9 (the two
    rows that say "87", better without a count, as "every axiom in the lock");
    [Book I's brief](book-I.md)
    ("81 tacit rules, from System E"); `CONTRIBUTING.md`, lines 53–54 ("new rules come from
    System E, or LeanEuclid's corrections of it", a policy that gains "or, by the owner's
    decision, a rule of our own, as `exists_centre`"); `README.md`, line 148 ("whose System E
    is the source of our tacit rules", of all but one) and `NOTICE`, line 11 (our tacit rules
    follow System E, save `exists_centre`, which is ours); the opening note of
    `Elements/Foundations/Definitions.lean` (section 2); MODEL.md and the harness (section
    2). `scripts/check_kernel.py` (#79) reads the lock, so nanoda admits the rule by its
    name with no change.
  - *With the restatements:* FORMALIZATION section 3 (the rows for a circle's centre, now
    "every circle has one, by our rule `exists_centre`; III.1 finds it", and for circles
    touching, now tagged) and section 4 ("a circle known to have one"); section 5's
    sentence of section 3 above, if approved, goes earlier, with step 3;
    [STYLE.md](../STYLE.md), line 232 (Book III's
    introduction "tells a circle's centre by hypothesis and III.1"); a dated note in
    [brief 0004](0004-book-III.md) on "Circles and their centres" (line 134) and its other
    mentions of a centre by hypothesis (lines 22, 152, 241, 265, 301, 327, 352 and the
    III.25 row at 371), pointing here;
    the mishnah of III.1 (section 3), of III.17 (line 5: "our statement names none. So we
    first find two", false once question 8 is adopted) and of III.34 (line 5: "our statement
    gives the circle its centre"); Book III's introduction, whose paragraph on "Let the
    centre of the circle ABC be taken" becomes one rule, Heath's bracket for III.1 and the
    rule otherwise, and whose count of statements "worded for our foundations" changes;
    [gaps-book-III.md](../reports/gaps-book-III.md), line 47 ("Our circles have a centre only
    when a hypothesis gives one"), line 149 (III.17's search for two points through the given
    centre, which question 8 removes) and line 243 (III.34's "our statement gives the circle
    its centre"); [overlaps.md](../reports/overlaps.md), its new row and
    opening, its sentence that "III.1 and III.25 take a centre from a hypothesis" (lines
    255–256), and its sweep of every rule (line 184, "We read each of the 81 tacit rules"),
    for which `Audit/screen.py` runs again, about ten minutes, with `Tacit.exists_centre`
    added to its list of rules about circles and the counts in its docstring and the
    report renewed; `Certificate/FIELDS.md`, the `axioms` row ("III.1's still has 56 tacit
    rules, and III.1 Por.'s has 57"); `tests/certificate_expectations.json`, values and `why`
    strings (section 3); and `scripts/scaffold_book.py`, lines 188–197 and its Book III
    signatures, which would scaffold the old interface. Brief 0006's "[axioms] stays at 87"
    (`docs/briefs/0006-statements.md`, lines 228 and 1674) and its tags for III.24 (line
    1279, `centre-given` among them); brief 0007's commentary on `Prop17.inside` ("for a
    circle with a centre", lines 291, 297, 326, 354 and 430 of
    `docs/briefs/0007-stage-4b.md`, and the module note and docstrings of
    `Staging/Stage4b/Prop17.lean`, lines 20, 32 and 48, though the lemma's statement needs no
    change) and its representation notes, which keep `centre-given` "as today" for III.7,
    III.8 and III.17 (lines 186, 275 and 354, against question 9): these change with those
    briefs' revisions, by their owners.
- **Generated pages,** regenerated by the integrator: 34 of Book III's pages, its
  introduction and scope row, CERTIFICATE.md and GRAPH.md.

## 5. What does not change, and why

- **III.25's construction input.** III.25 is still handed the whole circle, a straight line
  in it and a side, not the segment alone. Dropping the centre does not give it the segment;
  brief 0006's stage 4, whose core receives the segment only as a predicate on points, does.
- **`EqualCircles`.** Its witnesses, `∃ G H P Q, Centre G α ∧ Centre H β ∧ …`, are the
  radii it compares, not bare existence. So are `Arc.Less`, `Arc.Semicircle` and
  `Arc.Greater`, whose centre's side of the base is the definition.
- **Conditions said of every centre,** as in III.4 ("not through the centre") and III.8
  ("through the centre"): they stay, and with the rule they are never empty. `Centre.every`
  serves a citer who holds a named centre.
- **Conclusions that find or name a centre:** III.1's `Centre F ABC`, III.9's `Centre D ABC`,
  III.25's `Centre E ABC`, the restated III.25's `Centre E γ`, and III.5's and III.6's "not
  the same centre". Postulate 3 too, which gives a circle about a chosen centre.
- **`centre_unique`,** Generalities 2: the rule asserts existence only.
- **III.9's and III.10's `hypothesis-dropped`, III.24's and III.30's other tags,** and every
  restriction other than the centre.

## 6. The order of work

A check never lands in the pull request whose code it checks
([WORKFLOW.md](../WORKFLOW.md), section 10), so the guard of section 3 needs a pull request
between the construction it names and the restatement it guards. The order:

1. **First.** #40 lands (`tooling/model-law-names`, at `978dc04`): the model's law names as
   `tests/model/laws.toml`. It also takes the count out of `run.py`'s "87 at present" and
   `hyperbolic.py`'s "the other 86". Then, each in a pull request of its own, in any order:
   - `scripts/negative_tests.py` reads its count from the lock. It expects "declares 88
     axioms, not 87" when it plants one axiom, so the rule's pull request could not pass with
     origin/main's copy; #40 at `978dc04` does not change it.
   - `[overlap]`'s `kind = "step"`: `review/SCHEMA.md`, `heath.py` and both of `render.py`'s
     displays (question 3).
   - `review/terms.toml` gains `touching-whole-circles` (question 9).
   - **The prototype's rename,** before step 5 (question 12): a `lean` pull request of its
     own, from the owner of `Staging/Stage4b/MixedAngles.lean` (#86), renames its theorem
     `exists_centre (A : Point) : ∃ γ, Centre A γ`, in `Elements.MixedAngles`, for instance
     to `exists_circle_about`, with its fifteen uses in that file and the row of
     `docs/reports/mixed-angles-prototype.md` (line 231) that names it; nothing else
     changes. Within `Elements.MixedAngles`, which opens `Tacit`, the bare name means the
     prototype's theorem, so the rule could not be cited there as `exists_centre`; and were
     the theorem to reach `Elements/` under its name (#57 would move it to Book Zero), every
     proposition file's `exists_centre α` would resolve to it and fail. Both were tried in
     Lean on a small model of the two names.
2. **This brief,** challenged (Appendix B) and frozen by the coordinator, with brief 0006's
   and brief 0007's revisions and the three lemmas of section 4 if approved.
3. **III.1's construction, apart, under today's statement.** `Prop1.construction` goes before
   `Prop1` in `Elements/BookIII/Prop01.lean`, and today's `Prop1`, its hypothesis kept, calls
   it under Euclid's three sentences. No statement changes; III.1's record gains its
   `grouped` passage, and is read again and stamped; FORMALIZATION section 5 gains the
   sentence of section 3, if approved (question 14), so that the passage's warrant lands
   with it.
4. **The guard,** on its own: `Audit/Centre.lean`, imported by `Audit.lean`.
5. **The rule,** in one pull request, the coordinator's own: the axiom with its docstring;
   the lock (`--write-lock`); `tests/model/lock.sha256`; the law's line in `laws.toml` and the
   harness's two checks; MODEL.md; the prose of section 4 that goes with the rule; facts.json
   and the generated pages regenerated; and the decisions entry of section 2. Labels `lean`
   and `security-review`, with a `/security-review` recorded. Nothing uses the rule yet, so
   no certificate but the list of axioms changes. As for the formal model:
   - *If #73 has landed first,* this pull request also renews `model/lock.sha256` to the new
     lock, which the model's CI job compares, and adds `exists_centre`'s round-trip check to
     `model/Check/Hand.lean`, comparing the hand translation with the library's declaration,
     as `model/README.md` ("How the lock ties it") asks; `Model/Euclidean/Centre.lean`
     stands, and `Model/Hand.lean`'s note that the axiom is not yet in the library goes. The
     model package's owner writes those files, and the coordinator carries them in this one
     pull request, so that the lock and the model never disagree on main.
   - *If the rule lands first,* #73's package is built against the lock with the rule in it:
     its `lock.sha256` is that lock's, and its round-trip check of `exists_centre` is there
     from the start. Its owner is told when the rule lands.
6. **The restatements,** in one pull request, so that each record is read once: every
   statement of section 4, and III.1 of section 3, each moved from `Staging/Centre/` into its
   home; every citer's call; brief 0006's staged files and brief 0007's
   (`Staging/Stage4b/Prop08.lean` and `Prop17.lean`), or their homes in `Elements/` if they
   have moved by then;
   `Audit/Overlaps.lean` and its pins; the screen run again; the records, read again and
   stamped by their reviewers; the prose of section 4 that goes with the restatements;
   `tests/certificate_expectations.json`'s III.1 values, which move with the content;
   `Staging/Centre/` deleted; a decisions entry naming every statement changed, which the
   pre-flight's statement guard asks for, and each protected file changed
   (`Certificate/FIELDS.md`, `scripts/scaffold_book.py`); and the pages regenerated. Labels
   `lean` and `security-review`. Proofs by Codex sailors, best of two (WORKFLOW, section 5).
   Most are a line: a call loses an argument, or `obtain ⟨O, hO⟩ := h` becomes
   `obtain ⟨O, hO⟩ := exists_centre α`; III.1's correctness is the staged check, moved. The
   real work is III.17 through `Prop1.of_circle`.
7. **Afterwards,** `[tag.centre-given]` leaves `review/terms.toml`, in a pull request of its
   own, since that file is protected.

Steps 3 and 4 may come before or after step 5; steps 1, 3, 4 and 5 all come before step 6.
If a step needs a fact the axioms lack, work on it stops and the case goes to Jack, as for
every stage.

**Other branches.** `lean/iii5-iii6-ending` and `lean/iii5-iii6-euclid` rewrite
`Audit/Overlaps.lean`, `docs/reports/overlaps.md`, `review/III/02.toml` and `12.toml`, all
of which step 6 edits: step 6 starts from main after them, or merges them in, and the guard
has a file of its own so as not to meet them. `text/overlaps-i2-i3` (#81) and
`lean/i45-ii14-full` (#80) are on main, and the line references above are to main at
`e04f318`. `lean/model-skeleton` is #73 (step 5) and `tooling/model-law-names` is #40
(step 1). In the mixed-angle prototype (#86), besides the rename, six facts take a centre O
that nothing else in their statements mentions: `surrounds_inside`, `surrounds_outside`,
`near_across`, `Segment.exceeds_iff`, `Segment.nearVertexOpen` and `Segment.fallsShort_iff`.
Their proofs are complete and stay true as they stand; question 2's reading lets the centre
go when #57 moves them into `Elements/`: a note for #57. Brief 0006's stage 3 and stage 4
proofs are under way: their statements keep the hypotheses that go until step 6, and their
proofs should not use `Arc.Drawn`'s centre clause (question 5).

## 7. Open questions, for the freeze

Each question is the coordinator's to decide at the freeze, and is marked so; the
recommendation is the brief's. Astra's answer to the draft at `afe0ee9` took the same side
on questions 1 to 6, 8 and 10, and on question 9's removal of the tag; on question 7 it
endorsed the draft's pin of the whole list of axioms, which the revision replaced by a
targeted check on the Claude challenger's advice; and it asked for the lemmas of question
11. Questions 12 to 14 arose after the challenge.

1. **Where the rule sits.** *For the coordinator.* Recommended: `Tacit/Constructions.lean`, as
   `Tacit.exists_centre`, beside the other rules that a point exists. Weighed against a home
   beside Definition 15, as the challenge asked:
   - *For the definitions:* the rule's content is Euclid's Definition I.15, and a reader of a
     certificate would find it among the definitions taken as axioms, not among the tacit
     rules, which the README describes as "what Euclid reads off his figures without saying
     so".
   - *For the tacit rules:* System E already reads two facts of a circle's centre off the
     same definition, Generalities 2 and 3 (`centre_unique`, `centre_inside`), and counts them
     as tacit rules; Euclid's reductio supposes "let G be the centre" without saying why there
     is one, which is what a tacit rule records; the owner approved the name `exists_centre`
     as Astra wrote it, and Astra recommends this home; and every tool reads `Tacit.`
     already. On the other side, a name of the definitions' form such as `Definition16`
     would misname Definition I.16, which only names the centre, and a bare
     `Elements.exists_centre` would fall under "Other axioms" until the renderer, the
     harness's names and the counts were taught it.

   So the rule stays a tacit rule and says what it is (section 2), and the prose that calls
   every tacit rule System E's changes (section 4). The name goes into the lock, #40's
   `laws.toml`, facts.json and the expectations, so it is settled at the freeze.
2. **A named centre that nothing else mentions.** *For the coordinator.* `Prop25.complete`'s E and
   `EqualCircles.refl`'s G are named, but appear nowhere else in their statements.
   Recommended, as a rule for this brief and later ones: a named centre that appears nowhere
   else in the statement is dropped, since it asks only that a centre exist; one that
   appears anywhere else is kept. This reads the owner's "those that name the centre keep it"
   by its substance; by its letter the two would stay. `EqualCircles.refl`'s point P goes
   with it, by Points 7. The prototype's six facts of section 6 come under the same rule when
   #57 moves them. Since it reads the owner's words beyond their letter, the decisions entry
   states it as a rule, in those words.
3. **The line and the summary for III.1.** *For the coordinator.* Recommended: an optional key in `[overlap]`,
   `kind = "step"`, after the catalogue's "supplies a step", for a rule that carries one step
   of the proof and does not contain the proposition, written as section 3 says in both of
   `render.py`'s displays. `heath.py` accepts only that value and requires a `note` with it,
   and `review/SCHEMA.md` documents it. `render.py` has no tests of its own, so the pull
   request shows both displays from an in-memory III.1 record with the key, as Astra's probe
   did. It is a check change (`review/SCHEMA.md`, `scripts/`), landed first, on its own.
   III.1 alone takes it: I.7 and I.23, whose catalogue rows are also "supplies a step", keep
   "contains", since there the rule carries the proposition's content, in the catalogue's
   words, and their audit lemmas prove the propositions from the rules. The alternative is no
   `[overlap]` for III.1, the note in its statement row and the catalogue only.
4. **III.33's clause.** *For the coordinator.* Its conclusion says that the circle described has a centre, so that a
   citer could hand it on. Recommended: drop it, since it adds nothing once every circle has
   one; it is our clause, not Euclid's. Keeping it costs nothing but the question a reader
   would ask.
5. **`Arc.Drawn`.** *For the coordinator.* Recommended: its centre clause goes, in brief
   0006's file, before the definition joins the foundations if it has not yet, with its five
   users listed in section 4; after, it is a change of definition, with its lock entry and
   decisions entry. Either way the clause goes only once the rule is there to stand in for
   it, and the stage 3 proofs under way should not use it, so that its going breaks none.
6. **`Prop1.of_circle`, a lemma or a companion.** *For the coordinator.* Recommended: a lemma, after the porism,
   with no certificate entry, as for `Prop17.inside`: it generalizes no clause. III.1's
   overlap note makes it findable from the page, and section 3 gives its closure, 58 rules.
   A companion would show it on the page with its own certificate. The name is kept: as in
   Lean's `of_` names, it says what it is given, a circle, as brief 0006's `Prop25.of_circle`
   is given the circle rather than the segment. A distinct name, such as `Prop1.any_chord`,
   is the alternative if the coordinator prefers.
7. **The guard.** *For the coordinator.* Recommended: the targeted check of section 3, with the construction's
   type fixed beside it. A `#guard_msgs` pin of the construction's whole list of axioms (62
   names) would catch the same names, but must be renewed whenever a Book I proof beneath it
   changes, and a renewal could carry an added name in a long diff. A companion with a
   certificate expectation (`excludes`) is not open to us: a companion comes after its
   proposition, which may not cite it, and `Prop1` cites the construction. Keeping the
   construction inline, as today, reads more closely as Euclid, and leaves the separation to
   review alone.
8. **III.17.** *For the coordinator.* Recommended: its proof takes the centre by `Prop1.of_circle`, under Euclid's
   "[III. 1]", then draws EA and takes D on it, which removes today's search for two points
   through a given centre and its use of `centre_unique`. The smallest change takes the
   centre from the rule and keeps the search.
9. **The tag.** *For the coordinator.* Recommended: `centre-given` leaves all 31 records, and the 19 records in
   which it is the only tag are rehomed as section 4's table says, with a new tag,
   `touching-whole-circles`, for III.11–III.13. Rejected: keeping `centre-given` on the twelve
   that name a centre, with a new meaning, since a named centre is no difference from
   Euclid's words; and letting `[representation]` carry a note with no tag, which would
   weaken a schema check to let this change pass.
10. **One pull request or several, for the restatements.** *For the coordinator.*
    Recommended: one, after steps 1
    to 5. Each change is small, the citers of III.1, III.21 and III.22 run through most of
    Book III, and a record touched twice would be read twice.
11. **The three lemmas of section 4.** *For the coordinator.* Recommended: approve
    `Prop13.internally`, `Prop13.externally` and `Centre.every` with this brief, so that they
    land with the restatements and no Lean user ever passes `(ACK := α)`.
12. **The prototype's rename, and who makes it.** *For the coordinator.* Recommended: a
    `lean` pull request of its own, from the owner of `Staging/Stage4b/MixedAngles.lean`,
    landed before the rule (section 6, step 1), renaming the theorem to
    `exists_circle_about`, a name that says what it gives: a circle about A, by Postulate 3.
    The coordinator, who approved the prototype, approves the new name, with this brief or in
    that pull request, whichever comes first. The alternative is to carry the rename in the rule's own pull request, as step 5
    carries the model's files; a pull request of its own keeps the rule's to the rule, and
    lets #57 build on the new name at once.
13. **The proofs staged here.** *For the coordinator.* WORKFLOW section 2, "What proofs
    `Staging/` may hold", which reached main after this brief's base, has a staged
    statement's own proof wait for its brief's approval. Most proofs here are derivations,
    which it allows: the checks, `Prop1.of_circle` from the staged III.1, and III.13's two
    lemmas from the staged III.13, which Appendix A says prove nothing until their stubs are
    proved. Two are a statement's
    own: `Prop1.construction`, by today's construction steps, and `Centre.every`, from
    `centre_unique`. Recommended: the freeze approves them as staged facts resting on no
    stub, which the same section then lets stand, proved in place, until the steps that move
    them (steps 3 and 6). The alternative is to make both `sorry` until the freeze, at the
    cost of the first check of III.1 and the guard's trial, which use the construction.
14. **FORMALIZATION section 5's sentence.** *For the coordinator.* Recommended: approve the
    sentence of section 3 on a construction core kept apart, landed with step 3, so that the
    first `grouped` passage naming a construction has its warrant on main, and a later book's
    constructions can follow it. The alternative is III.1's record alone, citing
    FORMALIZATION section 4.

## Appendix A: what is staged, and why

The rule cannot be added before its pull request, so no staged statement can be proved from
it. Each new statement is staged with `sorry`, and the rule's content enters only as a
hypothesis of a check, named `exists_centre`, so that the same words refer to the rule once
it lands. Staging, rather than code blocks in this brief, is for the checks: they show that
each new statement is well formed, that it says what today's says given the rule, and so
that it needs no new mathematics, and, for III.1, that the construction and the correctness
fit. The checks of brief 0006's and brief 0007's statements show that the interfaces agree,
not that those statements are proved: several are `sorry` in those briefs themselves. The names sit in
`Elements.BookIII.Staging.Centre` (and `Elements.Staging.Centre` for Book Zero and the
definition), not `Elements.BookIII.Staging`, where brief 0006's restated III.24 and III.25
already are; `Centre.every` is declared at its future name, `Elements.Centre.every`, so that
the check can use it as `hO.every`. `Staging.lean`'s imports are the integrator's and are
left as they are; `lake build Staging` builds the folder by its glob.

Under WORKFLOW section 2, "What proofs `Staging/` may hold", most proofs here derive one
staged statement from others, and prove nothing until the stubs they rest on are proved:
the checks, `Prop1.of_circle` from the staged III.1, and `Prop13.internally` and
`Prop13.externally` from the staged III.13. Two are a statement's own and rest on no stub,
`Prop1.construction` and `Centre.every`; they stand on the freeze's approval (question 13).

| File | What it holds |
|---|---|
| `Staging/Centre/Prop01.lean` | `Prop1.construction`, proved, with the right angles ADC and BDC; III.1 restated; a check proving it from the construction and the rule's content; a check that today's III.1 follows; `Prop1.of_circle`, proved from the staged III.1 |
| `Staging/Centre/Restated.lean` | the other eighteen propositions, III.33, the three steps of `Circumferences.lean` and `EqualCircles.refl`, each with its two checks; `Prop13.internally` and `Prop13.externally`, proved from the staged III.13, with a check that they give it back; `Centre.every`, proved, with a check against the restated III.4 |
| `Staging/Centre/Brief0006.lean` | brief 0006's six statements and `Arc.Drawn` without the centre, with their checks, and the two checks that `Prop24.equalCircles` and `Prop25.of_circle` still have today's III.24 and III.25, restated |
| `Staging/Centre/Brief0007.lean` | brief 0007's three statements without the centre, `Prop8.partner`, `Prop8.general` and `Prop17.general`, with their checks, and the two checks that III.8 and III.17, restated, still follow from `Prop8.general` and `Prop17.general` |

## Appendix B: the challenge, finding by finding

Astra's answer to the draft at `afe0ee9`, with its bosun's triage, and the Claude
challenger's findings at the same commit. Every finding was checked against the repository
before it was applied.

| Finding | Source | What was done |
|---|---|---|
| `render.py` says "already contains the proposition" in the book's summary as well as under the enunciation; `kind = "step"` must reach both, the record block and the schema's validation | Astra (answers 5, 7; question 3), triage | Both displays named, with their wording (section 3, question 3); the key in the record block; `heath.py` accepts only "step" and requires a note; III.1 alone takes it |
| The guard sat beside the code it checks, against WORKFLOW section 10 | Astra (answers 2, 7), triage | Section 6, steps 3, 4 and 6: the construction under today's III.1, then the guard on its own, then the restatements |
| The guard reads axioms only: it shows neither the construction's algorithm nor its signature, nor rules out a shortcut through the existing axioms; keep semantic review | Astra (answer 2) | Section 3 says what it shows and what it leaves to review; the construction's type is now fixed beside it |
| A pin of 62 names breaks whenever Book I changes; a targeted check is firmer | Claude challenger (editorial) | Adopted, with the type fixed (section 3, question 7); tried against the staged construction, a planted `sorry` and a rename |
| "Uses no centre" is false: the construction's closure has `centre_inside` and `Definition15`, from Book I's circles | Astra (answer 2), Claude challenger (material) | Now "given no centre of the circle, and uses no rule that one exists", in the overlap note and throughout |
| Missing consumers: the `Arc.Drawn` users and `Stage4/Prop25.lean:92`; STYLE line 232; FORMALIZATION section 9; brief 0004 line 301; brief 0007's `Prop17.inside` commentary; `scaffold_book.py:188`; `hyperbolic.py:21` | Astra (answer 5), triage | All listed in section 4, save `hyperbolic.py`'s "the other 86", which #40 at `978dc04`, landing first, already removes (section 6, step 1) |
| Missing prose: CONTRIBUTING 53–54, the mishnah of III.17 and III.34, STYLE 232, `Certificate/FIELDS.md`, the expectations' `why`, README 148, NOTICE 11, brief 0006 lines 104 and 1242, overlaps.md 135 with the screen | Claude challenger (material) | All listed in section 4, by the pull request that changes each; the screen runs again with the rule among its rules about circles. Also found: overlaps.md lines 191–192 |
| The formal model: `Centre.lean` already proves the law, `⟨α.1.center, rfl⟩`, translated by hand, not "generated from the lock"; `model/lock.sha256` and `model/Check/Hand.lean`; what if #73 lands first | Astra (answer 6), triage | Section 2 corrected against the branch (now at `57f1454`); section 6, step 5, gives both orders and who writes what |
| Write question 2's reading down as a rule | Astra (answer 3), triage | Section 4 and question 2: a named centre that appears nowhere else in the statement is dropped |
| III.13 leaves a citer naming an unrelated circle; add projection lemmas now | Astra (answer 3), Claude challenger (material), triage | `Prop13.internally`, `Prop13.externally`, staged and proved, with a check; proposed for approval (question 11). Explicit circles alone would still leave A and C |
| `Prop1.of_circle` adds Points 7: 58 rules, not 57; "needs no other rule" was wrong | Astra (answer 4), triage | Section 3 corrected; its docstring says what it rests on |
| Make `of_circle` findable on III.1's page, with the two interfaces explained | Astra (answer 4) | In the overlap note: the rule for bare existence, `of_circle` for Euclid's construction |
| Retiring `centre-given` empties 19 records' only tag, which `heath.py` refuses, and loses notes readers need | Claude challenger (blocking) | Question 9 answered again, with section 4's table: notes rehomed, a new tag for touching circles, no schema weakened. The challenger counted 21 records; a count of the records gives 19 |
| `Prop1.construction` is no helper in FORMALIZATION section 5's or the schema's sense; cite section 4; the angle CDB | Claude challenger (material) | Section 3: section 4 is the warrant, the passage is `grouped`, and a sentence for section 5 is proposed. The construction now returns the angle BDC, so the reductio and the record's passage on it stay as today |
| Weigh the rule's home now, beside Definition 15 | Claude challenger (material) | Weighed in question 1; `Tacit/Constructions.lean` kept, for the reasons given there. The docstring drops its brackets so that the page's key stays true |
| III.19 does not name its centre: its centre is the binder of a universal | Claude challenger (editorial) | Corrected in section 4 |
| Say how the named-centre propositions come to rest on the rule; the porism's "as 'from this it is manifest' asks" | Claude challenger (editorial) | Section 4 names each route; the porism's sentence now says what `centre_unique` does |
| III.35–III.37 cite III.1 with no bracket in Heath; one rule would read more simply | Claude challenger (editorial) | Adopted: a bracket means III.1, none means the rule (section 4) |
| `Prop1.of_circle` and `Prop25.of_circle` use one suffix in two senses | Claude challenger (editorial) | Not adopted: each `of_` names what it is given, a circle, as Lean's `of_` names do; the alternative is in question 6 |
| Coordination with other branches, and the prototype's `surrounds_*` | Claude challenger (editorial) | Section 6, "Other branches" |
| The `Arc.Drawn` users; III.10's passage note | Claude challenger (editorial) | Both in section 4 |
| Conditions said of every centre burden a citer who holds a named centre | Claude challenger (editorial) | `Centre.every`, staged, proved and checked against III.4, proposed for approval; a docstring cannot carry the idiom, since a proposition's docstring is Heath's enunciation |
| The brief is long for "a short brief" | Claude challenger (editorial) | The decisions entry's draft and the model's detail are cut; what the challenge added stays |
| Astra could not fetch issue #59 | Astra (answer 6), triage | The owner's words were checked against his comment on issue #59 on 18 October (section 1) |
| The answer's links point to private paths | Triage | This brief cites repository paths only |
| Brief 0006's conversions show interfaces, not proofs; `of_circle`'s closure is provisional | Astra (answer 1) | Said in Appendix A and section 3 |
| `Audit/` lacks the protected-path treatment of `scripts/` and `tests/` | Astra (answer 5) | The guard is described as a regression check, and lands on its own; whether `Audit/` becomes protected is a policy question for the coordinator, outside this brief |
