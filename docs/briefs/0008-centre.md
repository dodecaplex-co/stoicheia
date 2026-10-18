# Brief 0008: every circle has a centre

*18 October 2026. A draft, for the coordinator to challenge and freeze. It settles, before
any proof work and as [WORKFLOW.md](../WORKFLOW.md), section 2, requires, the rule the owner
approved, that every circle has a centre, and every statement the rule changes. Each new
statement is written with `sorry` in the `Staging` library, in `Staging/Centre/`, and
checked by Lean against today's statement, given the rule's content. Once approved the brief
is frozen: others write against these statements, and a later change is a revision of this
brief (WORKFLOW, section 2, "Correcting a frozen brief"), never a quiet edit. Nothing lands
from it until issue #40 has landed and the brief is frozen; the rule itself lands only in
the coordinator's own pull request.*

Base: written on main at `f17b427`. `lake build Staging` passes with the new files in
`Staging/Centre/`: 30 statements with `sorry`, one definition, the construction of III.1
proved, its circle-only entry point proved from the staged III.1, and 63 checks. Nothing in
`Elements/` changes, so main's records, lock and CI are untouched.

The reading is Astra's. Asked by the owner, Astra answered three foundation questions at
`f17b427`, the first of them this one, with a precise account of what the rule adds, which
statements it changes and which it must leave alone; the answer is posted on
[issue #59](https://github.com/jackChallis/stoicheia/issues/59). This brief follows it
throughout, and owes it a great deal: warm thanks to Astra. The question itself came from
the fresh outside review (#47), which found the `centre-given` hypothesis across Book III.

## 1. The decision

Jack Challis decided on 18 October 2026, on issue #59:

> **The owner's decision (18 October): approved, as Astra recommends.** `axiom exists_centre
> (α : Circle) : ∃ O, Centre O α`; III.1 keeps its construction-rich conclusion and drops the
> existence hypothesis, with a circle-only entry point for users; the statements that only
> assume a centre exists drop that hypothesis, those that name the centre keep it; III.1
> gains an overlap note for bare existence; its page says the foundations assume a centre and
> the proposition proves that Euclid's construction finds it. The order: #40 first (a new
> axiom needs the model's law names pinned as data), then a short brief with every statement
> changed, challenged and frozen, then the axiom with its lock entry, model law and decisions
> entry, then the restatements and their records.

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
axiom exists_centre (α : Circle) : ∃ O : Point, Centre O α
```

- **Where.** `Elements/Foundations/Tacit/Constructions.lean`, in `Elements.Tacit`, under a
  heading of its own after System E's Points rules, whose last three take a point on, inside
  and outside a circle. It is a rule that a point exists, as those are; a reader looking for
  what is true of a circle finds the four together, with `centre_unique` and `centre_inside`
  (Generalities 2 and 3) next door, in `Diagram.lean`. Its full name is
  `Elements.Tacit.exists_centre`, `Tacit.exists_centre` in the lock and the certificate, and
  every proposition file reaches it as `exists_centre` through its `open Tacit`.
  (Question 1 asks whether it should sit beside Definition 15 instead.)
- **Its name and family.** Ours, not System E's: the first tacit rule that is neither a rule
  of System E nor LeanEuclid's correction of one. Its docstring says so and gives Euclid's
  definitions as its source; the file's opening note gains a sentence saying that one rule
  in it is ours:

  ```lean
  /-! ## The centre of a circle (ours)

  Euclid's definitions give every circle a centre: in a circle "all the straight lines
  falling upon it from one point among those lying within the figure are equal to one
  another" (Definition I.15), "And the point is called the centre of the circle" (Definition
  I.16). System E lets a circle be given without its centre, and reads III.1 as finding one
  (Avigad, Dean and Mumma, 2009, §4.2), so this rule is ours. It says that a centre exists,
  and no more: that there is only one is Generalities 2 (`centre_unique`), and III.1 finds
  it by Euclid's construction. -/

  /-- Every circle has a centre. (Ours: Definitions I.15 and I.16.) -/
  axiom exists_centre (α : Circle) : ∃ O : Point, Centre O α
  ```
- **The lock.** One line joins `[axioms]`, which goes from 87 to 88; the vocabulary does not
  change, since `Circle`, `Point` and `Centre` are there already. As Lean prints it, checked
  against the printing of Points 7 in the lock:

  ```toml
  "Tacit.exists_centre" = "∀ (α : Elements.Circle), Exists fun (O : Elements.Point) => Elements.Centre O α"
  ```

  It is written by `python3 scripts/check_fidelity.py --write-lock`, never by hand, and
  `tests/model/lock.sha256` is renewed in the same change, with a comment line saying why.
- **The model law, and why it holds.** In the plane of [MODEL.md](../../tests/model/MODEL.md)
  a circle is a circle of positive radius and `Centre A α` says that A is its centre, so the
  witness is the circle's own centre. The same holds in the hyperbolic plane. The law's name,
  `exists_centre`, joins the pinned data file of law names that #40 brings, and the harness
  checks the witness as it checks Points 7: in `search.py`, `is_centre(centre(al), al)`; in
  `hyperbolic.py`, the same with `in_disc(centre(al))`. MODEL.md gains a row in "Taking
  points, and where lines and circles cross" (`exists_centre` | every circle has a centre |
  a circle of the plane is its centre and a radius; its centre is the witness), its counts
  from `run.py --full --write`, its 87 and 81 made 88 and 82, and, with thanks, Astra's
  argument that the law is independent of the other 87. The rule has no guard, so no mutation
  goes with it. In the formal model of `model/` (#73), where a circle is a centre and a
  positive radius and `Centre A α` is `A = α.center`, the law is `⟨α.center, rfl⟩`: the
  easiest of them all, generated from the lock with the rest.
- **The decisions entry,** in the pull request that adds the rule, quoting the owner's
  approval above and naming each protected file it changes (`Certificate/axioms.lock`,
  `tests/model/lock.sha256`, `tests/model/MODEL.md`, the harness files and #40's data file),
  as [WORKFLOW.md](../WORKFLOW.md), section 10, requires. A draft:

  > **Every circle has a centre: a rule of our own.** The owner approved it on 18 October
  > 2026, on issue #59, as Astra recommended: "[the owner's words, as in section 1]". The rule
  > `Tacit.exists_centre`, that every circle has a centre, joins
  > `Elements/Foundations/Tacit/Constructions.lean` and the axiom lock (88 axioms; the
  > vocabulary unchanged). Its content is Euclid's Definitions I.15 and I.16; System E does
  > not have it. The model checks it in the plane and in the hyperbolic plane. Nothing uses
  > it yet: brief 0008's restatements follow, in a pull request of their own.

## 3. III.1

`Staging/Centre/Prop01.lean`.

```lean
theorem Prop1.construction {A B : Point} {ABC : Circle} (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hAB : A ≠ B) :
    ∃ F C D E : Point, Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧
      OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ ¬ Collinear A B C ∧
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
  and nothing else: no centre, and no rule that one exists. It returns Euclid's D, C, E and
  F, and that C is off AB, which the reductio uses and today's proof takes from the
  construction too. It is a helper before `Prop1`, and is proved in the staged file by
  today's construction steps, unchanged.
- **The correctness, with the rule.** In `Prop1`, the three sentences of the construction
  are carried by one call of `Prop1.construction` (a `helper` passage in the record); "let G
  be the centre" takes `obtain ⟨G, hG⟩ := exists_centre ABC`; and Euclid's reductio follows
  under his sentences, as today. The staged file's first check proves the restated III.1 in
  exactly this way, from the construction, the rule's content as a hypothesis and today's
  reductio, run on the construction's output alone. Its axioms, compared with facts.json at
  `f17b427`, are III.1's of today, all 56 tacit rules and no other; with the rule, III.1's
  certificate has 57, still without `centre_unique`.
- **The protection Astra asks for.** That the construction uses no centre is then a fact
  about one declaration. When it lands, `Audit/Overlaps.lean` pins the axioms of
  `Prop1.construction` with `#guard_msgs`, as it pins its audit lemmas, so that the rule
  appearing there would fail `lake build Audit` (question 7).
- **The entry point for a circle alone.** `Prop1.of_circle` takes two points of the circle
  by Points 7 (`exists_point_on_circle`, the second avoiding the first) and runs III.1 on the
  straight line through them, as Euclid draws AB "through it at random". It needs no other
  rule, and is proved in the staged file from the staged `Prop1`. It returns A and B with
  III.1's points; `A ≠ B` follows from `Between A D B`, and is not repeated. It goes after
  the porism, as a lemma beside III.1, with no certificate entry, as brief 0007 settled for
  `Prop17.inside` (question 6). For bare existence, a user cites the rule itself.
- **The porism** keeps its statement, which names its centre G. Its proof calls the
  restated `Prop1`, which drops `⟨G, hG⟩`, and keeps `centre_unique`, as "from this it is
  manifest" asks. Its certificate gains the rule through III.1: 58 tacit rules.
- **The overlap note.** The record gains:

  ```toml
  [overlap]
  rule = "Tacit.exists_centre"
  note = "Our foundations assume that every circle has a centre (`exists_centre`), which supplies the step Euclid's reductio supposes, \"let G be the centre\". The rule asserts bare existence only. The construction of F, which uses no centre (`Prop1.construction`), and the proof that F is the centre are III.1's own."
  ```

  The overlap catalogue, [overlaps.md](../reports/overlaps.md), gains the row "III.1's
  centre, in III.1" (rule `exists_centre`, ours; kind: supplies a step, the bare existence of
  the centre; first enters: III.1; audit: the pin above), and its opening says that one rule
  is ours. As `render.py` stands, any `[overlap]` makes the line under the enunciation say
  "one of our tacit rules already contains it", which is exactly what Astra says must not be
  said of III.1; question 3 proposes the fix, and it lands first.
- **The page text** is Astra's, word for word, in the mishnah's second paragraph, in place
  of its last sentence ("In our foundations too a circle has a centre only when a hypothesis
  gives one, …"), where it follows Heath's "unless we assume some point to be the centre":

  > Our foundations assume that every circle has a centre. This proposition proves that
  > Euclid's construction finds it: bisecting the perpendicular chord gives the centre F.
- **The record** loses `centre-given`; its statement note becomes "Given a circle and two
  points A, B of it, constructs D, C, E and F as Euclid does and proves that F is the
  centre"; its representation note keeps only the two points of the straight line drawn at
  random; the porism's passage adds that it rests on the rule through III.1; and
  `tests/certificate_expectations.json` moves with it, as values pinned to the edition: III.1
  57 and its porism 58, and III.1's `includes` gains `Tacit.exists_centre`.

## 4. Every other statement that changes

**How the list was found.** Not by searching the text: a Lean script, run at `f17b427` on
the elaborated declarations of `Elements`, `Staging` and `Audit`, listed every hypothesis
of exactly the form `∃ x : Point, Centre x α`, every hypothesis `Centre E α` with E a
variable, with whether E occurs anywhere else in the statement, every conclusion and
definition with such an existential inside, and every declaration that cites one of the
statements changed. The branches `docs/brief-0007` and `lean/i45-ii14-full` were read
against main. Astra's count holds: of the 31 records tagged `centre-given`, 19 main
statements have an existence hypothesis and 12 name their centre and use it.

**The rule for each.** An existence hypothesis is dropped. A named centre that the statement
uses is kept: existence of some centre does not identify E. A named centre that nothing else
in the statement mentions is an existence hypothesis in substance, and is dropped with it
(question 2). An existential inside a definition is kept where its witness takes part in the
definition, as in `EqualCircles`. The old statement of each is today's, in its file; the new
one is the same with the hypotheses named below removed, and is staged in full, in
`Staging/Centre/`, with two checks: given the rule's content, today's statement gives the
new one; and the new one gives today's. So, given the rule, each says exactly what today's
says, and each new proof is today's with the centre taken another way.

### The nineteen propositions, and their shared steps

Each drops the hypotheses named and nothing else, save III.34, whose circle becomes
explicit, `(ABC : Circle)`, since that hypothesis was all that named it. Where Euclid takes
the centre by III.1, the proof keeps citing III.1, now without the hypothesis; where he
takes it with no bracket and today's proof unpacks the hypothesis, it takes the rule.

| Statement | Dropped | How the proof takes the centre, after |
|---|---|---|
| III.1 | `hABC : ∃ G, Centre G ABC` | section 3 |
| III.2 | `hABC : ∃ D, Centre D ABC` | III.1, under "[III. 1]" |
| III.4 | `hABCD : ∃ F, Centre F ABCD` | III.1, under "[III. 1]"; `hAC`, `hBD`, said of every centre, stay |
| III.8 | `hABC : ∃ M, Centre M ABC` | III.1, under "[III. 1]"; `hGA`, said of every centre, stays |
| III.9 | `hABC : ∃ O, Centre O ABC` | the rule, for the centre the porism to III.1 places |
| III.10 | `hABC`, `hDEF : ∃ P, Centre P …` | the rule, for each circle |
| III.13 | `hABDC`, `hEBFD`, `hACK` | the rule, in its step for touching within ("let the centre G … be taken", no bracket); passed on to III.2 |
| III.17 | `hBCD : ∃ E, Centre E BCD` | `Prop1.of_circle`, under "[III. 1]" (question 8) |
| III.21 | `hABCD : ∃ F, Centre F ABCD` | the rule ("let the centre … be taken", no bracket) |
| III.22 | `hABCD : ∃ O, Centre O ABCD` | passed on to III.21: nothing to take |
| III.23 | `hACB`, `hADB : ∃ O, Centre O …` | passed on to III.10 and III.21 |
| III.24 | `hAEB`, `hCFD : ∃ O, Centre O …` | the rule, for each circle |
| III.25 | `hABC : ∃ E, Centre E ABC` | passed on to III.9; still handed the whole circle |
| III.30 | `hADB : ∃ O, Centre O ADB` | the rule |
| III.32 | `hABCD : ∃ O, Centre O ABCD` | the rule |
| III.34 | `hABC : ∃ O, Centre O ABC` | the rule; the circle explicit |
| III.35 | `hABCD : ∃ F, Centre F ABCD` | III.1, as today |
| III.36 | `hABC : ∃ F, Centre F ABC` | III.1, as today, in each case |
| III.37 | `hABC : ∃ F, Centre F ABC` | III.1, as today; passed on to III.17 and III.36 |
| `Circumference.eq`, `.standing`, `.whole` | `hα : ∃ O, Centre O α` | passed on to III.21 and III.22 |

III.13 is left with no explicit argument, and its first clause, used alone, needs its third
circle named, as its points A and C already do today; reshaping its two clauses is outside
this brief.

### Statements beyond the nineteen

| Statement | Where | Change |
|---|---|---|
| `EqualCircles.refl` | `Elements/Figure/OnCircles.lean` (Book Zero) | `(hG : Centre G α) (hP : OnCircle P α)`, which name nothing in the conclusion, go: `EqualCircles.refl (α : Circle) : EqualCircles α α`, from the rule and Points 7 (question 2) |
| III.33 | `Elements/BookIII/Prop33.lean` | the conclusion's clause `∃ O, Centre O AEB` goes; the circle and E stay (question 4) |
| `Circumference.add`, `Prop23.point`, III.24 restated, `Prop24.equalCircles`, `Prop25.of_circle` | brief 0006, `Staging/Stage3/`, `Stage4/` | each drops its existence hypotheses |
| `Prop25.complete` | brief 0006, `Staging/Stage4/Prop25.lean` | drops `hα : ∃ O, Centre O α`, and `hE : Centre E γ`, whose E names nothing else: any circle through A, B and C is α (question 2) |
| `Arc.Drawn` | brief 0006, `Staging/Stage3/Definitions.lean` | the clause "its circle has a centre" goes; it was there because `Prop23.point` needed one (question 5) |
| `Prop8.partner`, `Prop8.general` | brief 0007, branch `docs/brief-0007` | drop `hABC : ∃ M, Centre M ABC`; `hGA` stays |
| `Prop17.general` | brief 0007, branch `docs/brief-0007` | drops `hBCD : ∃ E, Centre E BCD`; its condition "not within" stays |
| `Audit.III_2`, `Audit.III_24_measure` | `Audit/Overlaps.lean` | `III_2`'s type is III.2's, and its proof loses one argument; `III_24_measure` drops `hAEB`, `hCFD`, as III.24 does |

`lean/i45-ii14-full` adds no centre clause. Brief 0006's and brief 0007's statements are
frozen, so this is a revision of each, for the coordinator to approve with this brief, made
in their files by their owners, after the rule lands. Two of brief 0006's changes are forced,
not chosen: its staged checks show that `Prop24.equalCircles` and `Prop25.of_circle` have
today's III.24 and III.25, and they break the moment those lose their hypotheses, so the
four move together. `Staging/Centre/Brief0006.lean` stages brief 0006's new statements, and
checks that the pattern survives. Brief 0007's companions are not staged here, since they
are not on main; if they land first, their checks of today's III.8 and III.17 force the same.

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
`BookI.Prop22.meet`), of III.19 (F), which names its centre and was never tagged, and of
brief 0006's and brief 0007's staged statements that name one.

### Records, Lean files and pages

- **The tag.** `centre-given` says that "a circle in Lean has a centre only when a
  hypothesis or Postulate 3 gives it one", which the rule makes false. It leaves all 31
  records; a named centre is Euclid's own object, and needs no tag (question 9). Its entry in
  `review/terms.toml` goes afterwards, in a pull request of its own, since that file is
  protected.
- **Records whose Lean changes, read again and stamped by their reviewer** (26): the
  nineteen; III.14, III.26, III.27, III.31 and III.33, which cite a changed statement or
  change themselves; and III.28 and III.29, which cite `Circumference.whole`.
- **Records whose Lean does not change** (8): III.3, III.7, III.11, III.12, III.15, III.16,
  III.18 and III.20, which lose the tag only. Their notes ("The centre E is given, as
  Euclid's setting-out takes it") stay true.
- **Notes that change.** Each mention of a circle's coming with a centre goes from the notes of
  III.2, III.4, III.8, III.9, III.10, III.13, III.17, III.21, III.22, III.23, III.24, III.30, III.32
  and III.34 to III.37. III.25 keeps its scope, `restricted`, and its `segment-with-circle`: its
  hypothesis becomes "the whole circle is given, not only the segment", its short form "handed the
  whole circle". III.33's notes lose "with its centre". III.1's are in section 3. Only III.5, III.6
  and III.19 are untouched.
- **Certificates.** With the proofs as above, 27 propositions and III.1's porism rest on the
  rule: III.1, 2, 4, 8, 9, 10, 13, 14, 15, 17, 21 to 37, read from the proof terms at
  `f17b427`. III.3, 5, 6, 7, 11, 12, 16, 18, 19 and 20 do not. The pins of `Audit.III_26_any`,
  `Audit.III_27_any` and `Audit.III_24_measure` gain the rule.
- **Prose.** [FORMALIZATION.md](../FORMALIZATION.md): section 3's row for a circle's centre,
  section 4's "a circle known to have one", section 7's count and "each tacit rule from
  System E". [Brief 0004](0004-book-III.md): a dated note on "Circles and their centres",
  pointing here. The mishnah of III.1 (section 3) and Book III's introduction, whose
  paragraph on "Let the centre of the circle ABC be taken" and whose count of statements
  "worded for our foundations" change. [gaps-book-III.md](../reports/gaps-book-III.md)'s
  "Our circles have a centre only when a hypothesis gives one". MODEL.md (section 2).
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
  ("through the centre"): they stay, and with the rule they are never empty.
- **Conclusions that find or name a centre:** III.1's `Centre F ABC`, III.9's `Centre D ABC`,
  III.25's `Centre E ABC`, the restated III.25's `Centre E γ`, and III.5's and III.6's "not
  the same centre". Postulate 3 too, which gives a circle about a chosen centre.
- **`centre_unique`,** Generalities 2: the rule asserts existence only.
- **III.9's and III.10's `hypothesis-dropped`, III.24's and III.30's other tags,** and every
  restriction other than the centre.

## 6. The order of work

1. **Before the rule.** #40 lands: the model's law names as a pinned data file. Three
   smaller things come first too:
   - `scripts/negative_tests.py` expects the words "declares 88 axioms, not 87" when it
     plants one axiom. With the rule the message reads "89 … 88", so the pull request adding
     the rule could not pass: origin/main's copy fails on it, and changing the copy there is
     a check change kept apart. The count is read from the lock instead, in a pull request of
     its own, unless #40 covers it.
   - The fix for the line under III.1's enunciation (question 3), with its schema key, in a
     pull request of its own.
   - The branch `lean/mixed-angle-prototype` declares `exists_centre (A : Point) : ∃ γ,
     Centre A γ` in `Elements.MixedAngles`, which opens `Tacit`; it is renamed there (for
     instance `exists_circle_about`) before the rule lands, so that the two never meet.
2. **This brief** is challenged by readers who did not write it, and frozen by the
   coordinator, with brief 0006's and brief 0007's revisions.
3. **The rule,** in one pull request, the coordinator's own: the axiom with its docstring; the
   lock (`--write-lock`); `lock.sha256`; the law name in #40's data file and the harness's two
   checks, with `run.py`'s "87 at present"; MODEL.md; FORMALIZATION, section 7, and
   [Book I's brief](book-I.md)'s "81 tacit rules, from System E"; facts.json and the generated
   pages regenerated; and the decisions entry of section 2, quoting the owner's approval and
   naming each protected file. Labels `lean` and `security-review`, with a `/security-review`
   recorded. Nothing uses the rule yet, so no certificate but the list of axioms changes.
4. **The restatements,** in one pull request, so that each record is read once: every
   statement of section 4, and III.1 of section 3, each moved from `Staging/Centre/` into
   its home; every citer's call; brief 0006's staged files (and brief 0007's, if landed);
   `Audit/Overlaps.lean`, its pins and the new pin of `Prop1.construction`;
   `tests/certificate_expectations.json`'s III.1 values, which move with the content;
   `Staging/Centre/` deleted; a decisions entry naming every statement changed, which the
   pre-flight's statement guard asks for; the records, read again and stamped by their
   reviewers; the prose of section 4; and the pages regenerated. Proofs by Codex sailors,
   best of two (WORKFLOW, section 5). Most are a line: a call loses an argument, or
   `obtain ⟨O, hO⟩ := h` becomes `obtain ⟨O, hO⟩ := exists_centre α`. The real work is
   III.1's construction and correctness, whose staged proofs are a starting point, and III.17
   through `Prop1.of_circle`.
5. **Afterwards,** `[tag.centre-given]` leaves `review/terms.toml`.

If a step needs a fact the axioms lack, work on it stops and the case goes to Jack, as for
every stage.

## 7. Open questions, for the challenge

1. **Where the rule sits.** Recommended: `Tacit/Constructions.lean`, as
   `Tacit.exists_centre`, beside the other rules that a point exists. Every tool already
   reads the `Tacit.` prefix (the model's names, the certificate's count of tacit rules, the
   page's family of rules), and a Lean user finds it with `centre_unique` in `Elements.Tacit`.
   The alternative is `Definitions.lean`, beside Definition 15, as the rest of Euclid's
   definition: truer to its source, at the cost of teaching the harness, the renderer and the
   counts a name outside `Tacit`.
2. **A named centre that nothing else mentions.** `Prop25.complete`'s E and
   `EqualCircles.refl`'s G name a centre used nowhere else in the statement. Recommended:
   drop them, reading the owner's rule by its substance, since each asks only that a centre
   exist. By the letter ("those that name the centre keep it") they would stay.
3. **The line under III.1's enunciation.** `render.py` writes "one of our tacit rules already
   contains it" for any `[overlap]`, and would say it of III.1. Recommended: an optional key
   in `[overlap]`, `kind = "step"`, after the catalogue's "supplies a step", read by
   `heath.py` and written by `render.py` as "one of our tacit rules supplies a step of it (see
   Overlap)". It is a check change (`review/SCHEMA.md`, `scripts/`), landed first, on its
   own. I.23's record, whose catalogue row is also "supplies a step", would take it too. The
   alternative is no `[overlap]` for III.1, the note in its representation row and the
   catalogue only.
4. **III.33's clause.** Its conclusion says that the circle described has a centre, so that a
   citer could hand it on. Recommended: drop it, since it adds nothing once every circle has
   one; it is our clause, not Euclid's. Keeping it costs nothing but the question a reader
   would ask.
5. **`Arc.Drawn`.** Recommended: its centre clause goes, in brief 0006's file, before the
   definition joins the foundations if it has not yet; after, it is a change of definition,
   with its lock entry and decisions entry.
6. **`Prop1.of_circle`, a lemma or a companion.** Recommended: a lemma, after the porism,
   with no certificate entry, as for `Prop17.inside`: it generalizes no clause. A companion
   would show it on the page with its own certificate.
7. **Pinning the construction.** Recommended: `#guard_msgs` on the axioms of
   `Prop1.construction`, in `Audit/Overlaps.lean`, as the audit lemmas are pinned; like them
   it must be renewed when Book I's proofs change. A companion with a certificate expectation
   (`excludes`) would be firmer, but `Prop1` cites it, and a companion comes after its
   proposition, which `check_fidelity.py` forbids to cite it. Either way the page shows the
   construction's Lean in the helper above the theorem, with one call under Euclid's three
   sentences: the price of a construction that a pin can hold. Keeping it inline, as today,
   reads more closely as Euclid, and leaves the separation to review.
8. **III.17.** Recommended: its proof takes the centre by `Prop1.of_circle`, under Euclid's
   "[III. 1]", which removes today's search for two points through a given centre and its
   use of `centre_unique`. The smallest change takes the centre from the rule and keeps the
   search.
9. **The tag.** Recommended: `centre-given` leaves all 31 records, the twelve that name a
   centre included. The alternative keeps it on those twelve with a new meaning ("the centre
   is named, as Euclid's setting-out names it"), which their notes already say.
10. **One pull request or several, for the restatements.** Recommended: one. Each change is
    small, the citers of III.1, III.21 and III.22 run through most of Book III, and a record
    touched twice would be read twice.

## Appendix: what is staged, and why

The rule cannot be added before its pull request, so no staged statement can be proved from
it. Each new statement is staged with `sorry`, and the rule's content enters only as a
hypothesis of a check, named `exists_centre`, so that the same words refer to the rule once
it lands. Staging, rather than code blocks in this brief, is for the checks: they show that
each new statement is well formed, that it says what today's says given the rule, and so
that it needs no new mathematics, and, for III.1, that the construction and the correctness
fit. The names sit in `Elements.BookIII.Staging.Centre` (and `Elements.Staging.Centre` for
Book Zero and the definition), not `Elements.BookIII.Staging`, where brief 0006's restated
III.24 and III.25 already are. `Staging.lean`'s imports are the integrator's and are left as
they are; `lake build Staging` builds the folder by its glob.

| File | What it holds |
|---|---|
| `Staging/Centre/Prop01.lean` | `Prop1.construction`, proved; III.1 restated; a check proving it from the construction and the rule's content; a check that today's III.1 follows; `Prop1.of_circle`, proved from the staged III.1 |
| `Staging/Centre/Restated.lean` | the other eighteen propositions, III.33, the three steps of `Circumferences.lean` and `EqualCircles.refl`, each with its two checks |
| `Staging/Centre/Brief0006.lean` | brief 0006's six statements and `Arc.Drawn` without the centre, with their checks, and the two checks that `Prop24.equalCircles` and `Prop25.of_circle` still have today's III.24 and III.25, restated |
