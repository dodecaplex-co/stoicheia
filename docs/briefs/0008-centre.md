# Brief 0008: every circle has a centre

19 October 2026: the frozen plan below uses the former baseline of 87 axioms.
[Eight rules are now theorems](../FORMALIZATION.md#rules-now-proved), keeping their
names and exact types, so the baseline is 79, including 73 tacit rules. Adding the
proposed centre-existence axiom would then have taken 79 to 80, and 73 tacit rules to 74.
Thirty-one more
rules became theorems the same day, so the baseline is now 48 axioms, including 42 tacit
rules. With them, the
centre-existence axiom would take 48 to 49. This note adds no axiom and grants no approval
to add one.

`centre_unique` is now proved in `Elements/Figure/Circles.lean`; Circle 4 is proved
after I.7 from I.7, Definition I.15 and `circle_eq`; Circle 2 is proved from Circle 3,
which stays an axiom. The old dependency counts must be measured again. A pin excluding
a retired name from an axiom list no longer detects calls to that theorem; any intended
restriction on its use needs a separate check proposal. Section 7's restated III.5 and
III.6 still cite neither `circle_eq` nor Circle 4, but the axioms pinned for them in
`Audit/Crossing.lean` now include `circle_eq` and Postulate 3, through proved
rules such as `centre_inside`; where the frozen text below says they rest on neither, it
records the state at the freeze. The historical readings and frozen statements below are
preserved.

*Frozen 18 October 2026 by the coordinator, after Astra's challenges of `afe0ee9` and
`3f00ebf` and the Claude challenger's; decisions Q1 to Q16 as recorded in section 8.*

*Status, 20 October 2026, after the eight axiom retirements:*

No certified proof uses Circle 2 or rests on Circle 3. The [guard](../../scripts/check_fidelity.py) now forbids the proved Circle 2 through its dependence on the retained Circle 3 axiom.
The [overlap kind](../../review/SCHEMA.md) is required (#93); the [negative test](../../scripts/negative_tests.py) reads the lock and [`touching-whole-circles`](../../review/terms.toml) exists (#113).
The [forbidden-command scan](../../scripts/check_fidelity.py) covers `Staging/` and `Audit/` (#39).
The [formal model](../../model/Model/Assembly.lean) proves all 79 locked laws, with [generated laws](../../model/Model/Laws.lean) (#109).
Stage 2's proofs are in [`Elements/`](../../Elements/) (#102).
Stage 4b's III.8 and III.17 companions are in [`Elements/BookIII/Prop08.lean`](../../Elements/BookIII/Prop08.lean) and [`Prop17.lean`](../../Elements/BookIII/Prop17.lean) (#111); stages 3 and 4 remain in `Staging/`.
[Staged III.1](https://github.com/jackChallis/stoicheia/blob/01ecbaa2/Staging/Centre/Prop01.lean) still calls Circle 2, now a theorem resting on Circle 3; its construction must be reconciled with [main's III.1](../../Elements/BookIII/Prop01.lean) before migration.
Still to do under #59: the prototype rename, centre rule, construction guard, restatements, tag revision and record migration.
The frozen text below is kept as history.

*Status, 21 October 2026, after trains C6a and C6b, merged with axiom wave one:*

The rule is in the foundations: `Tacit.exists_centre`, in [`Constructions.lean`](../../Elements/Foundations/Tacit/Constructions.lean), by the owner's decision of 18 October, and with it the lock holds 80 axioms and 74 tacit rules, main's 79 and 73 and the rule (step 5).
Section 7 is in the edition: III.5 reads "cut" as crossing (`CirclesCut`), and in III.6 contact within asks for a point of the inner circle within the outer; [`Audit/Crossing.lean`](../../Audit/Crossing.lean) recovers the earlier statements of III.5, III.6, III.11 and III.13.
The prototype's rename landed with the mixed angles of III.16 and III.31: the theorem is `exists_circle_about`, in [`Elements/Figure/Regions.lean`](../../Elements/Figure/Regions.lean).
The [formal model](../../model/Model/Assembly.lean) proves all 80 locked laws.
Stages 3 and 4 and the mixed angles are in `Elements/`, and their staged copies are deleted.
III.1's construction is at home in [`Elements/BookIII/Prop01.lean`](../../Elements/BookIII/Prop01.lean) and takes a centre from the rule only inside the proof that D is within, as the dated correction in section 3 records; [staged III.1](https://github.com/jackChallis/stoicheia/blob/1cc743ec/Staging/Centre/Prop01.lean) now checks the restated III.1 against it and calls neither Circle 2 nor Circle 3.
After C6b, the lock also holds 242 vocabulary words: train C6a's 238, which include those of main's restricted superposition rule, and C6b's four. The current certificate has 56 tacit rules for III.1 and 51 for its porism; `adjacent_eq_of_right`, which III.1 reaches, became a theorem in wave one. These current measurements supersede the dated correction's pre-wave-one count of 57 for III.1 without rewriting that historical measurement.
Still to do under #59: the construction guard (step 4), in a pull request of its own, then the restatements and the record migration (step 6, train C6c), and the tag revision (step 7).
This note changes no declaration of the brief, and the frozen text below is kept as history.

*Correction, 21 October 2026, train C6c (C6a, C6b and step 6), for issue #152:* the two
statuses above are kept as written, and this note corrects what step 6 has made false in
them. No statement, declaration, record or lock changes, so no consumer is affected.

- **Discrepancy.** Step 6 retired `Staging/Centre/` (the [dated completion in section
  3](#completion-step6-19-october-2026)), so neither staged III.1 the statuses describe
  exists on this train. Their links now name the file at the revision each status was
  written: 01ecbaa2, where the staged construction called Circle 2, and 1cc743ec, where it
  called neither Circle 2 nor Circle 3. The construction guard and step 6's restatements,
  listed above as still to do, are done on this train: the guard is `Audit/Centre.lean`,
  renewed after axiom wave one, and the completion note says what work remains.
- **III.1 and its pin.** `Prop1.construction` agrees with the pin by the route decision D1
  recorded in the [section 3 correction](#correction-iii1-19-october-2026): it takes a
  centre from `exists_centre` only inside the proof that D is within. Lean's axioms for
  `Elements.BookIII.Prop1.construction` are 64 names, 56 of them tacit rules, with
  `Tacit.exists_centre` among them and neither Circle 3 (`Tacit.outside_of_between`) nor
  `sorryAx`: the list `Audit/Centre.lean` pins, and the count the correction gives at
  `b117d01`. Since wave one, Circle 2 and `centre_unique` are theorems, so no axiom list
  shows either. Circle 2 is proved from Circle 3, and the absence of Circle 3 excludes it.
  A call to `centre_unique` is left to the reader, as the guard's opening note says, so the
  renewal read that the section 3 correction and the note before question 7 ask for can
  find only Circle 3 and `sorryAx`. A walk of the construction's proof terms on 21 October
  reaches neither Circle 2 nor `centre_unique`.
- **Staged work.** No file under `Staging/` calls Circle 2 or Circle 3, or any of Book
  Zero's three lemmas that rest on Circle 2, and no declaration of the Staging library
  rests on Circle 3, by Lean's axiom lists on 21 October.

*Correction, 22 October 2026, for issue #131:* the rule of section 4, "a bracket means
III.1, none means the rule", with its table's rows for III.2, III.4, III.8 and III.17,
its row in Appendix B and question 8, is corrected by the coordinator's
[decision entry of 22 October 2026](../decisions/2026-10-22-iii1-calls-dropped.md): a
proof takes a centre from the rule wherever a call of III.1 would do no work, and Heath's
"[III. 1]" stays on the page as his reference. So III.2, III.4, III.8 and III.17 take
their centres from `exists_centre`, and III.14, whose statement names E, takes none and no
longer rests on the rule. No statement changes. The frozen text below is kept as history.

*Status, 25 October 2026, at main bedbba23e, for #252:* the notes above and the frozen
text below are kept as written, and this note corrects two of their claims. No statement,
declaration, record or lock changes.

- **Heath's statement under III.5.** Section 7's paragraph on III.10 calls the sentence it
  quotes from Heath (vol. 2, p. 12) "the converse Heath gives under III.5". It is not
  III.5's converse. III.5 reads "If two circles cut one another, they will not have the
  same centre" (vol. 2, p. 12; [heath/III/05.md](../../heath/III/05.md)), and its converse, that circles
  with different centres cut one another, is false. Heath gives the statement under III.5,
  beside the enunciation that joins III.5 and III.6: two circles with the same centre and
  one point of their circumferences in common coincide altogether. It is what `circle_eq`
  gives in III.10's last step, from the common centre P and the common point B, as
  [III.10's record](../../review/III/10.toml) and the
  [gap catalogue](../reports/gaps-book-III.md#iii10) say.
- **III.1 and `adjacent_eq_of_right`.** The status of 21 October after trains C6a and C6b
  says that III.1 reaches `adjacent_eq_of_right`. Train C6c changed that the same day
  (#168, commit b796d53a): `Prop1.perpendicular` takes Euclid's step by I.13 in place, the
  two angles at A with AD making two right angles, so that taking the given right angle
  away leaves the other right (C.N. 3). A walk of the proof terms of `Prop1`,
  `Prop1.porism`, `Prop1.construction` and `Prop1.perpendicular` on 25 October, at main
  bedbba23e, reaches I.13 and not `adjacent_eq_of_right`, and in facts.json III.1 and its
  porism both cite I.13. The counts of 21 October no longer hold, since more rules have
  become theorems. The status gives 56 tacit rules for III.1 and 51 for its porism, and the
  correction 64 names for `Prop1.construction`, 56 of them tacit rules; at main bedbba23e
  [CERTIFICATE.md](../../CERTIFICATE.md)'s Book III rows give 39 tacit rules for III.1 and
  38 for its porism, and [`Audit/Centre.lean`](../../Audit/Centre.lean) pins 47 names for
  the construction, 39 of them tacit rules. The certificate is where the current counts are
  read.

*Status, 26 October 2026, for #59:* the notes above and the frozen text below are kept as
written. Step 7 is done: `[tag.centre-given]` has left `review/terms.toml`, by the
decisions entry `docs/decisions/2026-10-26-centre-given-retired.md`, and no record carries
the tag. III.1's axioms expectation in `tests/certificate_expectations.json` now names
`Tacit.exists_centre` beside its count of 39 tacit rules, so that another rule cannot take
its place unnoticed. With step 7, all seven steps of section 6's order of work have
landed, and nothing is left of the "Still to do under #59" lists above. No statement,
declaration, record or lock changes.

*Status, 26 October 2026, for #473:* the notes above and the frozen text below are kept as
written, and this note corrects one claim of the note of 19 October 2026 at the head of the
brief and brings one claim of section 7 up to date. No statement, declaration, record or
lock changes.

- **III.5's and III.6's pins.** That note says that the axioms pinned for the restated III.5
  and III.6 in [`Audit/Crossing.lean`](../../Audit/Crossing.lean) include `circle_eq` and
  Postulate 3, through proved rules such as `centre_inside`. Since Book Zero's lemma that a
  radius is not nothing came to rest on our radius rule (`Tacit.radius_ne_zero`,
  [the entry for that move](../decisions/2026-10-25-book-zero-radius-rule.md)), the pins
  hold Postulate 3 and the radius rule, and neither `circle_eq` nor Circle 1
  (`between_of_inside_chord`). So what the frozen text below says of the two proofs at the
  freeze, that they rest on neither `circle_eq` nor Circle 4, holds again.
- **The mixed-angle step.** Section 7's certificates say that the staged work used
  Diagram-segment 2 in one step of the mixed-angle prototype. That step, the case of equal
  radii in `exists_inside_both`, now in
  [`Elements/Figure/Regions.lean`](../../Elements/Figure/Regions.lean), compares lengths
  instead, and no proof of Book Zero calls the rule. In `Elements` it is called by III.10,
  by III.13's `TouchesInternallyAt.between`, by III.25's `Prop25.complete`, by
  `Arc.eq_of_aligned` and by the proof of Circle 4 after I.7, each to conclude that two
  circles with one centre and a common point are one.

*19 October 2026: the [dated correction in section 3](#correction-iii1-19-october-2026)
replaces the frozen construction, guard, porism, overlap and order claims it names below,
while the frozen text is retained as history.*

*19 October 2026: [step 6 is implemented](#completion-step6-19-october-2026) at
`17987153`. The completion note records the current declarations and certificate counts;
the earlier plans and reviews below remain dated records.*

*The brief settles, before any proof work and as [WORKFLOW.md](../WORKFLOW.md), section 2,
requires, the rule the owner approved, that every circle has a centre, and every statement
the rule changes. Each new statement is written with `sorry` in the `Staging` library, in
`Staging/Centre/`, and checked by Lean against today's statement, given the rule's content.
Frozen, it is what others write against: a later change is a revision of this brief
(WORKFLOW, section 2, "Correcting a frozen brief"), never a quiet edit. Issue #40, which the
owner set first, has landed (in train H2, #103), and the rule itself lands only in the
coordinator's own pull request, in the order that section 8 gives.*

*The challenges. The draft at `afe0ee9` was read by two challengers who did not write it:
Astra (GPT Pro, through Codex, read-only), which found no mathematical error in the 30
staged restatements and returned the draft for revision of its overlap display, the order in
which the construction's guard lands, its list of consumers and its plan for the formal
model; and a Claude challenger (Claude Opus 5.5), whose one blocking finding was that the
tag could not leave the records as planned. The revision at `05c9095` answered every finding
of both. Section 7, added afterwards, restates III.5 and III.6, by the coordinator's
decision when the owner asked whether there was a way around their resting on `circle_eq`
or Circle 4. Astra (GPT Pro, through Codex, read-only) challenged it on its own at
`3f00ebf`, supported the restatement, and found one thing that blocked its freeze: the
rules still give the restated III.5 and III.6 at once, so the overlap catalogue keeps their
rows. The revision at `d38c5bf` answered every finding. Appendix B gives each finding of the
three challenges, with its source and what was done. Warm thanks to Astra, twice, and to the
Claude challenger.*

*Brought up to main for the freeze, at `2130252` (#87 to #92, and #98, the formal model's
package) and again at `32eeba5` (#40, #65, #70, stage 2 in the edition by #102, and the
disclosures, #104): the line references and the prose that names other work are renewed
against it.*

Base: main at `f17b427`, merged with main at `e04f318`, at `5766311` for section 7, and at
`2130252` and `32eeba5` for the freeze. `lake build Staging` passes at this revision with
the files in `Staging/Centre/`: 33 statements with `sorry`, four definitions, eight proved
declarations (the construction of III.1; its circle-only entry point, from the staged III.1;
III.13's two clauses as lemmas, from the staged III.13; `Centre.every`; and, for section 7,
III.5 and III.6 restated and `CirclesCut.symm`), 81 checks, and the axioms of III.5 and
III.6 pinned. Nothing in `Elements/` changes, so main's records, lock and CI are untouched.

The reading is Astra's. Asked by the owner, Astra answered three foundation questions at
`f17b427`, the first of them this one, with a precise account of what the rule adds, which
statements it changes and which it must leave alone; the answer is posted on
[issue #59](https://github.com/jackChallis/stoicheia/issues/59). This brief follows it
throughout, and owes it a great deal: warm thanks to Astra. The question itself came from
the fresh outside review (#47), which found the `centre-given` hypothesis across Book III.

## 1. The decision

The owner decided on 18 October 2026, on issue #59 (the words below checked against the
owner's comment there, on 18 October):

> **The owner's decision (18 October): approved, as Astra recommends.** `axiom exists_centre
> (α : Circle) : ∃ O, Centre O α`; III.1 keeps its construction-rich conclusion and drops the
> existence hypothesis, with a circle-only entry point for users; the statements that only
> assume a centre exists drop that hypothesis, those that name the centre keep it; III.1
> gains an overlap note for bare existence; its page says the foundations assume a centre and
> the proposition proves that Euclid's construction finds it. The order: #40 first (a new
> axiom needs the model's law names pinned as data), then a short brief with every statement
> changed, challenged and frozen, then the axiom with its lock entry, model law and decisions
> entry, then the restatements and their records.

On the same day the owner decided to start the formal model now (#73): in `model/`, a Lake
package of its own in this repository with a pinned Mathlib and its own CI job, the main
library staying plain Lean, its laws generated from the elaborated declarations with
translation checks, the hardest first. The package landed on main in #98; issue #73 stays
open for the work to come. Section 2 says what that means for this rule.

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
  namespaces takes the same name (question 12). Question 1 weighed a home beside Definition
  15, as the challenge asked, and the freeze kept this one; the opening note of
  `Definitions.lean`, which says that Definition 15 carries content, gains a sentence
  pointing to the rule, so that a reader who looks for it among the definitions finds it.
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
  witness is the circle's own centre; the same holds in the hyperbolic plane. #40 has
  landed (in train H2, #103), so the law lands in the rule's own pull request, as
  MODEL.md's "Changing the axioms" says: a line in `tests/model/laws.toml`,
  `"Tacit.exists_centre" = "exists_centre"`, and the law's code in `search.py` and
  `hyperbolic.py`, each a function `_` under `@axiom('exists_centre', dict(al=C_))`,
  written as Points 7 and 8 are and keeping to the helpers the laws may call (`LAW_GLOBALS`
  in `scripts/safe_push.py`). In `search.py` a circle is its centre's coordinates and its
  squared radius, and `centre` is not among those helpers, so the law checks
  `is_centre((al[0], al[1]), al)`; in `hyperbolic.py`, which lists `centre` and `in_disc`,
  `is_centre(centre(al), al) and in_disc(centre(al))`. MODEL.md gains a row in "Taking
  points, and where lines and circles cross" (`exists_centre` | every circle has a centre |
  a circle of the plane is its centre and a radius; its centre is the witness), its counts
  from `run.py --full --write`, never inferred from the old totals, its 87 and 81 made 88
  and 82 (lines 3, 12, 23 and 504) and its "the other 86" made 87 (lines 399 and 440), and,
  with thanks, Astra's argument that the law is independent of the other 87, as an informal
  countermodel argument. The rule has no guard, so no mutation goes with it.
- **The formal model.** Its package is on main (#98, from `lean/model-skeleton`; Astra read
  `40dfa3c`), and `model/Model/Euclidean/Centre.lean` already proves the law,
  `⟨α.1.center, rfl⟩`, since a circle there is a sphere of positive radius, a subtype. Its
  translation, `Hand.exists_centre` in `model/Model/Hand.lean`, under "Proposed, and not yet
  in the library", is by hand: nothing is generated yet, from the lock or from the
  declarations. `model/README.md` ("How the lock ties it") has its round-trip check join
  `model/Check/Hand.lean` in the change that declares the axiom, so the rule's pull request
  carries it, with `model/lock.sha256` renewed (section 6, step 5).
- **The decisions entry,** in the pull request that adds the rule, quotes the owner's
  approval (section 1), says that the rule is ours and from Definitions I.15 and I.16, gives
  the counts (88 axioms, 82 tacit rules, the vocabulary unchanged), and names each protected
  file it changes, as [WORKFLOW.md](../WORKFLOW.md), section 10, requires.

## 3. III.1

<a id="correction-iii1-19-october-2026"></a>

### Dated correction, 19 October 2026: III.1's construction and porism

This dated correction follows [WORKFLOW.md](../WORKFLOW.md), section 2, "Correcting a
frozen brief". It replaces the claims named below, including their summaries in sections
4, 6 and 8 and Appendix B; the frozen text that follows is kept, not silently rewritten.

- **Discrepancy.** The frozen construction promises no use of a rule supplying a centre,
  but its staged proof used Circle 2 for D within. That would reintroduce the rule that
  contains III.2 into III.1 and its consumers. The frozen porism also describes a call to
  III.1 and `centre_unique`; the delivered proof instead uses its given centre directly.
- **Current declarations.** Section 3's code block fixes `Prop1.construction`, with the
  circle and two distinct points on it as input and the bisections and perpendicular
  straight line as output. Today's `Elements.BookIII.Prop1` still takes
  `hABC : ∃ G : Point, Centre G ABC`; `Elements.BookIII.Prop1.porism` takes
  `hG : Centre G ABC` and concludes `Collinear D C G`. Their types do not change in
  corrected step 3. The restated `Prop1` and `Prop1.of_circle` remain staged for step 6.
- **Corrected construction and reason, replacing "The construction, apart" and the
  closure claims in "The correctness, with the rule".** The correction keeps the construction's
  frozen type and moves it home before `Prop1`. It receives no centre. It uses
  `exists_centre` only inside the proof that D is within the circle, through
  `Prop1.within`, by III.2's argument using I.5, I.16 and I.19:

  ```lean
  have hD_in : InsideCircle D ABC :=
    (exists_centre ABC).elim fun G hG => Prop1.within hG hA hB hADB hAD
  ```

  No centre witness reaches its output. The bisections and perpendicular construction
  stay as before, and today's `Prop1` calls `Prop1.construction` under Euclid's three
  construction sentences. The proof that F is the centre stays in `Prop1`.
  `Prop1.within` keeps its given-centre interface for this confined use; changing that
  helper is not part of step 3.
- **Corrected guard, replacing "The guard Astra asks for", its sample comment and
  counts, and both versions of question 7.** `Audit/Centre.lean` fixes the same
  construction type and pins its complete axiom list afresh from Lean's actual output
  for the home declaration. `Tacit.exists_centre` is admitted. Every renewal is read
  for `Tacit.inside_of_between`, `Tacit.outside_of_between`, `Tacit.centre_unique` and
  `sorryAx`, all of which must be absent. At `b117d01`, `#print axioms` reports 64 names:
  Lean's three foundations, Definition I.15, Postulates 1 to 4 and 56 tacit rules, with
  `Tacit.exists_centre` included and those four names absent. This delivered output
  replaces the frozen prediction of 62 names and 54 tacit rules. The guard uses Lean's
  complete printing, not a list inferred from the count. A pin does not show where the
  witness was used; the reader checks that confinement in the proof.
- **Corrected porism, replacing "The porism" and its record and certificate promises.**
  The statement still names its centre G. Its proof takes the argument of Euclid's
  reductio directly from that centre: on AB it is D by `Prop1.middle`; off AB, the shared
  I.8 step `Prop1.equal_adjacent` makes the adjacent angles equal, Definition I.10 makes
  them right, Postulate 4 identifies their measure with `∟`, and `Prop1.perpendicular`
  puts G on DC. It neither calls III.1 nor uses `centre_unique` or `exists_centre`. The
  fresh certificate has 51 tacit rules, replacing the frozen prediction of 58. III.1 has
  57, including the rule through its construction, and still excludes `centre_unique`.
- **Corrected overlap, replacing "The overlap note" and "The catalogue".** In the
  final restated III.1, the rule supplies two steps: D within by III.2's argument, and
  "let G be the centre". The bisections, perpendicular straight line and correctness
  argument remain III.1's work. The record keeps `kind = "step"`; bare existence is
  supplied by the rule, while `Prop1.of_circle` will give Euclid's construction and its
  correctness from a circle alone. At corrected step 3, only D within uses the rule:
  today's `hABC` still supplies G for the reductio. The current record must say this,
  keep scope `full` and `centre-given`, and not claim the final restatement has landed.
- **Corrected record and page text, replacing the affected instructions in "The
  record" and section 4's prose list.** The grouped passage names `Prop1.construction`;
  the `Prop1.within` passage names the rule as the source of its centre; the porism
  passage names the shared comparison and its direct route. The commentary and overlap
  catalogue say the same. The certificate field guide's old 56/57 counts are no longer
  current. In `tests/certificate_expectations.json`, the porism's existing `equals`
  moves to the full fresh list, its count to 51, and it gains an exclusion of
  `Tacit.centre_unique`; III.1's count moves to 57 and its exclusion stays. Only those
  two expectations change, with their reasons; no field is dropped. These are values
  pinned to the content, after the earlier separate change that pinned the old porism's
  full list. Review stamps wait for an independent reader.
- **Corrected order, replacing section 6's order and its sentence allowing steps 3 and
  4 before step 5, section 8's order of landing and its summary, and their repeated
  guard instructions.** Step 5, the rule, precedes corrected step 3. Step 4 follows
  step 3 and precedes step 6, in a pull request of its own, never in a train with the
  content it judges. Section 7 landed earlier, as its separate dated correction says;
  it does not wait for step 6. The construction and porism content comes first, the
  guard next in a separate landing, then the centre restatements.
- **Consumers affected.** III.1's callers, the porism's callers, its review record and
  page, Book III's introduction (`mishnah/intro/III.md`) where it discusses centres,
  `docs/briefs/0004-book-III.md` where it discusses centres and porisms, III.2's
  commentary, `docs/reports/gaps-book-III.md`, the overlap catalogue,
  `Certificate/FIELDS.md`, `tests/certificate_expectations.json`, the future
  `Audit/Centre.lean`, and the dependency pins in `Audit/Overlaps.lean` and
  `Audit/Crossing.lean`. The integrator regenerates the pages. No proposition or porism
  statement, Heath sentence, foundation or lock changes under this correction.
- **Work that can go on meanwhile.** The remaining content proceeds under its approved
  interfaces. The construction guard waits for its separate landing; the restated
  III.1 and its circle-only entry point wait for step 6.

<a id="completion-step6-19-october-2026"></a>

### Dated completion, 19 October 2026: step 6

Step 6's centre restatements are done in both halves at `17987153`, under the approval
of 18 October and the correction of 19 October above. This is completion of the source
changes, not a claim that the outstanding reviews, tooling and generated edition have
been completed. The earlier plans in sections 4 and 6 and Appendix A remain historical.

- **Main statements.** `Prop1`, `Prop2`, `Prop4`, `Prop8`, `Prop9`, `Prop10`, `Prop13`,
  `Prop17`, `Prop21`, `Prop22`, `Prop23`, `Prop24`, `Prop30`, `Prop32`, `Prop34`, `Prop35`,
  `Prop36` and `Prop37` have no centre-existence inputs. `Prop34` takes its circle
  explicitly. `Prop33` no longer returns a centre-existence clause. III.25 was already
  restated as a construction from the segment's points; its core still constructs a
  circle with centre E, and the changes here are to its companions. Named centres stay
  wherever another hypothesis or conclusion uses them geometrically. `Prop1.within`
  retains its approved given-centre interface for the confined construction step.
- **Shared declarations and companions.** `Prop1.of_circle` now applies the restated
  III.1 to two points chosen on the given circle. `Prop2.within`, `Prop2.triangle`,
  `Prop2.oppositeSide`, `Prop2.sameSide`, `Prop8.partner`, `Prop8.general`,
  `Prop17.general`, `Prop23.point`, `Prop24.chord_cases`, `Prop24.equalCircles`,
  `Prop25.complete`, `Prop25.of_circle`, `Prop32.sameSide`, `Circumference.eq`,
  `Circumference.standing`, `Circumference.whole` and `Circumference.add` take no
  centre-existence input. `Prop25.complete` also drops its unused point parameter E
  and the hypothesis that E is the constructed circle's centre, obtaining a centre
  internally instead. `EqualCircles.refl` takes just its circle. The two projections
  `Prop13.internally` and `Prop13.externally` and Book Zero's `Centre.every` are in
  their homes. The dated notes in briefs [0006](0006-statements.md) and
  [0007](0007-stage-4b.md) describe their current interfaces after the frozen blocks.
- **Arcs.** `Arc.Drawn` now consists of endpoint incidence and non-collinearity of
  the side marker with the base, without a centre clause. Its consumers use that
  meaning, including `Arc.eq_of_aligned`, `Prop25.meets` (the planned `Arc.meets`),
  `Prop24.image`, `Prop24.equalMeasure`, `Arc.measure_eq_iff` and `Arc.congruent_iff`.
  Centres with geometric roles in `EqualCircles` and the three arc kinds remain.
- **Routes and coverage.** III.24 still proves congruence; its alternative companion
  `Prop24.equalCircles` takes two centres from the rule. III.25 has full coverage in
  its record with the proved, registered companions `complete`, `kind` and `of_circle`;
  the construction and `kind` keep E. III.30 takes no local centre witness:
  `EqualCircles.refl` uses the rule internally. III.35–III.37 use `exists_centre` at
  their unbracketed centre-taking steps, and their direct citations of III.1 are gone.
  III.28 and III.29 continue to take their centres from their equal-circle data.
- **Audit bridges.** `cut_point`, `CirclesCut.of_meet`, `within_point`, `III_13_today`
  and `Audit.III_24_measure` take no supplied centres. The crossing bridge still uses
  III.7 and III.8; the contact bridge still uses III.10. These comparisons with the
  earlier readings do not enter III.5's or III.6's proofs. `lake build Audit` passes at
  this revision, including all 26 axiom pins.
- **Certificate and guard.** After `lake build` and
  `lake env lean Certificate/Facts.lean` at `17987153`, fresh `facts.json` has
  **44 entries** whose full axiom lists contain `Tacit.exists_centre`: **28
  propositions and 16 companions, no porisms**, among 99 propositions, 3 porisms and
  33 companions. These are dependency counts, not counts of restated statements.
  III.1 Por. neither cites III.1 nor uses `exists_centre` or `centre_unique`.
  `Audit/Centre.lean` is unchanged by step 6: its construction type and complete axiom
  pin still pass. The guard does not replace the semantic review of how the witness
  is confined in `Prop1.construction`.
- **Staging and the separate proposal.** All files under `Staging/Centre/` have been
  retired, with no live import of that directory. `Prop30.halves` is a separate
  proposal staged with `sorry` in `Staging/Halves/Prop30.lean`, awaiting the owner's
  approval. It is unproved, unregistered and absent from the certificate; its proof
  is not assigned.
  *21 October 2026:* the owner approved it on 20 October 2026; it is proved in
  `Elements/BookIII/Prop30.lean`, registered as the companion "III.30 halves", and its
  staging file is deleted (brief 0006, the note after its Addition).
- **Remaining work.** The source and statement stamps still need independent review
  at the revision to be delivered. The scaffold's Book III types and the screen's
  circle-rule set need a separate tooling pull request, followed by a fresh screen.
  The integrator regenerates the edition after review. Step 7 still removes the
  unused `centre-given` definition from `review/terms.toml`.

### The text frozen on 18 October

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

**19 October 2026, step 6.** `Prop1`, `Prop1.construction` and `Prop1.of_circle`
now have the declarations above in `Elements/BookIII/Prop01.lean`. The construction
was already home under the earlier correction; the two entry points now use the
restated interfaces. The correction above, not the frozen claim below, describes
the confined use of `exists_centre` in the construction.

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
  `Prop1.construction`"). Approved at the freeze (question 14), FORMALIZATION section 5,
  "Helpers", gains one sentence, with step 3 of section 6, where the construction first
  lands: "A construction core kept apart under section 4, as III.1's `Prop1.construction`,
  carries Euclid's sentences of construction, not a step he takes for granted; the record
  shows it as a `grouped` passage naming it, and the proposition keeps the correctness
  argument under his sentences." It is proved in the staged file by today's construction
  steps, unchanged, and the freeze approved it as a staged fact (question 13).
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
  Euclid's points out, and pins with `#guard_msgs` the whole list of axioms Lean reports for
  the construction, as `Audit/Overlaps.lean` pins its lemmas and `Staging/Centre/Crossing.lean`
  pins III.5 and III.6: 62 names at this revision, among them neither `Tacit.exists_centre`
  nor `Tacit.centre_unique` nor `sorryAx`. `lake build Audit` fails if the list changes, or
  if the construction is not declared. The brief had planned a targeted check, an `#eval`
  that failed only if one of those three names entered; but `tooling/forbidden-scan` (issue
  #39, landing soon) refuses `#eval`, and every other command that runs code as a file is
  built, in `Audit/` and `Staging/` as in `Elements/`, so the guard is a pin. Tried at this
  revision against the staged construction, the pin passes, and a renamed construction, a
  planted `sorry` and a planted use of `centre_unique` each fail it.

  ```lean
  import Elements

  set_option warningAsError true

  section
  open Elements Elements.Tacit

  /-- The construction of III.1 is given a circle and two points of it, and nothing more. -/
  example : ∀ {A B : Point} {ABC : Circle}, OnCircle A ABC → OnCircle B ABC → A ≠ B →
      ∃ F C D E : Point, Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧
        OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ ∠ B D C = ∟ ∧ ¬ Collinear A B C ∧
        Between C F E ∧ ‖C F‖ = ‖F E‖ :=
    @Elements.BookIII.Prop1.construction

  end

  /-! And it uses no rule that a circle has a centre, nor that it has only one, nor an
  admitted proof: its axioms, pinned. A renewal of the list is read for those three names. -/

  /--
  info: 'Elements.BookIII.Prop1.construction' depends on axioms: [propext,
   Classical.choice,
   Elements.Definition15,
   Elements.Postulate1,
   …
   Elements.Tacit.triple_incidence2]
  -/
  #guard_msgs in
  #print axioms Elements.BookIII.Prop1.construction
  ```

  The list is elided here; the file holds Lean's own printing, 62 names at this revision:
  Lean's `propext`, `Classical.choice` and `Quot.sound`, Definition I.15, Postulates 1 to 4
  and 54 tacit rules. The pin comes after the section closes, so that Lean prints each name
  in full, as in `Audit/Overlaps.lean`. It is a regression check, and shows no more than
  that: not that the steps are Euclid's, which the record's passage and its reviewer say,
  nor by itself that no other route to a centre exists, which Astra's informal countermodel
  argument says. Unlike the targeted check, it must be renewed whenever a proof of Book I
  beneath the construction changes its axioms, and a renewal could carry an added name in a
  long diff, as the Claude challenger warned; so each renewal is read for the three names,
  and the decisions entry of step 4 names the guard. It lands on its own, after the
  construction and before the restatements (section 6).
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

- **The line and the summary.** With `kind = "step"`, from the tooling pull request that
  builds question 3's key together with issue #93, the line under the enunciation says that
  one of our tacit rules supplies a step of it (see Overlap), and Book III's summary, which
  also heads its index, its section of CERTIFICATE.md and its README row, says that in
  III.1 one of our tacit rules supplies a step of the proof, in the words that pull request
  settles for every record of that kind; III.1's overlap note says that the rule does not
  contain the proposition. Without the key, `render.py` writes "already contains" in both
  places (`in_lean_line`, and `overlap_sentences` at `render.py:1477`, which Astra's probe
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
"Other branches"). The rest add no centre clause. For the freeze the same scan ran again, over
`Elements`, `Audit` and every staged file outside `Staging/Centre/`, on main at `2130252`
(#87 to #92, and #98) and at `32eeba5` (#40, #65, #70, stage 2 in the edition by #102, and
the disclosures, #104), and found at each exactly the statements listed in this section, no
more: #87 restates no centre; #88 to #90 prove brief 0006's stages 2 to 4 in Staging
without changing their statements; #102 moves stage 2, of Books I and II, into `Elements`
and stages brief 0009's superposition prototype, neither with a circle's centre; and the
rest add no Lean outside `model/`, or none that takes a centre. The proofs of #89 and #90
do cite statements that change, which step 6 then edits (section 6, "Other branches").

**The rule for each.** An existence hypothesis is dropped. A named centre that appears
elsewhere in the statement is kept: existence of some centre does not identify it. A named
centre that appears nowhere else in the statement is dropped, as an existence hypothesis in
substance; that is a reading of the owner's words by their substance, not their letter,
which the freeze adopted as a standing rule (question 2). An existential inside a definition
is kept where its witness takes part in the definition, as in `EqualCircles`. The old
statement of each is today's, in its file; the new one is the same with the hypotheses named
below removed, and is staged in full, in `Staging/Centre/`, with two checks: given the
rule's content, today's statement gives the new one; and the new one gives today's. So,
given the rule, each says exactly what today's says, and each new proof is today's with the
centre taken another way.

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

### For Lean users: three lemmas, approved

Once III.13 loses its hypotheses, nothing names its three circles, and a citer of one clause
must name a circle the clause never mentions (`(ACK := α)`), as Astra and the Claude
challenger each reproduced in Lean. Conditions said of every centre, as III.4's and III.8's
are and stay, ask a citer who holds a named centre to go through `centre_unique`. Three
lemmas, each one line, take those burdens away; they are new statements, approved at the
freeze (question 11), and are proved in `Staging/Centre/Restated.lean`:

```lean
theorem Prop13.internally {B D : Point} {α β : Circle}
    (h : TouchesInternally α β D ∨ TouchesInternally β α D) (hBα : OnCircle B α)
    (hBβ : OnCircle B β) : B = D

theorem Prop13.externally {A C : Point} {α β : Circle} (h : TouchesExternally α β A)
    (hCα : OnCircle C α) (hCβ : OnCircle C β) : C = A

theorem Centre.every {O : Point} {α : Circle} {p : Point → Prop}
    (hO : Centre O α) (h : p O) : ∀ F : Point, Centre F α → p F
```

**19 October 2026, step 6.** `Prop13.internally` and `Prop13.externally` are now
proved in `Elements/BookIII/Prop13.lean` with the declarations above. `Centre.every`
is proved in `Elements/Figure/OnCircles.lean` with its written type unchanged. Their
centre staging files are retired.

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
| `Arc.eq_of_aligned`, `Arc.meets`, `Arc.measure_eq_iff`, `Arc.congruent_iff`, `Prop24.image`, `Prop24.equalMeasure` | brief 0006, `Staging/Stage3/Aligned.lean`, `Chord.lean`, `Arcs.lean`, `Prop24.lean` | their text does not change, but their `Drawn` hypotheses ask less, so each statement says more; all are proved in Staging since #89, four of them through the clause that goes, which step 6 replaces in a line each (section 6, "Other branches") |
| `Prop25.of_circle`'s proof | brief 0006, `Staging/Stage4/Prop25.lean:288` | `⟨hABC, hA, hC, hP⟩ : Arc.Drawn …` becomes `⟨hA, hC, hP⟩` |
| `Prop8.partner`, `Prop8.general` | brief 0007, `Staging/Stage4b/Prop08.lean` (#85) | drop `hABC : ∃ M, Centre M ABC`; `hGA` stays |
| `Prop17.general` | brief 0007, `Staging/Stage4b/Prop17.lean` (#85) | drops `hBCD : ∃ E, Centre E BCD`; its condition "not within" stays |
| the prototype's `exists_centre` | `Staging/Stage4b/MixedAngles.lean` (#86) | renamed `exists_circle_about`, with its fourteen uses; its statement, `∃ γ, Centre A γ`, does not change (question 12) |
| `Audit.III_2`, `Audit.III_24_measure` | `Audit/Overlaps.lean` | `III_2`'s type is III.2's, and its proof loses one argument; `III_24_measure` drops `hAEB`, `hCFD`, as III.24 does |

`lean/i45-ii14-full` (#80) adds no centre clause. Brief 0006's and brief 0007's statements
are frozen, so this is a revision of each, approved by the coordinator with this brief at
the freeze, made in their files by their owners, after the rule lands. Some of the changes
are forced, not chosen: brief 0006's staged checks show that `Prop24.equalCircles` and
`Prop25.of_circle` have today's III.24 and III.25, and brief 0007's that `Prop8.general` and
`Prop17.general` have today's III.8 and III.17; each check breaks the moment its proposition
loses its hypotheses, so each companion moves with its proposition.
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

**19 October 2026, measured dependencies after step 6.** The forecast above is superseded
by the certificate at `17987153`: seven of the twelve named-centre propositions rest on
`exists_centre`, III.7, III.11, III.14, III.15, III.26, III.27 and III.31. III.7 and
III.11 reach it through `Prop2.within` and III.2; III.1's porism does not rest on it.
The 28 main Book III propositions that rest on it are III.1, 2, 4, 7–11, 13–15, 17,
21–24 and 26–37. This also replaces the certificate forecast under "Records, Lean files
and pages" below; the earlier forecasts remain as history.

### Records, Lean files and pages

**19 October 2026, inventory after step 6.** The counts and predictions below belong
to the frozen plan. At `17987153`, `check_fidelity.py` reports 50 stale-stamp findings:
30 Lean-file stamps and 20 statement stamps, including every record from III.23 to
III.37. They await a reader; this documentation change stamps none. `centre-given`
is absent from the Book III records but remains defined in `review/terms.toml` until
step 7. The [completion note](#completion-step6-19-october-2026) gives the measured
certificate counts and current routes, including III.1 Por.'s independence from the
rule and III.25's full coverage with its three companions.

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
  same way, takes it too, in step 6 with section 7's change to its record (#87, which
  rewrote that record, has landed). In the 12 records with other tags, `centre-given`
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
  III.5, III.6 (until it takes the new tag) and III.19 are untouched by the rule; section 7
  changes III.5's and III.6's records for a reason of its own.
- **Certificates.** With the proofs as above, 27 propositions and III.1's porism rest on the
  rule: III.1, 2, 4, 8, 9, 10, 13, 14, 15, 17, 21 to 37, read from the proof terms at
  `f17b427`. The pins of `Audit.III_26_any`, `Audit.III_27_any` and `Audit.III_24_measure`
  gain the rule.
- **Prose, and the scripts that describe the old setup,** by the pull request that changes
  each (section 6):
  - *With the rule:* [FORMALIZATION.md](../FORMALIZATION.md) section 7 (its count, and
    "each tacit rule from System E", which now has one exception), whose section 9 names no
    count since train D1 (#104), so needs no change;
    [Book I's brief](book-I.md)
    ("81 tacit rules, from System E"); `CONTRIBUTING.md`, lines 53–54 ("new rules come from
    System E, or LeanEuclid's corrections of it", a policy that gains "or, by the owner's
    decision, a rule of our own, as `exists_centre`"); `README.md`, line 151 ("whose System E
    is the source of our tacit rules", of all but one) and `NOTICE`, line 11 (our tacit rules
    follow System E, save `exists_centre`, which is ours); the opening note of
    `Elements/Foundations/Definitions.lean` (section 2); MODEL.md and the harness (section
    2). `scripts/check_kernel.py` (#79) reads the lock, so nanoda admits the rule by its
    name with no change.
  - *With the restatements:* FORMALIZATION section 3 (the rows for a circle's centre, now
    "every circle has one, by our rule `exists_centre`; III.1 finds it", and for circles
    touching, now tagged) and section 4 ("a circle known to have one"); section 5's
    sentence of section 3 above, approved, goes earlier, with step 3;
    [STYLE.md](../STYLE.md), line 235 (Book III's
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
    308–309), and its sweep of every rule (line 236, "We read each of the 81 tacit rules"),
    for which `Audit/screen.py` runs again, about ten minutes, with `Tacit.exists_centre`
    added to its list of rules about circles and the counts in its docstring and the
    report renewed; `Certificate/FIELDS.md`, the `axioms` row ("III.1's still has 56 tacit
    rules, and III.1 Por.'s has 57"); `tests/certificate_expectations.json`, values and `why`
    strings (section 3); and `scripts/scaffold_book.py`, lines 188–197 and its Book III
    signatures, which would scaffold the old interface. Brief 0006's "[axioms] stays at 87"
    (`docs/briefs/0006-statements.md`, lines 233 and 1680) and its tags for III.24 (line
    1285, `centre-given` among them); brief 0007's commentary on `Prop17.inside` ("for a
    circle with a centre", lines 291, 297, 326, 354 and 430 of
    `docs/briefs/0007-stage-4b.md`, and the module note and docstrings of
    `Staging/Stage4b/Prop17.lean`, lines 20, 32 and 60 to 61, though the lemma's statement
    needs no change) and its representation notes, which keep `centre-given` "as today" for
    III.7, III.8 and III.17 (lines 186, 275 and 354, against question 9): these change with
    those briefs' revisions, by their owners.
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
  the same centre", whose hypotheses section 7 changes. Postulate 3 too, which gives a circle
  about a chosen centre.
- **`centre_unique`,** Generalities 2: the rule asserts existence only.
- **III.9's and III.10's `hypothesis-dropped`, III.24's and III.30's other tags,** and every
  restriction other than the centre.

### Dated correction, 19 October 2026: section 7 before step 6

The coordinator corrects the order frozen on 18 October, under WORKFLOW section 2.

- **Discrepancy:** section 7 waits for step 6 only to avoid reading III.10, III.11 and
  III.13 twice, although its restatement needs neither the centre rule nor the other
  restatements.
- **Current declaration:** section 6, step 6, and section 7, "Order", put section 7 in
  the same pull request as the centre restatements.
- **Corrected declaration:** section 7 lands now, before step 6, by the coordinator's
  order of 19 October. Step 6 reads III.10, III.11 and III.13 again when its own changes
  reach them.
- **Reason:** III.5 and III.6 need not wait for step 6; the cost is the second reading of
  those three records.
- **Consumers affected:** III.5 and III.6, the definitions of cutting and contact within,
  III.10's final step, III.11–III.13's semantic reviews, the overlap audit and catalogue,
  their review records and page prose, the lock and its two hashes, and the generated
  edition. The figures stay as drawn. The [decisions entry](0002-decisions.md#19-october-2026)
  records the work that accompanies this landing.
- **Work that can go on meanwhile:** the remaining steps of section 6 continue under their
  existing dependencies. This correction changes only section 7's place in the order;
  the frozen text below is retained.

## 6. The order of work

*19 October correction: the [section 3 correction](#correction-iii1-19-october-2026)
supersedes the frozen order below: step 5, corrected step 3, step 4 on its own, then
step 6. Section 7 landed earlier; step 4 never shares a train with content it judges.*

A check never lands in the pull request whose code it checks
([WORKFLOW.md](../WORKFLOW.md), section 10), so the guard of section 3 needs a pull request
between the construction it names and the restatement it guards. A pull request of its own
below may land as a branch of its own in a train (WORKFLOW, section 10, "Trains"), never in
a train with content its check judges, and the order holds between trains. The order:

1. **First.** #40 has landed (`tooling/model-law-names`, in train H2, #103): the model's law
   names as `tests/model/laws.toml`, an allow-list for a law's code, and no count left in
   `run.py` or `hyperbolic.py`; so an axiom and its law now land together, in one pull
   request. Then, each in a pull request of its own:
   - **The `[overlap]` kind,** next (question 3): one tooling pull request builds the key
     `kind` together with issue #93, which asks that each record's `[overlap]` carry its
     catalogue kind (states it, gives it at once, supplies a step), in `review/SCHEMA.md`,
     `scripts/heath.py` and both of `render.py`'s displays, with README's scope sentence,
     and the pages regenerated. III.1 takes `kind = "step"`; the other records take the kind
     of their catalogue rows, as #93 settles. It is a check change, with a `/security-review`
     and a decisions entry naming the protected files it changes.
   - **The prototype's rename,** after it and before step 5 (question 12): a `lean` pull
     request of its own, from the owner of `Staging/Stage4b/MixedAngles.lean` (#86),
     renames its theorem `exists_centre (A : Point) : ∃ γ, Centre A γ`, in
     `Elements.MixedAngles`, to `exists_circle_about`, with its fourteen uses in that file
     and the row of `docs/reports/mixed-angles-prototype.md` (line 231) that names it;
     nothing else changes. Within `Elements.MixedAngles`, which opens `Tacit`, the bare name
     means the prototype's theorem, so the rule could not be cited there as
     `exists_centre`; and were the theorem to reach `Elements/` under its name (#57 would
     move it to Book Zero), every proposition file's `exists_centre α` would resolve to it
     and fail. Both were tried in Lean on a small model of the two names.
   - `scripts/negative_tests.py` reads its count from the lock, before step 5. It expects
     "declares 88 axioms, not 87" when it plants one axiom, so the rule's pull request could
     not pass with main's copy at `32eeba5`; #40 did not change it.
   - `review/terms.toml` gains `touching-whole-circles` (question 9), before step 6.
2. **This brief,** challenged (Appendix B) and frozen by the coordinator on 18 October, with
   brief 0006's and brief 0007's revisions and the three lemmas of section 4, approved.
3. **III.1's construction, apart, under today's statement.** `Prop1.construction` goes before
   `Prop1` in `Elements/BookIII/Prop01.lean`, and today's `Prop1`, its hypothesis kept, calls
   it under Euclid's three sentences. No statement changes; III.1's record gains its
   `grouped` passage, and is read again and stamped; FORMALIZATION section 5 gains the
   sentence of section 3, approved (question 14), so that the passage's warrant lands with
   it.
4. **The guard,** on its own: `Audit/Centre.lean`, imported by `Audit.lean`, the pin of
   section 3, with a decisions entry that names it (question 7).
5. **The rule,** in one pull request, the coordinator's own: the axiom with its docstring;
   the lock (`--write-lock`); `tests/model/lock.sha256`; the law's line in `laws.toml` and its
   code in `search.py` and `hyperbolic.py` (section 2); MODEL.md's row and counts; the prose
   of section 4 that goes with the rule; facts.json and the generated pages regenerated; and
   the decisions entry of section 2, quoting the owner. Labels `lean` and `security-review`,
   with a `/security-review` recorded. Nothing uses the rule yet, so no certificate but the
   list of axioms changes. The formal model's package is on main (#98), so this pull request
   also renews `model/lock.sha256` to the new lock, which the model's CI job
   (`formal-model`) compares, and adds `exists_centre`'s round-trip check to
   `model/Check/Hand.lean`, comparing the hand translation with the library's declaration,
   as `model/README.md` ("How the lock ties it") asks; `Model/Euclidean/Centre.lean` stands,
   and `Model/Hand.lean`'s note that the axiom is not yet in the library goes. The model
   package's owner writes those files, and the coordinator carries them in this one pull
   request, so that the lock and the model never disagree on main.
6. **The restatements,** in one pull request, so that each record is read once: every
   statement of section 4 and III.1 of section 3, each moved from `Staging/Centre/` into its
   home; section 7's III.5 and III.6 restated, with `CirclesCut` and `CirclesCut.symm`, the
   changed definition of contact within and `CirclesMeet`'s docstring (the definitions the
   coordinator writes, in the foundations), the lock's entries for them, and
   `tests/model/lock.sha256` and `model/lock.sha256` renewed; every citer's call, III.10's
   last step among them, its route made `modified`; brief 0006's staged files, whose proofs
   (#89, #90) now cite the statements that change ("Other branches", below), and brief
   0007's (`Staging/Stage4b/Prop08.lean` and `Prop17.lean`), or their homes in `Elements/`
   if they have moved by then; `Audit/Overlaps.lean` and its pins; the screen run again; the
   records, read again and stamped by their reviewers, with the semantic reviews of III.11,
   III.12 and III.13 made again by deliberate re-reading, since the meaning of contact
   within moves under their unchanged text and files; the prose of section 4 and of section
   7 that goes with the restatements; `tests/certificate_expectations.json`'s III.1 values,
   which move with the content; `Staging/Centre/` deleted; a decisions entry naming every
   statement changed, which the pre-flight's statement guard asks for, the definition
   changed with the three statements whose meaning moves with it, and each protected file
   changed (`Certificate/FIELDS.md`, `scripts/scaffold_book.py`); and the pages regenerated.
   Before it lands, the whole migration is built on the revision delivered and its
   certificates compared with those this brief gives. Labels `lean` and `security-review`.
   Proofs by Codex sailors, best of two (WORKFLOW, section 5). Most are a line: a call loses
   an argument, or `obtain ⟨O, hO⟩ := h` becomes `obtain ⟨O, hO⟩ := exists_centre α`;
   III.1's correctness is the staged check, moved, and III.5 and III.6 are the staged
   proofs, moved. The real work is III.17 through `Prop1.of_circle`.
7. **Afterwards,** `[tag.centre-given]` leaves `review/terms.toml`, in a pull request of its
   own, since that file is protected.

Steps 3 and 4 may come before or after step 5; steps 1, 3, 4 and 5 all come before step 6.
If a step needs a fact the axioms lack, work on it stops and the case goes to the owner, as
for every stage.

**Other branches.** `lean/iii5-iii6-ending` and `lean/iii5-iii6-euclid` landed together in
#87, which rewrote `Audit/Overlaps.lean`, `docs/reports/overlaps.md` and the records of
III.2, III.5, III.6 and III.12 (with four of Book I's), all of which step 6 edits; section 7
is read against it, and
the guard has a file of its own. `text/overlaps-i2-i3` (#81) and `lean/i45-ii14-full` (#80)
are on main too, and the line references above are to main at `32eeba5`. The formal
model's package (`lean/model-skeleton`, for #73) is on main from #98 (step 5), and
`tooling/model-law-names` is #40 (step 1). In the mixed-angle prototype (#86), besides the
rename, six facts take a centre O that nothing else in their statements mentions:
`surrounds_inside`, `surrounds_outside`, `near_across`, `Segment.exceeds_iff`,
`Segment.nearVertexOpen` and `Segment.fallsShort_iff`. Their proofs are complete and stay
true as they stand; question 2's rule lets the centre go when #57 moves them into
`Elements/`: a note for #57.

Brief 0006's stages 2 to 4 are proved in Staging (#88, #89, #90), their statements keeping
the hypotheses that go until step 6. Their proofs cite statements that change, and step 6
edits each call. In `Staging/Stage3/`: III.21, given `hα`, in `Prop23Point.lean` (lines 77,
87 and 101); `Prop23.point`, given `hAEB` and `hCFD`, in `Prop24.lean` (lines 109 and 110);
III.22, III.24 and `Circumference.whole` and `.eq`, each given a centre as `⟨G, hG⟩`, in
`Prop24.lean` (lines 198 to 229), `Prop26.lean` (lines 85 to 147) and `Prop28.lean` (lines
92, 126, 127 and 141); `Circumference.eq` and III.22, given `hα`, in `CircumferenceAdd.lean`
(lines 35, 36 and 42); and III.24, `Prop24.equalCircles`, `Circumference.whole` and `.eq`,
given the centre clause of `Arc.Drawn`, in `Arcs.lean` (lines 128 and 143 to 150) and
`Prop24.lean` (lines 307 to 313). In `Staging/Stage4/`: III.9 and the restated III.25 in
`Prop25.lean` (lines 65 and 291). Brief 0007's `Staging/Stage4b/Prop08.lean` and
`Prop17.lean`, named in step 6, are proved too (#102), and pass `hABC` and `hBCD` on to
III.8 and III.17 and from one of their statements to another. Question 5's advice not to
use `Arc.Drawn`'s centre clause reached four of the proofs too late: `Arc.eq_of_aligned`
and `Arc.measure_eq_iff` take their centres from it (`Aligned.lean`, lines 59 and 60;
`Arcs.lean`, lines 39, 40, 52 and 53), and `Arc.congruent_iff` and `Prop24.equalMeasure`
hand it on to `Circumference.whole`, `.eq`, the restated III.24 and `Prop24.equalCircles`
(`Arcs.lean`, lines 119 and 120; `Prop24.lean`, lines 296 and 297); the others read the
later clauses by position (`Chord.lean`'s `ha.2.1`, and `Prop24.image`'s `⟨-, hB, hC, -⟩`,
lines 249 and 250), and two proofs build a drawn arc whole (`Prop26.lean`, lines 116 and
117; `Prop25.lean`, line 288). When the clause goes, the first two take `exists_centre` of
each circle, the other two pass nothing once those statements drop their hypotheses, and
each position moves up by one: a line apiece, in step 6, and nothing to prove again.

## 7. III.5 and III.6: cutting and touching as Definition III.3 reads them

*Added on 18 October 2026, after the challenge of sections 1 to 6, and read against main at
`5766311`. Challenged on its own by Astra at `3f00ebf`, which supported the mathematics and
asked for the corrections made here: the catalogue keeps its rows for III.5 and III.6;
circles that cut one another each pass within the other, in the definition as in the
plane; and the account of what the restatement keeps says only what was shown (Appendix B,
"Section 7's challenge"). Frozen with the rest, its questions 15 and 16 decided as
recommended, with `CirclesCut.symm` added at the freeze for Lean users (section 8).*

### The decision, and why

III.5 and III.6 rest on Diagram-segment 2 (`circle_eq`), and the overlap catalogue shows
that, as we state them, they must: a circle drawn twice over, as two circles with one centre
and one radius through the same points, meets our reading of both and shares its centre with
its copy, and every rule we take but Diagram-segment 2 and Circle 4
(`not_same_side_of_circles_meet`) holds of the pair, so any proof of today's statements uses
one of those two ([overlaps.md](../reports/overlaps.md), under III.5 and III.6; a model
argument, checked by hand). The owner asked on 18 October whether there was no way around it,
and the coordinator decided the same day to restate both, so that each says what Euclid's
words say and rests on neither rule. The enunciations, and the definition they turn on, in
Heath's words (`heath/III/05.md`, `06.md` and `front.md`):

> *If two circles cut one another, they will not have the same centre.* (III.5)
>
> *If two circles touch one another, they will not have the same centre.* (III.6)
>
> Circles are said to touch one another which, meeting one another, do not cut one another.
> (Definition III.3)

Today's III.5 reads "cut" as meeting at two points (`CirclesMeet`), with the circles two
(`ABC ≠ CDG`), and today's contact within asks only that the circles meet, be two, and have
no point of the inner outside the outer; the circle drawn twice over does all of that. But
Definition III.3 sets cutting against touching: of circles that meet, those that touch do not
cut. Our definitions of touching already say what not cutting is: touching within, no point
of the inner circle falls outside the outer (`TouchesInternally`); touching without, no point
is within both (`TouchesExternally`). Circles that cut one another, then, cross: each passes
within the other. Of contact within, Heath writes that the definition "must be taken to
imply" that "a circle touching another internally must, immediately before 'meeting' it,
have passed through points *within* the circle that it touches", and that these facts, this
and its like for contact without, "constitute a minimum admission necessary to the proof of
III. 6" (vol. 2, p. 3; checked against the page image, leaf n15). A circle and its copy
neither cross nor pass one within the other. Read so, Euclid's own argument proves both
propositions with neither rule: the straight line he draws "at random" from the supposed
centre is drawn through a point where the one circle passes within the other, and Definition
I.15, with the order of the points on that line, gives "the less to the greater".
`Audit.III_5_crossing` (#87) showed it first, by Definition I.15 and Diagram-segment 4.

What the restatement does not do is take III.5 and III.6 out of the overlap catalogue, and
the brief keeps the two things apart. **Avoidance:** our proofs are Euclid's, from
Definition I.15 and the order of the points on the straight line he draws (Diagram-segment 1
with Common Notion 5, through `len_lt_of_between`), and they use neither Diagram-segment 2
(`circle_eq`) nor Circle 4. **Overlap:** the rules still give the restated propositions at
once. Were two circles about one centre with a point in common, Diagram-segment 2 would make
them one circle, and the point of the one within the other would be within that circle and
on it, which Generalities 4 forbids; for III.6, contact without ends by Generalities 3.
Definition I.15, with Diagram-segment 4 and a law of magnitude, gives the restated III.5 in
three lines as well. Each is "a short proof, from at most three rules, that cites no
proposition", the catalogue's test for "gives it at once"
([overlaps.md](../reports/overlaps.md), "The catalogue"), so the restated propositions keep
their rows, reworded to say both, and the records keep their `[overlap]`, whose notes say
the same. That was the challenge's one blocking finding, and the brief adopts it (question
15); the challenged draft's proposal to replace the rows with a note is withdrawn.

### The statements

As they would read in `Elements` (the staged file has the docstrings in full):

```lean
/-- **Definition III.3**, circles that cut one another: they meet at two points, and each
passes within the other, for a point of `α` is within `β`, and a point of `β` within `α`. -/
def CirclesCut (α β : Circle) : Prop :=
  CirclesMeet α β ∧ (∃ P : Point, OnCircle P α ∧ InsideCircle P β) ∧
    ∃ P : Point, OnCircle P β ∧ InsideCircle P α

theorem CirclesCut.symm {α β : Circle} (h : CirclesCut α β) : CirclesCut β α

/-- If two circles cut one another, they will not have the same centre. -/
theorem Prop5 {E : Point} {ABC CDG : Circle} (hcut : CirclesCut ABC CDG) :
    ¬ (Centre E ABC ∧ Centre E CDG)

/-- **Definition III.3**, contact within: they meet at `C`, `β` has passed within `α`, for a
point of `β` is within `α`, and no point of `β` falls outside `α`. -/
def TouchesInternally (α β : Circle) (C : Point) : Prop :=
  OnCircle C α ∧ OnCircle C β ∧ (∃ P : Point, OnCircle P β ∧ InsideCircle P α) ∧
    ∀ P : Point, OnCircle P β → ¬ OutsideCircle P α

/-- If two circles touch one another, they will not have the same centre. -/
theorem Prop6 {C F : Point} {ABC CDE : Circle} (htouch : CirclesTouch ABC CDE C) :
    ¬ (Centre F ABC ∧ Centre F CDE)
```

- **Cutting, a new word.** `CirclesCut α β` asks that the circles meet at two points and
  that each pass within the other: a point of `α` is within `β`, and a point of `β` within
  `α`. That is crossing, read by our definitions of touching (above), and in the plane it is
  exactly what two different circles that meet at two points do (below): the definition is
  chosen for that equivalence, not for what the proof consumes. It is symmetric by its form,
  as "cut one another" is, and `CirclesCut.symm` says so, proved by exchanging the
  definition's parts; it goes to Book Zero beside `EqualCircles.symm`
  (`Elements/Figure/OnCircles.lean`), so that a citer who holds the circles in the other
  order writes `hcut.symm`. The coordinator asked for a symmetry bridge, or the symmetric
  definition if III.5's proof stayed the same in substance, which it does: it takes one
  point within either way. The brief gives both, since that is the clearer for a Lean user:
  the hypothesis says what the figure has, in either order, and the bridge is a one-line
  lemma under the name Lean users look for, where from a one-way definition it would be a
  theorem of the plane, needing an argument of its own. III.5's argument uses one common
  point, C, and one point within, Euclid's F, a point of ABC which his figure puts within
  CDG, nearer E than G; the second common point and the second point within say which figure
  is meant, as B does in Euclid's setting-out, and go unused. Asked of `α` alone, as the
  challenged draft asked, the definition would be an oriented representation, which the
  challenge accepted under that name while preferring this form (question 15). The two
  common points stay: Euclid's setting-out names both, and with one common point the one-way
  form would admit contact within as well, since the inner of two circles touching within
  has points within the outer. A definition reads more like "cut one another" than the
  hypotheses written out (`CirclesMeet ABC CDG` and the two points within), which would name
  points the enunciation never mentions, and it stands beside its kin: in
  `Elements/Foundations/DefinitionsIII.lean`, after `CirclesTouch`, under Definition III.3,
  whose module note gains circles cutting one another in its list of the words defined
  there.
  It joins `Certificate/axioms.lock` with III.5, the first statement that uses it, through
  `--write-lock`, with `tests/model/lock.sha256` and `model/lock.sha256` renewed; no law of
  either model changes, since no axiom reaches the word. It is
  a word this brief names, so once the brief is frozen the class approval of 18 October
  covers it: "the definitions of every frozen brief, this one's and later ones', are
  approved as a class; each moves with the first approved statement that uses it, and the
  pull request that moves it records it" ([0002-decisions.md](0002-decisions.md), "Brief
  0006 frozen").
- **III.5** reads "cut" as `CirclesCut` and loses `hne : ABC ≠ CDG`, which either point
  within implies: a point within a circle is not on it (Generalities 4). Today's III.5
  gives the restated one (a check), so it claims nothing that today's does not.
- **Contact within, in the definition** (decided, question 16). The point of the inner
  circle within the outer takes the place of the clause `α ≠ β`, which it implies. III.6's
  text does not change, nor does that of any statement: what changes is what touching within
  means, in `CirclesTouch` and in III.6, III.11 and III.13. Contact without
  (`TouchesExternally`) does not change. A changed definition is the coordinator's, approved
  at the freeze; it lands with its lock entry and a decisions entry that names the three
  statements whose meaning moves with it. The definition stays our whole-circle reading
  (brief 0004, "Touching, for circles"), and so does `touching-whole-circles` on the records
  of III.6, III.11 and III.13: Heath prefers to read Definition III.3 locally, the circles
  not cutting at the point of contact, and says the definition must imply the point within;
  the form given here is ours, and the point does not make our reading his.
- **Every user of `TouchesInternally`,** by `git grep` at `4a85d42` (main at `5766311`,
  merged into this brief): `CirclesTouch`, and III.6 through it; III.11
  (`htouch : TouchesInternally ABC ADE A`); III.13 (its first clause, and `htB`); III.13
  restated and `Prop13.internally`, in `Staging/Centre/Restated.lean`; `Audit/screen.py`'s
  list of phrases (line 48); and the descriptions in `scripts/render.py` (lines 568 and
  1659) and `scripts/scaffold_book.py` (line 194, and the signatures of III.11 and III.13).
  No branch on origin adds one. In Lean, III.11 reads the definition in two lines,
  `Prop6 (Or.inl htouch)` for F ≠ G and `obtain ⟨hA₁, hA₂, -, hwithin⟩ := htouch`, which
  discards the third clause; III.13 touches it in one, `⟨hBα, hBβ, ht.2.2.1, ht.2.2.2⟩`,
  which carries it unread to B, and elsewhere reads only the first two. With the point as
  the third clause, all three lines go through as written (two checks in the staged file).
  In a scratch copy at `4a85d42`, not committed, the whole of III.11 and of III.13,
  unchanged but for the staged names, checked, and each lost Diagram-segment 2 from its
  axioms and gained nothing; so did III.12, which cites III.6 for contact without. That is
  evidence for section 7's change alone, from a scratch copy, not a build of the migration:
  the rest of the brief brings the rule that every circle has a centre into III.13, among
  others (section 4), and the whole migration is built, and its certificates compared, on
  the revision delivered ("Order", below).
- **The alternative, not chosen** (question 16): today's definition kept, and the point
  given to III.6 alone, the form the coordinator first asked to be preferred. It stays in
  the staged file only as a check that it is the same theorem as the restated III.6, and
  goes with that file in step 6.

  ```lean
  theorem Prop6 {C F : Point} {ABC CDE : Circle}
      (htouch : (TouchesInternally ABC CDE C ∧ ∃ P : Point, OnCircle P CDE ∧ InsideCircle P ABC) ∨
        (TouchesInternally CDE ABC C ∧ ∃ P : Point, OnCircle P ABC ∧ InsideCircle P CDE) ∨
        TouchesExternally ABC CDE C) :
      ¬ (Centre F ABC ∧ Centre F CDE)
  ```

  It is the same theorem (a check derives it from the staged III.6), and it changes no
  definition. But it does not stay with III.6. III.11 cites III.6 for F ≠ G and cannot
  supply the point, for a circle and its copy touch within by today's definition and have
  one centre: III.11 as stated needs one of the two rules, whatever III.6 says. So III.11
  would call Diagram-segment 2 itself for that step, and its record would gain an overlap;
  III.11 and III.13 would go on resting on the rule, as they do today through III.6; and
  touching within would be read one way in III.6 and another in III.11 and III.13. Heath
  says that the definition must be taken to imply the point, though he gives no definition
  of this form. So the freeze put it there, where III.6, III.11 and III.13 all read it, as
  the brief recommended and Astra supported.

### No configuration Euclid's words admit is lost

The test is the intended plane, the one in which every axiom holds (the note of
`Elements/Foundations/Words.lean`, lines 18 to 28, and [MODEL.md](../../tests/model/MODEL.md),
line 28): a circle is one figure, a centre and a positive radius, and Euclid's two circles
are two figures. The axioms ask a positive radius as well: Points 7 gives a
point of any circle outside every finite list, so no circle is a single point, and Points 8
a point within every circle (`exists_point_on_circle` and `exists_point_inside_circle`, in
`Elements/Foundations/Tacit/Constructions.lean`); and a named centre and a point of its
circle are two points (`ne_of_centre_of_on`), so the radius between them has some length
(`len_pos`).

- **Two different circles that meet at two points cross, each within the other.** Let
  their centres be O and O′ and their radii r and r′, both positive. The centres differ,
  for one centre and a common point make one circle. The common points are two, and lie
  symmetrically about the straight line OO′, so neither is on it, and the triangle of O,
  O′ and a common point gives |r − r′| < OO′ < r + r′. The point of the first circle on
  the ray from O towards O′ is then |OO′ − r| from O′, which is less than r′: it is within
  the second circle. With the circles exchanged, the point of the second on the ray from O′
  towards O is |OO′ − r′| from O, which is less than r: it is within the first. So two
  circles that cut one another in the plane are `CirclesCut`, in either order.
- **A circle touching another within has its other points within.** If two circles meet at
  C, are two, and no point of the inner is outside the outer, then r′ < r and OO′ = r − r′.
  The inner circle's radius r′ is positive, so it has points other than C, and each of them
  is less than r from O: its distance from O is at most OO′ + r′, which is r, and equals r
  only on the ray from O through O′, where the inner circle has the one point C. So two
  circles touching within have the point of the definition. Touching without is as before.

Configuration by configuration (the table is Astra's, from the challenge):

| In the plane | Before and after |
|---|---|
| Two different circles that cross | They cut one another, both before and after, and the new definition holds in either order |
| One point in common, contact within | Not cutting, before or after; touching within, before and after, the new definition's point present |
| One point in common, contact without | Touching without, unchanged |
| One circle within the other, no point in common | Neither cutting nor touching |
| One centre, unequal radii | No point in common: neither |
| A circle and itself | Not two circles: excluded before by III.5's `ABC ≠ CDG` and contact within's `α ≠ β`, now by the point within, since no point of a circle is within it (Generalities 4) |

**What this shows, and what it does not.** In the intended plane the old and the new
hypotheses agree: there they do not part at all. So the restated III.5 and III.6 say what
today's say, and the records of III.5, III.6, III.11 and III.13 stay `full`, with the
representation disclosed (the whole-circle reading of touching, above). That rests on the
plane, not on the staged checks, which go one way only: today's statements give the
restated ones. In an interpretation without the two rules that tell two circles apart, a
circle drawn twice over meets today's hypotheses and not the new ones; that shows that the
readings differ there, not every way in which they could. Nor is a model of every axiom, by
itself, a reading of Euclid's objects: section 1 has a plane with a circle that no point is
the centre of. The intended plane is the test for these figures of Euclid's, and the one
used here.

### What changes

With the definition of contact within that the freeze chose (question 16).

- **The foundations,** the coordinator's: `CirclesCut`, and `TouchesInternally`'s third
  clause, in `DefinitionsIII.lean`; the lock, which gains `CirclesCut` and changes
  `TouchesInternally`'s entry, with `tests/model/lock.sha256` and `model/lock.sha256`
  renewed, no axiom reaching either word; and the decisions entry, naming III.5 and III.6
  restated, III.11 and III.13 whose meaning moves with the definition, and III.10's proof.
  `CirclesCut.symm` goes to Book Zero (`Elements/Figure/OnCircles.lean`). And, a change of
  step 6 decided at the freeze, `CirclesMeet`'s docstring in `Words.lean` (line 98), "Two
  circles that cut one another (in two points)", which a circle meeting itself also
  satisfies, and which would now misname it: it becomes "Two circles that meet at two
  points", with a sentence sending a reader to `CirclesCut` for circles that cut one
  another. The lock holds no docstrings, so that entry stays.
- **III.5,** `Elements/BookIII/Prop05.lean`: the statement and the proof below. Its record:
  the statement note says how "cut" is read (the circles meet at two points and cross, a
  point of ABC within CDG and a point of CDG within ABC, either of which makes them two; the
  proof uses one common point and the first point within), and stays `full`; the route
  stays `euclid`; the `[overlap]` stays on `circle_eq`, with `also =
  ["Tacit.inside_not_on"]` and the kind "gives it at once" of question 3's key, and its note
  says the two things apart (question 15): the proof is Euclid's, from Definition I.15 and
  the order of the points on his straight line, and does not use Diagram-segment 2 or
  Circle 4 (avoidance); Diagram-segment 2 with Generalities 4, and Definition I.15 with
  Diagram-segment 4, give the restated III.5 at once (overlap); the `helper` passage that
  names the rule goes, since the proof no longer calls it; a `carried` passage at "For, if
  possible, let it be E" says that EFG is drawn through F, where the circles cross, one
  straight line from E meeting the circles at two points being all the argument needs; the
  closing `grouped` passage stays.
- **III.6,** `Prop06.lean`: the proof. Its record: the route stays `euclid`; the `[overlap]`
  stays on `circle_eq`, with `also = ["Tacit.centre_inside", "Tacit.inside_not_on"]` and
  the kind "gives it at once", and its note says, as III.5's does, that the proof is
  Euclid's and does not use Diagram-segment 2 or Circle 4 (avoidance), while
  Diagram-segment 2 with Generalities 3 and 4 gives the restated III.6 at once (overlap)
  (question 15); the `helper` passage goes; the `case` passage for contact without, at "For,
  if possible, let it be F", gains a sentence: for contact within, FEB is drawn through a
  point of the inner circle within the outer, the one straight line Heath says is enough
  when he answers J. G. Camerer (vol. 2, p. 13); the `[representation]` takes
  `touching-whole-circles` (section 4), whose meaning then says that the inner circle has
  passed within the outer.
- **III.10,** `Prop10.lean`, cites III.5 for its last step: "therefore the two circles ABC,
  DEF which cut one another have the same centre P: which is impossible. [III. 5]". Circles
  about one centre do not cross, so the restated III.5 cannot serve there; and our III.10 is
  stated for circles that cut or only meet, as Heath observes the proof allows: "There is
  nothing in the demonstration of this proposition which assumes that the circles *cut* one
  another" (vol. 2, p. 23). Its conclusion, that two circles with three points in common are
  one, is false of a circle and its copy, so no proof of it can do without one of the two
  rules. The last line becomes `exact hne (circle_eq hP hP' hB₁ hB₂ rfl)`: with the one
  centre P and the common point B, the circles are one. That is the converse Heath gives
  under III.5: "*If two circles have the same centre and one point in their circumferences
  common, they must coincide altogether*" (vol. 2, p. 12). III.10 no longer imports or cites
  III.5. Its record: the route becomes `modified`, with a `different` passage at "therefore
  the two circles ABC, DEF which cut one another" saying so; its other entries are as
  section 4 leaves them.
- **III.11 and III.13:** no Lean changes. Their records are read again for the definition,
  which neither their fingerprints nor their Lean hashes can show, since neither the text of
  their statements nor their files change, and their semantic reviews are made again by
  deliberate re-reading; the notes on touching within gain the point within.
- **III.12:** nothing but its certificate; its semantic review is made again with III.11's
  and III.13's, since it cites III.6.
- **Certificates** (from the staged proofs and the scratch copy, at `4a85d42`, for section
  7's change alone; the rest of the brief changes some of the same certificates, and the
  migration's are compared before it lands, "Order"): III.5 and III.6 go from 16 tacit
  rules each to 13, losing Diagram-segment 2, Points 1, Between 6 and
  Between 7 and gaining Generalities 4, with Definition I.15 and Postulate 1 as before;
  III.11, III.12 and III.13 lose Diagram-segment 2 and nothing else; III.10 keeps its 64
  axioms and calls Diagram-segment 2 itself; III.23 does not change. In `Elements`,
  Diagram-segment 2 then serves exactly where a conclusion says that two circles are one:
  III.10, and III.23 through it; it first enters at III.10. The staged work uses it the same
  way, in brief 0006's arcs and restated III.25 and in one step of the mixed-angle
  prototype.
- **The catalogue,** [overlaps.md](../reports/overlaps.md), with question 15: its rows for
  III.5 and III.6 stay, for the restated propositions, reworded to say both things: our
  proofs are Euclid's, from Definition I.15 and the order of the points on his straight
  line, and do not use `circle_eq` (avoidance), while `circle_eq`, with Generalities 4 (and
  3, for III.6), gives both restated propositions at once, and Definition I.15 with the
  diagram rule Diagram-segment 4 gives the restated III.5 at once (overlap). III.5:
  Diagram-segment 2, with Generalities 4, gives it at once (circles about one centre
  through one point are one circle, and the point of the one within the other would then
  be within that circle and on it); and a second row, Diagram-segment 4, with Definition
  I.15 and a law of magnitude, gives it at once too (the point within is nearer the centre
  than the common point, and yet as far from it). III.6: Diagram-segment 2, with
  Generalities 3 and 4, gives it at once, Generalities 3 ending contact without.
  Diagram-segment 4's proof does not make a row for III.6: with contact without it takes
  four rules. "First enters" is read from the migrated facts.json, which since #65 keeps a
  proof's own rules (`own_axioms`) apart from those it reaches through a lemma
  (`inherited`): Diagram-segment 2 at III.10, called there (above); and, by today's
  facts.json, Generalities 3 at I.1, called there, Generalities 4 at I.22, through Book
  Zero's `ne_of_centre_of_on`, and Diagram-segment 4 at I.3, through `outside_of_len_gt`.
  The first proofs to call those two themselves are III.7 and III.17, so the notes under the
  rows name the lemmas, as the catalogue's notes do for a rule that comes through one, and
  its sentence that "Each first user in the table calls its rule itself" changes with them.
  The notes under III.5 and III.6 say that the proofs follow Euclid and use neither
  Diagram-segment 2 nor Circle 4, that the rows record what the rules contain, not what the
  proofs rest on, and that the twin-circle argument now concerns today's readings and
  Heath's combined enunciation, "*If the circumferences of two circles meet at a point they
  cannot have the same centre*" (vol. 2, p. 12), circles that merely meet, which
  Diagram-segment 2 gives at once and which carries III.10's last step: a note, not a row,
  since it is no proposition of ours. "The rows checked", the small certificates and the
  account of the screen follow, and the screen runs again in step 6. In
  `Audit/Overlaps.lean`, `III_5`, `III_6` and `III_5_crossing` are retyped to the restated
  propositions, with their pins. Their proofs, checked by Lean against the staged statements
  in a scratch file at this revision (not committed), are

  ```lean
  theorem III_5 : type_of% @Elements.BookIII.Prop5 :=
    fun ⟨⟨_, _, _, _, _, hC₁, hC₂⟩, ⟨_, hP₁, hP₂⟩, _⟩ ⟨hE₁, hE₂⟩ =>
      inside_not_on (circle_eq hE₁ hE₂ hC₁ hC₂ rfl ▸ hP₂) hP₁

  theorem III_6 : type_of% @Elements.BookIII.Prop6 := by
    rintro C F ABC CDE (⟨hC₁, hC₂, ⟨P, hP, hP_in⟩, -⟩ | ⟨hC₂, hC₁, ⟨P, hP, hP_in⟩, -⟩ |
      ⟨-, -, hout⟩) ⟨hF₁, hF₂⟩
    · exact inside_not_on (circle_eq hF₂ hF₁ hC₂ hC₁ rfl ▸ hP_in) hP
    · exact inside_not_on (circle_eq hF₁ hF₂ hC₁ hC₂ rfl ▸ hP_in) hP
    · exact hout F (centre_inside hF₁) (centre_inside hF₂)

  theorem III_5_crossing : type_of% @Elements.BookIII.Prop5 := by
    rintro E ABC CDG ⟨⟨_, C, _, _, _, hC₁, hC₂⟩, -, ⟨P, hP₂, hP₁⟩⟩ ⟨hE₁, hE₂⟩
    have h : ‖E P‖ < ‖E C‖ := len_lt_of_inside hE₁ hC₁ hP₁
    rw [Definition15 hE₂ hP₂ hC₂] at h
    exact lt_irrefl _ h
  ```

  and Lean reports, besides `Classical.choice`: for `III_5`, `circle_eq` and
  `inside_not_on`; for `III_6`, those two and `centre_inside`; for `III_5_crossing`,
  `Definition15`, `len_lt_of_inside` and `lt_irrefl`. `III_5_crossing` takes the second
  point within, a point of CDG within ABC, as #87's lemma took its point. In the same
  scratch file, `grind`, given Diagram-segment 2, Generalities 4 and the two definitions,
  closes the restated III.5.
- **Pages and prose,** by the owner of each, with step 6: the mishnah of III.5 (its
  paragraph on `circle_eq`, and its last sentence, that the proof proves Heath's combined
  enunciation, which is no longer so), of III.6 (Camerer's question, now answered with the
  words of Heath's note on Definition III.3 that name III.6, whose place is this page), of
  III.10 ("B and G give the meeting that III.5 needs") and of III.11 (its account of
  `TouchesInternally`); Book III's introduction (its paragraph on words);
  [gaps-book-III.md](../reports/gaps-book-III.md), under III.5, III.6 and III.10;
  FORMALIZATION section 3, the row for circles touching and a row for circles cutting, with
  no tag, since it is no limit; a dated note in [brief 0004](0004-book-III.md) at Definition
  3 (line 36), "Touching, for circles" (line 51) and the rows of III.5, III.6 and III.10 in
  its table of exceptions (lines 358, 359 and 363); `scripts/render.py` (lines 568 and
  1659), `scripts/scaffold_book.py` (line 194, and III.5's signature, line 216) and
  `Audit/screen.py`'s phrases (line 48), which gain `CirclesCut`. The figures do not change:
  in each, the point of the one circle within the other is the nearer, F in III.5 and E in
  III.6, as in Heath's.

### The proofs, staged

`Staging/Centre/Crossing.lean`, in this brief's layout (Appendix A): `CirclesCut` with
`CirclesCut.symm`, `TouchesInternally` and `CirclesTouch` in `Elements.Staging.Centre`,
since today's `TouchesInternally` and `CirclesTouch` are still declared, and III.5 and III.6
in `Elements.BookIII.Staging.Centre`, each proved under Heath's sentences as its home will
have them:

- **III.5.** The cutting gives F, a point of ABC within CDG. EC is drawn for the eye; EFG
  is drawn from E through F and, produced beyond F, meets CDG at G (Intersections 5,
  `line_circle_beyond`, since F is within CDG). EC is equal to EF and to EG, by Definition
  I.15, and F, between E and G, makes EF the less (Diagram-segment 1 and Common Notion 5,
  `len_lt_of_between`). This is #87's ending without its tacit step: there F and G were
  shown two by `circle_eq` and ordered on the ray by Henry Savile's argument; here the
  drawing gives both.
- **III.6.** Contact without ends at once, as today (Generalities 3). For contact within,
  FEB is drawn through the point of the inner circle within the outer and produced to the
  outer, and whichever of E and B is the nearer F gives the less, either circle the inner.
- **What they rest on.** `#print axioms` gives, for each, at `4a85d42` and again at this
  revision: `Definition15`, `Postulate1` and thirteen tacit rules, `add_comm`,
  `add_lt_add_right`, `add_zero`,
  `between_symm`, `centre_inside`, `eq_of_len_eq_zero`, `inside_not_on`,
  `len_add_of_between`, `line_circle_beyond`, `lt_irrefl`, `lt_trichotomy`, `ne_of_between`
  and `not_lt_zero`, with Lean's `Classical.choice`: neither `circle_eq` nor
  `not_same_side_of_circles_meet`. At the end of the file both lists are pinned with
  `#guard_msgs`, as `Audit/Overlaps.lean` pins its lemmas, so that `lake build Staging` fails
  if either changes; with `circle_eq` planted in III.5's proof, or `sorry` in III.6's, it
  fails. They are pins, as section 3's guard now is too, because `tooling/forbidden-scan`
  (issue #39), landing soon, refuses `#eval` and its kin in `Staging/` and `Audit/`
  (question 7). What the pins show is the names of these two declarations' axioms, whole:
  they would catch `circle_eq`, Circle 4 or `sorryAx` entering. They do not check the
  reading of the statements, the statements of the axioms, the other declarations in the
  file, or whether a shorter proof exists from other rules, which one does (above, "What
  changes", the catalogue). `lake build Staging` runs them, and CI runs it; the default
  `lake build` does not.
- **What they leave unused.** III.5 uses neither B, nor its incidences, nor B ≠ C, nor the
  point of CDG within ABC; III.6's contact within does not use the clause that no point of
  the inner circle is outside the outer; contact without uses no point of contact. Those
  clauses say which figure is meant, and ordinary circles that cross or touch satisfy them:
  no hypothesis is vacuous, and none is used artificially.
- **The bridge.** `CirclesCut.symm`, proved by exchanging the definition's parts; Lean
  reports no axiom for it.
- **The checks** (checked by Lean): circles that cut one another are two and meet at two
  points; contact within, as decided, is today's with the point; today's III.5 and III.6
  give the restated ones, a check that runs one way only (the other way holds in the plane,
  above, and is not checked); III.6 written the alternative's way, not chosen, is the same
  theorem; III.11's two lines and III.13's one go through against the definition; and
  III.10's last step, as planned, closes. Nothing in the file is `sorry`.
- **Their standing.** The two proofs are a statement's own, made at the coordinator's
  direction; like `Prop1.construction` and `Centre.every`, they rest on no stub, and the
  freeze approved them as staged facts (question 13), with `CirclesCut.symm`.

### Order

The restatement needs neither #40 nor the rule. Decided: it lands in step 6's pull
request, so that the records of III.10, III.11 and III.13, which section 4 changes too, are
read once (question 10's reason), and since `Audit/Overlaps.lean`, the catalogue and the
screen's run change with both. Before it lands, the whole migration is built on the
revision delivered and its certificates compared with those this section gives; III.5 and
III.6 keep the route `euclid`, III.10 takes `modified`, and the semantic reviews of III.11,
III.12 and III.13 are made again, though their fingerprints do not change.
`Staging/Centre/` is deleted there, this file with it. The definitions are the
coordinator's to write, in `Elements/Foundations/`, carried in that pull request as step 5
carries the model's files. Branches in flight touch the same files:
`lean/circle2-out` (#60) changes the proofs of III.10, III.11 and III.12 (not their calls of
III.5 and III.6) and `Audit/Overlaps.lean`; `text/screen-rows` and `tooling/screen-unfold`,
the screen and the catalogue. `text/overlaps-own`, which also changed the catalogue, landed
in train D1 (#104). Step 6 starts from main after them.

## 8. The decisions, at the freeze

The coordinator froze the brief on 18 October 2026 and decided every question as the brief
recommended, with what three of the lines below add: question 3's key is built together with
issue #93; question 7's guard is a pin, since the forbidden-command scan refuses `#eval`;
and question 15's symmetry is a named lemma as well as the definition's form. Astra's answer
to the draft at `afe0ee9` took the same side on questions 1 to 6, 8 and 10, and on question
9's removal of the tag; on question 7 it endorsed a pin of the whole list of axioms, which
the guard now is; and it asked for the lemmas of question 11. Questions 12 to 14 arose after
that challenge. Astra's challenge of section 7, at `3f00ebf`, supported question 16 and
changed two of question 15's three recommendations before the freeze (Appendix B).

### Each decision

*19 October correction: question 7 below is retained as frozen. The
[section 3 correction](#correction-iii1-19-october-2026) admits `Tacit.exists_centre`
and requires Circle 2, Circle 3, `centre_unique` and `sorryAx` to be absent at each renewal.*

1. **Decided:** the rule is `Tacit.exists_centre`, in `Tacit/Constructions.lean`, a tacit
   rule of our own, with a pointer to it in the opening note of `Definitions.lean`.
2. **Decided, as a standing rule for this brief and later ones:** a named centre that
   appears nowhere else in the statement is dropped, and one that appears anywhere else is
   kept. It is the reading of the owner's approval, "approved, as Astra recommends", since
   Astra's table on issue #59 keeps `Centre E α` only where "E occurs in the geometry as
   the centre"; step 6's decisions entry states it in these words.
3. **Decided:** `[overlap]` gains a `kind` (states it, gives it at once, supplies a step),
   built together with issue #93 in one tooling pull request landed before the rule; III.1
   takes `kind = "step"`.
4. **Decided:** III.33's conclusion loses `∃ O, Centre O AEB`.
5. **Decided:** `Arc.Drawn`'s centre clause goes once the rule is there; the four staged
   proofs that use it change by a line each in step 6.
6. **Decided:** `Prop1.of_circle` is a lemma after the porism, with no certificate entry,
   under that name.
7. **Decided:** the guard is `Audit/Centre.lean`, on its own (step 4): the construction's
   type fixed and its axioms pinned with `#guard_msgs`, each renewal read for
   `exists_centre`, `centre_unique` and `sorryAx`.
8. **Decided:** III.17 takes its centre by `Prop1.of_circle`, under Euclid's "[III. 1]".
9. **Decided:** `centre-given` leaves all 31 records, the 19 where it is the only tag
   rehomed as section 4's table says, with `touching-whole-circles` landed first.
10. **Decided:** the restatements land in one pull request, after steps 1 to 5.
11. **Decided:** `Prop13.internally`, `Prop13.externally` and `Centre.every` are approved.
12. **Decided:** the prototype's `exists_centre` becomes `exists_circle_about`, a name
    approved at the freeze, in a `lean` pull request of its own before the rule.
13. **Decided:** `Prop1.construction`, `Centre.every`, the restated III.5 and III.6, and
    `CirclesCut.symm` stand in Staging as approved staged facts resting on no stub.
14. **Decided:** FORMALIZATION section 5 gains the sentence on a construction core kept
    apart, with step 3.
15. **Decided:** "cut" is read as crossing, `CirclesCut` asking a point of each circle within
    the other, with `CirclesCut.symm`; the catalogue rows and the records' `[overlap]` for
    III.5 and III.6 stay, reworded to say avoidance by our proofs and overlap by the rules;
    III.10's last step takes `circle_eq`, its route `modified`; `CirclesMeet`'s docstring is
    clarified in step 6.
16. **Decided:** contact within takes the strengthened definition, a point of the inner
    circle within the outer in place of `α ≠ β`, with `touching-whole-circles` kept; the
    form for III.6 alone stays only as a staged check.

### The order of landing

*19 October correction: the [section 3 correction](#correction-iii1-19-october-2026)
replaces this order and its closing summary. Step 5 precedes corrected step 3; step 4
lands separately between step 3 and step 6, never in their content train. Section 7 has
already landed.*

1. **#40,** the model's law names as data: landed, in train H2 (#103).
2. **The `[overlap]` kind,** one tooling pull request with issue #93 (question 3).
3. **The prototype's rename** to `exists_circle_about` (question 12).
4. **The rule** (step 5), the coordinator's own pull request: the axiom; its lock entry;
   the hashes, `tests/model/lock.sha256` and `model/lock.sha256`; the law, in `laws.toml`,
   `search.py` and `hyperbolic.py`, with the formal model's round-trip check; MODEL.md's
   row and counts; and the decisions entry quoting the owner.
5. **The restatements** (step 6): every statement of section 4 and III.1; III.5 and III.6
   restated, with `CirclesCut` and `CirclesCut.symm`; the definition change of contact
   within; III.10's route `modified`; and the deliberate re-reading of III.11 and III.13,
   with III.12, whose meaning moves while their text and files stay.

Beside these, each on its own as section 6 says: the negative tests' count read from the
lock, before the rule; `touching-whole-circles` in `review/terms.toml`, before the
restatements; III.1's construction apart (step 3) and the guard (step 4), before the
restatements; and, last, `[tag.centre-given]` leaves `review/terms.toml` (step 7).

### The questions, as weighed

Each question as it was put to the coordinator, with its reasons and alternatives, and
marked with its decision.

1. **Where the rule sits.** *Decided as recommended.* Recommended:
   `Tacit/Constructions.lean`, as `Tacit.exists_centre`, beside the other rules that a point
   exists. Weighed against a home beside Definition 15, as the challenge asked:
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
2. **A named centre that nothing else mentions.** *Decided as recommended, as a standing
   rule.* `Prop25.complete`'s E and `EqualCircles.refl`'s G are named, but appear nowhere
   else in their statements. Recommended, as a rule for this brief and later ones: a named
   centre that appears nowhere else in the statement is dropped, since it asks only that a
   centre exist; one that appears anywhere else is kept. This reads the owner's "those that
   name the centre keep it" by its substance; by its letter the two would stay. The
   coordinator reads it as the owner's approval itself, "approved, as Astra recommends":
   Astra's table on issue #59 keeps `Centre E α` only where "E occurs in the geometry as the
   centre", and removes an input that is "merely `∃ O, Centre O α`". `EqualCircles.refl`'s
   point P goes with it, by Points 7. The prototype's six facts of section 6 come under the
   same rule when #57 moves them. Since it reads the owner's words beyond their letter, the
   decisions entry of step 6 states it as a standing rule, in those words.
3. **The line and the summary for III.1.** *Decided as recommended, built together with
   issue #93.* Recommended: an optional key in `[overlap]`, `kind = "step"`, after the
   catalogue's "supplies a step", for a rule that carries one step of the proof and does not
   contain the proposition, written as section 3 says in both of `render.py`'s displays.
   `heath.py` accepts only that value and requires a `note` with it, and `review/SCHEMA.md`
   documents it. `render.py` has no tests of its own, so the pull request shows both
   displays from an in-memory III.1 record with the key, as Astra's probe did. It is a check
   change (`review/SCHEMA.md`, `scripts/`), landed first, on its own. III.1 alone takes it:
   I.7 and I.23, whose catalogue rows are also "supplies a step", keep "contains", since
   there the rule carries the proposition's content, in the catalogue's words, and their
   audit lemmas prove the propositions from the rules. The alternative is no `[overlap]` for
   III.1, the note in its statement row and the catalogue only. *At the freeze:* issue #93,
   filed after this question was written, asks that every record's `[overlap]` carry its
   catalogue kind (states it, gives it at once, supplies a step) and that the status line
   and README's sentence be worded by it, since for I.2, I.3, I.7 and I.23 they say "contains
   it too" where the catalogue says only that the rule supplies a step. The coordinator
   decided that the key is built together with #93, in one tooling pull request landed
   before the rule (section 6, step 1). So `heath.py` accepts the three kinds, not "step"
   alone; III.1 takes `kind = "step"`; and the other records, I.7 and I.23 among them, take
   the kinds of their catalogue rows, as #93 settles, in place of "III.1 alone".
4. **III.33's clause.** *Decided as recommended.* Its conclusion says that the circle
   described has a centre, so that a citer could hand it on. Recommended: drop it, since it
   adds nothing once every circle has one; it is our clause, not Euclid's. Keeping it costs
   nothing but the question a reader would ask.
5. **`Arc.Drawn`.** *Decided as recommended.* Recommended: its centre clause goes, in brief
   0006's file, before the definition joins the foundations if it has not yet, with its
   users listed in section 4; after, it is a change of definition, with its lock entry and
   decisions entry. Either way the clause goes only once the rule is there to stand in for
   it, and the stage 3 proofs under way should not use it, so that its going breaks none.
   *At the freeze:* the stage 3 proofs had landed (#89), four of them using the clause, and
   section 4 lists six users; each changes by a line in step 6 (section 6, "Other
   branches").
6. **`Prop1.of_circle`, a lemma or a companion.** *Decided as recommended.* Recommended: a
   lemma, after the porism, with no certificate entry, as for `Prop17.inside`: it
   generalizes no clause. III.1's overlap note makes it findable from the page, and section
   3 gives its closure, 58 rules. A companion would show it on the page with its own
   certificate. The name is kept: as in Lean's `of_` names, it says what it is given, a
   circle, as brief 0006's `Prop25.of_circle` is given the circle rather than the segment. A
   distinct name, such as `Prop1.any_chord`, is the alternative if the coordinator prefers.
7. **The guard.** *Decided: the guard, as a pin.* Recommended: the targeted check of
   section 3, with the construction's type fixed beside it. A `#guard_msgs` pin of the
   construction's whole list of axioms (62 names) would catch the same names, but must be
   renewed whenever a Book I proof beneath it changes, and a renewal could carry an added
   name in a long diff. A companion with a certificate expectation (`excludes`) is not open
   to us: a companion comes after its proposition, which may not cite it, and `Prop1` cites
   the construction. Keeping the construction inline, as today, reads more closely as
   Euclid, and leaves the separation to review alone. (Added with section 7:
   `tooling/forbidden-scan` refuses `#eval` in `Audit/` and `Staging/` as well as
   `Elements/`.) *At the freeze:* the scan (issue #39) is landing soon, and refuses every
   command that runs code as a file is built, so a targeted check cannot be written in
   `Audit/`. The coordinator decided the guard in its own file and pull request (step 4),
   with the construction's type fixed, as a `#guard_msgs` pin, as `Crossing.lean` pins
   III.5 and III.6 (section 3 gives it, tried against the staged construction); each renewal
   is read for `Tacit.exists_centre`, `Tacit.centre_unique` and `sorryAx`, and step 4's
   decisions entry names the guard. Whether `Audit/` becomes a protected path, as Astra
   suggested, is a later question of policy, outside this brief.
8. **III.17.** *Decided as recommended.* Recommended: its proof takes the centre by
   `Prop1.of_circle`, under Euclid's "[III. 1]", then draws EA and takes D on it, which
   removes today's search for two points through a given centre and its use of
   `centre_unique`. The smallest change takes the centre from the rule and keeps the search.
9. **The tag.** *Decided as recommended.* Recommended: `centre-given` leaves all 31 records,
   and the 19 records in which it is the only tag are rehomed as section 4's table says,
   with a new tag, `touching-whole-circles`, for III.11–III.13. Rejected: keeping
   `centre-given` on the twelve that name a centre, with a new meaning, since a named centre
   is no difference from Euclid's words; and letting `[representation]` carry a note with no
   tag, which would weaken a schema check to let this change pass.
10. **One pull request or several, for the restatements.** *Decided as recommended.*
    Recommended: one, after steps 1 to 5. Each change is small, the citers of III.1, III.21
    and III.22 run through most of Book III, and a record touched twice would be read twice.
11. **The three lemmas of section 4.** *Decided as recommended.* Recommended: approve
    `Prop13.internally`, `Prop13.externally` and `Centre.every` with this brief, so that they
    land with the restatements and no Lean user ever passes `(ACK := α)`.
12. **The prototype's rename, and who makes it.** *Decided as recommended; the name
    approved at the freeze.* Recommended: a `lean` pull request of its own, from the owner of
    `Staging/Stage4b/MixedAngles.lean`, landed before the rule (section 6, step 1), renaming
    the theorem to `exists_circle_about`, a name that says what it gives: a circle about A,
    by Postulate 3. The coordinator, who approved the prototype, approves the new name, with
    this brief or in that pull request, whichever comes first: with this brief, as it fell
    out. The alternative is to carry the rename in the rule's own pull request, as step 5
    carries the model's files; a pull request of its own keeps the rule's to the rule, and
    lets #57 build on the new name at once.
13. **The proofs staged here.** *Decided as recommended, with `CirclesCut.symm`.* WORKFLOW
    section 2, "What proofs
    `Staging/` may hold", which reached main after this brief's base, has a staged
    statement's own proof wait for its brief's approval. Most proofs here are derivations,
    which it allows: the checks, `Prop1.of_circle` from the staged III.1, and III.13's two
    lemmas from the staged III.13, which Appendix A says prove nothing until their stubs are
    proved. Two are a statement's
    own: `Prop1.construction`, by today's construction steps, and `Centre.every`, from
    `centre_unique`; section 7 adds two more, the restated III.5 and III.6, proved by
    Euclid's argument at the coordinator's direction. Recommended: the freeze approves the
    four as staged facts resting on no stub, which the same section then lets stand, proved
    in place, until the steps that move them (steps 3 and 6). The freeze approved them, and
    with them `CirclesCut.symm`, added at the freeze (question 15), which rests on no axiom.
    The alternative is to make them `sorry` until the freeze, at the cost of the first check
    of III.1 and the guard's trial, which use the construction, and of section 7's evidence
    that III.5 and III.6 need neither `circle_eq` nor Circle 4.
14. **FORMALIZATION section 5's sentence.** *Decided as recommended.* Recommended: approve the
    sentence of section 3 on a construction core kept apart, landed with step 3, so that the
    first `grouped` passage naming a construction has its warrant on main, and a later book's
    constructions can follow it. The alternative is III.1's record alone, citing
    FORMALIZATION section 4.
15. **III.5 and III.6, read as Definition III.3 reads cutting.** *Decided as recommended,
    with `CirclesCut.symm` added and the rows reworded.* Does reading "cut" as crossing, and
    contact within with a point of the inner circle within the outer, say what Euclid's
    words say, and no more (section 7)? Astra's challenge at `3f00ebf` found that it does in
    the intended plane, with the corrections this revision makes (Appendix B). Three parts:
    - *One way, or both.* Recommended, after the challenge: both. `CirclesCut α β` asks for
      a point of `α` within `β` and a point of `β` within `α`, which is what circles that
      cross do in the plane, and is symmetric by its form, as "cut one another" is. III.5's
      proof uses one point within, and the other says which figure is meant, as B does.
      III.5 has no citer once III.10 stops citing it, so today no proof has to supply the
      second point. The challenged draft asked for one way only, which the challenge
      accepted as an explicitly oriented representation, while preferring both, or a
      proved bridge from one way to the other; a bridge would be a lemma of its own, with a
      proof the brief does not have. Asking for either way is a third form, symmetric too,
      at the cost of a second case in III.5. *At the freeze:* the coordinator asked for a
      bridge `CirclesCut α β → CirclesCut β α`, stated and proved, or the symmetric
      definition if III.5's proof stayed the same in substance, the clearer for Lean users.
      It does, so the definition stays symmetric, and its symmetry is stated and proved as
      well, `CirclesCut.symm`, beside `EqualCircles.symm` (section 7, "Cutting, a new
      word").
    - *Still an overlap?* Yes. Recommended, after the challenge: the catalogue keeps its
      rows, for the restated propositions, and the records keep their `[overlap]` (section
      7, "What changes"). Diagram-segment 2 with Generalities 4 gives the restated III.5 in
      a line, and with Generalities 3 as well the restated III.6; Diagram-segment 4 with
      Definition I.15 and a law of magnitude gives the restated III.5 in three (each
      checked by Lean in a scratch file at this revision). Each is "a short proof, from at
      most three rules, that cites no proposition". The challenged draft recommended a note
      in place of the rows, since Diagram-segment 4's proof is Euclid's argument and the
      screen's `grind` did not find it. The challenge rejected that under the catalogue's
      test, and the brief agrees: a search that fails does not show that no proof exists,
      and Diagram-segment 2's proofs stand whatever is said of Diagram-segment 4's. So the
      proofs avoid the rules, and the catalogue records the overlap. *At the freeze:* the
      rows stay, reworded to say both: our proofs are Euclid's, from Definition I.15 and the
      order of the points on his straight line, and do not use `circle_eq` (avoidance),
      while `circle_eq`, with Generalities 4 (and 3, for III.6), gives both restated
      propositions at once, and Definition I.15 with Diagram-segment 4 gives the restated
      III.5 at once (overlap); the records' overlap notes say the same, and the proposal of
      a note in place of the rows is dropped. The alternative is a different test for the
      catalogue, defined and applied to every row: a question for the catalogue's owner, not
      an exception made here. III.6's contact without, which Generalities 3 with our
      definition of touching without ends at once, is the case Euclid leaves to the reader:
      its `case` passage stays, and III.6's row covers it.
    - *III.10's last step.* Recommended: Diagram-segment 2, with the route `modified`
      (section 7), and the challenge agreed. Circles about one centre do not cross, so the
      restated III.5 cannot serve; splitting the step into circles that cross, for which
      III.5 would, and the rest, for which the rule would, cites III.5 only to match
      Heath's bracket, since the rule ends both cases, and FORMALIZATION section 5 forbids
      that ("No dummy citations").
16. **Contact within: the definition, or III.6 alone.** *Decided as recommended: the
    definition.* Recommended: the definition, `TouchesInternally` with a point of the inner
    circle within the outer in place of `α ≠ β` (section 7). Heath says the definition must
    be taken to imply that point; no user breaks; and with it III.11 and III.13 rest on
    neither rule, as III.12 does with either form, and touching within means one thing
    throughout. The alternative, the form the coordinator
    asked to be preferred, gives the point to III.6's statement alone and changes no
    definition, at the cost that III.11 calls Diagram-segment 2 itself, with a new overlap,
    and III.11 and III.13 keep resting on it. If the definition is chosen, the meaning of
    `touching-whole-circles` (section 4), which lands in step 1, says that the inner circle
    has passed within the outer. The challenge supported the definition, provided that
    disclosure stays, as it does: the definition remains our whole-circle reading, and
    Heath's own is local. *At the freeze:* the form for III.6 alone stays only as a check in
    the staged file, and goes with it.

## Appendix A: what is staged, and why

**19 October 2026, after step 6.** This appendix records the former staging layout.
All centre restatements now live in `Elements/` or `Audit/`; the last two files,
`Staging/Centre/Restated.lean` and `Staging/Centre/Brief0006.lean`, are deleted, and
there is no live import of that directory. `Staging/Halves/Prop30.lean` is a separate
proposal awaiting the owner's approval, with `sorry` and no companion registration.
**21 October 2026.** `Prop30.halves` is no longer staged: the owner approved it on 20
October 2026, and it is proved in `Elements/BookIII/Prop30.lean` as the companion "III.30
halves".

The rule cannot be added before its pull request, so no staged statement can be proved from
it. Each new statement is staged with `sorry`, and the rule's content enters only as a
hypothesis of a check, named `exists_centre`, so that the same words refer to the rule once
it lands. Staging, rather than code blocks in this brief, is for the checks: they show that
each new statement is well formed, that it says what today's says given the rule, and so
that it needs no new mathematics, and, for III.1, that the construction and the correctness
fit. The checks of brief 0006's and brief 0007's statements show that the interfaces agree,
not that the restated forms are proved: they are `sorry` here, though both briefs' own
statements are now proved in their staged files (#88 to #90, and #102), proofs that step 6
carries over a line at a time (section 6, "Other branches"). The names sit in
`Elements.BookIII.Staging.Centre` (and `Elements.Staging.Centre` for Book Zero and the
definition), not `Elements.BookIII.Staging`, where brief 0006's restated III.24 and III.25
already are; `Centre.every` is declared at its future name, `Elements.Centre.every`, so that
the check can use it as `hO.every`. `Staging.lean`'s imports are the integrator's and are
left as they are; `lake build Staging` builds the folder by its glob.

Under WORKFLOW section 2, "What proofs `Staging/` may hold", most proofs here derive one
staged statement from others, and prove nothing until the stubs they rest on are proved:
the checks, `Prop1.of_circle` from the staged III.1, and `Prop13.internally` and
`Prop13.externally` from the staged III.13. Four are a statement's own and rest on no stub,
`Prop1.construction`, `Centre.every`, and section 7's III.5 and III.6, and a fifth,
`CirclesCut.symm`, rests on no axiom at all; they stand on the freeze's approval (question
13).

Section 7's file stands apart from the rule: nothing in it waits on `exists_centre`, its two
statements and `CirclesCut.symm` are proved, and its three definitions sit in
`Elements.Staging.Centre`, since today's `TouchesInternally` and `CirclesTouch` are still
declared under the names they will replace.

| File | What it holds |
|---|---|
| `Staging/Centre/Prop01.lean` | `Prop1.construction`, proved, with the right angles ADC and BDC; III.1 restated; a check proving it from the construction and the rule's content; a check that today's III.1 follows; `Prop1.of_circle`, proved from the staged III.1 |
| `Staging/Centre/Restated.lean` | the other eighteen propositions, III.33, the three steps of `Circumferences.lean` and `EqualCircles.refl`, each with its two checks; `Prop13.internally` and `Prop13.externally`, proved from the staged III.13, with a check that they give it back; `Centre.every`, proved, with a check against the restated III.4 |
| `Staging/Centre/Brief0006.lean` | brief 0006's six statements and `Arc.Drawn` without the centre, with their checks, and the two checks that `Prop24.equalCircles` and `Prop25.of_circle` still have today's III.24 and III.25, restated |
| `Staging/Centre/Brief0007.lean` | brief 0007's three statements without the centre, `Prop8.partner`, `Prop8.general` and `Prop17.general`, with their checks, and the two checks that III.8 and III.17, restated, still follow from `Prop8.general` and `Prop17.general` |
| `Staging/Centre/Crossing.lean` | section 7: `CirclesCut` and `CirclesCut.symm`, contact within with the point of the inner circle within the outer, and `CirclesTouch` over it; III.5 and III.6 restated and proved; eight checks; and the axioms of each, pinned, with neither `circle_eq` nor Circle 4 nor `sorry` among them |

## Appendix B: the challenge, finding by finding

### Sections 1 to 6

Astra's answer to the draft at `afe0ee9`, with its bosun's triage, and the Claude
challenger's findings at the same commit. Every finding was checked against the repository
before it was applied.

| Finding | Source | What was done |
|---|---|---|
| `render.py` says "already contains the proposition" in the book's summary as well as under the enunciation; `kind = "step"` must reach both, the record block and the schema's validation | Astra (answers 5, 7; question 3), triage | Both displays named, with their wording (section 3, question 3); the key in the record block; `heath.py` accepts only "step" and requires a note; III.1 alone takes it. At the freeze the key is built together with issue #93, in one tooling pull request landed before the rule: `heath.py` accepts the three kinds (states it, gives it at once, supplies a step), III.1 takes `kind = "step"`, and the other records take their catalogue rows' kinds (question 3) |
| The guard sat beside the code it checks, against WORKFLOW section 10 | Astra (answers 2, 7), triage | Section 6, steps 3, 4 and 6: the construction under today's III.1, then the guard on its own, then the restatements |
| The guard reads axioms only: it shows neither the construction's algorithm nor its signature, nor rules out a shortcut through the existing axioms; keep semantic review | Astra (answer 2) | Section 3 says what it shows and what it leaves to review; the construction's type is now fixed beside it |
| A pin of 62 names breaks whenever Book I changes; a targeted check is firmer | Claude challenger (editorial) | Adopted at `05c9095`, with the type fixed, and tried against the staged construction, a planted `sorry` and a rename. At the freeze the guard became the pin after all, since the forbidden-command scan (#39) refuses `#eval` in `Audit/`; each renewal is read for the three names (section 3, question 7) |
| "Uses no centre" is false: the construction's closure has `centre_inside` and `Definition15`, from Book I's circles | Astra (answer 2), Claude challenger (material) | Now "given no centre of the circle, and uses no rule that one exists", in the overlap note and throughout |
| Missing consumers: the `Arc.Drawn` users and `Stage4/Prop25.lean:92`; STYLE line 232; FORMALIZATION section 9; brief 0004 line 301; brief 0007's `Prop17.inside` commentary; `scaffold_book.py:188`; `hyperbolic.py:21` | Astra (answer 5), triage | All listed in section 4, save `hyperbolic.py`'s "the other 86", which #40 at `978dc04`, landing first, already removes (section 6, step 1) |
| Missing prose: CONTRIBUTING 53–54, the mishnah of III.17 and III.34, STYLE 232, `Certificate/FIELDS.md`, the expectations' `why`, README 148, NOTICE 11, brief 0006 lines 104 and 1242, overlaps.md 135 with the screen | Claude challenger (material) | All listed in section 4, by the pull request that changes each; the screen runs again with the rule among its rules about circles. Also found: overlaps.md lines 191–192 |
| The formal model: `Centre.lean` already proves the law, `⟨α.1.center, rfl⟩`, translated by hand, not "generated from the lock"; `model/lock.sha256` and `model/Check/Hand.lean`; what if #73 lands first | Astra (answer 6), triage | Section 2 corrected against the branch (now at `57f1454`); section 6, step 5, gives both orders and who writes what. At the freeze #98 had landed the package, so step 5 carries the round-trip check and `model/lock.sha256` |
| Write question 2's reading down as a rule | Astra (answer 3), triage | Section 4 and question 2: a named centre that appears nowhere else in the statement is dropped |
| III.13 leaves a citer naming an unrelated circle; add projection lemmas now | Astra (answer 3), Claude challenger (material), triage | `Prop13.internally`, `Prop13.externally`, staged and proved, with a check; proposed for approval (question 11), and approved at the freeze. Explicit circles alone would still leave A and C |
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
| Conditions said of every centre burden a citer who holds a named centre | Claude challenger (editorial) | `Centre.every`, staged, proved and checked against III.4, proposed for approval, and approved at the freeze; a docstring cannot carry the idiom, since a proposition's docstring is Heath's enunciation |
| The brief is long for "a short brief" | Claude challenger (editorial) | The decisions entry's draft and the model's detail are cut; what the challenge added stays |
| Astra could not fetch issue #59 | Astra (answer 6), triage | The owner's words were checked against the owner's comment on issue #59 on 18 October (section 1) |
| The answer's links point to private paths | Triage | This brief cites repository paths only |
| Brief 0006's conversions show interfaces, not proofs; `of_circle`'s closure is provisional | Astra (answer 1) | Said in Appendix A and section 3 |
| `Audit/` lacks the protected-path treatment of `scripts/` and `tests/` | Astra (answer 5) | The guard is described as a regression check, and lands on its own; whether `Audit/` becomes protected is a policy question for the coordinator, outside this brief |

### Section 7's challenge

Astra's answer to section 7 at `3f00ebf` (GPT Pro, through Codex, read-only, in a
worktree without a build, so with no Lean run). Every finding was checked against the
repository before it was applied, and the Lean ones were run here, at this revision.

| Finding | Source | What was done |
|---|---|---|
| Reading "cut" as crossing is faithful to Definition III.3 and III.5's setting-out; for circles of positive radius the definition describes exactly that figure | Astra (answer 1) | Kept |
| The one-way `CirclesCut` is not symmetric as a Lean definition: acceptable as an explicitly oriented representation, but a reusable relation is better with both points within, or a proved bridge; justify it by geometric equivalence, not by what the proof consumes | Astra (answers 1, 6) | Adopted: both points within, symmetric by its form; the justification is now the plane's (section 7, "Cutting, a new word"); one way and either way are the alternatives (question 15). At the freeze the symmetry is also stated and proved, `CirclesCut.symm`, for Lean users |
| Keep the two common points: one common point with a point within describes contact within too | Astra (answer 1) | Kept, with that reason and Euclid's setting-out (section 7) |
| The point within is faithful and belongs in the definition of contact within, in place of `α ≠ β`; question 16 supported, provided `touching-whole-circles` stays | Astra (answer 2) | Recommendation kept; the disclosure stays, as section 7 and question 16 now say |
| "Heath puts the point in the definition" says too much: Heath says the definition must imply it, and gives no definition of this form | Astra (answer 2) | Reworded in section 7, question 16 and the staged docstring |
| The definition stays our whole-circle reading, not Heath's local one | Astra (answers 2, 6) | Said in section 7 and in the staged docstring of contact within |
| No configuration of circles of positive radius is lost; the argument should use the positive radius, and repeat the crossing argument with the circles exchanged | Astra (answer 3) | Section 7, "No configuration Euclid's words admit is lost", rewritten: the positive radius from the model and from Points 7 and 8, both directions, and Astra's table of configurations |
| "The old and the new statements part only over a circle drawn twice over" says too much: in the plane they do not part; the twin circle shows a difference elsewhere, not every one; a model of every axiom is not a reading of Euclid's objects; `full` rests on the plane, not on the staged checks, which run one way | Astra (answer 3) | Rewritten as "What this shows, and what it does not" (section 7); the checks are called one-way there and in the file |
| The staged check's docstring says the restatement gives up only the twin circle | Astra (answer 4) | Qualified in `Staging/Centre/Crossing.lean` |
| The pins check whole lists of axiom names, not the reading, the statements of the axioms, the other declarations, or shorter proofs; the default `lake build` does not run them | Astra (answer 4) | Said in section 7, "What they rest on", and above the pins in the file |
| Some hypotheses go unused, legitimately | Astra (answer 4) | Said in section 7, "What they leave unused"; nothing else changed |
| III.10's route `modified` and its direct step by `circle_eq` are right; III.11, III.12 and III.13 need no new construction; the audit lemmas need changes | Astra (answer 5) | Kept; the audit lemmas' new proofs are given (section 7, "What changes") |
| "III.11, III.12 and III.13 lose Diagram-segment 2 and gain nothing" is supporting evidence from a scratch copy, for section 7 alone, and the rest of the brief adds centre existence to III.13 | Astra (answer 5) | Qualified in section 7, at the users of `TouchesInternally` and at the certificates |
| Blocking: by the catalogue's test the restated III.5 and III.6 are still overlaps, from Diagram-segment 2 with Generalities 4 (and 3, for III.6), and III.5 from Diagram-segment 4 with Definition I.15; a failed `grind` does not undo a proof; keep the rows, or change the test everywhere | Astra (answer 6) | Adopted: the rows and the records' `[overlap]` stay (section 7, "What changes"; question 15), and the `helper` passages go, since the proofs no longer call the rule. The three proofs were checked by Lean in a scratch file at this revision, with the axioms Astra named. At the freeze the rows and notes are reworded to keep avoidance (our proofs) and overlap (the rules) apart, and the draft's proposal of a note in their place is dropped |
| Clarify `CirclesMeet`'s docstring, "cut one another", which a circle meeting itself satisfies | Astra (answer 6) | Decided at the freeze: a change of step 6 (section 7, "What changes"; section 6, step 6) |
| Before landing: build the whole migration and compare the certificates on the revision delivered; keep `euclid` for III.5 and III.6 and `modified` for III.10; review III.11 to III.13 again, though their fingerprints do not change | Astra (answer 6) | Section 7, "Order" and "What changes" |
| Astra ran no Lean, and read Heath's commentary in a text copy | Astra (handback) | `lake build Staging` and the pins ran here, at this revision; Heath's words on p. 3 were checked against the page image (leaf n15) when section 7 was written |
| The answer's links point to private paths | Triage | This brief cites repository paths only |
