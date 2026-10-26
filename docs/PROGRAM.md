# The programme: thirteen books at one standard

This page holds the state of the whole project and what we have learned making it. It
is updated at the end of every stage and every book. The rules themselves live in
[WORKFLOW.md](WORKFLOW.md), [FORMALIZATION.md](FORMALIZATION.md) and [STYLE.md](STYLE.md),
with [AGENTS.md](../AGENTS.md) as the way in; this page says where we are against them,
and why they are what they are.

## 1. The standard

We aim at 95/100 or more for every book, as three cold outside reviewers score it by the
[review rubric](RUBRIC.md). The first outside reading, [Astra's of 17
October](reports/outside-review-01.md), scored the books against the README; the measurements
by three reviewers on the rubric began on 19 October. A reader of any page should be able to
answer four questions at once:

1. What does Euclid claim?
2. What does the formal theorem prove?
3. How does each substantive step of his argument appear in the Lean?
4. What has the formalization added, changed or left out?

A book meets the standard when its acceptance checklist (`ACCEPTANCE.md`)
passes with no failures, an independent audit by a model family that wrote none of it
agrees, and a cold outside reading passes the gate of the [review rubric](RUBRIC.md). A few
deliberate limitations are allowed when they are stated plainly where they occur. In Book
III, every statement has full scope. Its records are all at review stage `full`, and
the overlap catalogue names the places where System E's rules already contain a
proposition (III.2, and III.5 and III.6 with rules together). I.45 and II.14, restricted
from 20 October 2026 to a figure given with a checked division into triangles, take
any rectilineal figure, given by its outline, from 22 October: that the outline has a
division, and that every division gives the same area, are proved
([#116](https://github.com/jackChallis/stoicheia/issues/116)).

## 2. How a book is made, in parallel

The detail is in [WORKFLOW.md](WORKFLOW.md). In outline, with the crew sizes of Books I–III:

1. **Ground.** Heath transcribed and proofread; the book's brief settles its vocabulary,
   representations, construction inputs and expected exceptions. One first mate.
2. **Statements before proofs.** Every statement is written with `sorry`, translated back
   into plain words, challenged by adversarial readers, and approved before anyone proves
   it. A change later is a recorded brief revision, never a quiet edit.
3. **Sailing.** For each proposition two OpenAI Codex sailors, one at its usual reasoning
   and one at its highest, prove it independently; a Claude bosun checks both and keeps
   the better; Claude first mates review faithfulness; Claude captains enforce the voice.
   About two agents per proposition plus one per pair, in fleets of up to 45.
4. **One voice.** Range enforcers read the book straight through; blind readers, given
   pages mixed from every book, try to hear a second writer; a polisher fixes what they
   hear.
5. **Records.** A review record for every proposition, keyed to the commit it read; the
   gap and overlap catalogues; the book's introduction; further reading from the verified
   list only.
6. **Acceptance.** The five required checks (`check`, `model`, `negative`, `formal-model`
   and `acceptance`) pass in CI, the independent audit agrees, and a reader goes through
   the book start to finish.
7. **Release.** An independent reviewer reads the candidate for stale content and assigns
   every finding to one of four tiers: **Tier 0, defects,** never on main; **Tier 1,
   generated facts,** regenerated rather than written by hand; **Tier 2, reader prose,**
   true at release; and **Tier 3, working records,** dated rather than quietly rewritten.
   The release waits until every Tier 0 to 2 finding is fixed in the release change, every
   Tier 3 finding has a dated status note, no open issue is labelled `blocks-release`, and
   the wiki is refreshed and reasonably correct as of its stated date. Release notes are
   drafted from the generated summaries and approved by the owner before the tag
   ([WORKFLOW](WORKFLOW.md#10-how-a-book-is-made-and-released), section 10, steps 8 and 10).

## 3. Status

<!-- status -->

| Book | Propositions | Stage | Records | Acceptance | Outside score | Release |
|---|---|---|---|---|---|---|
| I | 48 of 48 proved, and I.15's porism and ten companion theorems | released (I.45 for any figure given by its outline, done 22 Oct, #116; next: acceptance, then the consolidation release of Books I–III) | 48 of 48 current: 48 at "full", 0 at "exceptions" | — | 90 (Astra, 676244a) | [book-I](https://github.com/jackChallis/stoicheia/releases/tag/book-I) |
| II | 14 of 14 proved, and ten companion theorems | released (II.14 for any figure given by its outline, done 22 Oct, #116; next: acceptance, then the consolidation release of Books I–III) | 14 of 14 current: 14 at "full", 0 at "exceptions" | — | 85 (Astra, 676244a) | [book-II](https://github.com/jackChallis/stoicheia/releases/tag/book-II) |
| III | 37 of 37 proved, and the porisms of III.1 and III.16 and 25 companion theorems | released (next: the arc's field order, #165, and the centre-given tag's removal, #59; then acceptance and the consolidation release of Books I–III) | 37 of 37 current: 37 at "full", 0 at "exceptions" | — | 80 (Astra, 676244a) | [book-III](https://github.com/jackChallis/stoicheia/releases/tag/book-III) |
| IV | not stated | brief (draft, awaiting approval) | — | — | — | — |
| V–XIII | not begun | — | — | — | — | — |

<!-- /status -->

`render.py` writes this table, and CI checks that it is current. The propositions come
from `facts.json`; the records from `review/`, current when their stamps match the
statements and the Lean files, and, where a record carries a `text` stamp, its own text,
at the stage `exceptions` or `full`
([review/SCHEMA.md](../review/SCHEMA.md)); and the stage, the outside score and the
release from [program.toml](program.toml), which the coordinator keeps with this page.
The outside scores are Astra's reading of 17 October at `676244a`. The
[acceptance report](reports/acceptance-books-I-III.md) exists, but acceptance has not
passed. The Acceptance column stays a dash until it passes. CI now checks every pull
request against main ([#148]); full acceptance remains the consolidation release gate.
The scope of each book's statements, whole, restricted or in part,
stands in the [README](../README.md) and on [the certificate](../CERTIFICATE.md).

Book IV has a [draft brief](briefs/0012-book-IV.md), draft Lean statements and
[scratch prototypes](reports/crew/scratch-IV/). It is not yet in the edition: work there
awaits approval and Books I–III each reaching 95, as the brief's gate requires.

The work under way is [brief 0005](briefs/0005-astra-review.md):

| Stage | What | State |
|---|---|---|
| 0 | The review, this page, the brief | done |
| 1 | Precision: certificate, review records, wording, layout, evidence, overlaps, Book III's reading | done, 17 Oct |
| 1b | Standards: AGENTS.md, STYLE, FORMALIZATION, WORKFLOW, templates, `check_style.py` | done, 17 Oct |
| — | Release of Book III | [done, 17 Oct](https://github.com/jackChallis/stoicheia/releases/tag/book-III); Book I and II notes corrected |
| 2 | I.40 and II.1 general; I.45 and II.14 with supplied divisions | done, 18 Oct: proved in Staging ([#88]), and in the edition with their records ([#19], [#102](https://github.com/jackChallis/stoicheia/pull/102)); I.45 and II.14 restricted from 20 Oct, for figures supplied with a checked division, and full again from 22 Oct, for a figure given by its outline, with the division and the independence of area proved ([#116]) |
| 3 | Arcs and segments; III.24 | done: proved in Staging ([#89]), and in the edition ([#25]); its meeting fact for an arc is `Prop25.meets` in `Elements/BookIII/Prop25.lean` |
| 4 | III.14, III.15, III.25 | done: proved in Staging ([#90]), then moved into `Elements/` with their records in train C6b ([#28]); III.25's construction core and companions under [#153] |
| 5 | Consolidation review of all 99 | Books I and II: all records at `full` ([#115]); Book III: all at `full` ([#29]) |
| 6 | Acceptance, then a consolidation release of Books I–III | report exists; acceptance has not passed; CI checks regressions against main ([#148]) |

### Landed on 18 October

Stages 1 and 1b are done, and the book-III release is made; the owner's decision that the
figures at a glance carry Heath's letters came after them. On main, a GitHub ruleset
requires a pull request and the checks `check`, `model` and `negative` (and, since 20
October, `formal-model` and `acceptance`), allows merge commits only, and blocks force
pushes and deletion; secret scanning with push protection is on. On 18 October the items then open landed on main, each as a pull request of its
own, the figure letters as three:

- **The pull-request harness, [#1]:** `scripts/safe_push.py` as the pre-flight and the
  merge gate, the pre-push hook (reinstalled after the merge), the `git safe-push`
  launcher, the pull-request template and [WORKFLOW](WORKFLOW.md), section 10, "Landing
  work: pull requests".
- **The sweep, [#2]:** the reader-facing wording sweep, with the review records it
  re-read, and the scrub of two local file paths.
- **The phrase rules across a line break, [#3]:** D7 and the other phrase rules of
  `check_style.py` find a phrase however a line wraps it, with S3 kept at full strength.
- **The Staging library, [#4]:** statements with `sorry` before their proofs, built by a
  CI step of their own (`lake build Staging`).
- **The companions list in the edition, [#5]:** `Elements/Companions.lean`, so that
  listing a proved companion is not a check change.
- **The orders template's three kinds, [#6]:** a proof stretch, a statement wave, and a
  companion proof or a restatement's.
- **Brief 0005's dated revisions, [#7].**
- **The figure letters, [#8], [#9] and [#10]:** the rule, with its switch off; the 598
  letters on the 99 figures at a glance; then the switch on, so that every point a figure
  shows is lettered.
- **Brief 0006's statements staged in `Staging`, [#11]:** challenge, approval and freezing
  of the statements are next.

[#1]: https://github.com/jackChallis/stoicheia/pull/1
[#2]: https://github.com/jackChallis/stoicheia/pull/2
[#3]: https://github.com/jackChallis/stoicheia/pull/3
[#4]: https://github.com/jackChallis/stoicheia/pull/4
[#5]: https://github.com/jackChallis/stoicheia/pull/5
[#6]: https://github.com/jackChallis/stoicheia/pull/6
[#7]: https://github.com/jackChallis/stoicheia/pull/7
[#8]: https://github.com/jackChallis/stoicheia/pull/8
[#9]: https://github.com/jackChallis/stoicheia/pull/9
[#10]: https://github.com/jackChallis/stoicheia/pull/10
[#11]: https://github.com/jackChallis/stoicheia/pull/11
[#13]: https://github.com/jackChallis/stoicheia/issues/13

### Open items

What remains on 21 October, after trains C6a, C6b and C6c. Stage 2 is in the edition; I.47 general, for
squares on either side of each base, followed in [#134]. Stage 3 is in the edition too
(#20 to #25): placement in all its cases, with superposition not among its direct axioms,
III.23 point by point, III.24 restated to conclude congruence by Euclid's route, III.26 and
III.28 upgraded, and `Arcs.lean`. So are the mixed angles of III.16 and III.31 ([#57]),
the rule that every circle has a centre (`Tacit.exists_centre`, brief 0008's step 5), and
III.5 and III.6 read with crossing and contact within (brief 0008, section 7). Stage 4 is
in the edition as well: `Foot`, III.14 and III.15's companions, III.25 with `Prop25.kind`,
and `Prop25.meets` beside III.25 in `Elements/BookIII/Prop25.lean`. III.1's construction
is at home in `Elements/BookIII/Prop01.lean`, with its guard, `Audit/Centre.lean` (brief
0008's step 4). Brief 0008's step 6 is done as well: the Book III statements that only
assumed a centre now take it inside their proofs, and III.30's halves is proved as the
companion "III.30 halves" ([#67]). On 22 October, with the owner's approval, brief
0013's figures followed ([#116]): I.45 and II.14 hold for any rectilineal figure, given by
its outline (`Prop45.outline`, `Prop14.outline`), and their records are full again. How
work lands is in [WORKFLOW](WORKFLOW.md), section 10, "Landing work: pull requests".

- **The centre rule's tag revision** remains under [#59]: step 7 of frozen
  [brief 0008](briefs/0008-centre.md) removes the unused `centre-given` from
  `review/terms.toml`. The construction (step 3), its guard (step 4) and the restatements
  with their records (step 6) are done.
- **Book III's review records** are all at `full` ([#29]), as Books I and II's are
  ([#115]).
- **Acceptance** still has failing items in its report. CI now checks every pull request
  against main ([#148]); the consolidation release must pass every item.
- **Two that are not pull requests:** the finished worktrees and their merged branches are
  removed, and the fleet script, kept outside the repository, is rebuilt from the orders
  template, without "every hypothesis should be used" and without the rule that every one
  of Heath's references be cited.

## 4. Decisions later books depend on

- **Arcs and segments** (stage 3) are what Book IV will inscribe and circumscribe with;
  their definitions are in `Elements/Foundations/DefinitionsIII.lean`, and
  `Circumference.add` is in `Elements/BookIII/Circumferences.lean`. The arc's field order is
  still open ([brief 0010](briefs/0010-notation.md), question 3), to be settled before the
  consolidation release.
- **Construction inputs.** A construction receives only what the problem gives; its
  correctness may quantify over more (stage 4, III.25). Book IV's brief adopts this.
- **Proportion** (Book V): Eudoxus's definition taken literally, the Archimedean property
  as an axiom; one hard statement (V.18's fourth proportional) prototyped before any
  fleet.
- **Numbers** (Books VII–IX): what Euclid assumes, decided by brief; VII.16 proved without
  borrowing commutativity; prototyped first.
- **Incommensurables** (Book X): X.1 prototyped first.
- **Solids** (Books XI–XIII): planes as primitives; one statement prototyped first.
- **A formal model** of the axioms in Lean with Mathlib: done. Begun on 18 October 2026 in
  a package of its own, [`model/`](../model/README.md), with CI's `formal-model` job (#73,
  a gate for the consolidation release), it proves all <!-- count:axioms -->48<!-- /count --> locked laws in the ordinary
  plane, and `model_exists` has no hypothesis left: a model relative to Lean's logic and
  Mathlib's construction of the real numbers. It does not show that a formal statement
  captures what Euclid meant. The independence of Postulate 5 still rests on the
  numerical hyperbolic check in [tests/model](../tests/model/), until a hyperbolic model
  is built. GitHub now requires all five checks: `check`, `model`, `negative`,
  `formal-model` and `acceptance`. The merge gate in `scripts/safe_push.py` requires a
  passing run of the same five, and refuses any reported failure or pending check
  ([WORKFLOW](WORKFLOW.md#8-validation-on-the-integrated-revision), section 8).
- **The statements' vocabulary** (settled 17 Oct; extended for restricted superposition,
  and on 22 Oct for the figures given by their outlines).
  The lock holds every word that the axioms' statements or the entries' statements
  reach: <!-- count:vocabulary -->267<!-- /count -->, including the restricted calculus and its interpretation,
  as well as `Touches`, `EqualCircles`, `circumference`, `rect`, `Parallel` and others.
  A change to one is a decision, as a changed axiom is
  ([0002](briefs/0002-decisions.md), [FIELDS.md](../Certificate/FIELDS.md#the-vocabulary)).
  Each later book's definitions join the lock with its statements.

## 5. Lessons

- **16 Oct. The highest reasoning setting wins best-of-two.** Kept 15 of 16 times in
  Book I's fleet, 14 of 14 in Book II, 33 of 37 in Book III.
- **16 Oct. Captains enforcing five pages each do not make one voice.** Range enforcers
  reading a book straight through, and blind readers across books, do
  ([voice-01](reports/crew/voice-01.md), [voice-02](reports/crew/voice-02.md)).
- **16 Oct. A style rule can cause the drift it guards against.** Asking every commentary
  to explain every extra citation produced the same paragraph on twelve pages; a generated
  line under the certificate does the job once.
- **16 Oct. Agents read the message that launched them.** A relayed "Ignore" made a fleet
  stand down; every crew order now opens with a note on what the user's latest message
  means.
- **17 Oct. Our promises outran our coverage.** The outside review found claims of
  "complete", "sentence by sentence" and "never need" broader than the statements and
  checks behind them. Statements and representations are now reviewed before proofs, and
  every page shows its own scope.
- **17 Oct. A porism is a claim too.** It needs its own certificate and every check.
- **17 Oct. The fidelity check checks wording, not meaning.** Meaning needs a review
  record, tied to the commit it read.
- **17 Oct. An independent model is cheap.** Jev answered a scope question and three
  figure questions correctly in under a fifth of a second each; on the scope question it
  was right but only moderately confident, so its disagreements go to an adjudicator.
- **17 Oct. A new kind of entry reaches every reader of the data.** The porism entries
  ("III.1 Por.") stopped `check_fidelity.py` and `render.py`, which split references on
  the dot, until each used the contracts' `parse_ref`. Shared formats go in the contracts
  commit, and every consumer is named in the orders
  ([FIELDS.md](../Certificate/FIELDS.md)).
- **17 Oct. Text that becomes generated is overwritten.** README's book rows, rewritten by
  hand in the wording pass, were replaced on the first render by the summaries the review
  records give, which count the exceptions rather than describe them. A description
  wanted on a generated page has to live in the generator's inputs
  ([review/terms.toml](../review/terms.toml)).
- **17 Oct. Stamps come last.** A review record's `lean` stamp hashes its whole file, so
  even a comment changes it (Prop16, Prop31 and Prop18 this time). The integrator stamps
  after every branch is merged ([review_stamp.py](../scripts/review_stamp.py)).
- **17 Oct. One home per rule needs one owner per rule.** Two scripts grew the same lint:
  `check_fidelity.py` (`check_wording`) and `check_style.py` (S5) both reject "Euclid
  cites" and "never need". Who owns a rule is settled before the wave starts.
- **17 Oct. A statement can change while its print stays the same.** A statement prints
  `Touches` or `rect` by name, so a new definition of either would have moved no review
  fingerprint. The lock now holds every word a statement reaches
  ([axioms.lock](../Certificate/axioms.lock)).
- **17 Oct. A push needs no one's OK when the commit itself is checked.**
  `scripts/safe_push.py` reads the commit alone, in a fresh worktree; it refuses a secret,
  a statement or the lock changed without a decision, a Heath edit naming no scan leaf, a
  stale record or a deleted directory, runs every CI check, and only then pushes, and
  `test_safe_push.py` plants a bad commit for each guard ([WORKFLOW](WORKFLOW.md),
  section 10).
- **17 Oct. Move to pull requests as soon as a repository has CI and readers; we were
  late.** A checked push left no place for its reviews. Every change is now a pull
  request: `safe_push.py` is its pre-flight and its merge gate, the template records its
  reviews, and a ruleset on main requires it ([WORKFLOW](WORKFLOW.md), section 10,
  "Landing work: pull requests").
- **18 Oct. A rule that keeps a check change apart from content must spare what moves with
  content.** Values pinned to the edition (the certificate's expectations, the axiom lock,
  the model's lock hash), pages regenerated by origin/main's `render.py`, the guides and
  briefs, and a review record's stamps all change with the work they describe. Review
  found each before it blocked real work, and the companions list moved out of the check
  into the edition for the same reason ([#1], [#5]).
- **18 Oct. Reviews converge when the fixes are reviewed too.** Four rounds on the harness
  each found real defects. The last blocking one, an exemption that let a loosened
  expectation travel with the regression it guards, was in the previous round's fix; a
  `/no-mistakes` run on that commit found nothing blocking, and only an adversarial check
  of the fixes themselves caught it. The final `/no-mistakes` run then passed ([#1]).
- **18 Oct. A stricter rule that today's content fails lands with a switch.** The figure
  letters came as three pull requests: the rule with its switch off, the letters, then the
  switch on, so that no check travelled with what it judges ([#8], [#9], [#10]).
- **20 Oct. What a check cannot judge needs a standing read.** The first read for stale
  content (A0) found claims false on main and others that queued work would make false;
  the merge-conflict marker and the stale counts among them prompted checks of their own.
  The read now comes before every release and at the end of each programme stage
  ([WORKFLOW](WORKFLOW.md#10-how-a-book-is-made-and-released), section 10, step 8).

## 6. Cost and time

Claude agents and tokens per workflow (Codex sailors' tokens are logged by their bosuns
in the voyage logs).

| Work | Agents | Tokens | Wall time |
|---|---|---|---|
| Book III, first fleet (III.1–19) | 45 | 7.3M | 66 min |
| Book III, second fleet (III.20–37) | 42 | 6.8M | 125 min |
| Books I–II in one voice | 27 | 7.0M | 205 min |
| Book III in one voice | 8 | 2.4M | 88 min |
| Read-through (finish, after a network failure) | 8 | 2.3M | 149 min |
| Follow-ups (Common Notions, held fixes, Book III's introduction) | 6 | 1.0M | 136 min |
| Book III close-out (I.23, logs, catalogue, status) | 8 | 1.6M | 48 min |
| Pre-release checks | 6 | 1.4M | 57 min |
| Book III references research | 11 | 2.5M | 65 min |
| Precision pass and standards (brief 0005, stages 1 and 1b): the build | 23 (3 stopped at an account-terms prompt and were run again) | 5.9M | 95 min |
| Precision pass and standards: the finish (integration, readers, fixes) | 7 | 2.0M | 104 min |
| The night of 18 October: pull requests #1 to #11 | not logged | not logged | one night |
[#88]: https://github.com/jackChallis/stoicheia/pull/88
[#89]: https://github.com/jackChallis/stoicheia/pull/89
[#90]: https://github.com/jackChallis/stoicheia/pull/90
[#19]: https://github.com/jackChallis/stoicheia/issues/19
[#25]: https://github.com/jackChallis/stoicheia/issues/25
[#28]: https://github.com/jackChallis/stoicheia/issues/28
[#29]: https://github.com/jackChallis/stoicheia/issues/29
[#57]: https://github.com/jackChallis/stoicheia/issues/57
[#59]: https://github.com/jackChallis/stoicheia/issues/59
[#67]: https://github.com/jackChallis/stoicheia/issues/67
[#115]: https://github.com/jackChallis/stoicheia/pull/115
[#116]: https://github.com/jackChallis/stoicheia/issues/116
[#134]: https://github.com/jackChallis/stoicheia/pull/134
[#148]: https://github.com/jackChallis/stoicheia/pull/148
[#153]: https://github.com/jackChallis/stoicheia/issues/153
