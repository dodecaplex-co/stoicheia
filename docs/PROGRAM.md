# The programme: thirteen books at one standard

This page holds the state of the whole project and what we have learned making it. It
is updated at the end of every stage and every book. The rules themselves live in
[WORKFLOW.md](WORKFLOW.md), [FORMALIZATION.md](FORMALIZATION.md) and [STYLE.md](STYLE.md),
with [AGENTS.md](../AGENTS.md) as the way in; this page says where we are against them,
and why they are what they are.

## 1. The standard

We aim at about 95/100 for every book, in the sense of [Astra's outside
review](reports/outside-review-01.md). A reader of any page should be able to answer four
questions at once:

1. What does Euclid claim?
2. What does the formal theorem prove?
3. How does each substantive step of his argument appear in the Lean?
4. What has the formalization added, changed or left out?

A book meets the standard when its acceptance checklist (`ACCEPTANCE.md`)
passes with no failures, an independent audit by a model family that wrote none of it
agrees, and a cold outside reading scores it about 95. A few deliberate limitations are
allowed when they are stated plainly where they occur: in Book III, the mixed angles of
III.16 and III.31, and the places where a System E rule already contains a proposition
(III.2).

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
6. **Acceptance.** The checklist passes in CI, the independent audit agrees, a reader goes
   through the book start to finish.
7. **Release.** Release notes drafted from the generated summaries, approved by Jack, then
   the tag.

## 3. Status

<!-- status -->

| Book | Propositions | Stage | Records | Acceptance | Outside score | Release |
|---|---|---|---|---|---|---|
| I | 48 of 48 proved, and I.15's porism | released (next: I.40 and I.45 in full generality) | 48 of 48 current: 0 at "full", 48 at "exceptions" | — | 90 (Astra, 676244a) | [book-I](https://github.com/jackChallis/stoicheia/releases/tag/book-I) |
| II | 14 of 14 proved | released (next: II.1 and II.14 in full generality) | 14 of 14 current: 0 at "full", 14 at "exceptions" | — | 85 (Astra, 676244a) | [book-II](https://github.com/jackChallis/stoicheia/releases/tag/book-II) |
| III | 37 of 37 proved, and the porisms of III.1 and III.16 | released (next: arcs and segments) | 37 of 37 current: 0 at "full", 37 at "exceptions" | — | 80 (Astra, 676244a) | [book-III](https://github.com/jackChallis/stoicheia/releases/tag/book-III) |
| IV–XIII | not begun | — | — | — | — | — |

<!-- /status -->

`render.py` writes this table, and CI checks that it is current. The propositions come
from `facts.json`; the records from `review/`, current when their stamps match the
statements and the Lean files, at the stage `exceptions` or `full`
([review/SCHEMA.md](../review/SCHEMA.md)); and the stage, the outside score and the
release from [program.toml](program.toml), which the coordinator keeps with this page.
Acceptance stays "—" until brief 0005's stage 6 gives the acceptance report. The scope of
each book's statements, whole, restricted or in part, stands in the
[README](../README.md) and on [the certificate](../CERTIFICATE.md).

The work under way is [brief 0005](briefs/0005-astra-review.md):

| Stage | What | State |
|---|---|---|
| 0 | The review, this page, the brief | done |
| 1 | Precision: certificate, review records, wording, layout, evidence, overlaps, Book III's reading | done, 17 Oct |
| 1b | Standards: AGENTS.md, STYLE, FORMALIZATION, WORKFLOW, templates, `check_style.py` | done, 17 Oct |
| — | Release of Book III | [done, 17 Oct](https://github.com/jackChallis/stoicheia/releases/tag/book-III); Book I and II notes corrected |
| 2 | I.40, I.45, II.1, II.14 in full generality | next: statements first (brief 0006) |
| 3 | Arcs and segments; III.24 | |
| 4 | III.14, III.15, III.25 | |
| 5 | Consolidation review of all 99 | |
| 6 | Acceptance, then a consolidation release of Books I–III | |

### Open items, 18 October

Stages 1 and 1b are done, and the book-III release is made; the owner's decision that the
figures at a glance carry Heath's letters came after them. On main, a GitHub ruleset
requires a pull request and the checks `check`, `model` and `negative`, allows merge
commits only, and blocks force pushes and deletion; secret scanning with push protection
is on. On 18 October these items were open, each landing on main as a pull request of its
own, the figure letters as three, in this order:

- **The pull-request discipline, PR #1:** the safe-push hardening, with the reviewers'
  fixes, under `/security-review`. Once it is on main, the pre-push hook is reinstalled.
- **The sweep,** one pull request: the reader-facing wording sweep and the scrub of two
  private paths, with the review records it re-reads.
- **check_style's D7 pattern,** after the sweep, so that it also catches a phrase broken
  across a line; it also tightens S3 and S9. It changes a check, so it travels alone.
- **The orders template:** `docs/templates/orders.md` gains a statements-only wave and
  companion proofs.
- **The figure letters,** three pull requests in order: the letters rule (letters allowed,
  and checked where drawn), the lettered figures, then every point lettered (required).

Two more are not pull requests: the finished worktrees and their merged branches are
removed, and the fleet script, kept outside the repository, is rebuilt from the orders
template, without "every hypothesis should be used" and without the rule that every one of
Heath's references be cited.

## 4. Decisions later books depend on

- **Arcs and segments** (stage 3) are what Book IV will inscribe and circumscribe with;
  their definitions and `Circumference.add` must be settled first.
- **Construction inputs.** A construction receives only what the problem gives; its
  correctness may quantify over more (stage 4, III.25). Book IV's brief adopts this.
- **Proportion** (Book V): Eudoxus's definition taken literally, the Archimedean property
  as an axiom; one hard statement (V.18's fourth proportional) prototyped before any
  fleet.
- **Numbers** (Books VII–IX): what Euclid assumes, decided by brief; VII.16 proved without
  borrowing commutativity; prototyped first.
- **Incommensurables** (Book X): X.1 prototyped first.
- **Solids** (Books XI–XIII): planes as primitives; one statement prototyped first.
- **A formal model** of the axioms in Lean with Mathlib, as a separate package, defined
  in [MODEL.md](../tests/model/MODEL.md#a-formal-model-a-later-milestone). Until then the
  evidence is numerical: [tests/model](../tests/model/), in CI, with the hyperbolic check.
- **The statements' vocabulary** (settled 17 Oct). The lock holds every word that the
  axioms' statements or the entries' statements reach: 61, the 37 of the axioms and 24
  that only the statements use (`Touches`, `EqualCircles`, `circumference`, `rect`,
  `Parallel` and others). A change to one is a decision, as a changed axiom is
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
