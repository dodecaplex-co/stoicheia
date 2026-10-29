# Brief 0005: answering Astra's review

19 October 2026: this brief keeps its earlier measurements and instructions as history.
[Eight rules are now theorems](../FORMALIZATION.md#rules-now-proved), with their names
and types unchanged; the baseline is 79 axioms, including 73 tacit rules. Fresh
certificate output at `1e713bb` gives III.1 and its porism the same 60 axioms, including
55 tacit rules. `centre_unique` is proved in Book Zero, so the old 56/57 counts and
required axiom membership no longer describe their dependencies. Any change to those
checks needs its own approval and separate preparation under WORKFLOW, section 10.
Circle 2 is proved from Circle 3; III.2's remaining overlap is with Circle 3, and its
published proof uses neither the Circle 2 theorem nor the Circle 3 axiom. Thirty-one more
rules became theorems the same day, so the baseline is now 48 axioms, including 42 tacit
rules; fresh certificate output for the 48 gives III.1 and its porism 38 tacit rules each.

*Written and committed on 17 October 2026 (d040117), and revised on 18 October 2026 to the owner's decisions taken after it. The first text stands in the history, and each revised passage says so where it stands. What changed, and why:*

- **Placement has no time limit and no fallback.** The owner decided on 17 October that III.24 waits for a proved placement lemma, and that a fact the axioms lack is a decision for the owner, never a quiet new axiom. "Timeboxed", the fallback congruence and "if the fallback was used" are removed; the verification line for placement, which could never pass, is restated; the corrections to the design and the order of work, spike first, are added under stage 3.
- **I.45 and II.14 are stated as Euclid and Byrne state them.** The owner's decision, later on 17 October, replaces the general dissection (`Rectilineal`, `Fitted`) with a figure given by its corners and taken as divided by the straight lines from one corner (stage 2, and the places that named a dissection).
- **I.45 and II.14 are full** (18 October, after the revision above). [Brief 0006](0006-statements.md), as revised and frozen, takes them `full`: the figure is given with its division into triangles, checked, as triangles that lie apart (`Apart`), as triangles glued edge to edge (`Fitted`, `Rectilineal`, restored), or as Euclid's and Byrne's from one corner, with the two conditions that make it a division. Its statements, proved, are now in the edition. The passages of stage 2 below that speak of a figure given by its corners alone are kept as they stood, each with a note.
- **Stage 3 is in the edition** (18 October). [Brief 0006](0006-statements.md)'s statements of stage 3, proved, are now in `Elements/`: III.24 concludes that the segments are congruent, by `placement`, with the proof by the radii kept as `Prop24.equalCircles`; III.26 and III.28 conclude that the circumferences are congruent too; `Arcs.lean` follows III.29; and the placement policy is checked. The status notes of stage 1 that stage 3 overtook are kept as they stood, with a note.
- **Landing work: pull requests,** a new section: a pointer to the pull-request discipline of docs/WORKFLOW.md, section 10, which lands with pull request #1, and the branches stages 2, 3 and 4 work on.
- **The colour figures are to carry Heath's letters,** the owner's decision of 17 October, taken after stage 1b was done (stages 1b, 5 and 6).
- **What remains of stages 1 and 1b** is kept in docs/PROGRAM.md, with the state of the work; a line at the end of stage 1b points to it.

## Context

Astra reviewed Stoicheia at commit 676244a in four parts:
1. **A cold assessment,** with a 7-step priority table.
2. **A score against the README's goal:** 85 overall; Book I 90, Book II 85, Book III 80. Astra says about 90 needs the certificate fixed, qualifications shown and the easy gaps closed; 95 needs the arc and segment meaning and every clause accounted for.
3. **A roadmap to 95 for each book,** in five stages.
4. **A proposed contributor guide**, with `AGENTS.md`, `FORMALIZATION.md`, `WORKFLOW.md`, templates and a pilot.

The core finding: **the reader-facing promise outruns the formal coverage.**
- "Complete", "sentence by sentence", "following Euclid's own proof" and "never need Postulate 5" are sometimes broader than what the theorems and checks support.
- The proofs themselves are sound and kernel-checked.

We verified every claim against the code with three read-only explorers. All hold except one detail: III.16's porism adds nothing to its certificate.

**Certificate**
- Porisms are folded in only for their sorry status. III.1's certificate omits `centre_unique`, used only in its porism.
- Porisms escape every policy check (superposition, later citations, Postulate 5 in I.15's porism).
- `directDeps` walks proof values only, not types.
- Only the axiom count (87) is locked, not the axioms' statements.
- The Postulate 5 boundary is enforced only in Book I.

**Wording**
- "Euclid cites" and GRAPH.md's "Euclid's own bracketed references" are Heath's editorial references. Heath, vol. 1, p. 83: such references are "rare in Euclid".
- "Needs Postulate 5" should read "this proof uses".
- "Lean cannot give a segment without its circle" describes our representation, not Lean.
- render.py prints "the lines under each sentence are the Lean that carries it out" on all 99 pages, which is false on III.16 and III.31.

**Scope.** One green badge covers full statements and restricted ones:
- I.40: adjacent bases only.
- I.45 and II.14: two triangles.
- II.1: three pieces.
- III.14: diameters excluded, and not disclosed.
- III.16 and III.31: mixed-angle clauses omitted.
- III.25: handed the whole circle.
- III.24: concludes angular measure, not segment congruence.

**Representation.** `circumference` is an Angle, with no radius.
- III.26 and III.27 stay provable with EqualCircles removed, and III.24's second clause follows from its angle hypothesis alone.
- III.28 and III.29 genuinely need EqualCircles.

**Overlap.** III.2 is an instance of the axiom `inside_of_between`. Its proof depends on that axiom through III.1 and through I.5.

**Evidence.** The model and mutation harness behind "the axioms are sound" lives only outside the repository. It isn't reproducible from the repository.

**Layout.** Lean listings have a median of 94 lines and run up to 309 (II.8) before the commentary. Navigation is at the top only, and the scan references are plain text.

**The owner's decisions, 17 October 2026**
- An honest book-III release now, then a ~95 consolidation release of Books I–III.
- Publish Astra's review in the repository with a point-by-point response and warm thanks.
- Fold the helper lemmas and keep the main proof visible.
- The owner has already approved the book-III notes. They must be re-approved, because they now overclaim.

- Adopt Astra's layered contributor guide.
- Voice rules become defaults, not quotas.

**Later the same day, after this brief was committed** (added 18 October; each is set out where it applies):
- Placement has no fallback and no time limit; III.24 waits for a proved placement lemma (stage 3).
- I.45 and II.14 are stated as Euclid and Byrne state them, for a figure given by its corners (stage 2).
- The colour figures are to carry Heath's letters (stage 1b).
- All work lands on main through a pull request, with reviews ([Landing work: pull requests](#landing-work-pull-requests)).

## Stages and releases

| Stage | What | Ends with |
|---|---|---|
| 0 | Anchor: this plan as `docs/briefs/0005-astra-review.md`; the review (both parts plus the guide) with our point-by-point response in `docs/reports/outside-review-01.md`; references research files put in place | commit |
| 1 | Precision pass: certificate, review records (exceptions), wording, layout, evidence, overlaps, Book III references | **book-III release** (notes re-approved by the owner) |
| 1b | Standards: Astra's layered guide, adapted | in the same release |
| 2 | Books I–II generality (pilot of the guide: briefs before proofs) | — |
| 3 | Book III arcs and segments; III.24 | — |
| 4 | III.14/15 boundaries; III.25 construction core | — |
| 5 | Consolidation review of all 99 (full semantic records, figures against the scans, read-through) | — |
| 6 | **Acceptance**: `docs/ACCEPTANCE.md` checklist, `check_acceptance.py` with zero failures, an independent Jev audit (a fresh client), and a cold re-score by Astra | **consolidation release of Books I–III** (notes approved by the owner) |

**Status, 29 October 2026.** Stage 6's independent audit is now the cold outside reading,
by two reviewers, Claude and Astra, scoring by the [review rubric](../RUBRIC.md), as the
owner chose that day ([#703](https://github.com/dodecaplex-co/stoicheia/issues/703)); the
Jev audit's card, [#36](https://github.com/dodecaplex-co/stoicheia/issues/36), closed as not
planned on 28 October. The note under stage 6, below, says more.

Each stage runs as a workflow (ultracode): crews in git worktrees, adversarial verifiers, an integrator, and the coordinator landing each piece as a reviewed pull request (revised 18 October; the first text had the captain merging and pushing after full CI, and [Landing work: pull requests](#landing-work-pull-requests) points to the rules now). Nothing public (tags, releases, release notes, the GitHub description) happens without the owner's OK.

## The standing document: `docs/PROGRAM.md`

This is the owner's request. One living page tracks the programme across this work and **every later book**: how we run in parallel and keep to the 95/100 bar. It is created in stage 0 and updated at the end of every stage and every book. WORKFLOW.md holds the rules; PROGRAM.md holds the state and the lessons.

1. **The standard.** What 95/100 means for a book: Astra's four reader questions, the acceptance checklist (link to ACCEPTANCE.md), the allowed deliberate limitations, and how the score is measured (check_acceptance, Jev audit, cold re-score).
2. **How a book is run in parallel.** A one-page summary of WORKFLOW.md:
   - statements and representations approved before proofs;
   - waves and file ownership;
   - best-of-two Codex sailors with Claude bosuns, first mates and captains;
   - the voice guide in every prompt;
   - range enforcers, blind readers, a polisher;
   - review records tied to a commit;
   - the Jev audit;
   - the release gate.

   Each step carries its typical agent count and cost from past voyages.
3. **Status board**, one row per book (I–XIII) with these columns:
   - stage (brief, statements, proofs, voice, records, acceptance, released);
   - propositions proved;
   - records full and current;
   - acceptance failures;
   - Jev audit result;
   - cold score;
   - release tag.

   Generated where possible from facts.json, review/ and the acceptance report, and **checked fresh in CI** like the pages.
4. **Open risks and representation decisions** that later books depend on (arcs and segments for IV; proportion for V; construction inputs; the formal model).
5. **Lessons learned**, dated and short, each linked to its evidence. For example:
   - per-ship captain enforcement isn't enough;
   - resume workflows only with their exact args;
   - Jev is right but under-confident on scope questions;
   - porisms must be first-class.
6. **Cost and throughput log**, per stage: agents, tokens or credits, wall time. This is how we keep the next books to the bar without drift.

## Stage 0: anchor
- Create `docs/PROGRAM.md` (above), seeded with Books I–III's history and this plan's stages.
- Put the Book III references research (the reading plan and the verified works) in place for stage 1j.
- Commit this plan as brief 0005.
- Commit `docs/reports/outside-review-01.md`:
  - Astra's three texts, credited with warm thanks;
  - a response table with one row per point (accepted / changed how / where / stage);
  - the one place we differ: III.16's porism, which the review didn't single out and which we verified adds nothing.
- Add a line of thanks in README's "How it was made".

## Stage 1: the precision pass (gates the book-III release)

**a. Porisms get their own certificate entries.** "I.15 Por.", "III.1 Por." and "III.16 Por.".

*Certificate/Facts.lean*
- `refOf` maps `.porism` to "N Por.".
- Subjects are the propositions, then their porisms, then `companions` (an empty list now, so stage 2's general theorems drop in).
- Each entry gains `kind` (proposition / porism / companion), `of`, `statement`, and on the parent `attached`.
- `directDeps` records the porism itself.
- `sharedSteps` treats the parent's own helpers as local.
- The parent stays "sketched" until its porism is proved.

*heath.py*: `parse_ref`, a 3-tuple `prop_key`, `heath_porisms()`, and `theorem_span()` factored out of check_fidelity.

*check_fidelity*
- All three policies (later citation, superposition, Postulate 5 before FIRST_EUCLIDEAN) loop over **every** entry.
- Porism entries must match Heath's porisms.
- COMPLETE requires every attached entry to be proved.

*render.py*: a third "Porism" column in "What it rests on", rules marked "(porism)", a `#porism` anchor, and an indented CERTIFICATE row.

*Negative tests*, folded into `planted_assumptions` so one build covers them:
- I.15's porism with Postulate 5, superposition and a citation of I.22, each caught, and I.15 itself not blamed.
- `expect_failure` gains `unwanted=`.

Expected result: III.1 shows 56 tacit rules and III.1 Por. 57, including `centre_unique`.

**b. One dependency walk.** `mentions(ci)` (type, value including opaque values, and constructors), used by `directDeps`, `allNotions` and `sharedSteps`. Facts.lean also gets a self-check: each subject's `collectAxioms`, minus the foundations, equals its direct axioms plus those of what it cites. `axioms` lists stay byte-identical.

**c. Axiom lock.**
- facts.json gains `axiom_types` (the 87, printed with notation off and full names) and `vocabulary` (every definition, instance and opaque an axiom mentions).
- `Certificate/axioms.lock` changes only through `check_fidelity.py --write-lock`, together with a 0002 decisions entry.
- CI compares the lock with facts.json in both directions, and `AXIOM_COUNT` is derived from the lock.
- Negative tests: the planted axiom misses the lock; a weakened `Postulate1` in facts.json is caught.

**d. Review records (stage-1 exceptions).**
- One file per proposition, `review/<book>/NN.toml`, with sections `[statement]` (scope full/restricted/partial; hypotheses; omitted; note ≤160 chars; fingerprint; companions), `[route]` (euclid/modified/alternative, note), `[representation]` (tags from `review/terms.toml`), `[overlap]`, `[coverage]` (clause maps for III.16 and III.31), `[[passage]]` (carried/helper/grouped/different/unformalized; exceptions now, every passage at stage 5), `[figure]`, and `[review]` (stage, commit, lean hash). The schema lives in `review/SCHEMA.md`.
- *check_fidelity `check_reviews`*:
  - all 99 records valid;
  - the fingerprint equals facts' `statement` and `lean` equals the file hash (content hashes, so shallow clones work); otherwise "statement changed since reviewed";
  - `uncarried_runs()` flags `--` runs with no Lean beneath them (the prototype finds III.4–7, III.19 as grouped and III.16 as unformalized), and each must be declared;
  - III.31 is declared by hand.
- *Filling the records*, a crew of 5 classifiers and 2 adversarial verifiers:
  - classifiers work from worksheets (enunciation, Lean signature, mishnah, gaps entries);
  - verifiers hunt for any Heath instance outside a "full" statement and for III.31-style passages;
  - 100% recall is required on the review's seed list: I.40, I.45, II.1, II.14, III.1, III.9, III.12, III.14, III.16, III.24, III.25, III.26/27, III.31;
  - any mishnah disclosure phrase must be matched by its record.
- *Display*:
  - one line under the enunciation: "**In Lean:** ✅ proved, for a restricted statement: … · Euclid's argument";
  - under "In Lean", a field table (Proof, Statement, Extra hypotheses, Argument, Representation, Overlap, Reviewed at <commit>);
  - clause maps before the Lean for III.16 and III.31;
  - the generic "Lean that carries it out" sentence becomes conditional;
  - Index pages get a "Lean statement" column, and CERTIFICATE.md gets "Statement" and "Argument" columns.
  - Completion summaries (CERTIFICATE, index headers, README rows between `<!-- scope:I -->` markers) are generated, and README joins the CI freshness check.
  - III.2's overlap note goes in its top line.
  - III.14's undisclosed diameter exclusion and III.26's misleading "Where do the equal circles do their work?" are fixed in their mishnah and record.

**e. Wording.**
- STYLE §5: brackets are Heath's references; "this proof uses Postulate 5", never "needs".
- render.py: "Euclid cites" becomes "Heath's references", and `euclid_cites` becomes `heath_refs`.
- CERTIFICATE text: Heath's editorial references, with his vol. 1 p. 83 remark checked against the scan. Also "the proofs of 29 propositions do not use it" and "Nothing here is typed in by hand" are fixed.
- GRAPH header.
- README:
  - :15 gains the III.16/III.31 exception;
  - :25–27 become generated scope clauses;
  - :64 says "whether our proof uses it; whether some other proof could do without it is a different question";
  - :105 says statements rest on review.
- intro/I.md (:3, :9, :11); intro/III.md:15 ("Our representation of a segment includes its circle").
- Bracket references in mishnah I.11, I.15, I.20, I.36, II.10, III.11 and the three gap catalogues.
- The headers of Prop16.lean and Prop31.lean, plus a `/- -/` remark for III.31.
- A lint over README, CERTIFICATE and the index pages rejects "never need", "Euclid cites" and "Euclid's own bracketed".
- A blind reader checks the tone.

**f. Layout** (the owner's decision: fold helpers, keep the main proof).
- Jump links under the title, and prev/next repeated at the bottom.
- `lean_parts()` shows the main theorem open, the helpers before it in one `<details>` (with names and a line count), and the corollaries and porism proofs after it in another.
- `scan_url()` is factored out of `heath_figure_note`, and footers link "scan leaves nA–nB", "scan leaf nX" and "figure on nX".
- `scripts/check_links.py` checks relative links and `#anchors`, and runs in CI.

**g. A second graph.** GRAPH.md gets, per book, a section "From Heath's references" (the current graph) and one "From the Lean" (from facts `cites`, porisms mapped to their parent). Lean-only edges are dashed, and a list notes the Heath references the Lean doesn't cite.

**h. Model evidence in the repository.**
- `tests/model/`: model.py, search.py, exhaustive.py, structured.py, mutations.py, grid_check.py, angle_check.py (with its hard-coded path fixed).
- `run.py --fast` (CI, under 2 minutes) and `--full --write`, which writes `results/` headed with commit and seeds.
- The harness's axiom names must equal the lock's, and `lock.sha256` pins the lock so any axiom change forces a model revisit.
- `tests/model/MODEL.md` gives the interpretation and the evidence law by law. Laws no harness reaches get a hand argument.
- read-through-01's "8 million" gets a dated correction (about 11.8M configurations met the hypotheses).
- A new CI job, `model`.
- The Mathlib formal model is a named later milestone, as a separate package.

**i. Overlap catalogue.**
- `docs/reports/overlaps.md`: proposition, rule, kind, what the Lean proof does, audit lemma.
- `Audit/Overlaps.lean`, a lib nothing imports, built in CI. Each theorem is pinned to the proposition's own type, e.g. `theorem Audit.III_2 : type_of% @Elements.BookIII.Prop2 := … inside_of_between …`. `check_rules` covers `Audit/`.

**j. Book III further reading.** These are the researched lines, verified twice:
- 24 works, 23 of them new, in a new shelf "The circle, and where Book III leads", plus `references.bib`;
- 82 lines, about 2.2 a page, so III.11 and III.19 get lines again;
- every work described in full the first time it appears in each book;
- Thomas's Loeb is linked to Harvard, not marked free.

**k. Additions that close every remaining review point.**

*Certificate regressions* (the review asked for them by name):
- `tests/certificate_expectations.json` originally pinned that `III.1 Por.` includes
  `Tacit.centre_unique` and `III.1` does not. The membership pin was later dropped, with
  the owner's approval, ahead of retiring that axiom; the
  [decision record](0002-decisions.md#19-october-2026) owns that change. A negative test
  plants a dependency that occurs **only in a declaration's type** and checks the unified
  walk finds it.

*Overlap catalogue columns*: proposition, rule, **where the rule first enters the development** (its first user), which dependencies bring it in, what the Lean proof does, and the audit lemma. Deriving these propositions from weaker assumptions is recorded as an optional, separate, dependency-audited workstream, not this plan.

*Evidence levels:*
- A README section, "What the checks show", gives Astra's evidence table: a Lean proof term, no `sorryAx`, the fidelity check (wording only), the semantic review, the numerical model tests, the informal model argument, and a future formal interpretation. Each says what it does and does not establish.
- If the scratch harness has the hyperbolic check (all axioms except Postulate 5 and those tagged Euclidean hold), commit it as tests/model/hyperbolic.py with its results. Even so, the pages keep "this proof uses". Any independence claim must name that evidence.
- The formal model milestone is defined in MODEL.md:
  1. the vocabulary as an interpretable signature;
  2. a Mathlib plane instance in a separate package;
  3. the exact 87 laws proved, degenerate cases included;
  4. the lock hash tying them, so that any axiom change breaks the model proof.

*Three things kept apart* in CERTIFICATE.md's text:
- Heath's references;
- the Lean's dependencies;
- the reconstruction of the argument (review records and gap catalogues).

Also: "an absent bracket does not mean Euclid gave no reason, and a bracket is Heath's, not a machine-checked reconstruction."

*Correspondence notes visible on the page*: render.py prints the record's `[[passage]]` notes (what a helper does, where sentences are grouped, where the argument is different or the claim unformalized) as a short "How the Lean follows the text" list keyed to each sentence's first words, just above the listing. They are not hidden in `review/`.

**Stage 1 crew.** About 22 agent slots in 4 waves:
1. A contracts commit (parse_ref, field list, schema).
2. In parallel: certificate, checks, the records crew (7), evidence, overlaps, wording, references.
3. Render (2 agents).
4. A bosun merges, regenerates and runs the full CI, followed by two blind page readers.

Then:
- **Release.** Draft the book-III notes in the new precise terms, plus corrections to the book-I and book-II notes ("each one following Euclid's own proof" becomes scoped). **The owner approves.** Then tag and publish.

## Stage 1b: the standards (Astra's layered guide, adapted)
- `AGENTS.md`: Astra's §14 entry brief, adapted. Codex reads it.
- `CLAUDE.md`: `@AGENTS.md`.
- `CONTRIBUTING.md`: the human entry point, linking to the rest.
- `docs/STYLE.md`: voice, page, commentary, words, quotations, figures. The voice rules become **defaults**:
  - no count of "we" and no forced rhetorical leads;
  - "state facts directly; qualify uncertainty precisely";
  - a modern method may recur when it is clearest;
  - usually 250–450 words, with reasons for exceptions;
  - Astra's avoid/prefer table.
- `docs/FORMALIZATION.md`:
  - statement coverage and quantifiers;
  - representations and their bridge theorems (and where those sit in the dependency order);
  - construction data versus correctness evidence;
  - Lean as an argument (no dummy citations, no artificial hypothesis uses; label alternative routes);
  - where lemmas live;
  - the evidence table (Lean check / no `sorryAx` / fidelity / semantic review / edition review / regeneration).
- `docs/WORKFLOW.md`:
  - proposition briefs approved **before** proofs, and frozen-brief corrections;
  - roles (statement owner, proof contributor, edition contributor, independent reviewer, integrator);
  - waves; file ownership (the integrator owns generated output);
  - review records tied to a commit;
  - mutation tests run in isolation;
  - release criteria and severity (blocking / material / editorial);
  - how a book is made and released (our voyages, read-throughs and blind tests).
- `docs/templates/proposition.md`: task, handback and review templates, matching `review/SCHEMA.md`.
- `scripts/check_style.py` enforces hard rules only:
  - every link on docs/reading.md;
  - letters in NN.svg all and only Heath's, and no letters in idea figures, as stage 1b made it; by the owner's decision taken after it, the idea figures are to carry Heath's letters at every point they show, each one that Euclid's figure draws, and the check is to change with them (revised 18 October, below);
  - palette and strokes;
  - no em dashes, retired refrains or crew talk;
  - caption length;
  - book intros present.

  Defaults are reported, not failed.
- One home per rule. Duplicates are removed and linked.
- **AGENTS.md** opens with Astra's ten rules and states the priority order: "preserve the source, state the mathematics accurately, follow the declared route, explain clearly; stylistic defaults serve those obligations". Requirements and defaults are listed separately.
- **FORMALIZATION.md** also carries:
  - the code states what we formalized, not what Euclid intended, and a discrepancy is recorded and reconciled across documents;
  - a guide never grants authority to change foundations, weaken checks or publish;
  - unused hypotheses and surprising dependencies are review prompts, not verdicts: **no dummy citations, no artificial hypothesis uses**;
  - a helper supplies an identified step and never hides the whole conclusion.

  The Book III crew orders said "every hypothesis should be used" and asked bosuns to check that Euclid's brackets all appear among the citations. That rule is replaced in the order templates and in the fleet script.
- **STYLE.md** also carries:
  - "Euclid" for the historical argument, "Heath" for the translation, "Lean" for the checker; production details stay out of the public mathematics;
  - nothing competitive: no unsupported claims of novelty or superiority, and related work cited accurately and warmly (this keeps the owner's rule);
  - further reading only where apt, verified, never to fill a slot;
  - figures: departures from Heath's figure in the page's figure note, a one-case figure never implying the other cases, a reductio's impossible figure explained.
- **The colour figures are to carry Heath's letters** (revised 18 October). The owner decided on 17 October, after stage 1b was done, that the figures at a glance, in Byrne's colours, are to carry Heath's letters at every point they show, each one that Euclid's figure draws, with the same names as Euclid's figure, the text and the Lean. In the owner's words that day: "Proof without words is one thing - proof without Point labeling is quite another!" Byrne's diagrams use colours in place of letters, as his title says, and are a delight without them; the letters are wanted because a proof is read by its points, so that a reader passes from the colours to the proof by the same A and B. This replaces "no letters in idea figures" in the first text. The rule is to go into STYLE.md, section 7, its one home, in place of its "no letters", and `check_style.py`'s S14 is to change with it, as the figures are lettered.
- **Book briefs, one home per book's decisions.** Refresh 0004 (Book III) with the arc and segment representation, construction inputs and exceptions. Gather Books I and II's vocabulary, representations, shared lemmas and exceptions (now scattered over 0001–0003) into short book briefs. Each book's introduction links its brief.
- **Reviewed examples** (docs/examples.md), each tied to a commit and a reason:
  - a short construction (I.1);
  - a hard diagram argument (I.7 or III.8);
  - an area proof (II.4);
  - a page with a declared exception (III.31 or III.24, after stage 3).

  They guide judgment; they are not templates to copy.

Stage 1 also carries these status notes, with no Lean change:
- DefinitionsIII.lean's docstring and brief 0004 say plainly that the measure carries no radius;
- III.26 and III.27 hold for any two circles as stated, while III.28 and III.29 need equal circles;
- III.24 proves equal circles and equal measure, not placement;
- III.25 is handed its circle.

The review records carry tags for these: `redundant-hypothesis`, `angle-measure`, `segment-with-circle`.

*Overtaken on 18 October by stage 3, as brief 0006 froze it: III.24 concludes that the segments are congruent, by placement, and its earlier statement, equal circles and equal measures, is its companion `Prop24.equalCircles`; III.26 and III.28 conclude that the circumferences are congruent too, so III.26 now needs its equal circles, and III.27 still holds for any two circles. The notes above are kept as they stood.*

What remains of stages 1 and 1b is kept in [docs/PROGRAM.md](../PROGRAM.md), section 3, with the state of the work (added 18 October).

## Stages 2–4: representation and generality

*Revised 18 October 2026: the statements and routes of stages 2 to 4 are brief 0006's, which revises this design. This section keeps the design with its dated revisions, and brief 0006 governs where the two differ.*

**Design rule.** Every generalization is a **companion theorem** (`PropN.general`, `.figure`, `.square`) next to the unchanged, annotated `PropN`, which stays as Euclid's worked configuration.
- check_fidelity reads only `theorem PropN`, so its Heath sentences stay put.
- Companions get certificate entries through stage 1's `companions` list, and the page shows them with their own certificate column.
- Each is approved as a **statement with `sorry` before any proof work** (WORKFLOW.md, piloted here). The captain approves the briefs.

**Ground** (stage 2 wave R1):
- `Elements/Figure/Sums.lean`, plain Lean: `Magnitude.sum` over lists, `sum_append`, `sum_singleton`, `InOrder`, `segments`, `endOf`, `InOrder.between_end`.
- Brief 0006 (statements of every companion and of the Book III restatements).
- The certificate and render support for companions.
- A policy check that only III.24, `Arcs.lean` and the placement files themselves (`Placement.lean` and its case files, whose assembly cites the `Placement.*` names) may cite `placement`. It matches the `Placement.*` names, since placement is split across several files (revised 18 October; stage 3). (Added to `scripts/check_fidelity.py` on 18 October, with two negative tests: read from the source, and from the certificate's shared steps.)

**Stage 2: Books I and II**

*I.40 general*
- `Prop40.general`: four base ends on one line L, equal bases, equal areas, same side ⇒ ∃ M parallel to L through A and D. Plus `Prop40.join` (A ≠ D ⇒ AD ∥ BC) and `Prop40.special` (the current statement as a corollary).
- Proof: Euclid's own argument (`Prop31.line`, `Prop30.meet`, I.38 already general, `OnRay.eq_of_area_eq`). It covers separated, touching, overlapping and oppositely named bases.

Reconciled 19 October 2026: `Prop40` and `Prop40.general` now retain Euclid's closing
reductio. The contrary supposition makes the constructed intersection differ from D.
I.38 and Common Notion 1 give equal areas; `between_cases` and `area_lt_of_cut`
contradict them in either order on the ray. Neither proof calls `OnRay.eq_of_area_eq`.
The route is `euclid`; the statements, admitted configurations and companion registration
are unchanged, including the general companion's coverage of coincident vertices.

*I.45 for a figure given by its corners* (revised 18 October, to the owner's decision later on 17 October)

*Overtaken later on 18 October by brief 0006, as revised and frozen: I.45 is `full`, by `Prop45.apart`, for any figure given with triangles that lie apart, beside `Prop45.figure`, for a figure with one boundary glued together, and `Prop45.fan`, the main companion, for the division from one corner with its two conditions checked; `Rectilineal`, `Fitted` and `Prop45.sum` are restored. The design below is kept as it stood.*
- A rectilineal figure is given by its corners A₀, A₁, …, Aₙ, in order round it, and taken as one that the straight lines from A₀ divide into the triangles A₀A₁A₂, A₀A₂A₃, …, A₀Aₙ₋₁Aₙ, as Euclid and Byrne divide it: Euclid's DB divides his ABCD into ABD and DBC. Every convex figure is so divided from any corner, Euclid's ABCD among them. Byrne's I.45 figure is not convex, and both his lines start from its re-entrant corner. A figure that is not convex may need its first corner chosen, and some figures have no such corner.
- `Prop45.append`: the parallelogram so far plus one triangle, preserving the angle (the second half of I.45's proof).
- `Prop45.figure`: a parallelogram in the given angle equal to those triangles taken together, built one triangle at a time, I.42 for the first and `Prop45.append` for each of the rest. Euclid's ABCD with DB joined is the case of four corners, D, A, B and C.
- Nothing is claimed of another division of the figure. That every division gives the same sum is a step Euclid takes for granted; it goes in the gap catalogues of Books I and II, with thanks to David Hilbert, who proved it for the measure of area he builds from his own axioms ([*The Foundations of Geometry*](../reading.md#hilbert1902foundations), chapter IV), not for this edition's area.
- A pentagon needs no change of statement. The iteration is a departure to note.
- This replaces the design first written here, which the owner had chosen earlier on 17 October: a `Rectilineal` figure of pieces glued edge to edge in any dissection (`Fitted`), with `Prop45.sum` and `Prop45.figure (R : Rectilineal)`. `Rectilineal` and `Fitted` are withdrawn, and brief 0006 will give the statements in full.

*II.1 general*
- `Prop1.two`, one cut, re-running II.1's construction.
- `Prop1.general`: induction over `InOrder (B :: ps)`, rect(A; B, end) = Σ rect over consecutive pieces. One and two pieces are included, and the three-piece result is `[D, E, C]`.

*II.14 general* (revised 18 October, with I.45)

*Overtaken later on 18 October by brief 0006, as revised and frozen, as for I.45: `Prop14.apart` and `Prop14.square` carry `full`, beside `Prop14.figure` and `Prop14.fan`; `Prop14.sum` takes any list of triangles. The design below is kept as it stood.*
- `Prop14.rectangle` is proved directly, by the second part of Euclid's proof, keeping his semicircle and his cases (II.5 and I.47), and does not cite II.14. (Revised 18 October, as brief 0006 decides: the first text applied Prop14 to the rectangle's two halves, a route now withdrawn, since it would prove II.14 from II.14.)
- `Prop14.general`, for a figure given by its corners, by `Prop45.figure` with a right angle, then the rectangle.
- `Prop14.square` returns `Square P Q S T` with its area (I.46, `Square.described`), equal to the figure's triangles taken together. As in I.45, nothing is claimed of another division.
- The old two-triangle form is the case of four corners. The first text had `Prop14.general (R : Rectilineal)`, and `Prop14.sum` for the two-triangle form.

Book II's area correspondence is reviewed as part of stage 5.

**Stage 3: Book III arcs and segments**

*Definitions* (DefinitionsIII.lean, captain-owned, **no new axioms**):
- `structure Arc (circle, B, C, K)` and `Arc.Drawn`;
- `OnSideOrLine` (a closed half-plane), `OnArc`, `InSegment`;
- `Arc.Less`, `.Semicircle` and `.Greater`, decided by the **centre's** side of BC;
- `Arc.SameKind`, and `Arc.measure := circumference …`;
- `Places f S T` (into, onto, distance-preserving);
- `Arc.Congruent`: ends to ends, segment onto segment, arc onto arc.

The 4-argument `circumference` and `standing` stay as Heath's measure words.

*Ground*
- Book Zero: `Arc.congr_side`; `Arc.meets` (a ray from inside the chord meets the arc).
- `Elements/BookIII/Placement.lean`, the long pole, prototyped first, with its cases in files of their own under `Elements/BookIII/Placement/` (revised 18 October; below):
  - `placement`: equal bases AB = CD carry E's closed half-plane onto F's, preserving distances to the base ends, and carrying the side of the base and betweenness on it both ways;
  - `f` is chosen by epsilon. Existence through I.22 (`Prop22`), as step 2 below plans; uniqueness from I.7 and I.20; distances from I.8, `Prop24.within`, C.N. 3 and I.4; onto by the reverse construction.
  - **No new axiom, no time limit and no fallback.**
- `Arc.eq_of_aligned` (same chord, same side, equal radii, same kind ⇒ the circles, arcs and segments coincide), by I.7 and `circle_eq`.
- `Prop23.point` (on the circle ↔ equal angle; inside ↔ greater angle), by I.16, I.21 and III.21.
- `Circumference.add` (for Book IV).

*Placement: the concern, and how it is de-risked* (added 18 October)

The concern was never time. It was whether every case of carrying one segment onto another can be proved from the 87 axioms, with no motion axiom beyond I.4 and I.8. The feasibility analysis says it can:
- every case closes with lemmas already proved;
- no Postulate 5 is used, and no continuity beyond what I.22 uses;
- each piece is a first-order ruler-and-compass statement of the kind System E's completeness theorem covers.

Placement is about 450–600 lines of Lean, and the whole of stage 3 about 850–1,100.

The owner decided on 17 October that placement has no fallback and no time limit: III.24 waits for a proved placement lemma, and the other work goes on in parallel. If a case turns out to need a fact the axioms lack (it is not expected), the proof stops and the owner decides. No axiom is ever added quietly.

Corrections to the design:
- **The comparison is based at whichever end, A or B, avoids the bad case.** This removes the equal-angle and supplementary-angle branches.
- **The statement is strengthened.** The side clause becomes `SameSideOf P E A B ↔ SameSideOf (f P) F C D`, and `Between A P B ↔ Between C (f P) D` is added.
- **The verification line is restated** (Verification, below). Placement's transitive axioms will include superposition, since every distance fact rests on I.4 and I.8.
- **The I.20 degeneracy lemma** (three points lie on one straight line exactly when one of I.20's three inequalities is an equality) goes in a new Book I file, `Elements/BookI/HelpersTriangles.lean`, after I.20 and citing nothing later. FORMALIZATION, section 6, puts a shared step that cites a proposition at or after it, and `Elements/BookI/Helpers.lean` comes before I.20: I.7 imports it. The lemma's owner is step 2's task, below. Stage 4's `Prop15.le_diameter` needs it too.
- **Placement is split across several files,** so that parallel provers never share one, each owned by the task of its step below: the cases under `Elements/BookIII/Placement/`, after Book I; then `Placement.lean` itself, the assembly (step 4), after them and before III.24. Brief 0006's table of homes and owners names each file and the step that owns it. The policy check matches the `Placement.*` names, and lets only III.24, `Arcs.lean` and these placement files, whose assembly cites those names, cite `placement`.

The order of work, de-risking first:
- **Step 0, a spike by the coordinator.** The definitions, the `placement` statement and every sub-lemma's signature, all with `sorry`. Then the assembly proved from the stubs, and III.24 restated and proved from a stubbed `placement` and `Prop23.point`. This tests the interfaces, which is where the real risk lies.
- **Step 1, one strong prover:** the strict-angle case for two points off the line, and the choice of base end.
- **Step 2, Codex, best of two, in parallel on separate files:** the I.20 lemmas, existence (through I.22, `Prop22`), `Prop23.point` and `Arc.eq_of_aligned`.
- **Step 3, Codex:** uniqueness (I.7 off the line, and the I.20 lemma for the mixed cases), both points on the line, and the distance case with one point on the base and one off it (I.8, then I.4). Its files are those brief 0006's table assigns to placement step 3.
- **Step 4, the strong prover:** the assembly, then III.24, III.26 and III.28, then `Arcs.lean`.

*III.24 restated*
- It now concludes `Arc.Congruent ⟨AEB,A,B,E⟩ ⟨CFD,C,D,F⟩`, following Euclid: placement (A on C, AB on CD), B on D, then each point of the arc lands on CFD by I.8 + III.21 + `Prop23.point`, and inside points go inside. III.10 is not needed, and the correspondence note says so.
- The radius proof stays as `Prop24.equalCircles`, displayed as the **alternative formal proof**.
- `Prop24.equalMeasure` is derived from the congruence, so III.26's [III. 24] stays honest. (Renamed 18 October, as brief 0006 renames it: the first text had `Prop24.circumference`, whose short name shadowed the definition `circumference` inside the namespace `Prop24`.)
- **No fallback** (revised 18 October, to the owner's decision of 17 October): III.24 waits for a proved placement lemma, however long it takes, and the other work goes on in parallel. If a case of placement needs a fact the 87 axioms lack, work on it stops and the owner decides; no axiom is added quietly.

*III.26 and III.28 upgraded* so that "in equal circles" does real work: each clause concludes equal measure ∧ `Arc.Congruent` (III.26 by III.24 on the remaining segments; III.28 through III.26). The mishnah notes the mild departure from Euclid's "whole minus part". The `.1` calls in Prop27, Prop28 and Prop30 are updated.

*`Elements/BookIII/Arcs.lean`* (after III.29, as validation, so the argument can't go in a circle):
- `Arc.measure_eq_iff`: in equal circles, equal measure ↔ equal chords ∧ same kind (III.28, III.29, `Prop29.size`);
- `Arc.congruent_iff`: congruent ↔ EqualCircles ∧ equal measure.

*Migration.* Each step leaves the build green:
1. definitions;
2. ground lemmas;
3. `Prop24.equalCircles` plus a temporary tail;
4. restate III.24 and switch Prop26:92;
5. upgrade III.26 (fix Prop27:74 and Prop28:108), then III.28 (fix Prop30:88);
6. add `Arcs.lean`;
7. regenerate, then update the mishnah and gaps for III.23, 24, 26 and 28.

**Stage 4: III.14, III.15, III.25**

*III.14 and III.15*
- `Foot E A B F`: if the centre is on the line, F = E; otherwise the perpendicular. So distance zero is allowed with no zero-length right angle.
- `Prop14.general` covers two non-diameters (Prop14), two diameters, and one of each (I.20 and `len_ne_zero`).
- `Prop15.le_diameter` (≤, with equality ↔ through the centre, by I.20) and `Prop15.nearer`.

*III.25*
- `Prop25` restated so the construction core receives the segment only as a point predicate `S` plus the meeting fact Euclid reads off it. It never sees a circle or centre, and returns B, D, E and the circle γ described by Postulate 3 (III.9 moves out).
- `Prop25.complete` verifies, for `S := OnArc · ⟨α, A, C, P⟩` (with `meets` from `Arc.meets`), that γ = α and that every point of the supplied arc is on γ (III.9, `circle_eq`).
- The general construction-input convention goes into the Book IV brief. There is no construction calculus now.

## Stage 5: the consolidation review, then the consolidation release
- **Full semantic records for all 99.** Every passage is classified as carried / helper / grouped / different / unformalized, with `stage = "full"` keyed to the reviewed commit.
- **Records:** about 6 reviewers, one per range, plus 3 adversarial verifiers. Book II's area correspondence gets particular attention: which expression is which drawn piece, why the pieces subdivide, and the order and incidence facts.
- **Figures:** each lettered figure against Heath's scan, the colour figures' letters included (revised 18 October). Captions name the case shown when a theorem covers several (`[figure].case`).
- **Hardest blocks:** a mishnah paragraph only for the hardest formal blocks (I.7, I.35, I.47, III.8, and others), saying what obstacle the block resolves and why Euclid didn't need to say it.
- **A start-to-finish read-through:** 6 sequential readers, a measurer, 3 figure auditors, a judge, a critic and a fixer. Its findings feed the standards documents.
- **The pilot check Astra asks for.** The guide is piloted on three kinds of task in stages 2–4, each worked by parallel contributors with disjoint files:
  - a straightforward one (II.1 general);
  - a construction or generalization (I.45 and II.14 for a figure given by its corners; revised 18 October, from "over a dissection"; and, by brief 0006 as frozen, for a figure given with a checked division into triangles);
  - a representation or route exception (III.24 with its alternative proof).

  An independent editor then reads the resulting pages consecutively, for shared voice, consistent terms, truthful scope and an even depth of explanation. The defaults and examples are adjusted before stage 5 applies the guide to all 99.
- **Reviewers' checklist in stage 5** also hunts for:
  - dummy citations (calls whose results are unused, made only to match a bracket);
  - artificial hypothesis uses (`have _ := h…` and the like);
  - helpers that conceal a whole conclusion (Book I's `Figure`-structure helpers included).

  Each hit is fixed or declared in its record. A script lists the candidates (unused `have` bindings, `_`-named citations).
- **Book II's area correspondence** (which expression is which drawn piece, why the pieces subdivide) gets one compact explanation in Book II's introduction, linked at its important uses, not longer commentary on every page.
- **Consolidation release** of Books I–III. The notes are drafted from the generated scope summaries, and **the owner approves** before the tag.
- **After this:** Book IV starts with briefs approved before proofs. Each new foundation gets a one-statement prototype before any fleet: V (V.18's fourth proportional), VII (VII.16 without `Nat.mul_comm`), X (X.1), XI–XIII. The Mathlib formal model is its own milestone.

## Stage 6: acceptance, the checklist that says Books I–III meet the standard

This gates the consolidation release.

**`docs/ACCEPTANCE.md`**, one checklist with each item marked **[machine]** or **[review]**. It merges Astra's 95 criteria with the guide's §13 release criteria.

*Per proposition (all 99):*
1. [machine] Every declaration the page displays (the main theorem, its porism, its companions) is proved, and its certificate is shown. There is no `sorryAx` in its dependencies.
2. [machine] The statement fingerprint and Lean hash match a review record at `stage = "full"`. The record names its commit.
3. [machine] Every scope, route, representation or overlap exception in the record appears in the page's top line and field table. Every unformalized passage has a clause map. No disclosure lives only in the mishnah (phrase grep).
4. [machine] Policies hold: no superposition outside I.4/I.8; placement cited only by III.24 and Arcs; no later citations; Postulate 5 boundaries; the axiom lock matches.
5. [machine] Every `--` run is carried or declared, and every passage note is rendered.
6. [machine] Heath's text and the enunciation match; quotations are checked; letters are plain; links are on docs/reading.md; scan links resolve.
7. [machine] The figure letters are all and only Heath's; the idea figures carry Heath's letters at every point they show, each one that Euclid's figure draws (revised 18 October; the first text had no letters in the idea figures); the palette and strokes are right; a `[figure].case` is given when a theorem covers several cases.
8. [machine] Style hard rules pass (check_style), and the pages are regenerated clean.
9. [review] The statement says what Euclid's enunciation says, or the qualification is exact. Quantifiers, conclusions, hypotheses and cases have been checked.
10. [review] Each substantive passage is carried, or its helper, grouping, alternative or omission is named truly. There are no dummy citations, no artificial hypothesis uses and no concealing helpers.
11. [review] Representations used here (rect/sq, arcs, segments, figures given by their corners) have their bridge theorems, sitting correctly in the dependency order (revised 18 October; the first text had "dissections").
12. [review] The commentary is accurate, specific to this proposition, in the common voice, and explains the hardest block. Attributions are checked.
13. [review] The figures agree with the proof's geometry and scope.
14. [review] A reviewer other than the author signs off; the reviewer and the commit are recorded.

*Per book:*
- [machine] The completion summary is generated and true.
- [machine] The gap catalogue and overlap catalogue are current.
- [review] Reading the book straight through, it flows and the voice is common.
- [review] The remaining limitations are deliberate, few and stated plainly. For Books I and II, I.45 and II.14 cover only a figure that the straight lines from one of its corners divide, and do not prove that another division gives the same area. For Book III these are only the mixed-angle clauses of III.16/31 and the III.2-style overlaps. (Revised 18 October: with no fallback for placement, III.24's alternative proof is no longer a limitation, and the limits of the corners form are added. Overtaken later that day by brief 0006, as frozen: I.45 and II.14 take any figure given with a checked division into triangles, and what they leave unproved is that every figure can be so divided and that another division gives the same sum, as the tag `figure-with-dissection` states.)

**`scripts/check_acceptance.py`** checks every [machine] item across all 99 propositions. It reads every [review] item from the review records (each must be `pass` with a reviewer and a commit). It writes `docs/reports/acceptance-books-I-III.md`: a table per proposition and per book, with every failure listed. CI runs it, and **the consolidation tag requires zero failures**.

**Independent acceptance audit with Jev.** Astra's guide asks that "a reviewer other than the author" sign off. Claude and Codex wrote the work, so a **third model family, Jev** (TypeSafe), audits the [review] items .

*A fresh client*, written for Stoicheia from TypeSafe's public documentation.

*What Jev is.* A hosted **multiple-choice decision model**, not a chat model: it is given a question and its options, and returns a choice with probabilities. The service is `https://api.typesafe.ai`, with a decision endpoint (`POST /v1/systemone`) and a model listing. The exact request and response schema is taken from **TypeSafe's public documentation**, fetched when we build the client.

*The client.* `scripts/audit/jev.py`, standard library only (urllib). It handles model preflight, one decision request, retries off, a timeout, and per-row JSONL output with the choice, probabilities, model and latency.

*The key.* Read from a local key file named by `STOICHEIA_JEV_KEY_FILE`. It is never printed, logged or committed, and it is redacted from any echoed response. The audit runs locally, and Stoicheia is public, so nothing restricted is sent.

*Smoke first.* Model preflight, then one trivial decision, before any audit traffic.

*Sample already run* (17 October 2026, the owner's key, a fresh inline script):
- **III.14 text test**, comparing Heath's enunciation with the Lean statement: Jev chose "restricted" (p = 0.73, confidence 0.59) and gave "the hypotheses exclude diameters" a noul of 0.82. Both are correct.
- **I.1 figure test**, the lettered SVG rendered to PNG at 700 px: two circles (1.00), C where the circles cross above AB (0.99), D and E on the circles (0.97). All correct.
- Model `jev-1.13.0` (`jev-latest`); 1.14 is `jev-preview`. About 0.15 s and 700–1,300 input tokens per call.
- Images need the header `TypeSafe-Danger-Zone-Images: true`, the `assets` map, and PNG or JPEG of 280–1568 px. SVGs are rendered with rsvg-convert first.
- Each audit run **pins a model id** (e.g. `jev-1.14.0`) and records it with the results.
- The moderate confidence on a correct answer is why every low-confidence answer goes to adjudication.

*Figures too.* Jev's image input makes a cheap independent check of all 198 figures possible:
- letters present and placed as Heath's text needs, in both figures (revised 18 October);
- incidences (C where the circles meet);
- the idea figure's colours against its caption.

Each [machine] figure item that can't be scripted becomes a Jev image question, and its disagreements go to the adjudicator.

*The questions.* Each [review] item is framed as a multiple-choice question per proposition, with only the context it needs. For example, item 9 gives Heath's enunciation, the Lean statement and the record's note, and asks: "Does the Lean statement cover the enunciation? (A) fully (B) restricted, exactly as the note says (C) restricted beyond what the note says (D) cannot tell". There are similar questions for passages (carried / helper / grouped / different / unformalized), representations and figures-against-text.

*Calibration before trust.* A seeded calibration set has known answers:
- the old I.40, II.1, III.14 and III.24 statements labelled "full";
- a planted dummy citation;
- correct records as controls.

Jev must meet a stated accuracy bar on it. Below the bar, Jev's answers become a secondary signal only, and the independent pass falls back to a fresh-context reviewer of another family (Codex `gpt-6-astra` run cold, or Astra itself). Either way the report says which kind of evidence was used.

*Adjudication.* Every Jev answer that disagrees with a record, or is low-confidence, goes to a Claude adjudicator, who verifies it against the code before it counts. Agreements at high confidence are recorded as independent confirmation.

*The loop.* Blocking and material findings go back to a fixer, and the audit repeats on the touched propositions until clean. The raw Jev outputs, with no key, are committed under `docs/reports/acceptance/jev/` as evidence, and their cost is noted.

*Prior art.* The owner recalls a GitHub project that does this kind of "everything checks out" checklist. Before building, look for it (Massot's leanblueprint `checkdecls`, which checks that every declaration a blueprint names exists, is the obvious relative). Adopt or credit whatever fits.

**Cold re-score.** Finally Astra re-reviews the tagged candidate cold, with the same question as before: how well do Books I–III meet the README's goal, 0–100. The owner runs this in ChatGPT. The target is about 95 for each book, and any defect named goes back through the loop.

**Status, 21 October 2026.** The cold re-score is now made as the versioned [review
rubric](../RUBRIC.md) says, by three reviewers of three model families, and its gate is
recorded there.

**Status, 29 October 2026.** The Jev audit's card,
[#36](https://github.com/dodecaplex-co/stoicheia/issues/36), closed as not planned on 28
October. On 29 October the owner made the cold outside reading the independent audit, by two
reviewers, Claude and Astra: each scores every book by the [review rubric](../RUBRIC.md), on
the release candidate, and the gate is recorded there. The owner's words are quoted in
[#703](https://github.com/dodecaplex-co/stoicheia/issues/703), the coordinator's record of
them. The plan for Jev above stays as it was written.

## Crew, tools and safety
- **Lean proofs:** Codex sailors, best of two, with Claude bosuns and reviewers, as on the Book III voyages. Placement goes to the strongest prover and to Codex in the order under stage 3, with no time limit (revised 18 October). The sailors read AGENTS.md automatically.
- **Prose, records, review and design:** Claude agents.
- **Ownership:** the captain owns Foundations/Definitions*, the lock, decisions and merges; one writer per file; the integrator owns the generated output. Negative and mutation tests run in isolated worktrees.
- **Rough scale:** stage 1 is about 22 agent slots, stages 2–4 about 13 tasks in 3 voyages, and stage 5 about 20 agents.
- **Public actions need the owner's OK:** the release notes for book-III, the book-I/II note corrections, the consolidation release, and any GitHub description change.

## Landing work: pull requests

*Added 18 October 2026, to the owner's decision of 17 October.* The rules live in the pull-request discipline of [docs/WORKFLOW.md, section 10](../WORKFLOW.md#10-how-a-book-is-made-and-released), their one home. The ruleset on main already requires a pull request; pull request #1 writes the discipline there, in place of direct pushes to main. Stages 2, 3 and 4 each work on a branch of their own, and each piece of a stage lands as its own reviewed pull request; a change to a check lands first, on its own, before the code it checks.

## Astra's recommendations, traced

The same table, with each done-criterion, goes into `docs/reports/outside-review-01.md`.

| Astra's point | Where answered |
|---|---|
| Porism bug; separate entries; III.1 centre_unique; porism-only P5/superposition/later regressions; walk types too | 1a, 1b, 1k |
| Proof status / coverage / route / representation fields; scope note beside the badge; III.31's generic sentence | 1d |
| Arc object, segment predicate, congruence, bridge theorem; III.24 segment meaning; avoid the III.26–29 circularity | 3 |
| Axiom–proposition overlap catalogue (rule, first entry, dependencies); weaker-assumption workstream optional | 1i, 1k |
| Commit the model harness, seeds and mutations; law-by-law model; axiom signatures; evidence levels; Mathlib model milestone | 1c, 1h, 1k |
| "This proof uses", not "needs"; hyperbolic interpretation before any independence claim | 1e, 1k |
| "Heath's references"; second graph from the Lean; three objects kept apart | 1e, 1g, 1k |
| Construction inputs; III.25 pilot; III.1 left as is; the segment sentence fixed | 1e, 4 |
| Jump links, bottom nav, fold helpers, scope by the badge, scan links | 1d, 1f |
| Prototype each new foundation; settle Book IV interfaces first | 5 (after) |
| 95: semantic review of all 99 with the five relationships, records keyed to a revision, exceptions near the status | 1d (exceptions), 5 (full), 1k (visible notes) |
| 95: I.40 general; I.45 over a supplied dissection | 2 (I.45 for a figure given by its corners, divided as Euclid and Byrne divide it; revised 18 October; then, by brief 0006 as frozen, over a supplied dissection, checked) |
| 95: II.1 any number; II.14 general with a drawn Square; Book II area correspondence | 2, 5 |
| 95: arcs by membership, kinds by the centre, theorems (i) and (ii) | 3 |
| 95: III.24 congruence, alternative proof displayed, Euclid's proof in full | 3 |
| 95: III.25 construction core without the circle; correctness separately | 4 |
| 95: III.14 diameters (zero distance); III.15 diameter bound split out | 4 |
| 95: III.16/31 clause maps; III.2 overlap in the visible summary; completion summaries say so | 1d |
| 95: companions certified; captions name the case; hardest blocks explained | 1a, 5 |
| 95: statements and representations reviewed before proofs (later books) | 1b WORKFLOW, 5 (after) |
| Guide: three parts plus AGENTS.md; one home per rule; book briefs; reviewed examples | 1b |
| Guide: priorities; requirements vs defaults; voice via concrete choices; avoid/prefer table | 1b |
| Guide: predictable page; three status questions over the same declarations | 1b, 1d |
| Guide: briefs before proof; frozen-brief corrections; construction data vs evidence; representations justified | 1b, 2–4 |
| Guide: Lean as an argument, no dummy citations or artificial hypothesis uses, lemma placement | 1b, 5 |
| Guide: commentary functions; sources; figures checked as geometry | 1b, 5 |
| Guide: roles, waves, file ownership, integrator owns generated output, isolated mutation tests, revision-tied reviews | 1b |
| Guide: templates; evidence table; validation on the integrated revision; release criteria and severity | 1b, 1k |
| Guide: the pilot on three task kinds, then an independent editor | 2–4, 5 |
| What to preserve (named assumptions, careful construction conclusions, separate magnitudes, candour, separate modern commentary) | kept; said so in the response |

## Verification

**Stage 1**
- CI green, with the new jobs: links, model, `lake build Audit`, the lock, review records, and README freshness.
- Negative tests catch I.15 Por. plants (Postulate 5, superposition, a later citation) without blaming I.15, a lock miss, a weakened axiom, a stale review fingerprint, and a missing unformalized passage.
- III.1 shows 56 and III.1 Por. shows 57, with `centre_unique`.
- Every exception from the seed list appears in its page's top line.
- No "never need" or "Euclid cites" remains (lint).
- Two blind readers check III.1, III.2, III.16, III.31, I.40, II.14 and one plain page.

**Stages 2–4**
- Every companion is proved and certified. Old statements follow as `.special`.
- Superposition is not among `placement`'s direct axioms. The 87 axioms in `Certificate/axioms.lock` are unchanged; its vocabulary gains the stage's new words (`Arc` and the rest) through `check_fidelity.py --write-lock` and a decisions entry, with `tests/model/lock.sha256` updated and [tests/model/MODEL.md](../../tests/model/MODEL.md) read again in the same change, as [FORMALIZATION](../FORMALIZATION.md), section 7, and the lock's header require. (Revised 18 October: the first text asked `#print axioms` of `placement` to show no superposition, which can never pass, since every distance fact rests on I.4 and I.8; and a lock unchanged in every line could not pass either, since the new statements reach new words.)
- The `Audit/` file stops compiling where the old redundancy is gone (III.26 no longer provable without EqualCircles), which is the intended signal; update overlaps.md.
- Statement fingerprints force a re-review of every touched record.

**Stage 5**
- All 99 records are `full` and current.
- The read-through's blocking and material findings are resolved.
- Every claim on the consolidation release notes traces to a generated summary.

## Critical files
- Certificate/Facts.lean
- scripts/check_fidelity.py, render.py, heath.py, negative_tests.py, plus new check_style.py and check_links.py
- review/ (new), tests/model/ (new), Audit/ (new), Certificate/axioms.lock (new)
- Elements/Foundations/DefinitionsIII.lean, Elements/Figure/Sums.lean (new), Elements/BookIII/Placement.lean with its case files Placement/Strict.lean, Exists.lean, Unique.lean, OnLine.lean and Mixed.lean, and Arcs.lean (new), and Elements/BookI/HelpersTriangles.lean for the I.20 degeneracy lemma (new) (revised 18 October)
- Elements/BookI/Prop40.lean and Prop45.lean; BookII/Prop01.lean and Prop14.lean; BookIII/Prop14, 15, 24, 25, 26, 28.lean
- README.md, CONTRIBUTING.md, AGENTS.md and CLAUDE.md (new), docs/STYLE.md, docs/FORMALIZATION.md and WORKFLOW.md (new), docs/templates/, docs/reports/outside-review-01.md, overlaps.md and model notes
- mishnah/intro/{I,III}.md
- docs/ACCEPTANCE.md, scripts/check_acceptance.py, scripts/audit/jev.py, tests/certificate_expectations.json, and docs/reports/acceptance-books-I-III.md (all new)
- docs/PROGRAM.md (new, the standing tracker; its status board is generated and kept fresh by CI)
