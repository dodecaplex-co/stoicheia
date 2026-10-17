*Astra's draft contributor guide, 17 October 2026, as written. We adopt it, adapted, as `AGENTS.md`, [STYLE.md](../STYLE.md), `FORMALIZATION.md` and `WORKFLOW.md`; see [the response](outside-review-01.md).*

## Stoicheia Contributor Guide

Draft 1, 17 October 2026

## Purpose and adoption

Stoicheia presents Euclid's text, synthetic formal proofs in Lean, figures, and commentary as one coherent edition. Every contributor should preserve the historical text, make the formal theorem's meaning clear, and explain the mathematical work that connects them.

This guide sets a common standard for human contributors and automated contributors, including OpenAI and Codex agents. It proposes an organization of the existing house style and working rules. It is a draft for adoption, not a record of changes already made to the repository. Existing repository instructions and checks remain in force until their replacements are explicitly adopted.

The intended reader is curious about mathematics and willing to follow a proof, but need not know Lean. Contributors and reviewers need the additional technical detail required to maintain the edition. Keep those two audiences distinct.

### The ten rules to carry into every task

1. Read the whole enunciation and proof before working on the formalization.
2. Review the formal statement before assigning its proof.
3. Preserve every substantive quantifier and conclusion, or record the precise qualification.
4. Use Euclid's argument where the page promises that argument.
5. Give a represented mathematical object a justified connection to the object described in the text.
6. Keep historical quotations, project explanations, and Lean declarations distinguishable.
7. Treat a successful Lean check, a transcription check, and a semantic review as different kinds of evidence.
8. Give each file and shared interface a clear owner during parallel work.
9. Tie review and validation to the source revision actually delivered.
10. Prefer accurate, proposition-specific explanation to mechanical prose quotas.

## 1. Organize the guidance in layers

Maintain one authoritative home for each rule. Entry documents should link to these homes instead of copying their contents into several competing guides.

| Document | Responsibility |
| --- | --- |
| `AGENTS.md`, proposed | Short entry instructions for automated contributors: reading order, scope, source ownership, and handback obligations. |
| `CONTRIBUTING.md`, existing | Human entry point, supported kinds of contribution, and links to the detailed standards. |
| `docs/STYLE.md`, existing | Reader-facing voice, page structure, commentary, terminology, quotations, typography, and figures. |
| `docs/FORMALIZATION.md`, proposed | Statement coverage, representation choices, construction inputs, proof correspondence, helper placement, and assurance claims. |
| `docs/WORKFLOW.md`, proposed | Task assignment, shared ownership, dependency waves, review, integration, and release checks. |
| `docs/templates/proposition.md`, proposed | A compact task brief, handback, and review record. |
| The relevant `docs/briefs/` book document, existing pattern | That book's vocabulary, representations, shared lemmas, conventions, exceptional clauses, and dependency plan. |

The agent entry document should be short enough to read on every assignment. The book brief should contain the local mathematical decisions that would otherwise be rediscovered by each contributor.

Keep a small set of reviewed examples, each tied to a revision and a reason for inclusion: a short construction, a difficult diagram argument, an area proof, and a page with a declared scope or route exception. The current STYLE examples from I.1, I.5, I.29, and I.47 are useful starting points. Examples guide judgment; their surface phrases are not templates to copy.

### Resolve disagreements between documents

The implemented code establishes what the current formalization actually says. It does not establish that this is what Euclid intended. When the code, book brief, and reviewed statement disagree, record a discrepancy and reconcile all affected documents.

Follow the user's current instructions and the repository's operative rules. A proposed style guide does not grant authority to change foundations, weaken checks, or publish work. Within an already authorized assignment, the designated coordinator can make the routine decisions delegated to that role.

## 2. Use one public voice

Write as a knowledgeable companion following the figure with the reader: warm, direct, precise, and interested in the mathematical step.

Use concrete objects and verbs. Name the points and say what is constructed, what is equal, where something lies, and why the inference follows. Introduce a technical term when it helps the reader understand the proof, with a brief gloss where needed.

Use “we” for the project's choices and constructions when natural. Use “Euclid” for the historical argument, “Heath” for the translation or commentary, and “Lean” for the formal language and proof checker. Agent identities and production roles belong in internal work records.

State established facts directly. Keep necessary conditions and uncertainty beside the claim they qualify. Historical attribution, interpretation, and the limitations of a representation require the same precision as a mathematical hypothesis.

### Prefer these forms

| Avoid | Prefer |
| --- | --- |
| “Lean cannot represent a segment without its circle.” | “Our current representation of a segment includes its supporting circle.” |
| “This proposition needs Postulate 5.” | “This formal proof uses Postulate 5.” |
| “Lean verifies every word of Euclid.” | “Lean checks the formal derivation. The correspondence with Euclid's argument is reviewed separately.” |
| “The diagram is obviously valid.” | “The intersection lies between B and C; the helper proves the order needed for the next step.” |
| “The formulation is elegant and robust.” | State the specific cases or operations it supports. |
| “For completeness, it is worth noting that...” | State the fact and explain why it matters here. |
| “Euclid forgot to justify the step.” | “The text gives no justification for the intersection; our proof uses the stated intersection rule.” |
| “Unlike previous attempts, this work...” | Describe the project's contribution and cite related work accurately. |

The preferred examples are sentence patterns, not quotations from the repository.

Keep the project's restrained punctuation and familiar geometric vocabulary. Preserve quotations exactly under the transcription conventions. Explain a modern term wherever the reader needs it; the historical text itself remains unchanged.

### Defaults that should guide rather than distort

Retain 250–450 words and roughly three to five paragraphs as the usual size of a mishnah. Permit a shorter explanation when the proposition offers little additional material, and a longer one when a mathematical qualification needs space. A deviation should have a reason in review; it should not trigger padding or conceal a limitation.

Remove quotas for the number of uses of “we.” Do not require a quotation or an inventive modern method on every page. Reusing a modern method is acceptable when it is the clearest correct comparison; link to its earlier explanation and concentrate on the new point.

Use short, proposition-specific bold leads where they help. Avoid forcing every paragraph to open with a rhetorical question or flourish. The reader should recognize a common voice through clarity and judgment, not through identical paragraph rhythms.

Replace “nothing hedged” with “state facts directly and qualify uncertainty precisely.” Replace a blanket ban on comparisons with a ban on unsupported novelty or superiority claims.

## 3. Keep the proposition page predictable

Use the existing source organization and generate the reading pages from it.

1. Book navigation, proposition number, and descriptive title.
2. Heath's complete enunciation.
3. A compact formal-status and scope note, including a visible exception when one exists.
4. The at-a-glance figure.
5. Heath's lettered figure and complete proof.
6. The annotated Lean, with supporting declarations easy to reach and separable from the main argument.
7. The certificate for the formal claims displayed on the page.
8. The mishnah.
9. Specific further reading, a direct source-scan link, and repeated navigation.

Provide jump links so the reader can move between text, Lean, certificate, and commentary. Keep normal pages uncluttered. Detailed task records belong in contributor documents.

### Keep three status questions separate

- **Proof status:** Is the formal result checked, pending its own proof, or dependent on unfinished declarations?
- **Statement coverage:** Does the result cover the full enunciation, a restricted case, a reformulation, or only some clauses?
- **Proof route:** Does it follow Euclid, follow with explicit supplementary cases, or use an alternative argument?

These labels can be summarized in one sentence. A small omission is still an omission; clear disclosure improves the edition without changing what has been proved.

All three descriptions must refer to the same collection of declarations. If a page displays a main theorem, porism, and general companion, its certificate and completion claim must account for each.

## 4. Approve a mathematical brief before proof work

A proposition brief is the stable interface on which parallel work depends. It should normally fit on one page, with a clause table only when the statement is complex or qualified.

Reuse an existing reviewed brief when the statement, representation, and intended route are unchanged. A new brief or renewed mathematical review is needed when the assignment changes those decisions or exposes a discrepancy. For an editorial-only task, record the baseline, owned files, requested changes, and relevant checks; the full proposition contract is unnecessary.

Read the complete enunciation, setting-out, proof, and relevant definitions. Write the proposed Lean statement and translate it back into ordinary mathematical language. Have a reviewer compare that translation with the source before substantial proof work begins.

### Review the following

**Quantifiers.** Preserve “any,” “every,” “any number,” and analogous claims. A fixed number of named pieces or one pictured placement requires a qualification or a general theorem.

**Conclusions.** Account for conjunctions, converses, constructions, uniqueness claims, and porisms. A conclusion is not dispensable because later propositions do not use it.

**Hypotheses.** Distinguish conditions defining the intended objects from restrictions borrowed from the drawing. Record every material additional assumption.

**Cases.** Examine the configurations the intended statement actually admits: relevant boundary positions, equality cases, orientations, orders, coincidences, and major/minor alternatives. Use the proposition to determine the cases; avoid a generic list of every imaginable degeneracy.

**Objects and operations.** State what equality, order, area, ratio, similarity, and other operations mean for the representations used here.

**Proof route.** Identify the main construction and inferences, the propositions used, and the supplementary facts needed to justify the diagram.

**Outputs.** Make construction results easy to recognize. A returned side may determine a square, but the page should point to the proved wrapper that constructs that square.

### Examples of what the brief should catch

- A claim about any finite partition has been stated for exactly three pieces.
- A comparison of chords excludes diameters because its perpendicular-foot interface cannot admit zero distance.
- A figure-area construction takes a sum of triangles without relating them to a valid dissection.
- A selected arc is represented by an angular measure, but no theorem establishes the geometric meaning of equality of those measures.
- A theorem about several types of angle omits one type from its formal conclusion.

These are questions about the statement and representation. They should be addressed before a prover invests in the chosen declaration.

### Correct a frozen brief explicitly

“Frozen” means that other contributors may rely on the interface. It does not mean an incorrect interface must survive.

A proposed change should include the failed case, the old and proposed declarations, the reason, and the affected consumers. The coordinator resolves it within the assignment's delegated authority, records a new brief revision, and notifies affected contributors. Continue useful independent work while that decision is made.

A changed statement or representation invalidates the affected proof, commentary, figure, and review claims. A proof change with the same type can still change its historical route and certificate.

## 5. Separate construction data from correctness evidence

For a construction, identify:

- What the problem gives.
- What geometric operations the construction uses.
- What objects are returned.
- What properties establish that the construction solves the problem.

Existence of a background object is not automatically circular. A proof can meaningfully show that a specifically constructed point is the centre of a circle known to have a centre.

Where the problem recovers an object from partial information, distinguish a construction core using the supplied data from a correctness argument using the evidence that those data satisfy the problem's conditions. Merely hiding the complete target inside a structure does not establish this distinction.

A supplied finite dissection is a legitimate input convention when stated and geometrically validated. It is different from a theorem that constructs a dissection from an arbitrary list of polygon vertices.

The edition's goal permits synthetic existence and correctness proofs. An executable geometry programming language is a separate development.

## 6. Justify representations where the text depends on them

A definition chooses a meaning. It does not by itself prove agreement with the historical object.

For a representation central to a proposition or book, establish the relevant:

- Domain and validity conditions.
- Independence from arbitrary choices.
- Correspondence between its equality and order operations and the intended geometric or arithmetic claims.
- Construction or interpretation result connecting the representation to the object used in the figure.

A representation can be deliberately limited. State the limit in the book brief and on affected pages.

Apply the same standard to arcs, areas, ratios, products, magnitudes, numbers, and solids as they arise. Select only the correspondence results the edition needs. A formal model of every axiom is valuable additional assurance, but it is not a prerequisite for every new representation.

Review where the bridge theorem lives in the dependency order. A later result cannot justify an earlier interpretation when that later result already depends on the earlier proposition.

## 7. Write the Lean as an argument

Preserve the established convention: Heath's words in full-line `--` comments; project explanations in `/- … -/` comments. The corresponding Lean should be nearby.

For every substantive mathematical passage, the reviewer should be able to identify the formal assertion or construction, its premises, and the missing diagram fact or lemma when one is needed.

Several closely related source clauses may share one Lean block. Setting-out, narrative transitions, repeated conclusions, and “similarly” need not acquire artificial tactics. A clause proved as a separate porism should point to that declaration.

When the formalization changes the argument, label and explain the change at the point where it occurs. For a substantial alternative proof, display it as an alternative. Retain the source proof in full without implying that unrelated Lean steps implement its sentences. Changes to the parser or renderer required for this layout are shared infrastructure work, not a license for an individual prover to bypass the fidelity check.

### Preserve mathematical correspondence rather than cosmetic resemblance

- Do not add dummy theorem calls to make a dependency list match Heath's references.
- Do not add artificial uses of hypotheses to silence an unused-hypothesis warning.
- A checked intermediate fact tied to a real source assertion is legitimate even if the final proof term can be simplified without it.
- Unused hypotheses and surprising dependencies are review prompts. They are not automatic verdicts about historical fidelity.
- A helper should supply an identified step. It should not conceal the entire conclusion behind a name such as `figure`.
- Cite additional earlier results when needed and explain their mathematical role.

Use Heath's letters where appropriate, with an explicit mapping for additional formal objects. Name hypotheses so the geometry is recognizable. Prefer local proofs whose facts and cases correspond to the argument; retain automation when it checks a suitable local mathematical step.

### Locate lemmas by their actual dependencies

Search the existing library before adding a helper.

- Keep proposition-specific helpers beside the proposition.
- Put a reusable corollary after its proposition.
- Put genuinely shared work in the appropriate shared module.
- Book Zero depends only on foundations.
- A helper using a proposition belongs at or after the relevant point in the proposition dependency order.

Review transitive dependencies. Moving a theorem or axiom behind a helper does not remove its logical contribution.

Foundational changes remain coordinated design changes under the operative repository policy. Review axiom statements and their mathematical strength, not only their count. An assignment to finish a proof is not permission to introduce an axiom that asserts its conclusion.

## 8. Write commentary that explains this proposition

The mishnah should answer the questions that matter on this page. Its usual sequence is:

**The mathematical move.** Explain what Euclid does and why this step matters. Give the reader a way into the figure.

**The historical or interpretive point.** Include a source-supported observation from Heath or another author when it adds something. A quotation is optional. Cite the source and distinguish direct evidence from interpretation.

**The formalization's important decision.** Explain a real gap, case, construction choice, representation, or change of route. Use a few exact Lean names only when they help the reader find the relevant work.

**The modern way.** Close with a correct modern comparison, including the conditions it needs. Say when it establishes the same result by another route or changes the construction. Let the explanation be long enough to remain accurate.

These are functions, not four compulsory paragraphs. Combine or expand them as the proposition requires. Explain shared machinery once in the book introduction, with brief links from later pages. Keep a limitation visible where it affects the local claim even if its full explanation lives elsewhere.

### Sources and quotations

Use the approved transcription as the textual baseline. Check a correction against the source image and record the exact page or leaf.

Check quotations, attribution, page numbers, and the scope of historical claims. If Heath reports another author, make that chain of attribution clear. Preserve the adopted conventions for italics, lettering, and editorial additions.

Use “references in Heath's text” or “Heath's references” for the bracketed citation list. Distinguish these from the formal dependency graph. The absence of an editorial bracket is not itself proof that Euclid lacked a justification.

Add further reading only when it helps with this proposition and the work has been verified. Do not manufacture a citation or a different modern method to fill a template.

## 9. Draw the mathematics being explained

Keep the existing two-figure design and the visual constants centralized in STYLE.

The at-a-glance figure conveys the main relation with the established palette and a short caption. Equal colors should express the intended equality without being the reader's sole means of understanding it. The lettered figure supports the argument with the approved letters and configuration.

Check the geometry as well as the rendering:

- Incidence, betweenness, side selection, and intersections.
- The cases the picture represents.
- The relation between the depicted configuration and the theorem's scope.
- Label placement, clipping, and legibility at the displayed size.

A hypothetical or impossible configuration used in a reductio should be explained as such. A picture illustrating one case should not imply that the theorem's other cases were proved by that drawing.

Record departures from the source figure in the page's figure note. Render and inspect every changed figure. A label count or color check is useful but does not validate the geometry.

## 10. Parallelize around stable interfaces

Roles are responsibilities. A small assignment does not require five separate agents.

| Role | Responsibility |
| --- | --- |
| Statement and representation owner | Settle the mathematical brief, shared vocabulary, hypotheses, conclusions, and allowed exceptions. |
| Proof contributor | Prove the assigned declarations and local helpers, including porisms, and explain correspondence with the text. |
| Edition contributor | Prepare commentary, source notes, and figures against the brief; reconcile them with the completed proof. |
| Independent reviewer | Read the changed mathematical claims against the source, inspect the argument and the rendered edition, and report findings. |
| Integrator | Coordinate shared files, resolve conflicts, reconcile reviews, generate the edition, and validate the delivered revision. |

The coordinator may also own statements and integration. Proofs of different propositions can proceed together after their interfaces are stable. Source research and figure drafts can proceed alongside proof work. Final commentary and diagram signoff depend on the settled proof and its actual scope.

An independent reviewer should not be the author of the claim being reviewed. A fresh context helps prevent reliance on the author's explanation, but independence is not guaranteed merely by changing a model name.

### Work in dependency waves

1. Establish the baseline commit, toolchain, operative instructions, task scope, and known baseline failures.
2. Settle the book's representations and the statements needed by the next group of propositions.
3. Approve proposition briefs and publish shared helper signatures.
4. Assign disjoint work and record pending dependencies.
5. Land shared changes before their consumers and integrate a group of propositions.
6. Review the integrated proof, commentary, figures, and certificate.
7. Close pending dependencies and publish an accurately described state of the edition.

A proof may be developed against an unfinished earlier theorem with a stable statement. The handback must identify that dependency, and the result remains provisional until its dependency closure is complete.

### Own files explicitly

Prefer an isolated branch or worktree for each contributor, with a named baseline and separate build outputs. When working in one shared tree, assign disjoint files and coordinate commands that mutate common outputs.

Give shared foundations, Book Zero, helper modules, source transcriptions, the bibliography, scripts, certificate extraction, toolchain, and dependency files an assigned owner. A contributor who needs a shared lemma sends its proposed type, purpose, proof or proof plan, dependency constraints, and consumers to that owner.

Workers may generate local previews. The integrator owns the committed generated edition: `facts.json`, `CERTIFICATE.md`, `GRAPH.md`, and `book/`. This avoids merging separately generated versions of the same pages.

Run the mutation-based negative tests in a disposable checkout or isolated CI job. They must not run concurrently with other contributors' builds in a shared working tree.

### Freeze and refresh reviews

Record the base revision and brief revision in every task. A finding must identify the version reviewed.

When a statement, definition, or shared helper changes, identify the affected consumers and refresh their relevant reviews. When only a local proof changes, check whether its route, dependencies, commentary, or diagram changed. Rebuild and re-review what the change can affect; unchanged work need not be repeatedly audited.

A passing build from a contributor's earlier branch does not validate the final integrated tree.

## 11. Use compact task and handback templates

The following templates are intended for internal work records. Fill them with exact declarations and paths. “None” is sufficient for an exception field with no exception.

### Proposition task

```markdown
## Task <Book>.<Number>

Role and result:
Base commit:
Brief revision:
Owned files:
Shared-file owners:
Reviewer:

Source:
- Heath file and source pages.
- Relevant definitions, book brief, and style examples.

Mathematical contract:
- Exact Lean declaration, including porisms or companions.
- Plain-language meaning.
- Coverage: full, restricted, reformulated, or partial.
- Additional hypotheses and relevant cases.
- Construction inputs, outputs, and correctness evidence.
- Representation bridges needed.

Argument and dependencies:
- Euclid's main route and any approved departure.
- Available earlier declarations and shared helpers.
- Pending declarations or requested shared work.

Finish:
- Required deliverables.
- Targeted validation and review evidence.
```

Use only the fields relevant to the assignment, linking to the existing brief rather than copying it. For a routine proposition, most entries are one line. Expand the contract when the mathematics requires it.

### Contributor handback

```markdown
## Handback <Book>.<Number>

Status: ready for review / provisional dependencies / blocked
Source revision:
Brief revision:
Changed files and declarations:

Coverage and route:
- Clauses and cases completed.
- Remaining qualifications and where the reader sees them.
- Approved changes to the contract.

Shared work and dependencies:
- New or changed helper interfaces.
- Added dependencies and pending proof roots.
- Proposals requiring the shared owner.

Checks:
- Exact commands, outcomes, and revision checked.
- Source pages checked.
- Figures or pages rendered and inspected.

Open items:
- Exact failed goal or unresolved issue.
- Proposed next step and affected work.
```

A handback should report facts, not celebrate completion. Do not paste exploratory logs unless they establish an unresolved problem.

### Review record

```markdown
## Review <Book>.<Number>

Reviewed source revision:
Brief revision:
Reviewer and scope:

Statement and cases: pass / changes needed
Representation and constructions: pass / changes needed / not applicable
Sentence correspondence and route: pass / changes needed
Text, attribution, and commentary: pass / changes needed
Figures and rendered page: pass / changes needed
Proof and certificate closure: pass / provisional / changes needed

Findings:
- Severity, source location, defect, and required correction.

Disposition:
- Ready / ready with named published limitations / return for correction.
- Any checks or source material not reviewed.
```

An accepted published limitation must name a deliberate scope boundary. It cannot stand in for an uninvestigated defect in a claim presented as proved.

## 12. Separate machine checks from review judgments

| Evidence | What it establishes | What still needs review |
| --- | --- | --- |
| Lean accepts a theorem. | The formal derivation is accepted under its dependencies. | Whether its statement and hypotheses express the intended claim. |
| The dependency closure has no `sorryAx`. | No admitted proof hole remains in that closure. | Whether assumptions or definitions already contain the substantive result. |
| The fidelity check passes. | The checked source comments match the approved transcription under the checker's normalization. | Whether the Lean implements those sentences and follows their argument. |
| Dependency and provenance checks pass. | The implemented restrictions were satisfied. | Whether supplementary lemmas faithfully fill gaps and whether the restriction itself captures the intended policy. |
| Generated output is reproducible. | The pages and certificate match the source and generator. | Whether their descriptions of scope and meaning are accurate. |
| Figures render and their labels match. | The files display and meet the structural checks. | Whether the depicted geometry and case selection agree with the proof. |

The certificate describes proof-term dependencies. Use that evidence precisely. It does not by itself establish consistency of the foundations, necessity of an axiom, independence of the parallel postulate, or semantic equivalence to the historical text.

Check every formal declaration covered by a completion label, including porisms and displayed companions. At the reviewed revision, the certificate's porism aggregation needs repair; until that is repaired and tested, inspect their dependencies separately.

### Validation on the integrated revision

Use the repository's established commands:

```sh
lake build
lake env lean Certificate/Facts.lean
python3 scripts/check_fidelity.py
python3 scripts/render.py
```

Review the generated differences. Include the generated files with their source change, then verify regeneration leaves them unchanged.

Run the existing negative-test job against the same candidate revision in isolation:

```sh
python3 scripts/negative_tests.py
```

When fixing a certificate or guard defect, add a focused regression that demonstrates the defect would be caught. Do not add tests that merely repeat trivial prose changes.

Record the revision and actual outcomes. A command not run is not a passing check. If integration changes relevant source after validation, refresh the affected evidence.

## 13. Release a coherent edition

A proposition is ready for the stated reader-edition standard when:

1. The reviewed mathematical brief and final formal statements agree.
2. Every substantive clause and relevant porism is proved or explicitly qualified.
3. The intended cases are covered and construction inputs and outputs are appropriate.
4. Important representation choices have the correspondence results the claims require.
5. The displayed proof route is accurate and exceptions are visible.
6. The dependency closure, axiom boundaries, and certificate cover all published formal claims.
7. Quotations and attributions are checked, and commentary explains this proposition accurately.
8. Changed figures and the affected page have been inspected.
9. Required checks pass on the integrated revision.
10. A reviewer other than the author has assessed the changed mathematical claims.

Use severity to decide what needs correction:

- **Blocking:** an invalid or wrongly scoped formal claim presented as full, an unresolved dependency presented as closed, an unapproved foundational change, or a materially false certificate.
- **Material:** an unmarked alternative argument, a hidden clause omission, an unsupported representation claim, a misleading figure, or an incorrect quotation or attribution.
- **Editorial:** repetition, awkward prose, excessive detail, or inconsistent formatting that does not change the mathematical meaning.

Resolve blocking and material findings before presenting the affected claim as complete. A numerical quality score can summarize a review; it cannot cancel a concrete defect.

Small, deliberately published limitations can remain in an excellent edition. A full standard-plane model, a complete theory of curvilinear angles, or a general construction language can be separate projects. The release's scope should make that boundary explicit.

## 14. A short agent entry brief

The following is proposed content for a future `AGENTS.md`. Its linked companion documents should be created or updated before it is adopted.

```text
You are contributing to Stoicheia, a reader's edition of Euclid with
historical text, synthetic Lean proofs, figures, and commentary.

Read CONTRIBUTING.md, docs/STYLE.md, docs/FORMALIZATION.md,
docs/WORKFLOW.md, the relevant book brief, and your assigned proposition
brief. Use the current task's baseline and scope.

Before proving, read the whole enunciation and confirm the approved Lean
statement, cases, representation choices, and permitted proof route.
Preserve Heath's text and follow the project's comment conventions.

Work in your assigned files. Coordinate changes to statements,
foundations, shared helpers, source transcriptions, scripts, and generated
outputs with their assigned owners. Propose a concrete correction when an
interface is wrong; continue useful unaffected work.

Follow the mathematical argument, not just its quotations or citation
list. Explain added diagram facts. Mark genuine restrictions, omissions,
or alternative routes. Do not introduce axioms, dummy citations, or
weakened checks to complete an assignment.

Use the project's public voice in reader-facing work. Internal handbacks
should be brief and factual.

Return your source revision, coverage and route differences, dependency
changes, actual check results, review evidence, and remaining issues.
Include porisms and displayed companion theorems.

Treat checks and reviews as evidence tied to a revision. A locally
compiling proof with unfinished dependencies is provisional.
```

## 15. Adopt the guide in a small pilot

First reconcile the proposed changes with STYLE and CONTRIBUTING. Keep the existing voice, visual constants, source conventions, and mathematical controls. Move duplicated rules to their authoritative homes and link them from the entry documents.

Then trial the task and review templates on three different kinds of work: a straightforward proposition, a construction or area generalization, and a proposition with a representation or proof-route exception. Give those tasks to parallel contributors with disjoint ownership.

Have an independent editor read the resulting pages consecutively. Check for a shared voice, consistent terminology, truthful scope descriptions, and a consistent level of mathematical explanation. Use the findings to adjust the defaults and examples before applying the guide across the remaining books.

### Suggested changes to the current guidance

| Current tendency | Proposed standard |
| --- | --- |
| Confidence expressed as “nothing hedged.” | Direct statements with precise conditions and calibrated historical attribution. |
| Fixed counts of “we,” paragraphs, or quotation slots. | A recognizable voice and usual length range, with reasons for useful exceptions. |
| A different modern method demanded on every neighboring page. | The clearest correct comparison, with shared explanations linked. |
| Every finished proof receives the same sentence-by-sentence description. | Separate proof status, statement coverage, and route, with visible exceptions. |
| The current code is treated as the answer when a brief differs. | Code states the implemented meaning; discrepancies with the intended mathematics receive review. |
| Propositions can be divided among workers once statements exist. | Statements and representations are reviewed and versioned before downstream workers rely on them. |
| Each contributor regenerates the whole edition for handoff. | Contributors own sources and local previews; the integrator owns committed generated output. |
| Review is summarized as a general approval. | Findings and signoff identify the revision, scope, and unresolved limitations. |

## Repository basis

The guide is based on the following files at commit `676244a617e59e527b4ba0a3f33b8797c1552b90`. Recommendations and templates above are proposed policy, rather than claims that these changes already exist.

- [README and project goals](https://github.com/jackchallis/stoicheia/blob/676244a617e59e527b4ba0a3f33b8797c1552b90/README.md).
- [Current house style](https://github.com/jackchallis/stoicheia/blob/676244a617e59e527b4ba0a3f33b8797c1552b90/docs/STYLE.md).
- [Current contributor instructions](https://github.com/jackchallis/stoicheia/blob/676244a617e59e527b4ba0a3f33b8797c1552b90/CONTRIBUTING.md).
- [Book III mathematical brief](https://github.com/jackchallis/stoicheia/blob/676244a617e59e527b4ba0a3f33b8797c1552b90/docs/briefs/0004-book-III.md).
- [Text and house-rule checker](https://github.com/jackchallis/stoicheia/blob/676244a617e59e527b4ba0a3f33b8797c1552b90/scripts/check_fidelity.py).
- [Certificate extraction](https://github.com/jackchallis/stoicheia/blob/676244a617e59e527b4ba0a3f33b8797c1552b90/Certificate/Facts.lean).
- [Page generation](https://github.com/jackchallis/stoicheia/blob/676244a617e59e527b4ba0a3f33b8797c1552b90/scripts/render.py).
- [CI workflow](https://github.com/jackchallis/stoicheia/blob/676244a617e59e527b4ba0a3f33b8797c1552b90/.github/workflows/ci.yml).
