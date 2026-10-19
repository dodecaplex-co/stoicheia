# Formalization

How a proposition of Euclid becomes a Lean theorem here, what the theorem may claim, how
the Lean follows the argument, where its lemmas live, and what each kind of check shows.
[STYLE.md](STYLE.md) says how the page reads; [WORKFLOW.md](WORKFLOW.md) says who does
what, and when; [AGENTS.md](../AGENTS.md) holds the priorities and the ten rules. The
Lean is plain Lean 4.35, with no Mathlib and no other dependency (run
`export PATH=$HOME/.elan/bin:$PATH` first). This standard follows Astra's
[draft guide](reports/outside-review-01-guide.md), sections 4 to 7 and 12, adapted to
the project as it is.

## 1. What the code says, and who decides

**The code states what we formalized.** It does not establish that this is what Euclid
intended. When the code, the book's brief, the review record and the page disagree, the
disagreement is recorded (in the review record, or as a brief correction) and every
document it touches is reconciled. It is never settled by quietly editing whichever is
easiest. The early briefs (0001–0003) are kept as written, as history; the current
decisions for each book are in its brief ([Book I](briefs/book-I.md),
[Book II](briefs/book-II.md), [Book III](briefs/0004-book-III.md)), which agrees with the
code.

**No guide grants authority.** This page, STYLE, WORKFLOW and every other guide describe
the standard. None of them grants authority to change the foundations, weaken a check or
publish. Those decisions belong to the project's owner, Jack Challis, working with the
coordinator of the work ([WORKFLOW.md](WORKFLOW.md)), and each is recorded in
[0002-decisions.md](briefs/0002-decisions.md):

- **The foundations:** everything in `Elements/Foundations/` (the postulates, Definition
  I.15, the tacit rules, the primitive words and magnitudes, the definitions of each book,
  the phrases), and `Certificate/axioms.lock`.
- **Weakening the checks:** weakening, skipping or removing a check, an expected value, a
  lock or a schema, anywhere in the check inputs and protected paths that
  [WORKFLOW.md](WORKFLOW.md), section 10, "Landing work: pull requests", lists (their one
  home). None is ever loosened to let a change through. Adding or strengthening a check is
  ordinary work, done by the owner the orders name, with a regression test where a guard
  defect is fixed ([WORKFLOW.md](WORKFLOW.md), section 8). Either way a change to a
  protected path ([WORKFLOW.md](WORKFLOW.md), section 10, "Protected paths") is named file
  by file in a decisions entry and given a security review before it is merged; a check
  change is a pull request of its own ([WORKFLOW.md](WORKFLOW.md), section 10, "Landing
  work: pull requests").
- **Publishing:** tags, releases and their notes, the GitHub description, and anything
  sent outside the repository. Landing work on main is delegated to the coordinator: a
  pull request, opened and merged with a merge commit through `scripts/safe_push.py`
  alone ([WORKFLOW.md](WORKFLOW.md), section 10, "Landing work: pull requests").

Within an authorized assignment, the coordinator makes the routine decisions delegated to
that role ([WORKFLOW.md](WORKFLOW.md)).

## 2. Statements

### Writing one

- The theorem is `Elements.Book<book>.Prop<n>` (`Elements.BookIII.Prop31`), and its
  docstring is Heath's enunciation, exactly; `check_fidelity.py` insists.
- A problem is an `∃` theorem returning what it constructs, with the properties that make it
  a solution; a theorem is an implication.
- Hypotheses come from the setting-out, and conclusions from "I say that".
- Points, straight lines and circles take Heath's letters (`BCD` for the circle BCD); a
  straight line he names with one letter becomes two points (`A₁ A₂`); hypotheses are named
  off the letters (`hAB : A ≠ B`, `hA_BCD`).
- Magnitudes are lengths, angles and areas, `‖A B‖`, `∠ A B C`, `△ A B C`, with `∟` the
  right angle and Book II's `rect` and `sq`: they add and compare, and nothing more. "Greater
  than … by" is an equation (the less with the excess is the greater). No numbers,
  coordinates or real numbers appear in a statement or a proof.
- Each book's phrases, and how its statements say them, are in its brief.

### Coverage: does it say what Euclid says?

Read the whole enunciation, setting-out and proof first. Write the proposed statement,
then translate it back into plain words and compare that with the enunciation, before any
proof work. A reviewer who is not the author makes the same comparison, starting from
Heath and the Lean, before reading anyone's account of how they agree. The questions:

- **Quantifiers.** "Any", "every", "any number" survive. A fixed number of named pieces, or
  one pictured placement, needs a stated restriction or a general theorem.
- **Conclusions.** Every conjunction, converse, construction, uniqueness claim and porism
  is accounted for. A conclusion is not dispensable because later propositions do not use
  it.
- **Hypotheses.** Conditions that define the objects Euclid means are told apart from
  restrictions borrowed from the drawing, and every material extra assumption is recorded.
  A hypothesis that only names what his words presuppose (that a triangle's corners are not
  on one straight line) is not a restriction.
- **Cases.** The configurations the statement admits are examined: boundary positions,
  equality, orientation, order, coincidence, greater and less. The proposition decides which
  cases matter, not a generic list of degeneracies.
- **Objects and operations.** What equality, order, area and the rest mean for the
  representation used (section 3).
- **Outputs.** A construction's result is easy to recognize. Where the theorem returns a
  side that determines a square, the page points to what constructs the square.

What these questions catch, from our own history: "any number of segments" stated for
exactly three pieces (II.1); a comparison of straight lines in a circle that excludes
diameters because its perpendicular cannot have length nothing (III.14); a figure taken as a
sum of triangles without saying that they make up the figure (I.45, II.14); a circumference
represented by an angle with no theorem saying what equal measures mean in unequal circles
(III.24, III.26–III.29); an enunciation's clause about angles of another kind left out of
the conclusion (III.16, III.31).

The answer is the record's `[statement]` ([review/SCHEMA.md](../review/SCHEMA.md)), whose
three words are the home of these terms:

- **full:** every clause, for every configuration Euclid's words admit, in the meaning the
  representation gives them. A statement that leaves out one of his hypotheses, and so
  claims more, is still full (III.9's point need not be within the circle), and is tagged
  `hypothesis-dropped`.
- **restricted:** every clause, but only under extra hypotheses that exclude configurations
  his words admit (I.40's main theorem alone, its bases end to end).
- **partial:** some clause has no formal conclusion (III.16, III.31); the record quotes it
  and gives a clause map.

**A statement, once approved, is frozen:** others write against it. Never change an
approved statement, a porism's or a definition without the coordinator's approval, through
the correction in [WORKFLOW.md](WORKFLOW.md). If it seems wrong or too weak, stop work on
it and say so, with the case that fails; do not work round it. A changed statement or
representation makes the proof, commentary, figure and review claims built on it stale, and
the record's fingerprint shows it.

### Porisms

A porism is a claim too. It is stated after its proposition, as `PropN.porism`, proved
there ("from this it is manifest"), and certified as an entry of its own ("III.1 Por."),
under every policy check. The proposition is not finished until its porism is. A citer cites
the porism by its own name, as Heath's "[III. 1, Por.]" does.

### Companions beside Euclid's worked configuration

Where a statement is narrower than Euclid's words, the general result is a companion
theorem beside the unchanged `PropN`, which stays as Euclid's worked configuration under his
sentences: `Prop40.general`, `Prop45.figure`, `Prop14.square`, and the old statement as a
corollary (`Prop40.special`) where it helps citers. The fidelity check reads only
`theorem PropN`, so Heath's sentences stay where they are. A companion is listed in the
edition's companions list, [`Elements/Companions.lean`](../Elements/Companions.lean)
(who adds its entry, and when: [WORKFLOW](WORKFLOW.md), section 4); it gets a certificate
entry ("I.40 general"), which `Certificate/Facts.lean` checks; it is named in the review
record's `companions`; and it is shown on the page with its own certificate. Each
companion is approved as a statement with `sorry` before anyone proves it.

## 3. Representations

**A definition chooses a meaning; it does not prove agreement with Euclid's object.** For a
representation that a proposition or a book depends on, establish what the text needs:

- its domain, and when it is valid;
- that it does not depend on an arbitrary choice;
- that its equality and order say what Euclid's equality and order say;
- a construction or interpretation result connecting it to the object in the figure.

Book II's rectangle is the model. `rect A B C D` is defined by choosing one area of a
rectangle with sides AB and CD (`Classical.epsilon`), and `Rectangle.contained` proves that
every rectangle drawn with those sides has that area, so the choice makes no difference, and
a rectangle in Euclid's figure is the rectangle his words name.

**Bridge theorems sit where the dependency order allows.** A later result cannot justify an
earlier interpretation when the later result already depends on the earlier proposition.
Stage 3's theorems on arcs go after III.29 for this reason, so that the argument cannot run
in a circle.

**A deliberate limit is stated** in the book's brief, carried as a tag of
[review/terms.toml](../review/terms.toml) in each affected record, and shown on each
affected page. A new tag is added there, with its meaning, before any record uses it. A full
formal model of every axiom is valuable further assurance, and a separate milestone; it is
not a prerequisite for each new representation.

The representations Books I–III rest on:

| Euclid | Ours | Bridge, or limit | Tag |
|---|---|---|---|
| a straight line | a whole straight line, `Line`, named by any two points (Postulate 1) | producing it costs nothing | |
| lengths, angles, areas | `Magnitude` of one kind each, added and compared only | Common Notions proved as theorems | |
| a right angle | Definition I.10 as a predicate, and Postulate 4 making every right angle `∟` | | |
| superposition | one rule, `Tacit.superposition`, allowed in I.4 and I.8 alone | | |
| the rectangle contained, the square on | `rect`, `sq`, areas defined from lengths | `Rectangle.contained`, `Rectangle.eq_rect`, `Square.described` | `side-not-square` (II.14) |
| a rectilineal figure | given with its division into triangles, checked: triangles that lie apart (`Apart`), triangles fitted together (`Fitted`, `Rectilineal`), or Euclid's from one corner (`Fitted.fan`); equal to the figure means equal to those triangles together | that every figure can be so divided, and that another division gives the same sum, are not proved; Hilbert proved the second, for his measure of area | `figure-with-dissection` |
| a circle's centre | a hypothesis, `∃ O, Centre O α`, or Postulate 3's | III.1 finds it | `centre-given` |
| a circumference | twice the angle standing on it, `circumference`, `standing`; no radius | proved facts in `Circumferences.lean`; arcs with membership are stage 3's work | `angle-measure`, `redundant-hypothesis` |
| a segment | its circle, a straight line in it and one side | stage 3 | `segment-with-circle` |
| an angle of a straight line and a circumference | none | the rectilineal facts Euclid proves it by are stated | `mixed-angles-omitted` |
| circles touching | not crossing anywhere (the whole-circle reading Heath reports as Todhunter's) | III.13 keeps its content | |

The details, and the reasons, are in the book briefs.

## 4. Constructions: what is given, and what shows it works

For a construction, say:

- what the problem gives;
- which operations the construction uses;
- which objects it returns;
- which properties show that it solves the problem.

The existence of a background object is not circular. III.1 meaningfully shows that the
point it constructs is the centre of a circle known to have one.

Where a problem recovers an object from partial information, keep apart the construction
core, which receives only the data the problem gives, and the correctness argument, which may
use more: evidence that those data satisfy the problem's conditions. Hiding the whole target
inside a structure does not keep them apart. III.25 is the pilot (stage 4): its core receives
the segment only as a predicate on points, with the meeting fact Euclid reads off it, and a
separate theorem shows that the circle it finds is the one the segment came from.

A finite dissection supplied as input is a legitimate convention when it is stated and
checked geometrically. It differs from a theorem that constructs a dissection from any list
of vertices. The edition proves synthetic existence and correctness; an executable language
of constructions is a separate project.

## 5. The Lean as an argument

### Where the words go

- **Heath's words are `--` comments, word for word.** Read in order, the full-line `--`
  comments inside `theorem PropN`'s proof are Heath's proof exactly (indentation aside), and
  the docstring is his enunciation; `check_fidelity.py` fails on any difference. A porism's
  sentence is a `--` line in its proposition's proof.
- **The Lean for each sentence sits directly under it.** What a sentence with no Lean
  under it needs, and where a `/- … -/` remark may stand among sentences, is in
  [review/SCHEMA.md](../review/SCHEMA.md#two-stages), "Two stages".
- **Our words are `/- … -/` remarks and docstrings**, in the voice STYLE asks for.

### Correspondence, not resemblance

For every substantive passage, a reviewer should be able to find the formal assertion or
construction, its premises, and the diagram fact or lemma it needed.

- Closely related clauses may share one block of Lean. The setting-out, transitions,
  repeated conclusions and "similarly" need no artificial tactics. A clause proved as a
  porism or a helper points to that declaration.
- **No dummy citations.** Never add a theorem call to make the Lean's dependencies match
  Heath's references. The Lean cites what its argument uses; a difference from Heath's
  references is shown on the page (the generated line, a passage note), and explained in the
  mishnah only when it is this proposition's story.
- **No artificial hypothesis uses.** Never mention a hypothesis only to silence an
  unused-variable warning.
- **Unused hypotheses and surprising dependencies are review prompts, not verdicts.** An
  unused hypothesis may mean the route is not Euclid's, or that our representation makes it
  redundant (III.26 and III.27 hold for any two circles as stated). Say so in the handback;
  the record tags it `redundant-hypothesis` where that is the truth.
- A checked intermediate fact tied to a real sentence of Euclid is legitimate, even if the
  final proof term could do without it.
- Cite further earlier results when the argument needs them, and say what each does.
- Prefer local proofs whose facts and cases follow the argument. Automation (`ac_rfl` to
  close a sum of magnitudes, and the like) is fine for a local step it checks.

### Euclid's route, and departures from it

Where the page promises Euclid's argument, the Lean follows it: the propositions he uses, in
his order, and nothing later. Some propositions can be reached by a shortcut he did not take
(III.2 by an axiom; III.26, III.27 and III.30 by the circumference measure alone); take his
route, for his inferences are the proposition's content.

Where the Lean must part from him, keep his sentences, put Lean under them that does the same
work, and label the change where it happens: a `/- … -/` remark in the Lean, and a passage in
the review record. A step argued another way is a `different` passage, and makes the route
`modified` or `alternative`; a lemma for a step he takes for granted (`helper`), sentences
carried by one step (`grouped`), a case his figure leaves aside (`case`), a step the
statement already gives (`given`) and a passage with no Lean (`unformalized`) leave his
route as it is ([review/SCHEMA.md](../review/SCHEMA.md)). A substantial alternative proof is displayed as an alternative, with
Euclid's text kept in full and no suggestion that unrelated Lean carries its sentences
(III.24's proof by the radii, from stage 3 on). Where an axiom already contains the
proposition (III.2), the proof reconstructs Euclid's reasoning within our foundations and does
not establish the rule: the record's `[overlap]` and the overlap catalogue
(`docs/reports/overlaps.md`) say so. Changes to the parser or renderer that such a layout
needs are shared infrastructure, and never a licence to bypass the fidelity check.

### Helpers

A helper supplies one identified step: what Euclid reads off the figure, a case he leaves to
the reader, a fact he takes for granted. Its docstring says which. It never hides the whole
conclusion behind a name: if `Prop7.figure` proved I.7, the page would show nothing of
Euclid's argument. I.7 is the example to follow: its helpers settle where D can fall and what
the figure shows, and the main proof keeps every step of Euclid's reductio.

## 6. Where lemmas live

Search the library before writing a helper, and cite what is there rather than keep a copy. A
helper another page has proved is imported and cited with a pointer ("as in III.1",
`Prop1.perpendicular`), never proved again.

- **A helper for one proposition** goes before it in the same file, named
  `PropN.something`, with a docstring saying what Euclid takes for granted.
- **A porism, or any corollary,** goes after its proposition (`Prop15.porism`). A
  consequence of one proposition that later proofs share is a corollary after it
  (`Prop29.alternate`, `Prop31.line`, `Prop34.bisect`).
- **Book Zero,** `Elements/Figure/`, holds facts every figure needs, proved from the
  foundations alone. It imports no proposition, ever.
- **A shared step that cites a proposition** lives at or after that proposition in the
  dependency order: in `Elements/BookI/Helpers.lean`, named after it (`Prop5.base`); in
  `Elements/BookI/HelpersParallels.lean` if it cites I.28, I.30 or I.31 (`Prop30.meet`,
  `Prop31.parallelogram`); in `Elements/BookII/Rectangles.lean` for Book II's steps that
  cite Book I; in `Elements/BookIII/Squares.lean` for Book III's that cite Books I or II; and
  in `Elements/BookIII/Circumferences.lean` for those that cite III.20–III.22. A new shared
  module (stage 2's `Elements/Figure/Sums.lean`, stage 3's placement and arcs) has an owner,
  and its place in the order is set in the brief.
- **Imports.** Import `Elements.Figure.Basics`, the book's ground, every proposition cited,
  and the module of every shared step cited (`Elements.BookI.Helpers`,
  `Elements.BookI.HelpersParallels`). A proof cites an earlier book as `BookI.PropN`, `BookII.PropN`, and does not open
  it: in a Book III file a bare `Prop4` means III.4.
- **Staging,** `Staging/`, holds the statements that a stage of brief 0005, or of a later
  brief, adds or changes, each with `sorry` where its proof is due, until it moves to
  `Elements/`, and only the proofs that [WORKFLOW.md](WORKFLOW.md), section 2, "What proofs
  `Staging/` may hold", allows there.
  Its files import the modules of `Elements` they need. `lake build Staging` builds every
  file under `Staging/`, whether or not the root `Staging.lean` imports it, so a staged
  file need not be added to the root; nothing outside `Staging/` imports them, so nothing
  staged reaches a proof or the certificate. `Staging/.gitkeep` keeps the directory, which
  the build reads, when nothing is staged. A changed main theorem is staged as
  `Elements.Book<B>.Staging.PropN`, since the `PropN` it replaces is still declared in
  `Elements`; it takes the name `Elements.Book<B>.PropN` when it moves.

Moving a theorem or an axiom behind a helper does not remove its logical contribution: the
certificate walks through helpers and shared steps, and the review reads transitive
dependencies.

## 7. The foundations, and the policies the checks enforce

- **Every assumption is an `axiom` in `Elements/Foundations/`:** the five postulates,
  Definition I.15 and 81 tacit rules, 87 in all, each tacit rule from System E (or
  LeanEuclid's corrections of it) with its citation. A new rule, or a change to one, is a
  foundation decision (section 1); `Certificate/axioms.lock` holds every axiom's exact
  statement, with every definition that the axioms' statements or the propositions',
  porisms' and companions' statements reach (`Touches`, `rect`, `Parallel`), so that no
  word can change what an axiom or a claim says. It changes only through
  `check_fidelity.py --write-lock`, together with a decisions entry, and with the model
  brought to it in the same change, as
  [tests/model/MODEL.md, "Changing the axioms"](../tests/model/MODEL.md#changing-the-axioms),
  says; otherwise CI's `model` job fails. Review an axiom's statement and strength, not
  only the count. An assignment to finish a proof is never permission to add an axiom that
  asserts its conclusion.
- **Nothing gets round the kernel:** no `native_decide`, `decide +native`,
  `set_option debug.…`, `run_cmd`, `run_elab`, `elab`, `macro`, `implemented_by`, `extern`
  or `unsafe` under `Elements/`.
- **Superposition** only in I.4 and I.8.
- **Postulate 5.** No proof before I.29 uses Postulate 5 or a rule declared in
  `Elements.Tacit.Euclidean`; Books II and III come after Book I and may use it throughout.
- **No later citations:** no proof cites a proposition that does not come before it.
- **Complete books stay complete:** every proposition of a complete book is proved, with
  both figures and a mishnah, and so is every porism and companion attached to it.
- **Primitive words stay `opaque`,** so Lean knows of them only what the axioms say.

`check_fidelity.py` enforces these for every certificate entry, porisms and companions
included. `negative_tests.py` plants a break of these kinds to show each is caught: an
axiom declared outside the foundations; an axiom missing from the lock, and one weakened;
Postulate 5 and a Euclidean-only rule before I.29; superposition outside I.4 and I.8; a
later citation, one of them named only in a helper's statement; a `native_decide`; a
`sorry` in a complete book; and a primitive word no longer opaque. The other forbidden
commands, Book Zero's imports and a complete book's missing figure or mishnah have no
planted break yet.

The first two policies hold in `Staging/` (section 6) by rule: a staged file declares no
axiom and uses none of the forbidden commands. That no check enforces them there is a
known gap: `check_fidelity.py`'s scan for them (`check_rules`) covers `Elements/` alone
today, so in `Staging/` they rest on review. Extending the scan to `Staging/` is a change
to a check, and lands in a pull request of its own
([WORKFLOW.md](WORKFLOW.md), section 10).

## 8. Completion claims

A completion label and its certificate cover the same declarations: the main theorem, its
porism, and every companion the page shows. A certificate entry is `proved`, `sketched` (a
`sorry` in its own proof, through its helpers and shared steps) or `proved-pending` (resting
on a `sorry` only through what it cites). A proof that compiles against unfinished
dependencies is provisional, and is presented as finished only when its dependency closure
is. The summaries of what is complete (the README's rows, CERTIFICATE.md, the index pages) are
generated from `facts.json` and the review records, never written by hand.

## 9. What the checks show

Each kind of evidence establishes something definite, and leaves something to review. A
claim on a page, in the README or in release notes says which kind of evidence it rests on.

| Evidence | What it establishes | What it leaves to review |
|---|---|---|
| Lean accepts the theorem | The formal derivation is accepted by the kernel, under its dependencies. | Whether the statement and its hypotheses express the intended claim. |
| The kernel replays pass (`scripts/check_kernel.py`) | Every declaration of the compiled `Elements` library, Lean's own included, is accepted again: by Lean's kernel, replayed from nothing (`leanchecker --fresh`), so no declaration reached the compiled files without the kernel's check; and by nanoda, a checker written separately, which admits only the locked axioms and Lean's three, by name. | Only nanoda stands apart from a fault in the code of Lean's kernel: leanchecker runs the same kernel as `lake build`. The axioms nanoda admits are matched by name, so whether each states what the lock records is the lock check's question. Both check Lean's logic, so a fault in the logic itself would pass them both; and they establish nothing about meaning. |
| No `sorryAx` in the dependency closure | No admitted proof hole remains in that closure. | Whether an assumption or a definition already contains the result (an overlap). |
| The fidelity check passes | The `--` lines and the enunciation match Heath's text, under the checker's normalization. | Whether the Lean beneath them carries those sentences and follows their argument. |
| The policy and lock checks pass | Superposition, the Postulate 5 boundary, citation order, axiom placement, forbidden commands and the axioms' exact statements are as recorded. | Whether helpers fill gaps faithfully, and whether a policy captures what it is meant to. |
| A current review record | A named reviewer read the statement, route, representation and passages at a named commit and recorded them; the fingerprint shows the statements are unchanged since. | It is a reader's judgment; the independent audit and the acceptance checklist test it. |
| The edition review | Commentary, quotations, figures and scope descriptions agree with the reviewed mathematics. | |
| Regeneration is clean | The pages, certificate and graph match the sources and the generator. | Whether their descriptions of scope and meaning are accurate. |
| The figure checks pass | The files display, and their letters, palette and strokes meet the structural rules. | Whether the drawn geometry and the case shown agree with the proof. |
| The numerical model tests (`tests/model/`) | The locked axioms held in the configurations sampled from a standard model of the plane, and planted mutations of them were caught. | A proof of consistency: laws no harness reaches rest on a hand argument. |
| The informal model argument | A reasoned interpretation of each law in the standard plane. | A machine-checked proof. |
| A formal interpretation (a later milestone, a separate package with Mathlib) | The exact locked axioms proved in a model of the plane, tied to the lock so that any change to an axiom breaks it. | |

The certificate describes proof-term dependencies, and nothing more. "This proof uses
Postulate 5" is a fact about our proof. By itself it establishes neither the consistency of
the foundations, nor the necessity of an axiom, nor the independence of the parallel
postulate, nor that the Lean means what Euclid meant. A claim that a result holds without the
postulate names its evidence (an interpretation in which the other axioms hold and the
postulate fails), and even then the pages keep "this proof uses".
