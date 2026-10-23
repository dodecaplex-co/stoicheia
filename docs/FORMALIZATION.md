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
publish. Those decisions belong to the repository's owner, working with the coordinator
of the work ([WORKFLOW.md](WORKFLOW.md)), and each is recorded in a decision entry of
its own, `docs/decisions/<YYYY-MM-DD>-<slug>.md` ([WORKFLOW.md](WORKFLOW.md), section 10,
"Decision entries"), as those written before entry files are in
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
  than … by" is an equation (the less with the excess is the greater). No coordinates or
  real numbers appear in a statement or a proof, and no number measures a length, an angle
  or an area. Counts may appear, natural numbers, of a figure's corners and of what
  they make, since a count is part of what "a figure of n sides" means: the corners
  of a closed line of sides, or within a triangle, and a corner's place in their list,
  turned round some number of steps; the sides a ray or a finite straight line crosses
  (`crossingCount`); the closed lines round a point (`Outline.depth`); and the tiles and
  triangles of a division, with the sides they share. Counts are added and compared, and
  two are compared by their remainders on division by two, as
  `crossing_parity_independent` compares two crossing counts. They are part of how a figure
  is defined, not of Euclid's argument
  ([decision of 22 October 2026](decisions/2026-10-22-figures-promoted.md)).
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
- **Outputs.** A construction's result is easy to recognise. Where the theorem returns a
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
- **partial:** some clause has no formal conclusion (as in III.16 and III.31 before their
  mixed-angle companions); the record quotes it
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
sentences: `Prop40.general`, `Prop45.outline`, `Prop14.outline`, and the old statement as a
corollary (`Prop40.special`) where it helps citers. The fidelity check reads only
`theorem PropN`, so Heath's sentences stay where they are. A companion is listed in the
edition's companions list, [`Elements/Companions.lean`](../Elements/Companions.lean)
(who adds its entry, and when: [WORKFLOW](WORKFLOW.md), section 4); it gets a certificate
entry ("I.40 general"), which `Certificate/Facts.lean` checks; it is named in the review
record's `companions`; and it is shown on the page with its own certificate. Each
companion is approved as a statement with `sorry` before anyone proves it.

### Names, and how they change

The library is used as well as read ([README](../README.md#use-it), "Use it"), so its
names are an interface, and they change only in the open.

- **How names are made.** A proposition is `Elements.Book<book>.Prop<n>`, declared in its
  file's module, `Elements.Book<book>.Prop<nn>`; its porism and its companions are
  `PropN.porism` and `PropN.<word>`, in the same file. A helper is named for the step it
  supplies (section 6). Other new names follow Lean's own conventions, as the community's
  [naming guide](https://leanprover-community.github.io/contribute/naming.html) sets them
  out: a theorem in `snake_case` (`Prop5.base`, `collinear_of_between`), a predicate or a
  type in `UpperCamelCase` (`OnCircle`, `Parallelogram`), written in `lowerCamelCase`
  where it is part of a theorem's name (`OnRay.of_sameSideOf`, after `SameSideOf`), any
  other definition in `lowerCamelCase` (`quadArea`). A companion is a theorem, so its
  `<word>` follows the same rule: `Prop25.of_circle`, and `Prop24.equalCircles` after the
  predicate `EqualCircles`. `PropN`, `PostulateN`, `Definition15` and `CommonNotionN`
  keep Euclid's numbers.
  [The table of names](../book/names.md), which `scripts/render.py` writes from
  `facts.json`, gives every proposition, porism and companion with its module, its page
  and its certificate.
- **A released name stays, or is deprecated first.** A released name is one that a
  release tag's `Elements` declares (`book-I`, `book-II`, `book-III` and each after),
  helpers and Book Zero included. It is never renamed or removed without a deprecated
  alias for one release: the old name stays, marked deprecated and pointing to its
  replacement, through the next release, and may go in the release after. Lean then warns
  at every use and names the replacement. Plain Lean has no `alias` command (Batteries
  supplies one), so the alias is written out, dated the day it reaches main:

  ```lean
  @[deprecated NewName (since := "YYYY-MM-DD")]
  theorem OldName : type_of% @NewName := @NewName
  ```

  A definition's alias is an `abbrev` under the same attribute
  (`abbrev OldName := @NewName`), and a declaration
  removed with nothing to replace it stays as it was for that release, marked
  `@[deprecated (since := "YYYY-MM-DD")]`. A change in the foundations is still the
  owner's decision (section 1). `Staging/` and `Audit/` are not released, and their
  names promise nothing.
- **A statement that changes keeps its name.** A proposition's, porism's or companion's
  statement changes only by an approved correction (WORKFLOW, section 2). `PropN` names
  Euclid's proposition whatever its statement, so the name goes with the new statement,
  and where citers need the old one it stays beside it as a companion, as
  [brief 0006](briefs/0006-statements.md) keeps III.24's statement before stage 3 as
  `Prop24.equalCircles`. A helper's or a Book Zero fact's statement may change between
  releases; its name follows the rule above.
- **The release notes list the changes:** every name deprecated or removed, and every
  statement changed, with where its old form now stands.

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
formal model of every axiom is valuable further assurance, and a milestone of its own, now
complete: Lean checks, in [`model/`](../model/README.md), that the ordinary plane satisfies
every locked law ([MODEL.md](../tests/model/MODEL.md#the-formal-model)). It is not a
prerequisite for each new representation, and it does not show that a representation
captures the object in the text.

The representations Books I–III rest on:

| Euclid | Ours | Bridge, or limit | Tag |
|---|---|---|---|
| a straight line | a whole straight line, `Line`, named by any two points (Postulate 1) | producing it costs nothing | |
| lengths, angles, areas | `Magnitude` of one kind each, added and compared only | Common Notions proved as theorems | |
| a right angle | Definition I.10 as a predicate, and Postulate 4 making every right angle `∟` | | |
| superposition | `Tacit.superposition`, a restricted inference in System E's style, used directly only in I.4 and I.8 | a checked derivation over symbols exports one equality of lengths, angles or triangles about the given figure; it constructs nothing inside the placement and no exported formula names the placed corners or side ([the rule](../Elements/Foundations/Tacit/Superposition.lean), [Book I's reading](briefs/book-I.md#representations)) | |
| the rectangle contained, the square on | `rect`, `sq`, areas defined from lengths | `exists_rect`, `Rectangle.contained`, `Rectangle.eq_rect`, `Square.described` | `side-not-square` (II.14) |
| a rectilineal figure | given by its outline, `Outline`: finitely many simple closed lines of sides, apart or nested, so that a figure may have holes, separate pieces or contacts at corners; its region read from the sides by the parity of a ray's crossings (`Outline.Region`); and equal to the figure meaning equal to its area, `Outline.area`, the sum of every division of it into triangles that lie apart. The older forms take the figure with its division, checked: triangles that lie apart (`Apart`), triangles fitted together (`Fitted`, `Rectilineal`), or Euclid's from one corner (`Fitted.fan`); equal to the figure means equal to those triangles together | in Book Zero, `division_exists` divides every outline, the content theorem, `Apart.area_eq_of_same_region`, after David Hilbert's theory of content, gives every division of it the same sum (`area_eq`, `area_congr`, `area_of_same_boundary`), and `apart_has_outline` gives every `Apart` an outline with exactly its region; beside I.45, `Prop45.fan_boundary` gives the checked fan its outline, the closed line through its corners in order; and `outline_bounded`, in Book I after I.29, puts every figure within a triangle | `figure-with-dissection`, for the older forms |
| a circle's centre | `exists_centre` gives one for every circle; named centres remain where other hypotheses or conclusions use them geometrically | III.1 finds it by Euclid's construction; proofs cite III.1 where Heath does, and obtain other centres from the rule or the geometric data | |
| a circumference | twice the angle standing on it, `circumference`, `standing`, and for an arc `Arc.measure`; no radius; equal circumferences in III.26 and III.28 are equal in measure and congruent, `Arc.Congruent` | proved facts in `Circumferences.lean`; `Arc.measure_eq_iff` and `Arc.congruent_iff`, in `Arcs.lean` after III.29, say what equal measures and congruence come to | `angle-measure`, `redundant-hypothesis` |
| a segment | its circle, the ends of its base and a point naming its side, `Arc`, with its points, `InSegment`, and its circumference's, `OnArc`; equal segments read through Common Notion 4 as segments that coincide, `Arc.Congruent` | `placement`, from I.4 and I.8, lays one on another in III.24; only III.24 and `Arcs.lean` may cite it | `segment-with-circle` |
| an angle of a straight line and a circumference | `MixedAngle`, the region it opens near its vertex, compared there with a rectilineal angle | the companions of III.16 and III.31 prove the comparisons; no addition, ratio or motion of mixed angles is claimed | `mixed-angles-local` |
| circles cutting | `CirclesCut`: meeting at two points, each circle with a point within the other | `CirclesCut.symm` exchanges the circles; the bridge `CirclesCut.of_meet` in `Audit/` derives this reading from two different circles meeting at two points, obtaining centres internally, by III.7 and III.8 | |
| circles touching | meeting without crossing anywhere (the whole-circle reading Heath reports as Todhunter's); contact within has a point of the inner circle within the outer and none outside it; contact without has no point within both | `within_point` in `Audit/`, by III.10, gives the point within for the earlier reading, with no centre input; these later bridges compare readings, not steps in III.5 or III.6. III.13 still proves uniqueness of contact | `touching-whole-circles` |

The details, and the reasons, are in the book briefs.

## 4. Constructions: what is given, and what shows it works

For a construction, say:

- what the problem gives;
- which operations the construction uses;
- which objects it returns;
- which properties show that it solves the problem.

The existence of a background object is not circular. III.1 meaningfully shows that the
point it constructs is the centre of a given circle; `exists_centre` supplies the
background existence within the proof.

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
  redundant (III.27 holds for any two circles as stated). Say so in the handback;
  the record tags it `redundant-hypothesis` where that is the truth.
- A checked intermediate fact tied to a real sentence of Euclid is legitimate, even if the
  final proof term could do without it.
- **The sweep lists the candidates.** `python3 scripts/sweep_citations.py` lists every
  binding in a proof that Lean's unused-variables linter, its tactic analysis on, finds
  unused; every `obtain` whose whole result goes unused, as
  `obtain ⟨KF, -, -⟩ := Postulate1 …`, which the linter cannot see; every `have`, `let`
  or `obtain` whose name begins with `_` (`have _ := h…`); and every helper that is a
  proof's whole conclusion (below).
  Each hit is fixed, or, where a sentence of Euclid's stands over the step, declared in
  the record: the passage whose `at` begins a sentence of that run of `--` lines lists
  the binding, by the name the proof gives it, in its `unused`, as `unused = ["FC", "GB"]`
  for the joins by Postulate 1 in I.5, or `this` for an anonymous `have`; and
  `check_fidelity.py` fails a name there that the Lean beneath does not bind
  ([review/SCHEMA.md](../review/SCHEMA.md);
  [decisions, 21 October 2026](briefs/0002-decisions.md#21-october-2026)). Nothing else
  declares a hit, and a helper hit is fixed, never declared. The release waits until each
  hit is fixed or declared ([WORKFLOW](WORKFLOW.md), section 10).
- Cite further earlier results when the argument needs them, and say what each does.
- Prefer local proofs whose facts and cases follow the argument. Automation (`ac_rfl` to
  close a sum of magnitudes, and the like) is fine for a local step it checks.

### Euclid's route, and departures from it

Where the page promises Euclid's argument, the Lean follows it: the propositions he uses, in
his order, and nothing later. Some propositions can be reached by a shortcut he did not take
(III.2 by an axiom; III.27, III.30 and III.26's measures by the circumference measure
alone); take his route, for his inferences are the proposition's content.

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
the figure shows, and the main proof keeps every step of Euclid's reductio. The sweep above
reads each proof term and lists a proposition, porism or companion whose proof comes down,
in every case, to one helper that none of its own steps feeds, or that cites a helper
stating exactly what it states.

A construction core kept apart under section 4, as III.1's `Prop1.construction`, carries
Euclid's sentences of construction, not a step he takes for granted; the record shows it as
a `grouped` passage naming it, and the proposition keeps the correctness argument under his
sentences.

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
  in `Elements/BookIII/Circumferences.lean` for those that cite III.20–III.22; and in
  `Elements/BookI/OutlineBound.lean`, after I.29, for `outline_bounded`, which cites I.23
  and uses Postulate 5 (brief 0013). A new shared module (stage 2's
  `Elements/Figure/Sums.lean`, stage 3's placement and arcs, brief 0013's figures given by
  their outlines, in `Elements/Figure/` and `Elements/Foundations/Figures.lean`) has an
  owner, and its place in the order is set in the brief.
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
  Definition I.15 and <!-- count:tacit-rules -->74<!-- /count --> tacit rules, <!-- count:axioms -->80<!-- /count --> in all, each tacit rule from System E (or
  LeanEuclid's corrections of it) with its citation, save one of our own, added by the
  owner's decision of 18 October 2026: every circle has a centre (`exists_centre`), whose
  content is Euclid's Definitions I.15 and I.16 ([brief 0008](briefs/0008-centre.md),
  section 2). A new rule, or a change to one, is a foundation decision (section 1);
  `Certificate/axioms.lock` holds every axiom's exact statement, with every definition that
  the axioms' statements or the propositions', porisms' and companions' statements reach
  (`Touches`, `rect`, `Parallel`), so that no word can change what an axiom or a claim
  says. It changes only through
  `check_fidelity.py --write-lock`, together with a decisions entry, and with the model
  brought to it in the same change, as
  [tests/model/MODEL.md, "Changing the axioms"](../tests/model/MODEL.md#changing-the-axioms),
  says; otherwise CI's `model` job fails. Review an axiom's statement and strength, not
  only the count. An assignment to finish a proof is never permission to add an axiom that
  asserts its conclusion.
- **Nothing gets round the kernel:** no `native_decide`, `decide +native`,
  or any other command of the kinds below, in any Lean file the edition builds: under
  `Elements/`, `Staging/` and `Audit/`, and in their roots, `Elements.lean`,
  `Staging.lean` and `Audit.lean`, and under `model/`, except the package's own
  `model/.lake`, which the scan never enters. Mathlib imports are allowed in the model.
  Only in `model/Check.lean` and `model/Check/`, `run_cmd` may be the first word on its
  line followed by `Check.Generator.<ident>` or `(Check.Generator.<ident>`, since those
  files run the generator. Every other forbidden command or attribute is still refused
  there, and an `axiom` is refused everywhere under `model/`. `check_fidelity.py` matches
  each as a whole word, and `#eval`, `#exit`, `#guard_panic`, `#time`, `#with_exporting`
  and `#guard` also closed up to the word after them, since Lean reads the longest
  command it knows (`#evalx` is `#eval x`), in
  the Lean with its comments and the text of its string and character literals taken
  out, read as Lean reads them, raw strings and escapes among them (`native_decide` even
  in a comment or a string). The code in an interpolated string's `{…}` holes is read
  too; a string whose braces Lean could read either as text or as holes of code, one not
  just after `s!`, `m!`, `f!` or `throwError` whose two readings end in different places,
  is refused, since the scan cannot tell which Lean will do. So is a character literal
  or a raw string closed up to a name or a token that holds a character outside ASCII
  (`a℃'}'`, Mathlib's `⁻¹'`, `a℃r"\" …"`): Lean may read on through the `'` or the `r`
  as part of that name or token, and then a `"` or `}` the scan took for a literal's
  text opens a string or closes a hole, hiding the code after it; an `s!`, `m!`, `f!`
  or `throwError` so closed up (`a℃s!"{"`) is not taken to begin an interpolated string,
  so the string after it is refused if its braces could be holes (#234):
  - `native_decide`, `bv_decide` and `bv_check`, and `decide` with its `native` option,
    have the compiler vouch for a proof in the kernel's place; since `decide +native`,
    `decide (native := …)` and a whole configuration given by `(config := …)` all set
    that option, the word `native`, wherever it stands, and `(config := …)`, spelled
    `config` or `«config»`, are refused;
  - `set_option debug.…`, and its escaped spelling `set_option «debug».…`, which Lean
    reads the same way, with or without a space before the guillemet
    (`set_option«debug».skipKernelTC`): `debug.skipKernelTC` skips the kernel, and
    `debug.byAsSorry` and its kin put `sorry` in place of a proof;
  - `set_option doc.…`, and its escaped spelling `set_option «doc».…`, with or without
    that space (`set_option«doc».verso`): with `doc.verso`
    or `doc.verso.module` on, Lean reads a docstring as Verso and runs the Lean in its
    code blocks, an `#eval` among it, while the file is built, though the scan takes
    docstrings out with the comments; refusing the options keeps every docstring inert;
  - `#eval`, `run_cmd`, `run_elab`, `run_meta`, `run_tac`, `by_elab`, `initialize` and
    `builtin_initialize` run a program when the file is built or imported, which could
    declare an axiom without the word, or write any file, a check or `facts.json` among
    them;
  - `elab`, `elab_rules`, `macro` and `macro_rules` give syntax a meaning written in
    code, which could hide any of the others behind a new name. The simproc commands,
    `simproc`, `dsimproc`, `simproc_decl`, `dsimproc_decl` and `simproc_pattern%`, with
    their `builtin_`, `sym_` and `cbv_` forms, give `simp` code that runs the next time
    it is used in the file, and `set_library_suggestions` does the same for the tactics
    that suggest lemmas. An attribute can register code that Lean runs while a file is
    built or printed. The scan refuses the attributes whose names it lists: any whose
    name ends in `elab` (`command_elab`, `term_elab`, `doElem_elab`, `inductive_elab`,
    and so `delab` and `app_delab`), `macro` (`builtin_macro`), `tactic` (`tactic`,
    `grind_tactic`, `try_tactic`), `init`, `proc` (`simproc`, `dsimproc`, `sym_simproc`,
    `sevalproc`), `discharger`, `unexpander` (`app_unexpander`), `precheck`
    (`quot_precheck`), `formatter`, `parenthesizer`, `control_info`, `code_action`,
    `rpc_method`, `linter`, `parser` (`term_parser`, `command_parser`, `tactic_parser`),
    `pass` (`cpass`), `suggestion` or `suggestions` (`try_suggestion`,
    `library_suggestions`), `check` (`deferred_doc_check`, `package_code_quality_check`),
    `handler` (`missing_docs_handler`), `provider` (`code_action_provider`), `fn`
    (`unused_variables_ignore_fn`), `module` (`widget_module`), `hooks`
    (`run_parser_attribute_hooks`) or `Attr` (`simprocAttr`, `cbvSimprocAttr` and the
    other names Lean gives its simproc attributes); `builtin_doc`; and any whose name
    begins with `doc_` or `builtin_doc_` (`doc_role`, `doc_directive`, `doc_code_block`,
    `doc_command` and the rest). A reading of Lean 4.35's attributes found these to
    register code that Lean, its editor or Lake runs. A list of names trails the
    attributes each Lean release adds, so this one may not be complete, and review still
    reads every staged file and audit lemma;
  - `implemented_by`, `extern` and `unsafe` put code in place of a definition;
  - `#guard_msgs` with `drop`, in any of its forms (`(drop all)`, `(drop error)`,
    `(drop warning)`, `(drop info)`, `(warning, drop all)` and the rest, with or without
    spaces), takes the messages it matches out of the build: with `drop all` or
    `drop error` a theorem that Lean refused still builds, resting on `sorryAx`, and
    with `drop warning` the warning that a declaration uses `sorry` is gone. It is
    refused in every file the scan reads, the audit lemmas and the model among them, with
    no exception, since no file needs it
    ([decisions, 21 October 2026](briefs/0002-decisions.md#21-october-2026)); a need for
    one is asked for in a change of its own;
  - `#guard_msgs` with `substring`, in any setting (`(substring := true)`, or `false`),
    with or without spaces, beside any filter or option: with `substring := true` the
    docstring need only appear somewhere in the messages, so a docstring that is only
    part of the messages (`error`), an empty one, or none, matches an error and takes it
    out of the build. It is refused in every file the scan reads, with no exception,
    since no file uses it;
  - `#guard_msgs` under a docstring that pins an error, one that holds `error:`, the
    word Lean writes before each error it checks: the docstring matches
    the error, and the error leaves the build as with `drop`. It is refused in every
    file the scan reads but two, which pin errors on purpose:
    `model/Check/RoundTrip.lean` pins the generator's refusals, each over a `run_cmd`,
    and `model/Model/Audit.lean` pins one refusal of `#check`. Neither wraps a
    declaration, and review reads any new pin there. The scan reads both files, so the
    allow-list names what it would otherwise refuse
    ([decisions, 21 October 2026](briefs/0002-decisions.md#21-october-2026)). A
    `#guard_msgs` whose docstring pins only info messages or warnings, as the audit
    lemmas' pins do, or that has none, is not refused;
  - `#guard_panic`, which takes every message of the command it wraps out of the build
    once any one holds the word `PANIC`, an error among them;
  - `#time` and `#with_exporting`, each of which wraps the command after it: Lean reads
    the longest token it knows, so `#timeaxiom planted : False` is `#time` and an axiom,
    which a reader of `#` and one name would miss. No file uses either, so both are
    refused wherever they stand, closed up to a command or not (#234);
  - `#guard`, which evaluates its test by compiling and running it while the file is
    built, as `#eval` does. Lean has no token `#guard_x`, so it reads `#guard_x` as
    `#guard _x`, and the scan refuses `#guard` before anything but the rest of Lean's
    other `#guard` tokens, `#guard_msgs` and `#guard_expr`, which run nothing and are not
    refused (`#guard_panic` has its own item). No file uses `#guard`; the coordinator
    decided its refusal on 22 October 2026, as a tightening (#234);
  - a token declared in the file and ending in a character a name may hold, or one
    Python's `\w` takes, a letter, a digit, `_`, `'`, `!`, `?` or `℃` among them, once
    trimmed of blanks as Lean trims it: after
    `infixl:65 " +x " => Nat.add`, Lean reads `2 +x1set_option` as `2`, `+x`, `1` and
    `set_option`, so `2 +x1set_option«debug».byAsSorry true in theorem …` builds on
    `sorryAx`, while the scan, which does not read a file's tokens, takes `x1set_option`
    for one name; and the same holds of `" +x' "`, `" +x! "` and `" +x? "`. The
    coordinator decided the refusal on 22 October 2026 for a token ending in a word
    character, and widened it the same day to the rest of a name's characters, as
    tightenings (#234). A token is each string literal of
    `notation`, `infix`, `infixl`, `infixr`, `prefix`, `postfix`, `syntax`, `macro`,
    `elab`, `binder_predicate`, `declare_simp_like_tactic` or Mathlib's `notation3`, read
    as Lean reads it, escapes, gaps and raw strings among them, on any line of the
    command: from the command's word to its first `=>` outside brackets, or, for a
    `syntax` or `declare_simp_like_tactic`, which has none and may hold a literal after
    a spaced precedence (`syntax "a" term :max " +x " : term`), to the next command,
    known by a word of Lean's own that begins one, by `@[` or by a `#` before a letter.
    Every literal there is read, a `&"…"`, which declares no token, among them, and a
    string in the next command too when that command begins with a word of a library,
    as Mathlib's `lemma`. It is refused in every file the scan reads, with no exception,
    since none declares one ([the decision entry](decisions/2026-10-22-scan-token-boundaries.md)
    gives the count);
  - `#exit` stops Lean reading the file, though a reader and the checks here read on.
- **Superposition** only in I.4 and I.8.
- **Placement,** Euclid's application of one figure to another, only in III.24 and the
  bridge theorems of `Elements/BookIII/Arcs.lean` (brief 0006): outside its own files,
  `Elements/BookIII/Placement.lean` and `Elements/BookIII/Placement/`, no other Lean under
  `Elements/` names `placement` or a lemma of the `Placement` namespace, and no entry but
  III.24 calls on one.
- **Postulate 5.** No proof before I.29 uses Postulate 5 or a rule declared in
  `Elements.Tacit.Euclidean`; Books II and III come after Book I and may use it throughout.
- **Circle 2 and Circle 3.** No certificate entry rests on `Tacit.inside_of_between` or
  `Tacit.outside_of_between`, whether through its own proof or through a lemma it uses;
  each name must stay in the axiom lock, or name a theorem whose `proved_rules` entry
  in `facts.json` includes another forbidden circle rule still in the lock as an axiom.
  Thus a proved rule remains forbidden through the axiom beneath it; a missing name,
  or a proof without such an axiom, fails the check.
- **No later citations:** no proof cites a proposition that does not come before it.
- **Complete books stay complete:** every proposition of a complete book is proved, with
  both figures and a mishnah, and so is every porism and companion attached to it.
- **Primitive words stay `opaque`,** so Lean knows of them only what the axioms say.

`check_fidelity.py` enforces these for every certificate entry, porisms and companions
included. `negative_tests.py` plants a break of these kinds to show each is caught: an
axiom declared outside the foundations, in each of `Elements/`, `Staging/`, `Audit/`,
`model/Model/` and `model/Check/`,
one of them after another command on its line; an axiom missing from the lock, and one
weakened; Postulate 5 and a Euclidean-only rule before I.29; superposition outside I.4
and I.8; Circle 2 or Circle 3 in a proposition's, porism's or companion's axioms,
Circle 3 renamed in the lock; and Circle 2 proved without Circle 3 beneath it, with a
matching case that still rests on locked Circle 3 and must pass;
placement among the shared steps of an entry other than III.24, and a lemma of
its namespace named in another file under `Elements/`; a later citation, one of them
named only in a helper's statement; every forbidden command, and an attribute for each
ending and prefix the scan knows, in each of those five folders, and `#exit` at the end
of each root; generator `run_cmd` calls, plain and parenthesised, outside the model's
Check files, and calls there to another namespace or after another command on the line;
other forbidden commands on an allowed generator call's line or in its arguments;
`set_option«debug».skipKernelTC` and the other spellings of the `debug.` and `doc.`
options with no space before the guillemet, `#eval`, `#exit` and `#guard_panic` closed up
to the word after them, and `#guard_msgs` with `drop`, with `substring`, and under a
docstring that pins an error, each in each of its forms, in a scratch copy of I.1's file;
`set_option` closed up to decimal, hexadecimal, scientific and underscore-separated
numbers, after a projection and after a declared notation ending in `.`, with whitespace
or a comment beside it, and `axiom` closed up to such a number, with controls that
preserve ordinary projections; `set_option` and `axiom` closed up to the postfix `⁻¹`,
and to `#time` and `#with_exporting`, which are refused too before a `def` and alone on
their line; `#guard` closed up to the word after it; `set_option` closed up to a
declared token ending in `℃`; a declared token
ending in a letter, a digit, `_`, `'`, `!` or `?`, after a notation's other token on its
second line too, with `set_option` closed up to it; a character literal, a raw string and
an `s!`'s string closed up to a name or token that holds a character outside ASCII, each
before `set_option`, each in a scratch copy of its own;
the same pin at a new file beside each file of its allow-list, at each file's name in the
other's folder, in `Audit/` and in `Staging/`, and a pin whose `error:` ends its line;
a proposition imported by Book Zero; a `sorry` in a
complete book; and a primitive word no longer opaque. Some of the forbidden commands
stand after a string, a raw string or a character literal holding `/-`, `-/`, `]` or `"`,
and one in an interpolated string's hole, and a string whose braces Lean could read as
code is planted too. The source scan names each finding's file and line, except for
symbolic links to files or directories in the scanned trees and root files, which are
refused by their paths and never followed, a link at `model/.lake` among them. I.1's
figure, idea figure and mishnah are each removed in turn, and the fidelity check names
the one missing, since Book I is complete. Past the scan, a copy of I.1 outside the tree,
with `set_option debug.skipKernelTC true` and a `run_cmd` that adds `True.intro` as a
proof of `False`, is compiled over I.1's `.olean`, and leanchecker's replay (section 9)
must refuse that declaration by name. The tests also check
that generator calls first on their line are allowed in `model/Check.lean` and
`model/Check/`, that an axiom in a `.lake` folder of `model/Model/` or `model/Check/` is
caught while one in `model/.lake` is not read, that a link named `.lake`, to a
directory, a file or nothing, is refused in `model/`, `model/Model/` and `model/Check/`,
that a `#guard_msgs` that checks its messages or passes them on, one under a docstring
that pins an info message, `error:` in a theorem's own docstring, a comment or a module
docstring before a `#guard_msgs`, `#guard_msgs` and `#guard_expr` beside `#guard`, a
declared token ending in a symbol, a string after a notation's `=>`, and the words of
each of these commands in a comment or a string, are not refused, that the pin passes at
each file of its allow-list, that the scan reads the literals of a declaration as Lean
does, over two lines, after a spaced precedence, raw, escaped or with a gap, to the next
command begun by `@[` or a `#` command, and no string outside one nor a dotted name's
word, that it marks a literal closed up as above but no other, and that the unplanted
tree passes.
They plant source files in place, the `.lake` links and the scratch copy of I.1's file
in small trees of their own, and copy only `facts.json` and that one copy of I.1, never
`model/.lake`.

The first two policies hold in `Staging/` (section 6), `Audit/` and `model/` as well,
with the model's Check allowance above. Nothing there reaches the certificate, so the
source scan is what enforces them:
`check_fidelity.py`'s `check_rules` reads every `.lean` file under `Elements/`,
`Staging/` and `Audit/`, and the three roots, and every `.lean` file under `model/`,
without entering the directory `model/.lake`, whose contents go unscanned; a link at
`model/.lake` is refused like any other link, and a `.lake` folder deeper in the model is
read like any other. It refuses an `axiom` anywhere outside
`Elements/Foundations/` and every command and attribute the list above names, with only
two exceptions: the generator `run_cmd` allowance in `model/Check.lean` and
`model/Check/`, and the error pins of `model/Check/RoundTrip.lean` and
`model/Model/Audit.lean`.
`MODEL_CHECK_RUN_CMD` names that allowance in the script; it exempts only `run_cmd`,
so its arguments and any further command on the line are still scanned. Book Zero's
import rule and the placement policy remain confined to `Elements/`. It reads each file's
bytes decoded as UTF-8, with no newline translation, so a `--` comment ends only at a
line feed, as it does for Lean, and reads comments, literals and number endings as Lean
4.35's tokenizer does, so a string cannot hide a command by opening a comment or ending an
attribute's brackets, and a word closed up to a number remains visible. An adjacent
numeric projection stays a projection; where a declared `.` notation makes a longer
number the competing reading, the longer boundary stays visible too. Whitespace and
comments end projection adjacency, as they do in Lean. A name ends where Lean 4.35 ends
it, made only of the characters its `isIdFirst` and `isIdRest` take, so a letter or digit
that no name holds, as the `¹` of the postfix `⁻¹`, does not join the word after it
(`1⁻¹set_option` is `1`, `⁻¹` and `set_option`); and it ends sooner, before any of the 96
characters a Lean name may hold that Python's `\w` does not take, as `℃`, which no file
uses, so that a word after a token ending in one, as a library's, is seen to begin
(`2 +℃1set_option`). Ending a name early, or blanking a character, shows the scan more
words, and changes nothing else, but where a character literal, a raw string, or an
`s!`, `m!`, `f!` or `throwError` follows closed up: Lean may read on through it as part
of the name or a token, so the scan refuses the literal or the raw string, and takes no
such word to begin an interpolated string (the list above). It refuses a token the file
declares that ends in a character a name may hold (the list above). It does not read the
rest, and these stay open, each example built in Lean 4.35 as written:
- Lean's own tokens that begin with `#`
  ([#320](https://github.com/jackChallis/stoicheia/issues/320)), which the scan reads as
  `#` and the name after it. Lean reads the longest token it knows, so
  `#check1set_option«debug».byAsSorry true in theorem …` is `#check`, `1` and
  `set_option`, and builds on `sorryAx`, and `#whereaxiom planted : False` is `#where`
  and an axiom, while the scan reads the names `check1set_option` and `whereaxiom`. Those
  the list above names, `#eval`, `#exit`, `#guard_panic`, `#time`, `#with_exporting` and
  `#guard`, are refused closed up or not. A fixed list of the rest would not do: which
  `#` tokens Lean has depends on what the file imports (`#widget` comes with
  `import Lean`, not with `Init` alone), and a file may declare a longer one, so the list
  would misread a file that lacks one and could hide the code after it
  (`s!"{5#widget'}'"`, where Lean reads `5#widget'` as a bit-vector literal and the `}`
  closes the hole).
- Lean's other own tokens ([#317](https://github.com/jackChallis/stoicheia/issues/317)).
  Of those that end in a name's character, four end in `'`, `]'`, `×'`, `Σ'` and `⊕'`;
  the scan blanks the `Σ` and refuses a literal after it, but
  takes the `'` of the other three for a character literal's opening, so that
  `def T : Type := Nat ⊕'"' "`, with a coercion from `String` to `Type`, and
  `set_option«debug».byAsSorry true in theorem …` on the next line, builds on `sorryAx`
  while the scan reads the command as a string's text. Three end in `-` or `/`, `<-`,
  `//` and `\/`, and before a `-` the scan reads a comment where Lean reads none:
  `def S : Type := {x : Int //-1 < x}` and that `set_option` line build on `sorryAx`.
- A token the file declares that ends in a symbol, which is allowed
  ([#317](https://github.com/jackChallis/stoicheia/issues/317)): one that holds a
  comment's opening or a quote hides the code after it, as `infixl:65 " ⊕-- " => Nat.add`
  and `def k : Nat := 1 ⊕--2set_option«debug».byAsSorry true in theorem …` do.
- A token of a library a file imports, as Mathlib's `''` or `#find`, and a token declared
  by a command the list above does not name: neither is read.

A lone carriage return (a `\r` not followed by `\n`) is refused in any scanned file: Lean
refuses one between tokens but accepts it inside a comment or a literal, where a `--` comment does not end at it, so a
reader with universal newlines would end the comment there and let a string open behind
it that swallows the code, a forbidden command among it. CRLF files are allowed, as Lean
allows them (it reads `\r\n` as `\n`), and no tracked `.lean` file has a carriage return
today. Beyond that it reads words, not Lean's grammar nor the tokens a file declares, so it
catches a slip but not a command disguised from it on purpose, nor an attribute it does
not list: review still reads every
staged file, audit lemma and model file. In `Elements/` the certificate reads the axioms
from Lean itself as well. In `model/`, the scan reads words and the replay reads proofs:
after `lake build`, CI's `formal-model` job runs `scripts/check_model_kernel.py`, in which
leanchecker replays every compiled declaration of the model's `Model` and `Check` libraries
through Lean's kernel again, apart from the build (#121); a module compiled in the package
outside those two libraries is an error, by name. That replay runs without `--fresh`, so
what those modules import is loaded, not replayed; then leanchecker replays the whole
environment of `Check`, which has no Mathlib, from nothing (`--fresh`). So Lean's own
library is replayed here as far as `Check` loads it, `Std` and every `Lean` module among it
(`Check/Generator.lean` has `import Lean`), and so are the library's declarations that
`Check` imports, which, with `Init`, are `check_kernel.py`'s as well. What `Model` loads
through Mathlib is loaded, not replayed: Mathlib's declarations, and five of `Lake`'s
modules outside `Check`'s environment, are left to Mathlib's own checks, on Mathlib's
toolchain. Its self-test plants a theorem of `False` added without the kernel's check,
which `lake build` accepts and the check must reject by name, in the model's libraries and
in a package that `Check` requires
([model/README.md](../model/README.md#the-ci-job), "The CI job").
The checks' own Lean, `Certificate/Facts.lean`, which writes `facts.json`, is not
scanned: it is a protected path ([WORKFLOW.md](WORKFLOW.md), section 10), changed only
with a decisions entry and a security review.

### Rules now proved

19 October 2026: eight rules became theorems, taking the lock from 87 axioms to 79.
Each keeps its `Elements.Tacit` name and exact type. The namespace preserves the
interface; it does not make a declaration an assumption. The certificate follows each
proof to the assumptions it uses.

| Theorem under `Elements.Tacit` | System E label | Derivation and home |
|---|---|---|
| `adjacent_eq_of_right` | Diagram-angle 3 | I.13 makes adjacent angles two right angles; Common Notion 3 removes the given right angle. Proved after I.13 in [`Prop13.lean`](../Elements/BookI/Prop13.lean). |
| `not_same_side_of_circles_meet` | Circle 4 | Definition I.15 gives equal distances from each centre, `circle_eq` tells the centres apart, and I.7 excludes two common points on the same side. Proved after I.7 in [`Prop07.lean`](../Elements/BookI/Prop07.lean). |
| `centre_unique` | Generalities 2 | Two supposed centres bisect the same straight line through the circle by Definition I.15. Equal doubles have equal halves, and the strict order of lengths forces the centres to coincide. Proved from the foundations in [`Circles.lean`](../Elements/Figure/Circles.lean). |
| `inside_of_between` | Circle 2 | Circle 3, `outside_of_between`, would put the second endpoint outside if the middle point were not inside. Proved in `Circles.lean`. Circle 3 stays an axiom. |
| `exists_point_outside_circle` | Points 9 | Points on the circle enclose an interior point; Postulate 2 produces the line beyond the circumference, avoiding the given finite list, and Circle 3 puts the new point outside. Proved in `Circles.lean`. |
| `line_meets_circle_of_opposite_sides` | Intersection 2 | Intersection 1, betweenness and Pasch 2 locate a crossing between the given points; Circle 3 puts it inside, and Intersections 5 gives two distinct points of the circle on the line. Proved in `Circles.lean`. |
| `triple_incidence3` | Triple incidence 3 | Angle addition and positivity, Intersection 1, and the order and side rules locate a crossing and carry its side relation to the given point. Proved in `Circles.lean`. |
| `inside_of_angle_add` | Diagram-angle 2, converse | I.13, angle addition, positivity and the side rules exclude each way the point could lie outside the angle. Proved after I.13 in `Prop13.lean`; the forward rule, `angle_add_of_inside`, stays an axiom. |

The current proofs of Points 9 (`exists_point_outside_circle`) and Intersection 2
(`line_meets_circle_of_opposite_sides`) both depend on Circle 3. The certificate applies
the Circle 2 and Circle 3 ban transitively, so no proposition, porism or companion may
depend on either proved rule.

A client that previously imported only the foundations must now import the theorem's
home. Book Zero still imports no proposition. I.7 cannot be established independently
through Circle 4, since that theorem now uses I.7. III.2 still has an overlap with the
retained Circle 3 axiom, as the [catalogue](reports/overlaps.md) explains.

No certificate entry currently rests on Circle 3. I.12 finds the crossing X of
CD with AB between the centre C and the point D on the circle, proves X inside
by `InsideCircle.of_between_centre`, and uses the assumed Intersection 3
(`line_meets_circle_of_inside`) to find two points of the circle on AB. The proved
Intersection 2 has no user in the published proofs.

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
| The numerical model tests (`tests/model/`) | The locked axioms held in the configurations sampled from a standard model of the plane, exactly where coordinates allow, and planted mutations of them were caught. | A proof of consistency: a test can find a counterexample but cannot show there is none, and laws no harness reaches rest on a hand argument. |
| The hyperbolic check (`tests/model/hyperbolic.py`) | Every axiom but Postulate 5 held in the configurations sampled from the hyperbolic plane, and Postulate 5 failed there. | Non-derivability: numerical tests do not establish that a statement failing there cannot be proved without Postulate 5. |
| The informal model argument | A reasoned interpretation of each law in the standard plane. | A machine-checked proof. |
| The formal model ([#73](https://github.com/jackChallis/stoicheia/issues/73): [`model/`](../model/README.md), a Lake package of its own with a pinned Mathlib, built by CI's `formal-model` job) | Lean checks that the ordinary Euclidean plane satisfies every law in this revision's foundations: all <!-- count:axioms -->80<!-- /count --> laws of the lock, generated from the elaborated declarations with the translation checked, each proved in the plane with only Lean's own axioms beneath it, and gathered in `model_exists`, with no hypothesis left. This establishes a model relative to Lean's logical foundations and Mathlib's construction of the real numbers, so the consistency of the axioms is a theorem relative to those. The model holds the lock's hash, so any change to the lock fails its build until the model is brought to it ([MODEL.md](../tests/model/MODEL.md#the-formal-model)). | That every formal statement captures Euclid's intended meaning. Non-derivability: that a statement cannot be proved without Postulate 5 still rests on the numerical hyperbolic check, until a hyperbolic model is built. |

The certificate describes proof-term dependencies, and nothing more. "This proof uses
Postulate 5" is a fact about our proof. By itself it establishes neither the consistency of
the foundations, nor the necessity of an axiom, nor the independence of the parallel
postulate, nor that the Lean means what Euclid meant. A claim that a result cannot be
proved without the postulate names its evidence and its kind. The evidence is an
interpretation in which the other axioms hold and the result's own statement fails, its
hypotheses met; that the postulate fails there is not enough, and a result whose statement
stays true there needs a different analysis. The kind is numerical until a proof replaces
it, and even then the pages keep "this proof uses".
