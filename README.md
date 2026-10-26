<p align="center">
  <img src="assets/stoicheia-social.png" alt="Raphael's Euclid, from The School of Athens, drawing the figure of Proposition I.47 on a laptop" width="760">
</p>

# Stoicheia

*Euclid's Elements in Lean, sentence by sentence.*

Στοιχεῖα, *Stoicheia*, "Elements", is Euclid's title for the book that taught geometry for more than two thousand years. Abraham Lincoln, in the short autobiography he wrote in 1860, said of himself: "He studied and nearly mastered the Six-books of Euclid, since he was a member of Congress." The book turns up in his debates and his letters too, as [Lincoln and Euclid](docs/lincoln.md) tells. This project carries the same book into [Lean](https://lean-lang.org), a programming language that checks mathematical proofs, so that Euclid's steps are checked by a machine that can't be talked into anything.

Lincoln's autobiography is in Roy P. Basler (ed.), [*The Collected Works of Abraham
Lincoln*](docs/lincoln.md#basler1953collected), vol. 4, p. 62; his uses of Euclid in
vol. 3, pp. 186 and 375. These passages were found through Glenn W. LaFantasie,
["Lincoln, Euclid, and the Satisfaction of Success"](docs/lincoln.md#lafantasie2020satisfaction),
*Journal of the Abraham Lincoln Association* 41, no. 1 (2020): 24–46, pp. 24 and 43–44.

For every proposition of Books I to III you get:

- **Euclid's words**, in Sir Thomas Heath's 1908 translation (public domain).
- **Two figures**: one "at a glance", in the bold red, yellow and blue of Oliver Byrne's 1847 Euclid, to show the idea before you read a word; and Heath's figure, redrawn, to follow the proof by. Both carry Heath's letters, the names the Lean uses too, so you can pass from one to the other.
- **The proof in Lean**, written to follow Euclid sentence by sentence. Each of his sentences is a comment, and the Lean beneath carries it out, sometimes several sentences together. Where the Lean takes another step, or leaves a passage in Euclid's words with no Lean beneath it (as in I.4 and III.16), the page says so beside the listing.
- **A certificate**, computed by Lean itself, of exactly what the proof rests on: which postulates, which common notions, and which of the many things Euclid takes for granted without saying so.
- **A mishnah**: commentary on what Euclid assumed, what Lean made us say out loud, and how the same result looks with modern tools.

The proofs use no coordinates, real numbers or complex numbers; only "The modern way", a paragraph that closes a commentary where one helps, reaches for them. The geometry is the geometry Euclid wrote, the kind Lincoln would recognise. Lengths, angles and areas are *magnitudes*, which can be added and compared and nothing more, just as in the *Elements*.

## Where things stand

| | |
|---|---|
| **Book I** | <!-- scope:I -->**All 48 propositions proved in Lean**, every one as Euclid states it. Every proof follows Euclid's argument, and each page notes where the Lean departs from his sentences. Our proofs of 29 propositions do not use the parallel postulate: I.1–I.28 and I.31. The first proof that does is I.29's, just where Euclid first calls on it.<!-- /scope:I --> [Read Book I →](book/I/index.md) |
| **Book II** | <!-- scope:II -->**All 14 propositions proved in Lean**, every one as Euclid states it. Every proof follows Euclid's argument, and each page notes where the Lean departs from his sentences. Every proof uses the parallel postulate: II.10's directly, where Euclid calls on it, and the others through the propositions they cite.<!-- /scope:II --> "The rectangle contained by AB, BC" and "the square on AB" are areas in our foundations, defined rather than assumed, and a rectangle drawn in a figure is proved equal to the rectangle contained by its sides. [Read Book II →](book/II/index.md) |
| **Book III** | <!-- scope:III -->**All 37 propositions proved in Lean**, every one as Euclid states it. 26 proofs follow Euclid's argument and 11 follow it with one or more steps changed ([III.2](book/III/02.md), [III.4](book/III/04.md), [III.8](book/III/08.md), [III.10](book/III/10.md), [III.16](book/III/16.md), [III.17](book/III/17.md), [III.24](book/III/24.md), [III.26](book/III/26.md), [III.27](book/III/27.md), [III.28](book/III/28.md), [III.29](book/III/29.md)); each page says how. In [III.5](book/III/05.md) and [III.6](book/III/06.md) our tacit rules contain the propositions too, but our proofs never use those rules. In [III.1](book/III/01.md) one of our tacit rules supplies a step of a proof of the proposition, and our proof rests on it. [The overlap catalogue](docs/reports/overlaps.md) gives each. Our proofs of 17 propositions do not use the parallel postulate: III.1–III.13 and III.16–III.19. The first proof that does is III.14's.<!-- /scope:III --> Equal circles, a straight line touching a circle and circles touching one another are defined in Lean, not assumed, and a circumference is measured by twice the angle standing on it, a measure with no radius in it. So, as stated, III.27 holds in any two circles. Segments are figures with their points, and equal segments are those that coincide: III.24 lays one on the other, and III.26 and III.28 conclude that equal circumferences coincide as well as having equal measures. [Book III's introduction](book/III/index.md) tells how. [Read Book III →](book/III/index.md) |
| Books IV–XIII | To come, one book at a time. |

The [certificate](CERTIFICATE.md) is regenerated from the proofs on every change, and so is the [graph of who uses whom](GRAPH.md), drawn from Heath's references and from the Lean's own.

## Read it

Start with [the definitions, postulates and common notions](book/I/front.md), then [Proposition 1](book/I/01.md). Every page of Books I to III reads the same way: Euclid's statement, with a line saying what the Lean statement covers; his figure; his proof; then the Lean, what it rests on, and the mishnah.

Here is the heart of I.1. Euclid's sentences are the comments:

```lean
  -- With centre A and distance AB let the circle BCD be described; [Post. 3]
  obtain ⟨BCD, hA_BCD, hB_BCD⟩ := Postulate3 A B hAB
  -- again, with centre B and distance BA let the circle ACE be described; [Post. 3]
  obtain ⟨ACE, hB_ACE, hA_ACE⟩ := Postulate3 B A hAB.symm
  -- and from the point C, in which the circles cut one another, …
  have hmeet := circles_meet hB_BCD (centre_inside hA_BCD) (centre_inside hB_ACE) hA_ACE
  -- …
  -- Now, since the point A is the centre of the circle CDB,
  -- AC is equal to AB. [Def. 15]
  have hAC : ‖A C‖ = ‖A B‖ := Definition15 hA_BCD hC_BCD hB_BCD
```

That `circles_meet` is a step Euclid never justifies. Heath: "It is a commonplace that Euclid has no right to assume, without premising some postulate, that the two circles *will* meet in a point C." In our foundations it has to be a named rule, and so it appears on I.1's page, under "What it rests on".

To read further, a page may end with a line or three chosen for its proposition, and [the reading list](docs/reading.md) gathers books, papers and a few web pages by theme, from Proclus and Hilbert to Lean, marking the ones free online.

## What Euclid takes for granted

The foundations are in [`Elements/Foundations/`](Elements/Foundations):

- [**Postulates**](Elements/Foundations/Postulates.lean): Euclid's five, each a Lean `axiom`.
- [**Common Notions**](Elements/Foundations/CommonNotions.lean): all five turn out to be *theorems*, once we state how magnitudes add and compare.
- [**Definitions**](Elements/Foundations/Definitions.lean): the ones that do work in the proofs. Definition I.15 (all radii of a circle are equal) is really an axiom, and is treated as one. [Book II's](Elements/Foundations/DefinitionsII.lean) are the rectangle contained by two straight lines and the square on one, defined, not assumed; [Book III's](Elements/Foundations/DefinitionsIII.lean) are equal circles, a straight line touching a circle, circles touching one another, read of the whole circles and at the point of contact, a circumference measured by twice the angle that stands on it at the circumference, and the angle at the centre standing on that circumference, which may be two right angles or more.
- [**Tacit rules**](Elements/Foundations/Tacit): what Euclid reads off his figures without saying so, and how magnitudes add and compare. <!-- count:tacit-rules:Word -->Forty-three<!-- /count --> remain axioms, including that two triangles which match in every side and angle have the same area. Forty are now theorems. For example, producing a straight line from an interior point to the circumference in both directions proves that it cuts the circle. Their [derivations and homes](docs/FORMALIZATION.md#rules-now-proved) distinguish what is proved from what remains assumed. Most follow, rule by rule, the System E of Jeremy Avigad, Edward Dean and John Mumma, which was designed to capture exactly how Euclid reasons from a diagram; the laws of magnitude are its §3.5. Superposition is a restricted inference in System E's style, with placement data adapted from LeanEuclid, and is allowed only in I.4 and I.8 ([its file](Elements/Foundations/Tacit/Superposition.lean) says more). Two rules are our own: every circle has a centre (`exists_centre`), which Euclid's definition of a circle gives it (Definitions I.15 and I.16), and a circle's radius is not nothing (`radius_ne_zero`), since Euclid draws every circle with a distance (Postulate 3).

Because every assumption is a Lean `axiom`, `#print axioms` lists exactly what a proof rests on, and [`Certificate/Facts.lean`](Certificate/Facts.lean) turns that into the certificate. One famous question has a mechanical answer: whether our proof of a proposition uses the parallel postulate. CI fails if any proof before I.29 does. Whether some other proof could do without it is a different question, which the certificate does not answer.

Proposition by proposition, the steps Euclid takes without a word, and the rule or lemma that fills each one, are gathered in catalogues for [Book I](docs/reports/gaps-book-I.md), [Book II](docs/reports/gaps-book-II.md) and [Book III](docs/reports/gaps-book-III.md), with the names of those who noticed them first, where we know.

## What the checks show

Each check answers one question and leaves others open. Here is what each one shows, and what it does not.

| Evidence | What it shows | What it does not show |
|---|---|---|
| **Lean's kernel accepts the proof** (`lake build`) | The Lean statement follows, by steps the kernel has checked, from the axioms the proof rests on | That the statement says what Euclid says, or that the axioms are true of the plane |
| **Lean's kernel again, and nanoda** (`scripts/check_kernel.py`) | Every declaration of the compiled `Elements` library, Lean's own included, is checked twice more. Lean's leanchecker (Kim Morrison's and Sebastian Ullrich's, begun as Morrison's [lean4checker](https://github.com/leanprover/lean4checker)), run with `--fresh`, replays the whole environment of `Elements` through Lean's kernel, so no declaration reached the compiled files without the kernel's check. Chris Bailey's [nanoda](https://github.com/ammkrn/nanoda_lib), written separately, checks the whole export of `Elements` that Henrik Böving's leanexport writes, admitting only the axioms of [`Certificate/axioms.lock`](Certificate/axioms.lock) and Lean's three (`propext`, `Classical.choice`, `Quot.sound`). With `--self-test`, Postulate 5, which I.29's proof uses, is withheld, and nanoda must then fail, naming it | Anything about meaning: both check Lean's logic, and a fault in that logic would pass them both. A fault in the code of Lean's kernel would pass leanchecker too, which runs the same kernel as `lake build`; nanoda, written separately, is the guard against one. Nor that each axiom admitted states what the lock records: nanoda admits them by name, and the fidelity check compares the statements |
| **No `sorryAx`** in anything a proof rests on, as each ✅ on the [certificate](CERTIFICATE.md) says | Nothing was left unproved, in the proof or in anything it cites; and each proposition's page lists every axiom it rests on | That no other proof could rest on fewer: "this proof uses Postulate 5" is not "this proposition needs it" |
| **The fidelity check** (`scripts/check_fidelity.py`) | Each enunciation, and each sentence of Euclid's proofs, stands in the Lean word for word and in order, as Heath has them; and the house rules hold: no axiom outside the foundations, each axiom, and each definition the statements use, as [`Certificate/axioms.lock`](Certificate/axioms.lock) records it, superposition only in I.4 and I.8, Postulate 5 in no proof before I.29, no certificate entry (proposition, porism or companion) resting on Circle 2 or Circle 3 as an axiom, none before III.2 using either, and no proof citing a later proposition | That the Lean beneath a sentence does what the sentence says: it checks wording, not meaning; nor that no proof rests on a rule containing a later proposition: the [overlap catalogue](docs/reports/overlaps.md) lists where one does |
| **The review records** ([`review/`](review)) | Reviewers have read each Lean statement against Euclid's enunciation and recorded every departure (its scope, route, representation and any passage not plainly carried), tied to the commit read; a record read in full classifies every passage of the argument as well. Each record names its reviewer, and CI flags a record whose statement or Lean has changed since | A machine check of meaning: a record is a careful reader's judgment, and a reader can be wrong. How many of each book's records are read in full is in [the status table](docs/PROGRAM.md#3-status); the [Jev audit of Books I and II](docs/reports/acceptance/jev/audit-books-I-II.md) preserves its evidence and unresolved limits |
| **The citation sweep** (`scripts/sweep_citations.py`) | Every candidate for a dummy citation, an artificial hypothesis use or a concealing helper is listed, and marked where its review record declares it: each binding in a proof that Lean's own unused-variables linter, with its tactic analysis on, finds unused (a hypothesis that `assumption` or `simp_all` uses counts as used); each `obtain` whose whole result goes unused, as `obtain ⟨KF, -, -⟩`, which the linter cannot see; each `have`, `let` or `obtain` whose name begins with `_`; and each proof, read from Lean's proof terms, that comes down to one helper its own steps do not feed, private or not, or to a part, a turn or one way of one (`.2`, `.symm`, `.mp`), directly or through a step that binds it. A file is refused if it sets the linter's options itself, in any spelling or spacing; uses `#guard_msgs` for anything but a pin of `#print`, which could swallow a report; or, outside Staging, holds a `sorry` or `admit`, even one that never runs, which makes the linter pass over its declaration. A release waits until every hit is fixed or declared. With `--self-test`, a planted case of each kind must be found and its controls passed | That a hit is a defect: a fact Euclid states and the Lean never uses again is legitimate, and a reader decides. Nor that nothing escapes it. These shapes pass it: a binding cleared with `clear h`, or handed to a function that ignores it, `(fun _ => …) h`; a kept name that automation such as `contradiction` or `simpa` follows in its declaration, where the textual pass stands aside; a name an `obtain` or `rcases` keeps that a later binding writes again, which counts as naming it; a `_` name inside a pattern or after `intro`; a citation whose result feeds only another idle step, listed by that step alone; a helper fed by one trivial step, unless its statement is the entry's own; and a part of a helper's result returned from a `match` on two or more terms at once |
| **The negative tests** (`scripts/negative_tests.py`) | The checks catch an edited Heath word, a wrong step, a `sorry` in a complete book, forbidden commands including `native_decide`, a weakened axiom, a definition given another meaning, a primitive word no longer opaque, stale and incomplete review records, Postulate 5, superposition, a later citation or a new axiom slipped into an early proof or porism, and Circle 2 or Circle 3 added to an entry's dependencies. Further plants test a style rule, a broken relative link, a generated page stale beside a changed source, an audit lemma's expected axiom list, a complete book's missing figure or mishnah, and leanchecker's rejection of a corrupt compiled file header and of an ill-typed proof in a compiled module. Each must produce its own diagnostic or, for freshness, the page's Git status line. The kernel check's own `--self-test` withholds Postulate 5 from nanoda | That no fault of another kind could slip past. The corrupt header tests leanchecker's loading of compiled files, and an ill-typed proof in I.1's compiled module (`True.intro` given for `False`) its kernel replay; the formal model's replay has its own planted proofs, in its self-test. An audit pin tests the expected axiom list, not the completeness of the overlap catalogue |
| **The numerical model tests** ([`tests/model/`](tests/model)) | In the ordinary plane, no configuration tested breaks any axiom, and all 15 deliberate mutations are caught: fourteen weaken rules, assumed or now proved, and one the placement that supports superposition, so the search can find counterexamples of those kinds | That no configuration anywhere breaks one |
| **The hyperbolic check** ([`tests/model/hyperbolic.py`](tests/model/hyperbolic.py)) | Every axiom but Postulate 5 holds, numerically, in the hyperbolic plane, and Postulate 5 fails there | That the other axioms provably cannot give Postulate 5, or that a statement failing there cannot be proved without it: numerical tests do not establish non-derivability |
| **The model argument** ([`tests/model/MODEL.md`](tests/model/MODEL.md)) | An argument, law by law, that every axiom holds in the ordinary plane, degenerate cases included; if it is right, the axioms cannot contradict one another unless the real numbers do | A checked proof: readers must follow it for themselves |
| **The overlap audit** (`lake build Audit`) | Each current axiom overlap in the [catalogue](docs/reports/overlaps.md) is checked: the proposition is proved from the rules named, with the axioms Lean reports pinned. The retained derivations through retired rules are labelled, including those that are now circular | That there are no other overlaps |
| **The formal model** ([`model/`](model/README.md)) | Lean checks, with Mathlib, in a package of its own, that the ordinary Euclidean plane satisfies every law of the lock, all <!-- count:axioms -->49<!-- /count --> of them, gathered in the theorem `model_exists` with no hypothesis left. This establishes a model relative to Lean's logic and Mathlib's construction of the real numbers, so the axioms cannot contradict one another unless those foundations do. The model holds the lock's hash, so any change to the lock fails its build until the model is brought to it; CI's `formal-model` job builds it. Then leanchecker replays every compiled declaration of the model's own `Model` and `Check` libraries through Lean's kernel, apart from the build (`scripts/check_model_kernel.py`), so each passes Lean's kernel a second time; one that reached the compiled files without the kernel's check and does not pass it fails the job, as does a module compiled in the package outside those two libraries. It then replays the whole environment of `Check`, which has no Mathlib, from nothing: Lean's own library as `Check` loads it, the `Elements` modules that `Check` imports, the plain-Lean part of `Model`, and `Check`. With `--self-test`, a theorem of `False` added without the kernel's check, which `lake build` accepts, must be rejected, by name | That every formal statement captures what Euclid meant: that is the work of the review records. Nor that the other axioms cannot give Postulate 5: until a hyperbolic model is built in Lean, that rests on the numerical hyperbolic check above. Nor that Mathlib's own declarations, whose compiled files are downloaded, pass a second check here: the model's replay loads them without replaying them, and leaves them to Mathlib's own checks. Nor that all of Lean's own library beneath the model does: the replay from nothing covers all that `Check` loads, every `Lean` module among it, but five of `Lake`'s modules, which the model loads through Mathlib, lie outside it, and are left with Mathlib to Mathlib's daily job, on Mathlib's toolchain |

Each proposition's page shows, under Euclid's enunciation, what its Lean statement covers and whose argument its proof follows, from its review record.

## Run it

1. Install Lean: the easiest route is VS Code with the **Lean 4** extension, or `curl https://elan.lean-lang.org/elan-init.sh -sSf | sh`. The `lean-toolchain` file pins Lean 4.35.0. The checks below and the pages need Python 3.11 or later, and nothing else.
2. Check every proof:
   ```sh
   lake build
   ```
3. Rebuild the certificate and the pages, and check that the Lean still quotes Heath word for word:
   ```sh
   lake env lean Certificate/Facts.lean
   python3 scripts/check_fidelity.py
   python3 scripts/render.py
   ```
4. Run the other checks behind [What the checks show](#what-the-checks-show). The kernel
   check reads the build of step 2, and takes about a minute on a laptop. The negative
   tests break files on purpose and put them back, so run them on a clean checkout:
   ```sh
   lake build Audit
   python3 scripts/check_kernel.py --self-test
   python3 scripts/check_style.py
   python3 scripts/check_links.py
   python3 scripts/negative_tests.py
   python3 -I tests/model/run.py --fast
   python3 -I tests/model/results_check.py
   ```

**Try breaking it.** In [`Prop01.lean`](Elements/BookI/Prop01.lean), change `Definition15 hA_BCD hC_BCD hB_BCD` to `Definition15 hB_ACE hC_ACE hA_ACE` and run `lake build`. Lean refuses: B is the centre of the other circle, so the radii it gives are the wrong ones.

## Use it

Stoicheia is a Lean library as well as a book, and a Lean project of yours can build on it. Add it to your `lakefile.toml`, pinned to a release tag:

```toml
[[require]]
name = "stoicheia"
git = "https://github.com/jackChallis/stoicheia"
rev = "book-III"
```

In a `lakefile.lean` it is one line: `require stoicheia from git "https://github.com/jackChallis/stoicheia" @ "book-III"`. Your `lean-toolchain` must name the same Lean, `leanprover/lean4:v4.35.0`. There is nothing else to download. In a new project, `lake build` fetches the tag and builds the modules you import; in one that already has a `lake-manifest.json`, run `lake update stoicheia` first, which adds Stoicheia to the manifest and leaves your other dependencies as they are (a bare `lake update` would update them all). The same command moves you to a later tag once you change `rev`. Then import a proposition and use it; here I.20, that any two sides of a triangle are together greater than the third, gives one of its three inequalities:

```lean
import Elements.BookI.Prop20

example {A B C : Elements.Point} (h : Elements.Triangle A B C) :
    ‖B C‖ < ‖B A‖ + ‖A C‖ := (Elements.BookI.Prop20 h).1
```

A proposition is `Elements.Book<book>.Prop<n>`, declared in the module whose name gives its number in two digits (I.1 is `Elements.BookI.Prop1`, in `Elements.BookI.Prop01`), and `import Elements` brings in every book. Its porism is `Prop<n>.porism`, and a companion, a theorem shown beside the proposition (its general form where our statement is narrower, an earlier statement kept for those who cite it, or a theorem that ties one of our definitions to a reading of Euclid's word), is `Prop<n>.<word>`, in the same module. [The table of names](book/names.md) gives each proposition, porism and companion with its Lean name, its module, its page and its certificate. The theorems speak of the points, lines and circles of our foundations, which Lean knows through the axioms of [What Euclid takes for granted](#what-euclid-takes-for-granted) alone, so `#print axioms` on a theorem of yours lists what it rests on. A released name does not change without a deprecated alias for one release, and each release's notes list what changed ([FORMALIZATION](docs/FORMALIZATION.md#names-and-how-they-change), section 2).

## How it's built

| Where | What |
|---|---|
| [`heath/`](heath) | Heath's translation, transcribed from the 1908 scans and checked against the page images |
| [`Elements/Foundations/`](Elements/Foundations) | Postulates, common notions, definitions, tacit rules |
| [`Elements/Figure/`](Elements/Figure) | "Book Zero": small facts every figure needs, proved once |
| [`Elements/BookI/`](Elements/BookI), [`Elements/BookII/`](Elements/BookII), [`Elements/BookIII/`](Elements/BookIII) | One file per proposition; Book II's shared ground, rectangles and squares from Book I, is in [`Rectangles.lean`](Elements/BookII/Rectangles.lean), and Book III's in [`Squares.lean`](Elements/BookIII/Squares.lean), [`Feet.lean`](Elements/BookIII/Feet.lean), [`Circumferences.lean`](Elements/BookIII/Circumferences.lean) and [`MixedAngles.lean`](Elements/BookIII/MixedAngles.lean) |
| [`mishnah/`](mishnah) | The commentary, and each book's introduction (`mishnah/intro/`), shown on its index page |
| [`figures/`](figures) | The figures: the "at a glance" figures in Byrne's colours, and Heath's, redrawn; both carry his letters |
| [`Certificate/`](Certificate) | [`Facts.lean`](Certificate/Facts.lean), which computes the certificate from the proofs, and [`axioms.lock`](Certificate/axioms.lock), the exact statement of every axiom and of every definition the axioms and the propositions are stated in; CI fails if one differs from the lock |
| [`review/`](review) | A review record for each proposition: what its Lean statement covers of Euclid's enunciation, whose argument the proof follows, how it represents his objects, and the commit the reviewer read ([the schema](review/SCHEMA.md)) |
| [`Audit/`](Audit) | Audit lemmas, which no proof imports: each proposition that our rules state or give at once, proved from the rules alone (the former I.2, I.3 and I.23 construction overlaps were retired and their audit lemmas removed with restricted superposition); the former I.7 shortcut, now circular through its own corollary; III.5, which reads "cut" as crossing, proved without citing Diagram-segment 2 or Circle 4, and, since 26 October 2026, without resting on `circle_eq`, for the proved radius comparisons beneath both proofs rest on our radius rule instead; the bridges of [`Crossing.lean`](Audit/Crossing.lean), `CirclesCut.of_meet` and `within_point`, which recover the earlier statements of III.5, III.6, III.11 and III.13, before cutting was read as crossing and contact within asked for a point within; the equal measures of III.24's companion `Prop24.equalCircles` and of III.26, and III.27 whole, proved without the hypotheses our measure of circumferences leaves idle; III.30 by the same measure, without III.28; and, the other way round, Diagram-angle 3 proved from I.13, and Circle 2 and Circle 3 each derived from the other, both now circular, since both rules are proved from III.2, as the [overlap catalogue](docs/reports/overlaps.md) lists |
| [`Staging/`](Staging), [`Staging.lean`](Staging.lean) | Statements that a stage adds or changes, until they move to `Elements/`, each with its proof or with `sorry` where its proof is due; nothing in the edition imports them, so no proof rests on them |
| [`tests/model/`](tests/model) | The model tests: the axioms checked numerically in the ordinary plane, with their seeds, mutations and results, and [`MODEL.md`](tests/model/MODEL.md), the argument law by law |
| [`book/`](book), [`CERTIFICATE.md`](CERTIFICATE.md), [`GRAPH.md`](GRAPH.md) | Generated pages; don't edit by hand |
| [`docs/`](docs) | The [plan](docs/briefs/0001-plan.md) the project started from, the catalogues of what Euclid takes for granted in [Book I](docs/reports/gaps-book-I.md), [Book II](docs/reports/gaps-book-II.md) and [Book III](docs/reports/gaps-book-III.md), the [logs](docs/reports/crew), and notes on [earlier work](docs/reports/0001-prior-art.md) |

A Lean proof needs only the *statements* of the propositions it cites, not their proofs. So once a book's statements are written, its propositions can be proved in any order, and many at once.

## Join in

Books I to III are proved, and Book IV, of figures inscribed in and circumscribed about circles, is next: once its statements are in Lean, pick any 🚧 proposition and prove it. There is plenty to do in [Book I](book/I/index.md), [Book II](book/II/index.md) and [Book III](book/III/index.md) as well: read a page and tell us where it could be clearer, check a quotation against Heath's scans, or improve a figure or a proof. [CONTRIBUTING.md](CONTRIBUTING.md) explains the few house rules.

## How it was made

Stoicheia is built with Claude (Anthropic's AI) working as a crew of agents. A captain plans and merges; first mates prepare each stretch, writing the statements and testing them; sailors prove each proposition, in parallel; bosuns and first mates merge their work and review it for faithfulness to Euclid; artists drew the at-a-glance figures in Byrne's colours; inspectors audited Book I for consistency. From the third voyage OpenAI's Codex joined the crew: Codex sailors proved I.26, I.28, I.30, I.32, all of I.33–I.48 and all of Books II and III, some of them from scratch proofs Claude's first mates had written to test the statements; they drew Euclid's figure for each and wrote the first draft of its mishnah, and Claude's bosuns, first mates and captains reviewed and edited their work. In October 2026 every review record of Books I and II was read again in full by a reader from the family other than that of the original proof: GPT-6 Astra (Codex) for Claude's proofs, Claude Opus 5.5 for Codex's. This cross-family claim is about the original proofs, not every later edit. Some of Codex's proofs also keep parts that Claude wrote, such as a first mate's scratch argument or corollary, or a step a bosun rewrote. Where only Claude had read those parts, GPT-6 Astra has since read the whole record: I.28, I.34, I.36, I.38, I.41, I.42 and I.46 in Book I, and II.6, II.7, II.12 and II.13 in Book II. Each record's `reviewer` names the reader of its latest stamp. The first cross-family sign-off (card 220) wrote `run` lines beginning "card 220"; each of those still in place names the original proof's family and its reader. For those eleven, whose `run` lines begin "card 257" or "card 326", the `run` line also uses only git or record evidence to distinguish later contributions, names their readers, and says when a writer or a cross-family reading remains unrecorded. Early planning also drew on conversations with ChatGPT. The crew's logs are in [docs/reports/crew](docs/reports/crew). In October 2026 Astra, an OpenAI model run in ChatGPT, read the whole work cold and wrote a careful outside review; we are very grateful, and [our response](docs/reports/outside-review-01.md) says what we are doing with it.

Lean's kernel checks every proof, and CI checks that every proof still quotes Heath word for word. Beyond that, three things rest on review rather than on a machine: the assumptions, which are all listed; whether each Lean statement says what Euclid says; and whether the Lean under each of his sentences does what it says. Each page says where either falls short of his. Every quotation in the commentary was checked against the scanned 1908 text, and [What the checks show](#what-the-checks-show) says what each kind of check establishes.

## Standing on shoulders

This project is a love letter to a long line of people who have read Euclid carefully, and it leans on all of them.

- **The text.** Euclid, of course. J. L. Heiberg, whose Greek text Heath translated. Sir Thomas L. Heath, whose 1908 translation and notes are the backbone of every page here. Proclus, whose commentary on Book I is still the first place to look, and Thomas Taylor, who translated it in 1788–89. Robert Simson, whose 1756 *Elements* Heath quotes again and again, and whose added sentence in I.24 our mishnah on that proposition builds on. John Casey, whose 1885 *First Six Books* is lovingly kept on Project Gutenberg, and Oliver Byrne, whose 1847 Euclid in colour is one of the most beautiful books ever printed; our "at a glance" figures borrow his palette and his idea that a picture can carry a proof's meaning before any letters do.
- **Readers' editions today.** David E. Joyce's [online *Elements*](https://mathcs.clarku.edu/~djoyce/elements/elements.html) and Richard Fitzpatrick's Greek–English edition, both wonderful companions.
- **The foundations of geometry.** David Hilbert and Alfred Tarski, who showed how to fill Euclid's gaps, and Robin Hartshorne, whose *Geometry: Euclid and Beyond* explains it all with great clarity. Above all, Jeremy Avigad, Edward Dean and John Mumma, whose System E is the source of all our tacit rules but one.
- **Euclid in proof assistants.** Michael Beeson, Julien Narboux and Freek Wiedijk, whose [*Proof-checking Euclid*](https://arxiv.org/abs/1710.00787) worked through all of Book I in Coq and HOL Light, together with the [GeoCoq](https://github.com/GeoCoq/GeoCoq) team. Logan Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and Xujie Si, whose [LeanEuclid](https://github.com/loganrjmurphy/LeanEuclid) brought System E to Lean. We kept their careful rendering of the rules open beside the paper the whole time, and borrowed their corrections and the combined placement our superposition rule keeps (see [NOTICE](NOTICE)). André Hernández-Espiet and Alex Kontorovich, whose [synthetic_euclid_4](https://github.com/ah1112/synthetic_euclid_4) proves all of Book I in Lean 4 with every diagram step spelled out. Ariel Kellison, Mark Bickford and Robert Constable, whose [*Implementing Euclid's straightedge and compass constructions in type theory*](https://doi.org/10.1007/s10472-018-9603-0) builds Euclid's constructions in the intuitionistic type theory of the Nuprl proof assistant, and from it proves I.2 in its full generality. Tadd Mao, Tianjun Zhong, Dhruva Arekar, Yuming Feng, One An, Jiani Huang, Xujie Si and Ziyang Li, whose [*Does the Proof Prove It That Way?*](https://arxiv.org/abs/2608.15432) asks exactly the question this project cares about: whether a formal proof follows Euclid's own argument.
- **Lean.** Leonardo de Moura, Sebastian Ullrich, the Lean FRO and the whole Lean community. Patrick Massot's [leanblueprint](https://github.com/PatrickMassot/leanblueprint) and the Lean FRO's [Verso](https://github.com/leanprover/verso), by David Thrane Christiansen, showed us mathematics written out in prose beside its Lean, and inspired the way these pages are laid out. Lean's leanchecker, by Kim Morrison and Ullrich, which began as Morrison's [lean4checker](https://github.com/leanprover/lean4checker), and Chris Bailey's [nanoda](https://github.com/ammkrn/nanoda_lib), written apart from Lean, check every proof here again; nanoda reads the export that Henrik Böving's leanexport writes. We are very grateful for all three.
- **The keepers of the books.** The Internet Archive, Google Books and Stanford University Libraries, whose copies of Heath we read from; Cornell University Library, whose scans of Casey are the ones Project Gutenberg's edition was made from; Project Gutenberg and its Distributed Proofreaders, among them Joshua Hutchinson and Keith Edkins, who prepared that Casey, and Richard Tonsing, who revised it; the Perseus Digital Library.
- **The logo.** Raphael's *School of Athens* (1509–1511), in Marie-Lan Nguyen's photograph on Wikimedia Commons. Euclid's slate has become a laptop, and he is drawing I.47. See [assets/CREDITS.md](assets/CREDITS.md).

Full references are in [docs/references.bib](docs/references.bib).

## License

The Lean code and scripts are under the [Apache License 2.0](LICENSE). Our own prose and figures are under [CC BY 4.0](LICENSE-PROSE.md): `mishnah/`, `reading/`, `figures/`, `docs/`, our parts of `assets/`, the README, CONTRIBUTING, and the pages under `book/` apart from Heath's text and the Lean. Heath's 1908 translation and Euclid himself are in the public domain. Anyone may use any of it; we'd love to hear if you do.
