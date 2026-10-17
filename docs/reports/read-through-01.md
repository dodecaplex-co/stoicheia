# Read-through 01: Books I to III

*16 October 2026, at main `5541197`. Books I and II are released; Book III is stated.
What has been done about it since is at the end, under "What was done".*

## Who read what

Five readers went through the pages as a curious visitor would. They covered:
- I.1 to I.24;
- I.25 to I.48;
- Book II;
- Book III, with its figures and definitions;
- the whole site, entered from the README.

A consistency pass compared every surface with every other. Two verifiers tested the 87 axioms against models of the plane. Checkers then tested 170 claims the project makes about itself, in the README, CONTRIBUTING, STYLE, the briefs, NOTICE, CITATION.cff, the generated pages and both release notes. Of those claims, 114 hold, 53 hold in part and 3 do not. The readers and checkers reported 124 findings, gathered here into twelve issues.

## In short

Books I and II are what they say they are:
- every proof is checked by Lean's kernel;
- every proof quotes Heath word for word;
- every Heath quotation has his words and his page;
- the axioms are sound.

What needs work is how the pages talk:
- Book II's commentary repeats itself;
- the certificate tables count in two ways without saying so;
- Book III's pages promise more than they yet have;
- a handful of credits are wrong.

None of this touches a proof.

## The four answers

### 1. Is it all one voice?

**Yes, but its register drifts.** No reader found a page that sounds like a different writer. The same manners run through every book: bold leads, Heath quoted in his words with his page, "we" for the project, Euclid's words for Euclid's things, no em dashes, no comparisons, and a closing modern way that is right. Readers could not tell Codex's drafts of I.26, I.28, I.30 and I.32 from Claude's pages.

The drift is in register. I.1 to I.4 read like light essays. From I.5 on the mishnah turns gradually into a ledger. By I.33 to I.48, and above all in Book II, it reads like one writer filling in a form:
- the same three or four sentences about Lean's shared steps;
- certificate bookkeeping the table already shows;
- labels instead of hooks as leads;
- "we" less than half as often (0.9 per page in Book II against 2.4 in I.1 to I.25; seven of the fourteen never say it).

Book II is the one place a careful reader can hear the second drafter. II.12 and II.13 reuse I.47's certificate sentence almost word for word. Part of the cause is our own STYLE check 19, which asks every mishnah to explain every extra citation.

Book III's hand-written parts (captions, titles, `DefinitionsIII.lean`) match the house voice. Its generated boilerplate does not, because it was written for proved pages. The brief 0004 also has a few asides addressed to the captain.

### 2. Is it consistent?

**Mostly, yes.** It is one project with about two dozen seams, and none of them breaks a proof. The seams cluster where Book I meets Books II and III, and where the generated pages meet the hand-written docs. These are the ones readers will notice first:
- Book III has no lettered figures, though the README promises two figures for every proposition.
- Book III is "Stated" in the README and "Sketched" on its pages.
- Book I's Definition 15 is written "I.15" in Book II's tables, right beside Proposition I.15.
- One table counts postulates through the cited propositions but Common Notions only where named.
- Book I's titles say "line" and "wider" where everything else says "straight line" and "greater".
- Full names at first mention appear on some pages and not others.
- "Tacit assumptions" is used on the pages and "tacit rules" everywhere else.
- "Intersection 5" and "Intersections 5" are different rules, told apart by one letter.
- The lettered figures for I.1 to I.29 are drawn at off-spec stroke widths.
- Captions have grown past "short".
- Heath's vol. 2 is credited nowhere.
- The book-II release notes credit no one.

### 3. Does it do what it says?

**For Books I and II, yes.** All 62 propositions are proved and the kernel checks them. There is:
- no `sorry` outside Book III;
- no axiom outside Foundations;
- no `native_decide` or other bypass.

CI recomputes the certificate and checks that it is fresh, and an edited Heath word fails the fidelity check. The twelve proofs read in full against Heath each follow Euclid's route. Every difference between what Euclid cites and what the Lean cites is explained in its mishnah. The parallel-postulate result is real: 29 propositions avoid Postulate 5, and a hyperbolic model shows that no other rule smuggles it in.

The three claims that fail are these:
- The README and NOTICE say Harvard's library supplied the Heath scans; the copies are Stanford's.
- Book II's scratch proofs were to be retired once Book II was proved, and they are still in the repository.

Most of the partial ones are claims of scope:
- "For every proposition you get…" is not yet true of Book III.
- "Checked line by line" fits Books I and II only.
- "Nothing rests on trust" leaves out the 87 axioms and the faithfulness of each statement, which rest on review.
- The certificate's Common Notions are not counted through the propositions a proof cites.
- The Book II release notes promise "any straight-sided figure" for II.14, which is proved for two triangles.

There are three factual slips on pages:
- II.4 confuses Euclid's "For the same reason" with the interpolated Porism.
- II.11's caption says the cut "can never be drawn exactly".
- Heath's italics are dropped in about 18 quotations.

CI's guard against stray axioms is a regular expression with a hole. Nothing gets through it today, but it can be got past.

### 4. Are the axioms sound?

**Yes.** The 87 axioms are 5 postulates, Definition 15 and 81 tacit rules. All of them are true together in the ordinary plane, including every degenerate case. In that model:
- points are points of the plane, lines are whole lines, and circles have positive radius;
- betweenness is strict, and sides are open half-planes;
- magnitudes are reals of at least 0, and length is distance;
- angles lie in [0, π], and an angle with a repeated point is 0;
- area is the area of the triangle, and ∟ = π/2.

So the axioms are consistent relative to Lean's logic and the reals, and no false axiom stands behind any Book I or Book II certificate.

How we know:
- Two verifiers searched independently, and about 8 million configurations met an axiom's hypotheses with no counterexample.
- A mutation test caught all 15 deliberately weakened axioms, so the search can find a false rule when one exists.
- For this report we also read Postulates 1 to 5, Definitions 10 and 15, superposition, the magnitude laws and the angle and area transfer rules against the model, and each holds.

Four things are worth writing down:
1. Soundness depends on the 17 primitive words and magnitudes staying `opaque`.
2. Definition 10's `¬ Collinear A B C` clause is what keeps Postulate 4 true, and its docstring does not say so.
3. The model is written down nowhere in the repository.
4. Six Book III circumference lemmas rest on the still-unproved statements of III.20 to III.22.

## Checked again for this report

- **Book III's figures.** `figures/III` holds only the 37 `NN-idea.svg` files. `render.py:290` skips a missing lettered figure without a word. `render.py:296-298` prints "the lines under each one are the Lean that carries it out" on every page, including Book III's, where the body is `sorry`.
- **The Heath scans.** The vol. 1 OCR reads "STANFORD UNIVERSITY LIBRARIES" (line 32486). The archive.org record for vol. 2 (`00heibgoog`) says "unknown library". Only `03heibgoog`, a vol. 3, is Harvard's. `NOTICE:59-60`, `README:114` and `references.bib:9` say Harvard, or name vol. 1 alone.
- **II.4's porism.** Heath vol. 1, p. 381 (OCR 27466): "There is also in the Greek text a Porism which is undoubtedly interpolated: 'From this it is manifest that in square areas the parallelograms about the diameter are squares.'" `mishnah/II/04.md:5` calls Euclid's own "For the same reason" that porism.
- **The II.11 caption** reads "(Drawn with 89 and 144, since this cut can never be drawn exactly.)"
- **`facts.json`.**
  - Common Notions are direct only: I.5 shows C.N. 3 and 5.
  - The 29 propositions free of Postulate 5 are I.1 to I.28 and I.31.
  - Postulate 5 is used directly only in I.29, I.44 and II.10.
  - Every axiom listed is a Postulate, a Definition or a Tacit rule.
  - 73 of the 87 axioms are used so far.
- **`check_fidelity.py:93`** matches `^\s*(private\s+|protected\s+)?axiom\s`, and `render.py:233-235` keeps only Postulate*, Definition* and Tacit.* names.
- **Book II's refrains.**
  - "I.4 and I.34" appears in 12 of 14 mishnahs.
  - Proclus "under I.31" appears in 11.
  - `exists_off_line` appears in 10.
  - "Postulate 5 comes in" appears in 16 mishnah files across Books I and II.
  - STYLE check 19 is the rule that asks for these sentences.
- **The book-II release notes** have no "How it was made" and no thanks. They promise "any straight-sided figure".
- **`0002-decisions.md:98`** says scratch-II is "retired when Book II is proved". Its six files are still at HEAD.
- **`CERTIFICATE.md:74`** says "none yet" for Book II.
- **The README's I.1 code block** contains a `/- … -/` comment that is not in `Prop01.lean`.
- **Book II's tables** read "Definitions | I.15", while Book III's read "Def. I.10".

## The issues, in order

### 1. Book III's pages say more than they show

The README promises two figures, a certificate and a mishnah for every proposition, and says every page reads "Euclid's statement, his figure, his proof…". Book III has none of the lettered figures. Proofs that run on Heath's letters (III.8, III.10, and III.33's "as in the first figure") cannot be followed, and nothing on the page says the figure is missing.

The page also tells the reader that "the lines under each one are the Lean that carries it out" above a bare `sorry`, which is never explained. The status reads "Sketched" where the README says "Stated". The front page says words with no Lean partner are "never used in a proof", yet III.16 and III.31 argue with Def. 7.

**Fix now:** these are render.py changes that touch only Book III pages, plus README scope lines. **Later:** draw the 37 figures.

### 2. Book II repeats its Lean bookkeeping

Read in order, Book II tells the visitor the same few things on almost every page:
- a rectangle drawn is the rectangle contained, by I.4 and I.34;
- parallels meet, as Proclus says under I.31;
- a point with no letter picks the side for the square.

The prose also restates the certificate postulate by postulate. I.47's paragraph on Proclus, the high point of Book I, ends in that bookkeeping. II.11, the golden section, never says why it matters, or what its own title, "extreme and mean ratio", means.

The cause is partly STYLE check 19. **Fix:** say each shared step once, in a short note on the Book II index, and give the freed words to Euclid and Heath. This is held by Decision 1.

### 3. The certificate tables count in two ways

Postulates, definitions and tacit rules include everything the cited propositions bring in. Common Notions count only those named in the proof itself. The tacit list is headed "The N things Euclid takes for granted here", yet it lists rules this proof never uses:
- superposition appears on every page after I.8;
- I.29 shows 51 rules where its own steps use 16.

CERTIFICATE.md explains the Common Notions; no proposition page does. **Fix:** clearer labels and a key under each table. Splitting the tacit list is for Jack.

### 4. Credits and provenance

Some credits are wrong:
- **Heath scans.** They are Stanford's copies, not Harvard's.
- **Heath vol. 2.** It is the source of Book III and is credited nowhere.
- **Taylor's Proclus.** It is dated 1792; it appeared in 1788–89.
- **Verso.** The tagline quoted in prior-art and `references.bib` is not Verso's own.
- **Heiberg.** Books I–XIII ran 1883–1886, not 1883–1885.
- **The fresco.** CREDITS.md gives the full fresco the wrong Commons tag.

**Fix now.**

### 5. Two factual slips in Book II

- **II.4.** The mishnah treats Euclid's "For the same reason" as the interpolated Porism; Heath's p. 381 bears this out.
- **II.11.** The caption says the cut "can never be drawn exactly". II.11 draws it exactly; what is meant is that no two whole numbers give the ratio.

**Fix:** held by Decision 1, since both are on released pages.

A later check found a third, the same kind of slip. Eight Book II mishnahs say that Heath reports Proclus arguing, under I.31, that "a straight line meeting one of two parallels meets the other". What Heath reports under I.31 is that Proclus draws from I.30 that only one parallel can be drawn through a point; the meeting lemma is Proclus's own, argued from distances, and Heath gives it in his note on Postulate 5 (vol. 1, p. 207). Inspection 2 had already corrected this on seven Book I pages. It too waits on Decision 1, and the Book II index note (issue 2) should use I.37's corrected form.

### 6. The release notes

**book-II** credits no one, though Codex sailors proved every proposition and Claude's crew reviewed them. It also overstates two things:
- "any straight-sided figure" for II.14, which is proved for two triangles;
- "every proposition stated as Euclid states it", though II.1 is stated for two points of section.

**book-I's** "Twenty-nine" reads like an off-by-one error until the reader is told the 29th is I.31. Drafts are in the discussion list, for Jack's OK.

### 7. The README claims a little more than is true

- The tagline's "line by line" fits Books I and II only.
- "Nothing rests on trust" leaves out the assumptions and the statements.
- "Which common notions" omits that they are counted only where named.
- The circumference is said to be measured by "the angle", where the definition takes it twice.
- "No coordinates" sits beside a modern way on every page that uses them.
- "Artists drew the figures" and "inspectors audit the whole" are each half true.
- The Codex credit leaves out the scratch proofs Claude's first mates wrote first.
- The I.1 code block contains a comment that is not in the file.

**Fix now.**

### 8. The axiom guard in CI is a regex

An axiom written after a same-line docstring in a proposition file passes `check_fidelity`. `render.py` would then leave it off every page. Nothing like this exists today. **Fix now:** check from the Lean environment instead, and show any unrecognised axiom under "Other".

Two more ways round CI's house rules, found by a later check, are not in the repository either: Lean 4.35's `decide +native` does what `native_decide` does without that word, and adds an axiom without the keyword; and `set_option debug.skipKernelTC true` with a `run_cmd` that calls `addDecl` lets an ill-typed proof in with no axiom at all. CI's page check also used `git diff`, which does not see a page that was never committed.

### 9. Heath's italics dropped

About 18 quotations drop Heath's italics, confirmed on the page images, including the README's *will*. STYLE forbids adding italics but not dropping them. **Fix:** STYLE and `gaps-book-I.md` now; the mishnahs after Decision 1.

### 10. Decisions not carried out, or not recorded

- scratch-II has not been retired.
- Book II was released without `gaps-book-II.md`, and 0002 does not record the change.
- 0002 still says "Lean needs" where the pages say "Lean cites".
- The negative tests pass when rerun but were never logged.
- The voyage logs drop the plan's "axioms added, gaps found" lines.

**Fix now.**

### 11. Naming seams across books

- Definition 15 is "Def. I.15", "I.15" or "Definition I.15" depending on the page.
- Book III is "stated" in one place and "sketched" in another.
- Book I's titles use modern words.
- Full names at first mention are uneven.
- "Tacit assumptions" is used against "tacit rules".
- "Intersection 5" and "Intersections 5" are told apart by one letter.
- The figures for I.1 to I.29 use off-spec stroke widths.
- Captions in Books II and III run to 69 words.

**Fix:** write the rules into STYLE now; the page fixes after Decision 1.

### 12. A visitor is never told the house words

System E, Book Zero, mishnah, `sorry`, Q. E. D., Euclid's "diameter" and "applied" are explained only in the README, or nowhere. The Book II index has no introduction, though the book-II release notes already contain a good one. **Fix:** after Decision 1.

## One decision comes first

Books I and II "render byte for byte as tagged" (0002, 0004), and the book-II release says Book I is unchanged. Most of the readers' fixes change released pages:
- the II.4 and II.11 slips;
- the Book II refrains;
- Heath's italics;
- the glosses;
- the table labels.

We suggest one deliberate reader's-edition pass on main, recorded in 0002, with optional tags `book-I.1` and `book-II.1`. The original tags would keep the text as released. Until Jack decides, the fixes marked "after decision 1" wait.

## Fixes a bosun can make now

None of these touches a released page, a statement or an axiom.

1. **`render.py`, Book III only.**
   - When the lettered figure is missing, print a placeholder with a link to Heath's scan leaf.
   - Status: "🚧 Stated: … the proof is to come".
   - On stated pages, say the Lean is still to be written and explain `sorry`.
   - Use "stated" in the index legend and GRAPH.md.
   - Show the bracket note for III.12.
   - Front page: "never used in a Lean proof"; give reasons for the empty Def. 7 and Def. 10 cells; gloss the touching words; say Def. 9 is measured twice.
2. **`render.py`:** print "none", not "none yet", for a finished book.
3. **README.**
   - Scope Book III's lines, explain I.31 in the "29", and note II.1 and II.14.
   - "Nothing rests on trust but the assumptions, and those are all listed"; "common notions it names"; the circumference "twice".
   - Reword the no-coordinates sentence and replace the invented I.1 comment with `-- …`.
   - Restore *will*; drop "own" from "Euclid's own title".
   - Rework the crew paragraph: define the ranks first, scope the artists and inspectors, and credit the scratch proofs. Add the same to voyage-05.
   - Write "David Hilbert and Alfred Tarski".
4. **Provenance and credits.**
   - README, NOTICE and `references.bib`: Stanford copies, both volumes.
   - Taylor's Proclus 1788–89; Heiberg 1883–1886; Verso's own title.
   - The CREDITS.md tag.
   - The vol. 2 leaf offset in prior-art.
   - Reword prior-art's "two things we noticed" to credit LeanEuclid for rule 4.
5. **Licences:** one list in README, NOTICE and LICENSE-PROSE. In CITATION.cff, give both licences, add a version, and add the Kellison reference.
6. **Retire scratch-II** as voyage 4 did. Remove it at HEAD, point its links at `19279eb`, and add a 0002 bullet.
7. **0002:** "Lean cites". Record that the Book II gap catalogue follows the book.
8. **0003 and 0004.**
   - The `sq_pos` note; split the `lt_semicircle` row.
   - Reword the III.24 sentence.
   - "`rect` chooses one area".
   - Turn the captain asides into design statements.
9. **Comments that are not rendered:** the three `DefinitionsIII.lean` slips, and the em dash in `Transfer.lean`'s module comment.
10. **Book III captions:** III.17 (outer circle colour, length), III.10, III.1, III.22 and III.37.
11. **`check_fidelity.py`.**
    - Check axiom modules from the environment; check that the primitives stay opaque and that the axiom count is 87.
    - In `render.py`, show unrecognised axioms under "Other".
12. **Logs:** record the negative tests, or make them a CI job. Add "No axiom added; gaps: …" to voyages 3 to 5.
13. **Write down the model** in a `Words.lean` docstring or in CERTIFICATE.md's source. Add the sentence on why Definition 10 needs `¬ Collinear A B C`.
14. **`gaps-book-I.md`.**
    - Add the page and the italic to the circles quotation.
    - Give full names at first mention.
    - Fill the seven entries that name nothing, and replace `PropN.something`.
    - Restore Heath's italics.
15. **STYLE.**
    - Keep Heath's italics, and add check 12b.
    - A person's full name at first mention on each page.
    - Book III's bracket forms.
    - "Def. I.15" in tables and "Definition I.15" in prose.
    - Stroke widths and angle marks; captions of about 40 words at most.

## Fixes that wait on Decision 1

1. **II.4:** correct the porism sentence. **II.11:** correct the caption and trim it.
2. **Book II's shared steps:** one note on the Book II index, with the release notes' introduction above it. Then cut the refrains and the certificate-accounting sentences, and write "the Lean cites" for "the certificate cites".
3. **Heath's italics** in the mishnahs, and "vol. 1" in II.3, II.8 and II.9.
4. **Small page fixes:**
   - the I.23 dangling note;
   - `_ =quadArea` in II.4's Lean;
   - the II.5 comment;
   - the I.46 docstring wrap;
   - the I.1 C.N. 5 sentence;
   - I.17, I.19, I.39, I.31, I.48 and I.8 wording;
   - the Riemann gloss moved to I.12;
   - the II.1, II.5, II.7, II.8 and II.10 sentences;
   - Heath's title and the *Elements* in italics.
5. **Table and navigation labels:**
   - "Tacit rules";
   - "The N tacit rules beneath this proof…", with the rules used directly marked;
   - a key under each table;
   - the `/- -/` note above the Lean;
   - links across books;
   - titles for I.48 and III.37;
   - "Def. I.15".
6. **Glosses:** what each page holds, on the Book I index; System E in I.1; "diameter"; plain words for "associative" and "transitive"; "straight line" in the tacit docstrings.

## For Jack to decide

1. Decision 1, above.
2. **The release notes:** approve the drafted book-II "How it was made" and thanks, the II.14 and II.1 scope, and book-I's "twenty-nine" and "used directly".
3. **The tagline:** keep "checked line by line", or use "sentence by sentence"?
4. **Certificate meaning:** make Common Notions transitive, or keep them direct and say so on every page? Split the tacit list?
5. **STYLE check 19:** let a generated line under the table explain which shared step brings in which citation, so the mishnah need not?
6. **Book II's register:** rewrite II.1 to II.8 toward the house voice, and rebuild II.11 on Heath's p. 403?
7. **Book III statements** that depart from the enunciation:
   - III.1 takes a centre by hypothesis;
   - III.9 drops "within";
   - III.16 and III.31 leave out their mixed angles;
   - III.25 is handed the circle;
   - III.12 is bracketed.

   Should each page show a short "How Lean says it" note before its mishnah lands? Should Book III gain the rule that a circle has a centre?
8. **III.20 to III.22** carry six circumference lemmas: prove them first, or review their statements first.
9. **Stated pages** print Euclid's proof twice: fold the comment lines until the proof lands?
10. **Book I** titles in Euclid's words, and the front page's Defs. 17 and 18.
11. **Ground files:** one naming and namespace scheme.
12. **When to draw Book III's lettered figures**, and when to write `gaps-book-II.md`.
13. **Only Jack can confirm** the ChatGPT sentence, and whether LeanEuclid's area rules were adapted, which NOTICE would then name.

## What holds

These claims were all verified:
- All 62 proofs build. They quote Heath exactly, and CI keeps the certificate fresh.
- No axiom is hidden.
- The Common Notions are theorems.
- Definition 15 is the only definition that is an axiom.
- Book II's and Book III's words are defined, not assumed.
- Superposition is used directly only in I.4 and I.8.
- Book Zero cites no proposition.
- The System E labels match the paper.
- Every one of 3,346 tacit-rule links points at its axiom.
- Every Heath quotation has his words and page.
- Every figure's letters are Heath's.
- Book I is unchanged since its tag.
- "Try breaking it" breaks as promised.
- The Lincoln quotation is exact.
- The people credited are credited correctly, apart from the dates and libraries above.

The care is visible on every page. What remains is mostly a matter of saying things once, and saying what is not yet done.

## What was done

*16 October 2026, after the further reading and the Book II gap catalogue were merged.*

**The fifteen fixes that could be made now were all made**, in the commit "Read-through of Books I–III: fixes". Books I and II render as at their tags but for the further reading and the Book II index's link to its gap catalogue, which came with the merge; Book III's pages, `CERTIFICATE.md`, `GRAPH.md` and the docs carry the rest. Where a fix was carried out differently from the list above, this is how:

- **1.** A proposition with more than one figure in Heath (III.25, III.33, III.35, III.36) names every leaf. The front page's new lead, "never used in a Lean proof", is Book III's alone; Books I and II keep theirs.
- **3.** The no-coordinates sentence reads: "The proofs use no coordinates, real numbers or complex numbers; only the last paragraph of each commentary, 'The modern way', reaches for them." The README no longer credits HathiTrust, which we did not use.
- **4.** The vol. 2 scan is Stanford's copy too: its last leaf carries the Stanford University Libraries stamp, though the archive.org record says "unknown library". Taylor's Proclus in `references.bib` is the 1791–92 second edition; Verso's title is its own, "Verso: An Authoring Tool for Lean".
- **5.** The one list of what CC BY 4.0 covers includes `reading/`, the further reading, which arrived with the merge.
- **7.** `gaps-book-II.md` has since been written, so 0002 records that Book II's catalogue followed its book, and 0003's "Later" item says it now exists.
- **10.** III.10's caption now ends "cross only at the centre". III.17's calls its translucent arc "the outer circle" and uses Euclid's word "perpendicular" to come in at about 45 words.
- **11.** `Certificate/Facts.lean` writes `axiom_modules` (every axiom the project declares, and every axiom a proposition rests on, with its module) and `opaque` to `facts.json`. `check_fidelity.py` fails if any proposition rests on an axiom outside `Elements/Foundations/` (Lean's `propext`, `Classical.choice` and `Quot.sound` aside), if any axiom is declared elsewhere in `Elements`, if the count is not 87, or if any of the 17 primitives stops being `opaque`. With the later check above, it also refuses `decide +native`, `set_option debug.…`, `run_cmd`, `run_elab`, `elab`, `macro`, `implemented_by`, `extern` and `unsafe` in the Lean with its comments taken out, and the source check for `axiom` now reads past a docstring on the same line. CI's page check is `git status --porcelain`, which sees new and deleted pages. Replaying the build with lean4checker, a further guard the later check suggested, is not done.
- **12.** The negative tests are a CI job, `scripts/negative_tests.py`: an edited Heath word, the README's wrong radii in I.1, and, in I.16, Postulate 5, a planted `Tacit.Euclidean` rule and an axiom after a same-line docstring. All were caught when it was first run. Voyage 5's line points at `gaps-book-II.md`, which now exists.
- **13.** The model is a section of `Words.lean`'s module docstring, "The plane they describe".
- **14.** The seven entries now name `CommonNotion4` (I.4), `between_cut` (I.11), `Prop13.cases` (I.13), `Triangle.bac` and `Triangle.cab` (I.17), `Prop3` (I.26), I.31's hypothesis `¬ Collinear B C A`, and `line_unique`, `Parallel.not_onLine` and `same_side_trans` (I.45). Full names at first mention also reach J. L. Heiberg, Bernhard Riemann, Augustus De Morgan and Paul Tannery, and Sir Thomas L. Heath.
- **15.** Check 12b reads the italic flags in the scan's ABBYY file. Subject strokes are 2.4 to 2.6, as the figures of I.30 to II.14 draw them.

**The fixes that wait on Decision 1 were made once it was taken** (0002, "Books I and II in one voice"): most in the pass that put Books I and II in one voice, the rest in "The held reader's-edition fixes, in the common voice". Where one was carried out differently from the list above, this is how:

- **1.** II.4 tells "For the same reason" as Euclid's own and the Porism, "undoubtedly interpolated", as a separate statement (vol. 1, p. 381). II.11's caption ends "(Drawn with 89 and 144: no two whole numbers make this cut exactly.)".
- **2.** Each book's shared steps are told once, in its introduction (`mishnah/intro/<book>.md`), set above the table on its index page, and the line "Brought in by shared steps" under each page's table names those a proof calls on. No page of Books I and II now says that Heath reports the meeting lemma under I.31: Book I's introduction credits it to Proclus' attempt on Postulate 5 (vol. 1, p. 207), beside his inference under I.31 that the parallel is unique (p. 316), and the II.1 entry of `gaps-book-II.md` now says the same.
- **4.** I.8 glosses "the vertical angles" as the angles at the vertices A and D; the Riemann gloss stands in I.12, and I.16 points to it.
- **5.** "Def. I.15" is written so in the tables of Books II and III and in the certificate's, as the row "Euclid cites" already writes "Def. I.10" on III.1; Book I's tables keep "15", as Heath's own brackets there have it.
- **6.** "Diameter" is glossed at I.34, the first page that says it; I.33's modern way says "diagonals". The tacit files' own prose says "straight line", and the laws of magnitude are in plain words.
