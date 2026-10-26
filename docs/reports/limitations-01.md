# Limitations review 01: Books I to III

*26 October 2026. Read at main `41dc2a0ae729f19b56c93292fdea7a392e89d26f` by Claude Opus 5.5, as the limitations reviewer of Books I to III. The reviewer wrote, prompted and edited none of the records, pages, catalogues or checks judged here.*

## What B4 asks

B4 is in [ACCEPTANCE](../ACCEPTANCE.md), under "For each book" (`ACCEPTANCE.md:149`). It passes when "The remaining limitations are deliberate, few and stated plainly where they occur: the overlaps of III.2's kind, and any allowed below, where none is now."

The table of the limitations allowed names none (`ACCEPTANCE.md:164`–`165`). So the only limitations B4 can admit are overlaps, each declared in its record and in [the overlap catalogue](overlaps.md). This review also holds every other departure a record declares to the same test: a changed route, `hypothesis-dropped`, or a representation tag. Is it recorded as a choice? Does the page say it plainly, without contradicting the record, facts.json or the catalogues?

## How it was read

`git log -1 --format=%H` gave the commit above.

These were read whole first:

- ACCEPTANCE;
- [FORMALIZATION](../FORMALIZATION.md), sections 2, 5, 8 and 9;
- [review/SCHEMA.md](../../review/SCHEMA.md) and `review/terms.toml`;
- the overlap catalogue;
- the gap catalogues for [Book I](gaps-book-I.md), [Book II](gaps-book-II.md) and [Book III](gaps-book-III.md);
- the [routes report for Book III](routes-book-III.md): its summary, its sections on #125 to #131 and its addenda;
- the [decision of 22 October 2026 on the calls of III.1](../decisions/2026-10-22-iii1-calls-dropped.md);
- the [decisions page](../briefs/0002-decisions.md), where it bears on III.24's tags;
- the briefs for the three books, and briefs [0006](../briefs/0006-statements.md), [0008](../briefs/0008-centre.md), [0011](../briefs/0011-mixed-angles.md) and [0013](../briefs/0013-figures.md), where the records cite them.

**The census.** A script, kept outside the repository, read each of the 99 records with Python's tomllib. From each it took:

- the scope and the route;
- the representation tags;
- the `[overlap]`, with its kind and rules;
- any `[coverage]`;
- the kind of every passage.

From facts.json it took the status of each proposition, and of each porism and companion attached to it. From each committed page it took the line numbers of:

- the line under the enunciation;
- the Statement, Argument, Representation and Overlap rows;
- every passage led "Argued another way" or "Left in Euclid's words".

The script listed every record that declares a departure, and every record that declares none. Each record it listed was then read by hand, beside its page.

**Three further reads.**

1. **Statements.** A second script printed Heath's enunciation beside the Lean statement of each entry at risk, and the two were compared clause by clause. The entries were:
   - Book I: I.4, I.5, I.7, I.13, I.15 and its porism, I.24, I.26, I.32, I.34–I.36, I.40 with its three companions, I.44, I.45 with `Prop45.outline` and the definition of `Figures.Outline`, I.47 with `Prop47.general`, and I.48;
   - Book II: II.13, and II.14 with `Prop14.outline` and `Prop14.outline_side`;
   - Book III: III.1 and its porism, III.3, III.7, III.8, and III.11–III.37 with all their companions.
2. **Words that mark a limitation.** The record notes and every mishnah were searched for "not proved", "left out", "leaves out", "assumed", "restricted", "excludes", "not stated", "not covered", "formalised" and similar words. Each hit was read in its paragraph.
3. **The pages.** A third script called `scripts/render.py`'s own functions in memory and wrote nothing. All 99 pages, the three book indexes and CERTIFICATE.md came out byte for byte as committed. So each page's top line and field table are exactly what its record gives.

`python3 scripts/check_fidelity.py` and `python3 scripts/heath.py` both passed at this commit, and the tree was unchanged afterwards.

**What could not be checked.**

- No `lake build`, kernel replay, `check_style.py`, `check_links.py` or `check_acceptance.py` was run. The last of these writes its report, and this review changes no file.
- GitHub was not consulted. So the state of the `blocks-release` issue for `Staging/Routes/`, and of open pull request #505, is not known here.
- Statements outside the list above were read through their records and pages, not clause by clause.
- The drafts in `Staging/Routes/` were read only where a page's claim bears on them.
- Heath's text was not compared with the scans.

## The census

facts.json holds 140 entries for Books I to III: 99 propositions, three porisms and 38 companions. All are "proved". Every record has scope `full`. None is restricted or partial, no route is `alternative`, and no record has an `unformalized` passage or a `[coverage]` clause map. What remains declared is set out below.

### Book I

| Proposition | Departure | Where the page states it | What makes it deliberate | Judgement |
|---|---|---|---|---|
| I.5 | `hypothesis-dropped`: the statement asks only that AB equal AC, so it covers equilateral triangles too | `book/I/05.md:94` (Statement), `:96` (Representation) | FORMALIZATION, section 2: a statement that leaves out a hypothesis, and so claims more, is full and carries this tag. The record's note gives the reason. | Deliberate, plain. It claims more, so it limits nothing. |
| I.45 | `figure-with-dissection`, for the older companions only. The main theorem takes two triangles unchecked. | `book/I/45.md:60`, `:62` | Brief 0013; brief 0006, stage 2; ACCEPTANCE, B4 (#116) | Deliberate, plain. Full through `Prop45.outline`, for a figure given by its outline alone, so no limitation remains. |
| I.13, in I.47 | A catalogue row only. Metric 5 (`angle_le_two_right`) supplies, inside `Prop47.within`, the upper bound on an angle that I.13 gives. | `book/I/47.md:154` (the Lean), `:436` (the rule, "(used here)"); not at `:73` | `overlaps.md:34`; ACCEPTANCE, B2 (`ACCEPTANCE.md:147`), under which no record reads such a row | Deliberate. Stated only as a rule used (finding 5). |

**Counts for Book I.** No limitation of scope, and no overlap that a record declares. There is one catalogue row on a rule's use, which B2 leaves out of the count. There is one `hypothesis-dropped`, one representation tag kept for older companions, and no changed route.

**The rest.** The other 46 propositions declare nothing, and their pages carry no sentence saying that something of Euclid's is left out. I.40, which Heath prints in brackets, is stated in full with its three companions, and its route is Euclid's.

### Book II

| Proposition | Departure | Where the page states it | What makes it deliberate | Judgement |
|---|---|---|---|---|
| II.1 | `hypothesis-dropped`, in the companions: the straight line A may be nothing | `book/II/01.md:58`, `:60` | [Book II's brief](../briefs/book-II.md), table of exceptions (line 118) | Deliberate, plain. |
| II.13 | `hypothesis-dropped`: acute angles at B and C, nothing asked of A | `book/II/13.md:54`, `:56` | Book II's brief, lines 87–89; the gap catalogue, II.13 | Deliberate, plain. The page also says that the scholiast's wider reading is not stated. |
| II.14 | `side-not-square`, for the main theorem and the forms that return a side; `figure-with-dissection`, for the older companions | `book/II/14.md:74`, `:76` | Book II's brief, lines 110–119; brief 0013 | Deliberate, plain. Full through `Prop14.outline` and `Prop14.outline_side`. |

**Counts for Book II.** No limitation of scope and no overlap. There are two `hypothesis-dropped`, two representation tags on II.14, and no changed route.

**The rest.** The other 11 propositions declare nothing, and their pages carry no sentence saying that something of Euclid's is left out.

### Book III

The departures of the kinds B4 names:

| Proposition | Departure | Where the page states it | What makes it deliberate | Judgement |
|---|---|---|---|---|
| III.1 | Overlap, a step. `exists_centre` supplies the centre for the proof that D is within the circle, and the supposed centre G of the reductio. | `book/III/01.md:13`, `:76`; mishnah `:442` | Brief 0008; the owner's decision of 18 October 2026 (`overlaps.md:5`–`7`); `overlaps.md:35` | Deliberate, plain. The catalogue's row names only one of the two steps (finding 6). |
| III.2 | Route modified, one step: the centre D comes from `exists_centre`, where Heath's reference is III.1 | `book/III/02.md:13`, `:71`, `:79` | Decision of 22 October 2026 on the calls of III.1 | Deliberate, plain. |
| III.4 | Route modified, one step: the same, for the centre F | `book/III/04.md:13`, `:61`, `:68` | The same decision | Deliberate, plain. |
| III.5 | Overlap, gives it at once: `circle_eq` (Diagram-segment 2), with Generalities 4 | `book/III/05.md:13`, `:56`; mishnah `:159` | Brief 0008, section 7; `overlaps.md:36` | Deliberate. Plain in the top line; dense in the row (finding 3). |
| III.6 | Overlap, gives it at once: `circle_eq`, with Generalities 3 and 4 | `book/III/06.md:13`, `:57` | Brief 0008, section 7; `overlaps.md:37` | Deliberate. The row names rules without saying what they say (finding 3). |
| III.8 | Route modified, two steps: the centre M comes from the rule; the last step uses I.24 at M where neither order reaches | `book/III/08.md:13`, `:121`, `:129`, `:147` | Routes report on III.8, its addendum and its correction of 23 October; decision of 22 October 2026 | Deliberate, plain. |
| III.9 | `hypothesis-dropped`: Euclid's "within" is left out | `book/III/09.md:66`, `:68`; mishnah `:342` | Gap catalogue, III.9; [brief 0004](../briefs/0004-book-III.md), table of exceptions | Deliberate, plain. |
| III.10 | `hypothesis-dropped`, for circles that only meet. Route modified, one step: the last step uses `circle_eq` in place of III.5. | `book/III/10.md:13`, `:56`–`58`, `:72` | Brief 0008, section 7; brief 0004, note of 19 October 2026 | Deliberate, plain. |
| III.16 | Route modified, two steps: the angle clauses are argued directly, not by reductio | `book/III/16.md:13`, `:85`, `:103`, `:104` | Brief 0011; brief 0004, note of 19 October 2026 | Deliberate, plain. |
| III.17 | Route modified, one step: the centre E comes from the rule | `book/III/17.md:13`, `:75`, `:82` | Decision of 22 October 2026 | Deliberate, plain. |
| III.21 | Route modified, one step: Simson's completion for the semicircle and the less segment | `book/III/21.md:13`, `:55`, `:65` | Heath's preference (vol. 2, p. 49), quoted in the mishnah; routes report, #129 | Deliberate, plain. |
| III.24 | Route modified, three steps: the coincidence is argued point by point, in place of Euclid's reductio, and III.10 is not needed | `book/III/24.md:13`, `:57`, `:68`–`70` | Brief 0006, stage 3, "Placement" and "III.24 restated" | Deliberate, plain. |
| III.26 | Route modified, two steps: Heath's separate cases for the right and obtuse angles; the remainders' congruence by III.24 | `book/III/26.md:13`, `:65`, `:73`, `:77` | Heath, vol. 2, p. 57; brief 0006, stage 3; routes report, #129 | Deliberate, plain. |
| III.27 | Route modified, one step: the obtuse case by the remainders and III.22; the right case read off the measure | `book/III/27.md:13`, `:65`, `:77` | Routes report, III.27 and its addendum | Deliberate, plain. |
| III.28 | Route modified, two steps: the case of diameters; the greater circumferences' congruence by III.24 | `book/III/28.md:13`, `:59`, `:68`, `:71` | Gap catalogue, III.28 (Heath, vol. 2, p. 60); brief 0006, stage 3 | Deliberate, plain. |
| III.29 | Route modified, two steps: the case of semicircles, and the greater circumferences by the remainders | `book/III/29.md:13`, `:53`, `:62`, `:63` | Gap catalogue, III.29 (Heath, vol. 2, p. 61) | Deliberate, plain. |

The representation readings, by tag:

| Tag | Records | Where the pages state it | What makes it deliberate | Judgement |
|---|---|---|---|---|
| `touching-whole-circles` | III.6, III.11, III.12, III.13 | `book/III/06.md:56`; `book/III/11.md:58` and mishnah `:237`–`239`; `book/III/12.md:64`; `book/III/13.md:74` | Brief 0004, "Touching, for circles" and its notes of 19 October; brief 0008, section 7; Todhunter's reading, as Heath reports it (vol. 2, p. 3) | Deliberate, plain. III.11's mishnah says the agreement with Heath's reading is not formalised, though a staged file proves it (finding 4). |
| `angle-measure` | III.24–III.30 | The line under each enunciation (`:13`), and each Representation row | Brief 0004, "Circumferences" and its note of 19 October; brief 0006, stage 3 | Deliberate and plain for III.26–III.30. The badge stands beside the main theorems of III.24 and III.25, which name no measure (finding 1). |
| `mixed-angles-local` | III.16, III.31 | `book/III/16.md:86`, `book/III/31.md:96` | Brief 0011; [decision of 25 October 2026](../decisions/2026-10-25-mixed-angles-homes.md) | Deliberate, plain. |
| `segment-with-circle` | III.23, III.24, III.25, III.30, III.33, III.34 | The Representation rows: `book/III/23.md:46`, `24.md:58`, `25.md:88`, `30.md:58`, `33.md:130`, `34.md:52` | Brief 0006, stage 3 | Deliberate, plain. |
| `redundant-hypothesis` | III.24, III.27 | `book/III/24.md:58`; `book/III/27.md:64`, `:66` | FORMALIZATION, section 5 | Deliberate, plain. |

**Counts for Book III.**

- No limitation of scope.
- Three overlaps: III.1's is a step; III.5's and III.6's are given at once.
- Twelve changed routes, made up of nineteen steps argued another way. Four of those steps only take a centre from the rule where Heath's reference is III.1 (in III.2, III.4, III.8 and III.17).
- Two `hypothesis-dropped`: III.9 and III.10.
- 21 representation tags, spread over 16 records.

**Few?** Three limitations, all overlaps of III.2's kind, is few. The changed routes are departures of argument, not of scope, and each step is labelled where it happens.

**The rest.** 21 propositions declare none of the kinds B4 names: III.3, III.7, III.11–III.15, III.18–III.20, III.22, III.23, III.25 and III.30–III.37. Nine of these carry a representation tag (III.11–III.13, III.23, III.25, III.30, III.31, III.33 and III.34). The statements spot-checked among them say what Euclid's enunciations say, read in their representations. Four restrictions might look like limitations, and each matches what Euclid's words presuppose; the pages say so:

- III.20's centre on A's side of BC;
- III.26's and III.27's centres on the side where their angles stand on BC;
- III.7's point F taken on ED;
- III.8's convention that a point of contact lies on neither circumference.

**Work still staged.** Euclid's own arguments for III.21 and III.26 are staged in `Staging/Routes/`. So are three new statements or definitions: III.20 for an angle at the centre of any size, Definition III.3 read at the point of contact, and the angle of contact after III.18. All await the owner's approval (routes report, "For the owner"). The committed acceptance report, at `b46efb938dd3`, fails P10 for III.18, III.20, III.21 and III.26 on account of them.

If they land, III.21's and III.26's routes become Euclid's, and III.11's mishnah changes. The rows above for III.20, III.21, III.26 and the touching tags should then be read again.

## Findings

Each finding is graded by [WORKFLOW](../WORKFLOW.md), section 9.

### 1. Material: the measure's badge stands beside III.24 and III.25, whose main theorems name no measure

**What the pages say.**

- `book/III/24.md:13` reads "proved, as Euclid states it, in our measure of circumferences · Euclid's argument, with three steps changed".
- `CERTIFICATE.md:170` marks III.24 "whole†".
- But the Representation row on the same page, `book/III/24.md:58`, says: "The main theorem says nothing of a measure."
- III.25 has the same badge at `book/III/25.md:13` and the same † at `CERTIFICATE.md:173`. Its Representation row, `book/III/25.md:88`, gives the measure to one companion only: "`Prop25.kind` also compares the arc's circumference with two right angles".

**What facts.json says.** The statements of III.24 and III.25 name none of `circumference`, `standing` or `Arc.measure`. The statements of III.26–III.30 each name one of them.

**What was decided.** On 19 October 2026 the decisions page (`docs/briefs/0002-decisions.md:1796`–`1799`) left `angle-measure` off III.24, because "that tag's badge would put "in our measure of circumferences" beside the main theorem, which says nothing of a measure". It allowed the tag back only "if the badge is first kept to statements that use the measure."

The tag came back the same day, in commit `d0508d6c1`. But representation_badge (`scripts/render.py:990`) still gives the badge to every record that carries the tag. Yet `review/terms.toml:12`–`13` reserves a badge for "A tag that changes how a whole statement is read".

**Why it matters.** The scope line tells a reader that III.24's equal segments are read in a measure with no radius in it. Stage 3 removed exactly that reading, when III.24 came to conclude that the segments coincide. This is an unsupported claim about a representation, on the very page where it stands.

**Fix.** Keep the tags: the schema asks for every term that applies. Keep the badge to statements that use the measure, as the decision asks:

- In `scripts/render.py`, let representation_badge take the proposition's facts.json entry.
- Have its two callers pass that entry: in_lean_line (`:1013`) and the certificate (`:2321`).
- Give the `angle-measure` badge only when that entry's `statement` names `circumference`, `standing` or `Arc.measure`.

After regeneration, III.24 and III.25 read "✅ proved, as Euclid states it" and lose their †; III.26–III.30 keep both. No record changes. This is a change to `render.py`, and the pages, the indexes and CERTIFICATE.md are regenerated with it.

### 2. Material: the README overstates the overlap audit

`README.md:90` says: "Each current axiom overlap in the [catalogue](overlaps.md) is checked: the proposition is proved from the rules named, with the axioms Lean reports pinned."

But the catalogue's current table (`docs/reports/overlaps.md:34`–`35`) gives "None" as the audit lemma for two of its four rows: I.13's upper bound in I.47, and III.1's centre. A rule that only supplies a step cannot give its proposition on its own, and `Audit/` proves neither from its rule. `Audit/Centre.lean` pins only the type and axioms of III.1's construction. `README.md:157` gets this right: "each proposition that our rules state or give at once".

**Fix.** Replace that first sentence of `README.md:90` with:

> "Each current axiom overlap in the [catalogue](overlaps.md) whose rules state the proposition or give it at once is checked: the proposition is proved from the rules named, with the axioms Lean reports pinned. The two rows where a rule supplies a step, I.13's upper bound on an angle in I.47 and III.1's centre, have no audit lemma; `Audit/Centre.lean` pins the type and axioms of III.1's construction."

This finding holds no book's B4. The pages state each overlap where it occurs; this sentence is part of the edition's account of its own checks (E5).

### 3. Editorial: III.5 and III.6 do not say plainly that the proof rests on the rule, and III.6's row does not explain its rules

**The top lines.** `book/III/05.md:13` and `book/III/06.md:13` read "one of our tacit rules already contains it (see Overlap)". They do not say that our proof rests on the rule. The schema asks the line to say "whether our proof rests on all, some or none of the named rules" (`review/SCHEMA.md:127`–`128`). III.1's line says it (`book/III/01.md:13`), and so does the book's summary (`book/III/index.md:5`). The wording comes from `scripts/render.py:1045`.

**III.6's row.** `book/III/06.md:57` names "Diagram-segment 2 with Generalities 4" and "Generalities 3" without saying what any of them says. III.5's row does explain its rule: "one centre and a common point make the circles one".

**Change-logs.** Both rows carry a change-log, which STYLE, section 4, "Change-logs on the page", has removed elsewhere:

- `book/III/05.md:56`: "have been theorems since 19 October 2026";
- `book/III/06.md:57`: "are former assumptions, proved since 19 October 2026".

**Fix.**

1. At `scripts/render.py:1045`, write `parts.append(f"{overlap_word(ov)} already {verb} it, and our proof rests on {'it' if one else 'them'} (see Overlap)")`.
2. In review/III/06.toml, `[overlap] note`, replace the first two sentences with: "Diagram-segment 2, that one centre and a common point make two circles one, with Generalities 4, that no point within a circle is on it, ends contact within at once; Generalities 3, that a circle's centre is within it, ends contact without, so the three rules give III.6 at once. Generalities 3 (`Tacit.centre_inside`) and 4 are proved in Elements/Figure/RuleBase.lean, so Diagram-segment 2 is the one rule among them we assume."
3. In review/III/05.toml, `[overlap] note`, replace "have been theorems since 19 October 2026, proved in" with "are proved in".

Both records' `text` stamps then go stale, and the records are read again.

### 4. Editorial: III.11's mishnah says the agreement with Heath's reading is not formalised, though a staged file proves it

`mishnah/III/11.md:5` (`book/III/11.md:239`) says: "Neither his local contact nor its equivalence to our whole-circle reading has been formalised."

But `Staging/Routes/Touching.lean` defines contact at a point:

- TouchesInternallyAt, line 75;
- TouchesExternallyAt, line 82.

It also proves that the two readings agree, with no `sorry`:

- touchesInternally_iff, line 415;
- circlesTouch_iff, line 426.

These are unapproved drafts, outside the default build and outside the edition. So the sentence is true of the edition and false of the repository. The reading used in `Elements/` is described correctly, and nothing is hidden.

**Fix.** Replace "has been formalised" with "is part of the edition".

### 5. Editorial: I.47 does not say that a rule which I.13 gives closes one of its cases

`book/I/47.md:73` (the record's passage at "let the angle ABC be added to each") says: "the Lean finds the reason in I.17 and I.13, with the squares standing outward."

But the helper closes the case where AD would cross BC beyond B by Metric 5: `exact angle_le_two_right A B D h₄` (`book/I/47.md:154`). This is the one current overlap row in Book I (`docs/reports/overlaps.md:34`). The page shows the rule only in its list of tacit rules (`:436`). The gap catalogue's entry (`docs/reports/gaps-book-I.md:273`) names only I.17 and I.13.

B2 keeps the row out of the records' count. The page can still say it in a clause.

**Fix.**

1. In review/I/47.toml, set that passage's note to: "Euclid reads off his figure that C lies within the angle DBA and A within FBC; the Lean finds the reason in I.17 and I.13, with the squares standing outward, and closes the case of AD beyond B by Metric 5 (`Tacit.angle_le_two_right`), a rule we assume that no angle exceeds two right angles, which I.13 gives for an angle between two straight lines."
2. At `gaps-book-I.md:273`, after "by I.13,", insert: "with Metric 5 (`angle_le_two_right`), a rule we assume, for the case where AD would cross BC beyond B (I.13 gives that bound; see [the overlap catalogue](overlaps.md)),".

The record's `text` stamp then goes stale.

### 6. Editorial: the catalogue's row for III.1 names one of the two steps the record names

`docs/reports/overlaps.md:35` says: "Supplies a step: a centre for the proof that D is within the circle, by III.2's argument".

The record (review/III/01.toml, `[overlap] note`) and the page (`book/III/01.md:76`) name a second step as well: "and, in the reductio, the supposed centre G".

**Fix.** Make that cell read: "Supplies two steps: a centre for the proof that D is within the circle, by III.2's argument, and the supposed centre G of the reductio".

### 7. Editorial: PROGRAM.md still counts III.2 among the overlaps

`docs/PROGRAM.md:27`–`28` says: "the overlap catalogue names the places where System E's rules already contain a proposition (III.2, and III.5 and III.6 with rules together)".

This is out of date in three ways:

- III.2's rows have been former overlaps since 24 October 2026 (`docs/reports/overlaps.md:25`–`28`, `:141`–`142`).
- `exists_centre` is our rule, not System E's.
- The two steps go unnamed: III.1, and I.13's bound in I.47.

**Fix.** Replace the clause with: "the overlap catalogue names the places where our rules already contain a proposition (III.5 and III.6, with rules together) or supply a step of a proof of one (III.1, and I.13's upper bound on an angle in I.47); III.2's two rows are among its former overlaps since 24 October 2026".

### 8. Editorial: Book III's brief says III.2's overlap remains catalogued

`docs/briefs/0004-book-III.md:583` says: "III.2's overlap remains catalogued,". It now stands only among the former overlaps.

**Fix.** Replace it with: "III.2's two overlaps stay in the catalogue, among the former overlaps since 24 October 2026,".

### 9. Editorial: `review/terms.toml` still describes limitations that have gone

Four scope tags describe, in the present tense, limitations that no record carries any longer, with no word to say so:

- `adjacent-bases` (line 20): "Equal bases on one straight line are taken end to end, BC and CE meeting at C, where Euclid's may lie apart or overlap (I.40)."
- `two-triangles` (line 24);
- `three-pieces` (line 28);
- `diameters-excluded` (line 32).

`mixed-angles-omitted` (line 36) shows how this is done: "No record carries it now that III.16 and III.31 state their mixed angles".

`centre-given` (line 44) still says "Brief 0008's centre rule, once it is in the axiom lock, gives every circle a centre". But that rule is now in the lock, and no record carries the tag.

**Fix.** Append a sentence to each of the four:

- line 20: "No record carries it now that I.40 is full through its companion I.40 general; the worked example in review/SCHEMA.md shows it, as I.40 stood at commit d040117."
- line 24: "No record carries it now that I.45 and II.14 are full through their outline companions."
- line 28: "No record carries it now that II.1 is full through its companion II.1 general."
- line 32: "No record carries it now that III.14 is full through its companion III.14 general."

At line 44, replace the clause from "Brief 0008's centre rule" to the end of the sentence with: "Brief 0008's centre rule, `exists_centre`, is in the axiom lock and gives every circle a centre, so the hypothesis asks only for a centre the circle already has and excludes no circle; no record carries the tag now (briefs 0004 and 0008)."

## Verdicts

- Book I: pass.
- Book II: pass.
- Book III: fail, held by finding 1.
