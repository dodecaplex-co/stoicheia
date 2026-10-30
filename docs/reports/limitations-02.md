# Limitations review 02: Book III

*29 October 2026. Read at `5592377317aeca29ce685831bbbd192fd2c6025e` by Claude Opus 5.5, as the limitations reviewer of Book III. The reviewer wrote, prompted and edited none of the records, pages, catalogues or checks judged here.*

*A note of 29 October 2026. This review's verdict, and the record it offers under "Verdict", were not recorded: an independent review held its new finding 1 material, not editorial, and so failed its pass. [Limitations review 03](limitations-03.md) reads Book III again at `a00151d876ac118eae16f5ba1c0c6e02beec7c7f`. The text below stands as read at its own revision.*

## What B4 asks

B4 is in [ACCEPTANCE](../ACCEPTANCE.md), under "For each book" (`ACCEPTANCE.md:177`). It passes when "The remaining limitations are deliberate, few and stated plainly where they occur: the overlaps of III.2's kind, and any allowed below, where none is now."

The table of the limitations allowed names none (`ACCEPTANCE.md:190`–`199`). An overlap is not a limitation of scope. It is a disclosure, declared in the record and in [the overlap catalogue](overlaps.md) (`ACCEPTANCE.md:207`). So the only limitations B4 can admit in Book III are its overlaps.

[Limitations review 01](limitations-01.md) held Book III: "fail, held by finding 1" (`limitations-01.md:289`). This review reads Book III again at the revision above, by that review's method. As there, every other departure a record declares is held to the same test: a changed route, hypothesis-dropped, or a representation tag. Is it recorded as a choice? Does the page say it plainly, without contradicting the record, facts.json or the catalogues?

Findings are graded by [WORKFLOW](../WORKFLOW.md), section 9 (`WORKFLOW.md:1005`–`1014`). Book III passes only if no blocking or material finding stands.

## How it was read

`git log -1 --format=%H` gave the commit above, and `git status --short` was empty before and after.

These were read whole first:

- ACCEPTANCE, B4 and "The limitations allowed";
- limitations-01: its method, its Book III census, findings 1, 3, 4, 6, 7, 8 and 9, and its verdicts;
- [FORMALIZATION](../FORMALIZATION.md), sections 2, 5, 8 and 9;
- [review/SCHEMA.md](../../review/SCHEMA.md) and `review/terms.toml`;
- the overlap catalogue. Its historical account, from `:323`, is marked as superseded, and only its Book III rows were read closely;
- the [gap catalogue for Book III](gaps-book-III.md);
- [brief 0004](../briefs/0004-book-III.md);
- these decisions entries from 26 October on that bear on Book III's scope, routes, tags or badges:
  - [generated phrases made true](../decisions/2026-10-26-generated-phrases-read-through-03.md), for the badge;
  - [the centre by III.1](../decisions/2026-10-26-centre-by-iii1.md);
  - [the crossing bridge](../decisions/2026-10-26-crossing-bridge.md);
  - [`centre-given` retired](../decisions/2026-10-26-centre-given-retired.md);
  - [four corrections on the angle at the centre](../decisions/2026-10-26-routes-iii-centre-corrected.md);
  - [the tag `angle-at-centre`](../decisions/2026-10-28-angle-at-centre-tag.md);
  - [the route labels of III.20 and III.21](../decisions/2026-10-28-route-labels-iii20-iii21.md);
  - [SCHEMA's route examples](../decisions/2026-10-28-schema-route-examples.md).

  The folder's other entries of those days, Circle 1's retirement among them, were listed and searched for Book III. None changes a Book III statement, route, tag or badge.

**The census.** A script, kept outside the repository, read each of the 37 records with Python's tomllib. From each it took:

- the scope, the companions and the route;
- the representation tags;
- the `[overlap]`, with its kind, rule and `also`;
- any `[coverage]`;
- the kind of every passage;
- the stage, the stamp's commit and the reviewer.

From facts.json it took the status of each of the 66 Book III entries, and which entries are attached to which proposition. Each committed page was searched for these lines:

- the line under the enunciation;
- the Statement, Argument, Representation and Overlap rows;
- every passage led "Argued another way", "A further case" or "Left in Euclid's words".

Every record was then read by hand beside its page.

**Four further reads.**

1. **Statements.** A second script printed Heath's enunciation, facts.json's `enunciation`, beside facts.json's Lean statement. The two were compared clause by clause for:
   - III.1 and its porism, III.3, III.7 and III.8;
   - III.11–III.37 with all their companions;
   - III.2, III.4–III.6, III.9 and III.10, for context.
2. **Words that mark a limitation.** These were searched:
   - `mishnah/III/`, `mishnah/intro/III.md` and `book/III/index.md`;
   - every note of the 37 records.

   The words were "not proved", "left out", "leaves out", "assumed", "restricted", "excludes", "not stated", "not covered", "formalised", "formalized", "omit", "is claimed", "says nothing", "unproved" and similar. Each hit was read in its paragraph.
3. **The earlier findings.** Each file limitations-01 named was read at the lines it named, and where those lines now stand. Two further sources were read beside them:
   - the renderer's badge code (`scripts/render.py:1017`–`1078`);
   - the names that facts.json's statements use for III.20–III.30 and their companions.
4. **Routes.** Every case and different passage of the 37 records was listed. Each was read against SCHEMA's rule for routes, as the coordinator's ruling of 28 October 2026 applies it.

`python3 scripts/check_fidelity.py` and `python3 scripts/heath.py` both passed at this commit. `python3 scripts/check_acceptance.py --help` was read, and no check was run with it.

Other Claude sessions wrote some of the words judged here, as the records' run lines say: III.20's, III.21's, III.26's and III.27's among them. This reading is by the same model family. The independent audit by another family is still to come (ACCEPTANCE, "Beyond the checklist").

**What could not be checked.**

- No `lake build`, kernel replay, `check_style.py`, `check_links.py` or `check_acceptance.py` run. The last of these writes its report, and this review changes no file.
- `scripts/render.py` was not run, and its functions were not called. So this review does not confirm, as limitations-01 did, that the pages, the index and CERTIFICATE.md are byte for byte what `render.py` makes. That is for P4, P9, B1 and E5. The pages were read as committed.
- GitHub was not consulted. So any open pull request that would change Book III's routes is not taken into account, and nothing of card #156 is known here beyond the comment quoted in the orders.
- Statements were compared as facts.json prints them, not from the Lean sources. The proofs were read only where a page's claim bears on them.
- Heath's text was not compared with the scans. Heath's words quoted here are as the repository gives them.
- Passages not cited below were read through their records and pages, not each against its Lean.

## The census

facts.json holds 66 entries for Book III, and all are "proved":

- 37 propositions;
- two porisms, III.1 Por. and III.16 Por.;
- 27 companions.

Each is attached to its proposition, and each companion is listed in its record's `companions`.

Every record is at the stage full, with scope full. None is restricted or partial, no route is alternative, and no record has an unformalized passage or a `[coverage]` clause map. `Staging/` holds only `.gitkeep`.

### The departures of the kinds B4 names

| Proposition | Departure | Where the page states it | What makes it deliberate | Judgement |
|---|---|---|---|---|
| III.1 | Overlap, a step, in two places. `exists_centre` supplies the centre for the proof that D is within the circle, and the supposed centre G of the reductio. | `book/III/01.md:13`, `:76`, `:86`; mishnah `:443` | Brief 0008; the owner's decision of 18 October 2026 (`overlaps.md:5`–`7`); `overlaps.md:83`; III.1's certificate pinned to the rule ([decision of 26 October 2026](../decisions/2026-10-26-centre-given-retired.md)) | Deliberate, plain. The catalogue's row now names both steps (finding 6 mended). |
| III.2 | Route modified, one step: the centre D comes from `exists_centre`, where Heath's reference is III.1. | `book/III/02.md:13`, `:71`, `:79` | Decision of 22 October 2026. The decision of 26 October leaves III.2 to a train of its own, which is to find D by III.1's construction (`centre-by-iii1.md:39`–`41`). | Disclosed and labelled. The reason the page gives is no longer the project's (new finding 2). |
| III.5 | Overlap, gives it at once: `circle_eq` (Diagram-segment 2), with Generalities 4 | `book/III/05.md:13`, `:56` | Brief 0008, section 7; `overlaps.md:84` | Deliberate, plain. The line under the enunciation now says that the proof does not use the rule, which facts.json bears out. |
| III.6 | Overlap, gives it at once: `circle_eq`, with Generalities 3 and 4 | `book/III/06.md:13`, `:57` | Brief 0008, section 7; `overlaps.md:85` | Deliberate. Plain in the line under the enunciation. The row still names two rules without saying what they say (finding 3, still open). |
| III.8 | Route modified, one step: the last step compares the angles at M by I.24 only where a point of contact is involved. | `book/III/08.md:13`, `:121`, `:147` | The decision of 26 October 2026 (`centre-by-iii1.md:31`–`33`): M now comes by III.1's construction, and only the last step stays changed. Brief 0004, note of 28 October (`:661`–`662`). | Deliberate, plain. |
| III.9 | hypothesis-dropped: Euclid's "within" is left out. | `book/III/09.md:66`, `:68`; mishnah `:341` | Gap catalogue, III.9 (`gaps-book-III.md:130`); brief 0004 (`:402`–`405`) | Deliberate, plain. It claims more, so it limits nothing. |
| III.10 | hypothesis-dropped, for circles that only meet. The route is now Euclid's. | `book/III/10.md:56`, `:58` | Brief 0004 (`:406`–`407`); the [decision of 26 October 2026](../decisions/2026-10-26-crossing-bridge.md) that ends III.10 by III.5, through `CirclesCut.of_meet` | Deliberate, plain. |
| III.21 | Route modified, one step: in the semicircle and the less segment, the doubling by III.20 rests on our angle at the centre. | `book/III/21.md:13`, `:55`, `:65`; `mishnah/III/21.md:7` | The coordinator's ruling of 28 October 2026 (`route-labels-iii20-iii21.md:18`–`22`); Heath, vol. 2, p. 49, quoted in the mishnah | Deliberate, plain. Simson's completion is no longer used. |
| III.26 | Route modified, one step: the congruence of the remainders, by III.22 and III.24 | `book/III/26.md:13`, `:65`, `:77` | Brief 0006, stage 3; brief 0004 (`:491`–`497`) | Deliberate, plain. But the I.4 passage, argued another way for two cases within Euclid's statement, is declared a case (new finding 1). |
| III.27 | Route modified, one step: in the obtuse case, the reductio runs on the angles that stand on the circumferences that remain. | `book/III/27.md:13`, `:65`, `:78` | Routes report, III.27; SCHEMA's example of a modified route (`review/SCHEMA.md:81`–`84`) | Deliberate, plain. But the right case is declared a case (new finding 1). |
| III.28 | Route modified, two steps: the case of diameters; the greater circumferences' congruence by III.24 | `book/III/28.md:13`, `:59`, `:68`, `:71` | Gap catalogue, III.28 (Heath, vol. 2, p. 60); brief 0006, stage 3 | Deliberate, plain. |
| III.29 | Route modified, two steps: the case of semicircles; the greater circumferences by the remainders | `book/III/29.md:13`, `:53`, `:62`, `:63` | Gap catalogue, III.29 (Heath, vol. 2, p. 61) | Deliberate, plain. |

The representation readings, by tag:

| Tag | Records | Where the pages state it | What makes it deliberate | Judgement |
|---|---|---|---|---|
| `touching-whole-circles` | III.6, III.11, III.12, III.13 | `book/III/06.md:56`; `11.md:58` and mishnah `:238`; `12.md:64`; `13.md:74` | Brief 0004, "Touching, for circles" and its notes of 19 and 25 October (`:65`–`107`); `review/terms.toml:41`; III.13's three companions, which prove Heath's reading at the point the same as ours | Deliberate, plain. III.11's mishnah is now true (finding 4 mended). |
| `mixed-angles-local` | III.16, III.18, III.31 | `book/III/16.md:86`, `18.md:62`, `31.md:96` | Brief 0011; [decision of 25 October 2026](../decisions/2026-10-25-mixed-angles-homes.md); III.18 added to the tag's meaning on 28 October (`terms.toml:37`) | Deliberate, plain. |
| `angle-at-centre` | III.20 | `book/III/20.md:64`, `:66` | [Decision of 28 October 2026](../decisions/2026-10-28-angle-at-centre-tag.md); brief 0004, notes of 26 October (`:328`–`344`, `:442`–`447`) | Deliberate, plain. It has no badge, by that decision: on Euclid's figures the angle it names is his angle BEC (`angleAtCentre.within`), and `Prop20.special` states that form. |
| `angle-measure` | III.20, III.24–III.30 | The badge in the line under the enunciation of III.26–III.30 (`:13`). The Representation rows: `book/III/20.md:66`, `24.md:58`, `25.md:88`, `26.md:66`, `27.md:66`, `28.md:60`, `29.md:54`, `30.md:58` | Brief 0004, "Circumferences" (`:109`–`168`); `terms.toml:49` | Deliberate, plain. The badge now stands only beside statements that name the measure (finding 1 mended). |
| `segment-with-circle` | III.23–III.25, III.30, III.33, III.34 | `book/III/23.md:46`, `24.md:58`, `25.md:88`, `30.md:58`, `33.md:130`, `34.md:52` | Brief 0006, stage 3; `terms.toml:45` | Deliberate, plain. |
| redundant-hypothesis | III.24, III.27 | `book/III/24.md:58`; `27.md:64`, `:66` | FORMALIZATION, section 5 (`:322`–`331`); `terms.toml:58` | Deliberate, plain. |

**Counts for Book III.**

- No limitation of scope.
- Three overlaps, as before:
  - III.1's supplies a step, in two places, and III.1's proof rests on the rule;
  - III.5's and III.6's give the proposition at once, and neither proof rests on `Tacit.circle_eq`, which facts.json lists in neither entry's `axioms`.
- Seven changed routes, made up of nine steps argued another way (III.28 and III.29 have two each). limitations-01 counted twelve routes and nineteen steps.
  - III.4, III.10, III.16, III.17 and III.24 now follow Euclid.
  - III.8 is down to one step.
  - III.21's changed step is now its doubling, not Simson's completion.
  - One step only takes a centre from the rule where Heath's reference is III.1: III.2's.
- Two hypothesis-dropped: III.9 and III.10.
- 24 representation tags, spread over 18 records (limitations-01 counted 21 over 16). New since then:
  - `angle-at-centre` on III.20;
  - `angle-measure` on III.20, for its companion `Prop20.circumference`;
  - `mixed-angles-local` on III.18.

**Few?** Three limitations, all overlaps, is few. The seven changed routes are departures of argument, not of scope, and each step is labelled where it happens (but see new finding 1 on the count).

**The rest.** 25 records declare none of the kinds B4 names: III.3, III.4, III.7, III.11–III.20, III.22–III.25 and III.30–III.37.

- 13 of these carry a representation tag: III.11–III.13, III.16, III.18, III.20, III.23–III.25, III.30, III.31, III.33 and III.34.
- 12 declare nothing at all: III.3, III.4, III.7, III.14, III.15, III.17, III.19, III.22, III.32 and III.35–III.37.

No page among the 25 says that our statement or the Lean leaves something of Euclid's out. The searched words fall on Euclid's or Heath's own omissions:

- III.17's point on the circumference, "A point on the circumference Euclid leaves out" (`mishnah/III/17.md:5`);
- III.20's "Properly left out" (`mishnah/III/20.md:7`);
- Heath's quotations in III.12, III.13 and III.33.

The rest fall within a declared tag. III.16's and III.18's representation notes say "no addition, ratio or motion of mixed angles is claimed", for example.

**Statements.** Each statement compared clause by clause says what Euclid's enunciation says, read in its representation, with its companions where the record counts them. Five main statements keep Euclid's figure, and their companions take every case: III.7, III.8, III.14, III.15 and III.17 (`book/III/index.md:25`).

Five restrictions might look like limitations. Each only names what Euclid's words presuppose, and the pages say so:

- III.26's clause at the centres asks that G lie across BC from K, where the angle BGC stands on BKC (`book/III/26.md:66`). III.27's clause at the centres asks the like (`book/III/27.md:64`).
- III.7's point F is taken between the centre E and D; the other side is the same statement with A and D named the other way.
- III.8 has a convention that a point of contact lies on neither circumference (`book/III/08.md:128`). Its last clause covers a point of contact too.
- III.3's straight line through the centre is read as FE (`book/III/03.md:72`).
- III.4 has B off AC, so that the two straight lines are two (`book/III/04.md:60`).

III.20's centre on A's side of BC, which limitations-01 listed, is now only in the companion `Prop20.special`. The main statement takes the angle at the centre of any size.

**What has moved since limitations-01.** limitations-01 asked that certain rows be read again if the staged work landed: III.20's, III.21's, III.26's and those of the touching tags (`limitations-01.md:142`). That work has landed in `Elements/` or been retired, and the rows above are those readings.

## The earlier findings

**1. Mended.**

- `book/III/24.md:13` and `book/III/25.md:13` now read "✅ proved, as Euclid states it · Euclid's argument". `CERTIFICATE.md:179` and `:182` mark III.24 and III.25 "whole", with no †.
- III.26–III.30 keep the badge (each page at `:13`) and the † (`CERTIFICATE.md:186`–`190`).
- How it was done:
  - BADGE_WORDS (`scripts/render.py:1022`–`1023`) and representation_badge (`:1067`–`1078`), which now takes the statement's facts.json entry, give the `angle-measure` badge only to a statement that names `Elements.circumference`, `Elements.standing` or `Elements.Arc.measure`.
  - in_lean_line passes that entry (`:1095`).
  - [The decision entry of 26 October 2026](../decisions/2026-10-26-generated-phrases-read-through-03.md) records the change (`:35`–`44`).
- facts.json bears it out:
  - III.24's and III.25's statements name none of the three.
  - III.26, III.28 and III.29 name `circumference`; III.27 and III.30 name `standing`.
  - III.20 carries the tag for `Prop20.circumference`. Its own statement names `angleAtCentre` and none of the three, so it has no badge, rightly.
- III.24's page now agrees with itself. Its row says "The main theorem says nothing of a measure" (`book/III/24.md:58`), and the line above no longer says otherwise.
- `review/terms.toml:12`–`17` now says that the renderer may keep a badge to the statements that use its representation. `:49` lists those statements.

**3. Mended in part. Editorial, still open.**

- **Mended: the lines under the enunciation.** `book/III/05.md:13` and `book/III/06.md:13` now read "one of our tacit rules contains it too, though this proof does not use it (see Overlap)" (`scripts/render.py:1131`–`1133`). That says whether our proof rests on the rule, as SCHEMA asks (`review/SCHEMA.md:128`–`129`). It is true, by facts.json. (The wording limitations-01 proposed, "our proof rests on it", would be false since 26 October 2026.)
- **Still open: III.6's row.** `book/III/06.md:57` still names "Diagram-segment 2 with Generalities 4" without saying what either says. Generalities 3 is now explained, later in the row.
- **Still open: the change-logs.** They remain, and now there are more of them (STYLE, section 4, `docs/STYLE.md:337`–`339`):
  - `book/III/05.md:56`: "have been theorems since 19 October 2026" and "Since 26 October 2026 the proofs of";
  - `book/III/06.md:57`: "former assumptions, proved since 19 October 2026" and "Since 26 October 2026 our proof does not rest on Diagram-segment 2".
- **Fix.**
  1. In `review/III/06.toml`, `[overlap] note`, replace its first two sentences with: "Diagram-segment 2, that one centre and a common point make two circles one, with Generalities 4, that no point within a circle is on it, ends contact within at once; Generalities 3, that a circle's centre is within it, ends contact without, so the three rules give III.6 at once. Generalities 3 (`Tacit.centre_inside`) and 4 are proved in Elements/Figure/RuleBase.lean, so Diagram-segment 2 is the one assumption among them."
  2. In the same note, replace "Since 26 October 2026 our proof does not rest" with "Our proof does not rest".
  3. In `review/III/05.toml`, `[overlap] note`, replace "have been theorems since 19 October 2026, proved in" with "are proved in".
  4. In the same note, replace "Since 26 October 2026 the proofs of" with "The proofs of".

  Both records' `text` stamps then go stale, and the records are read again.

**4. Mended.** `mishnah/III/11.md:5` (`book/III/11.md:238`) now says: "His local contact is defined too, and after III.13 its companions prove it the same as our whole-circle reading, for any two circles (`Prop13.touchesInternally_iff`)." facts.json holds III.13's three companions, proved. The definitions are in `Elements/Foundations/DefinitionsIII.lean` (brief 0004, `:93`–`99`), and `Staging/` is empty.

**6. Mended.** `docs/reports/overlaps.md:83` now reads: "Supplies a step, in two places: inside the construction, a centre for the proof that D is within the circle, by III.2's argument; and, in the reductio, the supposed centre G". That is as the record says, and as `book/III/01.md:76` says.

**7. Not mended. Editorial.**

- `docs/PROGRAM.md:27`–`28` still says: "the overlap catalogue names the places where System E's rules already contain a proposition (III.2, and III.5 and III.6 with rules together)".
- The fix limitations-01 proposed is itself now out of date. On 28 October 2026 (#515) I.47's row left the current table for the former overlaps (`overlaps.md:70`–`77`).
- **Fix.** Replace the clause with: "the overlap catalogue names the places where our rules already contain a proposition (III.5 and III.6, with rules together) or supply a step of a proof of one (III.1); III.2's two rows, since 24 October 2026, and I.47's, since 28 October, are among its former overlaps". PROGRAM.md is the coordinator's.

**8. Not mended. Editorial.**

- `docs/briefs/0004-book-III.md:676` (it was `:583`) still says "III.2's overlap remains catalogued,".
- **Fix.** As before: "III.2's two overlaps stay in the catalogue, among the former overlaps since 24 October 2026,".

**9. Mended in part. Editorial, still open.**

- **Mended.** `centre-given` is gone from `review/terms.toml`, by the [decision of 26 October 2026](../decisions/2026-10-26-centre-given-retired.md), and so is `mixed-angles-omitted`.
- **Still open.** Four scope tags still describe their limitations in the present tense:
  - `adjacent-bases` (`:19`–`21`);
  - `two-triangles` (`:23`–`25`);
  - `three-pieces` (`:27`–`29`);
  - `diameters-excluded` (`:31`–`33`), which is III.14's.

  No record carries any of them. Only SCHEMA's worked example of I.40 at d040117 does.
- **Fix.** As limitations-01 gave it: append "No record carries it now that …" to each, in a change to that protected file with its decisions entry.

## Findings

Each finding is graded by [WORKFLOW](../WORKFLOW.md), section 9.

### 1. Editorial: III.26 and III.27 declare as further cases two steps that Book III's rule for routes makes steps argued another way

**The rule.** SCHEMA (`review/SCHEMA.md:77`–`84`) separates two kinds of case:

- a case "that is trivial, or lies beyond his statement" leaves the route Euclid's;
- "a real case within his statement, argued another way" makes the route modified.

The coordinator's ruling of 28 October 2026 applies this. III.20's right and obtuse angles lie beyond Euclid's statement, so they are a case. III.21's semicircle and less segment lie within it, and there "the Lean's first step, the doubling by III.20, rests on our angle at the centre and not on Euclid's", so it is different (`docs/decisions/2026-10-28-route-labels-iii20-iii21.md:6`–`9`, `:18`–`22`).

**III.26.** The gap catalogue quotes Heath (vol. 2, p. 57; `gaps-book-III.md:233`): "As in III. 21, if Euclid's proof is to cover all cases, it requires us to take cognisance of 'angles at the centre' which are equal to or greater than two right angles. Otherwise we must deal separately with the cases where the angle at the circumference is equal to or greater than a right angle." Right and obtuse angles at the circumferences are within III.26's statement, as the semicircle is within III.21's.

The passage at "therefore the base BC is equal to the base EF" (`review/III/26.toml:21`–`22`; `book/III/26.md:74`, "A further case") argues both cases another way:

- where the angles at the centres are two right angles, "there are no triangles for I.4, and BC and EF are diameters, each two radii (`Tacit.len_add_of_between` …)";
- where they are greater, I.4 is applied to the angles that remain of four right angles.

Other records call the same kind of step different:

- III.29's (`review/III/29.toml:21`–`22`; `book/III/29.md:62`: "BC and EF are diameters, each twice the equal radius, so the Lean adds the radii by `Tacit.len_add_of_between` instead of applying III.27 and I.4");
- III.28's, for its case of diameters (`review/III/28.toml:20`–`21`).

**III.27.** Right angles at A and D are within III.27's statement, which takes angles "of any size" (`book/III/27.md:64`). Heath: "the remarks about the method of treating the different cases apply here also" (vol. 2, p. 59; `gaps-book-III.md:241`). The passage at "And the angle at A is half of the angle BGC" (`review/III/27.toml:38`–`39`; `book/III/27.md:77`, "A further case") takes the right case another way: the angles at the centres "are each two right angles (`angleAtCentre.semicircle`), and so equal with no reductio". The obtuse case beside it is different (`:43`–`44`).

**What follows.** The lines under III.26's and III.27's enunciations say "with one step changed" (`book/III/26.md:13`, `book/III/27.md:13`; `CERTIFICATE.md:186`–`187`), where the rule gives two.

Three sentences say that Euclid's one argument serves every case:

- `mishnah/III/26.md:5`: "So Euclid's one argument serves every case";
- `gaps-book-III.md:233`: "so Euclid's one argument covers every case";
- Book III's introduction, `mishnah/intro/III.md:17` (`book/III/index.md:25`): "so that III.20, III.21 and III.26 take Euclid's one argument for every case".

III.21's own mishnah says of the same doubling "there that step is ours" (`mishnah/III/21.md:7`), and its record calls that step different.

**Why editorial, not material.** Each page says, at the step, what the Lean does there and that the angle at the centre there is ours:

- `book/III/26.md:65`, "a reading that is ours, made after Heath's notes, and not Euclid's", and `:74`;
- `book/III/27.md:65` and `:77`.

No argument is unmarked, and both routes are already modified. What disagrees with the rule, and with III.21, III.28 and III.29, is three things: the kind of one passage in each record, the count the line under the enunciation draws from it, and the three sentences.

**Fix.** These steps are for a reader of the other family:

1. `review/III/26.toml:22`: `kind = "different"`, with the note led by what is argued another way. For example: "Euclid's I.4 gives the bases from the angles BGC, EHF, as in his figure (`angleAtCentre.within`). Where the angles at the centres are two right angles, a case of his statement that his proof does not reach (Heath, vol. 2, p. 57), there are no triangles for I.4: BC and EF are diameters, each two radii (`Tacit.len_add_of_between`, System E, Diagram-segment 1, a rule we assume); where they are greater, I.4 applies to the angles BGC, EHF that remain of four right angles (`angleAtCentre.reflex`), equal by Common Notion 3." That reader should also say whether the doubling under "Therefore etc." (`review/III/26.toml:43`) is a third such step, as the same doubling is in III.21.
2. `review/III/27.toml:39`: `kind = "different"`, with the note unchanged in substance.
3. The three sentences then say what III.21's mishnah says. For example, at `mishnah/intro/III.md:17`, replace "take Euclid's one argument for every case" with "carry Euclid's steps into every case, the step that needs our angle at the centre being ours where Euclid's does not reach". Make the like change at `mishnah/III/26.md:5` and `gaps-book-III.md:233`.
4. The same rule should be applied, on a second reading, to two more case passages:
   - III.2's AB through the centre (`review/III/02.toml:29`–`30`; `book/III/02.md:81`). SCHEMA used it as its example of a case passage until the ruling of 28 October replaced it with III.11's case left to the reader, "to one that fits the wording of the ruling" (`docs/decisions/2026-10-28-schema-route-examples.md:12`–`16`).
   - III.32's D at A (`review/III/32.toml:38`–`39`), where the Lean uses III.31 in place of the triangle ABD.

If the coordinator reads III.26's and III.27's cases as of III.20's kind instead, a ruling should say why, and III.21's record should be reconciled with it. This review recommends the first course.

No statement changes. The records' `text` stamps go stale, and III.26 and III.27 then read "with two steps changed".

### 2. Editorial: III.2's page gives a reason for its changed step that the rule now refutes

III.2's page gives as its reason that a call of III.1 would do no work:

- `book/III/02.md:71`, the route note (`review/III/02.toml:9`): "the Lean from `Tacit.exists_centre`, a rule we assume, for the proof needs the centre alone";
- `book/III/02.md:79` (`review/III/02.toml:20`): "The proof needs the centre alone, so a call of III.1 would do no work".

But since the owner's decision of 26 October 2026, FORMALIZATION, section 5, says that "A call that obtains what Euclid's step obtains, by Euclid's means, is not a dummy citation, even when the proof then uses less than the call returns" (`docs/FORMALIZATION.md:313`–`316`). The decision's entry corrects exactly the reading that III.2's sentences keep: "III.1's construction finds the centre the way Euclid finds it, so its call under "[III. 1]" does the work of his step, even where the proof then keeps the centre alone" (`docs/decisions/2026-10-26-centre-by-iii1.md:9`–`20`). III.4, III.8 and III.17 now find their centres that way. III.2 "is then to find it by III.1's construction in the same way" (`:39`–`41`).

The departure is disclosed and labelled where it happens, and it waits on a train of its own. Only its stated reason is false by the current rule. Book III's introduction states the departure without the reason (`mishnah/intro/III.md:3`), and is right.

The brief, too, presents the old reading as current. Under "Circles and their centres" (`docs/briefs/0004-book-III.md:232`–`246`), the note of 22 October still lists III.2, III.4, III.8 and III.17 as taking the rule's centre: "each needs the centre alone, so a call of III.1 would do no work". The section's opening (`:193`–`197`) names only that correction as superseding the older account. The decision of 26 October left "a dated note in brief 0004 under 'Circles and their centres'" to the brief's owner (`centre-by-iii1.md:94`–`95`), and none has been added. The note of 28 October under "Exceptions" (`:655`–`665`) gives the current state for III.4, III.8 and III.17, but a reader of the centres section never reaches it.

**Fix.**

1. Best: III.2's own train, as the decision names it. D comes by `Prop1.of_circle`, the passage becomes a `helper`, and the route Euclid's. III.2's row in the census above then goes.
2. Until then, in `review/III/02.toml`:
   - in the route note, delete ", for the proof needs the centre alone";
   - in the passage note, replace "The proof needs the centre alone, so a call of III.1 would do no work: the Lean takes D" with "The Lean takes D".

   The record's `text` stamp then goes stale.
3. In brief 0004, after `:246`, add the dated note the decision proposed: "**26 October 2026, #547.** By the owner's decision of that day ([its entry](../decisions/2026-10-26-centre-by-iii1.md)), a call of III.1 that finds the centre by Euclid's construction is no dummy citation, though the proof keeps the centre alone. III.4, III.8 and III.17 find their centres by `Prop1.of_circle` under Heath's "[III. 1]"; III.2 still takes its centre from `exists_centre`, until its own train. The note of 22 October above is overtaken for those four."

## Verdict

- Book III: pass.

limitations-01's finding 1, which held Book III, is mended, and so are its findings 4 and 6. No blocking or material finding stands. Still open, all editorial, and none holding B4:

- new findings 1 and 2;
- limitations-01's findings 3, 7 and 8;
- finding 9, in part.

The record this review supports, for `docs/reports/acceptance/book-III.toml` (ACCEPTANCE, "Recording a review item"):

```toml
[limitations]
verdict = "pass"
reviewer = "Claude Opus 5.5, limitations reviewer of Book III"
commit = "5592377317aeca29ce685831bbbd192fd2c6025e"
evidence = "docs/reports/limitations-02.md"
```

The verdict is of this revision. A train that changes Book III's records, pages or routes, the fixes above among them, changes what was read.
