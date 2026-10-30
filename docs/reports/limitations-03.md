# Limitations review 03: Book III

*29 October 2026. Read at main `a00151d876ac118eae16f5ba1c0c6e02beec7c7f` by Claude Opus 5.5, independent limitations reviewer. The reviewer wrote, prompted and edited none of the records, pages, catalogues or checks judged here.*

## What B4 asks

B4 is in [ACCEPTANCE](../ACCEPTANCE.md), under "For each book" (`ACCEPTANCE.md:177`). It passes when "The remaining limitations are deliberate, few and stated plainly where they occur: the overlaps of III.2's kind, and any allowed below, where none is now."

The table of the limitations allowed names none (`ACCEPTANCE.md:190`–`205`), and an overlap is "no limitation of scope" but a disclosure (`:207`). P3 lets a route be Euclid's or modified, never alternative (`:155`). So the checklist allows a changed route, and B4 asks of it what it asks of any limitation: that it be deliberate, few and stated plainly where it occurs. This reads B4 otherwise than limitations-02 did, which held that "the only limitations B4 can admit in Book III are its overlaps" (`limitations-02.md:9`). The table admits statements short of full (`ACCEPTANCE.md:192`), and P3 admits a `modified` route beside it. #704, and #547's plan as #704 gives it, read B4 the same way, for they make the changed routes limitations that Book III's B4 lists.

Two things have changed since [limitations review 02](limitations-02.md), which read `5592377317aeca29ce685831bbbd192fd2c6025e`:

- #720, Book III's spine, has landed. III.2, III.8 and III.28 now follow Euclid's route; III.26, III.27 and III.29 changed; and README now counts four changed routes (`README.md:33`).
- Card #704, which blocks the release, is open. It names the cases of III.21, III.26, III.27 and III.29 that depart from Euclid's printed route, a consensus gap of the outside reading ([RUBRIC](../RUBRIC.md), `:37`–`39`). It gives two ways to close each. The first is Euclid's route or, for a case his printed proof does not reach, "a completion Heath reports (Simson's, for III.21)". The second lets the departure stand if "the record and the page say why the departure is needed in our representation, and name the bridge that carries it; Book III's B4 limitations list it". As #704 quotes it, #547's plan of 26 October keeps III.26, III.28 and III.29 `modified` for this release, "as deliberate limitations in Book III's B4 (#156)", and "III.21 is in no plan".

So for those four propositions this review does two things. It judges each departure as B4 asks. And it says, departure by departure, whether the condition of #704's second way holds, so that the list below can serve #704.

Findings are graded by [WORKFLOW](../WORKFLOW.md), section 9 (`WORKFLOW.md:1005`–`1020`):

- Blocking: "an invalid or wrongly scoped formal claim presented as full; an unresolved dependency presented as closed; an unapproved change to the foundations; a materially false certificate."
- Material: "an unmarked alternative argument; a hidden omission of a clause; an unsupported claim about a representation; a misleading figure; a wrong quotation or attribution."
- Editorial: "repetition, awkward prose, excess detail, or inconsistent formatting that does not change the meaning."

The section goes on: "A few deliberate limitations can stand in an excellent edition when each is stated plainly where it occurs. An accepted limitation names a deliberate boundary; it never stands in for a defect nobody has looked into." A blocking or material finding fails B4.

## How it was read

Each file was read as revision `a00151d876ac118eae16f5ba1c0c6e02beec7c7f` holds it, with `git show` and from an archive of that revision unpacked in a scratch directory. The working tree was not used, and no file of the repository was changed. This text was revised after an independent review of it, still reading that revision.

These were read whole first:

- ACCEPTANCE: P3, P4, B4, "The limitations allowed" and "Recording a review item";
- WORKFLOW, section 9; RUBRIC, "The gaps" (`RUBRIC.md:37`–`44`) and "What to report" (`:90`–`100`);
- the rule for routes in [review/SCHEMA.md](../../review/SCHEMA.md) (`:70`–`88`), and [FORMALIZATION](../FORMALIZATION.md), "Euclid's route, and departures from it" (`:355`–`377`);
- `review/terms.toml`;
- limitations-02 and the independent review of it, which held limitations-02's new finding 1 material, not editorial, and so failed its pass, as inputs and not as conclusions;
- the text of card #704, read once;
- the decisions entries of 28 October 2026 that bear on Book III's routes or statements:
  - [the route labels of III.20 and III.21](../decisions/2026-10-28-route-labels-iii20-iii21.md);
  - [SCHEMA's route examples](../decisions/2026-10-28-schema-route-examples.md);
  - [III.27 and III.29 swapped](../decisions/2026-10-28-iii27-iii29-swap.md);
  - [III.2's centre](../decisions/2026-10-28-iii2-centre.md);
  - [the congruent companions](../decisions/2026-10-28-congruent-companions.md), [III.1 under Heath](../decisions/2026-10-28-iii1-under-heath.md) and [III.1's attached pin](../decisions/2026-10-28-iii1-attached-pin.md), searched for routes;
- [brief 0004](../briefs/0004-book-III.md)'s notes of 28 October (`:170`–`182`, `:261`–`280`) and its list of routes "of its date" (`:701`–`719`);
- the [routes report](routes-book-III.md): its sections on III.27 (`:224`–`298`) and on the angle at the centre (`:420`–`542`), and everything from its addendum of 26 October on the angle at the centre (`:1684`) to its end (`:1921`);
- the [gap catalogue for Book III](gaps-book-III.md), its entries for III.20 to III.29 (`:195`–`254`);
- Book III's introduction, `mishnah/intro/III.md`.

**The census.** A script, kept outside the repository, read the 37 records with Python's tomllib, and the 69 Book III entries of facts.json. From each record it took the scope, the companions, the route, the tags, any `[overlap]` or `[coverage]`, the kind of every passage, and the stage and stamp. From facts.json it took each entry's kind and status, and which entries are attached to which proposition.

**The four changed routes.** For each of III.21, III.26, III.27 and III.29 the record, the committed page (the line under the enunciation, the field table, the passage list, and the Lean listing where cited) and the mishnah were read whole. Beside them was read the Lean at the steps in question: `Elements/BookIII/Prop21.lean` whole, `Prop26.lean:474`–`503`, `Prop27.lean:178`–`237` and `Prop29.lean:84`–`104`. Every `case` and `different` passage of the 37 records was listed, and read against SCHEMA's rule as the coordinator's ruling of 28 October 2026 applies it.

**Words that mark a limitation.** The mishnahs of the 28 records that declare none of B4's kinds were searched for "not proved", "left out", "leaves out", "restrict", "exclud", "not stated", "not covered", "omit", "does not prove", "does not cover", "extra hypothes", "says nothing", "unproved", "not Euclid", "is ours", "another way" and "depart". Each hit was read in its paragraph.

**Checks.** On the unpacked archive:

- `python3 scripts/heath.py` passed: "contracts: references, porisms, review/terms.toml, 2 examples in review/SCHEMA.md and 99 review records hold".
- `python3 scripts/check_style.py --no-lean` passed: "the hard rules hold (S1–S11 and S13–S26)".
- `python3 scripts/check_links.py` passed: "all 16118 relative links and anchors in 633 Markdown files resolve".
- `python3 scripts/check_fidelity.py` did not run. It needs a Git work tree, and none was made for it, so that the repository's `.git` stayed untouched. A check not run is not a pass, so this review does not say that the records' stamps are current.

**What could not be checked.**

- No `lake build`, kernel replay, S12, `check_acceptance.py` or `render.py`. The pages were read as committed, not compared with what `render.py` makes; that is for P4, P9, B1 and E5.
- Heath's page images were not consulted, and his words are as the repository gives them. Two judgements below lean on them: finding 3, which cites Heath's p. 57 and III.20's mishnah's report of his p. 47 (leaves n69 and n59); and finding 5, on III.29's two citations of his p. 60 (leaf n72).
- GitHub was not consulted. #547's plan is known here only as #704 quotes it.
- Statements were not compared clause by clause again, save those of III.27 and III.29, which #720 changed by the owner's decision of 28 October 2026 ([the entry](../decisions/2026-10-28-iii27-iii29-swap.md)). Each now states Euclid's congruence reading, with its measure form as a companion, and neither is narrowed. For the rest, limitations-02's comparison stands, at its revision.
- Other Claude sessions wrote some of the words judged here, as the records' run lines say: III.21's route label and III.27's record among them. This reading is of the same family. The independent audit by another family is still to come (ACCEPTANCE, "Beyond the checklist").

## The census

facts.json holds 69 entries for Book III, and all are "proved":

- 37 propositions;
- two porisms, III.1 Por. and III.16 Por.;
- 30 companions, three of them new since limitations-02: III.1 of_circle, III.27 of_measure and III.29 of_measure.

Each is attached to its proposition, and each companion is listed in its record's `companions`.

Every record is at the stage `full`, with scope `full`. None is restricted or partial, no route is `alternative`, and no record has an `unformalized` passage or a `[coverage]` clause map. `Staging/` holds only `.gitkeep`.

### The departures of the kinds B4 names

| Proposition | Departure | Where the page states it | What makes it deliberate | Judgement |
|---|---|---|---|---|
| III.1 | Overlap, a step, in two places: `Tacit.exists_centre` gives a centre for the proof that D is within the circle, and the supposed centre G of the reductio. | `book/III/01.md:13`, `:76`; `overlaps.md:83` | Brief 0008; the owner's decision of 18 October 2026 (`overlaps.md:5`–`7`) | Deliberate, plain. |
| III.5 | Overlap, gives it at once: `Tacit.circle_eq` (Diagram-segment 2), with Generalities 4 | `book/III/05.md:13`, `:56`; `overlaps.md:84` | Brief 0008, section 7 | Deliberate, plain. The proof does not use the rule. |
| III.6 | Overlap, gives it at once: `Tacit.circle_eq`, with Generalities 3 and 4 | `book/III/06.md:13`, `:57`; `overlaps.md:85` | Brief 0008, section 7 | Deliberate, plain. The row still names two rules without saying what they say (limitations-01's finding 3, below). |
| III.9 | `hypothesis-dropped`: Euclid's "within" is left out. | `book/III/09.md:66`, `:68`; `mishnah/III/09.md:7` | Gap catalogue, III.9; brief 0004 | Deliberate, plain. It claims more, so it limits nothing. |
| III.10 | `hypothesis-dropped`, for circles that only meet | `book/III/10.md:56`, `:58` | Brief 0004; the [decision of 26 October 2026](../decisions/2026-10-26-crossing-bridge.md) | Deliberate, plain. |
| III.21 | Route modified, one step: in the semicircle and the less segment, the doubling by III.20 rests on our angle at the centre. | `book/III/21.md:13`, `:55`, `:65`; `mishnah/III/21.md:7`; `mishnah/intro/III.md:17` | The coordinator's ruling of 28 October 2026 (`route-labels-iii20-iii21.md:18`–`22`) | Deliberate, plain. #704's condition is not met (finding 3). |
| III.26 | Route modified, one step, at I.4: right angles at the circumferences give diameters; obtuse ones give angles at the centres greater than two right angles, and I.4 takes those that remain of four right angles. | `book/III/26.md:13`, `:65`, `:74`; `mishnah/III/26.md:5`; `mishnah/intro/III.md:17` | #547's plan, as #704 quotes it; brief 0004 (`:271`–`280`); routes report (`:1913`–`1921`) | Deliberate, plain. #704's condition is met in part (finding 2). |
| III.27 | Route modified, one step declared: where the angles at A and D are obtuse, the reductio runs on the angles that stand on the circumferences that remain. A second step, where they are right, is declared a further case (finding 1). | `book/III/27.md:13`, `:65`, `:78`, `:79`; `mishnah/III/27.md:7` | SCHEMA's example of a `modified` route (`review/SCHEMA.md:81`–`84`; [the ruling](../decisions/2026-10-28-schema-route-examples.md)) | Deliberate. Not plain at the right angles (finding 1). |
| III.29 | Route modified, two steps: for greater circumferences, the angles at the centres, greater than two right angles, are taken from four right angles before I.4; semicircles give diameters. | `book/III/29.md:13`, `:53`, `:64`, `:65`; `mishnah/III/29.md:5`, `:7` | #547's plan, as #704 quotes it; brief 0004 (`:271`–`280`); routes report (`:1913`–`1921`) | Deliberate, plain. #704's condition is met in part (finding 2). |

The representation readings, by tag:

| Tag | Records | Where the pages state it | What makes it deliberate | Judgement |
|---|---|---|---|---|
| `touching-whole-circles` | III.6, III.11, III.12, III.13 | `book/III/06.md:56`, `11.md:58`, `12.md:64`, `13.md:74` | Brief 0004, "Touching, for circles"; `review/terms.toml:41`; III.13's three companions | Deliberate, plain. |
| `mixed-angles-local` | III.16, III.18, III.31 | `book/III/16.md:86`, `18.md:62`, `31.md:96` | Brief 0011; [decision of 25 October 2026](../decisions/2026-10-25-mixed-angles-homes.md); `terms.toml:37` | Deliberate, plain. |
| `angle-at-centre` | III.20 | `book/III/20.md:66` | [Decision of 28 October 2026](../decisions/2026-10-28-angle-at-centre-tag.md); `terms.toml:54` | Deliberate, plain. |
| `angle-measure` | III.20, III.24–III.30 | The badge in the line under the enunciation of III.26, III.28 and III.30 (`:13`), whose statements name the measure. The Representation rows: `book/III/20.md:66`, `24.md:58`, `25.md:88`, `26.md:66`, `27.md:66`, `28.md:60`, `29.md:54`, `30.md:58` | Brief 0004, "Circumferences"; `terms.toml:49` | Deliberate, plain. III.27's and III.29's main statements now speak of circumferences that coincide, and name no measure, so they rightly have no badge; their companions do name it. |
| `segment-with-circle` | III.23–III.25, III.30, III.33, III.34 | `book/III/23.md:46`, `24.md:58`, `25.md:88`, `30.md:58`, `33.md:130`, `34.md:52` | Brief 0006, stage 3; `terms.toml:45` | Deliberate, plain. |
| `redundant-hypothesis` | III.24, III.27, III.29 | `book/III/24.md:58`, `27.md:66`, `29.md:54` | FORMALIZATION, section 5; `terms.toml:58`, whose meaning names III.24 and III.27 only (finding 6); brief 0004's note of 28 October (`:170`–`182`) | Deliberate, plain. III.29's is new: in `BookIII.Prop29`, circumferences that coincide lie in equal circles already. |

**Counts for Book III.**

- No limitation of scope.
- Three overlaps, as before:
  - III.1's supplies a step, in two places, and III.1's proof rests on the rule;
  - III.5's and III.6's give the proposition at once, and neither proof rests on `Tacit.circle_eq`.
- Four changed routes, with five steps declared argued another way: one each in III.21, III.26 and III.27, and two in III.29. Finding 1 makes III.27's two, and the steps six. limitations-02 counted seven routes and nine steps.
  - III.2 now finds its centre by III.1's construction (`Prop1.of_circle`), and its route is Euclid's.
  - III.8's last step now goes by Euclid's two orders in every case, and its route is Euclid's.
  - III.28's route is Euclid's: its two diameters are a case Heath calls "scarcely worth giving, as the proof can easily be supplied" (vol. 2, p. 60), declared as a passage.
  - III.26's remainders now come by Euclid's subtraction (`Prop26.extend`, `Prop26.remainder`), so that step is Euclid's again; its step at I.4 is now declared `different`.
- Two `hypothesis-dropped`: III.9 and III.10.
- 25 representation tags over 18 records. New since limitations-02: `redundant-hypothesis` on III.29.

**Few?** Three overlaps and four changed routes, in 37 propositions. The four routes share one cause. Euclid's angle at the centre is less than two right angles, so his printed proofs of III.21, III.26 and III.27 reach only the segment greater than a semicircle, or the acute angle at the circumference, as Heath says of each (vol. 2, pp. 49, 57 and 59); and Euclid's figure for III.29 has the circumference less than a semicircle, as its record says. The Lean takes the other cases through one reading of ours, the angle at the centre of any size (`angleAtCentre`), and its bridges. That is few, and one boundary.

**The rest.** 28 records declare none of the kinds B4 names: III.2–III.4, III.7, III.8, III.11–III.20, III.22–III.25, III.28 and III.30–III.37.

- 14 of these carry a representation tag: III.11–III.13, III.16, III.18, III.20, III.23–III.25, III.28, III.30, III.31, III.33 and III.34.
- 14 declare nothing at all: III.2–III.4, III.7, III.8, III.14, III.15, III.17, III.19, III.22, III.32 and III.35–III.37.

No mishnah among the 28 says that our statement or the Lean leaves something of Euclid's out. The searched words fall elsewhere:

- on Euclid's or Heath's own omissions: III.7's quotation of De Morgan, III.17's "A point on the circumference Euclid leaves out", III.20's "Properly left out";
- on companions under a declared tag: III.13's "they are not Euclid's proofs, which keep the whole-circle reading";
- on a declared reading: III.20's "That reading is ours";
- on the modern way: III.22's "Heron's proof, which Heath gives under III.20, not Euclid's".

The `case` passages of these records were read under SCHEMA's rule. Each that bears on it is a case Euclid's figure leaves aside that is trivial or degenerate, as the rule allows. III.2's AB through the centre needs no triangles, for DE is then nothing, or part of a radius (`book/III/02.md:81`). III.32's D at A has no triangle ABD, and III.31 makes the angles right (`review/III/32.toml`, the passage at "therefore the angle ADB"). limitations-02 asked that both be read again, and both fit. III.28's two diameters are a case Heath calls scarcely worth giving. III.27's right angles, which are not of that kind, are finding 1.

## The departures #704 names

For each departure, the table asks: does the record say why it is needed in our representation, and does it name the bridge; does the mishnah; is its label true under SCHEMA's rule; is it a limitation ACCEPTANCE allows; and does #704's second way hold.

| Proposition and cases | Why it is needed | The bridge | Label | Allowed by ACCEPTANCE? | #704's second way |
|---|---|---|---|---|---|
| III.21: the semicircle and the less segment, the doubling by III.20 | The record (`:8`, `:31`) and the mishnah (`:3`, `:7`) say why Euclid's printed step does not reach these segments: his angle at the centre is less than two right angles (Heath, vol. 2, p. 49). They do not say why this departure is needed. They say instead that Simson's completion, which Heath reports and #704 names, "is not needed" (record `:8`, page `:55`), and "our proof needs no completion of Simson's" (mishnah `:7`, `gaps-book-III.md:202`). | `angleAtCentre`, `angleAtCentre.size` and `BookIII.Prop20`, in the record (`:31`) and on the page (`:65`); the mishnah names `angleAtCentre`. | True: `different`, and `modified`, by the ruling of 28 October. | Yes. P3 admits `modified`; the ruling makes it deliberate; the page states it at `:13`, `:55` and `:65`, and the mishnah at `:7`. | Not met (finding 3). |
| III.26: right and obtuse angles at the circumferences, at I.4 | The mishnah says "The proof needs a division at I.4" and quotes Heath (vol. 2, p. 57); the record, that the angles at the centres are taken from four right angles "before I.4 applies" (`:23`). Why, in our representation, is left to be inferred: I.4 compares angles of triangles, and an angle of two right angles or more is no angle of a triangle. The introduction says it for the right case alone ("with no triangles for I.4", `mishnah/intro/III.md:17`). | `Prop26.alike`, at the step before, in the record (`:17`) and on the page (`:73`). `angleAtCentre.reflex` is not named in the record or the mishnah, nor in the page's field table or passage list: it appears only in the Lean listing (`book/III/26.md:527`) and the list of shared steps (`:607`). `Tacit.len_add_of_between`, for the diameters, appears only in the Lean listing (`:522`) and the list of rules (`:647`). | True: `different`, `modified`. | Yes. Deliberate by #547's plan and brief 0004 (`:271`–`280`); stated plainly. | In part (finding 2). |
| III.27: obtuse angles at A and D, the reductio on the angles that stand on the circumferences that remain | Said, in our representation: the angles at the centres "are greater than two right angles, which I.23 does not construct and III.26's statement does not speak of" (record `:9`, page `:65`); "I.23 cannot make one for the reductio" (mishnah `:7`). | `angleAtCentre.reflex` and `Circumference.whole`, in the record (`:52`) and on the page (`:79`); the mishnah names `angleAtCentre` and says what the bridge does. | True: `different`, `modified`, SCHEMA's own example. | Yes. Deliberate by the ruling that makes it SCHEMA's example; stated plainly. | Met. |
| III.27: right angles at A and D, the halving by III.20 | Said: the angles at the centres "are each two right angles (`angleAtCentre.semicircle`), and so equal with no reductio, and III.20 (`Prop20`) halves them" (record `:47`), on "a reading that is ours" (`:9`); the Lean adds that such an angle is "no angle of ours, for our angles are less than two right angles" (`Prop27.lean:196`–`198`). | `angleAtCentre.semicircle` and `Prop20`, in the record (`:47`) and on the page (`:78`). | Not true: declared `case`, "A further case" (finding 1). | Yes, once it is labelled as a departure. As it stands it is not stated plainly where it occurs. | Not met until its label is true. |
| III.29: greater circumferences, and semicircles | Said in part: Euclid's I.4 "uses the ordinary central angles standing on lesser circumferences" (record `:9`), and the reflex angles at the centres standing on the greater "must be subtracted from four right angles before I.4 applies" (`:35`); "Which circumference does the angle see?" (mishnah `:7`); for semicircles, "we need no triangles" (mishnah `:5`). Why, in our representation, is left to be inferred, as in III.26: an angle greater than two right angles is no angle of a triangle. | `Prop20`, `Prop26.alike` and `angleAtCentre.reflex`, in the record (`:34`, `:40`, `:41`) and on the page (`:64`, `:65`). `Tacit.len_add_of_between`, for the diameters, appears only in the Lean listing (`book/III/29.md:140`) and the list of rules (`:266`). | True: two `different` passages, `modified`. | Yes. Deliberate by #547's plan and brief 0004 (`:271`–`280`); stated plainly. | In part (finding 2). |

**Are the departures material?** Two of the three outside readers rate them material, as #704 records, and the third deducts for them. They grade by RUBRIC, whose "material" is "something a careful reader would be misled by, or a scope or route short of Euclid's" (`RUBRIC.md:96`). By that definition every one of these departures is material, disclosed or not, until the route is Euclid's or #704 closes the gap another way. That is the right measure for the outside reading, whose gate it holds: "neither a consensus gap nor a confirmed singleton gap is open" (`RUBRIC.md:42`–`44`).

B4 is graded by WORKFLOW, section 9, and its "material" is narrower: "an unmarked alternative argument; a hidden omission of a clause; an unsupported claim about a representation; a misleading figure; a wrong quotation or attribution". By that definition a departure is material when it is not marked where it occurs, not because it departs. Four of the five cases above are marked: the route is `modified`, the passage `different`, the page says "Argued another way" at the step and "with one step changed", or two, above the table, and the mishnah says why Euclid's printed proof does not reach the case. They are not material, and WORKFLOW says why they may stand: "A few deliberate limitations can stand in an excellent edition when each is stated plainly where it occurs." The fifth, III.27's right angles, is argued another way and marked as a case that leaves the route Euclid's. That is material (finding 1), and it fails B4.

The two scales do not disagree about the facts. RUBRIC's measures distance from Euclid, at the outside reading; WORKFLOW's measures defects, which B4 must not accept. #704 joins them: it lets a disclosed departure stand at the outside reading when its need and its bridge are stated and B4 lists it. So B4 does not wait on #704. That would count one gap twice, and grade B4 on a scale ACCEPTANCE does not give it. But B4 lists the departures, with #704's condition judged for each, above. A pass of B4 would not by itself close #704.

## The earlier findings

**limitations-02's new finding 1. Mended for III.26; open for III.27, and now finding 1 below.**

- III.26's passage at "therefore the base BC is equal to the base EF" is `different` (`review/III/26.toml:22`), and the page says "Argued another way" there (`book/III/26.md:74`).
- The three sentences that said Euclid's one argument serves every case now say otherwise:
  - `mishnah/III/26.md:5`: "this additional subtraction changes Euclid's written argument";
  - `gaps-book-III.md:232`: "the proof takes Euclid's steps in every case but at I.4";
  - `mishnah/intro/III.md:17`: "III.26 takes Euclid's argument with one step changed, at I.4".
- limitations-02 asked whether III.26's doubling under "Therefore etc." is a third such step. It is not. Euclid's setting-out takes both pairs of equal angles as given, and the helper (`review/III/26.toml:43`–`47`) supplies the passage from one pair to the other, which he leaves to III.20; it argues none of his steps another way. Its use of our angle at the centre in the right and obtuse cases is the case already marked at I.4.
- III.2's and III.32's `case` passages, read again, fit the rule (above).
- III.27's right case is still `case`.

**limitations-02's new finding 2. Mended.** III.2 finds its centre D by III.1's construction (`Prop1.of_circle`), and its route is Euclid's ([the entry](../decisions/2026-10-28-iii2-centre.md)). Its page no longer gives a reason the rule refutes. Brief 0004 now has the dated note the decision of 26 October left to it (`0004-book-III.md:261`–`269`).

**limitations-01's finding 3. Mended in part. Editorial, still open.** The change-logs remain in the overlap notes of III.5 and III.6 (STYLE, section 4): "have been theorems since 19 October 2026" and "Since 26 October 2026 the proofs of" (`review/III/05.toml:13`); "former assumptions, proved since 19 October 2026" and "Since 26 October 2026 our proof does not rest" (`review/III/06.toml:17`). III.6's row still names Diagram-segment 2 and Generalities 4 without saying what either says (`book/III/06.md:57`). The fix is limitations-02's.

**limitations-01's finding 7. Not mended. Editorial.** `docs/PROGRAM.md:27`–`28` still says "the overlap catalogue names the places where System E's rules already contain a proposition (III.2, and III.5 and III.6 with rules together)". The fix is limitations-02's. PROGRAM.md is the coordinator's.

**limitations-01's finding 8. Not mended. Editorial.** `docs/briefs/0004-book-III.md:722` (it was `:676`) still says "III.2's overlap remains catalogued,". The fix is limitations-02's.

**limitations-01's finding 9. Mended in part. Editorial, still open.** Four scope tags still describe their limitations in the present tense (`review/terms.toml:19`–`33`), though no record carries any of them. The fix is limitations-02's, in a change to that protected file with its decisions entry.

## Findings

Each finding is graded by [WORKFLOW](../WORKFLOW.md), section 9.

### 1. Material: III.27's right angles at A and D, a step argued another way within Euclid's statement, are declared a further case

**The rule.** SCHEMA separates two kinds of case (`review/SCHEMA.md:77`–`84`). "Nor does a case that is trivial, or lies beyond his statement, which the Lean takes as well" change the route; it "is declared as a passage (`case`, `helper` or `given`)". But "a real case within his statement, argued another way" makes the route `modified`. The coordinator's ruling of 28 October 2026 applies the rule to III.21's semicircle: "There the Lean's first step, the doubling by III.20, rests on our angle at the centre and not on Euclid's, so record 21 marks it `different`" (`docs/decisions/2026-10-28-route-labels-iii20-iii21.md:18`–`22`).

**III.27.** Right angles at A and D are within III.27's statement, whose angles at A and D are "of any size" (`review/III/27.toml:3`). Euclid's printed proof does not reach them: with the centres on BC and EF there is no angle EHF for I.23 to copy, and no angle BGC for III.20 to halve. Heath does not count the case trivial. Under III.26 he says: "if Euclid's proof is to cover all cases, it requires us to take cognisance of 'angles at the centre' which are equal to or greater than two right angles. Otherwise we must deal separately with the cases where the angle at the circumference is equal to or greater than a right angle" (vol. 2, p. 57; `gaps-book-III.md:232`). Of III.27 he says "the remarks about the method of treating the different cases apply here also" (vol. 2, p. 59; `gaps-book-III.md:240`). III.28's two diameters, which he calls "scarcely worth giving", are another matter.

The Lean argues the case another way. The passage at "And the angle at A is half of the angle BGC" (`review/III/27.toml:45`–`47`; `book/III/27.md:78`, "A further case") says that "the angles at the centres standing on BC and EF are each two right angles (`angleAtCentre.semicircle`), and so equal with no reductio, and III.20 (`Prop20`) halves them." Euclid's reductio is set aside, and his halving by III.20 rests on our angle at the centre, two right angles, not on his. The Lean says so (`Elements/BookIII/Prop27.lean:196`–`207`). So does the record's own route note: the halving where the angles at A and D "are right or obtuse" is "a reading that is ours, made after Heath's notes, and not Euclid's" (`:9`). This is III.21's step in its semicircle, which the ruling makes `different`.

**What follows.** The passage is `case`, so the page labels it "A further case", which by SCHEMA is a case that leaves the route Euclid's. The line under the enunciation says "with one step changed" (`book/III/27.md:13`), and so does the certificate (`CERTIFICATE.md:188`), where the rule gives two.

**Why material, and not editorial or blocking.** Editorial is only what "does not change the meaning", and this changes two claims of the page: what the label at the step says the step is, and how many steps the line under the enunciation and the certificate count as changed. It is not blocking. No formal claim is wrong, and the certificate's dependencies are true; its count of steps is a disclosure, not "a materially false certificate". Of WORKFLOW's material kinds it is the first: a step argued another way, marked where it occurs as one that is not. The field table's Argument row and the passage's note do tell the reader what the Lean does, so nothing is hidden, and the mend is small. But B4 asks that each limitation be "stated plainly where it occurs". Where this one occurs, the page marks a case Euclid's figure leaves aside (`book/III/27.md:69`), which is true, and not a step argued another way, which it also is; and the line under the enunciation counts one step changed where SCHEMA's rule gives two. #704, too, asks that each route label "stays true under review/SCHEMA.md's route rule".

limitations-02 graded this editorial, for III.26 and III.27 together, and III.26's half is mended. The independent review of limitations-02 held the finding material. This review grades III.27's half material, for the reasons above.

**Fix (#704).** These steps are for a reader of the other family who wrote none of it:

1. `review/III/27.toml:46`: `kind = "different"`, with the note led by what is argued another way. For example: "Where the angles at A and D are right, a case of Euclid's statement that his proof does not reach (Heath, vol. 2, pp. 57 and 59), the centres lie on BC and EF, and there are no angles BGC, EHF for I.23 or for the reductio. The angles at the centres standing on BC and EF are each two right angles (`angleAtCentre.semicircle`), so equal with no reductio, and III.20 (`Prop20`) halves them, on our angle at the centre and not Euclid's. In Euclid's figure the angles at A and D are acute and the centres on their sides, where III.20 halves the angles BGC, EHF, as its companion `Prop20.special` states it; equal circumferences put the centres alike (`Prop27.sides`, which sorts them by `Prop24.angle_type`)."
2. The record is read again in full, and stamped. The page then says "with two steps changed", and CERTIFICATE.md "two steps changed", from `render.py`.
3. No statement, `--` line or Lean changes. The mishnah already says what the Lean does (`mishnah/III/27.md:7`), and SCHEMA's example, III.27's obtuse case, stays true.

If the coordinator reads the right case as trivial instead, like III.28's diameters, a ruling should say why, against Heath's grouping of it at p. 57 and against the ruling on III.21. This review recommends the first course.

### 2. Editorial: III.26 and III.29 leave why their changed step at I.4 is needed to be inferred, and name its bridges only in part

The two proofs take I.4 the same way (`Elements/BookIII/Prop26.lean:482`–`503`; `Prop29.lean:92`–`104`). `Prop26.alike` sorts the cases; where the angles at the centres are two right angles, the bases are diameters, each two radii (`Tacit.len_add_of_between`); where they are greater, I.4 takes the angles that remain of four right angles (`angleAtCentre.reflex`, Common Notion 3). So one test serves both.

**III.26.** The record says what the Lean does at I.4 and that it departs: "For obtuse inscribed angles, the central angles are reflex: Common Notion 3 removes them from four right angles before I.4 applies, a different argument within the statement (Heath, vol. 2, p. 57). When the inscribed angles are right, the bases are diameters, each the sum of two equal radii" (`review/III/26.toml:23`; `book/III/26.md:74`). The mishnah says "The proof needs a division at I.4" (`mishnah/III/26.md:5`).

**III.29.** The record says that Euclid's I.4 "uses the ordinary central angles standing on lesser circumferences" (`review/III/29.toml:9`), and that the angles at the centres standing on the greater are reflex, "which must be subtracted from four right angles before I.4 applies" (`:35`); for semicircles, "adding the equal radii gives equal diameters" (`:41`). The page gives the same words (`book/III/29.md:53`, `:64`, `:65`). The mishnah says that for semicircles "we need no triangles", and that removing the reflex angles from four right angles "gives the ordinary angles BKC and ELF for I.4" (`mishnah/III/29.md:5`, `:7`).

**Why the step is needed.** Neither proposition says why, in our representation, I.4 cannot take the angles at the centres as they stand where those are greater than two right angles: I.4 compares angles of triangles, and such an angle is no angle of a triangle. III.29's "must" asserts the need without giving it. For the diameters each comes nearer: the bases "are diameters" (III.26's record), and BC "passes through the centre K" (`mishnah/III/29.md:5`), so there is no triangle, though neither record says so. III.27's record, by contrast, says its angles at the centres "are greater than two right angles, which I.23 does not construct and III.26's statement does not speak of" (`review/III/27.toml:9`).

**The bridges.** III.29 names `Prop26.alike` and `angleAtCentre.reflex` in its record (`:40`, `:41`) and at the step on its page (`book/III/29.md:65`). III.26 names `Prop26.alike`, at the step before (`review/III/26.toml:17`; `book/III/26.md:73`), but not `angleAtCentre.reflex`, which its page gives only in the Lean listing (`book/III/26.md:527`) and the list of shared steps (`:607`). Neither names `Tacit.len_add_of_between`, which carries the diameters, save in the Lean listing (`book/III/26.md:522`; `book/III/29.md:140`) and the list of rules each proof rests on (`book/III/26.md:647`; `book/III/29.md:266`). Before #720 III.26's passage said "there are no triangles for I.4" and named `Tacit.len_add_of_between`, as limitations-02 quotes it; the new note dropped both.

**Why editorial.** Every claim made is true, and the bridges are proved and used (`Elements/BookIII/Prop26.lean:492`–`502`; `Prop29.lean:98`–`103`), so this is no "unsupported claim about a representation". Adding the clauses and the names changes no claim. But #704's second way asks for both, in the record and on the page, so this holds #704 for III.26 and III.29.

**Fix (#704).**

1. `review/III/26.toml:23`: for example, "In Euclid's figure I.4 applies to the angles BGC, EHF of the triangles GBC, HEF (`angleAtCentre.within`). Where the angles at A and D are right, the angles at the centres are two right angles, G and H lie on BC and EF, and there are no triangles for I.4: BC and EF are diameters, each two equal radii (`Tacit.len_add_of_between`). Where they are obtuse, the angles at the centres are greater than two right angles, and so no angles of triangles; I.4 takes the angles BGC, EHF that remain when those are taken from four right angles (`angleAtCentre.reflex`, Common Notion 3), a different argument within the statement (Heath, vol. 2, p. 57)."
2. In III.26's route note (`:8`), after "I.4 takes the ordinary angles remaining from four right angles", add "(`angleAtCentre.reflex`), for an angle greater than two right angles is no angle of a triangle".
3. `mishnah/III/26.md:5`, after "I.4 takes the angles BGC, EHF that remain of four right angles": add ", for I.4 compares triangles, and an angle of two right angles or more is no angle of a triangle (`angleAtCentre.reflex`)".
4. `review/III/29.toml:35`, after "which must be subtracted from four right angles before I.4 applies": add ", for I.4 compares angles of triangles, and an angle greater than two right angles is none". In `:41`, for "For semicircles, adding the equal radii gives equal diameters", read "For semicircles, K and L lie on BC and EF, and there are no triangles for I.4: adding the equal radii gives equal diameters (`Tacit.len_add_of_between`)".
5. `mishnah/III/29.md:7`, after "gives the ordinary angles BKC and ELF for I.4": add ", for I.4 compares triangles, and an angle greater than two right angles is no angle of a triangle".

Each record's `text` stamp then goes stale, and each record is read again; III.29's reading can settle finding 5 with it.

### 3. Editorial: III.21 gives as its reason that the completion Heath reports is not needed, not that its departure is

III.21's record and page say why Euclid's printed step does not reach the semicircle and the less segment, and name the bridge (the table above). As their reason for the departure they say "and III.20 doubles BAD and BED in every segment, so Simson's completion is not needed" (`review/III/21.toml:8`; `book/III/21.md:55`); the mishnah, "our proof needs no completion of Simson's" (`mishnah/III/21.md:7`); the gap catalogue, the same (`gaps-book-III.md:202`). That is a reason for a choice. #704's second way asks why the departure "is needed in our representation", and FORMALIZATION speaks of the places "Where the Lean must part from him" (`docs/FORMALIZATION.md:364`).

**Why editorial.** By WORKFLOW's definitions it is no worse. Every claim made is true, the departure is marked where it occurs, and nothing is hidden, unsupported or wrongly attributed. But it holds #704 for III.21, and no rewording alone can meet #704's second way there, for this departure is not needed. Simson's completion, which Heath reports and #704 names, works in our representation; it was our III.21's until 26 October 2026 (`routes-book-III.md:441`–`443`, `:1684`–`1714`).

**What would meet #704.** The choice is the coordinator's, on #704, and the owner's if they wish:

1. **The completion Heath reports from Heron.** The repository gives Heath's words at p. 57: "As in III. 21, if Euclid's proof is to cover all cases, it requires us to take cognisance of 'angles at the centre' which are equal to or greater than two right angles" (`gaps-book-III.md:232`; `mishnah/III/26.md:5`). And III.20's mishnah says that Heath reports from an-Nairīzī, at p. 47, that Heron took III.20 on to the less segment, by the angle at the centre that is left of four right angles, "so III.21 holds in every segment" (`mishnah/III/20.md:3`). That is what our III.21 does. If the page images bear both out (leaves n69 and n59), III.21's step is a completion Heath reports, and #704's first way fits it. The record and the mishnah would then say so, citing those words, in place of "a reading that is ours ... so Simson's completion is not needed". #704 would record a ruling that this completion, not Simson's, which it names, meets its first way. The record would be read again by the other family.
2. **Simson's completion**, Heath's "simplest proof, of many" (vol. 2, p. 49), as #704 names it: a proof change (R2). The route stays `modified` under SCHEMA's rule, since Simson's too argues a real case within the statement another way.

This review recommends the first, which keeps Euclid's two steps in every segment, if Heath's pages bear it out.

### 4. Editorial: Book III's introduction, the routes report and brief 0004 do not yet say what the records say of III.21, III.27 and III.29

- **The introduction.** `mishnah/intro/III.md:17` (`book/III/index.md:25`) tells the changed steps of III.21 and III.26, and nothing of III.27's or III.29's. The generated summary above it names all four (`book/III/index.md:5`).
- **The routes report.** Its last word on III.21 is that "III.21's route is `euclid`: the Lean takes Euclid's two steps for every segment, and III.21 has no passage argued another way, so the schema allows it" (`routes-book-III.md:1802`–`1804`), overtaken by the ruling of 28 October. Its last word on III.27's right angles is that "III.27's proof does not halve it, and still reads its right angles off `Prop24.angle_type`" (`:1883`–`1888`), overtaken now that III.27 halves by III.20 in every case. Its notes of 28 October (`:1903`–`1921`) speak of III.2, III.8, III.26, III.28 and III.29 alone.
- **Brief 0004.** Its list of routes "of its date" gives III.8 "one step changed" (`:707`), III.21 `euclid` (`:714`) and III.26 "one step changed, the congruence of the remainders" (`:716`). Its notes of 28 October (`:261`–`280`) mend III.2, III.8, III.26, III.28 and III.29, but not III.21.

**Why editorial.** Each is a dated account, and the records and the pages, which readers see, are right. But #704 asks that "Book III's introduction and docs/reports/routes-book-III.md say the same as the records".

**Fix (#704).**

1. `mishnah/intro/III.md:17`, after the sentence on III.26 (with finding 1 mended): "III.27 takes Euclid's reductio and halving with two steps changed: where the angles at the circumference are right, the angles at the centres are each two right angles, equal with no reductio, and III.20 halves them; where they are obtuse, the reductio runs on the angles that stand on the circumferences that remain. III.29 takes Euclid's argument with two steps changed: where the circumference is greater than a semicircle, the angles at the centres standing on it, greater than two right angles, are taken from four right angles before I.4."
2. The routes report, a dated note after `:1921`: "III.21's route is `modified` since the coordinator's ruling of 28 October 2026 ([the entry](../decisions/2026-10-28-route-labels-iii20-iii21.md)): in the semicircle and the less segment its doubling by III.20 rests on our angle at the centre. III.27 halves by III.20 in every case: where the angles at A and D are right, the angles at the centres are two right angles each (`angleAtCentre.semicircle`); where they are obtuse, the reductio runs on the angles that stand on the circumferences that remain (`angleAtCentre.reflex`). The sentences above on III.21's route and on III.27's right angles are of their dates."
3. Brief 0004, a dated note after `:280`, for the brief's owner: "III.21's route is `modified` since the coordinator's ruling of 28 October 2026 (#546); the list of routes below is of its date for III.8, III.21 and III.26."

### 5. Not graded: III.29 cites Heath's p. 60 for a step that may be ours

III.29's record says that the angles at the centres standing on the greater circumferences "must be subtracted from four right angles before I.4 applies (Heath, vol. 2, p. 60)" (`review/III/29.toml:35`), and calls the subtraction "an additional step within the statement (Heath, vol. 2, p. 60)" (`:41`). Page 60 prints Euclid's III.29 (`heath/III/29.md:1`, leaf n72) and Heath's note on III.28's diameters (`gaps-book-III.md:244`); the repository cites his notes on III.29 at p. 61 (`gaps-book-III.md:250`, `:253`). If p. 60 says nothing of the subtraction, the two parentheses give our step to Heath, and that is material: "a wrong quotation or attribution". If it does, they stand. This review could not look. A transcription reader with leaf n72 should decide. The fix, if one is needed, is to cite p. 60 for Euclid's figure alone, or to drop the two parentheses (#704, or a new card). Until it is decided, B4 cannot pass: the attribution stands in the statement of a departure B4 lists, and an accepted limitation "never stands in for a defect nobody has looked into".

### 6. Editorial: `review/terms.toml` names III.24 and III.27 for `redundant-hypothesis`, and not III.29

The meaning of `redundant-hypothesis` ends with the records that carry it, "(III.24, III.27)" (`review/terms.toml:58`). III.29's record carries the tag too, new since limitations-02 (`review/III/29.toml:12`), and its page shows it (`book/III/29.md:54`); the table above cites that line for it.

**Why editorial.** The tag is defined, III.29's record and page carry it, and its representation note says what the hypothesis does there; only the list in the meaning falls short.

**Fix.** `review/terms.toml:58`: "(III.24, III.27, III.29)", in a change to that protected file with its decisions entry, beside limitations-01's finding 9. It is no #704 item.

## Verdict

- Book III: fail, held by finding 1.

Finding 1 is material: III.27's right angles at A and D are argued another way within Euclid's statement and declared a further case, so that limitation is not "stated plainly where it occurs". Finding 5 is not graded, for want of the page image; if p. 60 does not bear out III.29's two citations it is material, so B4 cannot pass until it is settled. Findings 2, 3, 4 and 6 are editorial, and so are limitations-01's findings 3, 7, 8 and 9, still open. No blocking finding stands. limitations-02's finding 2 is mended, and its finding 1 for III.26.

No `[limitations]` table is given for `docs/reports/acceptance/book-III.toml`.

**What must change for a pass.**

1. Finding 1 (#704): III.27's passage at "And the angle at A is half of the angle BGC" becomes `different`, the record is read again in full and stamped by a reader of the other family, and the page and the certificate are made again. Or a ruling says why the right case is trivial.
2. Finding 5 (#704, or a new card): a transcription reader reads leaf n72. If p. 60 does not speak of the subtraction, `review/III/29.toml:35` and `:41` cite it for Euclid's figure alone, or drop it, and the record is read again. If it does, the citations stand, and the reader says so on the card.

These two hold B4. When both are done, B4 is read again, at that revision. #704 needs more before B4's list can close it:

3. Finding 2 (#704): III.26's and III.29's records and pages say why the step at I.4 is needed in our representation; III.26's name `angleAtCentre.reflex`, and both name `Tacit.len_add_of_between` for the diameters.
4. Finding 3 (#704): for III.21, a ruling on #704 that the completion Heath reports from Heron (p. 47, as III.20's mishnah gives it), with his remark at p. 57, meets its first way, with the record and the mishnah citing it; or Simson's completion, a proof change.
5. Finding 4 (#704): the introduction and the routes report say what the records say of III.21, III.27 and III.29; brief 0004's dated note goes to the brief's owner (#704, or a new card).
6. limitations-01's findings 3, 7, 8 and 9, editorial and still open, and finding 6, which changes the same protected file as finding 9: a new card, as limitations-02 left the first four. None holds B4.

The verdict is of this revision. A train that changes Book III's records, pages or routes, the fixes above among them, changes what was read.
