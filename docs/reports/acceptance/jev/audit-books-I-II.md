# Jev audit of Books I and II

Brief 0005's stage 6 ([#36](https://github.com/jackChallis/stoicheia/issues/36)) asks a model family that wrote none of Stoicheia to audit the review records. This report records Jev's run and the adjudications for Books I and II, whose 62 records are at the stage `full`. Because neither a pre-run calibration bar nor the raw calibration answers survives, Jev is a secondary signal here and this report does not complete independent acceptance. Jev is TypeSafe's decision model, and we thank TypeSafe warmly for it.

**In short.** Jev agreed with the records on 251 of 293 questions (86%), and on 243 (83%) in both orders of the options. It agreed on all 79 citation questions, and found both defects planted among them. Those citation agreements are not independent confirmation without a passed calibration or fallback review. Correctly checking confidence in both orders sends 90 production answers to adjudication; adding the 15 remaining scope answers that the calibration decision required makes 105 required production adjudications. Ninety-eight are complete. Seven have a source-based Codex pre-review but still await the Claude adjudicator Brief 0005 requires for low-confidence answers, so they do not count. Of the 98 completed rows, the adjudicators found the record right in 96. The two others are figure captions, I.6 and I.26, which draw Euclid's impossible supposition without saying so. Those two readings are among eleven provisional figure readings, and their fixes are listed for later (see [Open](#open)). All 79 citation rows and 41 figure rows outside completed adjudication still need revision-pinned fallback review. The representation and commentary questions missed every defect planted in them, so Jev's agreement on those items is not evidence.

## What was asked, of which model, when

- **Model.** `jev-1.13.0`, a pinned id, which answered every request. The owner [reported in #36](https://github.com/jackChallis/stoicheia/issues/36) that the calibration of 19 October 2026 got 12 of 14 right and found that its scope answers could change when the options were reversed. The original redacted calibration answers and any pre-run accuracy bar are not in this tree or its branch history. The score cannot be checked against raw output or classified as a passed gate.
- **When.** 19 October 2026, Pacific time: 303 requests between 03:56:48 and 03:57:29 UTC on 20 October. The client was [`scripts/audit/jev.py`](../../../../scripts/audit/jev.py), with its order check on, so each choice was asked twice in one request, the second time with its options reversed. The requests carried 1,683,107 input tokens, at most 24,740 in one, and the median latency was 0.13 s.
- **Cost.** The committed responses record 1,683,107 input tokens and 30,915 output tokens. At TypeSafe's [published price](https://typesafe.ai/) of USD 0.042 per million input tokens and free output, their list-price equivalent is USD 0.070690494. This is not an account charge: no billing receipt or console export was preserved, so the actual charged amount remains unverified.
- **What.** The 303 rows of [audit-books-I-II.jsonl](audit-books-I-II.jsonl), written by the historical `scripts/audit/jev_questions.py` at `aca67cc385df6134272613c60c803b2aa9c2f398` from evidence commit `39ae65c21c6b8188c0fa53bf91b6fde3ce3b11a3`. Every state quotes its files exactly, and the generator checks each byte against `git show` of that commit. The record's expected answer stays on this machine: Jev saw the state, the question and, for figures, the image. [The manifest](audit-books-I-II-manifest.json) lists, for each proposition, its rows, proof units, calls and state sizes. Jev's answers are in [audit-books-I-II-jev-1.13.0-2026-10-19.jsonl](audit-books-I-II-jev-1.13.0-2026-10-19.jsonl). The committed [generator-history bundle](audit-books-I-II-generator-history.bundle) makes the historical generator and its later reviewed head retrievable from the evidence revision. The later generator at `e5fb40fcb550ac688f6bd16f0d0c735bc6447e39` corrects evidence and bridge placement; it is not the generator of these preserved audit bytes.

| Item | Question | Rows | Seeded |
|---|---|---:|---:|
| P11 | Does the Lean statement, with its companions and porism, cover the enunciation, and is the record's scope exactly right? | 62 | 2 |
| P12 | Does every proposition a proof unit calls do work, and is any hypothesis used only for show? One row for each main theorem and each companion or porism that calls a proposition. | 79 | 2 |
| P13 | Do the definitions and bridge theorems state the connection between each represented object (`quadArea`, `rect`, `sq`, figures given by their pieces) and Euclid's object? | 28 | 2 |
| P14 | Does what the commentary says about the scope, the route and the Lean it names agree with them? | 62 | 2 |
| P15 | Does Heath's figure, sent as an image, agree with the proof's letters and with its own caption? | 62 | 2 |

Some things were kept out of the states, so that agreement means something. No state carries a record's `[review]` table, fingerprint or passage notes. Citation rows carry no record at all. Figure rows carry the committed caption, which is itself under test, but no record table. Scope rows carry the record's `[statement]` table, since the question is whether it is right.

The ten seeded rows plant a defect in a generated state only, never in a file:

- **Scope:** I.6 made equilateral, and I.5's second conclusion removed.
- **Citations:** an unused call of an unrelated proposition in I.41, and a pointless hypothesis.
- **Representations:** II.4's bridges removed, and the same bridges given an impossible premise.
- **Commentary:** I.39 and I.40, each with one claim reversed.
- **Figures:** I.37 and II.4, each sent another proposition's figure.

Of the 293 states, 124 run past 12,000 characters, chiefly the citation and commentary states, since those quote whole proofs. Jev agreed on 118 of those 124 and on 133 of the other 169, so length did not cost agreement here.

## Agreement

| Item | Rows | Agrees | Agrees in both orders | Answer changed when reversed | Confidence under 0.5 in either order | To adjudication | Seeded defects found |
|---|---:|---:|---:|---:|---:|---:|---:|
| Scope (P11) | 62 | 39 (63%) | 34 | 10 | 46 | 47 | 2 of 2 |
| Citations (P12) | 79 | 79 (100%) | 79 | 0 | 1 | 1 | 2 of 2 |
| Representations (P13) | 28 | 20 (71%) | 18 | 5 | 15 | 18 | 0 of 2 |
| Commentary (P14) | 62 | 62 (100%) | 62 | 0 | 2 | 2 | 0 of 2 |
| Figures (P15) | 62 | 51 (82%) | 50 | 2 | 18 | 22 | 2 of 2 |
| **All** | **293** | **251 (86%)** | **243** | **17** | **82** | **90** | **6 of 10** |

What the figures support:

- **Citations: secondary signal only.** All 79 agree in both orders; 78 have confidence of 0.5 or more in both orders, while I.1's reversed confidence of 0.48 sent it to adjudication. Both planted defects were found. I.1 has only a Codex pre-review pending its required Claude adjudication, and the other 78 have no fallback adjudication. Agreement therefore does not establish that those proof units have no dummy citation or artificial hypothesis use. The helpers' own proofs were not sent.
- **Figures: secondary outside adjudication.** Both planted wrong figures were found. Twenty-two production figure rows went to adjudication, including the eleven provisional readings described below. I.5 remains pending its required Claude adjudication, so 41 figure rows are outside completed adjudication and need fallback review before they count as independent confirmation.
- **Scope: weak evidence alone.** Both planted restrictions were found, but Jev disagreed with 23 records and changed its answer on 10 when the options were reversed. Fifty-nine scope adjudications are complete; I.1, II.9 and II.11 have Codex pre-reviews but await the required Claude adjudication. The completed adjudications, not Jev's agreement, carry this item.
- **Representations and commentary: no evidence from agreement.** Jev called all four planted defects agreement, so its 62 agreements on commentary and 20 on representations show nothing. Those items rest on the adjudicated rows and on the records' own reviews.

## Adjudication

An answer goes to adjudication when it disagrees with the record, has a confidence under 0.5 or no confidence in either order, or changes when the options are reversed. Correcting the scorer to apply the confidence rule to both orders selects 90 production rows and 5 seeded rows; 82 production rows have low confidence in at least one order. The owner's calibration decision in [#36](https://github.com/jackChallis/stoicheia/issues/36) required every scope answer to go to an adjudicator, so 15 high-confidence scope agreements outside the corrected trigger also require review. This makes 105 required production adjudications. Ninety-eight are complete and seven are pending: the rows newly selected on reversed confidence still await Claude, including three scope rows previously pre-reviewed by Codex. Fifty-nine of the 62 scope rows therefore have completed adjudication.

The original adjudicators were fresh, read-only runs of OpenAI's Codex (GPT-6 Astra), which wrote none of the records. Six readers took the rows in groups. Each was told to decide from `heath/`, the Lean, the figures and the commentary alone, and not to open `review/`; it saw the record's claim only as the answer under test. Where a reader disagreed with Jev, the captain (Claude) decided. The captain read the files in full for I.30, recomputed the SVG coordinates for I.46, I.48, II.7 and II.13, and read the statements for I.14, I.27, I.45, II.1 and II.14. For the other rows the captain accepted the reader's cited evidence. A7 is OpenAI Codex (GPT-5) in the later no-mistakes review. It wrote none of the records and read Heath's whole proposition and the whole Lean file for each of the 18 scope rows the original trigger omitted. Its findings remain as source-based pre-reviews. A8 is OpenAI Codex (GPT-5) in the no-mistakes review begun at `f9ef57381dbed6c4b6560638c8922753f73a293a`. It wrote none of the records and pre-reviewed all seven rows newly selected by the corrected trigger against source evidence at `39ae65c21c6b8188c0fa53bf91b6fde3ce3b11a3`, reading the complete Heath proposition and Lean file in each case and rendering I.5's SVG. Three scope rows repeat A7's independent result; the citation, two representation and figure rows are new pre-reviews. A8's findings are preserved below but are not Claude adjudications and do not count as completed verdicts. A9, A10 and A11 are separate cold, read-only OpenAI Codex `gpt-6-astra` fallback reviewers commissioned in the no-mistakes review at `828aa9ba73c071b80478b9684847ead3eac91776`. They wrote none of the records, opened no `review/` file, and each read the complete Heath and Lean files for its five assigned scope rows at the exact evidence revision `39ae65c21c6b8188c0fa53bf91b6fde3ce3b11a3`. Each independently found both Jev and the record right; their source evidence is recorded in the rows below.

The reader for eleven figure rows (I.6 to I.42) did not run: its service had reached its usage limit, which resets on 26 October 2026. The captain read those eleven from the files instead: the SVG's coordinates, Heath's text, the Lean statement and the caption. Those readings are marked provisional, and a Codex reader is still owed them.

| Verdict | Rows |
|---|---:|
| both right | 56 |
| record right, Jev wrong | 40 |
| Jev right, record wrong | 2 |
| both wrong | 0 |
| pending Claude adjudication | 7 |

Of the 40 rows marked "record right, Jev wrong", 36 are a reader's verdict, which the captain accepted. Three are the captain's provisional figure readings (I.14, I.27 and I.33). The last, I.30, is the captain's decision against both Jev and the reader, and its row says why. The two rows marked "Jev right, record wrong" are both provisional.

The seven rows exposed by the corrected trigger have no protocol verdict yet. A8's pre-review found Jev and the record both right on all seven, but Brief 0005 requires Claude to verify every low-confidence answer before it counts. Three overlap the scope rows A7 reviewed. A9, A10 and A11 completed the permitted cold Astra fallback for the other 15 scope-policy rows and independently found Jev and the record both right.

### Completed adjudications and pending rows

Jev's answer is given as chosen, then (after the slash) as chosen with the options reversed. Parentheses give the first confidence, except that rows newly selected on reversed confidence show both confidences in asking order. A1 to A6 are the original Codex readers; A7 and A8 are the later Codex pre-reviewers; A9 to A11 are the cold Astra fallback reviewers described above. Rows marked pending preserve A7's or A8's evidence but do not count in the completed totals.

#### Scope (P11)

| Row | Jev | Record | Review: answer | Verdict | Evidence |
|---|---|---|---|---|---|
| `09-I.1-scope` | fully / fully (0.53 / 0.31) | fully | A7; A8 pre-review: fully; Claude pending | pending Claude adjudication | `Prop1` constructs an equilateral triangle on arbitrary distinct A and B; P only chooses a side and restricts no given object (`Elements/BookI/Prop01.lean:45`). |
| `09-I.2-scope` | fully / beyond (0.40) | fully | A1: fully | both right | `Prop2` takes A anywhere (`Elements/BookI/Prop02.lean:18`); the case A = B is proved at lines 22 to 23. |
| `09-I.3-scope` | beyond / beyond (0.33) | fully | A1: fully | record right, Jev wrong | `hC` and `h` name a genuine lesser straight line; no relative position of the two lines is assumed (`Elements/BookI/Prop03.lean:21`). |
| `09-I.4-scope` | fully / fully (0.87) | fully | A7 pre-review; A9 cold fallback: fully | both right | `Prop4` concludes equality of the base and triangle and both remaining angles (`Elements/BookI/Prop04.lean:23`). |
| `09-I.5-scope` | fully / fully (0.31) | fully | A1: fully | both right | Both conclusions, with the setting-out's angle pairs (`Elements/BookI/Prop05.lean:19`); D and E exist for every triangle by `produce`. |
| `09-I.6-scope` | fully / fully (0.88) | fully | A7 pre-review; A9 cold fallback: fully | both right | For any triangle whose angles at B and C are equal, `Prop6` concludes AB = AC; its exchanged case covers whichever side is supposed greater (`Elements/BookI/Prop06.lean:57`). |
| `09-I.7-scope` | fully / fully (0.21) | fully | A1: fully | both right | The positive uniqueness form of the enunciation (`Elements/BookI/Prop07.lean:256`); every placement of D handled by `Prop7.cases`. |
| `09-I.8-scope` | fully / fully (0.73) | fully | A7 pre-review; A9 cold fallback: fully | both right | The three side equalities of the two triangles give equality of the contained angles (`Elements/BookI/Prop08.lean:24`). |
| `09-I.9-scope` | fully / fully (0.59) | fully | A7 pre-review; A9 cold fallback: fully | both right | `Prop9` constructs F within BAC and proves both equal halves and that they compose the given angle (`Elements/BookI/Prop09.lean:145`). |
| `09-I.10-scope` | fully / fully (0.72) | fully | A7 pre-review; A9 cold fallback: fully | both right | For every finite straight line AB, `Prop10` constructs D strictly between its ends with AD = DB (`Elements/BookI/Prop10.lean:22`). |
| `09-I.11-scope` | fully / fully (0.25) | fully | A1: fully | both right | C anywhere on AB, the case C = A proved at lines 43 to 47 (`Elements/BookI/Prop11.lean:25`). |
| `09-I.12-scope` | fully / fully (0.72) | fully | A7 pre-review; A10 cold fallback: fully | both right | `Prop12` constructs H on AB and proves CH makes a right angle with every other point of the infinite straight line (`Elements/BookI/Prop12.lean:26`). |
| `09-I.13-scope` | fully / fully (0.45) | fully | A1: fully | both right | The sum covers Euclid's disjunction; the equal case is proved right at lines 119 to 122 (`Elements/BookI/Prop13.lean:99`). |
| `09-I.14-scope` | beyond / beyond (0.63) | fully | A1: fully | record right, Jev wrong | `OppositeSidesOf C D A B` formalises "not lying on the same side" for adjacent angles, which Definition I.8 puts off AB (`Elements/BookI/Prop14.lean:26`, `heath/I/front.md:13`). |
| `09-I.15-scope` | fully / fully (0.45) | fully | A1: fully | both right | Both vertical-angle equalities and the porism, `Prop15.porism` (`Elements/BookI/Prop15.lean:44`, `:101`). |
| `09-I.16-scope` | fully / fully (0.61) | fully | A7 pre-review; A10 cold fallback: fully | both right | With BC produced through C to D, `Prop16` concludes ACD is greater than both opposite interior angles (`Elements/BookI/Prop16.lean:61`). |
| `09-I.17-scope` | fully / fully (0.84) | fully | A7 pre-review; A10 cold fallback: fully | both right | `Prop17` states all three choices of two interior angles, not only the pair drawn in Euclid's figure (`Elements/BookI/Prop17.lean:25`). |
| `09-I.18-scope` | fully / fully (0.40) | fully | A1: fully | both right | Arbitrary triangle, conclusion in the right direction (`Elements/BookI/Prop18.lean:24`). |
| `09-I.19-scope` | fully / fully (0.57) | fully | A7 pre-review; A10 cold fallback: fully | both right | The hypothesis makes ABC greater than BCA and the conclusion makes the opposite side AC greater than AB (`Elements/BookI/Prop19.lean:25`). |
| `09-I.20-scope` | fully / fully (0.87) | fully | A7 pre-review; A10 cold fallback: fully | both right | `Prop20` states all three strict triangle inequalities for an arbitrary triangle (`Elements/BookI/Prop20.lean:25`). |
| `09-I.21-scope` | fully / fully (0.52) | fully | A7 pre-review; A11 cold fallback: fully | both right | `InsideTriangle D A B C` is Euclid's meeting within ABC, and `Prop21` gives both the side-sum inequality and the greater contained angle (`Elements/BookI/Prop21.lean:55`). |
| `09-I.22-scope` | beyond / beyond (0.31) | fully | A1: fully | record right, Jev wrong | The three inequalities are Euclid's own condition; `F ≠ E` and P only place the construction (`Elements/BookI/Prop22.lean:121`). |
| `09-I.23-scope` | exactly / exactly (0.28) | fully | A1: fully | record right, Jev wrong | `Triangle D C E` names a rectilineal angle (Definitions I.8 and I.9, `heath/I/front.md:13`); P chooses a side and always exists (`Elements/BookI/Prop23.lean:31`). |
| `09-I.24-scope` | fully / fully (0.61) | fully | A7 pre-review; A11 cold fallback: fully | both right | `Prop24` takes arbitrary triangles and handles F on EG, within DEG, or beyond EG, so its base inequality is not confined to Euclid's drawn case (`Elements/BookI/Prop24.lean:88`). |
| `09-I.25-scope` | fully / fully (0.79) | fully | A7 pre-review; A11 cold fallback: fully | both right | Equal corresponding sides and the greater base give the greater contained angle for arbitrary triangles (`Elements/BookI/Prop25.lean:26`). |
| `09-I.26-scope` | fully / fully (0.72) | fully | A7 pre-review; A11 cold fallback: fully | both right | The disjunction covers a side adjoining the equal angles or a side subtending one of them, and the conclusion includes all remaining sides and the remaining angle (`Elements/BookI/Prop26.lean:22`). |
| `09-I.27-scope` | beyond / beyond (0.56) | fully | A1: fully | record right, Jev wrong | E and F on the transversal, A and D on opposite sides name the alternate angles; meeting is excluded on both sides (`Elements/BookI/Prop27.lean:25`, `:98`, `:107`). |
| `09-I.28-scope` | beyond / beyond (0.56) | fully | A1: fully | record right, Jev wrong | The exact disjunction of the enunciation, each disjunct proved (`Elements/BookI/Prop28.lean:21`, `:33`). |
| `09-I.29-scope` | beyond / beyond (0.47) | fully | A1: fully | record right, Jev wrong | All three conclusions; the auxiliary points exist for any configuration by `AreParallel.figure_alternate` and `AreParallel.figure_interior` (`Elements/BookI/Prop29.lean:30`, `Elements/Figure/Parallels.lean:167`, `:195`). |
| `09-I.30-scope` | beyond / beyond (0.61) | fully | A1, then captain: fully | record right, Jev wrong | The reader chose "restricted beyond": `hC : ¬ Collinear A B C` excludes AB and CD on one straight line, and no convention in the row excuses it. The captain decided otherwise from the files: two straight lines that are one straight line when produced are not two lines parallel to one another, so `hC` names what Euclid's words presuppose (`Elements/BookI/Prop30.lean:75`; the record's comment, `review/I/30.toml:2`, says the same, but a comment is not carried by the audit or the page). |
| `09-I.31-scope` | beyond / beyond (0.36) | fully | A2: fully | record right, Jev wrong | `hA` names the setting a parallel through A needs: a point on BC has none (`Elements/BookI/Prop31.lean:27`). |
| `09-I.32-scope` | fully / fully (0.57) | fully | A7 pre-review; A11 cold fallback: fully | both right | `Prop32` gives both conclusions: the exterior angle equals the two opposite interior angles, and all three interior angles sum to two right angles (`Elements/BookI/Prop32.lean:48`). |
| `09-I.33-scope` | exactly / fully (0.27) | fully | A2: fully | record right, Jev wrong | `hdir : SameSideOf B D A C` formalises "in the same directions" (`Elements/BookI/Prop33.lean:20`). |
| `09-I.34-scope` | fully / fully (0.23) | fully | A2: fully | both right | All five conclusions on the parallelogram ACDB (`Elements/BookI/Prop34.lean:20`). |
| `09-I.35-scope` | beyond / beyond (0.36) | fully | A2: fully | record right, Jev wrong | No order of the opposite sides is assumed; separate, overlapping and touching placements are proved (`Elements/BookI/Prop35.lean:172`, cases at lines 260 to 283). |
| `09-I.36-scope` | fully / fully (0.37) | fully | A2: fully | both right | Equal bases in any position on the common line (`Elements/BookI/Prop36.lean:19`). |
| `09-I.37-scope` | fully / fully (0.49) | fully | A2: fully | both right | Common base and common parallels, A = D admitted (`Elements/BookI/Prop37.lean:27`). |
| `09-I.38-scope` | fully / fully (0.35) | fully | A2: fully | both right | Equal bases anywhere on the common parallel (`Elements/BookI/Prop38.lean:27`). |
| `09-I.39-scope` | fully / exactly (0.27) | fully | A2: fully | both right | `hAD` names the join AD that Heath draws (`Elements/BookI/Prop39.lean:20`, `heath/I/39.md:12`). |
| `09-I.40-scope` | fully / exactly (0.29) | fully | A2: fully | both right | `Prop40.general` drops the adjacency of the bases (`Elements/BookI/Prop40.lean:84`), with `Prop40.join` and `Prop40.special`. |
| `09-I.41-scope` | beyond / beyond (0.36) | fully | A2: fully | record right, Jev wrong | `Collinear A D E` puts E anywhere on the second parallel (`Elements/BookI/Prop41.lean:19`). |
| `09-I.42-scope` | beyond / beyond (0.41) | fully | A2: fully | record right, Jev wrong | The extra conjuncts are outputs of the construction, not restrictions on the given triangle or angle (`Elements/BookI/Prop42.lean:23`). |
| `09-I.43-scope` | exactly / beyond (0.36) | fully | A2: fully | record right, Jev wrong | The betweenness hypotheses describe the parallelograms about the diameter and their complements, as Heath names them (`Elements/BookI/Prop43.lean:73`, `heath/I/43.md:6`). |
| `09-I.44-scope` | beyond / exactly (0.21) | fully | A2: fully | record right, Jev wrong | P chooses a side and always exists (`Elements/BookI/Prop44.lean:87`, `Elements/Figure/Rectangles.lean:39`). |
| `09-I.45-scope` | exactly / exactly (0.35) | fully | A2: fully | record right, Jev wrong | `Prop45.apart` and `Prop45.figure` take any figure in the declared representation (`Elements/BookI/Prop45.lean:327`, `:341`); the representation's limits are the record's, quoted in the row. |
| `09-I.46-scope` | fully / fully (0.37) | fully | A2: fully | both right | A square on any AB, on either side (`Elements/BookI/Prop46.lean:30`). |
| `09-I.47-scope` | exactly / exactly (0.48) | fully | A3: fully | record right, Jev wrong | The outward squares are one placing, carried to every other by `Prop46.square_eq` (`Elements/BookI/Prop47.lean:110`, `Elements/BookI/Prop46.lean:96`), as the schema's I.47 example says. |
| `09-I.48-scope` | beyond / beyond (0.49) | fully | A3: fully | record right, Jev wrong | The squares' sides are placings, not restrictions on the triangle (`Elements/BookI/Prop48.lean:26`). |
| `09-II.1-scope` | beyond / beyond (0.23) | fully | A3: fully | record right, Jev wrong | `Prop1.general` takes any number of segments (`Elements/BookII/Prop01.lean:254`); `Prop1.two` the case of two. |
| `09-II.2-scope` | fully / fully (0.37) | fully | A3: fully | both right | Statement and conclusion as Euclid's (`Elements/BookII/Prop02.lean`). |
| `09-II.3-scope` | fully / fully (0.40) | fully | A3: fully | both right | Statement and conclusion as Euclid's (`Elements/BookII/Prop03.lean`). |
| `09-II.4-scope` | fully / fully (0.49) | fully | A3: fully | both right | Statement and conclusion as Euclid's (`Elements/BookII/Prop04.lean`). |
| `09-II.5-scope` | fully / exactly (0.19) | fully | A3: fully | both right | Statement and conclusion as Euclid's (`Elements/BookII/Prop05.lean`). |
| `09-II.6-scope` | exactly / exactly (0.44) | fully | A3: fully | record right, Jev wrong | Adding beyond A is the theorem with A and B exchanged; no restriction on the added length (`Elements/BookII/Prop06.lean:26`). |
| `09-II.7-scope` | fully / beyond (0.36) | fully | A3: fully | both right | Statement and conclusion as Euclid's (`Elements/BookII/Prop07.lean`). |
| `09-II.8-scope` | fully / fully (0.39) | fully | A3: fully | both right | Statement and conclusion as Euclid's (`Elements/BookII/Prop08.lean`). |
| `09-II.9-scope` | fully / fully (0.56 / 0.33) | fully | A7; A8 pre-review: fully; Claude pending | pending Claude adjudication | C is the equal cut, D is any distinct interior cut, and the proof exchanges A and B to cover either order of C and D (`Elements/BookII/Prop09.lean:33`). |
| `09-II.10-scope` | fully / fully (0.25) | fully | A3: fully | both right | Statement and conclusion as Euclid's (`Elements/BookII/Prop10.lean`). |
| `09-II.11-scope` | fully / fully (0.56 / 0.45) | fully | A7; A8 pre-review: fully; Claude pending | pending Claude adjudication | For arbitrary distinct A and B, `Prop11` constructs H strictly between them and proves the required rectangle equals the square on AH (`Elements/BookII/Prop11.lean:31`). |
| `09-II.12-scope` | beyond / beyond (0.32) | fully | A3: fully | record right, Jev wrong | The foot's external position is proved, not assumed (`Elements/BookII/Prop12.lean:23`, `:50`). |
| `09-II.13-scope` | beyond / exactly (0.33) | fully | A3: fully | record right, Jev wrong | Acute angles at B and C are given in an acute-angled triangle; D within BC is proved (`Elements/BookII/Prop13.lean:47`, `:77`). |
| `09-II.14-scope` | exactly / beyond (0.19) | fully | A3: fully | record right, Jev wrong | `Prop14.apart` and `Prop14.square` take any figure in the declared representation (`Elements/BookII/Prop14.lean:324`, `:364`). |

#### Citations (P12)

| Row | Jev | Record | Review: answer | Verdict | Evidence |
|---|---|---|---|---|---|
| `10-I.1-citations` | all do work / all do work (0.61 / 0.48) | all do work | A8 pre-review: all do work; Claude pending | pending Claude adjudication | The proof calls no proposition. Its two uses of Postulate 3 draw the circles, Postulate 1 names AB for the requested side, the circle-intersection rules supply C, Definition 15 supplies the equal radii, Common Notion 1 closes their equality, and `Prop1.figure` establishes that ABC is a triangle (`Elements/BookI/Prop01.lean:45`). |

#### Representations (P13) and commentary (P14)

| Row | Jev | Record | Review: answer | Verdict | Evidence |
|---|---|---|---|---|---|
| `11-II.1-representation` | bridge stated / bridge stated (0.57 / 0.45) | bridge stated | A8 pre-review: bridge stated; Claude pending | pending Claude adjudication | `Rectangle.contained` and `Rectangle.eq_rect` connect drawn rectangles to `rect`; `Prop1.general` states the arbitrary ordered segmentation using `InOrder.between_end`, `segments`, `endOf` and `Magnitude.sum` (`Elements/BookII/Rectangles.lean:81`, `Elements/BookII/Prop01.lean:248`). |
| `11-I.34-representation` | bridge stated / bridge stated (0.47) | bridge stated | A6: bridge stated | both right | `Parallelogram`, `quadArea` (`Elements/Foundations/Phrases.lean:48`, `:53`) with `Prop34.bisect` (`Elements/BookI/Prop34.lean:100`). |
| `11-I.35-representation` | missing / missing (0.44) | bridge stated | A6: bridge stated | record right, Jev wrong | `Parallelogram.cross` and `Parallelogram.quadArea_rotate` state that the measure does not depend on the diameter (`Elements/Figure/Parallelograms.lean:189`, `:200`). |
| `11-I.36-representation` | missing / bridge stated (0.32) | bridge stated | A6: bridge stated | record right, Jev wrong | As I.35: `Elements/Figure/Parallelograms.lean:189`, `:200`. |
| `11-I.37-representation` | missing / missing (0.61) | bridge stated | A6: bridge stated | record right, Jev wrong | As I.35, with `Prop34.bisect` for the halves (`Elements/BookI/Prop34.lean:100`). |
| `11-I.38-representation` | missing / missing (0.64) | bridge stated | A6: bridge stated | record right, Jev wrong | As I.37. |
| `12-I.38-commentary` | agrees / agrees (0.31) | agrees | A6: agrees | both right | The mishnah's account matches the route and statements (`mishnah/I/38.md`, `Elements/BookI/Prop38.lean:27`). |
| `12-I.40-commentary` | agrees / agrees (0.48) | agrees | A6: agrees | both right | The mishnah's account of the companions and the direct end matches (`mishnah/I/40.md`, `Elements/BookI/Prop40.lean:84`). |
| `11-I.41-representation` | missing / missing (0.88) | bridge stated | A6: bridge stated | record right, Jev wrong | As I.37. |
| `11-I.42-representation` | bridge stated / bridge stated (0.41) | bridge stated | A6: bridge stated | both right | As I.37. |
| `11-I.43-representation` | missing / bridge stated (0.32) | bridge stated | A6: bridge stated | record right, Jev wrong | As I.35. |
| `11-I.44-representation` | bridge stated / missing (0.43) | bridge stated | A6: bridge stated | both right | As I.35. |
| `11-I.45-representation` | bridge stated / bridge stated (0.40) | bridge stated | A6: bridge stated | both right | `Rectilineal.toApart`, `Rectilineal.area_toApart`, `Fitted.fan` (`Elements/Figure/Rectilineal.lean:79`, `:85`, `Elements/BookI/Prop45.lean:709`); the record names what is not proved. |
| `11-I.46-representation` | missing / bridge stated (0.29) | bridge stated | A6: bridge stated | record right, Jev wrong | `Prop46.square_eq` (`Elements/BookI/Prop46.lean:96`) with the area bundle. |
| `11-I.47-representation` | bridge stated / missing (0.35) | bridge stated | A6: bridge stated | both right | As I.46. |
| `11-I.48-representation` | missing / missing (0.53) | bridge stated | A6: bridge stated | record right, Jev wrong | As I.46. |
| `11-II.9-representation` | bridge stated / bridge stated (0.47) | bridge stated | A6: bridge stated | both right | `Rectangle.contained`, `Rectangle.eq_rect`, `Square.eq_sq`, `Square.described` (`Elements/BookII/Rectangles.lean`). |
| `11-II.10-representation` | bridge stated / bridge stated (0.39) | bridge stated | A6: bridge stated | both right | As II.9. |
| `11-II.13-representation` | bridge stated / bridge stated (0.52 / 0.40) | bridge stated | A8 pre-review: bridge stated; Claude pending | pending Claude adjudication | `Rectangle.contained`, `Rectangle.eq_rect`, `Square.eq_sq` and `Square.described` state the required rectangle and square connections; `Prop13` uses `rect` and `sq` through II.7 and the bridged square form of I.47 (`Elements/BookII/Rectangles.lean:81`, `Elements/BookII/Prop13.lean:83`). |
| `11-II.14-representation` | bridge stated / bridge stated (0.33) | bridge stated | A6: bridge stated | both right | As II.9, with the `Apart` bridges of I.45. |

#### Figures (P15)

| Row | Jev | Record | Review: answer | Verdict | Evidence |
|---|---|---|---|---|---|
| `13-I.5-figure` | agrees / agrees (0.51 / 0.49) | agrees | A8 pre-review: agrees; Claude pending | pending Claude adjudication | The symmetric coordinates make AB equal to AC; B–F–D and C–G–E have the required order, BC, FC and GB are drawn, and the marked base and under-base angles match Heath's proof (`figures/I/05.svg`: A (200, 32), B (150, 132), C (250, 132), F (110, 212), G (290, 212)). |
| `13-I.6-figure` | disagrees / disagrees (0.43) | agrees | captain (provisional): disagrees | Jev right, record wrong | The caption says DB is cut off equal to AC, but the drawn DB is 150 units against AC's 214 (`figures/I/06.svg`: A (200, 36), B (90, 220), C (310, 220), D (167, 91.2)). The impossible supposition makes that unavoidable, but unlike I.14's and I.40's captions this one does not say so. |
| `13-I.14-figure` | disagrees / disagrees (0.53) | agrees | captain (provisional): agrees | record right, Jev wrong | The caption names the one incompatibility, C, B and E not in a straight line (`book/I/14.md:23`); everything else agrees. |
| `13-I.21-figure` | agrees / agrees (0.41) | agrees | captain (provisional): agrees | both right | D within ABC, BD produced to E on AC (`figures/I/21.svg`). |
| `13-I.26-figure` | disagrees / disagrees (0.62) | agrees | captain (provisional): disagrees | Jev right, record wrong | Heath makes BG equal to DE and BH equal to EF; the drawn triangles are equal (AB = DE = 172.6), so BG is 120.8 and BH 108 against DE's 172.6 and EF's 150 (`figures/I/26.svg`). The caption names the suppositions but not this consequence. |
| `13-I.27-figure` | disagrees / disagrees (0.35) | agrees | captain (provisional): agrees | record right, Jev wrong | The caption discloses that the alternate angles supposed equal appear unequal (`book/I/27.md:23`); letters and incidences agree. |
| `13-I.29-figure` | agrees / agrees (0.34) | agrees | captain (provisional): agrees | both right | AGH, GHD and EGB marked as the caption says (`figures/I/29.svg`). |
| `13-I.33-figure` | disagrees / disagrees (0.27) | agrees | captain (provisional): agrees | record right, Jev wrong | AB and CD equal and parallel, AC and BD joining extremities in the same directions, BC joined (`figures/I/33.svg`, `heath/I/33.md:6`). |
| `13-I.34-figure` | agrees / agrees (0.41) | agrees | captain (provisional): agrees | both right | ACDB a parallelogram with diameter BC (`figures/I/34.svg`). |
| `13-I.39-figure` | agrees / agrees (0.41) | agrees | captain (provisional): agrees | both right | The caption names the impossible supposition and the unequal drawn areas (`book/I/39.md:23`). |
| `13-I.40-figure` | agrees / agrees (0.41) | agrees | captain (provisional): agrees | both right | The caption names the impossible supposition and the unequal drawn areas (`book/I/40.md:23`). |
| `13-I.42-figure` | agrees / agrees (0.41) | agrees | captain (provisional): agrees | both right | BE = EC, the angle CEF equal to D's (both about 57 degrees), A on FG produced beyond F (`figures/I/42.svg`). |
| `13-I.45-figure` | disagrees / disagrees (0.35) | agrees | A5: agrees | record right, Jev wrong | Every incidence and order of the proof holds in the SVG's coordinates; the caption says H is drawn on D, as the Lean has it (`figures/I/45.svg`, `book/I/45.md:23`, `Elements/BookI/Prop45.lean:74`). |
| `13-I.46-figure` | disagrees / disagrees (0.27) | agrees | A5: agrees | record right, Jev wrong | ADEB is a square with D on AC (`figures/I/46.svg`: A (140, 260), B (260, 260), D (140, 140), E (260, 140)). |
| `13-I.47-figure` | disagrees / agrees (0.31) | agrees | A5: agrees | record right, Jev wrong | Squares outward, C, A, G and B, A, H in line, AL parallel to BD (`figures/I/47.svg`, `heath/I/47.md:11`). |
| `13-I.48-figure` | disagrees / disagrees (0.88) | agrees | A5: agrees | record right, Jev wrong | AD at right angles to AC, AD = AB, D opposite B (`figures/I/48.svg`: A (200, 215), B (270, 215), D (130, 215)). |
| `13-II.3-figure` | agrees / disagrees (0.38) | agrees | A5: agrees | both right | CDEB a square, AF parallel to CD (`figures/II/03.svg`). |
| `13-II.7-figure` | disagrees / disagrees (0.38) | agrees | A5: agrees | record right, Jev wrong | The squares on CB and on AC at opposite corners, the gnomon KLM round the rest (`figures/II/07.svg`, `Elements/BookII/Prop07.lean:41`). |
| `13-II.10-figure` | agrees / agrees (0.37) | agrees | A5: agrees | both right | E, B, G and F, D, G in line, as proved (`figures/II/10.svg`, `Elements/BookII/Prop10.lean:113`, `:119`). |
| `13-II.12-figure` | agrees / agrees (0.35) | agrees | A5: agrees | both right | BAC obtuse, D on CA produced (`figures/II/12.svg`). |
| `13-II.13-figure` | disagrees / disagrees (0.83) | agrees | A5: agrees | record right, Jev wrong | All three angles acute (at A, AB · AC = 8900 > 0), D within BC (`figures/II/13.svg`, `book/II/13.md:23`). |
| `13-II.14-figure` | agrees / agrees (0.48) | agrees | A5: agrees | both right | B, G, E, F in order, H on the semicircle, GH² = 63² + 84² = 105² (`figures/II/14.svg`). |

In the scope table, "beyond" stands for "restricted beyond what the note says" and "exactly" for "restricted, exactly as the note says"; "missing" stands for "bridge missing or inadequate".

#### Seeded rows

A seeded row's right answer is the defect planted, so no reader is needed: the verdict is by construction.

| Row | Planted | Jev | Verdict |
|---|---|---|---|
| `09-I.5-scope-seeded-2` | the second conclusion removed | beyond / beyond (0.61) | found |
| `09-I.6-scope-seeded-1` | a hypothesis making the triangle equilateral | beyond / beyond (0.52) | found |
| `13-I.37-figure-seeded-1` | I.1's figure sent for I.37 | disagrees / disagrees (0.97) | found |
| `12-I.39-commentary-seeded-1` | one claim of the commentary reversed | agrees / agrees (0.88) | missed |
| `12-I.40-commentary-seeded-2` | one claim of the commentary reversed | agrees / agrees (0.49) | missed |
| `10-I.41-citations-seeded-1` | an unused call of an unrelated proposition | a dummy citation / a dummy citation (0.95) | found |
| `10-I.41-citations-seeded-2` | a pointless hypothesis, used only in an unused binding | an artificial hypothesis use / an artificial hypothesis use (0.44) | found, with confidence under 0.5 |
| `11-II.4-representation-seeded-1` | the bridge signatures removed | bridge stated / bridge stated (0.33) | missed |
| `11-II.4-representation-seeded-2` | an impossible premise added to each bridge | bridge stated / bridge stated (0.64) | missed |
| `13-II.4-figure-seeded-2` | I.31's figure sent for II.4 | disagrees / disagrees (1.00) | found |

## Fixes

**No record is wrong in its scope, its representations or its commentary**, on any completed adjudication. A8's pre-review found I.1's citation row right, but Claude has not adjudicated it, so all 79 citation rows remain a secondary Jev signal.

Two figure captions are wrong, on the captain's provisional reading. Each draws Euclid's impossible supposition, as Heath's figure does. Neither says so, as the captions of I.14, I.27, I.39 and I.40 do, and the row's question excuses only an incompatibility the caption names. The fix in each is a `note` in the record's `[figure]` table, which the page prints after the case:

- **I.6** ([review/I/06.toml](../../../../review/I/06.toml), `[figure]`): "Like Heath's, this figure draws Euclid's impossible supposition: with the angles at B and C equal, AB cannot be greater than AC, so the drawn DB is shorter than AC."
- **I.26** ([review/I/26.toml](../../../../review/I/26.toml), `[figure]`): "Like Heath's, this figure draws Euclid's impossible suppositions on triangles drawn equal, so the drawn BG is shorter than DE and BH shorter than EF."

Neither fix is made here. Both are listed for a later branch, after an independent Codex reader has confirmed or overturned all eleven provisional figure readings. That later branch must have each changed record re-read and stamped by a reviewer who wrote none of it.

One improvement, not a fault: the reason I.30's record is `full` lives in a TOML comment ([review/I/30.toml](../../../../review/I/30.toml), lines 2 and 3), which neither the page nor this audit carries. Both Jev and its reader read `hC` as a restriction for want of it. A `[statement]` `note` saying the same would put the reason where a reader looks.

## What this audit does not show

- That the proofs are sound: Lean's kernel shows that. Jev read proofs and the signatures of what they call, not the helpers' own proofs.
- That the commentary quotes and attributes exactly, or is in the common voice: P14's question asked only about its account of the mathematics, and that question missed both planted defects.
- That every representation's bridge is adequate: that question missed both planted defects.
- A judgement free of the records: scope and representation rows had to carry the record's claim, since that claim is what they test.
- That Jev passed a calibration gate: no contemporaneous bar or raw calibration response is preserved.
- That the 79 citation rows or the 41 figure rows outside completed adjudication have independent acceptance: they have no completed fallback review.

## Open

1. A Claude adjudicator for the seven rows newly selected by reversed-order confidence: `09-I.1-scope`, `09-II.9-scope`, `09-II.11-scope`, `10-I.1-citations`, `11-II.1-representation`, `11-II.13-representation` and `13-I.5-figure`. A8's source reviews remain preliminary until then.
2. The coordinator must approve and land the correction and behavioral self-test for the protected file `scripts/audit/jev.py` as a separate tooling prerequisite, with a new `docs/briefs/0002-decisions.md` line explicitly naming that file and its both-order confidence regression coverage. That landed prerequisite must then be merged into this branch, and the scoring instructions below pinned to its revision. No approval, decision line or landed prerequisite is available at this revision; the audit branch cannot land before them.
3. Recover and commit the original redacted calibration response and verifiable evidence of the bar fixed before the first request, then decide whether the reported 12 of 14 cleared it. Repository history and #36 preserve only the question set and the owner's summary. If that evidence cannot be recovered, Jev remains secondary.
4. Give the 79 citation rows and 41 figure rows outside completed adjudication revision-pinned fallback review before claiming independent acceptance.
5. Recover the account's billing evidence and record the actual audit charge in its billed currency. The committed usage proves only the USD 0.070690494 public-list-price equivalent.
6. An independent Codex reader for the eleven figure rows read provisionally by the captain, then the I.6 and I.26 caption fixes in a later branch, with each changed record re-read and stamped by a reviewer who wrote none of it.
7. The I.30 note, if the editors want it.
8. Sharper representation and commentary questions, which must find their planted defects before their agreement counts, then a new calibration for both.
9. Book III's audit, after Book III's records reach the stage `full` (train C6).

## Reproducing it

```sh
source_root=$(git rev-parse --show-toplevel)
repro_root=$(mktemp -d)
trap 'rm -rf "$repro_root"' EXIT
git clone --no-checkout https://github.com/jackChallis/stoicheia.git "$repro_root/stoicheia"
git -C "$repro_root/stoicheia" fetch \
  "$source_root/docs/reports/acceptance/jev/audit-books-I-II-generator-history.bundle" \
  refs/heads/tooling/jev-questions:refs/remotes/audit/tooling/jev-questions
git -C "$repro_root/stoicheia" checkout --detach aca67cc385df6134272613c60c803b2aa9c2f398
cp "$source_root/docs/reports/acceptance/jev/audit-books-I-II.jsonl" \
  "$repro_root/stoicheia/docs/reports/acceptance/jev/"
cp "$source_root/docs/reports/acceptance/jev/audit-books-I-II-manifest.json" \
  "$repro_root/stoicheia/docs/reports/acceptance/jev/"
cp "$source_root/docs/reports/acceptance/jev/audit-books-I-II-jev-1.13.0-2026-10-19.jsonl" \
  "$repro_root/stoicheia/docs/reports/acceptance/jev/"
cd "$repro_root/stoicheia"
python3 scripts/audit/jev_questions.py \
  --commit 39ae65c21c6b8188c0fa53bf91b6fde3ce3b11a3 --check
python3 scripts/audit/jev.py run docs/reports/acceptance/jev/audit-books-I-II.jsonl --dry-run
python3 "$source_root/scripts/audit/jev.py" score \
  docs/reports/acceptance/jev/audit-books-I-II-jev-1.13.0-2026-10-19.jsonl
python3 - <<'PY'
import hashlib, json, pathlib

directory = pathlib.Path("docs/reports/acceptance/jev")
questions = (directory / "audit-books-I-II.jsonl").read_bytes()
digest = hashlib.sha256(questions).hexdigest()
manifest = json.loads((directory / "audit-books-I-II-manifest.json").read_text())
answers = [json.loads(line) for line in
           (directory / "audit-books-I-II-jev-1.13.0-2026-10-19.jsonl").read_text().splitlines()]
assert digest == "01b71b7481e4a97e47632456ccf5689c7799fbcaadc53723ffe5e27009dfbc90"
assert manifest["questions_sha256"] == "sha256:" + digest
assert {row["input_sha256"] for row in answers} == {digest}
assert {row["input_rows"] for row in answers} == {303}
print("Questions, manifest and 303 answers share", digest)
PY
```

The clone supplies the evidence revision and the exact imported modules. The thin Git bundle, whose prerequisite is that evidence revision, supplies the historical generator commit and the later reviewed generator without relying on an unpushed branch. The first Python command regenerates the rows twice in the historical checkout and compares both generated files byte for byte with the committed artifacts. The second builds every request with the historical client and sends nothing. The third uses the corrected scorer from `source_root`, needs no key and selects 95 rows: 90 production rows and 5 seeded rows. The other 15 required rows are the high-confidence scope-policy rows, which the scorer does not select. At this revision that scorer is still the unapproved branch copy described in Open item 2; after the separate tooling prerequisite lands and is merged, `source_root` must be pinned to that approved tooling revision. The fourth ties the question bytes and manifest to every answer's `input_sha256`. Sending the questions needs TypeSafe's key, as the client's docstring explains. Running the later generator at `e5fb40fcb550ac688f6bd16f0d0c735bc6447e39` is a new audit input, not a reproduction of this one.
