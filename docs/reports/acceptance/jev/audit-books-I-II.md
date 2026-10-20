# Jev audit of Books I and II

Brief 0005's stage 6 ([#36](https://github.com/jackChallis/stoicheia/issues/36)) asks a model family that wrote none of Stoicheia to audit the review records. This is that audit for Books I and II, whose 62 records are at the stage `full`. The cold reviewers' finding it answers: "No record in any book is signed off by a human or a model family outside the authoring Claude/Codex crews." Jev is TypeSafe's decision model, and we thank TypeSafe warmly for it.

**In short.** Jev agreed with the records on 251 of 293 questions (86%), and on 243 (83%) in both orders of the options. It agreed on all 79 citation questions, and found both defects planted among them. Of the 83 answers sent to adjudication, the adjudicators found the record right in 81. The two others are figure captions, I.6 and I.26, which draw Euclid's impossible supposition without saying so. Those two readings are provisional, and their fixes are not yet made (see [Open](#open)). The representation and commentary questions missed every defect planted in them, so Jev's agreement on those items is not evidence.

## What was asked, of which model, when

- **Model.** `jev-1.13.0`, a pinned id, which answered every request. The calibration of 19 October 2026 with this model got 12 of 14 right, and found its scope answers could change when the options were reversed.
- **When.** 19 October 2026, Pacific time: 303 requests between 03:56:48 and 03:57:29 UTC on 20 October. The client was [`scripts/audit/jev.py`](../../../../scripts/audit/jev.py), with its order check on, so each choice was asked twice in one request, the second time with its options reversed. The requests carried 1,683,107 input tokens, at most 24,740 in one, and the median latency was 0.13 s.
- **What.** The 303 rows of [audit-books-I-II.jsonl](audit-books-I-II.jsonl), written by `scripts/audit/jev_questions.py` (on `tooling/jev-questions`, which lands first) from commit `39ae65c2`. Every state quotes its files exactly, and the generator checks each byte against `git show` of that commit. The record's expected answer stays on this machine: Jev saw the state, the question and, for figures, the image. [The manifest](audit-books-I-II-manifest.json) lists, for each proposition, its rows, proof units, calls and state sizes. Jev's answers are in [audit-books-I-II-jev-1.13.0-2026-10-19.jsonl](audit-books-I-II-jev-1.13.0-2026-10-19.jsonl).

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

| Item | Rows | Agrees | Agrees in both orders | Answer changed when reversed | Confidence under 0.5 | To adjudication | Seeded defects found |
|---|---:|---:|---:|---:|---:|---:|---:|
| Scope (P11) | 62 | 39 (63%) | 34 | 10 | 40 | 44 | 2 of 2 |
| Citations (P12) | 79 | 79 (100%) | 79 | 0 | 0 | 0 | 2 of 2 |
| Representations (P13) | 28 | 20 (71%) | 18 | 5 | 12 | 16 | 0 of 2 |
| Commentary (P14) | 62 | 62 (100%) | 62 | 0 | 2 | 2 | 0 of 2 |
| Figures (P15) | 62 | 51 (82%) | 50 | 2 | 17 | 21 | 2 of 2 |
| **All** | **293** | **251 (86%)** | **243** | **17** | **71** | **83** | **6 of 10** |

What the figures support:

- **Citations: strong evidence.** All 79 agree, in both orders and with confidence of 0.5 or more, and both planted defects were found. No proof unit in Books I and II has a dummy citation or an artificial hypothesis use, on Jev's reading of the proofs and the signatures of what they call. The helpers' own proofs were not sent.
- **Figures: good evidence.** Both planted wrong figures were found. Eleven answers disagreed, and nine of those were Jev's mistakes; the other two are the captions under [Fixes](#fixes).
- **Scope: weak evidence alone.** Both planted restrictions were found, but Jev disagreed with 23 records and changed its answer on 10 when the options were reversed. On adjudication every one of those records was right. The adjudicated rows carry this item, not Jev's agreement.
- **Representations and commentary: no evidence from agreement.** Jev called all four planted defects agreement, so its 62 agreements on commentary and 20 on representations show nothing. Those items rest on the adjudicated rows and on the records' own reviews.

## Adjudication

An answer went to adjudication when it disagreed with the record, had a confidence under 0.5, or changed when the options were reversed. That was 83 of the record rows, and 5 seeded rows.

The adjudicators were fresh, read-only runs of OpenAI's Codex (GPT-6 Astra), which wrote none of the records. Six readers took the rows in groups. Each was told to decide from `heath/`, the Lean, the figures and the commentary alone, and not to open `review/`; it saw the record's claim only as the answer under test. Where a reader disagreed with Jev, the captain (Claude) decided. The captain read the files in full for I.30, recomputed the SVG coordinates for I.46, I.48, II.7 and II.13, and read the statements for I.14, I.27, I.45, II.1 and II.14. For the other rows the captain accepted the reader's cited evidence.

The reader for eleven figure rows (I.6 to I.42) did not run: its service had reached its usage limit, which resets on 26 October 2026. The captain read those eleven from the files instead: the SVG's coordinates, Heath's text, the Lean statement and the caption. Those readings are marked provisional, and a Codex reader is still owed them.

| Verdict | Rows |
|---|---:|
| both right | 41 |
| record right, Jev wrong | 40 |
| Jev right, record wrong | 2 |
| both wrong | 0 |

Of the 40 rows marked "record right, Jev wrong", 36 are a reader's verdict, which the captain accepted. Three are the captain's provisional figure readings (I.14, I.27 and I.33). The last, I.30, is the captain's decision against both Jev and the reader, and its row says why. The two rows marked "Jev right, record wrong" are both provisional.

### Every adjudication

Jev's answer is given as chosen, then (after the slash) as chosen with the options reversed, with its confidence. A1 to A6 are the six Codex readers.

#### Scope (P11)

| Row | Jev | Record | Adjudicator: answer | Verdict | Evidence |
|---|---|---|---|---|---|
| `09-I.2-scope` | fully / beyond (0.40) | fully | A1: fully | both right | `Prop2` takes A anywhere (`Elements/BookI/Prop02.lean:18`); the case A = B is proved at lines 22 to 23. |
| `09-I.3-scope` | beyond / beyond (0.33) | fully | A1: fully | record right, Jev wrong | `hC` and `h` name a genuine lesser straight line; no relative position of the two lines is assumed (`Elements/BookI/Prop03.lean:21`). |
| `09-I.5-scope` | fully / fully (0.31) | fully | A1: fully | both right | Both conclusions, with the setting-out's angle pairs (`Elements/BookI/Prop05.lean:19`); D and E exist for every triangle by `produce`. |
| `09-I.7-scope` | fully / fully (0.21) | fully | A1: fully | both right | The positive uniqueness form of the enunciation (`Elements/BookI/Prop07.lean:256`); every placement of D handled by `Prop7.cases`. |
| `09-I.11-scope` | fully / fully (0.25) | fully | A1: fully | both right | C anywhere on AB, the case C = A proved at lines 43 to 47 (`Elements/BookI/Prop11.lean:25`). |
| `09-I.13-scope` | fully / fully (0.45) | fully | A1: fully | both right | The sum covers Euclid's disjunction; the equal case is proved right at lines 119 to 122 (`Elements/BookI/Prop13.lean:99`). |
| `09-I.14-scope` | beyond / beyond (0.63) | fully | A1: fully | record right, Jev wrong | `OppositeSidesOf C D A B` formalises "not lying on the same side" for adjacent angles, which Definition I.8 puts off AB (`Elements/BookI/Prop14.lean:26`, `heath/I/front.md:13`). |
| `09-I.15-scope` | fully / fully (0.45) | fully | A1: fully | both right | Both vertical-angle equalities and the porism, `Prop15.porism` (`Elements/BookI/Prop15.lean:44`, `:101`). |
| `09-I.18-scope` | fully / fully (0.40) | fully | A1: fully | both right | Arbitrary triangle, conclusion in the right direction (`Elements/BookI/Prop18.lean:24`). |
| `09-I.22-scope` | beyond / beyond (0.31) | fully | A1: fully | record right, Jev wrong | The three inequalities are Euclid's own condition; `F ≠ E` and P only place the construction (`Elements/BookI/Prop22.lean:121`). |
| `09-I.23-scope` | exactly / exactly (0.28) | fully | A1: fully | record right, Jev wrong | `Triangle D C E` names a rectilineal angle (Definitions I.8 and I.9, `heath/I/front.md:13`); P chooses a side and always exists (`Elements/BookI/Prop23.lean:31`). |
| `09-I.27-scope` | beyond / beyond (0.56) | fully | A1: fully | record right, Jev wrong | E and F on the transversal, A and D on opposite sides name the alternate angles; meeting is excluded on both sides (`Elements/BookI/Prop27.lean:25`, `:98`, `:107`). |
| `09-I.28-scope` | beyond / beyond (0.56) | fully | A1: fully | record right, Jev wrong | The exact disjunction of the enunciation, each disjunct proved (`Elements/BookI/Prop28.lean:21`, `:33`). |
| `09-I.29-scope` | beyond / beyond (0.47) | fully | A1: fully | record right, Jev wrong | All three conclusions; the auxiliary points exist for any configuration by `AreParallel.figure_alternate` and `AreParallel.figure_interior` (`Elements/BookI/Prop29.lean:30`, `Elements/Figure/Parallels.lean:167`, `:195`). |
| `09-I.30-scope` | beyond / beyond (0.61) | fully | A1, then captain: fully | record right, Jev wrong | The reader chose "restricted beyond": `hC : ¬ Collinear A B C` excludes AB and CD on one straight line, and no convention in the row excuses it. The captain decided otherwise from the files: two straight lines that are one straight line when produced are not two lines parallel to one another, so `hC` names what Euclid's words presuppose (`Elements/BookI/Prop30.lean:75`; the record's comment, `review/I/30.toml:2`, says the same, but a comment is not carried by the audit or the page). |
| `09-I.31-scope` | beyond / beyond (0.36) | fully | A2: fully | record right, Jev wrong | `hA` names the setting a parallel through A needs: a point on BC has none (`Elements/BookI/Prop31.lean:27`). |
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
| `09-II.10-scope` | fully / fully (0.25) | fully | A3: fully | both right | Statement and conclusion as Euclid's (`Elements/BookII/Prop10.lean`). |
| `09-II.12-scope` | beyond / beyond (0.32) | fully | A3: fully | record right, Jev wrong | The foot's external position is proved, not assumed (`Elements/BookII/Prop12.lean:23`, `:50`). |
| `09-II.13-scope` | beyond / exactly (0.33) | fully | A3: fully | record right, Jev wrong | Acute angles at B and C are given in an acute-angled triangle; D within BC is proved (`Elements/BookII/Prop13.lean:47`, `:77`). |
| `09-II.14-scope` | exactly / beyond (0.19) | fully | A3: fully | record right, Jev wrong | `Prop14.apart` and `Prop14.square` take any figure in the declared representation (`Elements/BookII/Prop14.lean:324`, `:364`). |

#### Representations (P13) and commentary (P14)

| Row | Jev | Record | Adjudicator: answer | Verdict | Evidence |
|---|---|---|---|---|---|
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
| `11-II.14-representation` | bridge stated / bridge stated (0.33) | bridge stated | A6: bridge stated | both right | As II.9, with the `Apart` bridges of I.45. |

#### Figures (P15)

| Row | Jev | Record | Adjudicator: answer | Verdict | Evidence |
|---|---|---|---|---|---|
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

**No record is wrong in its scope, its citations, its representations or its commentary**, on any adjudicated row.

Two figure captions are wrong, on the captain's provisional reading. Each draws Euclid's impossible supposition, as Heath's figure does. Neither says so, as the captions of I.14, I.27, I.39 and I.40 do, and the row's question excuses only an incompatibility the caption names. The fix in each is a `note` in the record's `[figure]` table, which the page prints after the case:

- **I.6** ([review/I/06.toml](../../../../review/I/06.toml), `[figure]`): "Like Heath's, this figure draws Euclid's impossible supposition: with the angles at B and C equal, AB cannot be greater than AC, so the drawn DB is shorter than AC."
- **I.26** ([review/I/26.toml](../../../../review/I/26.toml), `[figure]`): "Like Heath's, this figure draws Euclid's impossible suppositions on triangles drawn equal, so the drawn BG is shorter than DE and BH shorter than EF."

Neither fix is made yet. A record's fix is made through Codex in this branch, and the record is then re-read and stamped by a Codex reader who wrote none of it. Codex reached its usage limit during this audit and cannot run before 26 October 2026, so both fixes wait for it, after a Codex reader has confirmed or overturned the provisional readings.

One improvement, not a fault: the reason I.30's record is `full` lives in a TOML comment ([review/I/30.toml](../../../../review/I/30.toml), lines 2 and 3), which neither the page nor this audit carries. Both Jev and its reader read `hC` as a restriction for want of it. A `[statement]` `note` saying the same would put the reason where a reader looks.

## What this audit does not show

- That the proofs are sound: Lean's kernel shows that. Jev read proofs and the signatures of what they call, not the helpers' own proofs.
- That the commentary quotes and attributes exactly, or is in the common voice: P14's question asked only about its account of the mathematics, and that question missed both planted defects.
- That every representation's bridge is adequate: that question missed both planted defects.
- A judgement free of the records: scope and representation rows had to carry the record's claim, since that claim is what they test.

## Open

1. A Codex reader for the eleven figure rows read provisionally by the captain, then the I.6 and I.26 fixes through Codex, with each record re-read and stamped by a Codex reader who wrote none of it. Codex can run again from 26 October 2026.
2. The I.30 note, if the editors want it.
3. Sharper representation and commentary questions, which must find their planted defects before their agreement counts, then a new calibration for both.
4. Book III's audit, after Book III's records reach the stage `full` (train C6).

## Reproducing it

```sh
python3 scripts/audit/jev_questions.py --commit 39ae65c21c6b8188c0fa53bf91b6fde3ce3b11a3 --check
python3 scripts/audit/jev.py run docs/reports/acceptance/jev/audit-books-I-II.jsonl --dry-run
python3 scripts/audit/jev.py score docs/reports/acceptance/jev/audit-books-I-II-jev-1.13.0-2026-10-19.jsonl
```

The first regenerates the rows twice and compares them with the files. The second builds every request and sends nothing. The third needs no key. Sending the questions needs TypeSafe's key, as the client's docstring explains.
