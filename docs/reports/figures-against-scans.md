# Euclid's figures against Heath's scans

Each of Euclid's figures, `figures/<book>/NN.svg`, was set beside Heath's printed figure on the scan leaf that its source note names (`heath/<book>/NN.md`), and read as STYLE, section 7, asks a figure to be read: as geometry. This is the record of that reading, for [#30](https://github.com/jackChallis/stoicheia/issues/30), made at `89c5da4` on 19 October 2026, with what it mended and what it leaves to the owners of other files.

## How each figure was read

Heath's figure was cut from the leaf's image (the Internet Archive's `thirteenbookseu02heibgoog` for Books I and II, `thirteenbookseu00heibgoog` for Book III, as STYLE, section 5, gives them) and set beside ours, rendered with `rsvg-convert -w 700 figures/<book>/NN.svg`. Each pair was read for what the proof uses: which points lie on which straight lines and circles, the order of points along a line, which side of a line a point falls, where lines cross, which case of several is drawn, and every letter at its point. Three kinds of difference are kept apart:

- **As Heath's:** the same points in the same relations, under the same letters. Proportions may differ (a triangle acute where his is obtuse), since no proof here turns on them.
- **Laid out otherwise:** the same figure turned or reflected. Nothing the proof uses changes, so the record needs no note; the table says so, for a reader who opens the scan.
- **Departs:** a point placed otherwise than Heath places it, a line or a point he draws left out, or an impossible supposition drawn without saying so. Each is mended to match the scan, or said in the figure note (STYLE, section 7), whose line the record's owner writes.

Of the 99, 64 are as Heath's with nothing to add; each of the rest has its word in the table, whether it is as Heath's with a remark, laid out otherwise, or departs.

## Mended on this branch

- **III.24:** F stood at the crossing of the two curves, where the awry segment CGD meets CFD, and G at the top of the awry curve. Heath puts G at the crossing and F on CFD alone; so does the figure now, so that F names a point of CFD only.
- **III.1, III.2, III.12, III.32:** each theorem covers several cases, and each record now names the one its figure draws, which the page's caption gives (acceptance item P8): G off AB and off CE (III.1), the centre D off AB (III.2), C and D apart on FG (III.12), D on F's side of BA and apart from A (III.32), each as in Heath's figure.
- **III.1, III.19:** each figure draws an impossible supposition, a centre off the straight line on which the proof finds it, as Heath's does, and each record's note now says so.

## Proposed to the owners of other files

Book I's records are being taken to the stage `full` by their owner, and III.24's moves with stage 3, so these lines are proposed, not written:

- **I.13** `[figure]`: `case = "AB leaning towards C, as in Heath's figure"` (acceptance item P8).
- **I.7** `[figure]`: `note = "Like Heath's, this figure draws the impossible supposition: C and D on one side of AB, with CA equal to DA and CB equal to DB."`
- **I.8** `[figure]`: `note = "Like Heath's, this figure draws the impossible supposition: BA, AC falling beside ED, DF, as EG, GF."`
- **I.14** `[figure]`: `note = "Like Heath's, this figure draws the impossible supposition: BE in a straight line with CB, and so drawn apart from BD."`
- **I.27** `[figure]`: `note = "Like Heath's, this figure draws the impossible supposition: AB and CD, produced, meeting at G."`
- **I.4** `[figure]`: `note = "Heath's figure also draws the base bent below EF, the impossible case of two straight lines enclosing a space; ours leaves it out."`
- **III.24** `[figure]`: `note = "Like Heath's, this figure draws the impossible supposition: the segment falling awry, as CGD, and meeting CFD at G."`

I.6 and I.26 draw a reductio's supposition too (AB greater than AC; AB unequal to DE), but as a figure that could exist, so a note there is the records' owner's judgment. The acceptance report's P4 finding at I.45 (a departure the mishnah discloses and the record does not declare) is not a figure's, and is left to I.45's record and mishnah.

## Book I

| | Heath's figure | Reading |
|---|---|---|
| [I.1](../../book/I/01.md) | [n261](https://archive.org/download/thirteenbookseu02heibgoog/page/n261.jpg) | As Heath's. |
| [I.2](../../book/I/02.md) | [n264](https://archive.org/download/thirteenbookseu02heibgoog/page/n264.jpg) | As Heath's in its order and sides; Heath's BC runs up from B, ours down to the right, and his triangle DAB is smaller. |
| [I.3](../../book/I/03.md) | [n266](https://archive.org/download/thirteenbookseu02heibgoog/page/n266.jpg) | As Heath's; F, which only names the circle, stands at its lower left, Heath's at its lower right. |
| [I.4](../../book/I/04.md) | [n267](https://archive.org/download/thirteenbookseu02heibgoog/page/n267.jpg) | Departs, and says so nowhere yet: Heath also draws the base bent below EF, the impossible case of two straight lines enclosing a space, which ours leaves out (a note is proposed below). Otherwise as Heath's, ABC on the left and DEF on the right. |
| [I.5](../../book/I/05.md) | [n271](https://archive.org/download/thirteenbookseu02heibgoog/page/n271.jpg) | As Heath's. |
| [I.6](../../book/I/06.md) | [n275](https://archive.org/download/thirteenbookseu02heibgoog/page/n275.jpg) | As Heath's. |
| [I.7](../../book/I/07.md) | [n278](https://archive.org/download/thirteenbookseu02heibgoog/page/n278.jpg) | As Heath's. It draws an impossible supposition, and says so nowhere yet (a note is proposed below). |
| [I.8](../../book/I/08.md) | [n281](https://archive.org/download/thirteenbookseu02heibgoog/page/n281.jpg) | As Heath's, ABC on the left and DEF on the right. It draws an impossible supposition, G, and says so nowhere yet (a note is proposed below). |
| [I.9](../../book/I/09.md) | [n284](https://archive.org/download/thirteenbookseu02heibgoog/page/n284.jpg) | As Heath's. |
| [I.10](../../book/I/10.md) | [n287](https://archive.org/download/thirteenbookseu02heibgoog/page/n287.jpg) | As Heath's. |
| [I.11](../../book/I/11.md) | [n289](https://archive.org/download/thirteenbookseu02heibgoog/page/n289.jpg) | As Heath's. |
| [I.12](../../book/I/12.md) | [n291](https://archive.org/download/thirteenbookseu02heibgoog/page/n291.jpg) | As Heath's. |
| [I.13](../../book/I/13.md) | [n295](https://archive.org/download/thirteenbookseu02heibgoog/page/n295.jpg) | Reflected: C on the left and D on the right. AB leans towards C in both, the case Heath draws, which the record does not yet name (the line is proposed below). |
| [I.14](../../book/I/14.md) | [n296](https://archive.org/download/thirteenbookseu02heibgoog/page/n296.jpg) | As Heath's. It draws an impossible supposition, BE in a straight line with CB, and says so nowhere yet (a note is proposed below). |
| [I.15](../../book/I/15.md) | [n297](https://archive.org/download/thirteenbookseu02heibgoog/page/n297.jpg) | As Heath's. |
| [I.16](../../book/I/16.md) | [n299](https://archive.org/download/thirteenbookseu02heibgoog/page/n299.jpg) | As Heath's. |
| [I.17](../../book/I/17.md) | [n302](https://archive.org/download/thirteenbookseu02heibgoog/page/n302.jpg) | As Heath's in its order and sides; Heath's triangle is obtuse at B, ours acute. |
| [I.18](../../book/I/18.md) | [n303](https://archive.org/download/thirteenbookseu02heibgoog/page/n303.jpg) | As Heath's in its order and sides; Heath's triangle is obtuse at B, ours acute. |
| [I.19](../../book/I/19.md) | [n304](https://archive.org/download/thirteenbookseu02heibgoog/page/n304.jpg) | Turned: Heath sets B on the left and AC upright on the right. |
| [I.20](../../book/I/20.md) | [n306](https://archive.org/download/thirteenbookseu02heibgoog/page/n306.jpg) | As Heath's. |
| [I.21](../../book/I/21.md) | [n309](https://archive.org/download/thirteenbookseu02heibgoog/page/n309.jpg) | As Heath's. |
| [I.22](../../book/I/22.md) | [n312](https://archive.org/download/thirteenbookseu02heibgoog/page/n312.jpg) | As Heath's in its order and sides; of the three given straight lines Heath's A is the longest, ours B. |
| [I.23](../../book/I/23.md) | [n314](https://archive.org/download/thirteenbookseu02heibgoog/page/n314.jpg) | As Heath's. |
| [I.24](../../book/I/24.md) | [n316](https://archive.org/download/thirteenbookseu02heibgoog/page/n316.jpg) | Reflected: Heath sets C on the left of ABC and G on the left of DEF, where ours has B and E. F is below EG in both, the case Heath draws. |
| [I.25](../../book/I/25.md) | [n319](https://archive.org/download/thirteenbookseu02heibgoog/page/n319.jpg) | As Heath's. |
| [I.26](../../book/I/26.md) | [n322](https://archive.org/download/thirteenbookseu02heibgoog/page/n322.jpg) | As Heath's. |
| [I.27](../../book/I/27.md) | [n327](https://archive.org/download/thirteenbookseu02heibgoog/page/n327.jpg) | As Heath's in what it shows, AB and CD meeting at G; Heath draws them as parallels bent to meet, ours as straight lines. It draws an impossible supposition and says so nowhere yet (a note is proposed below). |
| [I.28](../../book/I/28.md) | [n330](https://archive.org/download/thirteenbookseu02heibgoog/page/n330.jpg) | As Heath's. The figure lower on the leaf, in Heath's note on Proclus, has EF slanting the other way. |
| [I.29](../../book/I/29.md) | [n331](https://archive.org/download/thirteenbookseu02heibgoog/page/n331.jpg) | As Heath's. |
| [I.30](../../book/I/30.md) | [n334](https://archive.org/download/thirteenbookseu02heibgoog/page/n334.jpg) | As Heath's. |
| [I.31](../../book/I/31.md) | [n336](https://archive.org/download/thirteenbookseu02heibgoog/page/n336.jpg) | As Heath's. |
| [I.32](../../book/I/32.md) | [n337](https://archive.org/download/thirteenbookseu02heibgoog/page/n337.jpg) | As Heath's. |
| [I.33](../../book/I/33.md) | [n343](https://archive.org/download/thirteenbookseu02heibgoog/page/n343.jpg) | As Heath's. |
| [I.34](../../book/I/34.md) | [n344](https://archive.org/download/thirteenbookseu02heibgoog/page/n344.jpg) | As Heath's. |
| [I.35](../../book/I/35.md) | [n347](https://archive.org/download/thirteenbookseu02heibgoog/page/n347.jpg) | As Heath's. |
| [I.36](../../book/I/36.md) | [n351](https://archive.org/download/thirteenbookseu02heibgoog/page/n351.jpg) | As Heath's. |
| [I.37](../../book/I/37.md) | [n352](https://archive.org/download/thirteenbookseu02heibgoog/page/n352.jpg) | As Heath's. |
| [I.38](../../book/I/38.md) | [n353](https://archive.org/download/thirteenbookseu02heibgoog/page/n353.jpg) | As Heath's. |
| [I.39](../../book/I/39.md) | [n356](https://archive.org/download/thirteenbookseu02heibgoog/page/n356.jpg) | Departs, and says so: AE is drawn level, as the proof supposes; Heath draws AD level. |
| [I.40](../../book/I/40.md) | [n357](https://archive.org/download/thirteenbookseu02heibgoog/page/n357.jpg) | Departs, and says so: F between C and D, with AF level, as the proof supposes. |
| [I.41](../../book/I/41.md) | [n358](https://archive.org/download/thirteenbookseu02heibgoog/page/n358.jpg) | As Heath's. |
| [I.42](../../book/I/42.md) | [n359](https://archive.org/download/thirteenbookseu02heibgoog/page/n359.jpg) | As Heath's. |
| [I.43](../../book/I/43.md) | [n360](https://archive.org/download/thirteenbookseu02heibgoog/page/n360.jpg) | As Heath's. |
| [I.44](../../book/I/44.md) | [n362](https://archive.org/download/thirteenbookseu02heibgoog/page/n362.jpg) | As Heath's. |
| [I.45](../../book/I/45.md) | [n365](https://archive.org/download/thirteenbookseu02heibgoog/page/n365.jpg) | Departs, and says so: H is drawn on D, as the Lean has it; Heath draws the parallelogram apart. |
| [I.46](../../book/I/46.md) | [n367](https://archive.org/download/thirteenbookseu02heibgoog/page/n367.jpg) | As Heath's. |
| [I.47](../../book/I/47.md) | [n369](https://archive.org/download/thirteenbookseu02heibgoog/page/n369.jpg) | As Heath's. |
| [I.48](../../book/I/48.md) | [n388](https://archive.org/download/thirteenbookseu02heibgoog/page/n388.jpg) | As Heath's. |

## Book II

| | Heath's figure | Reading |
|---|---|---|
| [II.1](../../book/II/01.md) | [n395](https://archive.org/download/thirteenbookseu02heibgoog/page/n395.jpg) | As Heath's. |
| [II.2](../../book/II/02.md) | [n396](https://archive.org/download/thirteenbookseu02heibgoog/page/n396.jpg) | As Heath's. |
| [II.3](../../book/II/03.md) | [n398](https://archive.org/download/thirteenbookseu02heibgoog/page/n398.jpg) | As Heath's. |
| [II.4](../../book/II/04.md) | [n399](https://archive.org/download/thirteenbookseu02heibgoog/page/n399.jpg) | As Heath's. |
| [II.5](../../book/II/05.md) | [n402](https://archive.org/download/thirteenbookseu02heibgoog/page/n402.jpg) | As Heath's. |
| [II.6](../../book/II/06.md) | [n406](https://archive.org/download/thirteenbookseu02heibgoog/page/n406.jpg) | As Heath's. |
| [II.7](../../book/II/07.md) | [n408](https://archive.org/download/thirteenbookseu02heibgoog/page/n408.jpg) | As Heath's, with his H and N, which his text does not name (an exception of S16). |
| [II.8](../../book/II/08.md) | [n410](https://archive.org/download/thirteenbookseu02heibgoog/page/n410.jpg) | As Heath's. |
| [II.9](../../book/II/09.md) | [n412](https://archive.org/download/thirteenbookseu02heibgoog/page/n412.jpg) | As Heath's. |
| [II.10](../../book/II/10.md) | [n415](https://archive.org/download/thirteenbookseu02heibgoog/page/n415.jpg) | As Heath's. |
| [II.11](../../book/II/11.md) | [n422](https://archive.org/download/thirteenbookseu02heibgoog/page/n422.jpg) | As Heath's. |
| [II.12](../../book/II/12.md) | [n424](https://archive.org/download/thirteenbookseu02heibgoog/page/n424.jpg) | As Heath's. |
| [II.13](../../book/II/13.md) | [n426](https://archive.org/download/thirteenbookseu02heibgoog/page/n426.jpg) | As Heath's. |
| [II.14](../../book/II/14.md) | [n429](https://archive.org/download/thirteenbookseu02heibgoog/page/n429.jpg) | As Heath's. |

## Book III

| | Heath's figure | Reading |
|---|---|---|
| [III.1](../../book/III/01.md) | [n18](https://archive.org/download/thirteenbookseu00heibgoog/page/n18.jpg) | As Heath's. The case it draws is now named (G off AB and off CE), and the note says it draws the impossible supposition, a centre G off CE. |
| [III.2](../../book/III/02.md) | [n20](https://archive.org/download/thirteenbookseu00heibgoog/page/n20.jpg) | As Heath's. The case it draws is now named (the centre D off AB); the note on the impossible supposition was there. |
| [III.3](../../book/III/03.md) | [n22](https://archive.org/download/thirteenbookseu00heibgoog/page/n22.jpg) | As Heath's. |
| [III.4](../../book/III/04.md) | [n23](https://archive.org/download/thirteenbookseu00heibgoog/page/n23.jpg) | As Heath's. |
| [III.5](../../book/III/05.md) | [n24](https://archive.org/download/thirteenbookseu00heibgoog/page/n24.jpg) | As Heath's, and its note says it draws the impossible supposition. |
| [III.6](../../book/III/06.md) | [n25](https://archive.org/download/thirteenbookseu00heibgoog/page/n25.jpg) | As Heath's, and its note says it draws the impossible supposition. |
| [III.7](../../book/III/07.md) | [n26](https://archive.org/download/thirteenbookseu00heibgoog/page/n26.jpg) | As Heath's. |
| [III.8](../../book/III/08.md) | [n30](https://archive.org/download/thirteenbookseu00heibgoog/page/n30.jpg) | As Heath's. |
| [III.9](../../book/III/09.md) | [n33](https://archive.org/download/thirteenbookseu00heibgoog/page/n33.jpg) | As Heath's. |
| [III.10](../../book/III/10.md) | [n35](https://archive.org/download/thirteenbookseu00heibgoog/page/n35.jpg) | As Heath's, and its note says it draws the impossible supposition. |
| [III.11](../../book/III/11.md) | [n36](https://archive.org/download/thirteenbookseu00heibgoog/page/n36.jpg) | As Heath's, and its note says it draws the impossible supposition. |
| [III.12](../../book/III/12.md) | [n40](https://archive.org/download/thirteenbookseu00heibgoog/page/n40.jpg) | As Heath's. The case it draws is now named (C and D apart on FG); the note on the impossible supposition was there. |
| [III.13](../../book/III/13.md) | [n44](https://archive.org/download/thirteenbookseu00heibgoog/page/n44.jpg) | As Heath's, and its note says it draws the impossible supposition. |
| [III.14](../../book/III/14.md) | [n47](https://archive.org/download/thirteenbookseu00heibgoog/page/n47.jpg) | As Heath's. |
| [III.15](../../book/III/15.md) | [n48](https://archive.org/download/thirteenbookseu00heibgoog/page/n48.jpg) | As Heath's. |
| [III.16](../../book/III/16.md) | [n50](https://archive.org/download/thirteenbookseu00heibgoog/page/n50.jpg) | Departs, and says so: G within the circle and H beyond it, as the proof finds them. Its record belongs to the lane moving III.16 into the edition. |
| [III.17](../../book/III/17.md) | [n55](https://archive.org/download/thirteenbookseu00heibgoog/page/n55.jpg) | As Heath's. |
| [III.18](../../book/III/18.md) | [n56](https://archive.org/download/thirteenbookseu00heibgoog/page/n56.jpg) | As Heath's. |
| [III.19](../../book/III/19.md) | [n57](https://archive.org/download/thirteenbookseu00heibgoog/page/n57.jpg) | As Heath's. The note now says it draws the impossible supposition, a centre F off CA. |
| [III.20](../../book/III/20.md) | [n58](https://archive.org/download/thirteenbookseu00heibgoog/page/n58.jpg) | As Heath's. |
| [III.21](../../book/III/21.md) | [n61](https://archive.org/download/thirteenbookseu00heibgoog/page/n61.jpg) | As Heath's. |
| [III.22](../../book/III/22.md) | [n64](https://archive.org/download/thirteenbookseu00heibgoog/page/n64.jpg) | As Heath's. |
| [III.23](../../book/III/23.md) | [n64](https://archive.org/download/thirteenbookseu00heibgoog/page/n64.jpg) | As Heath's. |
| [III.24](../../book/III/24.md) | [n66](https://archive.org/download/thirteenbookseu00heibgoog/page/n66.jpg) | Mended here: F stood where the two curves cross and G at the top of the awry one; Heath puts G at the crossing and F on CFD alone, and so does ours now. It draws the segment falling awry, an impossible supposition (a note is proposed to its record's owner). |
| [III.25](../../book/III/25.md) | [n67](https://archive.org/download/thirteenbookseu00heibgoog/page/n67.jpg), [n68](https://archive.org/download/thirteenbookseu00heibgoog/page/n68.jpg) | As Heath's, his three figures side by side. Its record belongs to the lane moving III.25 into the edition. |
| [III.26](../../book/III/26.md) | [n69](https://archive.org/download/thirteenbookseu00heibgoog/page/n69.jpg) | As Heath's. |
| [III.27](../../book/III/27.md) | [n70](https://archive.org/download/thirteenbookseu00heibgoog/page/n70.jpg) | As Heath's. |
| [III.28](../../book/III/28.md) | [n71](https://archive.org/download/thirteenbookseu00heibgoog/page/n71.jpg) | As Heath's. |
| [III.29](../../book/III/29.md) | [n72](https://archive.org/download/thirteenbookseu00heibgoog/page/n72.jpg) | As Heath's. |
| [III.30](../../book/III/30.md) | [n73](https://archive.org/download/thirteenbookseu00heibgoog/page/n73.jpg) | As Heath's. |
| [III.31](../../book/III/31.md) | [n74](https://archive.org/download/thirteenbookseu00heibgoog/page/n74.jpg) | As Heath's. Its record, which is to name the case drawn, belongs to the lane moving III.31 into the edition. |
| [III.32](../../book/III/32.md) | [n78](https://archive.org/download/thirteenbookseu00heibgoog/page/n78.jpg) | As Heath's. The case it draws is now named (D on F's side of BA and apart from A). |
| [III.33](../../book/III/33.md) | [n79](https://archive.org/download/thirteenbookseu00heibgoog/page/n79.jpg), [n80](https://archive.org/download/thirteenbookseu00heibgoog/page/n80.jpg), [n81](https://archive.org/download/thirteenbookseu00heibgoog/page/n81.jpg) | As Heath's, his three figures side by side (acute, right, obtuse). |
| [III.34](../../book/III/34.md) | [n83](https://archive.org/download/thirteenbookseu00heibgoog/page/n83.jpg) | As Heath's. |
| [III.35](../../book/III/35.md) | [n83](https://archive.org/download/thirteenbookseu00heibgoog/page/n83.jpg), [n84](https://archive.org/download/thirteenbookseu00heibgoog/page/n84.jpg) | As Heath's: the chords through the centre, and the chords not through it. |
| [III.36](../../book/III/36.md) | [n86](https://archive.org/download/thirteenbookseu00heibgoog/page/n86.jpg) | As Heath's: the secant through the centre, and the secant not through it. |
| [III.37](../../book/III/37.md) | [n88](https://archive.org/download/thirteenbookseu00heibgoog/page/n88.jpg) | As Heath's. |
