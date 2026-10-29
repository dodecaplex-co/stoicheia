# Heath's text against the scans

*28 October 2026. The transcriptions read are those of main `20d14b0a3`; `heath/` has not changed since `7103f442a` (26 October 2026), save one stop in III.16, mended after this reading (note 4). The page images were fetched from the Internet Archive on 28 October 2026, and their checksums are given below. This report is the committed record of the check, for [#551](https://github.com/dodecaplex-co/stoicheia/issues/551).*

Each file of `heath/`, the 99 propositions of Books I to III and the three books' front matter, was read line by line against the page images of the leaves its source comment names, from its first words to its last ("Q. E. D.", "Q. E. F.", or as the file ends). The leaves are the Internet Archive's scans that [STYLE, section 5](../STYLE.md#5-heaths-text-and-quotations), names: [thirteenbookseu02heibgoog](https://archive.org/details/thirteenbookseu02heibgoog) for volume 1 (Books I and II), where page N is leaf N + 20, and [thirteenbookseu00heibgoog](https://archive.org/details/thirteenbookseu00heibgoog) for volume 2 (Books III to IX; Book III is read here), where page N is leaf N + 12.

**Result.** Every line of every file agrees with the print wherever the print is legible. Two marks that the scans do not settle could change the text: one word in I.11 (note 1) and one stop in III.16 (note 4). A second copy of the 1908 printing settles the stop in III.16, and the file now reads a colon there. Four more places are read through damaged or faint print, and the scan alone does not settle them, though nothing on it contradicts the file: the words under a blot in I.17 (note 3), the last stop of I.48 (note 5), a comma in III.36 (note 6) and one in II.9 (note 7). Nothing else has been mended: the transcription stands as it was, and the word of note 1 is left as it is, since one copy cannot settle it.

## How the text was read

Six readers, each an instance of Claude Opus 5.5 (independent readers AU-h551-1 to AU-h551-6), took a run of files each: Book I's front matter and I.1 to I.16; I.17 to I.32; I.33 to I.48; Book II's front matter and II.1 to II.14; Book III's front matter and III.1 to III.18; III.19 to III.37. None of them made the transcriptions. Each read the leaves at full resolution, cut into overlapping bands with closer crops wherever a mark was unclear, and judged every line of the file against the print. A word diff against the OCR of the same leaves (made with tesseract) directed the eye; it was not taken as evidence, and every entry in it turned out to be OCR noise.

Counted as a difference: any word or spelling, any punctuation mark, a reference in square brackets, its content and its place after its clause, Heath's or Heiberg's square brackets round words, the italics of the enunciation and of Heath's emphasis, a capital, a word or clause left out or added, and the order of words. Not counted, since `heath/` follows them: STYLE (sections 4 and 5) names the paragraphs, the upright letters, the form of a reference and straight quotes; the rest are the transcription's own practice, which STYLE does not name, as note 2 says of I.10's brace: one sentence or clause per paragraph; the full stop after a heading ("PROPOSITION 1.") dropped; line breaks and end-of-line hyphens joined; Heath's italic letters set upright; margin line numbers, running heads, page numbers and signature marks left out; small capitals written as plain words ("PORISM."); the spacing inside a reference ("[C. N. 3]" as "[C.N. 3]") and the thin space Heath sets before a semicolon or colon; straight quotes. Each source comment was checked too: the pages it names agree with the numbers printed on those leaves, where a number is printed (Book I's opening page, p. 153, and Book II's, p. 370, print none, and are placed by the pagination of the leaves beside them), the proposition begins and ends on them, and its figure is on the leaf named. Each other comment in a file was checked against the print where the print can settle it (note 8).

## Checking it yourself

Each leaf's image is at `https://archive.org/download/<item>/page/n<leaf>.jpg`. Its SHA-256, in the table at the end, was taken from the file as the Internet Archive serves it on 28 October 2026. The 166 leaves named in the source comments matched the copies fetched on 22 October 2026; the two further leaves used for note 8, and the second copy's leaf used for note 4, were fetched and checked on 28 October alone. For example:

```sh
curl -sL https://archive.org/download/thirteenbookseu02heibgoog/page/n264.jpg | shasum -a 256
# 81d50e28a2122f7ba6f57771658b2a63f946e420b8a18ca13edc44042bc53b75
```

Then set the file beside the leaf, as the tables below pair them.

## Notes

1. **I.11, line 22 of `heath/I/11.md`: "and CF is common,".** On n289 (p. 269) no "and" is printed: the line begins at the indent of "For, since DC is equal to CE," with a small stray mark touching the C of CF, and the space where "and" would stand is blank. Another Internet Archive item, [bub_gb_UhgPAAAAIAAJ](https://archive.org/details/bub_gb_UhgPAAAAIAAJ) (p. 269 at its leaf n281), shows the line the same way, but it is no second witness: it is the same Google Books scan (UhgPAAAAIAAJ), and has the same blots elsewhere (I.17's on p. 282). No scan of a second copy of the 1908 printing of volume 1 could be found on 28 October 2026: the Internet Archive and Wikimedia Commons hold only this Google scan of it, and HathiTrust's search could not be reached. The second edition of 1926 ([bwb_S0-AHZ-704_1](https://archive.org/details/bwb_S0-AHZ-704_1), read only in its OCR) prints "and CF is common,", as the file has it. Whether the 1908 printing dropped the word, or this copy lost it, one copy cannot settle. Taking the word out would change the `--` line at `Elements/BookI/Prop11.lean:72`, which waits for approval (WORKFLOW, section 2); so the file stands, and the question goes to the coordinator.
2. **I.10 and I.11 (n287, n289).** The scan has lost the left edge of the column on several lines. Every word can be read from the letters that survive ("constructed", "straight", "been", "bisected", "CD", the C of "C on it"), but for note 1. On n287 the reference in I.10's "[I. 4]" (line 24 of the file) prints with a brace for its closing bracket, "[I. 4}"; the file writes "[I. 4]". That is a convention applied in this reading, not one STYLE names.
3. **I.17 (n302).** An ink blot covers "less", the comma after "right angles" and the "w" of "as well" in the sentence "Similarly we can prove that the angles BAC, ACB are also less than two right angles, and so are the angles CAB, ABC as well." (line 24), and a streak runs through the comma between ABC and BCA on line 22. What survives fits the file, and the 1926 edition's OCR reads line 24 word for word as the file does. That supports the file's reading, but it is another printing, and does not show the marks of the 1908 one: those under the blot stay unverified on this scan.
4. **III.16, line 21: "two right angles: which is impossible."** On n50 (p. 38) the mark has two round dots spaced like a colon's and a third, fainter dot below, where a semicolon's tail runs. The file, and its comment, read a semicolon, the 1926 edition's OCR ([bwb_S0-AHZ-704_2](https://archive.org/details/bwb_S0-AHZ-704_2), its volume 2) a colon (Heath's usual mark before "which is impossible", as on line 43 of the same file). n50 does not settle it. A second copy of the 1908 printing does: [euclid-the-thirteen-books-of-the-elements-vol.-2](https://archive.org/details/euclid-the-thirteen-books-of-the-elements-vol.-2), uploaded to the Internet Archive on 1 March 2026 behind a cover of the second edition, has the 1908 title leaf at n1, and that leaf bears a library's stamp, "National ... University Library", which the copy scanned by Google lacks. At its leaf n45 (p. 38; SHA-256 in the table below) it prints a plain colon, two equal dots with no tail. The coordinator ruled on 28 October 2026 that the file takes the colon, as the print reads ([the entry](../decisions/2026-10-28-iii16-colon.md)). So `heath/III/16.md` and its comment now read a colon, and so does the `--` line at `Elements/BookIII/Prop16.lean:90`.
5. **I.48 (n389).** After the D of "Q. E. D." there is only a faint speck, much lighter than the stops after Q and E: it may be a weakly printed full stop, as the file has it, or a blemish, and the scan does not settle which.
6. **III.36, line 51 (n87).** The mark after "at the point F" is a comma with a dot above it; read as a comma, as the file's comment says and as the matching clause on line 21 has it, though the scan alone does not settle it beyond doubt.
7. **II.9, line 39 (n412).** The mark after "angle", the last line of p. 392, is a dot with a faint tail; the file reads a comma, as its comment says, and the sentence runs on at the top of p. 393; the leaf alone does not settle whether the mark is a comma or a full stop.
8. **Comments that go beyond their leaves.** II.4's comment quotes Heath's note on p. 381, and III.31's his note on p. 64: both quotations were checked against those leaves (n401 and n76, added to the table below) and are exact. Three comments say whose brackets or numbers Heath prints: I.4's ("Heiberg's brackets marking an interpolated passage"), I.15's ("Heath (after Heiberg) brackets it as probably interpolated"; Heath's note on p. 278 discusses the Porism's genuineness without naming Heiberg) and Book I's front matter's ("their numbers in Heiberg's list"). The brackets and numbers are printed as the comments say; whose they are, the leaves named do not state, so those clauses are not checked here. I.38's, I.39's and III.1's comments cite Heath's notes on their neighbours' leaves (n352, n357, n20); the review of this report checked them there, and they are exact.
9. **Book II's front matter (n390).** The leaf prints no page number (p. 370, by the rule of leaf and page, and by n389's 369); and "contained" and "gnomon", the terms Definitions II.1 and II.2 define, are set in heavier type, which the file gives plain, as it gives Heath's other settings.

Specks and pencil marks on the leaves that are not print (volume 1's n323, n330, n405, n415, n416, n423, n429; volume 2's n58, n78) were read as such and not counted.

## The files
### Book I

| | Pages | Leaves | Against the scan |
|---|---|---|---|
| [Book I, front matter](../../heath/I/front.md) | pp. 153–155 | n173, n174, n175 | Agrees (note 8) |
| [I.1](../../heath/I/01.md) | pp. 241–242 | n261, n262 | Agrees |
| [I.2](../../heath/I/02.md) | p. 244 | n264 | Agrees |
| [I.3](../../heath/I/03.md) | pp. 246–247 | n266, n267 | Agrees |
| [I.4](../../heath/I/04.md) | pp. 247–248 | n267, n268 | Agrees (note 8) |
| [I.5](../../heath/I/05.md) | pp. 251–252 | n271, n272 | Agrees |
| [I.6](../../heath/I/06.md) | pp. 255–256 | n275, n276 | Agrees |
| [I.7](../../heath/I/07.md) | pp. 258–259 | n278, n279 | Agrees |
| [I.8](../../heath/I/08.md) | pp. 261–262 | n281, n282 | Agrees |
| [I.9](../../heath/I/09.md) | p. 264 | n284 | Agrees |
| [I.10](../../heath/I/10.md) | p. 267 | n287 | Agrees (note 2) |
| [I.11](../../heath/I/11.md) | p. 269 | n289 | Agrees but for one word, unsettled (notes 1, 2) |
| [I.12](../../heath/I/12.md) | pp. 270–271 | n290, n291 | Agrees |
| [I.13](../../heath/I/13.md) | pp. 275–276 | n295, n296 | Agrees |
| [I.14](../../heath/I/14.md) | pp. 276–277 | n296, n297 | Agrees |
| [I.15](../../heath/I/15.md) | pp. 277–278 | n297, n298 | Agrees (note 8) |
| [I.16](../../heath/I/16.md) | pp. 279–280 | n299, n300 | Agrees |
| [I.17](../../heath/I/17.md) | pp. 281–282 | n301, n302 | Agrees where legible; marks under a blot unverified (note 3) |
| [I.18](../../heath/I/18.md) | p. 283 | n303 | Agrees |
| [I.19](../../heath/I/19.md) | p. 284 | n304 | Agrees |
| [I.20](../../heath/I/20.md) | pp. 286–287 | n306, n307 | Agrees |
| [I.21](../../heath/I/21.md) | p. 289 | n309 | Agrees |
| [I.22](../../heath/I/22.md) | pp. 292–293 | n312, n313 | Agrees |
| [I.23](../../heath/I/23.md) | pp. 294–295 | n314, n315 | Agrees |
| [I.24](../../heath/I/24.md) | pp. 296–297 | n316, n317 | Agrees |
| [I.25](../../heath/I/25.md) | p. 299 | n319 | Agrees |
| [I.26](../../heath/I/26.md) | pp. 301–303 | n321, n322, n323 | Agrees |
| [I.27](../../heath/I/27.md) | pp. 307–308 | n327, n328 | Agrees |
| [I.28](../../heath/I/28.md) | pp. 309–310 | n329, n330 | Agrees |
| [I.29](../../heath/I/29.md) | pp. 311–312 | n331, n332 | Agrees |
| [I.30](../../heath/I/30.md) | p. 314 | n334 | Agrees |
| [I.31](../../heath/I/31.md) | pp. 315–316 | n335, n336 | Agrees |
| [I.32](../../heath/I/32.md) | pp. 316–317 | n336, n337 | Agrees |
| [I.33](../../heath/I/33.md) | pp. 322–323 | n342, n343 | Agrees |
| [I.34](../../heath/I/34.md) | pp. 323–324 | n343, n344 | Agrees |
| [I.35](../../heath/I/35.md) | pp. 326–327 | n346, n347 | Agrees |
| [I.36](../../heath/I/36.md) | p. 331 | n351 | Agrees |
| [I.37](../../heath/I/37.md) | p. 332 | n352 | Agrees |
| [I.38](../../heath/I/38.md) | pp. 333–334 | n353, n354 | Agrees |
| [I.39](../../heath/I/39.md) | p. 336 | n356 | Agrees |
| [I.40](../../heath/I/40.md) | pp. 337–338 | n357, n358 | Agrees |
| [I.41](../../heath/I/41.md) | p. 338 | n358 | Agrees |
| [I.42](../../heath/I/42.md) | pp. 339–340 | n359, n360 | Agrees |
| [I.43](../../heath/I/43.md) | p. 340 | n360 | Agrees |
| [I.44](../../heath/I/44.md) | pp. 341–342 | n361, n362 | Agrees |
| [I.45](../../heath/I/45.md) | pp. 345–346 | n365, n366 | Agrees |
| [I.46](../../heath/I/46.md) | pp. 347–348 | n367, n368 | Agrees |
| [I.47](../../heath/I/47.md) | pp. 349–350 | n369, n370 | Agrees |
| [I.48](../../heath/I/48.md) | pp. 368–369 | n388, n389 | Agrees but for one faint mark (note 5) |

### Book II

| | Pages | Leaves | Against the scan |
|---|---|---|---|
| [Book II, front matter](../../heath/II/front.md) | p. 370 | n390 | Agrees (note 9) |
| [II.1](../../heath/II/01.md) | p. 375 | n395 | Agrees |
| [II.2](../../heath/II/02.md) | p. 376 | n396 | Agrees |
| [II.3](../../heath/II/03.md) | p. 378 | n398 | Agrees |
| [II.4](../../heath/II/04.md) | pp. 379–380 | n399, n400 | Agrees (note 8) |
| [II.5](../../heath/II/05.md) | pp. 382–383 | n402, n403 | Agrees |
| [II.6](../../heath/II/06.md) | pp. 385–386 | n405, n406 | Agrees |
| [II.7](../../heath/II/07.md) | pp. 388–389 | n408, n409 | Agrees |
| [II.8](../../heath/II/08.md) | pp. 389–391 | n409, n410, n411 | Agrees |
| [II.9](../../heath/II/09.md) | pp. 392–394 | n412, n413, n414 | Agrees; one mark the scan alone does not settle (note 7) |
| [II.10](../../heath/II/10.md) | pp. 395–397 | n415, n416, n417 | Agrees |
| [II.11](../../heath/II/11.md) | pp. 402–403 | n422, n423 | Agrees |
| [II.12](../../heath/II/12.md) | pp. 403–404 | n423, n424 | Agrees |
| [II.13](../../heath/II/13.md) | p. 406 | n426 | Agrees |
| [II.14](../../heath/II/14.md) | pp. 409–410 | n429, n430 | Agrees |

### Book III

| | Pages | Leaves | Against the scan |
|---|---|---|---|
| [Book III, front matter](../../heath/III/front.md) | pp. 1–2 | n13, n14 | Agrees |
| [III.1](../../heath/III/01.md) | pp. 6–7 | n18, n19 | Agrees |
| [III.2](../../heath/III/02.md) | pp. 8–9 | n20, n21 | Agrees |
| [III.3](../../heath/III/03.md) | pp. 10–11 | n22, n23 | Agrees |
| [III.4](../../heath/III/04.md) | pp. 11–12 | n23, n24 | Agrees |
| [III.5](../../heath/III/05.md) | p. 12 | n24 | Agrees |
| [III.6](../../heath/III/06.md) | p. 13 | n25 | Agrees |
| [III.7](../../heath/III/07.md) | pp. 14–15 | n26, n27 | Agrees |
| [III.8](../../heath/III/08.md) | pp. 17–19 | n29, n30, n31 | Agrees |
| [III.9](../../heath/III/09.md) | pp. 21–22 | n33, n34 | Agrees |
| [III.10](../../heath/III/10.md) | p. 23 | n35 | Agrees |
| [III.11](../../heath/III/11.md) | pp. 24–25 | n36, n37 | Agrees |
| [III.12](../../heath/III/12.md) | pp. 27–28 | n39, n40 | Agrees |
| [III.13](../../heath/III/13.md) | pp. 32–33 | n44, n45 | Agrees |
| [III.14](../../heath/III/14.md) | pp. 34–36 | n46, n47, n48 | Agrees |
| [III.15](../../heath/III/15.md) | pp. 36–37 | n48, n49 | Agrees |
| [III.16](../../heath/III/16.md) | pp. 37–39 | n49, n50, n51 | Agrees; one mark, settled by a second copy and mended (note 4) |
| [III.17](../../heath/III/17.md) | p. 43 | n55 | Agrees |
| [III.18](../../heath/III/18.md) | p. 44 | n56 | Agrees |
| [III.19](../../heath/III/19.md) | p. 45 | n57 | Agrees |
| [III.20](../../heath/III/20.md) | pp. 46–47 | n58, n59 | Agrees |
| [III.21](../../heath/III/21.md) | p. 49 | n61 | Agrees |
| [III.22](../../heath/III/22.md) | pp. 51–52 | n63, n64 | Agrees |
| [III.23](../../heath/III/23.md) | pp. 52–53 | n64, n65 | Agrees |
| [III.24](../../heath/III/24.md) | pp. 53–54 | n65, n66 | Agrees |
| [III.25](../../heath/III/25.md) | pp. 54–56 | n66, n67, n68 | Agrees |
| [III.26](../../heath/III/26.md) | pp. 56–57 | n68, n69 | Agrees |
| [III.27](../../heath/III/27.md) | pp. 58–59 | n70, n71 | Agrees |
| [III.28](../../heath/III/28.md) | pp. 59–60 | n71, n72 | Agrees |
| [III.29](../../heath/III/29.md) | p. 60 | n72 | Agrees |
| [III.30](../../heath/III/30.md) | p. 61 | n73 | Agrees |
| [III.31](../../heath/III/31.md) | pp. 61–63 | n73, n74, n75 | Agrees (note 8) |
| [III.32](../../heath/III/32.md) | pp. 65–66 | n77, n78 | Agrees |
| [III.33](../../heath/III/33.md) | pp. 67–70 | n79, n80, n81, n82 | Agrees |
| [III.34](../../heath/III/34.md) | pp. 70–71 | n82, n83 | Agrees |
| [III.35](../../heath/III/35.md) | pp. 71–72 | n83, n84 | Agrees |
| [III.36](../../heath/III/36.md) | pp. 73–75 | n85, n86, n87 | Agrees; one mark the scan alone does not settle (note 6) |
| [III.37](../../heath/III/37.md) | pp. 75–76 | n87, n88 | Agrees |

## The leaves

| Volume | Leaf | Page | SHA-256 |
|---|---|---|---|
| 1 | n173 | 153 | e7db8691e9f03b947e36f0c56f75e42df7f143b09db83a3e10ab4a31f6fd9035 |
| 1 | n174 | 154 | c2abbedb7f4d82cc944b0f766b8552119e663c17e5f859906915039269630f58 |
| 1 | n175 | 155 | c235435583d5395fda591c168344b8a43e516df9419fa00d660093111af249e1 |
| 1 | n261 | 241 | a65a6d54abe28927deaa96c2bb90ac51f354691dab81a62244a04a503d467cc4 |
| 1 | n262 | 242 | d7c7a36e394e45aab77dc628ebc639855579079207e38ae8b60176bee3f20913 |
| 1 | n264 | 244 | 81d50e28a2122f7ba6f57771658b2a63f946e420b8a18ca13edc44042bc53b75 |
| 1 | n266 | 246 | 0ed7151138249b01430091985d61c450cee245d8f21aac33999acf41cb10e243 |
| 1 | n267 | 247 | ad2ec4c5cba2bd51589ee557f7101bd1db8c169324e09d8c9d62a6110ba5d5a7 |
| 1 | n268 | 248 | 5853ef6b823da6e8cabcc7f92cf37a7b6d340cc68e4889672beb30d556efb5fd |
| 1 | n271 | 251 | 7c9550b1fe1eb5287dcb2a4e38af7ffafb61e1c9c2710fce54122581460ab33d |
| 1 | n272 | 252 | 68c4c87bc554210c710ed2af205565d40b6e45a3529421beb124daab07cfbab7 |
| 1 | n275 | 255 | 53d6b29aa58e3c6bbfeba5eb188ab3515ddce2a54622383d91d2f9f1213a3915 |
| 1 | n276 | 256 | eaedf236b7a449cbafce047a65adb637a1805d89c36fb731f576903ce9fb62a5 |
| 1 | n278 | 258 | 0516db80caf92e267c41ab49401529b6319b5c14b308eb168cbb240136868de3 |
| 1 | n279 | 259 | 4c07d7f023242c3d473ad174f714e764a0a5afd37820e544485b80266106821e |
| 1 | n281 | 261 | b9aed03e050f105c5ea2ef7cf09aee181920087a75eae8aef67b6aa14bb2d5a6 |
| 1 | n282 | 262 | 0753181240375c6296b33f111f25dbee30039367545b0edb9b23cc3f1252a1dc |
| 1 | n284 | 264 | 1f93353c37423f1960b01ab38d32dcf8691ecb671d2cf75d431cd17c1a8b0449 |
| 1 | n287 | 267 | 0169a425cb0c1e91ef01f3ed18f49af7b49d2b8f5034a633275898b275222bb9 |
| 1 | n289 | 269 | b075a804f3f83eaac33e704796f95bd34bd7c8b8dee912f9da0647bab15e06c0 |
| 1 | n290 | 270 | 405c06ce9005c60e958e1f5edf46210690e6c1f6bc68d7662a348f1508af5ebf |
| 1 | n291 | 271 | d37b1463cd9c9349c38f6b5f3f8b26d084a4e032f61c0836dfd4e50ba0858014 |
| 1 | n295 | 275 | 8446172d16092a36c36267ebb4600b709a381b6c06d1a2ce1503f5f062febcd0 |
| 1 | n296 | 276 | 9df6badac5dc9f23e5d0e093ecfde7957cdfcc45ef0a1620f0c4b03bd125188a |
| 1 | n297 | 277 | 390ab203be306c49faf7100f042069421b742d1cab0f4e82537b59e5796eac7c |
| 1 | n298 | 278 | a708525cb53699973da6160c78649ca0ea73fed82af22b8a1a1646c357e14a5c |
| 1 | n299 | 279 | 8bda2c8f550937caf7340ca978887fbdf74aa4da62aabc83f160da82f525ebc7 |
| 1 | n300 | 280 | 67d1cda171783ba2faf67825d641d7d8510ceb1601c95463eaf2bd44c49e40e9 |
| 1 | n301 | 281 | 4cdd1d478baf013a763e8d422449ca563b106f7117954a36d994561794d414c7 |
| 1 | n302 | 282 | 3e1913278850199e7853eeadae7da0a11bd030f592c5b609c60cd6655060b3d3 |
| 1 | n303 | 283 | 7547c3ff4daa153c3198a1e9677d41810dbf48b6b73a2aaca3ff7573732f1773 |
| 1 | n304 | 284 | b3cc662aa99b30440dadc4f755ed52c874b79571673add362c72031dbb0111b4 |
| 1 | n306 | 286 | 83e8bc208ebe86a130a7281db13bdd1b3334cc4cf2f5241898561f7ec1407929 |
| 1 | n307 | 287 | ab77838bf69ed1f0be6a5d633b65bd4f3d650a8fa70ebeee6354632e478761e5 |
| 1 | n309 | 289 | e2218ca98a1c30586eacdc6c624eee66b9739b0d16e01b58c22d5364a9c27845 |
| 1 | n312 | 292 | 1a7f302210ee2d5aa17f7b202f636582bb31ccec42babcc110595bff34b30f38 |
| 1 | n313 | 293 | 7cb02ee2c7a4601aeec8f10ba779172adf32120a42685cb2b6b0cd1a331c5aeb |
| 1 | n314 | 294 | 134f4f113a076120afa66e1a0da5951ef0d54c594c717d0927db0641cd1a6b5c |
| 1 | n315 | 295 | 8e0fbf593584865ab0dbedd9adfab71a8f776072d745d2851e6cf95aada90b76 |
| 1 | n316 | 296 | 9bee0d7946ba9ac94d77aaa31b8f3b3c9064924f9a3da2ee2b0a41d4ceefc38b |
| 1 | n317 | 297 | 971f8d1cd10b923de05754cbc827b9b08a041be458a27a886b72b035112d974c |
| 1 | n319 | 299 | 2b52d034ce5f596a96674154846341fa2f4fa70a8900b1fffd002f8c1afcd4f6 |
| 1 | n321 | 301 | 044a636ec1dcbade7e60fcc0ea58fc9bc8a52316ae6b164b8000240c40214713 |
| 1 | n322 | 302 | 725bde155ee105795214fff0bebf8910ec88aaba0aad31d3568c16958e0c6525 |
| 1 | n323 | 303 | 656891f066521ff9e122a633d8218b80ac070d320ad5bb77f170210b52b0940d |
| 1 | n327 | 307 | 9421e55b7b0a7e88542d8d5c951e0c3a1e490aca20d330fb545a3b62a1a5fb6b |
| 1 | n328 | 308 | d72a34d731509342504f354bb4460d08f0ba3dd61faf737939a7a4d6b65e3001 |
| 1 | n329 | 309 | 3b8330daa47722b8bdec16ed6671d2ca8a52848c53f7085fb5417031a4a9b85f |
| 1 | n330 | 310 | e8fc5b6de50e221e470505dbff21522712bf122d0adb7c5102a3e3144e5564a2 |
| 1 | n331 | 311 | 491d12cab4fea2021ce2cf11fa69460f3f6634eeeaa1e2f6e8066596e0b895c5 |
| 1 | n332 | 312 | 6fc9dcb74e1250e9ed1956d5f3312a0d7b12f9db4ca10749e293c9b6872e7a21 |
| 1 | n334 | 314 | 17fa03153c15791833389353e00dae5512981521fe91d3ea9bff5587b6f5a7be |
| 1 | n335 | 315 | 84cb6400c87b3fb742a7e8bfa09893da2edea45afe28826f5e0de811a9557da9 |
| 1 | n336 | 316 | 1521d2bb867a325c736e673a75deef44704d62d2bd111279b752b8529fe5da99 |
| 1 | n337 | 317 | d5736937dc07ef728ce070b3d7e01e0ad798a39bda4d2119601c725f06bf791c |
| 1 | n342 | 322 | 15ec8035cc6e757fc3927fcb17e89c756833a9b441ebf6af922850a5340bca93 |
| 1 | n343 | 323 | fee878d6270797717176dbf56022779cb8ebeaa475c5ecfe21d7a10155a6f5b0 |
| 1 | n344 | 324 | acf3aeb5845b3cd72ebf30f325632c67f5e8b83f86402357248c0c85f41a3cae |
| 1 | n346 | 326 | b4753fd90b964ddd06b696c349384182075c6d7606eb2c0012531d3a3ec47ee2 |
| 1 | n347 | 327 | 84b7576607df44c887aa4c3c82048062f92b33ab70e69a94c5ea3e50a7e92401 |
| 1 | n351 | 331 | eaefcb981e4d99aa95a9feb54b88c367db738aa44c31ec7d349cb415ef91b06b |
| 1 | n352 | 332 | 0bc3a011fa6a40f270ca2613a5322e8d628f8099a7e06eb9cad385ffff2a63ec |
| 1 | n353 | 333 | 3ec684b53feb0d3364a4a71bcf737e14c89764d2e96b532354d59fca570be52b |
| 1 | n354 | 334 | 0389beb80a8c4748bdd267821ec829f8531c1b159ad6aa965ae84829266e4f1a |
| 1 | n356 | 336 | cf088824f4cb9fb8e5e4ef0ea4ac774fd6f9746b6b74f30bbcd8187acba6af0c |
| 1 | n357 | 337 | 258c3915d4cb617407ba8ff5bbb380ef526c50ddf3ca5428ed0841f19b343d2f |
| 1 | n358 | 338 | 04b9cf60bc3748eab467180670b977c1c660bdea68da6cd0cbcea54db2bd54b8 |
| 1 | n359 | 339 | 95f7c5d21bb662a76accbae0446af1d27d8b8c5fe86d492dd2f4eafa62a70c16 |
| 1 | n360 | 340 | 128182c5fed3f6e8445f0a74998340f885c8a7107f0615ce60aa5f4d6f488ddd |
| 1 | n361 | 341 | 91ed155929a1515300ca7775bade7713997dff8a3aa9d9c182e5465f706b1ea4 |
| 1 | n362 | 342 | cce37f202d0f8e199672bcd1a4ac568bf79999012836c1728bd5d135276df79f |
| 1 | n365 | 345 | 190a7ccb7e8e4ab6244b23457ab15404226777dffb51eeff805351ab0bc9de28 |
| 1 | n366 | 346 | a51de22ee81e0ddc05ad3c5f5c66689c236ce7eaa3ed49e147c83f37db9044a7 |
| 1 | n367 | 347 | bb7b3d8747d82a718a7a7d593d8ca2933432376436097ce8878b79e8bcc2d88a |
| 1 | n368 | 348 | 5ab550be749de720d478c5ca2ad2766e2ac25e008a900d38e2e0958d3486a390 |
| 1 | n369 | 349 | cfb483b1f3f1beec19e8eedebeee1b9bb93a542c33e9d630e0fc031a4a2ab053 |
| 1 | n370 | 350 | 1b27418a47f395aab764eb92751a8beeb3bd56b60cfe366d834c47b2d1e851d1 |
| 1 | n388 | 368 | 19e3e320302d1971ccc32a7e387cafe33967a77319a4e008e91e2730c2ac7212 |
| 1 | n389 | 369 | d08987fab5036b0ef13f6474dfce3e294ea818975bd15bce546b5e11f46b0dde |
| 1 | n390 | 370 | c2763567e24f44f8d01743ae91a7348048277c689a63b197ae0beb026678ca74 |
| 1 | n395 | 375 | c6e11326aa99fc2b0a7ec5c751bc0c44678b755adc10cde12c7fd3681193cfa5 |
| 1 | n396 | 376 | 0fb7406ee96952a2d8b8c21b1515c225e842538321c825baaf34bba3f9f02b76 |
| 1 | n398 | 378 | a23816682b7390be11a59bc630a402eb2329cf21f942b03f8690011c3b0d7cdd |
| 1 | n399 | 379 | cd19b844ca6b7706a9b6404f9af49ee8055c00ce638f9b713cb54bac8f32522b |
| 1 | n400 | 380 | 60911928e43df4355bc50b861c936ab41bfd6d66aa5117bfcd9d684d7669825a |
| 1 | n402 | 382 | 36fca8343e1efaae0a54e7d365b098687f441d50724a74d75d4fd459a734c179 |
| 1 | n403 | 383 | 34c9f87dd9ab1b5c376ac7a42ac23e55cdc43e9d24390c7f1249ed05e2728dec |
| 1 | n405 | 385 | c29cf3a364aafc59b5aa680dbbed5cf979a04c8e8e1ca9ede0caff4c51739897 |
| 1 | n406 | 386 | 4b6a1c62af45ad408702c4ff5acbee4850d9944f3c9c8e161e1322860208888a |
| 1 | n408 | 388 | 9bfe16f1dd5666db52c95038f42b8d6c19a8c2ec4f7749eb204b20cc54f98cd4 |
| 1 | n409 | 389 | 9e2b3ba342b4269a8d76fe54c4251c748ac7fa3ecd93c0c785c279b2ed1bc20c |
| 1 | n410 | 390 | 56293ae4482d287b68300b3ebf0e259c0331dafa789ac9de02dd3fd77f5e0aa7 |
| 1 | n411 | 391 | cb4557735f3b2afcea2c69eefab31ecd618a166a212bfbf25312ae7a13181c3c |
| 1 | n412 | 392 | 14eb2dc583f323d26bd4275826f52cddc8de6e4c3450c320384dca0c8c583cfc |
| 1 | n413 | 393 | a330341856f38440cf486cfffb3df536a72da2fa192c4a61214928451cdac509 |
| 1 | n414 | 394 | c1e155c4cb27b5fcc51825f5677cad9155cc30875eb73d19a2b395f3ef495db7 |
| 1 | n415 | 395 | 309d61fdcaf3b5326c8448b6eb8f604d2adc5e234b259c169fa23d523fe1fa17 |
| 1 | n416 | 396 | a86245bce5b9135d1029d55f11f8f4b29e94c83ce38b23001a9f06e5e1e66062 |
| 1 | n417 | 397 | 8a35038f7a6377bb082c5fef3cf511f1344a66ab00f8b66759dbcb6b2788359a |
| 1 | n422 | 402 | 79157c5b20c92574ad3aaee351d1a0d93efe83f183d75d84299cf49e6963fa65 |
| 1 | n423 | 403 | 157ccfb4f96b9dde4f65cf47f04cae970662f24cab46224fc49f86531ff0762a |
| 1 | n424 | 404 | 933b7ad649940cf5114d58e533337f839f8611fc4283b4abc078ae8ae0457e75 |
| 1 | n426 | 406 | 46b1741067026ab27e77e2597c520eed3b2d9991dcdd97d1e7d9a33c06212326 |
| 1 | n429 | 409 | 4f7f7971dd5c4b906393e710230877840a8685d78c2ff223e6db541eeb724adc |
| 1 | n430 | 410 | 126a73416a33b4efb4ec406786cb2a1f1ef0f7e1911cba0e6b7016297e5d5fc6 |
| 2 | n13 | 1 | 6e789a75319c320f7646d84343793ef1c56d86774e532ed1fe49be269aab575a |
| 2 | n14 | 2 | 65bc3de21a6269c8e656dbef357b655f31953c1101e29c97e98f7f1e92d81a91 |
| 2 | n18 | 6 | 056e292655f26741f384a47f6d96ab78dec7cd815fde06f693d998eebaf151c7 |
| 2 | n19 | 7 | 2c123700803a38f48569de0334edfb3ee953106b95489458a6d1ca5e3bf6dbac |
| 2 | n20 | 8 | 75477e0ec0c25f98c8e4933d97ce2f06801556d306cc9b396cfdb1b996c99e5d |
| 2 | n21 | 9 | 510588e46a76cedb7dbb8dcef992b6120829c11898e21972bcbbc51d0aa9e5e0 |
| 2 | n22 | 10 | 95681d5436bd3d79e36f3c40971800886d3bc00bdfd8e9bf6ba0908514aa26eb |
| 2 | n23 | 11 | 058afc084aafbf5cef2d8e03178fc7c9115adeeafae91a2d653e87e25014a6bc |
| 2 | n24 | 12 | 55886d6963c62e088568ecdb59ffe120abb96b6a483a2fb2d26d1740b83f9e72 |
| 2 | n25 | 13 | edde3ce8c82805e7ae68484d45406dae19632e24aed5a4c781add6b296f4cafa |
| 2 | n26 | 14 | 3189e5167b415f3144caba589a5a7576e22e7844dbd12670c58448a768518998 |
| 2 | n27 | 15 | 5dbf346c71829899bbfb16795e3d186851c6db4c6b794c6ee9e5ffe713f0408c |
| 2 | n29 | 17 | b58eb1237077b831e172aecf4cfa58401555bbbf546672366122d71553bb0cf5 |
| 2 | n30 | 18 | 9587bd7c882aecae0a663343a1da7522298e4672f6fae6886c498899eb99db18 |
| 2 | n31 | 19 | fa2f13c48551b82acc31f52807ddb05b7917fb42df2fe9423fb73e82d7b2e359 |
| 2 | n33 | 21 | 2b0d4b78cc3344272bf327b2426c28f126d94681ec29f81ca42d31438eed1303 |
| 2 | n34 | 22 | d1f4059520c2d180cea2609a9428f68e312a7d5db718ed43001c5c38439964ce |
| 2 | n35 | 23 | 1b1dafef6e902211d147b6349c24c81fa83872141ac2bc8197dcf6e2cfd8aaff |
| 2 | n36 | 24 | f1440868a58d472c4e8105513d79d4d53840c47c16dffda4af46ae851f34f1be |
| 2 | n37 | 25 | 3b589af6fe15e7d4f5072404a2c8fca8084b41d11d72cb64c903536444f8adf4 |
| 2 | n39 | 27 | f0d5d507b9c7c4f135b8e605aa470c45f7239c265aecf9066b8df77a6bf9e0bf |
| 2 | n40 | 28 | 63fc23487d6fc0487d0ae82eaeba5bebea6bca8cd3136bdb3b1ce0ca86537a22 |
| 2 | n44 | 32 | fc1a2c4879d4e864566f1653391f9f3078dcc3ef022d775f6b7c0bcad26edee5 |
| 2 | n45 | 33 | c6d49c0f74147ca492cc1795a24b069aa41da4b91f0684efa9a59440deebe2a0 |
| 2 | n46 | 34 | f2ad707739e7986616d6a3150ce5a40e3deab925c04d203f10b11ad1b864c09e |
| 2 | n47 | 35 | c1b1938efe28f8e225429892d01fa8925366216d81dca6ad9e52ba950a99fda0 |
| 2 | n48 | 36 | bdd1b56fd4954c14cccaf72f5e9349768fecde9abb4ab6ac10c74f97eb1bcc1f |
| 2 | n49 | 37 | 4854ab66af20cc66dabc59d1f7315e3fa3284763534690c30055d50618940c68 |
| 2 | n50 | 38 | bf71b9627f2834fa16af4da6b259577855944c2727e3370dddba5d3a8002061d |
| 2 | n51 | 39 | e23d832563b93ec90cafb5d2b7e46148d1709393063d943784beb9be1214cdd2 |
| 2 | n55 | 43 | eed3c22e9d2a129dcf519192abdf10c68d0c16289ae5d2a810a3789689e20cef |
| 2 | n56 | 44 | c5c5c0b830831bb125ab0fc393163f862d0712a23a60df7b11be8bf8a3206e3e |
| 2 | n57 | 45 | bd0e1d786801762bf4df2b843edf07201db1a77d62ac0565608e8092a1b722e5 |
| 2 | n58 | 46 | cf9142c9d3a45a860d561f519bb8f829e7c13c529ed01f6227d17abc65ae1dc4 |
| 2 | n59 | 47 | 6e78f14796a0b83b7e9550de7e9d7f0f7e0dfb0a3b6d9bd1409a22304c37d483 |
| 2 | n61 | 49 | 04ba81efb2a2422d562aee7fdccf317dfa950e4d9ff7e4c1de9d33a099c8f9a5 |
| 2 | n63 | 51 | 175038fac4efce7f24e2d68ad1ec95d68ba9cdf599b6dacd1cf57f5c720dc92e |
| 2 | n64 | 52 | a08e20d2af74a45e0163064b12f729e3ec4371d13f00cb83e0ad1b1c6e29059b |
| 2 | n65 | 53 | 269ec5d9a4eee8f9f07ac8a69f04ab4417320608762aa80179e85e8d9c17b3b1 |
| 2 | n66 | 54 | ee59d011d04e34bc4cdb92f9523adf41be04a4b283f72bcbc119c6a456a3abda |
| 2 | n67 | 55 | aec0340fa8ca3679d7c278df7010eb84ff328136e846c3f816e8b69ae85f1bdd |
| 2 | n68 | 56 | acda7637626850e4fd7c1cf12836a532a6034889b77605f2a85cc5a5b1d799bd |
| 2 | n69 | 57 | 5d18482fba8565b2009a3c5431315049ef59234a545fbc620b114c626073d435 |
| 2 | n70 | 58 | b168b2c137f1fc367247682c28267f2bddfd03032c956830d1675ed6fd1107c2 |
| 2 | n71 | 59 | c364cd5e22fa258ef14661217d2b439937202f5a543f18d1168d46fae5456c84 |
| 2 | n72 | 60 | 9a5ccacc8626a11d5647ca553ab303023d319b41bc27f2392a288d810f26d61e |
| 2 | n73 | 61 | 31e8e0787a8f08f123b7ae5f71a057016d1e1d17f32b5bdfb39868f0f47544da |
| 2 | n74 | 62 | 65ec20dba953ca07fcd966b5f1fc257818347ff1cdcb065e3e3a56845ca8cc66 |
| 2 | n75 | 63 | 7e5b4afa59af57b88e1ddb9b56b7b795c39c06edb9509531e704bd1aae144c10 |
| 2 | n77 | 65 | c0371ec1fcca40c0eb241982a05baf67dabc07717adebf66b71bfbf3d5ff4cc4 |
| 2 | n78 | 66 | 2983ebdfae448166e4f2767ebc60c742fded3aef92750f929d51903aa8895615 |
| 2 | n79 | 67 | 76c272b3674b5dad611522250fe5130b497e181948ee95ee3c6de442994076e5 |
| 2 | n80 | 68 | f4f477bab2a081bc89c486a764cbbbdec724ca8cb8b461db808b0443a5c75bc9 |
| 2 | n81 | 69 | a42bf2842a7653d1d9b4d19dd213a672cc70904241b2a53949cbe5ac0c8f5031 |
| 2 | n82 | 70 | 07d9311be65c3efa20bee2a365aa74b724b6c70642ab6020cc6fff678af933cd |
| 2 | n83 | 71 | 194a3f3b887ff8bce1c18e1e9ec78dcfe1aafb788e691c3b94b49a3956a22f07 |
| 2 | n84 | 72 | 7e7fd216db622e5d17901fcf4253a5c18c1b84c2477f116a01c4975c68ff6c05 |
| 2 | n85 | 73 | 6d6178bd7d8c109a5bf1a906778d58bbbb55b0a78e0f8df06b79becc2ffa680c |
| 2 | n86 | 74 | 72b26b3194fd12429f9b412626aa9b0cf86bd2f9767773d69e52d55004f04ef0 |
| 2 | n87 | 75 | 171114d9282a16152a8549ef828869180e1a9e70d23a4a412883ee386abd5e22 |
| 2 | n88 | 76 | 985ed00c0093ddd3a5eb02ac6d1f3e3b20f6186253b92bede8ec7dac0ce7ac83 |
| 1 | n401 | 381 | ca5681d4752b18aa745c5071aa1d88844a1e3de41499d4dc550c364e37cbd18c (Heath's note, for II.4's comment) |
| 2 | n76 | 64 | 0360e009e2a3a1bf5db99f636ad0a84305657c9a49d9c6d7aa887199e606a445 (Heath's note, for III.31's comment) |
| 2 | n45 | 38 | 58fa810189d14ea660204e741eb7cac4ebf578b2aa5314b42523dc866fc1f830 (the second copy, euclid-the-thirteen-books-of-the-elements-vol.-2, for note 4; fetched 28 October 2026) |
