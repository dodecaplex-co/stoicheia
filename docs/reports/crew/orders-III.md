# Sailing orders, Book III: Propositions 1–37

*The scratch proofs these orders name were removed once Book III was proved; they are
at commit 81d72f5
([scratch-III at 81d72f5](https://github.com/jackChallis/stoicheia/tree/81d72f5/docs/reports/crew/scratch-III)).*

Every sailor, Claude or Codex, follows these orders word for word. Your proposition
is III.N; NN is N in two digits.

**The job.** Prove III.N in Lean along Euclid's route, his steps in his order,
citing what he cites where he cites it; draw his figure; write the mishnah and a line
or three of further reading. Others are proving the rest of Book III at once, so cite
any proposition of Book III by its statement. Books I and II are proved: cite them as
`BookI.PropN` and `BookII.PropN`, under Euclid's "[I. N]" and "[II. N]".

**Read first.** `docs/STYLE.md`, `CONTRIBUTING.md` and `docs/reading.md`;
`docs/briefs/0004-book-III.md`, how Lean says "equal circles", "touches", "the
circumference BKC" and "the angle standing on a circumference", and why the circles
carry their centres; `heath/III/NN.md` and `Elements/BookIII/PropNN.lean`; your note
under "For the sailors" in `docs/reports/crew/first-mate-III.md`, and any scratch proof it names, which is in
[`docs/reports/crew/scratch-III/`](https://github.com/jackChallis/stoicheia/tree/81d72f5/docs/reports/crew/scratch-III) (not built; check one with
`lake env lean docs/reports/crew/scratch-III/T20.lean`);
`Elements/Foundations/DefinitionsIII.lean`, `Elements/Figure/OnCircles.lean` (Book Zero for
circles), `Elements/BookIII/Squares.lean` and, from III.23 on,
`Elements/BookIII/Circumferences.lean` (Book III's ground); Book Zero from
`Elements/Figure/Basics.lean`, above all `Circles.lean`, `Sides.lean` and `Angles.lean`;
System E's rules for circles in `Elements/Foundations/Tacit/Diagram.lean`,
`Constructions.lean` and `Transfer.lean` (`circle_eq`, `inside_of_len_lt`); and, as
models of a proof under Euclid's sentences, `Elements/BookI/Prop12.lean` and
`Elements/BookII/Prop12.lean`.

**Circles.**
- A circle takes Heath's letters: the circle ABC is `ABC : Circle`, and `OnCircle A ABC`
  says that `A` is on it.
- Our circles have a centre only by hypothesis. Where Euclid says "let the centre of the
  circle be taken [III. 1], and let it be F", take it from III.1:
  `obtain ⟨F, -, -, -, hF, -⟩ := Prop1 hABC hA hB hAB`, with `hABC : ∃ F, Centre F ABC`
  from your statement and two points of the circle. Where the statement names the centre
  and Euclid has no "[III. 1]", use it. Where it names the centre and Euclid still takes it
  "[III. 1]" (III.14), take III.1's and show it is yours:
  `obtain ⟨E₀, -, -, -, hE₀, -⟩ := Prop1 ⟨E, hE⟩ hA hB hAB`, then
  `obtain rfl : E = E₀ := centre_unique hE hE₀`. Where the statement gives no two points
  of the circle (III.17), find two first: from the centre `hABC` gives, a straight line to
  a point outside meets the circle between them (`line_circle_between`) and beyond the
  centre (`line_circle_beyond`); then `Prop1` on those two, and `centre_unique`. The
  scratch proofs of III.14 and III.17 do it, and the mishnah says why in a sentence.
- System E knows a good deal of Book III already: a straight line between two points of a
  circle is within it (`inside_of_between`, which *is* III.2); a circle is fixed by its
  centre and radius (`circle_eq`); a circle has one centre (`centre_unique`); a straight line
  through a point within a circle meets it twice (`line_circle_beyond`), and leaves it
  between a point within and a point outside (`line_circle_between`); a point within a
  circle on a straight line in it lies between the line's ends (`between_of_inside_chord`).
  Use them as steps; when one of them is the very thing Euclid proves, follow Euclid
  instead and say so in the mishnah.
- Three points of a circle are not on one straight line: `Triangle.of_onCircle`. A straight
  line in a circle has points of it on each side: `exists_onCircle_oppositeSidesOf`,
  `exists_onCircle_sameSideOf`.
- "Equal circles" is `EqualCircles`; "the radii are equal" is `EqualCircles.radii`. One
  circle is equal to itself: `EqualCircles.refl`.
- "DE touches the circle at C" is `Touches D E ABC` with `C` on both; no point of a
  tangent is within the circle: `Touches.not_inside`; a tangent named by other points of
  it: `Touches.of_collinear`.
- "The circumference BKC" is `circumference ABC B K C`; "the circumference on which the
  angle BAC stands" is `standing ABC B A C`. They are measured by twice the angle standing
  on them at the circumference: `Circumference.eq`, `Circumference.standing`. Name them from
  either side: `standing_eq_circumference`, `circumference_congr`, `standing_congr`.
- "The angle of the semicircle", "the angle of a segment" are mixed angles, not angles of
  ours: write Euclid's sentence as a `--` line with no Lean under it, and say what it
  means in the mishnah.

**Shared steps: cite them, never copy them.** The certificate walks through a step, so
the propositions inside it become citations of yours; each is shown after the step
("adds").
- The circumferences, from III.23 on: `Circumference.eq`, `Circumference.standing` (add
  III.21); `Circumference.centre` (adds III.20, III.21); `Circumference.whole` (adds III.21,
  III.22); `Circumference.semicircle` (adds I.5, I.32); `Circumference.lt_semicircle`,
  `.gt_semicircle` (add I.32, III.20, III.21, and III.22 for `gt`).
- Squares, Book III's ground: `BookI.Prop46.sq`, equal squares on equal straight lines
  (adds I.3, I.4, I.28, I.34, I.46); `sq_pos` (adds I.4, I.28, I.34, I.46). Book II's
  ground: `BookI.Prop47.sq` (adds I.4, I.28, I.34, I.46, I.47). Book Zero, adding nothing:
  `rect_congr`, `sq_congr`, `rect_comm`, `sq_self` (`Elements/Figure/Rectangles.lean`).
- The perpendicular from the centre: `foot_between` (adds I.17, I.19). Where Euclid draws
  a perpendicular from the centre and then bisects by III.3 (III.14, III.35, III.36), it
  gives the `Between` that `Prop3` asks for.
- The porisms: `Prop1.porism` (the centre on the perpendicular bisector; counts as citing
  III.1), `Prop16.porism` (the straight line at right angles to a radius at its end
  touches the circle; counts as citing III.16).
- From Book I: `BookI.Prop5.base` (adds I.5); `onRay_of_angle_eq`, `crossbar`,
  `angle_add_of_within`, `angle_add_of_between` and the other angle lemmas are Book Zero and
  add nothing. Write Book I's and II's names with their book and don't `open BookI`: in a
  Book III file a bare `Prop4` means III.4.
- Book Zero adds nothing. Close sums of magnitudes with `ac_rfl`.

**Citations Euclid doesn't bracket.** Your note lists the ones to expect, and the
mishnah explains each (STYLE check 19). When a shared step brings it in, one sentence
naming the step is enough: for the circumferences, that a circumference is measured by the
angle in the other segment rests on the angles in a segment being equal, which Lean proves
once from III.21 (`Circumference.eq`); Euclid takes it for granted whenever he speaks of a
circumference.

**The route.** Some propositions can be reached by a shortcut Euclid did not take: III.2
by `inside_of_between`, III.26, III.27 and III.30 by the circumference measure alone.
Take Euclid's route: his citations are the proposition's content. A shortcut through the
measure leaves "in equal circles" unused, and Lean's linter will say so. Where Lean must
part from him (III.24 has no superposition; III.5 and III.6 fall to `circle_eq`), keep his
sentences, put Lean under them that does the same work, and let the mishnah say how.

**The rules.** Edit only `Elements/BookIII/PropNN.lean`, `figures/III/NN.svg`,
`mishnah/III/NN.md`, `reading/III/NN.md`; the ground, Book Zero, Books I and II stay as
they are. Import `Elements.Figure.Basics`, `Elements.BookIII.Squares` (and from III.23 on
`Elements.BookIII.Circumferences`), every proposition you cite (`Elements.BookI.PropNN`,
`Elements.BookII.PropNN`, `Elements.BookIII.PropNN`), and `Elements.BookI.Helpers` for
`Prop5.base`. Keep every `--` line word for word, Lean under it, your remarks in `/- … -/`.
Never change the statement, nor a porism's statement after it; never add an `axiom`. If
the statement seems wrong or too weak, stop and say so in your report; do not work around
it. No `native_decide` or `superposition`. Postulate 5 is free in Book III. Your helpers
are `PropN.something`, before `PropN`, with a docstring. Cite nothing after III.N. Every
hypothesis of the statement should be used: an unused one is usually a sign of a route
that is not Euclid's. If you find one your proof truly does not need, say so in your
report rather than work around it.

**The porisms.** III.1 and III.16 end with a porism that later propositions cite. Its
sentence is a `--` line in the proof, as I.15's is; the theorem `Prop1.porism`
(`Prop16.porism`) follows `Prop1` (`Prop16`), already stated with a `sorry`. Prove it from
the proposition, "from this it is manifest", and prove it first: III.1 (III.16) is not
proved until its porism is. The certificate reads a citation of a porism as a citation of
its proposition, as Euclid's "[III. 1, Por.]" does, and does not walk into it; so a citer
(III.9, III.10, III.17, III.33, III.34, III.37) has III.1 (III.16) in its `cites`, its
`direct_axioms` are its own and final, and it reads "proved, citing propositions still to
be proved" until III.1 (III.16) is proved.

**The voice: last voyages' faults, and Book III's.**
- Euclid's words: "straight line", never "chord" or "segment" for a straight line;
  "circumference", never "arc" outside the modern way; "the angle in the segment", "the
  angle at the centre"; "touches", and "the tangent" only where Heath writes it.
- No defensive asides ("note that", "strictly speaking"). Say the thing.
- Quote a note of Heath's only on its own proposition's page. His notes on the
  definitions are each quoted once, by one owner: III.26 the note on equal circles (Def. 1,
  p. 2), III.17 the note on "to meet" and "to touch" (Def. 2, pp. 2–3), III.11 the note on
  touching circles (Def. 3, p. 3), III.31 the note on the angle of a segment (Def. 7, p. 4),
  III.20 the note on the sector (Def. 10, p. 5), III.23 De Morgan on similar segments
  (Def. 11, p. 5). Every other mishnah refers to them in a clause.
- The mishnah is 200 to 500 words. The modern way is the fact in a sentence, exactly
  right: III.20 is "the inscribed angle is half the central angle on the same arc"; III.35
  is the power of a point.
- Certificate claims must hold after the merge, when all thirty-seven are proved: your
  `cites` and `direct_axioms` in `facts.json` are final; anything further comes through a
  cited proposition, so name it. Never write "pending" or "sorry".

**The figure.** Heath's letters, all and only, each point where your proof puts it;
STYLE §4; title "Euclid III.N: …"; no `<desc>`. `figures/III/NN-idea.svg` is not yours:
the artists draw it later. In STYLE check 20, read `heath/III` and `figures/III` for
`heath/I` and `figures/I`; the letters inside the shared steps don't count; a point Heath
leaves without a letter gets a name in the Lean and none in the figure; a letter Heath
gives a point the Lean does not need (III.3's `C`, `D`) is drawn, and the Lean may leave it
unnamed. Where Heath has two or three figures (III.25, III.33, III.35, III.36), draw
them side by side in one SVG, up to 440 wide; III.7, III.8, III.13 and III.20 have one
figure each, carrying all their cases. Check 20 drops the word "PORISM" (III.1, III.16),
which is not a letter. Circles are `#8c7b62`; the circle or
circumference the proposition is about may be drawn in `#a0522d`.

**Further reading.** Write `reading/III/NN.md` the same way as the pages of Books I and
II, by STYLE §2: one to three lines, each a list item naming a work on `docs/reading.md`,
with the list's link and a friendly sentence on what it adds to III.N; nothing that is
not on the list. For the circle, look first at Benno Artmann's chapter "Euclid Book III:
About the Circle"; Coxeter and Greitzer's *Geometry Revisited* (circles, chapter 2;
inversion, chapter 5); Kiran Kedlaya's *Geometry Unbound* (the power of a point and the
radical axis, chapter 6; cyclic quadrilaterals, chapter 8); Tristan Needham on inversion
(chapter 3); for the straight lines in a circle and their tables, Eli Maor's
*Trigonometric Delights* (chapter 2), Glen Van Brummelen and Ptolemy's *Almagest*; and
Felix Klein's *Elementary Mathematics from a Higher Standpoint* for the horn angle of
III.16. Choose what truly fits III.N: one apt line is better than three loose ones.
Check it with STYLE check 25.

**Verify.**
```sh
export PATH=$HOME/.elan/bin:$PATH
lake build Elements.BookIII.PropNN
lake env lean Certificate/Facts.lean && python3 scripts/check_fidelity.py
rsvg-convert -w 800 figures/III/NN.svg -o "${TMPDIR:-/tmp}/figNN.png"   # then look at it
```
Then STYLE §6, with `$HEATH_OCR` at `heath-src/heathV2.ocr.txt` in the captain's
session scratchpad, outside the repository
(Heath's volume 2, the Internet Archive scan `thirteenbookseu00heibgoog`; Book III is
pp. 1–76; page N is scan leaf N + 12). No `lake update` or `lake clean`. The generated
pages are rendered after the merge, so CI's "generated pages up to date" step fails on
your branch until then; that is expected.

**Finish.** Commit your four files by name, "III.N: proof, figure, mishnah and further
reading"; not `facts.json`, `book/`, `CERTIFICATE.md`, `GRAPH.md`. Codex sailors: your
sandbox cannot write to `.git`, so leave the four files for your bosun to commit. Don't
push, merge or rebase.

**Report:** proved or where the `sorry` is; your helpers; citations beyond Euclid's
brackets, each with the step that brings it in; what Lean made you say; what III.N
rests on; checks run; anything in the statement, the ground or these orders that got in
your way.
