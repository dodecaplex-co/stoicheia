# First mate: Book III, its ground and its statements (16 October 2026)

Getting ready for the Book III voyage: thirty-seven propositions, the longest since Book I.
Four jobs: merge the transcribers' text of Book III; teach the scripts and the
certificate a third book; decide how Lean says Book III's words, and prove the ground they
need; and state III.1–III.37, test every statement, and write the
[sailing orders](orders-III.md). The design is in
[docs/briefs/0004-book-III.md](../../briefs/0004-book-III.md); this report is the working
detail for the crew.

Everything below builds: `lake build` (134 jobs), `lake env lean Certificate/Facts.lean`
(99 propositions) and `python3 scripts/check_fidelity.py` pass with three books. Every page
under `book/I/` and `book/II/` comes out byte for byte as at the tags `book-I` and
`book-II`; the Book I and II entries of `facts.json` equal the tag's; `CERTIFICATE.md` and
`GRAPH.md` gain a Book III section after the others and change nowhere else. A second
round answered twenty-six challenges to this work; the answers are at the end, under
"Challenges and answers", and the report above them is brought up to date.

## The transcribers' text

`heath/III/front.md` and `heath/III/01.md`–`37.md`, from four transcribers' branches
(`worktree-wf_8e0dd6ab-43b-1` to `-4`), merged without conflict. Their comments that matter
to the sailors:

- **III.9, III.10** cite "[III. 1, Por.]", and III.17, III.33 (twice), III.37 "[III. 16,
  Por.]". The scripts now read a porism's bracket as a citation of its proposition.
- **III.12** is printed in square brackets by Heath, as Heron's proof made into a
  proposition (the comment in `heath/III/12.md` quotes his note, p. 28). The `--` lines keep
  the closing bracket of "Q. E. D.]"; the heading keeps the opening one, "[Proposition 12",
  as printed (scan leaf n39), and the page shows it before the enunciation.
- **III.13** keeps "the circle ABCD" twice where Heath otherwise writes ABDC, as printed.
- **III.16** ends "straight line AE.—" with no "Therefore etc.", and its Porism comes
  before "Q. E. D."; **III.1**'s Porism comes before "Q. E. F.". Both are `--` lines inside
  the proof, as I.15's is.
- **III.31**'s corollary is not in the 1908 text (Heiberg omits it); the comment quotes it
  from Heath's note.
- **III.33** names one circle "AEB" and then "ABE", as printed; **III.37** "ACB" once.

## Three books in the scripts

- **`scripts/heath.py`**: `BOOKS` has `"III": 37`. `citations` and `justifications` read
  "[III. 1, Por.]" as III.1. Books I and II have no such bracket. `bracketed` says whether
  Heath prints a whole proposition in brackets (III.12).
- **`scripts/scaffold_book.py`**: `BOOK_III` holds the thirty-seven statements;
  `COROLLARIES` the two porisms later propositions cite (`Prop1.porism`,
  `Prop16.porism`), each scaffolded after its proposition with a `sorry`; `GROUNDWORK`
  imports `Elements.BookIII.Squares` into every Book III file, and the new
  `LATER_GROUNDWORK` imports `Elements.BookIII.Circumferences` from III.23 on.
  `python3 scripts/scaffold_book.py III` made `Elements/BookIII/Prop01.lean`–`Prop37.lean`.
- **`scripts/render.py`**: `TITLES_III`, `FRONT_LEAN_III`, and Book III's own definitions
  written "Def. 11" on its pages (another book's stay "Def. I.10"); a bracketed
  proposition's opening bracket before its enunciation. The index, front page, pages,
  certificate and graph sections come from the existing code.
- **`scripts/check_fidelity.py`**: `FIRST_EUCLIDEAN["III"] = 1`, as for Book II.
- **`Certificate/Facts.lean`**: `("III", Elements.BookIII, 37)` in `books`. A citation of
  `PropN.porism` is recorded as one of III.N, and the walk stops there, as at a
  proposition; a proposition with a porism is "sketched" while its porism is. I.15's
  Porism, which nothing cites, keeps its record.

## The design, in one paragraph

Book III's words are definitions, none an assumption: `EqualCircles`, `Touches` (a
straight line touching a circle), `TouchesInternally`, `TouchesExternally` and
`CirclesTouch`, and two names for a circumference, `circumference α B K C` (the
circumference BKC) and `standing α B A C` (the one on which the angle BAC stands), measured
by the angle standing on it at the circumference, taken twice. Euclid compares
circumferences only in one circle or equal circles, where that measure says exactly when
they are equal. Our circles carry a centre only by hypothesis, so a circle in a statement
has `∃ O, Centre O α` (in Heath's letter) unless the setting-out names its centre, and the
proofs take it by III.1. The mixed angles of III.16 and III.31 go to the mishnah; the
statements carry the rectilineal facts Euclid proves them by. Details and reasons are in
the brief.

## The ground

All proved, no `sorry`, no axiom.

**Definitions**, `Elements/Foundations/DefinitionsIII.lean`.

**Book Zero**, `Elements/Figure/OnCircles.lean` (first named `Chords.lean`), gathered by
`Basics.lean`:
`Triangle.of_onCircle`, `exists_onCircle_oppositeSidesOf`, `exists_onCircle_sameSideOf`,
`circumference_congr`, `standing_congr`, `standing_eq_circumference`,
`EqualCircles.radii`, `EqualCircles.symm`, `EqualCircles.refl`, `Touches.not_inside`,
`Touches.of_collinear`.

**Book III's ground.** "Adds" is what the certificate's walk finds inside each.

| Lemma | File | Use it for | Adds |
|---|---|---|---|
| `sq_pos` | `Squares.lean` | the square on `AB`, `A ≠ B`, is something | I.4, I.28, I.34, I.46 |
| `BookI.Prop46.sq` | `Squares.lean` | `sq A B = sq C D → ‖A B‖ = ‖C D‖` ("therefore EF is equal to EG") | I.3, I.4, I.28, I.34, I.46 |
| `foot_between` | `Squares.lean` | the perpendicular from the centre to `AB` falls between `A` and `B`, before III.3 (III.14, III.35, III.36) | I.17, I.19 |
| `Circumference.eq` | `Circumferences.lean` | `circumference α B K C = ∠ B A C + ∠ B A C`, `A` on the circle opposite `K` | III.21 |
| `Circumference.standing` | `Circumferences.lean` | `standing α B A C = ∠ B A C + ∠ B A C` | III.21 |
| `Circumference.centre` | `Circumferences.lean` | `circumference α B K C = ∠ B G C`, the centre `G` opposite `K` | III.20, III.21 |
| `Circumference.whole` | `Circumferences.lean` | the two circumferences on `BC` are `∟ + ∟ + (∟ + ∟)` | III.21, III.22 |
| `Circumference.semicircle` | `Circumferences.lean` | `∟ + ∟`, the centre on `BC`; argued at the measuring point, so not through III.21 | I.5, I.32 |
| `Circumference.lt_semicircle`, `.gt_semicircle` | `Circumferences.lean` | less than `∟ + ∟` beyond the centre, greater on its side | I.32, III.20, III.21 (and III.22) |

`Circumferences.lean` imports III.20–III.22, so until those are proved its users are
"proved, citing propositions still to be proved"; that is expected.

## The statements of III.1–III.37

Hypotheses from the setting-out, conclusions from "I say that". Every statement builds,
and every one was tested in scratch: eighteen proved in full, fifteen by Euclid's route
and three (III.26, III.27, III.30) by the measure, with both porisms; III.3 by its first
part; the rest through their first construction steps (see "Scratch"). In the table,
`∃O` stands for `∃ O : Point, Centre O α` with the circle and Heath's letter for the
centre, and `on X Y Z` for `OnCircle` of each point; the exact Lean is in
`scripts/scaffold_book.py` and the sketches.

| Prop | Lean (hypotheses ⊢ conclusion) | Note |
|---|---|---|
| III.1 | `∃G ABC`, `on A B`, `A ≠ B` ⊢ `∃ F C D E, Centre F ABC ∧ Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ on C E ∧ Between C D E ∧ ∠ A D C = ∟ ∧ Between C F E ∧ ‖C F‖ = ‖F E‖` | The problem with its construction; `G` is Euclid's "if possible, let G be the centre". Proved in scratch, porism too. |
| III.1 Por. | `Centre G ABC`, `on A B`, `Between A D B`, `‖A D‖ = ‖D B‖`, `¬ Collinear A B C`, `∠ A D C = ∟` ⊢ `Collinear D C G` | Cited by III.9, III.10. Prove it from `Prop1`, so the certificate shows III.1. |
| III.2 | `∃D ABC`, `on A B` ⊢ `∀ E, Between A E B → InsideCircle E ABC` | This is System E's Circle 2 (`inside_of_between`); prove it Euclid's way, not by citing it. |
| III.3 | `Centre E ABC`, `on A B`, `Between A F B`, `¬ Collinear A B E` ⊢ `(‖A F‖ = ‖F B‖ → ∠ A F E = ∟ ∧ ∠ B F E = ∟) ∧ (∠ A F E = ∟ → ‖A F‖ = ‖F B‖)` | "CD through the centre" is `FE`; `C`, `D` need no Lean name. First part proved in scratch. |
| III.4 | `∃F ABCD`, `on A B C D`, `Between A E C`, `Between B E D`, `¬ Collinear A C B`, `∀ F, Centre F → ¬ Collinear A C F`, same for `BD` ⊢ `¬ (‖A E‖ = ‖E C‖ ∧ ‖B E‖ = ‖E D‖)` | Two different straight lines (`B` off `AC`): one straight line twice would bisect itself. |
| III.5 | `ABC ≠ CDG`, `CirclesMeet ABC CDG` ⊢ `¬ (Centre E ABC ∧ Centre E CDG)` | `circle_eq` (System E, Diagram-segment 2) does it in a line. Proved in scratch. |
| III.6 | `CirclesTouch ABC CDE C` ⊢ `¬ (Centre F ABC ∧ Centre F CDE)` | As III.5; without, the centre would be within both. Proved in scratch. |
| III.7 | `Centre E ABCD`, `on A D`, `Between A E D`, `Between E F D` ⊢ FA greatest `∧` FD least `∧` (B, C on one side, `∠ A F B < ∠ A F C` → `‖F C‖ < ‖F B‖`) `∧` (G off `AD` → one `H` on the other side with `‖F H‖ = ‖F G‖`, and no other) | Universal, as the enunciation. "Nearer" is Euclid's: the less angle at `F` (Heath, pp. 15–16). |
| III.8 | `∃M ABC`, `OutsideCircle D`, `on A G`, `Between D G A`, `∀ M, Centre M → Between G M A` ⊢ DA greatest `∧` concave nearer greater `∧` DG least `∧` convex nearer less `∧` only two equal | A point is on the concave circumference if the straight line from `D` meets the circle before it, on the convex if after. |
| III.9 | `∃O ABC`, `on A B C`, distinct, `‖D A‖ = ‖D B‖`, `‖D B‖ = ‖D C‖` ⊢ `Centre D ABC` | Euclid's "within" is not used: `ED`, `FD` are drawn through from `E`, `F`, which are within. III.25 needs it so. |
| III.10 | `∃P ABC`, `∃P DEF`, `B G H` on both, distinct ⊢ `ABC = DEF` | As I.7 concludes `C = D`. Heath names `F` too; the proof uses three points. |
| III.11 | `Centre F ABC`, `Centre G ADE`, `TouchesInternally ABC ADE A` ⊢ `Between F G A` | `ADE` within `ABC`. Proved in scratch. |
| III.12 | `Centre F ABC`, `Centre G ADE`, `TouchesExternally ABC ADE A` ⊢ `Between F A G` | Bracketed by Heath; stated and proved all the same. |
| III.13 | `∃G ABDC`, `∃H EBFD`, `∃O ACK` ⊢ (`TouchesInternally ABDC EBFD D ∨ TouchesInternally EBFD ABDC D` → `B` on both → `B = D`) `∧` (`TouchesExternally ACK ABDC A` → `C` on both → `C = A`) | Euclid's two cases, in his one figure. Proved in scratch. |
| III.14 | `Centre E ABDC`, `on A B C D`, `E` off `AB`, `CD`, `F`, `G` the feet (I.12's form) ⊢ `‖A B‖ = ‖C D‖ ↔ ‖E F‖ = ‖E G‖` | Definition 4 is `‖E F‖ = ‖E G‖`, so the enunciation needs `E` and the feet. "[III. 1]": III.1's centre, which is `E`. The feet lie within: `foot_between`. |
| III.15 | `Centre E ABCD`, `on A D`, `Between A E D`, `on B C F G`, `E` off `BC`, `FG`, `H`, `K` the feet, `‖E H‖ < ‖E K‖` ⊢ `‖B C‖ < ‖A D‖ ∧ ‖F G‖ < ‖B C‖` | Definition 5 is `‖E H‖ < ‖E K‖`. `BC` not through the centre: else it would be a diameter. Euclid proves "AD greatest" through `MN`, on `EK`: it needs the more remote `FG`. |
| III.16 | `Centre D ABC`, `on A`, `Between A D B`, `¬ Collinear A B E`, `∠ B A E = ∟` ⊢ (every other point of `AE` is outside) `∧` (every other straight line `AF` has a point within) | The mixed angles go to the mishnah. Proved in scratch. |
| III.16 Por. | `Centre D ABC`, `on A`, `¬ Collinear D A E`, `∠ D A E = ∟` ⊢ `Touches A E ABC` | Cited by III.17, III.33, III.37, Book IV. Prove it from `Prop16`. Proved in scratch. |
| III.17 | `∃E BCD`, `OutsideCircle A BCD` ⊢ `∃ B, on B ∧ Touches A B BCD` | Euclid's construction needs `A` outside. |
| III.18 | `Centre F ABC`, `on C`, `Touches D E ABC`, `Collinear D E C` ⊢ `∀ P, Collinear D E P → P ≠ C → ∠ F C P = ∟` | I.12's form, so citers get `∠ F B D = ∟` at once. Proved in scratch. |
| III.19 | `on C`, `Touches D E ABC`, `Collinear D E C`, `A` off `DE`, `CA` at right angles (I.12's form) ⊢ `∀ F, Centre F ABC → Collinear A C F` | Proved in scratch. |
| III.20 | `Centre E ABC`, `on A B C`, `SameSideOf E A B C` ⊢ `∠ B E C = ∠ B A C + ∠ B A C` | The centre on `A`'s side: the angle at the centre less than two right angles, as Euclid's angles are. All three cases proved in scratch. |
| III.21 | `∃F ABCD`, `on A B D E`, `SameSideOf A E B D` ⊢ `∠ B A D = ∠ B E D` | Any segment: Euclid's case and Simson's. Proved in scratch. |
| III.22 | `∃O ABCD`, `on A B C D`, `OppositeSidesOf A C B D` ⊢ `∠ A B C + ∠ A D C = ∟ + ∟ ∧ ∠ B A D + ∠ D C B = ∟ + ∟` | Proved in scratch. |
| III.23 | `∃O ACB`, `∃O ADB`, `on A B C`, `on A B D`, `SameSideOf C D A B`, `∠ A C B = ∠ A D B` ⊢ `ACB = ADB` | "Similar and unequal" impossible: the circles are one. |
| III.24 | `∃O AEB`, `∃O CFD`, `on A B E`, `on C D F`, `E`, `F` off the bases, `‖A B‖ = ‖C D‖`, `∠ A E B = ∠ C F D` ⊢ `EqualCircles AEB CFD ∧ circumference AEB A E B = circumference CFD C F D` | No superposition. Proved in scratch. |
| III.25 | `∃E ABC`, `on A C` ⊢ `∀ P, ¬ Collinear A C P → ∃ B D E, on B ∧ SameSideOf B P A C ∧ Between A D C ∧ ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E ∧ Collinear D B E ∧` (three cases) | `P` names the side of the given segment, for every such `P`. |
| III.26 | `EqualCircles ABC DEF`, `Centre G`, `Centre H`, `on A B C`, `on D E F`, `OppositeSidesOf A K B C`, `OppositeSidesOf D L E F` ⊢ (`G`, `H` opposite `K`, `L`, `∠ B G C = ∠ E H F` → equal circumferences) `∧` (`∠ B A C = ∠ E D F` → `circumference ABC B K C = circumference DEF E L F`) | Euclid's "whether at the centres or at the circumferences". Compiles in scratch by the measure, which is not the route. |
| III.27 | `EqualCircles`, `Centre G`, `Centre H`, `on A B C`, `on D E F`, triangles `BAC`, `EDF`, `standing ABC B A C = standing DEF E D F` ⊢ `∠ B A C = ∠ E D F ∧ (SameSideOf G A B C → SameSideOf H D E F → ∠ B G C = ∠ E H F)` | Circumferences of any size at the circumferences (IV.11). |
| III.28 | `EqualCircles`, `on A B`, `on D E`, `OppositeSidesOf C G A B`, `OppositeSidesOf F H D E`, `‖A B‖ = ‖D E‖`, `AGB ≤ ACB`, `DHE ≤ DFE` ⊢ `ACB = DFE ∧ AGB = DHE` | `≤` lets diameters in (Heath, p. 60). Proved in scratch. |
| III.29 | `EqualCircles`, `on B C`, `on E F`, `G`, `H` off the bases, `circumference ABC B G C = circumference DEF E H F` ⊢ `‖B C‖ = ‖E F‖` | Any size. Proved in scratch. |
| III.30 | `∃O ADB`, `on A B` ⊢ `∀ P, ¬ Collinear A B P → ∃ D, on D ∧ SameSideOf D P A B ∧ standing ADB A B D = standing ADB D A B` | Compiles in scratch by the measure, which is not the route. |
| III.31 | `Centre E ABCD`, `on A B C`, `Between B E C`, `A ≠ B`, `A ≠ C` ⊢ `∠ B A C = ∟ ∧ (∀ X, on X → SameSideOf X B A C → ∠ A X C < ∟) ∧ ∀ D, on D → OppositeSidesOf B D A C → ∟ < ∠ A D C` | Euclid's figure, with the angle in each segment at every point of it (IV.5 needs the greater at any point), so that a citer wanting only the right angle names neither. The mixed angles to the mishnah. Proved in scratch. |
| III.32 | `∃O ABCD`, `on B D`, `B ≠ D`, `Touches E F ABCD`, `Between E B F` ⊢ (`∀ A`, on, opposite `F` wrt `BD` → `∠ F B D = ∠ B A D`) `∧` (`∀ C`, on, `F`'s side → `∠ E B D = ∠ D C B`) | Every angle in each alternate segment. |
| III.33 | `A ≠ B`, `Triangle C₁ C C₂` ⊢ `∃ AEB E, ∃O AEB ∧ on A B E ∧ ¬ Collinear A B E ∧ ∠ A E B = ∠ C₁ C C₂` | "The angle at C" as I.42 takes an angle. |
| III.34 | `∃O ABC`, `Triangle D₁ D D₂` ⊢ `∃ A B C, on A B C ∧ Triangle B A C ∧ ∠ B A C = ∠ D₁ D D₂` | |
| III.35 | `∃F ABCD`, `on A B C D`, `Between A E C`, `Between B E D` ⊢ `rect A E E C = rect D E E B` | True when the straight lines coincide, or one is through the centre and the other not; take each case. |
| III.36 | `∃F ABC`, `OutsideCircle D`, `on A B C`, `Between D C A`, `Touches D B ABC` ⊢ `rect A D D C = sq D B` | |
| III.37 | `∃F ABC`, `OutsideCircle D`, `on A B C`, `Between D C A`, `rect A D D C = sq D B` ⊢ `Touches D B ABC` | |

### Choices tried and set aside

- **A new kind of magnitude for circumferences.** Faithful to Euclid's arithmetic of
  circumferences, but it needs tacit rules that System E does not have, among them one to
  apply a segment to a segment (III.24); that is the captain's to add, not the first
  mate's. The statements are written in `circumference` and `standing`, so the change
  would touch only the definitions and the ground.
- **The circumference measured at the centre.** Natural for III.26–III.29, but an angle at
  the centre exceeds two right angles for a circumference greater than a semicircle, and
  we have no angle there; nor is the "straight angle" at the centre of a semicircle known
  to be two right angles. The angle at the circumference is always less than two right
  angles, and adds at one vertex (IV.11 will want that).
- **Equal circumferences as a property of chords and sides** (equal radii, equal bases,
  the same side of the centre). It says "equal" well, but not "greater" (III.27, III.28),
  and does not add (IV.11, IV.16).
- **Circles touching as "one point in common"** (no second common point). Then III.13 would
  be the definition. Lean reads "do not cut" of the whole circle, the reading Heath reports
  as Todhunter's (vol. 2, p. 3), made precise by Heath's inside and outside; III.13 stays a
  theorem.
- **Circles touching at the point of contact only**, Heath's own reading, "the circles meet
  at a point but do not cut at that point" (p. 3). Lean has no neighbourhoods to say "at
  that point" in. The whole-circle reading carries instead what Heath says Euclid assumes
  without stating in III.11–III.13, that touching circles do not cross anywhere; III.11's
  mishnah says so.
- **III.20 for every position of the centre.** With the centre on `BC` the angle `BEC` is a
  straight line, which our angles do not measure; beyond `BC`, the angle at the centre
  would be greater than two right angles. Heath: Euclid "had no idea of III. 20 applying
  ... to the case where the angle at the circumference ... is obtuse" (p. 48).
- **III.21 for Euclid's segment only.** Faithful to his proof, but III.22 cites it for
  segments that may be less than semicircles, and Book IV too.
- **III.31's greater segment at `B` only.** Euclid proves it at `B`, the end of the
  diameter; IV.5 cites [III. 31] at a point that is not, and would need III.21 besides. Said
  of every point of the segment, it costs no new citation: III.22 is already among the
  brackets.
- **III.3's converse in I.12's form** (the foot on the straight line, not between its ends).
  The citers of the converse (III.14, III.35, III.36) would then need nothing more, but
  Euclid's III.3 has `F` between `A` and `B`. The shared step `foot_between` gives them the
  `Between`.
- **III.15's "the diameter is greatest" on its own** (`‖E H‖ < ‖E K‖` only in the second
  conjunct). Euclid proves it through `MN`, made on `EK` by cutting off `EL` equal to the
  less `EH`, which needs `EH` less than `EK` (`BookI.Prop3` asks for it); and nothing in the
  *Elements* cites III.15.
- **III.26 and III.27 at the centres through `standing`** (`∠ B G C = ∠ E H F →
  standing ABC B G C = standing DEF E H F`), without the points `A`, `D` on the
  circumferences. Euclid sets out all six letters for one conclusion; a citer of a centre
  part names a point of the circle in a line (`exists_onCircle_oppositeSidesOf`,
  `exists_onCircle_sameSideOf`), as the scratch proofs of III.28 and III.29 now do.
- **Circumferences as a type of their own over `Angle`.** It would stop a statement from
  equating a circumference with an angle, which none does; every law of magnitudes, now
  axioms about `Magnitude k`, would have to be proved again for it. Left to the captain.

## Scratch

The statements were tested in scratch files, committed, not built, in
[`scratch-III/`](https://github.com/jackChallis/stoicheia/tree/81d72f5/docs/reports/crew/scratch-III), as Book II's were. Each compiles with
`lake env lean docs/reports/crew/scratch-III/T20.lean`, against the sketches: a scratch
proof cites a proposition's statement, as a sailor's will.

| File | Proves | Cites |
|---|---|---|
| `T01.lean` | III.1 in full, and its Porism (here before III.1, as a helper; in the voyage the Porism follows III.1 and is proved from it) | I.8, I.10, I.11 |
| `T11.lean` | III.11 in full; III.13 in full, from the statements of III.11 and III.2 | I.20; III.2, III.11 |
| `T16.lean` | III.16 in full, its Porism, III.18 in full | I.12, I.17, I.19 |
| `T20.lean` | III.20 in full, every case: Euclid's two cases and the centre on an arm | I.5, I.13, I.32 |
| `T21.lean` | III.21 in full, Euclid's case and Simson's, from the statement of III.20 | III.20 |
| `T22.lean` | III.22 in full, from the statement of III.21 | I.32, III.21 |
| `T24.lean` | III.24 in full, without superposition | I.5, I.26, I.32, III.20, III.22, the ground |
| `T26.lean` | III.28 and III.29 in full by Euclid's route and their cases, citing III.26 and III.27 at the centres; III.26, III.27, III.30 by the measure (not the route) | I.4, I.5, I.8, I.10, I.11, I.20, III.20, III.26, III.27, the ground |
| `TFirst.lean` | III.5, III.6, III.19, III.31 in full (III.31 at every point of each segment); the first part of III.3; the first steps of III.2, III.4, III.7–III.10, III.12, III.14 (III.1's centre, `foot_between`), III.15, III.17 (two points of the circle, then III.1), III.23, III.25, III.32–III.37 | |

The by-the-measure proofs of III.26, III.27 and III.30 show the statements true; they leave
"in equal circles" unused, which Lean's linter reports, and which is the sign that they
are not Euclid's.

## Citations each sailor should expect beyond Euclid's brackets

The mishnah explains each (STYLE check 19); when a shared step brings it in, a sentence
naming the step is enough. Many of Euclid's steps carry no bracket: "let it be bisected"
(I.10), "let it be drawn at right angles" (I.11, I.12), "let the angle be constructed"
(I.23), "the base is equal to the base" (I.4).

| Prop | Euclid brackets | Expect beyond them | Brought in by |
|---|---|---|---|
| III.1 | I.8 | I.10, I.11 | "bisected at D", "drawn at right angles" |
| III.2 | III.1, I.5, I.16, I.19 | | |
| III.3 | I.8, I.5, I.26 | | |
| III.4 | III.1, III.3 | | |
| III.5 | (Def. I.15 only) | none | `circle_eq` (System E, Diagram-segment 2) does the work |
| III.6 | none | none | `circle_eq`, as III.5 |
| III.7 | I.20, I.24, I.23, I.4 | | the "nearer" angles, a Book Zero step (`crossbar`) |
| III.8 | III.1, I.20, I.24, I.21, I.4 | I.23 | "let the angle DMB be constructed" |
| III.9 | I.8, III.1 (Por.) | I.10 | "bisected at the points E, F" |
| III.10 | III.1 (Por.), III.5 | I.10, I.11 | "bisected", "drawn at right angles" |
| III.11 | none | I.20, III.6 | "AG, GF are greater than FA"; the centres differ |
| III.12 | I.20 | III.2 or III.6 | where `FG` meets the circles |
| III.13 | III.11, III.2 | | |
| III.14 | III.1, III.3, I.47 | I.3, I.4, I.17, I.19, I.28, I.34, I.46 | the feet lie within (`foot_between`); `Prop47.sq`; `Prop46.sq`. The feet are given, so no I.12; III.1 through its centre being `E` |
| III.15 | III.14, I.20, I.24 | I.3, I.11 | "EL made equal to EH", "LM at right angles"; the perpendiculars are given, so no I.12 |
| III.16 | I.5, I.17, I.19 | I.12 | "DG drawn perpendicular" |
| III.17 | III.1, I.4, III.16 | I.11 | "DF drawn at right angles" |
| III.18 | I.17, I.19 | I.12 | "FG drawn perpendicular" |
| III.19 | III.18 | | |
| III.20 | I.5, I.32 | I.13 | Euclid's second figure, by subtraction |
| III.21 | III.20 | | Simson's case uses III.20 again |
| III.22 | I.32, III.21 | | |
| III.23 | I.16 | III.10, III.21 | the segments do not cross; moving `D` onto `AC` |
| III.24 | III.10 | I.5, I.26, I.32, III.20, III.21, III.22 | no superposition; the ground |
| III.25 | I.6, III.9 | I.4, I.10, I.11, I.23 | "the base AE is equal to the base CE"; the construction |
| III.26 | I.4, III.24 | III.21, III.22 | `Circumference.whole` |
| III.27 | I.23, III.26, III.20 | III.21 | `Circumference.centre` |
| III.28 | I.8, III.26 | I.5, I.20, I.32, III.20–III.22 | the ground; two diameters (I.20) |
| III.29 | III.27, I.4 | I.5, I.32, III.20–III.22 | greater circumferences, semicircles; the ground |
| III.30 | I.4, III.28 | I.10, I.11, I.17, III.21, III.22 | the construction; "less than a semicircle" |
| III.31 | I.5, I.32, I.17, III.22 | | |
| III.32 | III.19, III.31, I.32, III.22 | I.11, III.21 | "BA at right angles"; any angle in the segment |
| III.33 | I.4, III.16, III.32, III.31 | I.10, I.11, I.23 | the construction |
| III.34 | I.23, III.32 | I.11, III.16 | "EF drawn touching at B" |
| III.35 | III.3, II.5, I.47 | III.1, I.12, I.17, I.19, I.4, I.28, I.34, I.46 | the centre; the perpendiculars; their feet within (`foot_between`); `Prop47.sq` |
| III.36 | III.18, II.6, I.47, III.3 | III.1, I.12, I.17, I.19, I.4, I.28, I.34, I.46 | as III.35 |
| III.37 | III.18, III.36, I.8, III.16 | III.1, III.17, I.3, I.4, I.28, I.34, I.46 | "DE drawn touching"; `Prop46.sq` |

## Heath's notes before the propositions, and their owners

Heath's notes on the definitions (vol. 2, pp. 1–5) are each quoted once, by one owner;
every other mishnah refers to them in a clause.

| Note | Owner |
|---|---|
| Def. 1, equal circles a definition proper; "can of course be proved by superposition" (p. 2) | III.26 ("since the circles ABC, DEF are equal, the radii are equal") |
| Def. 2, "to meet" and "to touch" (pp. 2–3) | III.17 |
| Def. 3, touching circles: Todhunter's reading (the circles do not cut at all) and Heath's (not at the point of contact), the assumption Euclid leaves tacit in III.11–III.13, internal and external contact (p. 3) | III.11 |
| Def. 7, the angle of a segment, and its part in proofs before Euclid's (p. 4) | III.31 |
| Def. 10, the sector, the shoemaker's knife, an-Nairīzī's wider definition (p. 5) | III.20 |
| Def. 11, De Morgan on "similar" (p. 5) | III.23 |

Heath's long note on III.16, the horn-like angle from Proclus to Wallis, is III.16's own.

## For the sailors

Book I's names take `BookI.` and Book II's `BookII.` in a Book III file; don't
`open BookI` or `open BookII`, since there a bare `Prop4` means III.4.

- **III.1.** `BookI.Prop10` for `D`; `exists_off_line` and `BookI.Prop11` for the
  perpendicular at `D`; `D` is within the circle (`inside_of_between`), so the straight line
  meets it on both sides (`line_circle_beyond` twice); `BookI.Prop10` for `F`. Then
  Euclid's reductio, with `G` the centre from `hABC`: if `G` is off `CE`, the angles `ADG`,
  `GDB` are equal [I. 8] and right, and so equal to `FDB`, "the greater to the less"
  (`onRay_of_angle_eq` puts `G` on `DC`). Heath remarks that Euclid takes for granted that
  the centre on `CE` is its middle point (p. 8): `between_of_inside_chord` and the
  uniqueness of a middle point. Scratch `T01.lean` has every step. Then `Prop1.porism`
  from `Prop1`, first, since III.1 is not proved until it is: III.1's centre lies on the
  perpendicular at the middle point of any straight line in the circle, and there is only
  one such perpendicular. The sentence "At the beginning of Book III. we have nothing more
  to base the proof upon than the definition of a circle ..." (p. 8) is Heath's own, after
  Simson's observation that the proof must be by *reductio*; quote it as Heath's.
- **III.2.** `Prop1` for `D`. Euclid's reductio in Lean is a case split: `E` outside, or
  on, the circle. Do not cite `inside_of_between` (System E's Circle 2) for the
  conclusion: it *is* III.2. The mishnah should say so.
- **III.3.** Scratch `TFirst.lean` proves the first part: I.8, then Definition 10 with
  Postulate 4. The second: `BookI.Prop5.base` and `BookI.Prop26`.
- **III.4.** `Prop1`, then `Prop3` twice: `FE` is at right angles to `AC` and to `BD` at
  `E`. "The less to the greater": one of `B`, `D` is on `A`'s side of `FE`, and
  `onRay_of_angle_eq` puts it on `AC`.
- **III.5, III.6.** Euclid's `EFG` "drawn through at random" meets the circles at one point
  if they share a centre and a point: `circle_eq` (System E, Diagram-segment 2). Use it
  under "the less to the greater: which is impossible", and let the mishnah say that
  Lean's circles are fixed by centre and radius. Scratch `TFirst.lean` has both.
- **III.7.** Four parts. The "nearer" angle is at `F`; Euclid reads off his figure that the
  angle `BEF` is greater than `CEF` (Heath, pp. 15–16, shows how: `FB` meets `EC` within,
  by `crossbar`). "Only two": `BookI.Prop23` on `EF` at `E` on the other side, I.4, and the
  first parts for uniqueness.
- **III.8.** The longest. Prove the four comparisons, then "only two" as in III.7. De Morgan's
  two assumptions (Heath, p. 20), that `K` falls within the triangle `DLM` and `E` outside
  `DFM`, need proof; name them in helpers.
- **III.9.** `BookI.Prop10` for `E`, `F`; I.8 and Definition 10 for the right angles;
  `Prop1.porism` twice; the two straight lines meet only at `D` (`line_unique`), and they
  are two because `A`, `B`, `C` are three points of the circle (`Triangle.of_onCircle`).
  The statement does not ask that `D` be within: Euclid draws `ED`, `FD` through from `E`
  and `F`, which are within (`inside_of_between`), and never uses it. The mishnah says so,
  and that III.25 cites III.9 for a point not yet known to be within. Mind the case where
  `AB` or `BC` passes through `D`, so that `D` is `E` or `F` (Camerer's remark, Heath
  p. 22), which Euclid leaves to the reader; the mishnah says how Lean takes it.
- **III.10.** By contradiction (`Classical.byContradiction`): the centre `P` of `ABC` on two
  perpendicular bisectors (`Prop1.porism`), likewise of `DEF`; then `Prop5` with
  `⟨B, G, ...⟩ : CirclesMeet`.
- **III.11.** Scratch `T11.lean`, the whole proof. `F ≠ G` is III.6 (`circle_eq` in
  scratch: cite `Prop6`); `G` is within `ABC`; `FG` produced meets `ABC` at `H`; if `H` is
  not `A`, the point `D` of `ADE` beyond `G` at the distance `GA` falls outside `ABC`. The
  case of `A` on the straight line `FG` is `between_of_inside_chord`. The mishnah owns
  Heath's note on Definition 3: Lean's definitions are the whole-circle reading, which
  Heath reports as Todhunter's and does not himself prefer, made precise by his inside and
  outside; they carry what he says Euclid assumes without stating in III.11–III.13, that
  touching circles do not cross anywhere. Say it plainly, with his words.
- **III.12.** As III.11, outside: `FG` meets `ABC` at `C` and `ADE` at `D`; were `D` not
  beyond `C`, a point between them would be within both circles.
- **III.13.** Scratch `T11.lean`, the whole proof, both cases (one figure).
- **III.14.** "Let the centre ... be taken [III. 1], and let it be E": `Prop1 ⟨E, hE⟩ hA hB`
  and `centre_unique` (the orders give the two lines), so that III.1 is cited where Euclid
  brackets it. `E` and the feet are in the statement because Definition 4 measures from
  them; they are given, so I.12 is not cited, and the mishnah says why in a sentence. The
  feet lie between `A`, `B` and `C`, `D`: `foot_between` (adds I.17, I.19). Then `Prop3`,
  `BookI.Prop47.sq`, `CommonNotion3`, and `BookI.Prop46.sq` for "therefore EF is equal to
  EG". "AB is double of AF": `Magnitude.eq_of_add_self_eq`. Scratch `TFirst.lean` has the
  first steps.
- **III.15.** `BookI.Prop3` cuts `EL` off `EK` (first steps in `TFirst.lean`); `BookI.Prop11`
  for `LM`; `Prop14` gives `BC = MN`; I.20 and I.24 as Euclid. That the angle `MEN` is
  greater than `FEG` is read off the figure: prove it. The perpendiculars `EH`, `EK` are
  given, so I.12 is not cited.
- **III.16.** Scratch `T16.lean`, the whole proof; Euclid's reductio for the first part
  ("let it fall within as CA") may replace the scratch's direct argument. The Porism from
  `Prop16`: produce `AD` to `B`.
- **III.17.** "Let the centre E of the circle be taken [III. 1]": the statement gives the
  circle no point, so first take the centre `E₀` from `hBCD`, then two points of the circle
  on the straight line `E₀A` (`line_circle_between` toward `A`, `line_circle_beyond` away
  from it), then `Prop1` on those two, and `centre_unique` to make its centre `E₀`. Scratch
  `TFirst.lean` has it; the mishnah says why in a sentence. Then `D` where `EA` meets the
  circle (the first of those two points); `Postulate3 E A`; `BookI.Prop11` at `D`; `F`,
  then `B` where `EF` meets `BCD`; I.4; `Prop16.porism`; `Touches.of_collinear` to read
  `BA` as `AB`. The mishnah owns Heath's note on Definition 2.
- **III.18.** Scratch `T16.lean`, the whole proof.
- **III.19.** Scratch `TFirst.lean`, the whole proof.
- **III.20.** Scratch `T20.lean`, the whole proof: Euclid's first case (`crossbar` puts
  `AE` produced across `BC`), his second (`case_across`), and the centre on an arm. One
  figure carries both his cases, as in Heath.
- **III.21.** Scratch `T21.lean`, the whole proof: Euclid's case is III.20 twice; for the
  rest, Simson's (Heath, pp. 49–50), with `SameSideOf.of_cross` for where the points lie.
- **III.22.** Scratch `T22.lean`, the whole proof.
- **III.23.** If the circles differ, `C` is not on `ADB` (`Prop10`); `AC` meets `ADB` again at
  `D'` (on `AC` or `AC` produced); `Prop21` moves `D` to `D'`; then I.16.
- **III.24.** Scratch `T24.lean`, the whole proof, without superposition. Euclid's sentences
  of applying the segment are carried by the Lean that compares the angles at the centres;
  the mishnah says so, and Heath's note that "the first two hypotheses are disposed of by a
  tacit reference to the preceding proposition III. 23" (p. 54) is this page's.
- **III.25.** `BookI.Prop10`, `BookI.Prop11` on `P`'s side, `B` where the perpendicular meets
  the circle; the three cases by `lt_trichotomy`; `BookI.Prop23`, `BookI.Prop6`, I.4,
  `Prop9` for "will also pass through the remaining points", in every case: III.9 does not
  ask that `E` be within, which in the first case (beyond the segment) nothing yet shows.
- **III.26.** Euclid's route: radii (`EqualCircles.radii`), I.4 for `BC = EF`, `Prop24` for the
  segments, `Circumference.whole` and `CommonNotion3` for "the circumference BKC which
  remains". For the second conjunct, the central angles are equal by `Prop20` when the
  circumference is less than a semicircle; otherwise use the remaining circumferences. The
  measure alone (scratch `T26.lean`) is not the route.
- **III.27.** Euclid's reductio for the centres (`BookI.Prop23`, `Prop26`,
  `Circumference.centre`, `angle_add_of_within` for "the less to the greater"), then
  `Prop20`; for circumferences greater than semicircles, `Circumference.standing`.
- **III.28.** Scratch `T26.lean`, the whole proof, citing `Prop26` at the centres: a point of
  each circle on the other side of the base (`exists_onCircle_oppositeSidesOf`) fills
  III.26's setting-out.
- **III.29.** Scratch `T26.lean`, the whole proof, citing `Prop27` at the centres: a point of
  each circle on the centre's side (`exists_onCircle_sameSideOf`), and
  `standing_eq_circumference`.
- **III.30.** Euclid's route through `Prop28`: `AD`, `DB` are less than semicircles
  (`Circumference.standing` and I.17 on the isosceles triangle `ADB`), so their
  complements are greater (`Circumference.whole`). Scratch `T26.lean` has the construction.
- **III.31.** Euclid's route, I.5, I.32, Definition 10, I.17, then `Prop22` for `ABCD` (read
  as `BCDA`, `hBD.swap`), for any `D` of the less segment. For any `X` of the greater: a
  point `D` of the less (`exists_onCircle_oppositeSidesOf`) and `Prop22` for `AXCD`, under
  "and it is the angle in the segment ABC greater than the semicircle". Scratch
  `TFirst.lean` proves it all, with the ground's semicircle in place of Euclid's first
  steps; take his. The right angle `CAF` comes on the way ("therefore each is right"). The
  mixed angles: a `--` line each, no Lean, and the mishnah.
- **III.32.** `BookI.Prop11` for `BA` (first steps in `TFirst.lean`), `Prop19`, `Prop31`, I.32,
  `Prop22`; `Prop21` to pass from Euclid's `A` and `C` to any.
- **III.33.** Three cases by `lt_trichotomy`; `BookI.Prop23`, `BookI.Prop10`, `BookI.Prop11`, I.4,
  `Prop16.porism`, `Prop32`, `Prop31`.
- **III.34.** First steps in `TFirst.lean`: a point `B`, the tangent at it by `Prop16.porism`;
  then `BookI.Prop23` and `Prop32`.
- **III.35.** `Prop1`; the case where `E` is the centre is in `TFirst.lean`. Otherwise
  `BookI.Prop12` for `FG`, `FH`, `foot_between` for their feet within, `Prop3`,
  `BookII.Prop5` (mind its `D ≠ C`: when `E` is the foot `G`, `rect_congr` and `sq_self` do
  it), `BookI.Prop47.sq`. Two figures, side by side.
- **III.36.** `Prop1`, `Prop18` (first steps in `TFirst.lean`), `BookII.Prop6`,
  `BookI.Prop47.sq`; the second case with `BookI.Prop12`, `foot_between` and `Prop3`. Two
  figures, side by side.
- **III.37.** `Prop17`, `Prop36` and `BookI.Prop46.sq` (first steps in `TFirst.lean`), then
  I.8, and `Prop16.porism`. "Even if the centre be on AC" is a case.

## Looking ahead, and the risks

- **The measure's shortcuts.** By the measure, III.26, III.27 and III.30 follow in a few
  lines. The orders ask for Euclid's route; the linter flags an unused "equal circles";
  the bosun should check that each certificate's "Lean cites" contains Euclid's brackets.
  One bracket is left out by design: III.24's [III. 10], since Lean has no superposition
  there (the brief). III.14's and III.17's [III. 1] are cited through III.1's centre.
- **System E proves some of Book III.** Circle 2 is III.2; Diagram-segment 2 (one centre
  and radius, one circle) makes III.5 and III.6 a line each; Generalities 2 (one centre) is
  the end of III.1's reductio. The mishnah of each should say so plainly.
- **Long proofs.** III.7, III.8 (diagram facts De Morgan points out), III.20 and III.21
  (cases; scratch has them), III.24 (no superposition; scratch has it), III.25 (three
  cases), III.33 (three cases), III.35 and III.36 (two cases each).
- **Centres by hypothesis.** `∃ O, Centre O α` appears in most statements; III.1 is the
  ceremony that takes the centre. If the captain adds Definition 15's other half, these go.
- **Book IV.** IV.11 adds circumferences: Book IV's first mate will need
  `Circumference.add` (a circumference cut at a point of it is the two it is cut into),
  from III.21. IV's uses of III.1, 16, 17, 21, 22, 26, 27, 29, 30, 31, 32, 36 and 37 fit these
  statements.
- **Figures.** Heath has two or three figures for III.25, III.33, III.35 and III.36; III.7,
  III.8, III.13 and III.20 have one each, carrying every case. III.3's `C`, `D` and
  III.16's `B`, `C`, `H` are in the figure though the Lean needs them only in the proof, if
  at all. STYLE check 20 now drops "PORISM" (III.1, III.16).
- **III.12** is bracketed by Heath as an interpolation; its page shows both brackets, and
  its mishnah should open by saying so, and quote his note (p. 28).

## Housekeeping

- `lake build` (134 jobs) passes; the only warnings are the sketches' `sorry`.
  `lake env lean Certificate/Facts.lean` writes 99 propositions; Books I and II's 62
  entries equal the tag's. `python3 scripts/check_fidelity.py` passes for all 99.
- `python3 scripts/render.py` leaves `book/I/` and `book/II/` byte for byte as at `book-I`
  and `book-II`, and adds `book/III/` and Book III's sections of `CERTIFICATE.md` and
  `GRAPH.md`.
- The scratch proofs in `scratch-III/` compile against the sketches, and the certificate's
  walk, run over each in scratch, finds the citations the tables give.
- All thirty-seven statements and the two porisms in `scripts/scaffold_book.py` match the
  Lean files, which the scaffold made: rendered again, each file comes out byte for byte.
- New modules are listed in `Elements.lean`; `Basics.lean` gathers
  `Elements/Figure/OnCircles.lean`.
- Changed besides: `docs/briefs/0002-decisions.md`, `docs/STYLE.md` (§3 and §6 for a third
  book and Heath's second volume), `CONTRIBUTING.md` and `README.md` (Book III).

## Challenges and answers

Twenty-six challenges came back on this work, each answered here: fixed, or shown not to
be a problem. Some are one point found twice (1 and 16, 3 and 21, 4 and 15, 6 and 22).
Where an answer rests on Lean, the check was run in scratch.

1, 16. **`Circumference.semicircle` cites III.21, not only I.5 and I.32.** True of its proof,
which measured the circumference at a point of its own choosing and moved there by
`Circumference.eq`. Fixed in the proof, not the lists: Euclid's argument (I.5, I.32) holds
at every point of the circle, so it now runs at the point Lean measured
(`Classical.epsilon_spec`), and III.21 is not needed. The certificate's walk over the
ground now gives `[I.5, I.32]` for it, and every other ground lemma agrees with its
docstring and the tables, which stand.

2. **Definition 3 credited the wrong reading to Todhunter.** True. Heath (p. 3): "Todhunter
thinks" the circles do not cut at all; Heath prefers "that the circles meet at a point
but do not cut at that point". Lean's definitions are the whole-circle reading, made
precise by Heath's inside and outside. Corrected under "Choices tried and set aside", in
the brief (Heath prefers the local reading, which Lean cannot say without
neighbourhoods; the definition carries what he says Euclid leaves tacit in
III.11–III.13), in `0002-decisions.md`, and in the III.11 note, whose mishnah owns the
note on Definition 3.

3, 21. **"The diameter BD" in III.22, and "one of the three".** True: `BD` joins opposite
corners and need not pass through the centre. The brief says "the straight line `BD`
(joining opposite corners)", and `CirclesTouch` is "either within the other, or without".

4, 15. **III.14's centre and feet are hypotheses, so its "[III. 1]" and I.12 have nothing
to cite; III.15's perpendiculars likewise; the centre rule is broken.** The statement
keeps `E` and the feet: Definition 4 measures from them, and the enunciation cannot be
said without them. "[III. 1]" is still cited: the proof takes III.1's centre and shows it
is `E` (`Prop1 ⟨E, hE⟩ hA hB`, `centre_unique`), as III.4 and III.8 take theirs, and as
Euclid writes "let the centre ... be taken [III. 1], and let it be E". Scratch `T14` does
it, and its walk cites III.1, III.3, I.17, I.19. I.12 is gone from both rows (the feet are
given). The brief now has a third case in its rule: where the enunciation measures from
the centre (III.14, III.15).

5. **III.31's angle CAF.** True: the Lean states that `BAC` is right; `CAF` is shown in the
proof, where Euclid finds `BAC` equal to `FAC` and each right. The brief now says so. Not
added to the statement: nothing cites it.

6, 22. **The comment in `heath/III/09.md`.** Fixed: "the scripts read it as a citation of
III. 1."

7. **III.9's `hD` blocks III.25.** Chose (a), and dropped it. Euclid draws `ED`, `FD` through
from `E` and `F`, which are within, and never uses that `D` is; Simson's proof, which
Heath says needs III.8 (p. 3), is the one that would. III.25 can now cite III.9 in all
three cases. The III.9 and III.25 notes say so; scratch `T09` builds with the new
statement.

8. **III.31's greater segment only at `B`.** Adopted:
`∀ X, OnCircle X ABCD → SameSideOf X B A C → ∠ A X C < ∟`. Scratch `T31` proves it at any
`X` with a point `D` of the less segment and `Prop22` for `AXCD`, so no new citation (its
walk: I.5, I.17, I.32, III.21, III.22, the III.21 coming from the scratch's shortcut
through the ground's semicircle, which the note tells the sailor not to take). "Later: the
general III.31" is gone from the brief.

9. **III.15's "the diameter is greatest" cannot be cited alone.** Not changed. Euclid proves
`AD` greater than `BC` through `MN`, made on `EK` by cutting off `EL` equal to `EH`, and
`BookI.Prop3` asks for the less: `(h : ‖C₁ C₂‖ < ‖A B‖)`, here `‖E H‖ < ‖E K‖`. With
`hnearer` moved into the second conjunct, the first could not go Euclid's way. And
nothing cites III.15: in the OCR of Heath's three volumes the only "[III. 15]" is in his
note on III.28, whose two diameters the III.28 scratch handles by I.20.

10. **III.3's converse wants `Between`; every citer has `Collinear`.** Adopted: `foot_between`
in `Squares.lean`, before III.1: the perpendicular from the centre to a straight line in
the circle, not through the centre, falls between its ends. Proved, citing I.17 and I.19
(the walk agrees). Named in the orders' shared steps and the III.14, III.35, III.36 notes.

11. **The centre parts of III.26 and III.27 carry points they do not use.** Not changed:
Euclid's setting-out has all six letters for one conclusion, and a citer names a point in
one line. To show it, the scratch proofs of III.28 and III.29 now cite `Prop26` and
`Prop27` at the centres (`exists_onCircle_oppositeSidesOf`, `exists_onCircle_sameSideOf`,
`standing_eq_circumference`); their walks have III.26 and III.27 where Euclid brackets
them. Before, they went by `Circumference.centre` and would have left those brackets
uncited.

12. **`circumference` is an `Angle`.** Left to the captain, and put in the brief's "Later". No
statement of Book III equates a circumference with an angle or adds one to an angle; they
are compared only with each other (III.24, III.26–III.30). A type of their own would need
every law of magnitudes proved again, those laws being axioms about `Magnitude k`; a new
`Kind` would need an axiom tying it to angles, which the first mate cannot add.

13. **Citers of a porism are certified as sketched.** Chose (a). `Certificate/Facts.lean`
records a citation of `PropN.porism` as one of PropN and stops there, as at a
proposition. A scratch citer of `Prop1.porism` now walks to `[III.1]` with no `sorry`
seen: "proved, citing propositions still to be proved". A proposition's status also
counts its porism, so III.1 reads "sketched" until its porism is proved. Books I and II's
entries in `facts.json` are unchanged; I.15's Porism is cited by nothing. The orders say
it, and ask the III.1 and III.16 sailors to prove the porisms first.

14. **III.17 has no two points for III.1.** Fixed in the note and the orders: the centre `E₀`
from `hBCD`, two points of the circle on `E₀A` (`line_circle_between`,
`line_circle_beyond`), `Prop1` on them, `centre_unique`. Scratch `T17` does it; its walk
cites III.1.

17. **The figures.** True. The page images show one figure each for III.7 (n26), III.8 (n30),
III.13 (n44) and III.20 (n58), and two for III.36 (n86). The orders and this report now
name III.25, III.33, III.35 and III.36, and speak of two cases in one figure for III.13 and
III.20; so does the brief, and scratch `T20`'s comments.

18. **"PORISM" in check 20.** Fixed in `docs/STYLE.md` for every book (`-e 's/PORISM\.//'`).
Run on `heath/III`, III.1 gives A to G and III.16 A to H; I.15's Porism is in brackets and
was never read.

19. **Simson and Heath.** True (p. 8, the flattened OCR agrees). The brief now has Simson's
observation and Heath's explanation as his own, and the III.1 note says to quote it as
Heath's.

20. **"Intersections 3".** Fixed to "Intersection 3" in `OnCircles.lean` and the brief. Every
other rule label in the Book III files matches a docstring in `Elements/Foundations`.

23. **Three slips.** Fixed: "the longest since Book I"; "eighteen proved in full, fifteen by
Euclid's route and three by the measure"; III.5 and III.6 on rows of their own.

24. **"Read first" and "Shared steps".** Fixed: `Transfer.lean` in "Read first"; the squares
bullet split into Book III's ground, Book II's, and Book Zero's, which adds nothing.

25. **III.12's closing bracket with no opening one.** The heading keeps Heath's opening
bracket as printed, `# [Proposition 12` (leaf n39), and `render.py` puts it before the
enunciation on the page (`heath.bracketed`); the comment says so. The III.12 mishnah is
asked to open with the bracket. Pages of Books I and II are unchanged.

26. **"Tangent" and "chord" in names.** III.17's title is now "Drawing a straight line to touch
a circle"; III.19 and III.36 keep "tangent", which their enunciations use. Book Zero's
module is now `Elements/Figure/OnCircles.lean`, not `InCircles`, which a reader of Book IV
could take for the inscribed circle.
