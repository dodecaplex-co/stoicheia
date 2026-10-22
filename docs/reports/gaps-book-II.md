# What Euclid takes for granted: Book II

A running catalogue of the steps in Book II that Euclid takes without saying why,
found by writing his proofs out in Lean. It carries on
[the catalogue for Book I](gaps-book-I.md), whose introduction names those who
noticed Euclid's gaps, or formalized the Elements, before us;
[*Does the Proof Prove It That Way?*](https://arxiv.org/abs/2608.15432) (Pistis),
which catalogues 52 gaps in Books I–III, is its companion here too. Book II reckons
with rectangles and squares as areas, and most of what it takes for granted is of two
kinds: where the points of a figure fall, and that the figure drawn is the rectangle
or square Euclid names. Where we know who saw a gap first, we say so; nothing here is
meant to be new.

Each entry names the Lean lemma or tacit rule that fills the gap. Book II's proofs
cite Book I's propositions with their book, as `BookI.Prop47`, and the steps they
share, each citing Book I, live in
`Elements/BookII/Rectangles.lean`: one right angle makes a parallelogram a rectangle
(`Rectangle.of_right`, I.29); rectangles contained by equal straight lines are equal,
so that a rectangle or square drawn is the one Euclid names (`Rectangle.contained`,
`Rectangle.eq_rect`, `Square.eq_sq`, I.4 and I.34); a square that I.46 describes is
a parallelogram (`Square.described`, I.28); the parallelograms about the diameter of
a square are squares (`Square.about_diameter`, I.5, I.6, I.29, I.34); the figure of
II.4–II.8 and its gnomon (`Parallelogram.figure`, `Parallelogram.complements`,
`Parallelogram.about_diameter`, I.30 and I.31); and I.47 said of the squares on
straight lines, which it describes by I.46 (`BookI.Prop47.sq`). These, with the steps
below that Euclid takes without a word, or where Heath gives no reference, are why
[CERTIFICATE.md](../../CERTIFICATE.md) shows the Lean citing more of Book I than
Heath's references give in every proposition of Book II.
Steps of Book I that cite I.28, I.30 or I.31, such as `BookI.Prop30.meet`, are in
`Elements/BookI/HelpersParallels.lean`; the two lemmas particular to one figure,
`Prop8.cell` and `Prop13.not_beyond`, live in its file; and the rest are Book Zero's
(`Elements/Figure/`) or tacit rules.

## II.1
- "Let BG be made equal to A" carries Heath's reference [I. 3], but I.3 cuts off only from the greater of two straight lines, and I.11 gives BF no length. Our proof first sets out a straight line equal to A at B, by I.2, which Euclid does not use, and produces BF beyond it (`produce_longer`, as in I.11 and I.16).
- Every given point lies on BC, and BF stands on a side of it that Euclid leaves to his figure. `exists_off_line` finds a point off BC where the two circles of I.1 cut one another (Post. 3, Def. I.15; `circles_meet`, System E, Intersection 5). Each of II.1–II.11 needs such a point, with no letter in Euclid's figure, before its first square or perpendicular.
- Euclid names K, L, H, where DK, EL, CH meet GH, without asking whether they do. A straight line meeting one of two parallels meets the other (`BookI.Prop31.parallelogram`, through `BookI.Prop30.meet`, from I.30), a lemma Proclus states in his attempt to prove Postulate 5 (Heath, vol. 1, p. 207). I.30 also makes DK, EL, CH parallel to one another (`BookI.Prop30.parallel`), once `Parallel.off_transversal` has shown them different straight lines.
- "Then BH is equal to BK, DL, EH" has no reason given. K and L lie between G and H, in the order of D and E on BC, because parallels keep order (`Parallel.between`), and a parallelogram cut by a parallel to two of its sides is the two parallelograms it is cut into (`quadArea_add_of_parallelograms`).
- "Now BH is the rectangle A, BC, for it is contained by GB, BC" takes two things for granted. That BH is right-angled, though only its angle at B was drawn right: one right angle makes a parallelogram a rectangle (`Rectangle.of_right`), as Heath remarks under II.4, and DL and EH have right angles at D and E because these lie beside right angles (`adjacent_eq_of_right`, System E, Diagram-angle 3, now proved after I.13 by taking one right angle from two). And that rectangles contained by equal straight lines are equal, so that the rectangle drawn is the rectangle named. Our `rect` (Definition II.1) is any rectangle contained by the two straight lines, and we prove once that they are all one area (`Rectangle.contained`, `Rectangle.eq_rect`). Every proposition of Book II needs it.
- The enunciation cuts BC into "any number of segments whatever"; the setting-out, and our main theorem, cut it at two points, D and E. Our companions cut it at any number, repeating the construction one segment at a time: of three or more points in order, the second lies between the first and the last (`InOrder.between_end`), so the first segment can be cut off and the rest taken as before.

## II.2
- Our I.46 describes a square as Definition I.22 has it, with four equal sides and four right angles. That it is also a parallelogram, as Euclid's construction makes it, is I.28 (`BookI.Prop28.square`, inside `Square.described`), as for the squares of I.47 in Book I.
- "Let CF be drawn through C parallel to either AD or BE": Heath's reference [I. 31] is I.31, but "either" is I.30, as in I.44 and I.47 (`BookI.Prop30.parallel`). F, where CF meets DE, comes from `BookI.Prop31.parallelogram`, and lies between D and E (`Parallel.between`), so that AF and CE make up AE.

## II.3
- "Let ED be drawn through to F" names F before saying where it is: where the parallel through A meets DE produced, from I.30 (`BookI.Prop31.parallelogram`). D lies between F and E, as C lies between A and B (`Parallel.between`).
- "AD is the rectangle AC, CB" needs AD right-angled, but the square's right angle at C is BCD. DCA lies beside it, and so is right (`adjacent_eq_of_right`); `Rectangle.of_right` does the rest.

## II.4
- "Through C let CF be drawn parallel to either AD or EB, and through G let HK be drawn parallel to either AB or DE" names G, where CF crosses the diameter BD, without saying so, and Euclid reads off his figure where each parallel meets the sides. `Parallelogram.figure` draws this figure once, for II.4–II.8: I.31 draws the parallels, `BookI.Prop30.meet` finds where each is cut, and `Parallel.between` puts each point between the ends of its side.
- "I say next that it is also right-angled": Euclid proves all four angles of CGKB right. The proof attributed to Theon stops at the angle at B, which Heath calls "a legitimate abbreviation of the genuine proof; because there can be no need to repeat exactly that part of the proof of I. 46 which shows that all the angles of the figure there constructed are right when one is" (vol. 1, p. 381). The rest of Book II takes it for granted; we prove it once (`Rectangle.of_right`).
- "For the same reason HF is also a square": the parallelograms about the diameter of a square are squares. The Greek text states this after II.4 as a porism, which Heath calls "undoubtedly interpolated"; Heiberg doubted it and conjectured that Theon may have added it, and a papyrus fragment lacks it (vol. 1, p. 381). II.5–II.8 take it for granted ("LG, which is equal to the square on CD"). We prove it once, as `Square.about_diameter`.
- At "Now, since AG is equal to GE" Heath gives no reference: it is I.43. That the complements AG and GE are parallelograms, as "AG is the rectangle AC, CB" needs, is I.30 (`Parallelogram.complements`).
- "But HF, CK, AG, GE are the whole ADEB": the parallelograms about the diameter and the complements make up the whole (`Parallelogram.about_diameter`), cut along HK and then along CF (`quadArea_add_of_parallelograms`). A gnomon (Definition II.2) is three of these four taken together, so it needs no Lean word of its own.

## II.5
- The setting-out does not say on which side of C the point D falls, and Euclid's figure puts it between C and B. Reading II.5 as the solution of a quadratic, Heath remarks that "Euclid's figure corresponds to one only of the two solutions" (vol. 1, p. 384). We prove Euclid's case and get the other by exchanging A and B (`lt_trichotomy`, `OnRay.eq_of_len_eq`).
- "And again through A let AK be drawn parallel to either CL or BM": K, where AK meets KM, comes from I.30 (`BookI.Prop31.parallelogram`), and I.30 again makes AK parallel to DG, so that AH is a parallelogram (`BookI.Prop30.parallel`). L lies between K and H (`Parallel.between`), so that "the whole AH" is AL and CH together.
- "Let LG, which is equal to the square on CD": LG is a square about the diameter (`Square.about_diameter`), and on CD because its side HL is equal to CD by I.34, for which Heath gives no reference here. "DH is equal to DB" in the same way, DM being a square.

## II.6
- As in II.5, with D beyond B: K comes from `BookI.Prop31.parallelogram`; L lies between K and M (`Parallel.between`), so that AM is AL and CM together; BM and LG are squares about the diameter (`Square.about_diameter`), so that DM is equal to DB; and HL is equal to BC by I.34, for which Heath gives no reference.

## II.7
- "And let the figure be drawn": five words for two parallels and the points where they meet, II.4's figure (`Parallelogram.figure`), and Heath gives no reference for I.31 or I.30.
- "But AF, CE are the gnomon KLM and the square CF": AF and CE overlap in CF, so together they count it twice. Euclid reads AF off his figure; our proof shows it a parallelogram, its sides lying along those of CF and of ADEB, and a rectangle from the square's right angle at B (`Rectangle.of_right`).
- CF and DG are squares about the diameter (`Square.about_diameter`), and DG is the square on AC because GH is equal to CA, by I.34, for which Heath gives no reference.

## II.8
- At "Let the square AEFD be described on AD" Heath gives no reference: it is I.46. "Let the figure be drawn double" is `Parallelogram.figure` twice, through B and through C; where a parallel of one figure crosses a parallel of the other, at G and at R, `BookI.Prop30.meet` finds the point. Our proof puts every point of the double figure in order (`Parallel.between`) and shows its cells to be parallelograms (`Prop8.cell`), as I.36 and I.43 need.
- "CB is equal to GK, and BD to KN", and "BK, that is CG", are I.34, and Heath gives no reference. "BD is equal to BK" and "GK, that is GQ" are the porism of II.4, KD and GR being squares about a diameter (`Square.about_diameter`).
- "The eight areas, which contain the gnomon STU, are quadruple of AK" takes AK to be AG and CK together, and the eight areas to make up the gnomon's three parallelograms (`quadArea_add_of_parallelograms`, `Parallelogram.about_diameter`).

## II.9
- At "Let CE be drawn from C at right angles to AB" Heath gives no reference: it is I.11. "Let it be made equal to either AC or CB" is a circle about C (`OnRay.exists_len_eq`, Post. 3), so I.3 is not needed. "The angle EAC is also equal to the angle AEC" is I.5, again with no reference from Heath.
- "Let DF be drawn through D parallel to EC, and FG through F parallel to AB" is I.31, for which Heath gives no reference (`BookI.Prop31.line`). F, where DF meets EB, comes from `BookI.Prop30.meet`, and G, where FG meets CE, from `BookI.Prop31.parallelogram`. Euclid's figure puts F between E and B and G between E and C, as the angles he takes at F and G need: `Between.of_sameSide` carries the order of C, D, B across DF, and of E, F, B across FG.
- "Half a right angle": Our Lean has no word for a half. An angle is half a right angle when, added to itself, it makes a right angle, and two such halves are equal, the halves of equal things being equal (`Magnitude.eq_of_add_self_eq`), the step Heiberg brackets in I.37. "Therefore the whole angle AEB is right" adds the halves at E, which needs C between A and B (`angle_add_of_between`).
- From here on, Heath notes, "the method of demonstration by showing in the figures the various rectangles and squares to which the theorems relate is here abandoned" (vol. 1, p. 394). The squares that I.47 compares are not drawn, and `BookI.Prop47.sq` describes them by I.46 and names each the square on its side, in II.9–II.14. Here Heath gives no reference at its second use, for the square on EF.
- D may fall on either side of C, as in II.5; on A's side, exchanging A and B gives Euclid's figure.

## II.10
- "Let it be made equal to either AC or CB [I. 3]": I.3 needs a greater straight line to cut from, so the perpendicular is produced far enough first (`produce_longer`, as in II.1).
- At "Therefore the angles FEB, EFD are less than two right angles" Heath gives no reference. EB falls within the angle CEF, B being on F's side of EC and on C's side of EF (`angle_add_of_within`); the part is less than the whole (C.N. 5); and adding the same to unequals keeps them unequal, the tacit rule of magnitude `add_lt_add_right`, as in I.17.
- Postulate 5, as Euclid calls on it here, "[I. Post. 5]" in Heath's reference, leaves out its conditions, as Heath remarks of it under I.29. `Postulate5` asks for the straight lines through E and B, through E and F, and through F and D, with B and D on one side of EF, and puts the meeting G on that side. Our proof then shows that B lies between E and G, and D between F and G (`Between.of_inside`, `Between.of_sameSide`), as "if produced in the direction B, D" says and I.15 at B needs.

## II.11
- At "Let AC be bisected at the point E" Heath gives no reference: it is I.10.
- "Let CA be drawn through to F, and let EF be made equal to BE": a circle about E lays EF off along EA produced (`OnRay.exists_len_eq`, Post. 3, Def. I.15), the circle Heath finds in Simson's solution, which "describes a circle with EB as radius cutting EA produced in F" (vol. 1, p. 403). That F falls beyond A, Euclid reads off his figure: the angle ABE is less than the right angle BAE (I.17), so EB is greater than EA (I.19), and EF, equal to EB, reaches past A (`OnRay.between_of_len_lt`).
- "Let the square FH be described on AF": its side AH lies along AB, for the angle FAB, beside the square's right angle CAB, is right (`adjacent_eq_of_right`), and on one side of a straight line only one ray makes a given angle (`onRay_of_angle_eq`). H falls within AB because AF is less than AB: EA and AF together make EF, equal to EB, which is less than EA and AB together (I.20; `Magnitude.lt_of_add_lt_add_left`). Euclid's figure shows both; he gives a reason for neither.
- "And let GH be drawn through to K": K, where GH meets CD, comes from `BookI.Prop30.meet`, since GH meets AB, the parallel to CD, at H. G, H, K and C, K, D lie in order (`Parallel.between`), so that FK is FH and AK together, and AD is AK and HD, as "let AK be subtracted from each" needs.

## II.12
- "Let BD be drawn from the point B perpendicular to CA produced": Euclid's figure puts the foot D beyond A. Our statement gives the perpendicular and its foot on the straight line CA, and our proof finds where the foot falls. It is not A, where the angle BAC would be right, nor on the ray from A through C, where the triangle ABD would have an obtuse angle and a right angle, against I.17. So C, A, D lie in that order (`between_cases`, System E, Between 6), as "the straight line CD has been cut at random at the point A" needs for II.4.

## II.13
- "Let AD be drawn from the point A perpendicular to BC": Euclid's figure puts D within BC, as "the straight line CB has been cut at random at D" needs for II.7. We prove it from the acute angles at B and C. D is not B or C, where the acute angle would be right; nor beyond either end, for the angle beside the acute one would be obtuse (I.13), and no triangle has an obtuse angle and a right angle (I.17). `Prop13.not_beyond` says so, and is used at B and at C.
- The enunciation is of acute-angled triangles, yet the setting-out adds "having the angle at B acute", and Heath remarks that "the last words have no point if all the angles of the triangle are necessarily acute" (vol. 1, p. 407). The Greek scholiast, and Isaacus Monachus, Campanus, Peletarius, Clavius and Commandinus, noticed early that the relation holds at an acute angle of any triangle (vol. 1, p. 407). Euclid's route through II.7 needs the angle at C acute as well, so our statement asks for acute angles at B and C, and for nothing at A.
- "And the square on AC is equal to the squares on AD, DC" is I.47 again, and Heath gives no reference.

## II.14
- "Let A be the given rectilineal figure": it may have any number of sides. Any rectilineal area, Heath says under I.45, "can of course be resolved into triangles" (vol. 1, p. 347). That the figure can be cut into triangles, and that another cutting gives the same whole, are the steps taken for granted under I.45, the latter of which David Hilbert proved, for his measure of area; his own note credits Gérard and F. Schur (1892 and 1898) with like theories and refers to an article by O. Stolz (1894). As under I.45, Book Zero proves both for a figure given by its outline (`Figures.division_exists`, `Figures.area_eq`), and `Prop14.outline` draws the square equal to its area. The older companions take the figure with a checked division into triangles, as I.45's do, and make the square equal to those triangles, which is that area too.
- "For let there be constructed the rectangular parallelogram BD equal to the rectilineal figure A" carries Heath's reference [I. 45], but I.45 makes a parallelogram in a given angle, so a right angle is given first, by I.11, for which Heath gives no reference (`Rectangle.of_right` then makes it a rectangle).
- "Let BE be greater": Simson pointed out that the words are not needed, and Heath suggests that Euclid wanted B, G, E, F placed as A, C, D, B are in the figure of II.5 (vol. 1, p. 410). Our proof writes Euclid's case once, and reads the rectangle the other way round when ED is the greater. "Let BF be bisected at G" is I.10, and Heath gives no reference.
- "Let the semicircle BHF be described; let DE be produced to H": our proof draws the whole circle (Post. 3). E lies inside it: G falls between B and E, since BE is the greater, so E lies between the centre G and F, nearer the centre than the circumference (`InsideCircle.of_between_centre`, from Definition I.15); and DE produced beyond E meets the circle (`line_circle_beyond`, System E, Intersections 5). "But GF is equal to GH" is Definition I.15, and Heath gives no reference.
- "But the squares on HE, EG are equal to the square on GH" needs the angle HEG right, which Euclid does not say. The angles DEB, BEH on the straight line DH together make two right angles (I.13), and taking away the rectangle's right angle DEB leaves BEH right (Common Notion 3); HEG is the same angle (`angle_onRay_left`), since G lies between B and E, BE being more than half of BF (`OnRay.between_of_len_lt`).

## The postulates: what the Lean uses and what Heath's references give

Euclid calls on one postulate in Book II, the fifth, in II.10. The certificate counts
everything a proof rests on, the propositions it cites included, so all five are on
every Book II certificate; these are the places where a proof's own steps use one.

- **Postulate 1**: naming a straight line before a point can be on it or off it, as
  in Book I.
- **Postulate 2**: a straight line produced to give I.3 room to cut from
  (`produce_longer`, II.1 and II.10), or behind a point, so that a circle about it is
  cut on the side we want (`OnRay.exists_len_eq`, II.9, II.11 and II.14); FG
  produced in II.10, since our I.32 asks for a side produced, and BE produced in
  II.14, where Heath gives no reference; and, inside `Square.described`, the sides of
  each square produced to make I.28's figure (`BookI.Prop28.interior`), which is how
  II.12 and II.13 come to use it.
- **Postulate 3 and Definition I.15**: circles Euclid does not draw, the two of I.1
  that find a point off a straight line (`exists_off_line`, II.1–II.11) and those
  that give room to cut from (`produce_longer`) or lay a length along a ray
  (`OnRay.exists_len_eq`); and the semicircle of II.14, which Euclid draws, but
  with no reference from Heath for the circle or for its radii.
- **Postulates 4 and 5**: no difference. The Lean uses Postulate 5 directly just
  where Euclid calls on it, in II.10, and Postulate 4 nowhere; every proposition of
  Book II rests on both through the propositions it cites.
