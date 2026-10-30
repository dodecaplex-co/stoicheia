# Further reading

Euclid has been read closely for more than two thousand years, and many of his readers
wrote down what they found. Here are books, papers and a few web pages to read beside the
*Elements*, grouped by theme. Each has a sentence or two on what it offers, and
**Free** marks the ones you can read online at no cost, at the link given. Every title,
date and link was checked against the work itself, its publisher or a library catalogue,
and every work is in [references.bib](references.bib), under the key in its anchor.

The works Stoicheia is built on, Heath's translation and System E above all, are named in
the README, under [Standing on shoulders](../README.md#standing-on-shoulders). A page of
the book may end with a line or three from this list, chosen for its proposition.

[Euclid and his commentators](#euclid-and-his-commentators) ·
[Lincoln and the six books](#lincoln-and-the-six-books) ·
[The foundations of geometry](#the-foundations-of-geometry) ·
[Coordinates, vectors and complex numbers](#coordinates-vectors-and-complex-numbers) ·
[Transformations](#transformations) ·
[Areas and dissections](#areas-and-dissections) ·
[The theorem of Pythagoras](#the-theorem-of-pythagoras) ·
[The golden section](#the-golden-section) ·
[Was Book II algebra?](#was-book-ii-algebra) ·
[The circle, and where Book III leads](#the-circle-and-where-book-iii-leads) ·
[Ruler and compass, and what they cannot do](#ruler-and-compass-and-what-they-cannot-do) ·
[The history of Greek mathematics](#the-history-of-greek-mathematics) ·
[Diagrams and proof](#diagrams-and-proof) ·
[Lean and proof assistants](#lean-and-proof-assistants)

## Euclid and his commentators

Heath's notes, quoted all through the mishnah, gather what readers of the *Elements* have
said of it since antiquity. These carry the conversation on. Robert Simson, Augustus De
Morgan and Isaac Todhunter, whom Heath quotes again and again on Book III, can be read
here in their own words.

- <a id="morrow1970proclus"></a>Proclus, [*A Commentary on the First Book of Euclid's Elements*](https://press.princeton.edu/books/paperback/9780691020907/proclus),
  translated with an introduction and notes by Glenn R. Morrow (Princeton University
  Press, 1970; paperback 1992, with a foreword by Ian Mueller). Heath quotes Proclus on
  nearly every proposition of Book I, from Pappus' proof of I.5 to the story told of
  I.47, and Morrow's careful modern translation lets you read him in full.
- <a id="artmann1999euclid"></a>Benno Artmann, [*Euclid: The Creation of Mathematics*](https://doi.org/10.1007/978-1-4612-1412-0)
  (Springer, 1999). A mathematician's affectionate walk through all thirteen books in
  today's language, with short essays between them on where the ideas came from; its
  chapters on Books I, II and III make a natural next read after ours.
- <a id="mueller1981philosophy"></a>Ian Mueller, [*Philosophy of Mathematics and Deductive Structure in Euclid's Elements*](https://openlibrary.org/books/OL7640284M)
  (MIT Press, 1981; Dover, 2006). Mueller charts, book by book, which propositions each
  proof rests on and what Euclid assumes without saying, the questions our certificate
  answers in Lean. A careful, scholarly book for going deeper.
- <a id="simson1756elements"></a>Robert Simson, [*The Elements of Euclid, viz. the First Six Books, together with the Eleventh and Twelfth*](https://archive.org/details/bim_eighteenth-century_elements-english-sele_euclid_1756_0)
  (Robert and Andrew Foulis, Glasgow, 1756). **Free.** The Glasgow first edition of
  Simson's Euclid, whose notes Heath quotes again and again. In his short notes on Book III
  (pp. 363–368) Simson explains in his own words why III.1 can only be proved indirectly,
  why he added the second case of III.21, and why he restored the cases of III.35.
- <a id="demorgan1849remarks"></a>Augustus De Morgan, ["Short Supplementary Remarks on the First Six Books of Euclid's Elements"](https://archive.org/details/sim_british-almanac-companion_1849),
  in *The Companion to the Almanac; or, Year-Book of General Information for 1849*
  (Charles Knight, 1849), 5–20. **Free.** Sixteen brisk pages of advice to teachers, from
  which Heath draws his reports of De Morgan: the gaps in III.7 and III.8, the "state of
  confusion" of touching circles, and the request that III.26 to III.29 be read as one
  statement and III.35 with III.36 as another.
- <a id="todhunter1872elements"></a>Isaac Todhunter, [*The Elements of Euclid for the Use of Schools and Colleges*](https://archive.org/details/todhuntereuclid00todhrich),
  new edition (Macmillan, 1872; first edition 1862). **Free.** Simson's text revised, with
  notes. The seven short, kindly pages on Book III (pp. 271–277) give in Todhunter's own
  words the remarks Heath passes on to our mishnah, from his reading of touching circles to
  the converse of III.22.
- <a id="dodgson1879euclid"></a>Charles L. Dodgson, [*Euclid and His Modern Rivals*](https://archive.org/details/euclidandhismode000469mbp)
  (Macmillan, 1879; 2nd ed. 1885). **Free.** Lewis Carroll puts the new geometry
  textbooks of his day on trial, in a comic dialogue between Minos and a ghostly German
  professor, and makes a spirited case for keeping Euclid's order of propositions.
- <a id="smith1911teaching"></a>David Eugene Smith, [*The Teaching of Geometry*](https://www.gutenberg.org/ebooks/37681)
  (Ginn, 1911). **Free.** A warm, practical book for teachers, full of history and outdoor
  uses: an engineer finds the centre of a railway curve as in III.1 and III.3, a
  carpenter's square tests a semicircle as in III.31, and III.35 and III.36 become one
  theorem by letting the point wander. Smith's Book II is Euclid's Book III, in the
  American order.
- <a id="wardhaugh2021encounters"></a>Benjamin Wardhaugh, [*Encounters with Euclid: How an Ancient Greek Geometry Text Shaped the World*](https://press.princeton.edu/books/hardcover/9780691211695/encounters-with-euclid)
  (Princeton University Press, 2021; published in Britain in 2020 as *The Book of
  Wonders: The Many Lives of Euclid's Elements*). A charming history of the *Elements*
  told through the people who copied, translated, taught, drew and argued over it: the
  long line of readers Stoicheia joins.
- <a id="casselman_papyrus"></a>Bill Casselman, ["The oldest diagram from Euclid"](https://personal.math.ubc.ca/~cass/Euclid/papyrus/)
  (web page, University of British Columbia). **Free.** A scrap of papyrus from
  Oxyrhynchus, written around AD 100, carries the statement and figure of II.5; this short
  page shows it and tells its story, a reminder of how old and how fragile our text is.

## Lincoln and the six books

We have always found it remarkable that Euclid was a linchpin of Abraham Lincoln's
self-education. By his own account, in the short autobiography of 1860, "He studied and
nearly mastered the Six-books of Euclid, since he was a member of Congress" (Roy P. Basler,
ed., [*The Collected Works of Abraham Lincoln*](lincoln.md#basler1953collected), vol. 4, p. 62). For
readers who share our interest in how the sixteenth president, raised in the backwoods of
Kentucky and Indiana and self-taught on the Illinois prairie, set himself to master Euclid,
[Lincoln and Euclid](lincoln.md) tells the story, with warm thanks to Glenn W. LaFantasie,
through whose article its passages and their sources were found:
["Lincoln, Euclid, and the Satisfaction of Success"](https://quod.lib.umich.edu/j/jala/2629860.0041.104/--lincoln-euclid-and-the-satisfaction-of-success?rgn=main;view=fulltext), *Journal
of the Abraham Lincoln Association* 41, no. 1 (2020): 24–46. **Free.**

## The foundations of geometry

Euclid reads a good deal off his figures without saying so. Our tacit rules, after System
E, name each of those readings; these books tell the longer story of filling the gaps, and
of the parallel postulate.

- <a id="hilbert1902foundations"></a>David Hilbert, [*The Foundations of Geometry*](https://www.gutenberg.org/ebooks/17384),
  translated by E. J. Townsend (Open Court, 1902). **Free.** The short book of 1899 in which
  Hilbert wrote down the axioms Euclid took for granted, among them the axioms of order
  behind "between" (chapter I) and a congruence axiom that gives the remaining angles of
  I.4, from which he proves the bases equal; chapter IV rebuilds the theory of plane areas
  behind I.35–I.41.
- <a id="hartshorne2000geometry"></a>Robin Hartshorne, [*Geometry: Euclid and Beyond*](https://doi.org/10.1007/978-0-387-22676-7)
  (Springer, 2000). Written to be read alongside the *Elements*, it fills Euclid's gaps
  with Hilbert's axioms, says exactly when circles and straight lines must meet, builds a
  theory of area and asks which constructions ruler and compass can do. The mishnah of
  I.1 leans on it.
- <a id="greenberg2008euclidean"></a>Marvin Jay Greenberg, [*Euclidean and Non-Euclidean Geometries: Development and History*](https://store.macmillanlearning.com/us/product/Euclidean-and-Non-Euclidean-Geometries/p/0716799480),
  4th ed. (W. H. Freeman, 2008; first edition 1974). A warm textbook that works through
  betweenness, Pasch's axiom and the crossbar theorem, which our tacit rules supply, then
  tells the long and very human story of the parallel postulate (chapters 3 to 6).
- <a id="bonola1912noneuclidean"></a>Roberto Bonola, [*Non-Euclidean Geometry: A Critical and Historical Study of Its Development*](https://archive.org/details/noneuclideangeom00bonorich),
  translated by H. S. Carslaw, with an introduction by Federigo Enriques (Open Court,
  1912; Dover, 1955). **Free.** The history of the fifth postulate, from the old
  commentators through Saccheri to Bolyai and Lobachevsky, told with evident love; the
  Dover reprint adds George Bruce Halsted's translations of Bolyai and Lobachevsky.
- <a id="vanbrummelen2013heavenly"></a>Glen Van Brummelen, [*Heavenly Mathematics: The Forgotten Art of Spherical Trigonometry*](https://doi.org/10.1515/9781400844807)
  (Princeton University Press, 2013). A charming, hands-on introduction to geometry on a
  sphere, where the angles of a triangle make more than two right angles and I.16 can
  fail; it makes Heath's asides on spherical geometry concrete.

## Coordinates, vectors and complex numbers

A mishnah may end with the modern way: the same fact in coordinates, vectors or complex
numbers, in a sentence or three. These books walk that road at leisure. The turns,
reflections and slides those ways use have [a section of their own](#transformations),
with Yaglom and Klein.

- <a id="descartes1925geometry"></a>René Descartes, [*The Geometry of René Descartes*](https://archive.org/details/geometryofrenede0000davi_t0j4),
  translated by David Eugene Smith and Marcia L. Latham, with a facsimile of the 1637
  original (Open Court, 1925; Dover, 1954). **Free.** The book in which Descartes turns
  ruler-and-compass problems into equations: geometry done by algebra, in his own words.
- <a id="loney1895coordinate"></a>S. L. Loney, [*The Elements of Coordinate Geometry*](https://archive.org/details/elementsofcoordi00lone)
  (Macmillan, 1895). **Free.** A clear Victorian textbook that does with equations what
  Book III does with figures: its chapter on the circle puts the tangent at right angles to
  the radius and gets the rectangle of III.35 and III.36 from the two roots of a quadratic,
  as our modern ways do.
- <a id="stillwell2005four"></a>John Stillwell, [*The Four Pillars of Geometry*](https://doi.org/10.1007/0-387-29052-4)
  (Springer, 2005). One plane seen four ways, through Euclid's straightedge and compass,
  coordinates and vectors, projective geometry and transformations: the road each modern
  way takes in a few lines, here at a comfortable pace.
- <a id="coxeter1969introduction"></a>H. S. M. Coxeter, [*Introduction to Geometry*](https://www.wiley-vch.de/de/fachgebiete/mathematik-und-statistik/introduction-to-geometry-978-0-471-50458-0),
  2nd ed. (Wiley, 1969; Wiley Classics Library, 1989). A much-loved classic by a great
  geometer, with short, lively chapters on the isometries of the plane (chapter 3) and on
  coordinates (chapter 8), and on complex numbers and the golden section if you keep
  reading.
- <a id="sanderson_linalg"></a>Grant Sanderson (3Blue1Brown), [*Essence of linear algebra*](https://www.3blue1brown.com/topics/linear-algebra)
  (video lessons, 2016). **Free.** Short animated lessons that make vectors,
  the dot product and the determinant, which is signed area, as easy to see as one of
  Byrne's coloured figures.
- <a id="steele2004cauchy"></a>J. Michael Steele, [*The Cauchy-Schwarz Master Class: An Introduction to the Art of Mathematical Inequalities*](https://doi.org/10.1017/CBO9780511817106)
  (Cambridge University Press and the Mathematical Association of America, 2004). A
  friendly course in inequalities that starts from the Cauchy–Schwarz inequality, the
  modern reason two sides of a triangle are greater than the third (I.20), with a chapter
  on the AM–GM inequality that II.5 and II.14 draw as a picture.
- <a id="needham2023visual"></a>Tristan Needham, [*Visual Complex Analysis*](https://doi.org/10.1093/oso/9780192868916.001.0001),
  25th anniversary edition, with a foreword by Roger Penrose (Oxford University Press,
  2023; first edition 1997). Complex numbers almost entirely in pictures, where
  multiplying is turning and stretching; chapter 1, "Geometry and Complex Arithmetic",
  reads like a modern companion to Book I, and chapters 3 and 6 go on to inversion and
  non-Euclidean geometry.
- <a id="hahn1994complex"></a>Liang-shin Hahn, [*Complex Numbers and Geometry*](https://doi.org/10.1090/text/052)
  (Mathematical Association of America, 1994; American Mathematical Society, 2019). A
  short, gentle book that assumes nothing about complex numbers, then uses them in its
  chapter "Applications to Geometry" for quick, satisfying proofs of classical theorems of
  the plane.
- <a id="andreescu2014complex"></a>Titu Andreescu and Dorin Andrica, [*Complex Numbers from A to ... Z*](https://doi.org/10.1007/978-0-8176-8415-0),
  2nd ed. (Birkhäuser, 2014; first edition 2005). A cheerful problem book that teaches
  complex numbers from scratch and then turns them on geometry, with a section of tests
  for when points lie on one straight line, meet at right angles or lie on one circle
  (§3.2).
- <a id="nahin1998imaginary"></a>Paul J. Nahin, [*An Imaginary Tale: The Story of √−1*](https://doi.org/10.1515/9781400833894)
  (Princeton University Press, 1998; with a new preface, 2010). How mathematicians went
  from distrusting √−1 to drawing it as a quarter turn, told with real enthusiasm: a good
  bedside companion to the modern ways that use complex numbers.
- <a id="kedlaya2006geometry"></a>Kiran S. Kedlaya, [*Geometry Unbound*](https://kskedlaya.org/geometryunbound/)
  (2006). **Free.** A lively geometry book that sets trigonometry, vectors and complex
  numbers beside classical proofs (chapter 2), with chapters on rigid motions, the power
  of a point and the radical axis, cyclic quadrilaterals and inversion. The free PDF has
  no figures, so keep a pencil near.

## Transformations

Euclid moves one triangle onto another in I.4 and I.8, and one segment of a circle onto
another in III.24. In 1872 Felix Klein proposed that a geometry is known by the transformations
it allows, Euclid's by the rigid motions, and these books start from there.

- <a id="klein1893comparative"></a>Felix Klein, ["A comparative review of recent researches in geometry"](https://arxiv.org/abs/0807.3161),
  translated by M. W. Haskell, *Bulletin of the New York Mathematical Society* 2 (1893),
  215–249. **Free.** The Erlangen Programme of 1872 itself, a short manifesto, and a good
  place to see why superposition is really about symmetry.
- <a id="klein2016elementary"></a>Felix Klein, [*Elementary Mathematics from a Higher Standpoint, Volume II: Geometry*](https://doi.org/10.1007/978-3-662-49445-5),
  translated by Gert Schubring (Springer, 2016); earlier translated by E. R. Hedrick and
  C. A. Noble as *Elementary Mathematics from an Advanced Standpoint: Geometry*
  (Macmillan, 1939; Dover, 2004); the German original of 1909 is
  [free on the Internet Archive](https://archive.org/details/elementarmathema02kleiuoft).
  Klein's lectures of 1908, given for future teachers, look at geometry through its
  transformations. Their survey of Euclid's *Elements* points out that Euclid has no
  axioms of betweenness, the gap our tacit rules fill, and discusses the Archimedean
  axiom by way of horn angles, which come up in III.16.
- <a id="yaglom1962geometric"></a>I. M. Yaglom, [*Geometric Transformations I*](https://doi.org/10.5948/UPO9780883859254),
  translated by Allen Shields (Random House, 1962; now the Mathematical Association of
  America). A slim, playful classic for curious school students: translations,
  half-turns, rotations and reflections, each put to work on clever construction problems,
  beside I.4, I.5, I.15 and I.34.
- <a id="yaglom2009geometric"></a>I. M. Yaglom, [*Geometric Transformations IV: Circular Transformations*](https://doi.org/10.5948/UPO9780883859582),
  translated by Abe Shenitzer (Mathematical Association of America, 2009; now MAA Press
  and the American Mathematical Society). The last volume of the series begun above, which
  introduces reflection in a circle by analogy with reflection in a line. Its chapter 3
  calls the product MA · MB the power of M, d² − r², and finds the radical axis as the line
  where two circles' powers agree.
- <a id="martin1982transformation"></a>George E. Martin, [*Transformation Geometry: An Introduction to Symmetry*](https://doi.org/10.1007/978-1-4612-5680-9)
  (Springer, 1982). A clear, step-by-step book that builds congruence itself out of
  reflections (chapters 4 and 5), the modern sense of Euclid's superposition in I.4 and
  I.8.
- <a id="coxeter1967geometry"></a>H. S. M. Coxeter and S. L. Greitzer, [*Geometry Revisited*](https://bookstore.ams.org/NML/19)
  (Random House, 1967; now MAA Press and the American Mathematical Society). A small
  classic that picks up where Book III leaves off, with chapters on the properties of
  circles (chapter 2), on transformations (chapter 4) and a gentle first look at inversion
  (chapter 5).

## Areas and dissections

From I.35 on, Euclid calls figures equal that have different shapes, because they are
equal in area. Cutting one into pieces that rebuild the other makes that equality
something you can see.

- <a id="frederickson1997dissections"></a>Greg N. Frederickson, [*Dissections: Plane & Fancy*](https://www.cs.purdue.edu/homes/gnf/book.html)
  (Cambridge University Press, 1997). A richly illustrated book of dissections: one figure
  cut into pieces that rebuild another, Euclid's "equal" made visible.
- <a id="boltyanskii1963equivalent"></a>V. G. Boltyanskii, [*Equivalent and Equidecomposable Figures*](https://store.doverpublications.com/collections/math-algebra/products/9780486170053),
  translated by Alfred K. Henn and Charles E. Watts (D. C. Heath, 1963; Dover, 2007, in
  one volume with *Hyperbolic Functions* and *Configuration Theorems*). A slim, gentle
  book, for readers with only school geometry, on when two figures of equal area or volume
  can be cut into matching pieces.
- <a id="aigner2018proofs"></a>Martin Aigner and Günter M. Ziegler, [*Proofs from THE BOOK*](https://link.springer.com/book/10.1007/978-3-662-57265-8),
  6th ed. (Springer, 2018). Its short chapter "Hilbert's third problem:
  decomposing polyhedra" shows why cutting and rearranging always works for polygons of
  equal area and fails for solids.
- <a id="braden1986surveyor"></a>Bart Braden, ["The Surveyor's Area Formula"](https://web.archive.org/web/20140629065751/https://www.maa.org/sites/default/files/pdf/pubs/Calc_Articles/ma063.pdf),
  *The College Mathematics Journal* 17 (1986), 326–337. **Free.** A friendly article on
  the "shoelace" formula, which takes the corners of a field and hands back its area: what
  I.35–I.45 do with parallelograms and triangles, done with coordinates.

## The theorem of Pythagoras

I.47 has been proved in hundreds of ways, and was known in some form long before Euclid.

- <a id="maor2007pythagorean"></a>Eli Maor, [*The Pythagorean Theorem: A 4,000-Year History*](https://press.princeton.edu/books/paperback/9780691196886/the-pythagorean-theorem)
  (Princeton University Press, 2007; paperback 2019). A warm, wide-ranging life of I.47,
  from Babylonian clay tablets to Einstein, with a chapter on Euclid's own proof and
  another on the hundreds of other ways people have proved it.
- <a id="robson2002words"></a>Eleanor Robson, ["Words and Pictures: New Light on Plimpton 322"](https://doi.org/10.1080/00029890.2002.11919845),
  *The American Mathematical Monthly* 109 (2002), 105–120. The famous Babylonian tablet
  of "Pythagorean triples", read carefully by a historian who shows what its scribe was
  probably doing.
- <a id="loomis1968pythagorean"></a>Elisha Scott Loomis, [*The Pythagorean Proposition*](https://files.eric.ed.gov/fulltext/ED037335.pdf),
  2nd ed. (1940; reissued by the National Council of Teachers of Mathematics, 1968).
  **Free.** A delightfully obsessive collection of 370 proofs; dip in anywhere and set
  them beside Euclid's in I.47.
- <a id="bogomolny_pythagoras"></a>Alexander Bogomolny, ["Pythagorean Theorem and its many proofs"](https://www.cut-the-knot.org/pythagoras/),
  *Cut the Knot* (web page). **Free.** Over a hundred proofs on one page, starting with
  Euclid's own, many of them dissections you can check by eye.

## The golden section

II.11 cuts a straight line so that the rectangle contained by the whole and one segment
is equal to the square on the other, which Euclid later calls cutting in extreme and mean
ratio. A good deal of folklore has grown up around it.

- <a id="herzfischler1998golden"></a>Roger Herz-Fischler, [*A Mathematical History of the Golden Number*](https://openlibrary.org/books/OL703522M)
  (Dover, 1998; first published in 1987 as *A Mathematical History of Division in Extreme
  and Mean Ratio*). A careful history that starts from Euclid's own text rather than from
  legends about pyramids and paintings.
- <a id="markowsky1992misconceptions"></a>George Markowsky, ["Misconceptions about the Golden Ratio"](https://www.jstor.org/stable/2686193),
  *The College Mathematics Journal* 23 (1992), 2–19. A short, cheerful look at the
  golden-ratio folklore, so that you can enjoy the mathematics of II.11 without the myths.

## Was Book II algebra?

Book II is often read as algebra in geometric dress, II.4 as (a + b)² = a² + b² + 2ab. In
1975 Sabetai Unguru asked whether that reading is Euclid's or ours, and the argument has
gone on ever since. Our modern ways write the algebra; these let you hear both sides, and
Jens Høyrup's survey below is a gentle way in.

- <a id="unguru1975need"></a>Sabetai Unguru, ["On the Need to Rewrite the History of Greek Mathematics"](https://doi.org/10.1007/BF00327233),
  *Archive for History of Exact Sciences* 15 (1975), 67–114. The paper that started the
  quarrel, asking whether Book II is really algebra in disguise or whether we only read
  it that way; spirited and a little fierce.
- <a id="vanderwaerden1976defence"></a>B. L. van der Waerden, ["Defence of a 'Shocking' Point of View"](https://doi.org/10.1007/BF00412256),
  *Archive for History of Exact Sciences* 15 (1976), 199–210. Van der Waerden's
  spirited reply, defending the idea that the Greeks did algebra in geometric form.
- <a id="freudenthal1977algebra"></a>Hans Freudenthal, ["What Is Algebra and What Has It Been in History?"](https://doi.org/10.1007/BF00328154),
  *Archive for History of Exact Sciences* 16 (1977), 189–200. A mathematician's
  thoughtful answer to the question under the whole debate: what would count as algebra
  at all?
- <a id="weil1978betrayed"></a>André Weil, ["Who Betrayed Euclid?"](https://doi.org/10.1007/BF00328609),
  *Archive for History of Exact Sciences* 19 (1978), 91–93. Three sharp pages from a
  great mathematician, arguing that to write the history of mathematics you must
  understand the mathematics.
- <a id="christianidis2004classics"></a>Jean Christianidis (ed.), [*Classics in the History of Greek Mathematics*](https://doi.org/10.1007/978-1-4020-2640-9)
  (Kluwer, 2004). The quarrel in one volume: Unguru's paper, van der Waerden's reply,
  Weil's letter and Unguru's later reflections side by side, each part with an
  introduction that sets the scene.
- <a id="fowler1999mathematics"></a>David Fowler, [*The Mathematics of Plato's Academy: A New Reconstruction*](https://academic.oup.com/book/52809),
  2nd ed. (Clarendon Press, 1999; first edition 1987). A bold book
  that reads Book II without algebra, as being about squares and rectangles (chapter 3,
  "Elements II: The Dimension of Squares"), and links it to the "take the smaller from the
  larger" process behind continued fractions.
- <a id="blasjo2016defence"></a>Viktor Blåsjö, ["In Defence of Geometrical Algebra"](https://doi.org/10.1007/s00407-015-0169-5),
  *Archive for History of Exact Sciences* 70 (2016), 325–359. **Free** in the
  [Utrecht University Repository](https://hdl.handle.net/1874/339381). A lively modern
  case for the algebraic reading, with a fair map of the arguments; read it with Unguru or
  Fowler for the other side.
- <a id="hoyrup2017geometric"></a>Jens Høyrup, ["What is 'geometric algebra', and what has it been in historiography?"](https://doi.org/10.3934/Math.2017.1.128),
  *AIMS Mathematics* 2 (2017), 128–160. **Free.** A guided tour of fifty years of
  argument, which sorts out what each side meant by "geometric algebra".
- <a id="hoyrup2017algebra"></a>Jens Høyrup, [*Algebra in Cuneiform: Introduction to an Old Babylonian Geometrical Technique*](https://www.mprl-series.mpg.de/textbooks/2/)
  (Edition Open Access, 2017). **Free.** A readable introduction to the Babylonian
  "cut-and-paste" way with squares and rectangles, the same moves you see in II.5, II.6
  and II.14; chapter 8, "Origin and Heritage", asks where the technique came from and
  where it went.

## The circle, and where Book III leads

Book III is Euclid's book of the circle: chords and tangents, touching circles, the angles
in a segment, and the rectangles of III.35 and III.36. Geometers went on from there to the
power of a point, the radical axis, coaxal circles and inversion. These books follow them,
from school geometry to a university course.

- <a id="casey1886sequel"></a>John Casey, [*A Sequel to the First Six Books of the Elements of Euclid, Containing an Easy Introduction to Modern Geometry, with Numerous Examples*](https://archive.org/details/sequeltofirstsix00caserich),
  4th ed. (Hodges, Figgis, & Co., Dublin, 1886; first edition 1881). **Free.** Written in
  Dublin for students who had finished Euclid, by the author whose *First Six Books* the
  README thanks. Its supplement to Book III adds the propositions Euclid left out, from
  equal tangents and touching circles to the radical axis, proved in Euclid's manner and
  citing his propositions by number.
- <a id="coolidge1916treatise"></a>Julian Lowell Coolidge, [*A Treatise on the Circle and the Sphere*](https://archive.org/details/cu31924001508955)
  (Clarendon Press, 1916; Chelsea, 1971). **Free.** A great old treatise wholly about the
  circle and the sphere. Its first chapter gives the power of a point a sign, just as
  III.35's modern way does, and finds the radical axis of III.10 from it; its preface
  remarks that had Euclid taken Lobachevsky's or Riemann's assumption in place of his
  parallel postulate, he could not have proved that the angles in one segment are equal.
  Scholarly, but rewarding to dip into.
- <a id="johnson1929modern"></a>Roger A. Johnson, [*Modern Geometry: An Elementary Treatise on the Geometry of the Triangle and the Circle*](https://archive.org/details/bwb_P9-AFM-481)
  (Houghton Mifflin, 1929; Dover, 1960 and 2007, as *Advanced Euclidean Geometry*).
  **Free.** A classic that begins where Euclid's circles leave off: its third chapter joins
  III.35 and III.36 into one theorem, defines the power of a point as OP² − r², the very
  form of our modern way, and builds the radical axis, coaxal circles and inversion on it.
- <a id="ogilvy1969excursions"></a>C. Stanley Ogilvy, [*Excursions in Geometry*](https://store.doverpublications.com/products/9780486265308)
  (Oxford University Press, 1969; Dover, 1990). A pleasantly written little book for
  readers who liked school geometry and wanted more. It states III.35 and III.36 as one
  "basic theorem", then goes on to orthogonal circles, the radical axis, inversion,
  Peaucellier's linkage and Steiner's chains of touching circles.
- <a id="pedoe1995circles"></a>Dan Pedoe, [*Circles: A Mathematical View*](https://doi.org/10.1090/spec/012),
  revised edition (Mathematical Association of America, 1995; first published 1957; now
  MAA Press and the American Mathematical Society). A small, concise book given wholly to
  the circle. Its gentle Chapter 0, new in this edition, retells the circle theorems of
  Book III with only paper, pencil, compass and ruler; then the book turns, more
  demandingly, to inversion, coaxal circles and the cross-ratio of four points on a circle.
- <a id="hadamard2008lessons"></a>Jacques Hadamard, [*Lessons in Geometry, I: Plane Geometry*](https://doi.org/10.1090/mbk/057),
  translated by Mark Saul from the 13th French edition of 1947 (American Mathematical
  Society and Education Development Center, 2008; first edition 1898). Hadamard's school
  geometry, revised by him twelve times and now in English. Its book on the circle walks
  much of Book III's road, from chords and tangents and two circles meeting to the
  inscribed angle, and its book on similarity reaches the power of a point and the radical
  axis.
- <a id="davis2011inversion"></a>Tom Davis, ["Inversion in a Circle"](http://www.geometer.org/mathcircles/inversion.pdf)
  (handout, 2011). **Free.** One of the friendly handouts Tom Davis wrote for math circles
  for high-school students, showing inversion in a circle at work, mostly in pictures
  rather than proofs: the inverse of a point found with a straight line touching the
  circle, as in III.17, touching circles turned into parallel lines, and the radical axis
  put to use in proving Steiner's porism.
- <a id="brannan2012geometry"></a>David A. Brannan, Matthew F. Esplen and Jeremy J. Gray, [*Geometry*](https://doi.org/10.1017/CBO9781139003001),
  2nd ed. (Cambridge University Press, 2012; first edition 1999). For a reader ready for a
  university course, a generous Open University textbook that follows Klein in studying
  each geometry through its transformations. Its chapter 5, "Inversive Geometry", treats
  circles and lines together, inverts touching circles, and gathers circles with a common
  radical axis into coaxal families.
- <a id="chen2016euclidean"></a>Evan Chen, [*Euclidean Geometry in Mathematical Olympiads*](https://doi.org/10.5948/9781614444114)
  (Mathematical Association of America, 2016; now the American Mathematical Society).
  Written for students preparing for olympiads, and more demanding than most books here,
  but its first two chapters are a lively modern course in Book III's ideas: angles in
  circles, cyclic quadrilaterals, tangents, the power of a point and the radical axis.
- <a id="alsina2020cornucopia"></a>Claudi Alsina and Roger B. Nelsen, [*A Cornucopia of Quadrilaterals*](https://doi.org/10.1090/dol/055)
  (MAA Press and the American Mathematical Society, 2020). A generous, picture-filled book
  about four-sided figures, many of its results proved without words, in the spirit of
  Nelsen's [*Proofs Without Words*](#nelsen1993proofs). Its chapter "Quadrilaterals and
  their circles" takes the quadrilateral in a circle of III.22 on to Ptolemy's theorem and
  Brahmagupta's formula for its area.

## Ruler and compass, and what they cannot do

With nothing but ruler and compass, Euclid bisects any angle in I.9 and constructs a
square equal to any rectilineal figure in II.14. Trisecting an angle, doubling a cube and
squaring a circle cannot be done that way, and proving so took until the nineteenth
century. Robin Hartshorne's chapter "Construction Problems and Field Extensions" (under
[the foundations](#hartshorne2000geometry)) tells it with care.

- <a id="klein1897famous"></a>Felix Klein, [*Famous Problems of Elementary Geometry*](https://archive.org/details/famousproblemsof00kleiiala),
  translated by Wooster Woodruff Beman and David Eugene Smith (Ginn, 1897; 2nd ed., with
  notes by R. C. Archibald, 1930; Dover, 1956). **Free.** In about eighty friendly pages
  Klein shows why no ruler and compass can trisect an angle, double the cube or square the
  circle, gives Gauss's construction of the regular 17-gon, a sequel to the pentagon and
  fifteen-angled figure of Book IV, and proves that e and π are transcendental.
- <a id="courant1996what"></a>Richard Courant and Herbert Robbins, [*What Is Mathematics? An Elementary Approach to Ideas and Methods*](https://openlibrary.org/books/OL815900M),
  2nd ed., revised by Ian Stewart (Oxford University Press, 1996; first edition 1941). A
  much-loved classic whose chapter III, "Geometrical Constructions. The Algebra of Number
  Fields", shows which lengths ruler and compass can reach (square roots, and nothing
  more): so the √3 of I.1 and the √5 of II.11 can be drawn, and an angle in general cannot
  be trisected.
- <a id="richeson2019tales"></a>David S. Richeson, [*Tales of Impossibility: The 2000-Year Quest to Solve the Mathematical Problems of Antiquity*](https://doi.org/10.1515/9780691194233)
  (Princeton University Press, 2019). A friendly tour of the four famous problems
  (squaring the circle, trisecting the angle, doubling the cube and drawing regular
  polygons), full of history and short "tangents", up to Pierre Wantzel's proofs of 1837.
- <a id="knorr1986ancient"></a>Wilbur Richard Knorr, [*The Ancient Tradition of Geometric Problems*](https://openlibrary.org/books/OL1736639M)
  (Birkhäuser, 1986; Dover, 1993). The ancient story of how Greek geometers attacked the
  problems ruler and compass could not solve, with the conchoid, the quadratrix and the
  spiral that the mishnah of I.9 names; scholarly but readable.

## The history of Greek mathematics

The *Elements* gathers the work of Euclid's predecessors, and trigonometry grew out of its
circles. These histories set Euclid among the mathematicians before and after him.

- <a id="heath1921history"></a>Thomas L. Heath, [*A History of Greek Mathematics*](https://archive.org/details/cu31924008704219),
  2 vols. (Clarendon Press, 1921; Dover, 1981): vol. I, *From Thales to Euclid*, at the
  link, and [vol. II](https://archive.org/details/cu31924008704227), *From Aristarchus to
  Diophantus*. **Free.** Heath's own history, for when a mishnah points past the
  *Elements* to Pythagoras, Hippocrates or Eudoxus, or to Heron, Pappus, Theon and Proclus.
- <a id="thomas1939selections"></a>Ivor Thomas (translator), [*Selections Illustrating the History of Greek Mathematics*](https://www.hup.harvard.edu/books/9780674993693),
  2 vols., Loeb Classical Library 335 and 362 (Heinemann and Harvard University Press, 1939
  and 1941): vol. I, *From Thales to Euclid*, at the link, and
  [vol. II](https://www.hup.harvard.edu/books/9780674993990), *From Aristarchus to
  Pappus*; Harvard sells them today as *Greek Mathematical Works*. The ancient witnesses
  themselves, Greek and English on facing pages with patient notes: Eudemus' account of
  Hippocrates' lunes, which judges a segment greater or less than a semicircle by the angle
  in it, and Ptolemy proving his theorem on the quadrilateral in a circle with III.21.
- <a id="mactutor_hippocrates"></a>J. J. O'Connor and E. F. Robertson, ["Hippocrates of Chios"](https://mathshistory.st-andrews.ac.uk/Biographies/Hippocrates/),
  *MacTutor History of Mathematics Archive* (web page, University of St Andrews).
  **Free.** A short, clear page on the first geometer known to have written *Elements*,
  which quotes Eudemus' old account of his lunes and draws the first one, the lune on a
  right-angled isosceles triangle in a semicircle, for you to follow.
- <a id="aaboe1964episodes"></a>Asger Aaboe, [*Episodes from the Early History of Mathematics*](https://doi.org/10.5948/UPO9780883859285)
  (Random House, 1964; now MAA Press and the American Mathematical Society). A slim
  classic of the New Mathematical Library whose last chapter follows Ptolemy as he builds
  his table of chords and puts it to use: the straight lines in a circle of III.15, III.28
  and III.29, set out arc by arc.
- <a id="dunham1990journey"></a>William Dunham, [*Journey through Genius: The Great Theorems of Mathematics*](https://www.wiley.com/en-us/Journey+through+Genius%3A+The+Great+Theorems+of+Mathematics-p-9780471500308)
  (Wiley, 1990; Penguin, 1991). Great theorems told with their history. The warm,
  story-filled opening chapter meets Thales, proves the right angle in a semicircle by an
  argument taken from III.31, and follows Hippocrates of Chios as he squares a lune with
  it.
- <a id="ostermann2012geometry"></a>Alexander Ostermann and Gerhard Wanner, [*Geometry by Its History*](https://doi.org/10.1007/978-3-642-29163-0)
  (Springer, 2012). Geometry learned from the old masters, roughly in the order it was
  found, with a section on Book III that sets III.20, III.22, III.31, III.35 and III.36 side
  by side and carries them on to the power of a point; its chapter on trigonometry then
  begins from Ptolemy's chords.
- <a id="koshkin2020bisecting"></a>Sergiy Koshkin, ["Bisecting Horn Angles"](https://arxiv.org/abs/2206.09499),
  *The College Mathematics Journal* 51 (2020), 124–131, DOI 10.1080/07468342.2020.1700745;
  the link is the author's preprint on arXiv. **Free.** A short paper that opens with a
  page of history on the horn-like angle of III.16, from Proclus, who wondered whether it
  could be bisected, to Edward Kasner, and then bisects it by means the Greeks had; its
  later sections lean on conics and complex analysis.
- <a id="katz2009history"></a>Victor J. Katz, [*A History of Mathematics: An Introduction*](https://openlibrary.org/books/OL22656816M),
  3rd ed. (Addison-Wesley, 2009). A clear, wide-ranging textbook history that sets Euclid
  beside the mathematics of Egypt, Mesopotamia, China, India and the Islamic world.
- <a id="stillwell2010mathematics"></a>John Stillwell, [*Mathematics and Its History*](https://doi.org/10.1007/978-1-4419-6053-5),
  3rd ed. (Springer, 2010). A friendly grand tour whose first chapters, "The Theorem of
  Pythagoras", "Greek Geometry" and "Greek Number Theory", sit right beside Books I and II.
- <a id="knorr1975evolution"></a>Wilbur Richard Knorr, [*The Evolution of the Euclidean Elements*](https://doi.org/10.1007/978-94-010-1754-1)
  (D. Reidel, 1975). A scholarly detective story about how the *Elements* grew out of
  earlier work on incommensurable magnitudes; heavy going, but the place to start on how
  the book was put together.
- <a id="vanbrummelen2009mathematics"></a>Glen Van Brummelen, [*The Mathematics of the Heavens and the Earth: The Early History of Trigonometry*](https://press.princeton.edu/books/hardcover/9780691129730/the-mathematics-of-the-heavens-and-the-earth)
  (Princeton University Press, 2009). A full history of early trigonometry, where you can
  watch Greek astronomers turn the straight lines in a circle into tables they could
  compute with.
- <a id="toomer1984almagest"></a>G. J. Toomer (translator), [*Ptolemy's Almagest*](https://press.princeton.edu/isbn/9780691002606)
  (Duckworth and Springer, 1984; Princeton University Press, 1998). For the curious,
  Ptolemy's own table of chords, built from the geometry of the circle, in a careful
  modern translation.
- <a id="maor1998trigonometric"></a>Eli Maor, [*Trigonometric Delights*](https://press.princeton.edu/books/paperback/9780691202198/trigonometric-delights)
  (Princeton University Press, 1998; paperback 2013 and 2020). A warm, story-filled
  history of trigonometry, from Greek chords (chapter 2) to two theorems of geometry
  (chapter 6) and imaginary angles (chapter 14).

## Diagrams and proof

Euclid proves with a figure in front of him. When may a proof trust the picture? Our tacit
rules, after System E, give one answer; these look at the question from other sides.

- <a id="manders2008euclidean"></a>Kenneth Manders, ["The Euclidean Diagram (1995)"](https://doi.org/10.1093/acprof:oso/9780199296453.003.0005),
  in Paolo Mancosu (ed.), *The Philosophy of Mathematical Practice* (Oxford University
  Press, 2008), 80–133. The essay that sorts what Euclid's figures may be trusted for,
  such as which point lies within which region, from what they never show, such as that
  two lengths are equal; System E, and so our tacit rules, is built on that distinction.
- <a id="miller2007euclid"></a>Nathaniel Miller, [*Euclid and His Twentieth Century Rivals: Diagrams in the Logic of Euclidean Geometry*](https://web.stanford.edu/group/cslipublications/cslipublications/site/9781575865072.shtml)
  (CSLI Publications, 2007). A short book that treats Euclid's diagrams as a real part of
  the proof and builds a formal system around them, complete with a computer proof
  checker; chapter 1 opens with a short history of diagrams, logic and geometry.
- <a id="nelsen1993proofs"></a>Roger B. Nelsen, [*Proofs Without Words: Exercises in Visual Thinking*](https://doi.org/10.1090/clrm/001)
  (Mathematical Association of America, 1993; a second volume, 2000). Page after page of
  pictures that prove at a glance, (a + b)² and the AM–GM inequality among them: a
  natural companion to Book II, read the algebraic way.
- <a id="rougeux2018byrne"></a>Nicholas Rougeux, [*Byrne's Euclid*](https://www.c82.net/euclid/)
  (2018). **Free.** Oliver Byrne's Euclid of 1847, in red, yellow and blue,
  rebuilt for the web: click a coloured shape and watch it light up in the proof. Our "at
  a glance" figures take their palette from Byrne.
- <a id="oechslin2010byrne"></a>Oliver Byrne, [*The First Six Books of the Elements of Euclid*](https://www.taschen.com/en/books/classics/47706/oliver-byrne-the-first-six-books-of-the-elements-of-euclid),
  facsimile of the 1847 edition, edited by Werner Oechslin (Taschen, 2010; new edition
  2022). A printed facsimile of Byrne's coloured pages, with Oechslin's essay on why the
  book looks the way it does: a companion to have on the table while reading our figures.

## Lean and proof assistants

Every proof here is checked by Lean. If a page makes you want to write one yourself, these
are friendly ways in, followed by a few glimpses of what machines have done with geometry.

- <a id="leanLearn"></a>The Lean community, ["Learning Lean 4"](https://leanprover-community.github.io/learn.html).
  **Free.** One signpost page listing the games, books and courses the community
  recommends, sorted by how much background you have.
- <a id="buzzard_nng4"></a>Kevin Buzzard and Jon Eugster, [*Natural Number Game*](https://adam.math.hhu.de/#/g/leanprover-community/nng4)
  (Lean 4 version; the original by Kevin Buzzard and Mohammad Pedramfar). **Free.** A game
  in the browser in which you build addition and multiplication from scratch and prove
  that 2 + 2 = 4 and much more, one small step at a time, with nothing to install.
- <a id="leanMechanicsOfProof"></a>Heather Macbeth, [*The Mechanics of Proof*](https://hrmacbeth.github.io/math2001/)
  (Fordham University, 2022–2024). **Free.** A gentle first course in writing proofs with
  Lean, for readers new both to proofs and to Lean.
- <a id="velleman2019prove"></a>Daniel J. Velleman, [*How to Prove It: A Structured Approach*](https://doi.org/10.1017/9781108539890),
  3rd ed. (Cambridge University Press, 2019). A patient introduction to the logic under
  every proof, Euclid's included; chapter 3 covers proof by contradiction, as in I.6, I.19
  and I.25, and proof by cases.
- <a id="velleman_htpiwl"></a>Daniel J. Velleman, [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/).
  **Free.** A companion to the book above that tries each proof technique out in Lean:
  proof by contradiction, for instance, is the `by_contra` tactic.
- <a id="avigad_tpil4"></a>Jeremy Avigad, Leonardo de Moura, Soonho Kong and Sebastian Ullrich, with contributions from the Lean community,
  [*Theorem Proving in Lean 4*](https://lean-lang.org/theorem_proving_in_lean4/). **Free.**
  The official guide to how Lean itself thinks, from propositions as types (chapter 3) to
  the axioms its kernel accepts (chapter 12, "Axioms and Computation"): what it means
  when we say Lean checks every proof here.
- <a id="avigad_massot_mil"></a>Jeremy Avigad and Patrick Massot, [*Mathematics in Lean*](https://leanprover-community.github.io/mathematics_in_lean/).
  **Free.** A hands-on introduction to doing everyday mathematics in Lean 4 with its
  library Mathlib, written for mathematicians, to read with Lean open beside it. (Stoicheia
  itself uses plain Lean, with no Mathlib.)
- <a id="wiedijk_100"></a>Freek Wiedijk, ["Formalizing 100 Theorems"](https://www.cs.ru.nl/~freek/100/)
  (Radboud University Nijmegen). **Free.** A running scoreboard of which famous theorems
  have been checked by which proof assistants, among them the theorem of Pythagoras
  (no. 4) and the sum of the angles of a triangle (no. 27), our I.47 and I.32.
- <a id="gelernter1959realization"></a>Herbert Gelernter, ["Realization of a Geometry-Theorem Proving Machine"](https://purl.stanford.edu/mb725bt3951)
  (Paris, 1959; reprinted in Edward A. Feigenbaum and Julian Feldman (eds.), *Computers
  and Thought*, McGraw-Hill, 1963). **Free**: the link is a scan of the whole of
  *Computers and Thought*. An early AI program, and it did Euclid; the popular story that
  it found Pappus' proof of I.5 for itself is mostly legend, for Marvin Minsky found that
  proof by hand while imagining what such a machine might do.
- <a id="chou1994machine"></a>Shang-Ching Chou, Xiao-Shan Gao and Jing-Zhong Zhang, [*Machine Proofs in Geometry: Automated Production of Readable Proofs for Geometry Theorems*](https://doi.org/10.1142/2196)
  (World Scientific, 1994). How a computer can write short, readable geometry proofs by
  keeping track of the areas of triangles, a method with a strong family likeness to
  Euclid's own arguments in I.35–I.41.

---

Suggestions are welcome. A new entry needs a checked citation and link, and goes into
[references.bib](references.bib) too.
