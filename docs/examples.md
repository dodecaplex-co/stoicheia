# Reviewed examples

Five examples to learn from, each chosen for a reason and tied to the commit at which it
was read. They show the standards of [STYLE.md](STYLE.md) and
[FORMALIZATION.md](FORMALIZATION.md) at work. They guide judgment; they are not templates.
Copying their leads, their rhythm or their sentences onto another page would make the drift
the voice passes were run to remove. Take from them how a decision was made, and make your
own for your proposition.

The first four were read again at commit `6b3c462`, after the voice and records passes of
brief 0005. I.1, I.7 and II.4 have revised commentary and records at the `full` stage; III.31
now uses III.2's helpers for its circle facts, with its record read again. When one of them
changes, it is read again and its commit here brought up to date, or it is replaced.

## A short construction: I.1

[Page](../book/I/01.md) · [Lean](../Elements/BookI/Prop01.lean) ·
[mishnah](../mishnah/I/01.md) · [figure](../figures/I/01.svg)

**Why this one.** The first proposition, a short construction whose circles, helper and
side choice can be read together.

- **The statement says a little more than Euclid's, and says so.** The triangle may be put
  on the side of a given point P when P is off AB, because I.9 and I.11 need a particular
  side. The file's header gives the reason, and the decision is recorded
  ([0002-decisions.md](briefs/0002-decisions.md), 15 October).
- **A helper supplies one named step.** `Prop1.figure` proves that C is off AB, so that ABC
  is a triangle: a fact Euclid reads off the figure. Its docstring says so; it does not hide
  the construction, which stays in the main proof under Heath's sentences.
- **The gap is a named rule, credited.** The circles' meeting is System E's Intersection 5
  (`circles_meet`), and the remark above it says why the circles cross and why the side can
  be chosen. The remark also says plainly that the straight lines CA, CB are drawn for the
  eye: our proof uses only the point C.
- **The mishnah does all four things in four paragraphs:** the move (must the circles
  meet?), the history (Zeno's worries, reported by Heath, with the chain of report clear),
  the formal decision (C off AB, and the side), and a modern way that earns its place: the
  √3 of the complex point is why the rational plane fails I.1, with Robin Hartshorne's book
  credited warmly.

**Do not copy.** "Lean wants it said" is allowed on I.1, I.5 and I.22 alone (STYLE,
section 3). The first three leads are questions; the last is **The modern way.** The
questions suit the first page; a run of pages that all open on questions is a rhythm, not
a voice.

## A hard diagram argument: I.7

[Page](../book/I/07.md) · [Lean](../Elements/BookI/Prop07.lean) ·
[mishnah](../mishnah/I/07.md) · [figure](../figures/I/07.svg)

**Why this one.** Euclid draws one figure and leaves the rest to the reader; Lean has no
reader to leave them to. I.7 shows how to make every case explicit without losing Euclid's
argument.

- **Each helper settles one thing the figure shows.** `Prop7.triangle` (ACD is a triangle),
  `Prop7.cross` (when BC separates D from A, AD meets BC within CB or beyond C),
  `Prop7.cases` (where D can fall), `Prop7.figure` (in Euclid's figure, CB falls within the
  angle ACD and DA within the angle CDB), and `Prop7.within` (the case Euclid leaves out,
  answered as Proclus answers it, by the second part of I.5). Each docstring says which step
  it supplies.
- **The cases are labelled where they are taken.** A remark in the main proof names all
  four figures, exchanges C and D for the one that is Euclid's figure lettered the other
  way, sends the Proclus case to its helper, and then follows Euclid's reductio sentence by
  sentence.
- **A missing step is told in Heath's words.** Where Heath says "It would be natural to
  insert here the step …", the remark quotes him and says what the figure supplies.
- **The mishnah** keeps the formal story to its fourth paragraph (**Four places for D.**):
  it names `Prop7.cases`, explains why there is no fifth place, and says why Euclid could
  leave the other figures to his reader. The first three paragraphs have no bold leads;
  they give Heath's reading of the enunciation, Charles Dodgson's hinged rods and Proclus's
  answer to the missing case. The fifth, the modern way, shows the two mirror-image
  answers, one on each side, which is the proposition's point.

III.8 is a second example of the kind: its helpers are De Morgan's two assumptions, named as
his. Its last step uses the convex and concave orders also when the more remote point lies
on the other circumference or at a point of contact; `Prop8.contact_last` shows that a point
of contact cannot be the nearer, and the mishnah says so.

## An area proof: II.4

[Page](../book/II/04.md) · [Lean](../Elements/BookII/Prop04.lean) ·
[mishnah](../mishnah/II/04.md) · [figure](../figures/II/04.svg)

**Why this one.** Book II speaks of rectangles and squares that need not be drawn, and
proves its equalities with figures that are. II.4 shows the representation (`rect`, `sq`)
meeting the drawn figure, and a shared step told on its home page.

- **The statement is Euclid's, in areas:** the square on AB equals the squares on AC, CB
  with twice the rectangle AC, CB. Twice the rectangle is the area added to itself; the
  numerical and vector comparisons belong to the modern way.
- **The figure is drawn as Euclid draws it,** by shared steps with recognisable names: the
  square by I.46 and `Square.described`, its side chosen by `exists_off_line`, and the
  parallels and the point G by `Parallelogram.figure`. Each drawn piece is then named as a
  rectangle or square of Euclid's words by the bridge lemmas of Book II's ground.
- **Euclid's proof is followed in full,** down to every right angle of CGKB, and the mishnah
  names the subtraction of a right angle as Common Notion 3. It also identifies I.43 behind
  the equality of the complements, where Heath gives no reference.
- **"For the same reason"** is Euclid's own, and the general fact behind it, the porism
  Heath calls interpolated, is proved once as `Square.about_diameter` and used again in
  II.5–II.8. II.4's second mishnah paragraph tells it alongside the proof for CGKB; the
  later mishnahs leave that history here. Its first paragraph links Book II's introduction
  for the account of how the areas correspond to the pieces drawn.

## A page completed by companions: III.31

[Page](../book/III/31.md) · [Lean](../Elements/BookIII/Prop31.lean) ·
[mishnah](../mishnah/III/31.md) · [figure](../figures/III/31.svg)

Read again against the Lean, record and page at commit `560da15a2`, on 25 October 2026.

**Why this one.** The main theorem and its companions cover the whole enunciation. III.31
shows how to account for clauses proved after the main theorem, state the limits of a
representation, and extend Euclid's worked case where a later citer needs it.

- **The completion.** The angles "of the greater segment" and "of the less segment" are
  contained by a straight line and a circumference. The main theorem proves the
  rectilineal claims; `Prop31.greater` and `Prop31.less`, after it, prove the mixed-angle
  comparisons for every straight line in the circle not through the centre, at either
  end. The companions use the right angle BAC, and the less-segment proof obtains the
  adjacent right angle CAF. The note beside Heath's closing sentences points to the
  companions and says that the final `exact` returns only the main theorem's claims.
- **The widening.** Euclid proves the angle in the greater segment less than a right angle
  at B, but IV.5 needs it at any point. The statement says it of every point of the segment,
  the Lean reaches the other points through III.22, and the mishnah's fourth paragraph says
  why.
- **The representation still has limits.** The tag `mixed-angles-local` names a comparison
  of regions near the vertex: near A the right angle BAC lies within the greater segment
  with room to spare, and the less segment lies within the right angle CAF. The companions
  also prove that the named points give well-formed mixed angles. No addition, ratio or
  motion of mixed angles is claimed. The page's Representation row and the mishnah explain
  this meaning beside the claim of full coverage.
- **The record, and what the page makes of it.** The review record,
  [review/III/31.toml](../review/III/31.toml), declares the statement's scope `full`,
  lists both companions and keeps the route `euclid`, its note giving the further step
  through III.22. Of its nine passages, four are `helper` passages, naming
  `Prop2.triangle`, `Definition15` twice and `angle_add_of_between`; one, a `case`,
  finds by III.2 the point of the less segment that the further case needs; and four are
  `carried` by the companions, two by `Prop31.greater` and two by `Prop31.less`, since a
  step proved as a companion is declared as carried. The page says the whole enunciation
  is proved, names both companions in its table, explains where they carry the closing
  sentences, and gives each its certificate.

III.24 uses its companions another way: its main theorem carries the whole enunciation, and
one companion keeps an alternative proof. The main theorem keeps Euclid's application of
one segment to the other (`placement`) and proves coincidence by reductio: III.23's companion
`Prop23.point` puts the image of E on CFD, and III.10 contradicts distinct circles sharing C,
D and that image, so its route is `euclid`. The proof by the radii is kept as the companion
`Prop24.equalCircles`, which proves less: the circles equal, and the circumferences equal in
our measure. The [page](../book/III/24.md) lists it after the main theorem, its docstring
naming it the alternative, and its Argument row and the [record](../review/III/24.toml)'s
route note say so.

**Do not copy.** Full coverage does not make the representation's limits disappear, and a
proof after the main theorem still needs a clear connection to the sentences it carries.
The record and the page must describe the declarations that actually do the work.

## A construction completed by companions: I.45 and II.14

I.45: [Page](../book/I/45.md) · [Lean](../Elements/BookI/Prop45.lean) ·
[mishnah](../mishnah/I/45.md) · [figure](../figures/I/45.svg)

II.14: [Page](../book/II/14.md) · [Lean](../Elements/BookII/Prop14.lean) ·
[mishnah](../mishnah/II/14.md) · [figure](../figures/II/14.svg)

Read against the Lean and the pages at commit `747903c52`, on 30 October 2026, with the
table notes of the two records as the change that adds this example wrote them.

**Why this one.** Both enunciations ask for "a given rectilineal figure", any figure with
straight sides. Euclid's proof of I.45 divides one four-sided figure into two triangles, and
II.14's proof first makes a rectangle equal to the figure by I.45. The main theorems keep his
proofs on his two triangles, and companions after them reach every such figure. The pair
shows how to say which declaration takes which input, and whether a construction returns the
square or only its side; and how a second page leans on the first instead of telling its
story again.

- **The main theorems take two triangles, unchecked.** `Prop45` takes ABD and DBC, and
  `Prop14` the same two lettered A₁A₂A₄ and A₄A₂A₃. Each asks only that they be triangles, so
  they may overlap, and makes a parallelogram, or the square on a straight line, equal to
  their sum. They are the division Euclid pictures in I.45 when A and C lie on opposite sides
  of DB, and that checked case is `Prop45.fan` for the corners D, A, B, C, and `Prop14.fan`
  for the same corners, II.14's A₄, A₁, A₂, A₃. The Statement and Representation rows and
  both commentaries say "unchecked" where they describe the main theorem, as STYLE section 4
  asks.
- **The outline companions give the whole enunciation.** `Prop45.outline` and
  `Prop14.outline` take the figure by its boundary alone: an `Outline`
  ([`Elements/Foundations/Figures.lean`](../Elements/Foundations/Figures.lean)), finitely
  many closed lines of straight sides, which holds no division, triangle list or area, so
  that the figure may have a hole, separate pieces or a corner pointing inwards.
  `Prop45.outline` constructs, in the given angle, a parallelogram equal to the figure's area
  (`Outline.area`). `Prop14.outline` constructs the square with its four corners, a `Square`
  that is also a `Parallelogram`, equal to the same area; `Prop14.outline_side` returns only
  its side, a straight line whose square is that area. Of II.14's main theorem and
  companions, only `Prop14.outline` and `Prop14.square` draw the square: the rest return a
  side, as Euclid ends with "the square which can be described on EH". II.14's mishnah says
  that the main theorem finds the side EH and `Prop14.outline` a square with its four
  corners, and its Representation row says which form returns which.
- **Book Zero gives the division and the one area.** Neither proposition's file proves them.
  `Figures.division_exists`, in
  [`Elements/Figure/Divisions.lean`](../Elements/Figure/Divisions.lean), divides every
  outline into triangles that do not overlap, no point inside two of them, covering exactly
  its region. The content theorem, `Figures.Apart.area_eq_of_same_region` in
  [`Elements/Figure/Content.lean`](../Elements/Figure/Content.lean), after David Hilbert's
  theory of content, proves that two such divisions of the same points have the same sum; and
  `Figures.area_eq`, in `Divisions.lean` again, makes every division's sum the outline's
  area. Each outline companion's proof has three steps: a division, Euclid's
  construction for its triangles (`Prop45.apart`; `Prop14.square`, or `Prop14.apart` for the
  side), and `Figures.area_eq`. I.45's commentary names the two facts as what Euclid takes
  for granted when he calls the sum of ABD and DBC the figure (**"The whole rectilineal
  figure ABCD."**), and II.14's points to it in a clause.
- **The older companions keep a figure given with a checked division.** `Prop45.apart`,
  `Prop14.apart` and `Prop14.square` take triangles that lie apart (`Apart`); `Prop45.figure` and
  `Prop14.figure`, triangles glued edge to edge in a suitable order, for a figure with one
  boundary (`Rectilineal`); and `Prop45.fan` and `Prop14.fan`, Euclid's and Oliver Byrne's
  division from one corner, with its two conditions (neighbours on opposite sides of the
  straight line they share, and the angles at that corner together less than four right
  angles), which `Fitted.fan` shows make the triangles fit together. Each makes its
  parallelogram, or the square on a straight line, equal to the triangles it is given, taken
  together (`Prop14.square` draws that square with its four corners), and that sum is the
  figure's area, the same for every division. They stay beside the outline companions for
  a figure that comes with its division, and `Prop45.fan_boundary` joins the checked fan to
  the outline through its corners. Their detailed hypotheses are in their docstrings, which
  the Proof row links.
- **"Full" is said of the page's declarations together.** Each record's `scope = "full"`
  counts its companions ([review/SCHEMA.md](../review/SCHEMA.md)), and its statement note,
  the Statement row, says which declaration covers what: the main theorem takes two
  triangles unchecked, and the outline companions a figure by its boundary. So the status
  line's "as Euclid states it" is true of the page, and the main theorem's statement is no
  larger for it.
- **Each row tells its part once.** The records, [review/I/45.toml](../review/I/45.toml) and
  [review/II/14.toml](../review/II/14.toml), follow STYLE section 2, "Each thing in one
  place". The Argument rows tell the constructions, the division by `Figures.division_exists`
  among them, and point to Representation for the area; the Representation rows tell the
  inputs, the outline and the checked divisions, and the one area. I.45's Representation row
  keeps the fan's two conditions, and its commentary the argument of `Fitted.fan`, which
  follows the triangles round the corner one at a time. II.14's rows name the division and the area
  in a clause each, point to I.45 for the outline, and add what is II.14's own: the square,
  or its side.

**Do not copy.** I.45's long Representation row and commentary are earned by its inputs and
its fan argument; a page whose figure is given more simply needs neither. Full coverage
through companions does not let a sentence describe the main theorem as covering every
figure, and a companion that returns a side is not "the square". A page that uses Book Zero's
division and area names them where its rows need them and leaves their story to I.45, as
II.14's commentary does, rather than telling it again.
