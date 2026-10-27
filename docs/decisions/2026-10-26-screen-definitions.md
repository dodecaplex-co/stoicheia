- **The overlap screen takes the 37 words its pass over the definitions stopped on
  (tooling, [#416](https://github.com/jackChallis/stoicheia/issues/416)).** The
  coordinator's orders of 25 October 2026 (evening) assign card #416, the overlap screen
  after train C6a and wave two. With this train, [`Audit/screen.py`](../../Audit/screen.py)
  can run again: its pass over the definitions no longer stops. The card's second item,
  the canary III.5, is not settled here; it follows in a train of its own, with an entry
  of its own. No Lean file, statement, definition, lock or `--` line changes, and
  `facts.json` stays as it was.

  Why 37, not 18. Before its tries, the screen walks from each statement and each rule of
  `facts.json` through the bodies of the definitions they reach, and stops on any
  definition of the edition that none of its lists names, since a word it does not unfold
  leaves `grind` nothing to reason with. The card counted the 18 words that train C6a's
  statements reach. At cf1591f14, with the screen main has, the pass reaches 85
  definitions and stops on 37, so that placing C6a's 18 alone would leave it stopped. A
  walk from each statement in turn, at the same commit, shows where each group comes
  from:
  - the statements train C6a brought (III.16's and III.31's companions, the restated
    III.24, III.26 and III.28, and III.24's equal measure) reach 18: `WithinAngle`,
    `LocallyWithin`, `Surrounds`, `NearVertexOpen`, `LocallyLess`, `MixedAngle.Exceeds`,
    `MixedAngle.FallsShort`, `MixedAngle.WellFormed`, `MixedAngle.vertex`,
    `MixedAngle.region`, `MixedAngle.casesOn`, `Arc.Congruent`, `Arc.Drawn`,
    `Arc.measure`, `InSegment`, `OnArc`, `OnSideOrLine` and `Places`;
  - those train C6b brought reach four more: III.25's kind reaches `Arc.Less`,
    `Arc.Semicircle` and `Arc.Greater`, and III.14's general case and III.15's nearer
    reach `Foot`;
  - the outline companions of I.45 and II.14 (22 October 2026) reach fifteen more:
    thirteen words of `Figures` (`sides`, `Covers`, `Divides`, `LoopBoundary`, `GoodRay`,
    `RayCrosses`, `crossingCount`, `LoopInside`, `Outline.Boundary`, `Outline.depth`,
    `Outline.Inside`, `Outline.Region` and `Outline.area`) and the phrases
    `OnFiniteLine` and `OnOrInsideTriangle`.

  Two later statements, III.25's completion (train C6b) and III.30's halves (21 October
  2026), reach only words of the first group. Until every one of the 37 is placed the
  screen cannot run, so this train places them all.

  Where each goes, by the rule each list's comment states. Thirty-five go in DEFS, unfolded
  in every try: the phrases that say something of points, regions and arcs; the three
  words defined by cases on the mixed angle, a type of two kinds (`MixedAngle.vertex`,
  `.region` and `.WellFormed`), unfolded by the equations Lean proves for them, as
  `segments` is; `Figures.sides`, defined by cases on a list; `Arc.measure`, which is the
  circumference it names, so that the lemma CHOSEN already gives for `circumference` then
  applies; and the two counts, `Figures.crossingCount` and `Figures.Outline.depth`, each
  the length of a list. One goes in CHOSEN: `Figures.Outline.area`, an area Lean chooses,
  given by a new lemma of SPECS, `Screen.outline_area_spec`, proved from Lean's choice
  alone: if some triangles divide the figure's region, the area is that of some such
  division. It leaves out `area_eq`, that every division gives the area, as the lemma of
  `circumference` leaves out III.21, and the docstring says so. The last,
  `MixedAngle.casesOn`, is no word of ours. A probe at cf1591f14 shows the three words by
  cases all compiled through one matcher, `MixedAngle.vertex.match_1`, which calls
  `MixedAngle.casesOn`, the recursor Lean makes for the type (an auxiliary recursor, by
  Lean's own test). The screen's rule already said that the definitions Lean makes for
  itself, to compile a definition by cases or by recursion, are followed and not listed,
  and the pass held to it for the matchers and for names with a part that begins `_`; it
  now holds to it for Lean's auxiliary recursors too (`isAuxRecursor`), and still walks
  their bodies, as it walks every definition it reaches. Nothing went to CARRIERS, and no
  list of a new kind was needed; `Arc` and `Figures.Outline` are structures, whose fields
  the pass follows as it follows `Apart.pieces`.

  Seven goals join CONTROLS, which the preamble of every file of tries proves: a mixed
  angle's vertex, a point of its region within the circle, a point of an arc in its
  segment, an arc's measure through the circumference's lemma, an outline's area through
  its new lemma, the sides of a triangle's outline, and the crossings of an outline with no
  corners. In a probe at cf1591f14, each closed with every word given and failed without
  the one it shows, so a file whose preamble stops unfolding these words stops, as it does
  for the earlier words. No word, control, rule or known row is removed from any list, and
  no budget changes.

  The evidence, at cf1591f14. With this train's screen, the pass reaches 84 definitions,
  every one of them listed, and every word listed is reached; the screen's reading of the
  pass accepts it. A full run, `python3 -I Audit/screen.py OUTDIR --jobs 6`, without
  `--write`, on 26 October 2026, ended so:

  ```text
  18200 attempts, 140 of them bare; 31360 tries (4900 left with no rule grind takes); 86 ran out of time at 30000 and were tried again at 120000
  0 tries closed:
  0 statements closed with no rule, by their definitions and logic alone: none
  0 statements closed by a rule: none
  8 tries ran out of time again, not searched to the end, on III.34:
    family__BookIII_Prop34__Postulates
    fampair__BookIII_Prop34__Constructions__Postulates
    fampair__BookIII_Prop34__Definitions__Postulates
    fampair__BookIII_Prop34__Diagram__Postulates
    fampair__BookIII_Prop34__Magnitudes__Postulates
    fampair__BookIII_Prop34__Postulates__Superposition
    fampair__BookIII_Prop34__Postulates__Transfer
    single__BookIII_Prop34__Postulate4
  screen: the known rows ['BookIII.Prop5'] did not close by a rule; the screen may be broken
  ```

  and it exited 1. No try closed, bare or with rules. The exit is the canary of the card's
  second item: the restated III.5 needs Generalities 4, a theorem since the second axiom
  retirement, and the screen tries axioms alone. This train asks nothing less of KNOWN or
  of its one row: III.5 stays, and the reading of a lost row is as it was. So until the
  canary's train lands, every run of the screen on this revision reports itself broken,
  and `--write` records nothing.

  The tests. `tests/test_screen.py` gains three cases of the pass over the definitions:
  the 36 words are listed, 35 in DEFS and the area of an outline in CHOSEN with its lemma;
  each, taken out of its list again, stops the pass, which names that word and no other,
  and so does a planted word, `MixedAngle.apex`, that no list names; and
  `MixedAngle.casesOn` is in no list, the pass's filter names `isAuxRecursor`, and a pass
  that printed `casesOn` would stop the screen. Against the screen main has at cf1591f14
  all three fail; with this train's, the file's 63 cases pass. No case is removed or
  loosened, and no expected value changes.

  The account. The screen's docstring says what is unfolded now, and its account of the
  runs says that from train C6a until this train the screen could not run, which words
  held it, and what the run above gave; it and the comment on KNOWN name #416 where they
  named #160 for these two items. The catalogue of overlaps,
  [`docs/reports/overlaps.md`](../reports/overlaps.md), still names #160 for them and says
  that the screen cannot run; this train does not change it. The decisions page's entry for
  wave two names #160 for them too; it is dated history, and this entry is the record that
  card #416 carries them now. Neither this entry nor the train claims any decision of the
  owner's.

  This entry approves the change to `Audit/screen.py`, which places 35 words in DEFS and
  `Figures.Outline.area` in CHOSEN with its lemma `Screen.outline_area_spec` in SPECS, adds
  seven goals to CONTROLS, has its pass over the definitions follow Lean's auxiliary
  recursors with the matchers, and brings its docstring and the comment on KNOWN up to
  date, removing nothing from any list.

  This entry approves the change to `tests/test_screen.py`, which gains three cases of the
  pass over the definitions, with a sentence on them in its docstring, and loses or loosens
  none.
