# Brief 0011: the mixed angles of III.16 and III.31

*18 October 2026. This brief settles the companions that make the records of III.16 and
III.31 full: the statements of their last clauses, on angles contained by a straight line
and a circumference, with the words those statements use and the homes of the proofs. It is
written for the coordinator's approval in the pull request that moves the prototype of
mixed angles into the edition (issue #57), as [WORKFLOW.md](../WORKFLOW.md), section 2, asks
of every new statement; until that approval nothing in it is frozen. Brief
[0007](0007-stage-4b.md) left III.16 and III.31 out of stage 4b to wait for this prototype
(its question 4), and this brief takes them up beside it.*

The representation is Astra's, from its answer on
[issue #51](https://github.com/jackChallis/stoicheia/issues/51); the prototype that tried
it is [`docs/reports/mixed-angles-prototype.md`](../reports/mixed-angles-prototype.md)
(#56), which the coordinator approved on 18 October (the decisions entry "Mixed angles: the
prototype approved, its proofs kept in Staging"). The owner's decision on #51 was that if
the prototype holds, III.16 and III.31 go full. Astra then read the prototype afresh, at
`4d02d50`, and passed it for both propositions, finding no gap in the four comparisons
themselves; its findings, and what was done with each, are below. This brief owes Astra the
design, the checks it asked for and the challenge that shaped the move: warm thanks.

Base: the branch was written on `origin/main` at `32eeba5`, and has main merged in at
`0c221b6` (`5812d71`). The first commit of the branch, `ca8bd4d`, renames the prototype's
`exists_centre` to `exists_circle_about`, as brief 0008 (question 12) asks, before the rule
`Tacit.exists_centre` lands. No axiom is added or changed: the lock's `[axioms]` table stays
the same 87, byte for byte.

## Companions, not restatements

The report's condition 2 proposed restating `theorem Prop16` and `theorem Prop31` with the
comparisons as further conjuncts. This brief takes companions instead, by the rule of
[FORMALIZATION.md](../FORMALIZATION.md), section 2, "Companions beside Euclid's worked
configuration": a statement narrower than Euclid's words keeps its place under his
sentences, and the general result stands beside it. So the frozen statements of III.16 and
III.31 do not change, no `--` line moves, and nothing that cites them is touched. The
companions are entries of the certificate in their own right, and a record's scope
describes the main theorem together with them (review/SCHEMA.md), so the clauses are
counted among the declarations the certificate checks.

Euclid's sentences on the mixed angles keep no Lean beneath them in the main theorems, as
the sentence of III.16's porism keeps none: each record declares the passage and names the
companion that proves it.

## The words

Each moves, unchanged in meaning, from the prototype to
`Elements/Foundations/DefinitionsIII.lean`, under Definition III.7:

| Word | Plain words |
|---|---|
| `WithinAngle B A C P` | P is on C's side of AB and on B's side of AC: the region of the rectilineal angle BAC |
| `MixedAngle`, `.ofSegment A B α S`, `.ofContact A E α B` | the angle of a segment, AB and the circumference on S's side; the angle of contact, AE and the circumference on E's side of AB |
| `MixedAngle.vertex`, `MixedAngle.region` | its vertex; its region, within the circle for a segment, without it for contact |
| `MixedAngle.WellFormed` | the named points give the angle Euclid draws |
| `LocallyWithin`, `NearVertex`, `Surrounds`, `NearVertexOpen` | within, near A; points near A; a whole circle about P; whole circles near A |
| `LocallyLess`, `LocallyEqual` | less near A, with whole small circles of excess; equal near A |
| `MixedAngle.Exceeds m B C`, `MixedAngle.FallsShort m B C` | `m` greater, or less, than the true angle BXC placed at its vertex X; a "less" also says that `m` is something |

None is an assumption. They join the lock's vocabulary once the companions' statements
reach them: `check_fidelity.py --write-lock` grows `[vocabulary]` from 91 words to 107, by
the thirteen the statements reach (`WithinAngle`, `MixedAngle` with its two kinds,
`vertex`, `region`, `WellFormed`, `LocallyWithin`, `Surrounds`, `NearVertexOpen`,
`LocallyLess`, `Exceeds`, `FallsShort`) and three that Lean declares for them
(`MixedAngle.rec`, `.casesOn`, `.vertex.match_1`). `NearVertex` and `LocallyEqual` are
reached by no statement. Two caveats that Astra asked to see at the interface are now in
the docstrings and the module doc: the comparisons compare the angles as placed, and are
Euclid's comparison only with the rectilineal angle along the mixed angle's straight arm,
on its side; and the kinds may be formed from any points, so a statement about Euclid's
angle states its figure or proves `WellFormed`.

## Homes and owners

| Module | What goes in it | Place in the dependency order |
|---|---|---|
| `Elements/Foundations/DefinitionsIII.lean` | the words above | the foundations |
| `Elements/Figure/Regions.lean` (new, Book Zero; `Basics.lean` gathers it) | the facts that cite no proposition: sides and rays, circles about a point, rectilineal angles as regions, the order laws, the regions of a mixed angle | Book Zero |
| `Elements/BookIII/MixedAngles.lean` (new shared module) | the steps that cite a proposition: III.2 for points on or within a circle with a centre, whole circles about a point, the order of rectilineal angles as regions, an angle in a circle near its vertex | after I.20 and III.2, before III.16 |
| `Elements/BookIII/Prop16.lean` | after the porism: III.16's two parts as `Prop16.Outside` and `Prop16.FallsWithin`, the steps, the companions, then the comparisons at another vertex | after `theorem Prop16` |
| `Elements/BookIII/Prop31.lean` | after the theorem: the steps, then the companions | after `theorem Prop31` |
| `Elements/Companions.lean` | the five entries | |

The staged file goes in the same change. The shared module is new because
`Elements/BookIII/Squares.lean`, FORMALIZATION's home for Book III's steps that cite Book I,
holds squares and the perpendicular from the centre, and these steps cite III.2 as well; one
file keeps the machinery of the mixed angles together for a reader. This move's task writes
every file in the table: `DefinitionsIII.lean` by the coordinator's delegation, and
`Companions.lean`, the integrator's list, in the commit that moves the companions, as
[WORKFLOW](../WORKFLOW.md), section 4, has it.

Two steps overlap statements that other stages bring, as the report says (its section 2):
`len_lt_of_add_lt` is I.20 with its degenerate case, which stage 3 states as
`Prop20.collinear_iff` in `Elements/BookI/HelpersTriangles.lean`, and `foot_nearest` takes
the foot of the perpendicular as I.12 gives it, which stage 4 names `Foot`. Neither is on
main, so both steps stay in the shared module; when those land, the steps can go beside
them, or be derived from them, with a change of homes alone.

## III.16: the angle of the semicircle, and the remaining angle

Companions "III.16 semicircle", "III.16 remaining" and "III.16 acute".

```lean
theorem Prop16.semicircle {A B D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) :
    (MixedAngle.ofSegment A B ABC E).WellFormed ∧
      ∀ F : Point, SameSideOf F E A B → ∠ B A F < ∟ →
        (MixedAngle.ofSegment A B ABC E).Exceeds B F

theorem Prop16.remaining {A B D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) :
    (MixedAngle.ofContact A E ABC B).WellFormed ∧
      ∀ F : Point, SameSideOf F B A E → ∠ E A F < ∟ →
        (MixedAngle.ofContact A E ABC B).FallsShort E F

theorem Prop16.acute {A B D E X Y Z : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) (hXYZ : Triangle X Y Z) (hacute : ∠ X Y Z < ∟) :
    (∃ F : Point, SameSideOf F E A B ∧ ∠ B A F = ∠ X Y Z ∧
        (MixedAngle.ofSegment A B ABC E).Exceeds B F) ∧
      ∃ F : Point, SameSideOf F B A E ∧ ∠ E A F = ∠ X Y Z ∧
        (MixedAngle.ofContact A E ABC B).FallsShort E F
```

- **In plain words.** In III.16's figure, the circle ABC about D with the diameter AB and AE
  at right angles to it at A: the angle of the semicircle, contained by BA and the
  circumference on E's side, is a mixed angle as Euclid draws it, and it is greater than
  every acute angle BAF placed at A along AB on that side. The remaining angle, contained by
  that circumference and AE, is one too, and it is less than every acute angle EAF placed at
  A along AE on the circle's side; "less" says too that it is something. Every acute
  rectilineal angle XYZ, wherever it is, can be placed at A in both ways (I.23), and there
  it is exceeded by the one angle and exceeds the other.
- **Coverage.** Heath: "further the angle of the semicircle is greater, and the remaining
  angle less, than any acute rectilineal angle". Full, with the main theorem's two parts and
  the porism. "Any" survives twice: `semicircle` and `remaining` take every acute angle
  placed at A, and `acute` every acute angle anywhere, brought to A; a copy placed along one
  arm on one side has one region whatever the copy (`WithinAngle.locallyLess_placement`).
- **Cases.** F on the straight line AB makes no true angle, and the true-angle clause of
  `Exceeds` and `FallsShort` refuses it. F across AB from E places the angle away from the
  semicircle, a placement Euclid does not make, and the companions do not speak of it. A
  right or obtuse angle BAF: the angle of the semicircle falls short of it
  (`Prop16.semicircle_fallsShort_iff`), and exceeds exactly the acute ones
  (`Prop16.semicircle_exceeds_iff`). The remaining angle falls short of every true angle on
  the circle's side, acute or not, and exceeds none (`Prop16.horn_fallsShort_iff`,
  `Prop16.horn_not_exceeds`); it is not the region of any rectilineal angle
  (`Prop16.horn_no_ray`), and in this figure it does not depend on which straight line into
  the circle names its branch (`Prop16.horn_locallyEqual`). Heath's "remaining angle" is
  what is left of the right angle BAE when the angle of the semicircle is taken away, with
  the circumference between them (`Prop16.right_parts`).
- **Representation.** The tag `mixed-angles-local` (below). `WellFormed` is proved in each
  conclusion, so the certificate covers that the named points give the angle Euclid draws;
  that the angle of contact's straight line touches comes from the porism.
- **Route.** Euclid proves the clause by reductio from the second part: an acute angle
  greater than the angle of the semicircle, or one less than the remaining angle, would put
  a straight line between AE and the circumference. The companions argue directly from the
  same part: the straight line AF of an acute angle falls within the circle at some G
  (III.16's second part), so near A the angle BAF lies within the circle, and so within the
  angle of the semicircle, and what is left over holds whole small circles. That is a step
  argued another way: the passage is `different`, and the route becomes `modified`, as I.39
  and I.40 do for a reductio made direct. What Euclid leaves unsaid is how near A: the
  perpendicular from A to GD says it, by I.12, I.17 and I.19, and I.20 gives the whole
  circles of the excess.
- **Dependencies.** III.16, III.16 Por., I.23, and through the steps I.12, I.17, I.19, I.20
  and III.2.

## III.31: the angles of the greater and the less segment

Companions "III.31 greater" and "III.31 less".

```lean
theorem Prop31.greater {A C E : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hC : OnCircle C ABCD) (hACE : ¬ Collinear A C E) :
    (MixedAngle.ofSegment A C ABCD E).WellFormed ∧
      ∀ R : Point, SameSideOf R E A C → ∠ C A R = ∟ →
        (MixedAngle.ofSegment A C ABCD E).Exceeds C R

theorem Prop31.less {A C D E : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hC : OnCircle C ABCD) (hACE : ¬ Collinear A C E)
    (hED : OppositeSidesOf E D A C) :
    (MixedAngle.ofSegment A C ABCD D).WellFormed ∧
      ∀ R : Point, SameSideOf R D A C → ∠ C A R = ∟ →
        (MixedAngle.ofSegment A C ABCD D).FallsShort C R
```

- **In plain words.** For any straight line AC in the circle ABCD about E, not through the
  centre, and either of its ends, named A: the angle of the segment on the centre's side,
  the greater segment, is a mixed angle as Euclid draws it, and it is greater than every
  right angle CAR placed along AC on that side; the angle of the segment on the other side,
  the less segment, named by any point D there, is one too, and it is less than every right
  angle placed along AC on its side, and is something.
- **Coverage.** Heath: "and further the angle of the greater segment is greater than a right
  angle, and the angle of the less segment less than a right angle". Full, with the main
  theorem. Euclid's figure is the case in which B, the far end of the diameter through C,
  names the greater segment (`Prop31.diameter_through`); the companions take every straight
  line in the circle at either end, Astra's "for every nondiameter chord, at either
  endpoint". A diameter is no case: its two segments are semicircles, neither greater nor
  less, and III.16 speaks of the angle of the semicircle.
- **Cases.** Every right angle on the segment's side has one region, the angle CAB or CAF,
  since on one side one ray makes a given angle. The less segment lies wholly within the
  right angle CAF, not only near A; the greater segment's containment of CAB is near A.
- **Representation.** As for III.16, and `MixedAngle.wellFormed_ofSegment` for the
  conclusion's `WellFormed`.
- **Route.** Euclid's: "This is at once manifest", from the right angles BAC and FAC, and the
  companions prove the manifest containments, the right angle BAC within the circle near A
  by the perpendicular's bound and the less segment within the right angle CAF (System E,
  Circle 1, Pasch 2 and 3). The steps take the right angle BAC as a hypothesis, and each
  companion takes it from III.31, with the diameter through C. The route stays `euclid`:
  the record's two passages are `helper` passages, each naming its companion for the
  containment Euclid calls manifest.
- **Dependencies.** III.31, and through the steps I.12, I.17, I.19, I.20 and III.2. Through
  III.31, which cites I.32, the companions' proofs use Postulate 5, as III.31's does.

## The representation, and what it does not claim

The records drop `mixed-angles-omitted`, a tag of kind `scope` that a full record cannot
carry, and take a new tag of kind `representation`, `mixed-angles-local`, with Astra's
wording from the report's condition 4: the comparisons use local containment of curved
angular regions near the vertex, and no general arithmetic or ratio theory of mixed angles
is claimed. It has no badge: the pages show the reading in the Representation row and the
mishnah, as for `figure-with-dissection` (question 5). A tag is added to
`review/terms.toml` before any record uses it, and that file is a check's data, so the tag
lands first, in a pull request of its own (`tooling/mixed-angles-tag`), and the records
after it.

What the edition does not claim, each said where a reader meets it:

- no addition, multiple or ratio of mixed angles, and no law that every two are comparable:
  the horn is something and less than every acute angle, so no Archimedean law holds of the
  two kinds together (the report, section 3);
- no motion of a mixed angle: the comparisons at another vertex
  (`Segment.compare_alike`, `Prop16.semicircle_compare_alike`, `Prop16.horn_compare_alike`)
  are invariances of the comparisons with rectilineal angles, and agreeing with every
  rectilineal angle does not make two mixed angles one;
- the angle of contact for a straight line given only as touching, in general:
  `Prop16.horn_locallyEqual` is proved in III.16's figure, and the general case would need
  III.18, later than III.16;
- a comparison of arbitrary points: `Exceeds` and `FallsShort` say nothing of Euclid's
  angles until the figure, or `WellFormed`, and the placement along the straight arm are
  given.

## What changed on the move

The statements of the prototype's companions, the steps and the checks are kept, and their
proofs too, save these changes:

| In the prototype | In the edition | Why |
|---|---|---|
| `exists_centre` | `exists_circle_about` | brief 0008, question 12 (`ca8bd4d`) |
| `Prop16.semicircle_gt`, `Prop16.horn_lt`, with III.16's parts as hypotheses | kept as steps; the companions `Prop16.semicircle` and `Prop16.remaining` take the parts from III.16 and add `WellFormed` | Astra: the parts are results of the proposition, not hypotheses of what is published |
| `Prop16.semicircle_gt_acute`, `Prop16.horn_lt_acute` | one companion, `Prop16.acute` | one entry for "any acute rectilineal angle" |
| `Prop31.any_greater_gt_right`, `Prop31.any_less_lt_right` | the companions `Prop31.greater`, `Prop31.less`, with `WellFormed`, and without the hypothesis A ≠ C, which `¬ Collinear A C E` gives | as for III.16 |
| `Prop31.greater_wellFormed`, `Prop31.less_wellFormed` | one step, `MixedAngle.wellFormed_ofSegment`, of which each was a case | one lemma for every straight line in a circle |
| `Prop16.remaining` (the right angle in three parts) | `Prop16.right_parts` | the name goes to the companion, Heath's "remaining angle" |
| `Segment.congruent`, `Prop16.semicircle_congruent`, `Prop16.horn_congruent` | `Segment.compare_alike`, `Prop16.semicircle_compare_alike`, `Prop16.horn_compare_alike` | Astra: invariance of the comparisons, not superposition |
| System E's Circle 2 and Circle 3, called on seventeen times, and Book Zero's `Triangle.of_onCircle`, which calls Circle 2, four times | III.2, for a circle with a centre: `InsideCircle.of_between`, `OutsideCircle.of_between`, `Triangle.of_onCircle_centre`; `exists_onRay_inside` and `WithinAngle.exists_near` by lengths and rays alone | Circle 2 contains III.2 ([overlaps](../reports/overlaps.md)); the edition's proofs are coming off it (#60), and the companions should not bring it back |
| `near_inside_of_angle`, `exists_near_across`, `near_inside_of_ray`, `near_inside_of_onRay`, `Prop16.sameSideOf_of_inside` | each takes the circle's centre too | so that III.2 applies |
| `WithinAngle.of_onRay` | new, in Book Zero | for `WithinAngle.exists_near` |

The three III.2 corollaries say what `Prop2.within` and `Prop2.triangle` say on the branch
that takes the proofs off Circle 2 (#60), and are proved the same way; when that branch is
on main they can give way to its names, a change of citations alone. Until #60 lands, III.2
itself still rests on Circle 2 through III.1, so the companions' certificates list it,
inherited through III.2; no proof of theirs calls it.

## Astra's challenge, and what was done

Astra read the prototype at `4d02d50`, in a read-only checkout, and edited nothing. "M" is
the staged file at that revision, and "R" the report.

| Finding | Done |
|---|---|
| *Note.* The four regions represent the objects in the intended configurations; branch choices are controlled | No change needed |
| *Should fix.* Raw data and an actual mixed angle are not told apart: the constructors impose nothing, and the comparisons accept any data (A at the centre) | The companions prove `WellFormed` in their conclusions, so what is published names the angles Euclid draws; the docstrings of `MixedAngle`, `Exceeds` and `FallsShort`, and DefinitionsIII's module doc, say that the words take any points and that a statement about Euclid's angle states its figure or proves `WellFormed`; the tag's representation note says so on the page |
| *Note.* The representation is an interpretive choice; R:161's "The angles are Euclid's" says more than the `_wellFormed` lemmas show | The report is history and keeps its heading; this brief, the tag, the records and the mishnah call the comparison a reading, and `WellFormed` is described as the named points giving the angle Euclid draws, nothing more |
| *Note.* `Exceeds` and `FallsShort` express the comparisons when the rectilineal angle is placed along the arm, on the side; the quantifier "any acute angle" is addressed | No change needed |
| *Should fix.* The bare predicates depend on placement, so `¬ m.Exceeds B C` is no comparison of sizes in general | Said in the docstrings of `Exceeds` and `FallsShort` and in the module doc; every published statement places the angle along the arm on the side |
| *Note.* The tangent threshold is handled correctly | No change needed |
| *Blocking if claimed as superposition.* `Segment.congruent` contains no placement, and agreement against every rectilineal angle does not determine a mixed angle (two circles touching within) | Renamed `Segment.compare_alike`, with the two others; their docstrings and the module doc of `Prop16.lean`'s last section say they are invariances of the comparisons, move no mixed angle, and give the touching circles as the reason agreement is not equality. None is a companion. The decisions entry of 18 October that called this form the check of congruent placement is history; the new entry corrects the wording |
| *Note.* `horn_congruent` is vacuous when F = A, and asks no equality of the test angles | Said in `Prop16.horn_compare_alike`'s docstring; no hypothesis added, since one unused would be an artificial use |
| *Blocking.* III.16's statement omits both mixed-angle conclusions | The companions "III.16 semicircle" and "III.16 remaining" state them, and "III.16 acute" the form for any acute angle; the record lists them and becomes full |
| *Blocking.* III.31's statement omits both angles of segments | The companions "III.31 greater" and "III.31 less" state them, in the general form of M:2009 and 2023 |
| *Blocking.* The helpers' premises (III.16's parts, the right angle BAC) must be results, not assumptions of what is published | Each companion takes them from `Prop16` or `Prop31`; only the steps take them as hypotheses |
| *Blocking.* Preserve the dependency order: the prototype imported both propositions | The steps that cite no proposition are in Book Zero, those that cite Book I or III.2 in the shared module, and everything that cites III.16 or III.31 after the theorem in its file; nothing cites a later proposition, which the certificate checks |
| *Should fix.* Make the domain and placement requirements explicit at the public interface | As the two rows above on raw data and placement |
| *Should fix.* III.16's comparisons are direct where Heath's closing passage is a reductio; a `helper` label does not account for it | The record's passage is `different`, naming `Prop16.semicircle`, and the route becomes `modified`, with a note (the III.16 section) |
| *Blocking for sign-off.* Build and certify the integrated declarations and review them at the delivered revision | Built and certified on this branch, the checks and their revision in the pull request; the records are stale until a reviewer who did not write this reads and stamps them |
| *Refuse outright.* Full while the statements omit the clauses; congruence claimed; well-formedness inferred from the predicates; the parts kept as hypotheses, a circular dependency, or a new axiom | None of these is done: the clauses are companions counted by the certificate, no congruence is claimed, `WellFormed` is proved, the parts are results, the order holds, and no axiom is added |

## Records made stale, and prose that follows

- `review/III/16.toml`, `review/III/31.toml`: their Lean files change and companions attach,
  so their fingerprints change. This branch writes their new entries (full, the companions,
  the passages, the tag); a reviewer who did not write them reads and stamps them. They use
  the new tag, and III.16's declares its angle clauses as argued another way, where
  `scripts/negative_tests.py` looks for a passage left in Euclid's words; so they land
  after two check changes of their own, `tooling/mixed-angles-tag` and
  `tooling/negative-iii16-passage`, which teaches that test to find the run's passage of
  any kind.
- `mishnah/III/16.md`, `mishnah/III/31.md` and `mishnah/intro/III.md`: the sentences that
  said the clauses stay in Euclid's words are rewritten on this branch.
- For their owners, each now false or stale once this lands:
  [FORMALIZATION.md](../FORMALIZATION.md), section 2's examples of partial statements
  (III.16, III.31) and section 3's table row for an angle of a straight line and a
  circumference; [brief 0004](0004-book-III.md)'s rows for Definition III.7, III.16 and
  III.31 and its paragraph on mixed angles; `docs/reports/gaps-book-III.md` under III.16;
  `docs/examples.md`, whose III.31 example cites `mixed-angles-omitted`;
  `scripts/render.py`'s front page row for Definition III.7 ("none: a mixed angle") and the
  comment on words with no Lean partner; `review/terms.toml`'s `mixed-angles-omitted`, which
  no record will use; README.md's sentence on passages the Lean argues another way or leaves
  in Euclid's words, "as in I.4, III.16, III.25 and III.31", from which III.31 goes (III.16
  stays, its step argued another way); PROGRAM.md, the coordinator's, whose limitations
  allowed in Book III name the mixed angles; and the generated pages and README rows, the
  integrator's.

## Questions for the coordinator

1. **The companions' names.** `semicircle`, `remaining` and `acute` follow Heath's
   enunciation; `greater` and `less` his segments. Approve, or name others.
2. **`WellFormed` in the conclusions.** Recommended, as above: it puts on the certificate
   that the named points give the angles Euclid draws. The alternative is the `_wellFormed`
   lemmas alone.
3. **III.16's two parts as definitions in III.16's file.** `Prop16.Outside` and
   `Prop16.FallsWithin` abbreviate the theorem's two conclusions for the steps; no published
   statement uses them, so they stay out of the lock. Recommended: keep them there. The
   report's alternatives were the foundations, or writing them out in each step.
4. **The III.2 corollaries.** Recommended: keep them here until #60 lands, then cite
   `Prop2.within` and `Prop2.triangle` and delete them, in the train that brings the two
   together.
5. **The tag, without a badge** (the section on the representation). A badge, "in our
   reading of mixed angles", beside the green check would say at a glance that the
   comparison is a reading; but the certificate's sentence on badges says that a statement
   so marked "has no radius in it", which is true only of `angle-measure`, so a badge waits
   for that sentence in `scripts/render.py` to be rewritten, in a tooling change of its
   own. Recommended: the tag now, and the badge only if the coordinator wants it.
6. **III.16's route `modified`.** Recommended, as Astra advises and I.39 and I.40 have it.
