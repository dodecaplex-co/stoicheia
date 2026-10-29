<!-- entry: id=jev-iii27-iii29-bridges cards=674 line="The Jev generator gives III.27's and III.29's rows the congruence and the earlier bridges their records name, and does not ask them for the two later theorems their notes name as context; it reads List.nodup_cons, written whole, as Lean's own." -->
- **The Jev generator follows III.27's and III.29's records to the earlier bridges they name, and not to the later theorems they name as context (#674).**
  Since III.27 and III.29 were swapped ([that entry](2026-10-28-iii27-iii29-swap.md)), their
  main statements read Euclid's equal circumferences as ones that coincide (`Arc.Congruent`)
  and their companions as ones equal in measure. III.27's representation note says that the
  proof makes them "equal in measure, twice the angle standing on them, by III.24's companion
  `Prop24.equalMeasure`", and that "congruent circumferences already lie in equal circles
  (`Prop24.image`, `Prop24.equalCircles`)". III.29's says that its proof takes "its equal
  angles from III.27, which `Prop27` states with the same congruence", that its companion
  "repeats the argument through III.27's companion `Prop27.of_measure`", and that "the
  congruence already gives the equal straight lines (`Prop24.image`), and the equal circles
  with them (`Prop24.equalCircles`)". The generator gave both rows the measure's bridges
  alone, so its guard refused both. The notes name theorems proved after them as well:
  III.27's says its companion is stated in "the form in which III.29's companion
  `Prop29.of_measure` cites it", and that the two readings agree by `Arc.congruent_iff`,
  "proved after III.29, from it"; III.29's names `Arc.congruent_iff` where "the two readings
  agree". As this entry reads the notes, and it claims no more than that reading, neither
  record rests its verdict on those as bridges. The coordinator ruled on 29 October 2026, in
  these words: "the generator learns the bridges III.27's record uses, rather than the record
  changing its words to pass the test, and a theorem proved after III.27 is not a bridge for
  it. If the record names a later theorem as a bridge, that is a record question". The ruling
  is the coordinator's, not the owner's, and no record is changed.

  `scripts/audit/jev_questions.py` now gives III.27's and III.29's rows the words of the
  congruence (`CONGRUENCE_DEFINITIONS`) beside the measure's, but not `CONGRUENCE_BRIDGES`,
  since `Arc.congruent_iff` is declared in `Elements/BookIII/Arcs.lean`, which imports Prop28
  and Prop29. Both rows get `Prop24.image` and `Prop24.equalCircles`
  (`CONGRUENT_CIRCLE_BRIDGES`), III.27's gets `Prop24.equalMeasure`
  (`CONGRUENT_MEASURE_BRIDGES`), and III.29's gets `Prop27` and `Prop27.of_measure`
  (`EQUAL_ANGLE_BRIDGES`), each declared before the main theorem; the comments quote the
  notes. A table beside `RECORD_CHECKED`, `RECORD_LATER`, holds `Prop29.of_measure` and
  `Arc.congruent_iff` for III.27 and `Arc.congruent_iff` for III.29, and `Generator.checked`
  does not ask a row for such a name on its note's naming it; every other name is asked as
  before, and no check is removed or loosened. Its guard refuses an entry that the record's
  representation note does not name in backticks, a stale entry, and an entry declared before
  the main theorem, by `Index.available_before`, the test of a bridge's placement that
  `Generator.bridges` now calls too. III.29's note names `Arc.measure_eq_iff` "after III.29"
  as well; the row has it from `MEASURE_BRIDGES`, so it is not in `RECORD_LATER`.
  `tests/test_jev_questions.py` adds `CongruentCircumferences`, which generates III.27 and
  III.29 alone at HEAD against their real records. It pins both bundles, with the congruence's
  words and without `Arc.congruent_iff`, and checks `Generator.checked` against copied records
  whose notes contain controlled declaration names. A row leaving out any one of the new
  bridges is refused, as are a `RECORD_LATER` entry that the note does not name, removal of a
  previously named later declaration, and an earlier declaration listed as later context. As
  before, `MEASURE_BRIDGES` gives III.24 to III.30 `Arc.measure_eq_iff`, and
  `CONGRUENCE_BRIDGES` gives III.24, III.26,
  III.28 and III.30 `Arc.congruent_iff`, both declared in `Arcs.lean`, and `bridge_placement`
  marks them in those rows as explanatory later declarations. They stay: the coordinator
  ruled on 29 October 2026, in these words, that "a later theorem is never a bridge a proof
  or statement rests on, but may be supplied as an explanatory later declaration, marked so
  by `bridge_placement`, as these already are". That ruling, too, is the coordinator's, not
  the owner's. The generator sends nothing: it reads no key and makes no request.

  `Elements.Parallelogram.convexOutline`, in `Elements/Figure/Divisions.lean` (#622), shows
  a parallelogram's outline convex, so that its area as an outline is `quadArea`, and writes
  Lean's `List.nodup_cons` whole inside `simp [...]` to show its four corners different. The
  generator's reader did not know the name and reported it unresolved, which stops a
  generation. The coordinator ruled on 29 October 2026, in these words: "XS-jev674 is
  already a check train queued after G2-bridges633, so it gains that one name in the
  generator's allowlist, with a planted case (the name resolves, and an unlisted neighbour
  stays refused). Nothing wider." The ruling is the coordinator's, not the owner's.
  `Calls.CORE_NAMES` now holds `List.nodup_cons`, read as its other names are, only whole
  and after a first word that names no declaration of the project; no other name or rule
  changes. Two tests in `CoreNames` check it: the name read inside `simp [...]` and as
  `@List.nodup_cons` leaves nothing unresolved, and each of `List.nodup_append`,
  `List.nodup_nil`, `Missing.nodup_cons`, `Array.nodup_cons` and `List.nodup_cons_of`, read
  alone, is still found unresolved.
