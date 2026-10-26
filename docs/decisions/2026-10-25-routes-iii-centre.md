- **The angle at the centre of any size moved into `Elements/`, with III.20 for it and
  III.21 and III.26 by Euclid's argument (Book III, #129).**
  On 25 October 2026 the owner chose, of the options put to them (the coordinator's
  decisions-waiting item 15), "A": the drafts of #126, #129 and #130 for Euclid's routes in
  Book III are approved in the text they had. The coordinator has recorded that ruling on
  #126, #129, #130 and #332. Two entries of that day,
  [one for #130](2026-10-25-routes-iii-contact.md) and
  [one for #126](2026-10-25-routes-iii-touching.md), moved two of those drafts; this one
  moves #129's, the last, and with it the work #332 tracks is done.

  Under the ruling, the word for the angle at the centre standing on a circumference,
  `angleAtCentre`, leaves the staged Prop20.lean for the foundations' definitions of Book
  III, next to `circumference`, its binders, body and docstring untouched. Its seven
  theorems, `angleAtCentre.diameter`, `.congr`, `.within`, `.semicircle`, `.reflex`,
  `.reflex_gt` and `.size`, and five private steps now stand ahead of III.20 in
  [Elements/BookIII/Prop20.lean](../../Elements/BookIII/Prop20.lean), under
  `Elements.BookIII`. One staged step, that an angle of a triangle is less than two right
  angles, is not carried over: it repeated a lemma of I.13's file,
  triangle_angle_lt_two_right, by I.13 and Common Notion 5, which loses the word
  `private` and takes the name `Prop13.angle_lt_two_right`, by FORMALIZATION's rule for a
  proposition's helpers, its statement and proof unchanged, so that `.reflex_gt` and `.size` cite it from that one home.
  Book I's public `Figures.OutlineBound.angle_lt_two_right` gives the same fact, but rests
  on Metric 5, and citing it would have added that axiom to III.26 and to the propositions
  that cite III.26, so it is not cited.
  III.20 in general takes the name `Elements.BookIII.Prop20`, Heath's sentences standing
  over the staged proof. The statement III.20 had until now becomes its companion
  `Prop20.special`, and the theorem that each circumference is its angle at the centre
  becomes the companion `Prop20.circumference`; the certificate lists them as "III.20
  special" and "III.20 circumference", from `Elements/Companions.lean`, and
  `Prop20.across_side` follows as a step. III.21 and III.26 keep their statements, and
  their proofs give way to the staged ones, which take Euclid's single argument; III.26
  gains the step `Prop26.alike`. A scratch Lean file outside the repository compared each
  moved declaration with the staged one, its type with binder names, binder kinds and
  universe parameters, and the definition's value as well, and found no difference; the
  staged forms of III.20 special, III.21 and III.26 matched the statements `Elements` held,
  in the same strict way. III.27, III.28, III.24's companion `Prop24.equalCircles` and
  `Circumference.centre` call `Prop20.special` where they called the old III.20, while the
  new proofs of III.21 and III.26 cite the general one. The three staged files are deleted,
  `Staging/Routes/` goes with them, and `Staging.lean` imports nothing now.

  This changes a released statement, III.20's. FORMALIZATION, section 2, "A statement that
  changes keeps its name", is followed: `Prop20` names the general statement now, and the
  former one survives beside it as III.20 special, which each of its citers names. The
  release notes, which list such a change and say where the old form went, belong to the
  owner and are written at the next release.

  The review records of III.20, III.21, III.26 and III.27 were made to say what is true of
  the new Lean, with their verdicts taken out, and then read in full by an independent
  reader who wrote none of them, who stamped them at `d2e249c39`; the records of III.24 and
  III.28, whose Lean changes by the one citation, and of I.13, whose lemma loses the word
  `private`, were read again for that change, and stamped at `d2e249c39`
  (III.28's, after one note was corrected, at `4aad4576`). Review then corrected III.21's
  passage note on the joins, III.27's commentary on the right angles and III.28's Lean
  comments on the diameters, and gave I.13's lemma its name; those three records, with
  I.13's and III.20's for the name, were read and stamped again. III.21's route becomes `euclid`; III.26's
  stays `modified`, because the congruence of the circumferences that remain is still
  argued by III.22 and III.24 rather than by Euclid's subtraction. The mishnah of the four,
  the gap catalogue's entries for III.20, III.21, III.26 and III.27, the overlap catalogue's
  sentence on the staging folder, and an addendum to the
  [routes report](../reports/routes-book-III.md) record the rest. Book III's brief keeps its dated bullets on III.20
  and III.21 and gains a dated note under each saying what is overtaken.

  By the coordinator's orders of 25 October 2026, given as owner of the foundations, this
  train writes `Elements/Foundations/DefinitionsIII.lean`: the new word is placed there
  beside `circumference`, as those orders set its home, and the module text names it
  among the words of Book III.

  `Certificate/axioms.lock` was regenerated with `check_fidelity.py --write-lock` under
  the coordinator's approval, as the lock's owner, of one word and no more, `angleAtCentre`;
  its vocabulary rises from 267 entries to 268, and all 48 axioms are as before.

  Within `Certificate/FIELDS.md` the one thing altered is the generated vocabulary count,
  267 becoming 268.

  `model/lock.sha256` is renewed to
  9265a082f7114a20b41ae39690f326a61827250f477e80aad8e8fd99c159e0cb, the new lock's sha256,
  beneath a note of 26 October 2026 saying that the formal model has no law using the word.

  `tests/model/lock.sha256` carries that hash as well, for the numerical harness, beneath
  its own note of 26 October 2026: only the statements of III.20 and of its companion III.20
  circumference reach the word, so the harness changes no law.

  `model/Model/Laws.lean` is the generator's own output again, from `Check/Write.lean`, and
  differs in the single line that names the lock's hash; the model builds afterwards.

  `Audit/Overlaps.lean`, a protected audit file, changes in one call alone: its
  `Audit.III_27_any` names `BookIII.Prop20.special` in place of the old III.20, as the
  coordinator's orders of 25 October 2026 for this move ask, and `lake build Audit` holds
  every pin unchanged.
