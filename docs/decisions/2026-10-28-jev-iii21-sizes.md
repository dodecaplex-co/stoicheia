- **The Jev generator follows III.21's record to the three sizes of the angle at the centre (#624).**
  III.21's record, read in full again for its route label (#546,
  [its entry](2026-10-28-route-labels-iii20-iii21.md)), now says in a passage at "Now,
  since the angle BFD is at the centre" that the angle at the centre is the angle BFD in
  the greater segment, two right angles in a semicircle and more in a less segment
  (`angleAtCentre.size`), and its route that "III.20 doubles BAD and BED in every
  segment". Its representations item stays `pass`, on the angle at the centre that III.20
  gives it. [The entry that taught the generator the angle](2026-10-26-jev-bundles-angle-at-centre.md)
  gave III.21's row the angle and three of its theorems; this one adds the fourth that the
  record now names.

  `scripts/audit/jev_questions.py` gives III.21's row `angleAtCentre.size` among its
  bridges, and its guard refuses a III.21 row that leaves it out, beside the angle,
  `angleAtCentre.within`, `angleAtCentre.congr` and `angleAtCentre.diameter`. Its comments
  quote the record's new words. `tests/test_jev_questions.py` reads those words in the
  record, pins III.21's bundle with the new bridge, and shows that a row leaving it out is
  refused. The generator sends nothing: it reads no key and makes no request.
