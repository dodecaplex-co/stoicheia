- **The test of the superposition pins compares the audit file's `#check` pins with brief
  0009's list, name for name, where it counted 17 (checks,
  [#150](https://github.com/jackChallis/stoicheia/issues/150)).** The coordinator's orders
  of 26 October 2026 assign and approve this change. Since the statement-pins train of 21
  October ([its entry](2026-10-21-superposition-statement-pins.md)), a test of
  `scripts/check_superposition_pins.py` has counted the `#check` pins of
  `Audit/Superposition.lean` and held them to 17. Train B adds one,
  `Rule.of_placement_of_join`, with its line in brief 0009's section "The restriction
  theorem". It could not land with the count changed to 18, since a change to a check is
  kept apart from the content it judges; nor could the count change first, since 18 would
  fail on main, which holds 17. So the count becomes an exact list, read from the brief.

  The test now takes the names the section writes, read with the script's own readers, less
  the two definitions pinned by `#print`, `Rule.Figure` and `Interpretation.Embedding`, and
  adds the three theorems pinned outside the section, `Cited.holds_all`, `Derives.sound`
  and `Rule.apply`. On main the section writes 16 distinct names, `Rule.of_placement`
  twice, so the list holds 14 theorems from it and the three besides, 17 in all. The test
  sorts that list, and the names of the `#check` pins the script's reader finds in the
  audit file, each as often as it is pinned, and requires the two to be equal. A repeated
  pin still fails, since the comparison is of sorted lists and not of sets. Copies of the
  real file show the comparison failing, by the names concerned, for a pin removed, one of
  an invented name, one renamed, one commented out and one repeated; the count alone let
  the renamed pin pass, since it kept the number at 17.

  The coordinator's reasoning and approval, in their orders: "An exact set is at least as
  strict as a count: a missing, extra, renamed or wrongly counted pin still fails. The one
  case a count also caught, a new pin with a matching brief line, now needs a change to
  brief 0009, which is mine to approve. So this is not a weakening, and it is my call to
  make."

  This entry approves the change to `tests/test_check_superposition_pins.py`, where the
  count of the audit file's `#check` pins becomes an exact comparison with the names brief
  0009's restriction section lists, less the two definitions pinned by `#print`, plus the
  three theorems pinned outside it.

  No Lean file, statement, definition, lock, record, check script or `--` line changes.
