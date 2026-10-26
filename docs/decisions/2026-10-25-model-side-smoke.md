- **The numerical check of superposition's kept side called a construction smoke test
  (model, [#150](https://github.com/jackChallis/stoicheia/issues/150), question 5).** The
  coordinator's orders of 25 October 2026 take the optional item of card #150 headed "A
  side check that can fail", which offers two options, by its second: to call the side
  check a construction smoke test where the model harness's page describes it. Both
  samplers of superposition, the Euclidean search and the hyperbolic one, build the kept
  side, the straight line through `D` and the placed third corner `C'`, from those two
  points, and check that `D ≠ C'` and that both lie on it. That check cannot fail on its
  own: the line is computed from the two points, and `D ≠ C'` already follows from the
  check that `C'` is strictly on `H`'s side of `L`, since `D` is on `L`. No mutation in
  `tests/model/mutations.py` targets it; the one mutation on superposition, M9, drops the
  triangle hypothesis.

  In scratch copies of the two samplers, never committed, with the side's conjuncts
  counted apart and superposition run alone, the side was reached with every other check
  of the placement passing 33 and 28 times in the Euclidean search (20,000 samples, seeds
  1 and 2) and 857 and 860 times in the hyperbolic one (2,000 samples, seeds 1 and 2),
  and it failed none of them; the committed runs, with every rule, reach it 34 and 35
  times and 8,691 times, with no counterexample.

  So the page now says so: in the superposition row of its table of why each rule holds,
  and in its paragraph on the hyperbolic plane. No harness code, law, mutation, count,
  count marker or result changes, and no other claim on the page. The first option, a new
  mutation that only the side check would catch, which would raise the pinned count of
  mutations, is not taken here.

  This entry approves the change to `tests/model/MODEL.md`, which now calls the harness's
  check of the kept side a construction smoke test, in the superposition row and in the
  hyperbolic paragraph, and changes nothing else; the same row's naming of
  `Rule.of_placement_of_join` is approved by
  [the entry on the side laid down](2026-10-25-superposition-side-cost.md).
