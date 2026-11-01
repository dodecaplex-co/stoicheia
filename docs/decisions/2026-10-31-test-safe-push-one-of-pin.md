<!-- entry: id=test-safe-push-one-of-pin cards=517 line="A re-proof moves a one_of pin's counts with its content, like a counted pin's, in safe_push's pinned values and the test helper." -->
- **A re-proof moves a one_of pin's counts with its content, like a counted pin's, in
  safe_push's pinned values and the test helper.**
  Tooling for [#517](https://github.com/dodecaplex-co/stoicheia/issues/517).
  In `9044a61d0`, #517's first part, the porism of III.1 acquired two alternative axioms
  expectations under `one_of` ([the decision](2026-10-31-517-pin-either.md)). The test
  helper `reproof()` expected a top-level counted pin instead.
  `ProtectedPaths.test_pinned_values_move_with_their_content` and
  `ProtectedPaths.test_pinned_values_with_check_code_kept_apart` both stopped with
  `StopIteration`. Once the helper handled both shapes, the former test still failed:
  `kept_expectations` compared the entire `one_of` value without allowing its counts or
  exact lists to move. It therefore withheld pinned-value status, and `keep_apart`
  refused the change as one that "drops or loosens an expectation". A re-proof of III.1
  dropping a tacit rule could land in no order while its porism retained this pin shape.

  `kept_expectations` now matches the alternatives by state name. Both sides must be
  lists of state dictionaries with expectations lists; malformed shapes return false.
  The new names must be distinct and must name exactly the old set: adding a state
  would widen the choice. Within each named state, expectations retain their order,
  number and keys. Only `count.is`, `equals` and the words of `why` may vary; the other
  count keys and values stay fixed. Inclusion and exclusion lists stay fixed, and no
  expectation may be added.
  Exactly one state must hold, so tightening one state can loosen the choice. Both
  reviewers found this fault in the first comparison, with thanks: a tree naming both
  `Tacit.a` and `Tacit.b` fails alternatives that separately require those names, but
  passes after the second alternative also excludes `Tacit.a`.

  The helper `reproof()` traverses each alternative's counted axioms expectations,
  subtracts one from their counts and removes `Tacit.line_unique` from exact lists when
  present. It checks the `Tacit.` prefix, requires that name before removal, and asserts
  that every state and each of the two refs has a counted pin changed. Its top-level
  counted-pin path remains available for III.1.

  A synthetic fixture in `Units.test_an_expectation_with_one_of_is_kept_by_its_states`
  keeps this regression independent of the live certificate expectations. Its refusal
  table covers a state dropped, added or renamed; exclusions emptied or grown; an
  includes key added; a count removed or its prefix changed; a state's expectations
  emptied or added to; and the alternatives replaced by one ordinary expectation.
  A separate fixture refuses the reviewers' change that lets a tree holding both states
  pass. Its acceptance table covers unchanged data, both states' counts and exact lists
  moving after removal of `Tacit.line_unique`, and the `one_of`'s `why` reworded.
  WORKFLOW section 10, "Landing work: pull requests", describes alternative pins.

  Asked "May I fix main's test_safe_push.py for 517-1's new pin format? It's a protected
  path, and RT700, the fourth part, can't land without it.", the owner answered on
  31 October 2026: "Both yes."

  Asked "Option 1 (my recommendation): extend kept_expectations so a one_of pin's counts
  move with a re-proof, as counted pins already do. The state names must stay the same,
  and nothing else may change. It's a protected change to the gate's code.", the owner
  answered on 31 October 2026: "Yes option 1".

  This entry approves the change to `scripts/safe_push.py`: distinct state names remain
  fixed, with their expectations paired in order and unchanged in number and keys;
  only the values of `count.is` and `equals`, and `why`'s words, may move.

  This entry approves the change to `scripts/test_safe_push.py`: the helper's traversal
  of counted pins both directly and within alternatives, with assertions on every state
  and ref, and the synthetic Units test's refusal and acceptance tables described here.

  The clause added to `docs/WORKFLOW.md` section 10, "Landing work: pull requests", is
  approved here: alternative pins keep their named states and ordered expectations,
  allowing only `count.is` and `equals` values to change, with no additions or list growth.

  #517's final part restores a single axioms list. Replacing alternatives with one
  ordinary expectation is not kept by this rule; that narrowing is a check change of
  its own.
  A value moved in a state that does not hold is checked by nothing until that state
  holds, since the commit's own pass reads only the state that holds; neither `one_of`
  on main can gain by this: I.4's states are separated by fixed `includes` and `excludes`,
  while III.1 Por.'s differ only in `equals`, which a counted pin could already move.
