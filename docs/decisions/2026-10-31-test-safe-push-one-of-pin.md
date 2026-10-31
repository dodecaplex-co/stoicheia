<!-- entry: id=test-safe-push-one-of-pin cards=517 line="The reproof helper moves III.1's counted pin and every state of III.1 Por.'s axioms pin." -->
- **The reproof helper moves III.1's counted pin and every state of III.1 Por.'s axioms
  pin (tooling, [#517](https://github.com/dodecaplex-co/stoicheia/issues/517)).** Commit
  `9044a61d0`, #517's first part, made III.1 Por.'s axioms pin an expectation with
  `one_of`, as recorded in [the pin entry](2026-10-31-517-pin-either.md).
  `reproof()` in `scripts/test_safe_push.py` sought a counted pin at the top level alone,
  so `ProtectedPaths.test_pinned_values_move_with_their_content` and
  `ProtectedPaths.test_pinned_values_with_check_code_kept_apart` raised `StopIteration`.

  The helper now moves the count and the list inside each state of a `one_of` pin, just
  as for a counted pin. III.1's counted path stays as it was. Every state must contain a
  counted axioms pin, and each ref must have a pin changed; a pin of neither shape fails
  with an assertion. No other test changes, and no check code changes.

  Asked "May I fix main's test_safe_push.py for 517-1's new pin format? It's a protected
  path, and RT700, the fourth part, can't land without it.", the owner replied on
  31 October 2026: "Both yes."

  This entry approves the change to `scripts/test_safe_push.py`: `reproof()` updates
  counted axioms expectations both at the top level and within every `one_of` state,
  asserting that each state and each ref has a counted pin to move.

  What this does not settle: `kept_expectations` in `scripts/safe_push.py` decides whether
  an expectations change is a pinned value that moves with its content. It compares an
  expectation with `one_of` as a whole, so a re-proof moving the count inside III.1 Por.'s
  states is not yet read as a pinned value.
  `ProtectedPaths.test_pinned_values_move_with_their_content` now reaches that assertion
  rather than erroring. Changing `kept_expectations` is a separate protected change for
  the owner.
