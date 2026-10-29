- **The Jev generator knows Lean's four names for choice that III.26's helpers use (checks,
  [#656](https://github.com/dodecaplex-co/stoicheia/issues/656)).** Two helpers of III.26's
  subtraction route (#547), `Prop26.radial_extension` and `Prop26.extend_places`, build a
  function on points (the radial extension `g`, the inverse `k`) from a proof that each
  image exists, so they need choice by their nature. They write four of Lean's own names
  that the generator's closed lists did not hold: `choose` and `choose_spec`, as fields of
  that proof, and `Classical.epsilon` and `True.intro`, whole. With them unknown,
  `tests/test_jev_questions.py` stops at III.26 with "unresolved names". On 28 October
  2026, at 19:04, the coordinator ruled that the generator's closed allowlist is a check
  input, widened only in a check train of its own; issue #656 is the coordinator's record
  of it. This is that train, and it adds those four names and no others.

  In `scripts/audit/jev_questions.py`, `Calls.CORE_FIELDS` gains `choose` and
  `choose_spec`, beside `epsilon_spec`, and `Calls.CORE_NAMES` gains `Classical.epsilon`
  and `True.intro`, beside `And.intro`; the docstring that lists both gives the four. As
  for every word of `CORE_FIELDS`, `choose` and `choose_spec` are exempt only where no
  declaration of the project is a candidate for the field, so a project theorem of either
  name is still collected; and as for every name of `CORE_NAMES`, `Classical.epsilon` and
  `True.intro` are exempt only written whole, from a first word that names no declaration
  of the project.

  The decisions page's entry of 21 October on the generator's parser of the module header
  had the coordinator rule that adding a name which really is a Lean core lemma is upkeep
  of the list, provided each is shown to be core. The four are Lean's own declarations, if
  not all of them lemmas: the toolchain's `lean` (4.35.0, commit `eb6cafb7`), with no
  Mathlib and no project import, on a scratch file outside the repository holding
  `#check @Exists.choose`, `#check @Exists.choose_spec`, `#check @Classical.epsilon` and
  `#check @True.intro`, prints

  ```
  @Exists.choose : {α : Sort u_1} → {p : α → Prop} → (∃ a, p a) → α
  @Exists.choose_spec : ∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.choose
  @Classical.epsilon : {α : Sort u_1} → [h : Nonempty α] → (α → Prop) → α
  True.intro : True
  ```

  `tests/test_jev_questions.py` gains two cases in `CoreNames`. In the first, each of the
  four names, written alone as III.26 writes it, resolves; each of its four parts fails on
  the generator before this change. In the second, six names outside the list are still
  unresolved: `Classical.choice` and `Classical.indefiniteDescription`, Lean's other names
  for choice, and `Missing.epsilon`, `True.epsilon`, `Classical.intro` and
  `Missing.True.intro`, the two whole names' words in other places. The generator sends
  nothing: it reads no key and makes no request.
