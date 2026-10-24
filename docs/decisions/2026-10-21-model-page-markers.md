- **MODEL.md's count markers stand, as the other check inputs' do
  ([#187](https://github.com/jackChallis/stoicheia/issues/187)).** `scripts/safe_push.py`
  pinned [`tests/model/MODEL.md`](../../tests/model/MODEL.md) whole: the page is the
  model's account of its laws and moves with them, so `pinned` counted any change to it as
  a value pinned to the edition. Since #177 it also carries count markers that
  `scripts/check_fidelity.py` reads, so a pull request could add, remove or rename one of
  them together with judged content while origin/main's checks failed, where in the
  Markdown of every other check input only a marker's value may move (the entry of 20
  October on #177). On 21 October 2026 the owner chose, of two options put to them, "Yes,
  tighten it": MODEL.md's count markers are held to the rule for the other check inputs,
  so that only a marker's value may move, never the marker itself together with content
  (the coordinator's record of the choice is on #187). The page keeps
  its pin for its prose, but a change to it is now a pinned value only while the same
  markers stand, by name and in order, as origin/main's `scripts/generated_counts.py`
  reads them, the file stays a regular file of the same mode, and both sides read.
  `counts_moved`, which already read the markers of that Markdown, compares the page's
  marker names alone, in order, and `pinned` asks it for the page. A marker added,
  removed, renamed or reordered, the file added or deleted, its mode changed, or a side that does not read, is
  no pinned value, so `keep_apart` refuses it as a check change when origin/main's checks
  fail, and its refusal says so: "it adds, removes, renames or reorders a count marker of
  tests/model/MODEL.md". A renamed or reordered marker is the case that matters: the commit's own
  `check_fidelity.py` checks each value against the marker that holds it, so a count of
  the axioms renamed to a count of the tacit rules, its value moved to match, would pass
  that check and leave the page miscounting the axioms. The guard holds the markers, not
  the sentences around them: the page's prose still moves with its laws, so a sentence
  reworded to put a standing count beside the wrong noun is a pinned value, as before,
  for the security review to read. This is a tightening, not a
  weakening: it lets through nothing that was refused before, and refuses what was let
  through. The module docstring, the comments on the pinned values, the docstrings of
  `counts_moved`, `pinned` and `keep_apart`, and the refusal's list of pinned values say
  so, and [WORKFLOW](../WORKFLOW.md), section 10, step 4, gives the rule beside its
  sentence on counts in the other check inputs. `scripts/test_safe_push.py` gains two
  tests beside the count tests. In the first, an axiom added with its law moves MODEL.md's
  account and its counts of the axioms, with a sentence around a marker reworded as well;
  the page is a pinned value, and the change lands as content. In the second, the same
  change with a marker added, removed, renamed, reordered or left unclosed, or the page
  deleted or made executable, is no pinned value, and is kept apart with that refusal. Against
  origin/main's `safe_push.py` (`e7ffaf68`) the first passes and each of the second's seven
  cases fails, the page counted as a pinned value; with this change both pass. No negative
  plant is added, as for #177: the harness's regressions are in its own suite. Nothing
  else states the rule. CI's `acceptance` job, [ACCEPTANCE](../ACCEPTANCE.md) and
  `tests/test_check_acceptance.py` keep main's own MODEL.md, among main's pinned values,
  when main is checked beside a pull request; that is another matter, and is unchanged.
  The decisions page's entry of 20 October that says MODEL.md stays pinned whole is true
  of its date. The protected files changed are `scripts/safe_push.py` and
  `scripts/test_safe_push.py`; `docs/WORKFLOW.md` changes too, and is not protected.
  This entry approves the change to `tests/test_check_train.py`, whose fixture's base
  gains main's reader of count markers, `scripts/generated_counts.py`: the train checker
  of [#383](https://github.com/jackChallis/stoicheia/pull/383) reads the model's page as
  a pinned value by `pinned`, which under this entry's rule asks that reader whether the
  page's markers stand, and with no reader pins nothing, so its test of a page moving with
  content needs the reader there.
