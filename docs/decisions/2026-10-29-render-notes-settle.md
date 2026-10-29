<!-- entry: id=render-notes-settle cards=677 line="The render-notes test and the stale-page plant render once before they plant, so a renderer change is not kept apart for its stale pages." -->
- **The render-notes test and the stale-page plant render once before they plant
  (checks, [#677](https://github.com/dodecaplex-co/stoicheia/issues/677)).** The
  coordinator's orders of 29 October 2026, 02:51, assign card #677: "the test renders the
  copy once before the entry is written and compares against that output. Do the same for
  any other test that renders a copy and requires no change, in that file or elsewhere."
  The test is `RenderFillsTheNotes.test_one_brief_changes_between_its_markers_alone` in
  `tests/test_decision_entries.py`; the case came with
  [#577](https://github.com/dodecaplex-co/stoicheia/issues/577), which ship RT landed as
  pull request [#651](https://github.com/dodecaplex-co/stoicheia/pull/651), and the file
  stays ship RT's. This train changes that one case, the docstrings that describe it, and
  the negative suite's stale-page plant, `scripts/negative/stale_page.py`.

  The case copied the sources, wrote a headed entry, ran `render.py` on the copy and
  required every file of it to be byte for byte as before. In the pre-flight's pass with
  origin/main's checks, a commit that changes `render.py` brings the pages its own
  renderer regenerates, and origin/main's renderer writes the old wording back into the
  copy. So the case failed on staleness, which the pre-flight's step 3 and its
  `git status` step already report, and which `keep_apart` passes over there as
  freshness; the negative suite's failure is not passed over, so every renderer change
  that altered a committed page and also changed judged content was kept apart at step 4.
  The shadow run of main's policy found it
  ([#574](https://github.com/dodecaplex-co/stoicheia/issues/574)), in its plant
  `renderer-freshness`. The stale-page plant has the same fault: it rendered the worktree
  and required `git status` to be the status before any render with the planted page and
  its source beside it, so origin/main's renderer added the commit's own regenerated
  pages to that status. The suite stops at its first failing regression and runs no plant
  after it, so the shadow run showed the case alone.

  Now each renders once before it plants, and compares what follows with that output: the
  case tests what the entry and the planted markers change, and the plant that `git status`
  names a page made stale beside its changed source, not whether the committed pages are
  current. The plant still restores every generated output and requires the worktree to
  return to its entry status. A stale committed page is caught where it always was: by
  the pre-flight's step 3, "generated pages", by the check sequence's `render.py` and
  `git status --porcelain is empty`, and by CI's check job, which runs the same. The other
  cases that run `render.py` on a copy or the tree were read: in
  `tests/test_generated_counts.py`, three compare the outputs of a run that refuses before
  it writes, one compares a page with the running renderer's own output, and one compares
  no file; `RenderLeavesTheRecord` compares the decisions record, which holds no generated
  region; the count-marker plant compares a symlink's target; the cases of
  `scripts/test_safe_push.py` render a fixture of their own. None depends on the committed
  pages being current, so none changes.

  This entry approves the change to `tests/test_decision_entries.py`, in
  `RenderFillsTheNotes` and in the file's docstring.
  This entry approves the change to `scripts/negative/stale_page.py`, in its plant and its
  docstrings.
