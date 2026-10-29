<!-- entry: id=render-notes-settle cards=677 line="The render-notes test renders its copy once before it writes the entry, so a renderer change is not kept apart for its stale pages." -->
- **The render-notes test renders its copy once before it writes the entry (checks,
  [#677](https://github.com/dodecaplex-co/stoicheia/issues/677)).** The coordinator's
  orders of 29 October 2026, 02:51, assign card #677: "the test renders the copy once
  before the entry is written and compares against that output". The test is
  `RenderFillsTheNotes.test_one_brief_changes_between_its_markers_alone` in
  `tests/test_decision_entries.py`, which came with
  [#577](https://github.com/jackChallis/stoicheia/issues/577) (pull request
  [#651](https://github.com/dodecaplex-co/stoicheia/pull/651)); the file stays its
  ship's, and this train changes that one case and the docstrings that describe it.

  The case copied the sources, wrote a headed entry, ran `render.py` on the copy and
  required every file of it to be byte for byte as before. In the pre-flight's pass with
  origin/main's checks, a commit that changes `render.py` brings the pages its own
  renderer regenerates, and origin/main's renderer writes the old wording back into the
  copy. So the case failed on staleness, which the pre-flight's step 3 and its
  `git status` step already report, and which `keep_apart` passes over there as
  freshness; the negative suite's failure is not passed over, so every renderer change
  that also changed judged content was kept apart at step 4. The shadow run of main's
  policy found it ([#574](https://github.com/dodecaplex-co/stoicheia/issues/574)), in its
  plant `renderer-freshness`.

  Now the case renders the copy once before it writes the entry, and compares what
  follows with that output: it tests what the entry and the planted markers change, not
  whether the pages are current. Staleness is caught where it always was, by the
  generated-pages step and `git status`, and by the negative suite's stale-page plant.
  The other cases that run `render.py` on a copy were read: those of
  `tests/test_generated_counts.py` compare the outputs of a run that refuses before it
  writes, `RenderLeavesTheRecord` compares the decisions record, which holds no
  generated region, and the count-marker plant compares a symlink's target; none depends
  on the pages being current, so none changes.

  This entry approves the change to `tests/test_decision_entries.py`, in
  `RenderFillsTheNotes` and in the file's docstring.
