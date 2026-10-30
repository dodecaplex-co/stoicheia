<!-- entry: id=single-parts-with-cards cards=283 line="Work lands one part at a time, each with a record of the checks run on it, starting with dated reports and decision entries." -->
- **Single parts, each with a record of its checks (landing,
  [#283](https://github.com/dodecaplex-co/stoicheia/issues/283)).** The owner decided on 30
  October 2026 that work lands one part at a time: the files of one sort of work, such as
  a report, a commentary, a figure, a proof or a tool, never several sorts batched
  together. A decision entry travels with the part it records; an entry that records no
  other change, as this one does, is a part on its own.

  Each part carries a record of what it is, the commit of main it was made on, and the
  checks run on it with their verdicts. In this first version that record is the pull
  request's own template with the pre-flight's summary. The full local checks, step 4 of
  the pre-flight, run once: on the yard VM, through `scripts/safe_push.py --dry-run
  --emit-proof`, for a change that needs them before it is pushed, the landing taking them
  from that proof (`--land --preflight-proof`, as decided on 29 October 2026); or in CI, for
  a change of class R0 to R2, whose pre-flight leaves them to CI. The preconditions, the
  secret scan and the guards still run on the yard VM and again at the landing, and CI
  still runs again on main after each merge; later changes are to remove both repeats. The
  reviews, `/code-review` and `/no-mistakes`, run once, by the part's writer, and their
  results travel with it in the pull request.

  The first parts are dated reports and decision entries, in `docs/reports/` and
  `docs/decisions/`: they hold no generated regions, few other documents link to them, and
  each has one writer. Other sorts of part follow one at a time, each once the sort before
  it has landed end to end. The guides, README.md and PROGRAM.md come after their generated
  and hand-written parts are separated
  ([#695](https://github.com/dodecaplex-co/stoicheia/issues/695),
  [#723](https://github.com/dodecaplex-co/stoicheia/issues/723)), and the hand edits of
  those three files become a stream of their own then
  ([#694](https://github.com/dodecaplex-co/stoicheia/issues/694)). Until WORKFLOW.md is in
  sections, its account of landing is the older one, and where the two differ this entry
  is the rule.

  Work is pulled, not pushed. Each writer holds at most two parts in progress, and starts
  another only when the landing can take it. Two stops are to come with the records: a part
  still being written when parts of its sort have usually landed, at the 80th percentile of
  their times, is to be split, given a second writer, or escalated for a decision; and a
  part whose checks fail is to stop its writer from starting another until it passes. The
  aim is delivery that can be predicted, with little variation, and problems stopped as
  early and as cheaply as they can be.

  Why: the same checks were run several times on one change, at the yard, again before
  the push, in CI and again on main after the merge; changes waited their turn in one queue
  behind larger ones; and many landings carried several sorts of work together, so that a
  fault in one held up the rest.
