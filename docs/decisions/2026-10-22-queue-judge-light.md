- **The queue's judge accepts the light pre-flight of a train of R0 to R2 (tooling).** On
  22 October 2026 the owner approved checks scaled to risk (#292): "we should not be
  spending the same amount of time on high risk and low risk"
  ([2026-10-22-checks-by-risk](2026-10-22-checks-by-risk.md)). Since #329, a change of R0
  to R2 by origin/main's `scripts/risk.py` leaves step 4 of its pre-flight, the full local
  checks, to CI, and its block in the pull request says so: the summary ends "the full
  local checks left to CI, for the class" and names the class, a line "Risk class" names
  it again, and step 4 is two rows, `4. class`, passed, and `4. full local checks`,
  skipped. The queue's judge, `scripts/check_queue.py`, asked every block for every full
  check (rule (b) of the queue), so once the queue was on it would have refused every
  train of R0 to R2. Card #334, part of #209, records the gap.

  The coordinator's ruling, recorded on #334 on 22 October: under the owner's approval of
  checks scaled to risk, the judge accepts the light pre-flight of a train of R0 to R2,
  with CI's checks as the evidence. It is no new loosening, since a merge group's own CI
  run is classed R5, so every check still runs on the group before it merges. The ruling
  is the coordinator's, made under that approval.

  What changed. The judge accepts a block that left the full checks to CI only when
  every one of these holds, and otherwise refuses, saying which failed. The summary's
  class is R0, R1 or R2; the block's one Risk class line, read in any capitals, names
  that same class; and the `LOW_CLASSES` of the harness the block names, read from its
  `scripts/safe_push.py` by `ast`, never run, as the judge reads its `CHECKS` and
  `NEGATIVE`, holds that class, so a block naming a harness from before #329, which
  never wrote one, refuses. The block gives one passing verdict, has no failing row, and
  its step 4 is the row `4. class`, passed, and the row `4. full local checks`, skipped,
  with no other row. Two diffs are classed now by the `scripts/risk.py` of the group's
  base, main, through safe_push's own `risk_class` and with the pull request's labels,
  and each must be R0 to R2: the block's own change, from its base to its head, the diff
  its pre-flight classed; and what the entry's merge brings into the group, from the
  merge's first parent to the merge, as CI's risk job classes the merge commit GitHub
  makes of a pull request. This is the rule of `checks_record` for a record that left
  step 4 to CI, that the class it records and the class recomputed at the merge both be
  R0 to R2; the diffs the judge classes are its own. And neither diff touches a check
  input or a protected path but content the checks judge (`beyond_low`), as safe_push's
  short path itself requires. Every other part of rule (b) holds a light block as
  before: its head, its base, the harness commit and its blob, its visibility and a
  train's body. A block of the full checks is judged as it was, and one saying the full
  checks were skipped by safe_push's internal test flag still refuses. Rule (b) in
  `docs/WORKFLOW.md` now says so.

  Why two diffs. The diff from the group's base to the head, `git diff <base>...<head>`,
  uses only one merge base when criss-cross merges have made several, and commit dates,
  which the author sets, can decide which; so it can miss a change that the group's
  merge brings in. The block's own diff starts at its base, which the head contains, and
  the merge's at its first parent, the group before it, which the merge contains: each
  has one merge base only, and the merge's shows exactly what the entry brings into the
  group, wherever the block's base stands.

  Why main's classifier, not the block's class. The block is a declaration that anyone
  who can edit the body can type, and main's table may have put the change's paths
  higher since its pre-flight ran. `risk_class` reads the classifier out of Git at the
  group's base, never from the group's checkout, so no entry's copy of the classifier
  classes anything, its own or an earlier entry's; a `release` label makes the class R5,
  and so does a base with no classifier, or any failure to compute the class.

  Why this is safe. The judge is not the only evidence. The `risk` job of
  `.github/workflows/ci.yml` classes a merge group's run R5, so `check`, `model`,
  `negative`, `formal-model` and `acceptance` run in full on the group's tree, which
  holds the train, before it merges: the builds, `Facts.lean`, the kernel's self-test and
  the negative tests that the light pre-flight left out among them.

  The queue is still off, and stays off until the owner turns it on, which waits on the
  owner's choice of an authenticated source for the pre-flight's evidence
  (`docs/WORKFLOW.md`, "Turning it on"). This changes only what its judge will accept
  once it is on.

  This entry approves the change to `scripts/check_queue.py`, whose new
  `light_preflight` accepts a light block on the terms above, whose new
  `harness_low_classes` reads a harness's `LOW_CLASSES`, through `harness_tree`, which
  `harness_check_names` now shares, whose `preflight_steps` reads such a block's Risk
  class line and step 4, and whose docstring now gives rule (b) with the light block in
  it.

  This entry approves the change to `scripts/safe_push.py`, whose `risk_class` takes a
  keyword-only `diff_base`: given it, `risk.py` classes `git diff <diff_base>...<sha>`,
  the classifier still read at `base`, and every rule that makes the class R5 holds as
  before; without it, nothing changes.

  This entry approves the change to `tests/test_check_queue.py`, whose planted groups,
  on a main given its own copy of `scripts/risk.py`, pass light blocks of R0, R1 and R2,
  and refuse a block of R3, a block claiming R1 for paths of R3, R4 or R5, a train
  labelled `release`, a main whose classifier is missing, fails or prints no class, a
  check input that a lowered classifier calls R0, a block whose step 4, verdict, failing
  row or Risk class line is not as safe_push writes it, a block naming a harness with no
  `LOW_CLASSES`, or with `LOW_CLASSES` that lack its class or cannot be read, a
  criss-cross head whose diff from the group's base hides a change of R4, and a head
  whose block's base is no merge base, R0 from either base, whose merge brings a change
  of R4 into the group. Its fixture harness now has `LOW_CLASSES`, and a workflow case
  pins the risk job's classing a merge group R5.
