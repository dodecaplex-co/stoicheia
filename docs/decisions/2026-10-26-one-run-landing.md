- **`git safe-push --land` pushes, follows CI and merges in one run, the merge's step 4
  taken from the pre-flight's record kept in memory (landing,
  [#557](https://github.com/jackChallis/stoicheia/issues/557)).** A heavy landing, of
  class R3 to R5, ran its full local checks twice: in the pre-flight, and again in
  `--merge`, which never lets the pre-flight's record stand in for step 4 when the head
  changes the checks or a protected path. That record is a file, and the head's own code
  ran during its pre-flight, so a forged record could let a change to the checks skip
  origin/main's checks, which CI never runs on it. #557 measured what the second run
  costs: in each of the 31 heavy merges since 18 October that took over ten minutes, the
  head, origin/main and the harness were all as they had been at the push, and every one
  of those heads changed the checks or a protected path; about 17 hours of lane time went
  to running the same checks again.

  On 26 October 2026 the owner chose, of the options put to them, "One run"
  ([#557](https://github.com/jackChallis/stoicheia/issues/557) is the coordinator's record
  of it). Standing order 12(a), which keeps new guards and tests out of the landing tool
  and its tests until about 29 October, is waived for this change alone.

  What changes. The pre-flight takes a new option, `--land`, given with `--branch` and
  `--ready`, since nothing comes between the push and the merge: the pull request must be
  ready, and its body final, at the push. The parser refuses `--land` unless both are
  given, and with `--dry-run` or `--merge`; only the command line sets it. Once CI is
  green on the commit pushed and no step failed, the same process prints the push's
  summary and goes on to the merge of that pull request, as `--merge` runs it. The record
  the pre-flight makes is copied in memory at once, before it is saved, and the merge
  takes that copy as the earlier record: on this path it never loads a record from the
  disk, whatever the disk holds. The rule that refuses a record for a head changing the
  checks or a protected path is skipped for that copy alone: it was never a file, so
  nothing the head's code ran could have written it. The record is still saved to the
  disk by the pre-flight and by the merge, as before. The merge's step 3 says when its
  step 4 came from memory.

  When the copy stands in. Only while the head GitHub has for the pull request is the
  commit pushed; a fresh `git fetch origin`, made by the merge's preconditions, shows
  origin/main where it stood at the push; origin/main's pass of step 4 in the pre-flight
  was not taken from the main-checks cache; and `checks_record` accepts the copy, as it
  would accept a file's (made by the harness running now, of step 4 in full, every step
  of it passed). Otherwise step 4 runs again by the class, the full checks for R3 to R5,
  as for a separate `--merge`, and a step line says why the copy stands in for nothing.

  Five choices are the stricter of those open. A head moved during CI is refused, never
  checked again in its place: the run merges only the commit it pushed, and says to run
  the pre-flight on the new head. The merge's fresh fetch must be of the origin whose URL
  git gave the pre-flight before any of the commit's code ran: that code could point the
  clone's origin at a copy where main is never seen to move, so a URL changed since is
  refused. A hit in the main-checks cache lets the copy stand in
  for nothing, since the hit replays steps from an entry, a file. Today a hit never
  reaches a merge's step 4 either: the cache serves only a head that changes a check
  input, whose record a separate `--merge` never lets stand in. The merge of `--land`
  itself takes no cache, as a separate `--merge` takes none, and runs outside the cache's
  sandbox. When origin/main's harness is no longer the one the run started with, the
  merge's harness does not hand over to it, as a run's harness otherwise does, for the
  hand-over would run the push's arguments, and so the whole push, again: the merge is
  refused, and a separate `--merge` then runs the new main's harness; so too when
  origin/main's harness predates running from origin/main, which a separate `--merge`
  would let the checkout's copy run. And a merge refused after the push exits 3, "pushed,
  but", where a separate `--merge` refused exits 1, since the branch is on origin; so does
  a merge that stops on an error of the harness's own, with a word to look at the pull
  request before anything else, since it may have merged. When CI fails, nothing more is done, and the run exits
  3, as a push does today; the lane's retry falls back to a separate `--merge`.

  What does not change. A separate `--merge` keeps its rule, line for line: for a head
  that changes the checks or a protected path, it runs the full checks again, whatever
  record it finds. In the merge of `--land` every other step runs as in `--merge`: the
  gates; the secret scan and the guards on the head, run again; the train check; the
  release's need of a full record, judged before the checks and again after the gates
  (`release_needs_full_record`); the labels and the body, read again; the train's body,
  compared; the last look at main and main's health; and the check, after the merge, that
  the merge commit joins the base and the head checked, with the head's tree.

  The tests. The stand-in for gh in the landing tool's tests gains four things it does
  once each while CI is followed: it moves origin's main, moves the pull request's branch,
  writes files, or runs git commands in the clone. A new class, `Land`, holds eleven
  tests: a head that changes the checks
  lands in one run, step 4 taken from memory and never run again at the merge; origin/main
  moving during CI to a commit the head holds runs the full checks, and the body's
  summary, of the old main, then refuses the merge, as it refuses a separate `--merge`,
  while a move to a commit the head lacks is refused by the merge's preconditions; a head
  moved during CI is refused; origin's URL changed during CI is refused; a harness changed during CI is refused, with no hand-over
  and no second push; a forged record on disk changes nothing, neither one that would
  stand in for nothing nor one, written for a main moved during CI, that a separate
  `--merge` does let stand in, as the test then shows; a separate `--merge` still runs
  the full checks again for a head that changes the checks; the parser's rules; CI
  failing merges nothing; a cache hit lets the copy stand in for nothing, shown by calling
  the merge in the test's own process with what `--land` would hand it, since the cache
  needs step 4 in full, which the internal test flag skips; and the cache's lookup marks a
  hit in memory, and a miss not. In a scratch run with the merge loading the record from
  the disk in place of the copy, the first of these and the test of a forged record
  failed. Two tests of the class `HandOver` make a copy of the harness that never hands
  over by rewriting the line that defines `harness`; they now look for that line as it
  reads with its new keyword, and rewrite it to the same effect as before.

  The card's other items stay with the lane: its `ship_land.sh` taking the option, with
  `land.sh` kept as the fallback and tried first on a planted train, and the measure, after
  five heavy landings, that the median merge step is under five minutes and that nothing
  merged which a separate `--merge` would have refused.

  This entry approves the change to `scripts/safe_push.py` that brings the option `--land`
  and its rules in the parser; the class `Held` and the function `held_record`; the
  keyword `hand_over` of `harness` and `merge_preconditions`; the checks of the head and
  of origin's URL at the merge of `--land`; the exit 3 for a merge that stops after the
  push; the path of `merge_main` that
  takes the copy, and its step-3 lines; the flag `CACHE_HIT`, set where `main_checks`
  reports a hit; and the docstring, usage text and help that describe them.

  Approved here as well is the change to `scripts/test_safe_push.py`, whose stand-in for gh
  gains the four actions above, each documented beside its others, which gains the class
  `Land` and its eleven tests, and in whose two tests of `HandOver` the line that defines
  `harness` is looked for, and rewritten, as it now reads.

  Approved here too is the one change to the launcher, `scripts/hooks/safe-push`, whose
  usage comment now names `--land` on its `--branch` line; nothing else in it changes.
