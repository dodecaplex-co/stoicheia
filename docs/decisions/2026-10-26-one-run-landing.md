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
  summary and goes on to the merge of that pull request, as `--merge` runs it. With
  `--land`, the record the pre-flight makes is copied in memory at once, before it is
  saved, and the merge takes that copy as the earlier record: on this path it never loads
  a record from the disk, whatever the disk holds. The rule that refuses a record for a
  head changing the checks or a protected path is skipped for that copy alone: it was
  never a file, so nothing the head's code ran could have written it. The record is still
  saved to the disk by the pre-flight and by the merge, as before. The merge's step 3 says
  when its step 4 came from memory.

  What the merge refuses, merging nothing; each is the stricter of the choices open. A
  head GitHub has for the pull request that is not the commit pushed: the run merges only
  what it pushed, and says to run the pre-flight on the new head. An origin whose URL, as
  git gives it (`insteadOf` expanded), is not the one git gave the pre-flight before any
  of the commit's code ran, since that code could point the clone's origin at a copy where
  main is never seen to move; it is compared before the merge fetches anything. Only the
  URL is compared: settings that redirect a fetch with the URL unchanged
  (`core.sshCommand`, `http.proxy`, `include.path` and the like) are no more checked here
  than for a separate `--merge`, a gap older than this change, noted for a card of its
  own. origin/main moved during CI, refused as soon as the merge's fetch shows it, before
  origin/main's harness is compared or anything is judged against the new main; the
  refusal says to run the pre-flight again against the new main, then `--merge` (in a
  merge queue, `--merge` alone). The card asked that the full checks run in this case;
  refusing is the stricter choice, for these reasons. Run on,
  the full checks would take about 36 minutes, and then the body's summary, of the old
  main, refuses the merge, or the merge's preconditions refuse it for a main the head
  lacks; and the harness would be compared with the copy on disk, which code left running
  by the commit could rewrite to match the new main's, so that a superseded harness, in
  memory, would run the merge. Outside a merge queue nothing that would have merged is
  refused. In queue mode the fetched tip is the main compared as well, so the same refusal
  holds there; but a queued head is checked against the base it holds, so a moved main
  that a separate `--merge` would check in full and enqueue now waits for that `--merge`.
  And a copy of the harness on disk that no longer matches origin/main's: with main
  unmoved, it was rewritten since the run started, or origin/main's predates running from
  origin/main. The merge's harness hands over to no other copy, as a run's harness
  otherwise does, for the hand-over would run the push's arguments, and so the whole push,
  again; a run that was itself handed over is refused the same way, before
  `STOICHEIA_HARNESS` is read. A separate `--merge` then runs as it always has.

  What holds the merge. When a head changes the checks, a failure of origin/main's copies
  of them is a note, not a failure, and WORKFLOW sends it to the security review: a
  check's failure at step 3 or 4 that `keep_apart` reads (its name ends in
  "(origin/main's checks)", and it is not one of the two that show only stale pages), or
  the "pinned values" note `keep_apart` writes when it lets such a failure pass. With
  `--land` the body is final at the push and the merge follows at once, so no review would
  read the note first. So when the pre-flight's report holds one, the run merges nothing:
  after the push's summary it says that CI is green but the pre-flight noted origin/main's
  checks failing on the head, names the notes, and says to record the security review
  before a separate `--merge`. `keep_apart` and this rule read the failures through one
  function, `base_pass_failures`, so the two cannot drift apart. The hold exits 3, as a
  failed CI does, so a lane that falls back to a separate `--merge` when CI fails must
  stop on the hold instead, and never fall back on it: the line "CI is green, but the
  pre-flight noted" marks it.

  When the copy stands in. Otherwise the copy stands in for step 4 only while
  origin/main's pass of step 4 in the pre-flight was not taken from the main-checks cache,
  and `checks_record` accepts it, as it would accept a file's: made by the harness running
  now, and either of step 4 in full, every step of it passed, or, for a change still of R0
  to R2, of a pre-flight that left step 4 to CI. `held_record` holds the copy as well to
  the head and the base the merge checks, which backs up the refusal of a moved head. Else
  step 4 runs again by the class, the full checks for R3 to R5, as for a separate
  `--merge`, and a step line says why the copy stands in for nothing. A hit in the
  main-checks cache lets the copy stand in for nothing, since the hit replays steps from
  an entry, a file. Today a hit never reaches a merge's step 4 either: the cache serves
  only a head that changes a check input, whose record a separate `--merge` never lets
  stand in. The merge of `--land` itself takes no cache, as a separate `--merge` takes
  none, and runs outside the cache's sandbox.

  The exit status. Once it has pushed, a run with `--land` that does not merge exits 3,
  "pushed, but", where a separate `--merge` refused exits 1, since the branch is on
  origin: when CI fails, as a push does today, and the lane's retry falls back to a
  separate `--merge`; when the merge is refused; when it is held for the security review;
  and when the run is interrupted, or stops on an error of the harness's own, anywhere
  from the push's summary to the merge's end. An error once the merge has started, or an
  interruption once `gh pr merge` has been asked, says that it may have merged, and to
  look at the pull request before anything else; an interruption before then says that
  the run was interrupted, and nothing is merged.

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
  writes files, or runs git commands in the clone. The driver that runs the harness with
  some of its functions wrapped gains six actions: it marks a cache hit before CI is
  followed, leaves a cache and its sandbox set after it, plants a note in the pre-flight's
  report once its checks are done, crashes or interrupts the merge's first step, and
  interrupts a run's summary, the push's or the merge's. A new class, `Land`, holds
  eighteen tests. A head that changes the checks lands in one run, step 4 taken from
  memory and never run again at the merge, while the scan and the guards run again; a
  head of R0 lands in one run, its short record standing in. origin/main moving during CI
  is refused once fetched, before the harness is compared, whether the head holds the new
  main or lacks it. A head moved during CI is refused. origin's URL changed during CI is
  refused before any fetch, the clone's origin/main left where it was. A harness changed
  during CI is refused, with no hand-over and no second push: on a main moved to it, as a
  moved main; and, with main unmoved, when the copy that runs is rewritten on disk, in a
  run handed over too. A forged record on disk changes nothing: with main unmoved, one
  that `checks_record` would accept, written during CI where a separate `--merge` would
  read it, is never read, and the record kept in memory stands in; one that would stand
  in for nothing changes nothing either; and one written for a main moved during CI,
  which a separate `--merge` then does let stand in, as the test shows, is never reached.
  A separate `--merge` still runs the full checks again for a head that changes the
  checks. The parser's rules hold. CI
  failing merges nothing. A cache hit lets the copy stand in for nothing, shown by calling
  the merge in the test's own process with what `--land` would hand it, since the cache
  needs step 4 in full, which the internal test flag skips; the cache's lookup marks a hit
  in memory, and a miss not; and a hit so marked during the run reaches the merge. The
  merge runs with no cache and no sandbox, though both were left set during CI. A merge
  crashed or interrupted after the push exits 3, at its first step and in its summary, as
  does a run interrupted in the push's summary. A note for the security review holds the
  merge, of either kind; and the notes that hold it are those `keep_apart` reads. Two
  tests of the class `HandOver` make a copy of the harness that never hands over by
  rewriting the line that defines `harness`; they now look for that line as it reads with
  its new keyword, and rewrite it to the same effect as before.

  The card's other items stay with the lane: its `ship_land.sh` taking the option, with
  `land.sh` kept as the fallback and tried first on a planted train, and the measure,
  after five heavy landings, that the median merge step is under five minutes and that
  nothing merged which a separate `--merge` would have refused.

  This entry approves the change to `scripts/safe_push.py` that brings the option `--land`
  and its rules in the parser; the class `Held` and the function `held_record`; the
  keyword `hand_over` of `harness`, and the keyword `held` of `merge_preconditions` with
  its refusals of a changed URL and a moved main; the refusal of a moved head at the merge
  of `--land`; the functions `base_pass_failures`, which `keep_apart` now reads, and
  `review_notes`, with the hold for the security review; the exit 3 for a run that pushed
  and then does not merge; the path of `merge_main` that takes the copy, and its step-3
  lines; the flag `CACHE_HIT`, set where `main_checks` reports a hit; and the docstring,
  usage text and help that describe them.

  Approved here as well is the change to `scripts/test_safe_push.py`, whose stand-in for
  gh gains the four actions above, each documented beside its others, whose driver gains
  the six actions above, each documented beside its others, and wraps `check_commit`,
  `merge_preconditions` and `summary` for them, which gains the class `Land` and its
  eighteen tests, and in whose two tests of `HandOver` the line that defines `harness` is
  looked for, and rewritten, as it now reads.

  Approved here too is the one change to the launcher, `scripts/hooks/safe-push`, whose
  usage comment now names `--land` on its `--branch` line; nothing else in it changes.
