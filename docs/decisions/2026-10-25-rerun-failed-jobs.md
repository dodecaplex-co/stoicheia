- **Either kind of rerun of a cadence run is judged on every shard's list
  ([#443](https://github.com/jackChallis/stoicheia/issues/443)).** The texts that
  [#233](https://github.com/jackChallis/stoicheia/issues/233) brought with the cadence's
  shards ([its entry](2026-10-24-safe-push-shards.md)) said that a run re-run with
  "re-run failed jobs" stays red, since its proof may not see the lists the other shards
  kept in the earlier attempt, and pointed to "re-run all jobs" alone. They rested on the
  coordinator's ruling of 24 October 04:40, made while it was not known whether a later
  attempt of a run can fetch an artifact an earlier attempt kept, and card
  [#411](https://github.com/jackChallis/stoicheia/issues/411) held the question until
  GitHub's behaviour was seen. That entry is history, and is not edited; this entry
  corrects what it said of a rerun of the failed jobs.

  What #411 showed. On 24 October the coordinator re-ran one shard of run 40122901299 of
  the cadence workflow, a run on a branch every job of which had passed, by itself: a
  second attempt that ran that shard again, and the verdict job, which needs it. The
  verdict job's fetch, which names no `run-id`, found all 16 artifacts of the run, each
  shard's list and log, the first attempt's among them, and the proof passed on all 466
  tests. A rerun of the failed jobs makes a later attempt of the same kind, which runs
  some of the jobs again and the verdict with them, and fetches the same way. So a rerun
  in part is judged, as a rerun of all the jobs is, on every shard's list: the lists of
  the shards it runs again, and those the others kept in an earlier attempt. (Card #443,
  carrying this from #425, called #411's rerun one of the failed jobs; the coordinator's
  log of 24 October says that one shard, shard 5, was run again alone.) #411 is closed,
  and the `run-id` fix it proposed, with the `actions: read` that fix would add to two
  jobs, is not made.

  The texts. In `.github/workflows/safe-push-tests.yml`, the comment on the step that
  keeps a shard's list said that a rerun of the failed jobs alone stays red; it now says
  that either kind of rerun is judged on every shard's list, and what #411 saw. The
  comment on the verdict job gave the reason both judgements are needed as a case that
  might arise, should a later attempt see a list an earlier one kept; it now says that a
  later attempt can see one, citing #411. [WORKFLOW](../WORKFLOW.md), section 8, under
  "The shards", says the same in the same two places, with links to #411 and to this
  entry. In `scripts/test_safe_push.py`, the docstring of `CadenceRun`, the model of a
  run, said that whether GitHub's fetch sees an earlier attempt's lists was not tried; it
  now says that the model's folder, which every attempt shares, lets a rerun see them, as
  GitHub's fetch did in #411.

  What stays. A rerun of all the jobs is judged afresh, as before. The proof never passes
  on lists it cannot see: that guard is unchanged, so should GitHub ever withhold a list,
  the proof fails, naming the shard, and the verdict is red. The verdict's own reading of
  the matrix's result stays too, since a shard cancelled in a rerun of all the jobs leaves
  its earlier list, which a later attempt can see. No step, condition or permission of the
  workflow changes, nor any code, test or expected value, nor what the model `CadenceRun`
  does. No test asserted the old texts or modelled a rerun of the failed jobs, and no test
  is changed.

  The coordinator settled the question on GitHub in #411, and filed this correction as
  card #443, carried from #425 so that the train of the shards' times landed as reviewed.
  This entry claims no approval of the owner.

  This entry approves, in `.github/workflows/safe-push-tests.yml`, the two comments above,
  on the step that keeps a shard's list and on the verdict job; the workflow's steps are
  as they were.

  This entry approves, in `scripts/test_safe_push.py`, the docstring of `CadenceRun`
  above; no code or test of the file changes.
