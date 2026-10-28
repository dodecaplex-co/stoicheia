- **The queue's judge moves to a workflow of its own, which an organization ruleset
  runs from main, so that a group cannot change or skip the code that judges it
  (tooling, the follow-on of [#259](https://github.com/jackChallis/stoicheia/issues/259)).**
  WORKFLOW section 10, "The merge queue", has held the queue off until something a group
  cannot change holds the queue's judging, since GitHub ran each group's own copy of
  `ci.yml`, whose `queue-integrity` and `queue-gaps` jobs the group could edit or drop.
  On 27 October 2026 the owner moved the repository into an organization and, in the
  coordinator's quotation of the owner's words, asked "How do I go the Github Teams
  route", then said "I upgraded": the organization is on GitHub Team. With it, the
  coordinator chose, of the three holders WORKFLOW named, an organization ruleset rule,
  "Require workflows to pass before merging", with the workflow run from main; code-owner
  review would put the owner's review in the path of every pull request, and signed
  evidence (#574) is several trains away.

  The workflow. `.github/workflows/queue-judge.yml`, "Queue judge", holds the two jobs,
  moved from `ci.yml` with their steps on a merge group unchanged: each takes `scripts/`
  from the group's base by Git objects, never from the checkout. On a pull request each
  passes at once, with nothing to judge. Its events are `pull_request` and
  `merge_group`, the rule's, unfiltered, since the rule ignores filters; neither job has a
  condition of its own, since a skipped required job counts as passed (the coordinator's
  trial, below). What `ci.yml` keeps of `queue-integrity` is its offline cases, as
  `queue-tests`, on pull requests and on main.

  Why move rather than vouch. A required workflow from main that checked the group's
  `ci.yml` against main's copy or main's job contracts would refuse every change of the
  jobs it held, or else accept the group's own new version and let the group vouch for
  itself. Requiring `ci.yml` itself from main would need no new code, but no change to CI
  would then run before it lands, and a broken `ci.yml` on main would fail every pull
  request, its own repair included, with no bypass to recover by but disabling the
  ruleset. The move costs one new mode of `check_queue.py`, below.

  Acceptance's verdicts. `queue-gaps` needed `acceptance` in its own run, and a job of
  another workflow cannot. `check_queue.py --acceptance-run` finds them in the group's CI
  run: the one run of `ci.yml` for the group's head and the `merge_group` event, its
  latest `acceptance` job, passed, and the one `acceptance` artifact made within that
  job, downloaded by its id, of which only `verdicts.json` is read, and the run, the job
  and the artifact read again after the download, the run's attempt unchanged; a list not
  read whole, or any other answer, refuses. It waits with no limit of its own earlier
  than the queue's status check timeout, 150 minutes, which binds as before. The
  handover after `acceptance` ends, a few reads and the download, takes the place of the
  runner `queue-gaps` waited for when it followed `acceptance` by `needs`; it is not
  exactly the same time, so a group that today ends at the very edge of the 150 minutes
  may now be ejected there, and the queue's trial is to measure it. The verdicts are the
  group's own CI's, as before, and are reported, not trusted further.

  Names. GitHub matches a required status check by its name alone, and a group can make
  a check of any name, so the judge's two jobs are never among the required checks: the
  organization ruleset requires them by their file. The ruleset to import is
  `docs/rulesets/queue-judge.json`: the repository `stoicheia`, renaming prevented; the
  branch `main`; the one rule `workflows`, naming `.github/workflows/queue-judge.yml` at
  `refs/heads/main` in the repository by its id; enforcement active; no bypass actor.
  The queue's tests hold it to that, and the installed ruleset is to be compared with it.
  The repository and the workflow's identity are settings in that file and the event's
  `github.repository`, never written in the judge's code, so that #574's signer can be a
  second entry of the same rule with no second design.

  What this holds, and what it does not. It holds the first of rule (b)'s two
  requirements, the judge's code and its running. It does not authenticate the
  pre-flight's block, which the judge checks only for consistency with the repository: a
  block typed to be consistent passes, and a test says so. That second requirement waits
  for evidence CI signs (#574) or for the owner's dated decision; the queue stays off
  until both are held.

  The coordinator's trial of 27 October 2026, on a pull request into a trial branch,
  showed the rule enforced on the Team plan, `ref: refs/heads/main` accepted, main's copy
  of a required file run in place of the pull request's own, and a skipped required job
  counted as passed. What it must still show, on a merge group and after this lands, is
  in the owner's steps: that main's copy runs there too, that a group whose own copy
  passes while main's fails is held, and the rest.

  A defect found on the way, already on main: the judge reads the names of the checks a
  pre-flight's harness runs from that harness's `CHECKS` and `NEGATIVE` lists, as string
  constants only, and main's `safe_push.py` names one entry by a constant,
  `EMPTY_CHECK`, so main's judge refused every full pre-flight that main's own harness
  records. It now reads a name bound once, at the harness's top level, by a plain
  assignment, to a string; anything else still refuses. Without it, no legitimate group
  could pass the queue's trial.

  This entry approves the new `.github/workflows/queue-judge.yml`, the queue's judge as
  above.

  This entry approves the change to `.github/workflows/ci.yml`, which loses `queue-gaps`
  and the judging step of `queue-integrity`, renamed `queue-tests`, whose offline cases
  now run on merge groups too, where it is required by name, with a limit of 30 minutes.

  This entry approves the change to `.github/workflows/post-merge.yml`, whose opening
  comment now says where the queue's judge runs.

  This entry approves the change to `scripts/check_queue.py`, which gains
  `--acceptance-run`, maps the new workflow to its tests, and reads a harness's check
  named by a constant.

  This entry approves the change to `tests/test_auto_revert.py`, whose test that the
  queue does not pass when acceptance failed or was skipped now tests it through
  `--acceptance-run`, the step it read having moved.

  This entry approves the change to `tests/test_check_queue.py`, whose tests of the
  judge's steps read the new workflow, and which gains the planted cases, the tests of
  `--acceptance-run` and the test that holds the ruleset file.

  This entry approves the change to `scripts/test_safe_push.py`, whose job contracts
  gain the new workflow and follow the move.

  This entry approves the change to `docs/WORKFLOW.md`, whose sections 8 and 10 say where
  the judge runs, what the ruleset holds and does not, and which checks are required.
