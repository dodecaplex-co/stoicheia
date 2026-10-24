- **Every step after a lane step carries its condition, by a test
  ([#346](https://github.com/jackChallis/stoicheia/issues/346)).** E2a
  ([#276](https://github.com/jackChallis/stoicheia/issues/276)) gave CI's `negative` and
  `formal-model` jobs a first step, `lane`, that reads the change's class, and every step
  after it the condition `if: steps.lane.outputs.full == 'true'`, so that for a change of
  a lower class the job does nothing, unless `formal-model` runs in full for a change to
  the model's inputs. #339 then added steps to the `negative` job without the condition,
  and nothing caught it until every R0 to R2 pull request failed. A unit test now reads
  every workflow in `.github/workflows/`: in each job with a step whose id is `lane`, the
  lane step must come first and each later step must carry that condition, as it stands
  or inside `${{ }}`, and CI's `negative` and `formal-model` jobs must have the lane step.
  The match is strict: any other spelling, or the condition combined with another, is
  refused, since a partial `${{ }}` or an `|| always()` would run the step for R0 to R2.
  The test is planted in each job with the condition removed from a step, replaced by
  `always()` and changed to `'false'`, with a step put before the lane step, and with
  steps named only by their action or their place; taking the condition from one step of
  the real `ci.yml` was seen to fail it, naming the step. No workflow changes. The test is
  in `Units`, which runs in seconds on any branch, and with the rest of the suite on the
  cadence, which finds such a step on main within six hours and holds the release. It
  does not yet run on a pull request's own path, so the pull request that adds such a
  step is not yet failed by it: that is the rest of #346, a check of the pull request's
  own once the registry of checks (#229) lets one be added as a file.

  This entry approves the change to `scripts/test_safe_push.py`, whose new test in
  `Units` checks that the lane step comes first and every step after it carries E2a's
  condition.
