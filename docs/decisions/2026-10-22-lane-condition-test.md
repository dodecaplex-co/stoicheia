- **Every step after a lane step carries its condition, by a test
  ([#346](https://github.com/jackChallis/stoicheia/issues/346)).** E2a
  ([#276](https://github.com/jackChallis/stoicheia/issues/276)) gave CI's `negative` and
  `formal-model` jobs a first step, `lane`, that reads the change's class, and every step
  after it the condition `if: steps.lane.outputs.full == 'true'`, so that for a change of
  a lower class the job passes at once. #339 then added steps to the `negative` job
  without the condition, and nothing caught it until every R0 to R2 pull request failed.
  A unit test now reads every workflow in `.github/workflows/`: in each job with a step
  whose id is `lane`, each later step must carry that condition, as it stands or inside
  `${{ }}`, and CI's `negative` and `formal-model` jobs must have the lane step. A step
  added without it fails the tests of the pull request that adds it. The test is planted
  three ways in each job, with the condition removed from a step, replaced by `always()`,
  and changed to `'false'`, and taking the condition from one step of the real `ci.yml`
  was seen to fail it, naming the step. No workflow changes.

  This entry approves the change to `scripts/test_safe_push.py`, whose new test in
  `Units` checks every step after a lane step for E2a's condition.
