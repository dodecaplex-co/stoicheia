- **The citation sweep runs in CI's `check` job, for every class.** The citation sweep
  ([#339](https://github.com/jackChallis/stoicheia/pull/339)) added its two steps to CI's
  `negative` job, as the decisions page's entry "The citation sweep (#32)" placed them,
  which since the risk classes check out the tree only for a change of R3 and above; for
  R0 to R2 the two steps found no `scripts/sweep_citations.py` and failed the job, and so
  every docs, text, records or proof pull request. The sweep reads the proofs' citations
  and the bindings that records declare in `unused`, which a proof or a records change can
  move, so it belongs to those pull requests too: its two commands now run in the `check`
  job, which checks out for every class, after the certificate and its test, and the
  `negative` job runs the negative tests alone, as before the sweep came. The pre-flight's
  lists and WORKFLOW section 8's command block move with them, in the same order, so that
  the three still agree; the commands themselves are unchanged.

  This entry approves the change to `.github/workflows/ci.yml`, whose two sweep steps move
  from the `negative` job to the `check` job.

  This entry approves the change to `scripts/safe_push.py`, whose sweep commands move from
  NEGATIVE to CHECKS, in the place the `check` job runs them.
