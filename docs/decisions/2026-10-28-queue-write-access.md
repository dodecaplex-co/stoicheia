- **Until #574's signatures replace it, write access to the pull request vouches for the
  pre-flight block; and CI's integration jobs wait for #574's signer (tooling,
  [#603](https://github.com/dodecaplex-co/stoicheia/issues/603) and
  [#605](https://github.com/dodecaplex-co/stoicheia/issues/605)).**
  WORKFLOW section 10, "The merge queue", keeps the queue off until two things are held
  by something a merge group cannot change. The first, the judge's code and its running,
  is to be held by the organization ruleset that requires `queue-judge.yml` from main
  ([27 October 2026](2026-10-27-queue-judge-required-workflow.md),
  [#602](https://github.com/dodecaplex-co/stoicheia/issues/602)). The second, the
  authenticity of the pre-flight block in a pull request's body, was left to the owner:
  the judge checks the block for consistency with the repository, not as proof that a
  pre-flight ran, and a block typed to be consistent passes it, as a test of the judge
  shows.

  On 28 October 2026 (about 04:55 Pacific) the owner chose, of the two routes the
  coordinator put to them, "Write access now, #574 later" (the coordinator's record:
  #603). So until #574's signed evidence lands, write access to the pull request is
  what vouches for the block: whoever can edit the body is trusted not to type a block
  for a pre-flight that did not run. That is anyone with write access to the repository,
  and the pull request's own author, whom GitHub lets edit its body, even after a writer
  has queued it. The card put the route as trusting the owner's account and the revert
  App alone; but to open a pull request between this public repository's branches,
  GitHub requires write access to the head branch or membership in the organization
  that owns the repository
  ([GitHub's documentation](https://docs.github.com/en/enterprise-cloud@latest/pull-requests/how-tos/create-pull-requests/creating-a-pull-request)),
  and the judge refuses only a bot's edit of the body, so the route trusts such an
  author too. Only an account with write access can queue an entry. The judge refuses
  one whose head is not in this repository, the automatic
  revert included, and, but for that revert, one that a bot wrote, queued, last edited
  or last renamed; the revert's author must be the revert App, and its body is read only
  for its `Reverts:` and `Failed run:` lines, each checked against GitHub's record of the
  failed push (WORKFLOW section 10). Today every pull request here is opened by the
  owner's account, which the project's tools push as, and its entries are to be queued
  from it, so the choice trusts the agents that work under it not to type a block by
  hand. When #574 lands, the judge checks CI's signature on the evidence instead, and
  that train changes rule (b).

  So the queue may be turned on once #602 has landed, the owner has imported its ruleset
  (the owner's step 1), and the queue's trial on real merge groups
  ([#606](https://github.com/dodecaplex-co/stoicheia/issues/606)) has passed: the trial
  is what shows the first requirement holding, and this entry records what holds the
  second.

  The second ruling answers #605. A merge group's own `ci.yml` runs `check`, `negative`,
  `model`, `formal-model`, `acceptance` and `queue-tests`; a group can edit that file,
  and the branch ruleset matches those checks by name alone (`queue-tests` among them
  once the queue is on). The coordinator put two routes to the owner: require `ci.yml`
  from main too, by file, as `queue-judge.yml` is, at the cost that no change to CI
  would then run before it lands; or #574's signer, under which CI signs the checks it
  ran and the judge verifies them. On 28 October 2026 (about 04:55 Pacific) the owner
  chose, of those two, "Use #574's signer later" (the coordinator's record: #605). So no
  ruleset changes for it now, changes to CI keep running on their own pull requests
  before they land, and #605 waits on #574. Until then GitHub does not hold a group that
  edits one of those jobs to pass: the change's review and its pre-flight are what stand
  in the way. This ruling changes no file but this entry.

  This entry approves the change to `docs/WORKFLOW.md`, whose section 10 now says that
  write access to the pull request vouches for the pre-flight block until #574's
  signatures replace it, and that the queue may then be turned on once the ruleset is
  imported and the trial passes.

  This entry approves the change to `scripts/check_queue.py`, whose docstring says the
  same of rule (b)'s second requirement, in place of "is not held"; no code changes.

  This entry approves the change to `tests/test_check_queue.py`, whose comment on
  `test_a_consistent_forgery_passes` says the same; the test is unchanged, and still
  passes a consistent forgery, since the judge does not check what write access vouches
  for.

  This entry approves the change to `.github/workflows/queue-judge.yml`, whose comment
  on `queue-integrity` says the same; no step, event or setting changes.
