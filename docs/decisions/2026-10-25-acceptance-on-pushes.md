- **The acceptance job's account of its events, and section 9's criteria retired
  (acceptance, [#155](https://github.com/jackChallis/stoicheia/issues/155),
  [#35](https://github.com/jackChallis/stoicheia/issues/35)).** The coordinator, who owns
  WORKFLOW's and ACCEPTANCE's account of CI, delegated these lines to ship HM on 25
  October 2026 at 21:50, from its check of the blocks-release cards that evening.

  What was false. [ACCEPTANCE](../ACCEPTANCE.md#in-ci) said that CI's `acceptance` job
  "is skipped on pushes". The post-merge workflow calls CI on each push to main, and the
  job runs there (post-merge run
  [40260506691](https://github.com/jackChallis/stoicheia/actions/runs/40260506691)),
  as [WORKFLOW](../WORKFLOW.md), section 8, already said. ACCEPTANCE's "In CI" now says
  that the job runs on every event CI runs on, a pull request, a merge-queue group and a
  push to main, and its step 2 gives, event by event, the commit that stands for main, as
  the workflow's own step does: on a pull request the checkout's first parent when it
  has exactly two parents and the second is the pull request's head, else the recorded
  base when the checkout is that head, and any other checkout fails the job; in a group
  its base; on a push, main before the push. Its steps speak of the checked-out
  revision, not of the pull request alone.

  What was kept twice. WORKFLOW's section 9 still listed its ten release criteria,
  saying that the checklist incorporates them. It now names
  [ACCEPTANCE](../ACCEPTANCE.md) as the release standard and keeps its severity rules,
  which other pages cite, unchanged. ACCEPTANCE's "Where the older criteria went" says
  that both older lists, brief 0005's stage 6 and section 9's ten, are retired, and its
  tables name the items that take each one up; the row for the criterion "figures and
  page inspected" names P9 and P4 for the page beside P8 and P15 for the figures, and B3,
  the read-through of the book. No item is added, removed or changed.

  The protected file. This entry approves the change to `docs/ACCEPTANCE.md`.
