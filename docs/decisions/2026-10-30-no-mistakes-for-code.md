<!-- entry: id=no-mistakes-for-code cards=283 line="/no-mistakes is required before every merge except of Markdown files alone, of R0 or R1, which have a second reader instead." -->
- **/no-mistakes for code, a second reader for documents (landing,
  [#283](https://github.com/dodecaplex-co/stoicheia/issues/283)).** On 30 October 2026 the
  owner asked: "Could we skip /no-mistakes on documents?", and went on: "Seems like it's
  only needed for code." and "A dedicated reviewer is fine." Later the same day:
  "Documentation doesn't need that, code does". Those are the owner's words; what follows
  is the coordinator's reading of them.

  A change of Markdown files alone, of class R0 or R1 by `scripts/risk.py` (most guides,
  the reports, the decisions, the briefs, Heath's text, the commentary and the book's
  pages), needs no `/no-mistakes`. A second reader reads it instead, recorded in the
  `/code-review` row of the pull request, whose `/no-mistakes` row says "Not needed".
  Every other change still needs `/no-mistakes`: code of R2 to R5, and the data and records
  of R0 and R1 as well, such as a review record, a figure or a ruleset's JSON, which are
  not documentation. At the merge, current main's copy of `scripts/risk.py` classes the
  change, and a class it cannot find, or labels that cannot be read, count as code.

  The pull request template, `.github/pull_request_template.md`, marks its `/no-mistakes`
  box **Required if code**, and its note on the reviews says when the review is needed.
  The merge's gates in `scripts/safe_push.py` read that mark: the box, and the
  `/no-mistakes` row of the Reviews table, bind every change but one of Markdown files
  alone, of R0 or R1, and every protected change. `scripts/test_safe_push.py` tests that a
  change of a Markdown file of R0 merges without them, and that a change of R3, or of a
  file of R1 that is not Markdown, does not. Section 10 of `docs/WORKFLOW.md` says the same
  of the reviews and the merge's gates, and its account of trains says what a member that
  needs no `/no-mistakes` writes in its row.

  Why: a document's faults are of fact and of wording, which readers find; `/no-mistakes`
  runs the tests and the lint that code needs. On the first part to land singly, a
  decision entry (#853), it took about 14 minutes and found one fault, of wording.
