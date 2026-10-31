<!-- entry: id=no-mistakes-for-code cards=283 line="/no-mistakes is required before the merge of a change of code, of R2 to R5; a change of documents, text and records alone has a second reader instead." -->
- **/no-mistakes for code, a second reader for documents (landing,
  [#283](https://github.com/dodecaplex-co/stoicheia/issues/283)).** On 30 October 2026 the
  owner asked: "Could we skip /no-mistakes on documents?", and went on: "Seems like it's
  only needed for code." and "A dedicated reviewer is fine." Later the same day: "Documentation
  doesn't need that, code does".

  So `/no-mistakes` is required before the merge of a change of code, of class R2 to R5 by
  `scripts/risk.py`: the proofs, the checks, the foundations, the landing tool and CI. A
  change of documents, text and records alone, of class R0 or R1, needs none. A second
  reader reads it instead, recorded in the `/code-review` row of the pull request, whose
  `/no-mistakes` row says "Not needed". The classes stay in one place: at the merge,
  current main's copy of `scripts/risk.py` classes the change, and a class it cannot find,
  or labels that cannot be read, count as code.

  The pull request template, `.github/pull_request_template.md`, marks its `/no-mistakes`
  box **Required if code**, and its note on the reviews says when the review is needed.
  The merge's gates in `scripts/safe_push.py` read that mark: the box, and the
  `/no-mistakes` row of the Reviews table, bind a change of code or a protected one, and
  no other. `scripts/test_safe_push.py` tests that a change of R0 merges without them and
  that a change of R3 does not. Section 10 of `docs/WORKFLOW.md` says the same of the
  reviews and the merge's gates.

  Why: a document's faults are of fact and of wording, which readers find; `/no-mistakes`
  runs the tests and the lint that code needs. On the first part to land singly, a
  decision entry (#853), it took about 14 minutes.
