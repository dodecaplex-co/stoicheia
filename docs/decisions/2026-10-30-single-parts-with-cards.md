<!-- entry: id=single-parts-with-cards cards=694 line="Work lands as single parts that carry a card of the checks run on them once, starting with dated reports and decision entries." -->
- **Single parts with their cards, beginning with reports and decision entries
  ([#694](https://github.com/dodecaplex-co/stoicheia/issues/694)).** From 30 October
  2026 work lands one part at a time: the files of one kind of work (a report, a
  commentary, a figure, a proof, a tool), never several kinds batched together. Each part
  carries a card: what it is, the commit of main it was made on, the checks run on it with
  their verdicts, and when its writing began. The checks run once, on the machine that
  makes the part, through `scripts/safe_push.py --dry-run --emit-proof`; the landing takes
  that pre-flight from its proof (`--land --preflight-proof`, as decided on 29 October
  2026), so nothing is checked twice before CI, which runs once.

  The first parts are dated reports and decision entries, in `docs/reports/` and
  `docs/decisions/`: they hold no generated regions, few documents link to them, and each
  has one writer. Other kinds of part follow one at a time, each once the kind before it
  has been shown to land end to end; the guides, README.md and PROGRAM.md come after their
  generated and hand-written parts are separated
  ([#695](https://github.com/dodecaplex-co/stoicheia/issues/695),
  [#723](https://github.com/dodecaplex-co/stoicheia/issues/723)).

  A part's card can also stop it. A part still being written when parts of its kind have
  usually landed (at the 80th percentile of their times) is split, given help, or held for
  a decision; and a part whose checks fail stops its kind of work from starting another
  part until it passes.

  Why: on 30 October 2026 one change to a review record was found to have run
  `check_fidelity.py` and `render.py` about eight times each, and the check sequence three
  times, before it landed; a small change waited a median of 227 minutes for its turn; and
  200 of the 328 merges into main since 18 October carried two to six kinds of work
  together. A part that carries its checks runs each once, and waits only for its own.
