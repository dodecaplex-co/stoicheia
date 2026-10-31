<!-- entry: id=s12-leaves-dated-reports cards=283 line="S12 no longer reads the dated reports of docs/reports/; the Catalogues, the Prose, the Review notes, the Rendered docstrings and the front pages keep it." -->
- **S12 leaves the dated reports (style,
  [#283](https://github.com/dodecaplex-co/stoicheia/issues/283)).** On 30 October 2026 a
  report failed CI on S12, which read `strace` in backticks as an unknown Lean name. The
  owner said: "But this isn't a Lean supplier? It shouldn't have that test", and then, of
  the proposal to take S12 off the dated reports: "Yes take these out." Those are the
  owner's words; the rest of this entry is the coordinator's reading of them.

  S12 no longer reads the Other reports, which are every `docs/reports/*.md` but the
  Catalogues, the outside reviews and `docs/reports/crew/`. The Catalogues, which describe
  the edition as it stands, keep S12 exactly as they had it, and so do the Prose, the
  Review notes, the Rendered docstrings and the front pages. Every other rule that reads
  the Other reports goes on reading them.

  The owner's decision changes two protected files: `scripts/check_style.py` gives S12 no
  Other report, drops the sorting of a report's backticked words that served only that
  reading, with its index of Git's tracked files, and takes out of `REACH_PENDING` the
  entry of `docs/reports/mixed-angles-prototype.md`, with its 147 findings, and the seven
  entries the check reports as done; `tests/test_check_style.py` drops the tests of that
  sorting and that index, and adds one that `strace` fails a Catalogue and the Prose and
  never a report. `tests/test_check_acceptance.py` no longer asks whether the generated
  acceptance report would pass S12, which no longer reads it, and keeps its tests of the
  report's one revision and of findings quoted whole. Section 8 of `docs/STYLE.md` says
  the same.

  Why: a dated report in `docs/reports/` is an editorial part, right as of its commit.
  Held to today's Lean library, a report nobody touched fails when a Lean name changes
  later; and that was the only thing that made checking a report need a built Lean tree.
