<!-- entry: id=sweep-refuses-a-panic cards=236 line="The citation sweep refuses a run of Lean that prints a panic, whatever its exit, naming the line." -->
- **The citation sweep refuses a run of Lean that prints a panic, whatever its exit
  (checks, [#236](https://github.com/dodecaplex-co/stoicheia/issues/236)).** The
  coordinator's orders of 29 October 2026, 12:33, assign card #236 to ship TL; this entry
  claims no decision of the owner's.

  `scripts/sweep_citations.py` runs Lean on each file it sweeps (`run_lean`) and reads the
  run as a success when Lean exits 0 with no error line, or exits 1 with the linter's
  reports alone. Lean can print `PANIC at …` and a backtrace and still exit 0 with no
  error line; the independent review TT-sweep-cr7 found that the sweep then read the run
  as whole, and the strict sweep is a step of the release (WORKFLOW, section 10, step 10).
  An internal panic, `INTERNAL PANIC …`, ends Lean with exit 1 (`lean_internal_panic`, in
  Lean 4.35's runtime), and the sweep refused that run already, since its standard error
  is not empty; a promise dropped unresolved prints `PANIC: Promise.result!: …`. Now a
  line of either stream that begins `PANIC at `, `PANIC: ` or `INTERNAL PANIC` fails the
  sweep, whatever the exit, before either reading: its
  `SweepError` names the stream and the line, and the sweep exits 2. A message that only
  quotes the words within a line is read as before.

  The self-test's runs of Lean, which stand Lean's output in for its process, gain four
  plants on exit 0 (a panic and its backtrace; a warning, then an internal panic; a
  warning, and a panic on standard error; a dropped promise) and one control (a warning
  that quotes a panic within its line), and the self-test now requires each refusal for a
  panic, the earlier exit-1 plant's among them, to come from the panic's rule and to end
  with the panic's line. Main's sweep reads all four exit-0 plants as whole runs. The
  module's docstring names the new refusal, among the causes of exit 2 and in the
  self-test's account.

  This entry approves the change to `scripts/sweep_citations.py`: the pattern `PANIC` and
  its use in `run_lean`, the self-test's runs, the constants they plant and the check that
  each refusal names its panic, and the module's docstring.
