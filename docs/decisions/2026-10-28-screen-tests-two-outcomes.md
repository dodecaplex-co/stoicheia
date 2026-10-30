- **The overlap screen's cases name both outcomes while its canary lands
  ([#416](https://github.com/dodecaplex-co/stoicheia/issues/416), tooling).** The screen
  of #416, each try given its background and its one known row a planted canary, moves
  nine of the cases of [`tests/test_screen.py`](../../tests/test_screen.py): their calls
  take the background, or the tries the screen made, and their expected values follow
  the canary. Main's cases fail on that screen, so the pre-flight keeps the screen and
  the cases that require it apart: the new outcomes cannot become active before the
  screen they call. On 28 October 2026 the coordinator ruled that it lands in three
  trains, with no check loosened between them: first these cases, then the screen, then
  the old outcomes retired. Nothing in Lean changes here, nor any statement, definition,
  lock or `--` line, nor `facts.json`, nor `Audit/screen.py`.

  Each of the nine names its two outcomes as whole cases, each a method of its own:
  `old_`, main's case as written, for the screen without a background, and `new_`, the
  case as written for the screen with its background and canary. The only words changed
  in an old case are the names of what the two share: III.5's fixture of `KnownRows` is
  `RULED_OLD` beside the canary's `RULED`, and `Record`'s helper for a stale build is
  `run_with_build_change_old` beside the new one, which stands in for the background.
  The case itself, `test_`, calls a helper, `exactly`, which holds the screen to the
  outcome its generation names, by `PLANTED`, which only the new screen has, and
  requires the other to fail; so a screen that mixes the two, or passes either outcome
  by chance, fails the case. The nine: in `Attempts`, the attempts of each statement; in
  `Tries`, the refused rules left out; in `Definitions`, the roots of the pass; in
  `KnownRows`, its three cases on III.5 and the canary; and in `Record`, the three runs
  whose stand-ins hold the background empty on the new screen. The other 54 cases are
  unchanged, and pass on both screens.

  Evidence, at origin/main d4d7f9a5c: the file's 63 cases pass on main's screen, and on
  the screen of #416 (staging/416-canary-d); with `PLANTED` added to main's screen, or
  taken from the new one, each of the nine fails.

  For the overlap screen's landing, this entry approves `tests/test_screen.py` as this
  train leaves it: the nine cases named above each naming its two outcomes, the helpers
  `exactly` and `as_named`, the fixture `RULED_OLD` and the helper
  `run_with_build_change_old` beside the new ones, and its docstring brought up to date,
  with no case lost or loosened.
