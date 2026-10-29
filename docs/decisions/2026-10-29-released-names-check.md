<!-- entry: id=released-names-check cards=700 line="A new check holds main to the names the last release tag declares: each stays, under its own name or a deprecated alias, unless that tag had deprecated it." -->
- **A check that main keeps every released name (checks,
  [#700](https://github.com/dodecaplex-co/stoicheia/issues/700)).** The coordinator's
  orders of 29 October 2026, 12:18, assign card #700.
  [FORMALIZATION.md](../FORMALIZATION.md), section 2 ("A released name stays, or is
  deprecated first"), holds that a name a release tag's `Elements` declares, helpers and
  Book Zero included, is never renamed or removed "without a deprecated alias for one
  release", and that a name deprecated in a release may go in the release after. Tag
  `book-III` declares `Elements.Triangle.of_onCircle`,
  `Elements.exists_onCircle_oppositeSidesOf` and `Elements.exists_onCircle_sameSideOf`,
  and main declares none of them and nothing in their place: the entry of 24 October,
  [Circle 3 retired](2026-10-24-circle-3-retired.md), removed them as having no user in
  the repository, where the rule protects the users outside it. The release-map gate
  reader found it, and no check compared a release tag's names with main's. The card has
  two trains, one risk class each: the aliases, which declare the three names again,
  deprecated and pointing to III.2's corollaries, and this one, the check. The check lands
  after the aliases: until they land, main lacks the three names, and the check, a step
  of CI's `check` job, would fail every pull request.

  What it holds. `scripts/check_released_names.py` compares the names of the last release
  tag, from a committed list, with those main's built library declares. A name the tag
  marked deprecated passes whether main declares it or not. Any other passes when main
  declares it, deprecated or not, and fails, by name, when main does not. A name new on
  main passes; a renamed name passes only with its deprecated alias under the old name;
  and a namespace renamed fails once for each name in it. The check exits 1 on a finding,
  and 2 when it cannot judge: with no `lake`, when the build of `Elements` is not current,
  when Lean fails, when the probe prints anything but its rows, a Lean message among them,
  and when the list is malformed. None of these is a pass.

  How it reads names. The probe is a Lean file, `import Elements` and one `#eval`, written
  to a temporary folder outside the repository and run as `lake env lean` from its root.
  It prints a row for each declaration of a module under `Elements` that is neither an
  internal detail nor private, is not one of the recursors Lean makes, is not a parser,
  and has a declaration range, so was written in the source: those without one are all
  Lean's own, such as `injEq` and `eq_def`. A parser is a constant of type
  `Lean.ParserDescr` or `Lean.TrailingParserDescr`, which Lean makes for a `notation` and
  names from its symbols, as `Elements.«term∠___»`. Parsers are left out because no citer
  writes such a name and no deprecated alias can stand in for one: a change to a notation
  is a change of how statements are written, which is outside this check. Instances stay,
  since they are names Lean prints and a user can cite. A row is `name` and the name, or
  `deprecated` and the name for a declaration marked `@[deprecated]`, so that a line of
  any other form, as a Lean message is, is refused. Measured on 29 October 2026, before
  parsers were left out: book-III's build gave 502 names and origin/main's at 511fb5fe5
  gave 1,854, each with the parsers of the four notations of
  `Elements/Foundations/Magnitudes.lean` among them, so 498 and 1,850 without them; and
  the three above are exactly those book-III has and main lacks.

  A stale build is refused, not judged. The probe reads the built library and not the
  sources, and a stale build would give a stale answer. So before the probe, in each mode
  that runs it, the script runs `lake build --no-build Elements` from the repository's
  root, which builds nothing and fails when a module of `Elements` is not up to date with
  its sources; when it fails, the script stops (exit 2), saying that the build is not
  current and that `lake build` comes first, with the last lines Lake printed. In CI's
  `check` job the build runs before the check, so there this costs a check of Lake's
  traces and nothing more.

  The list, and each release. `tests/released_names.txt` holds comment lines saying what
  it is and how it is made, a tag line with the tag's name and its full commit, then the
  probe's rows at the tag, sorted by code point, each name once; the reader refuses
  anything else, naming the line. The script's `--list TAG` prints the file, and refuses
  unless the repository holds the tag, HEAD is the tag's commit, no tracked file is
  modified and the build is current. Section 10 of [WORKFLOW.md](../WORKFLOW.md) makes
  the tag after the release's pull request merges, so the list cannot be in that pull
  request. At each release, once the tag is made, the list is made with
  `--list <new tag>` at the tag's commit and committed in the next pull request, the first
  after the release; until it lands, main is compared with the release before, which is
  still correct for every name that release declared. The step belongs in the release
  step of WORKFLOW.md, section 10, which this train does not change; that change is the
  coordinator's to file. Where the repository holds the list's tag, the check requires that
  tag to point to the list's commit; a checkout that fetches no tags is told so in one
  line, and judged all the same. The list committed here was written by the script's own
  `render_list` from a run of the probe on book-III's build, with the four parsers' rows
  taken out, so it is in the form `--list` prints.

  The self-test. `--self-test`, which the registry runs, puts a namespace of declarations
  in the probe's own file and requires the probe to read each as planted: four theorems
  and an instance plain, three deprecated, and no row for a private theorem, for a
  notation's parser or for an infix's, one of each parser type; and the real
  `Elements.BookI.Prop1` plain. On that output it then judges seven lists made in memory:
  a name removed fails; a renamed name with its alias passes, and so does a name
  deprecated with nothing to replace it; beside a name with its alias, a name aliased
  nowhere fails alone; a namespace renamed fails once for each of its two names; a removed
  name that the tag marked deprecated passes; and a list that names nothing new on main
  passes. Any surprise fails it. Then it runs the check on the same output, the planted
  namespace left out, so the whole is one Lean file. Lean 4.35 warns at
  `@[deprecated (since := …)]` with neither a new name nor a message, and a warning is
  output the probe refuses, so the plant deprecated with nothing to replace it carries a
  message. `tests/test_check_released_names.py` holds the rule, the readers of the list
  and of the probe's output, the refusal of a stale build in each mode with `lake` stood
  in for, the modes with the probe and git stood in for, and the committed list, case by
  case, without Lean.

  This entry approves the new `scripts/check_released_names.py`, the check with its probe
  and its self-test.

  This entry approves the new `tests/test_check_released_names.py`, the check's cases
  without Lean.

  This entry approves the new `tests/released_names.txt`, the names that tag `book-III`
  declares.

  This entry approves the new `checks/28-test-check-released-names.toml`, which runs those
  cases at order 147.

  This entry approves the new `checks/29-check-released-names.toml`, which runs the
  self-test and the check at order 148.

  This entry claims no approval of the owner's.
