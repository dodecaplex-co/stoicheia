<!-- entry: id=released-names-check cards=700 line="A new check holds main to the names the last release tag declares: each stays, under its own name or a deprecated alias, unless that tag had deprecated it, or its removal is approved and listed." -->
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
  when Lean fails, when the temporary probe cannot be created, resolved, written or
  removed, when the probe prints anything but its rows, a Lean message among them, and
  when the list is malformed. None of these is a pass.

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
  probe's rows at the tag, sorted by code point, each name once. The tag begins with an
  ASCII letter or digit, continues with ASCII letters, digits, `.`, `_`, `/` or `-`, and
  must make a valid `refs/tags/<tag>` Git ref; the reader refuses any other form, naming
  the line. The script's `--list TAG` prints the file, and refuses if the tag is outside
  that form, the repository does not hold it, HEAD is not the tag's commit or the build is
  not current. Any tracked file save the list itself that is marked `assume-unchanged` or
  `skip-worktree` causes refusal with exit 2, even when its contents match HEAD; clear the
  flags before listing. No file that could change what the build declares may differ from
  the commit: no tracked file is modified, save the list itself, which the recipe's
  redirection empties before the script runs, and there is no untracked or ignored Lean
  file, Lake configuration, manifest or toolchain. [WORKFLOW.md](../WORKFLOW.md), section
  10, makes the tag after the release's pull request merges, so the list cannot be in that
  pull request. At each release, once the tag is made, the list is made with
  `--list <new tag>` at the tag's commit, copied to a branch off main and committed in the
  next pull request, the first after the release; until it lands, main is compared with
  the release before, which is still correct for every name that release declared.
  WORKFLOW.md, section 10's release step does not yet name this step, and this train does
  not change it; the change is the coordinator's to file. Where the repository holds a tag
  after the list's, one whose history holds the list's commit, the check names it in a
  note: the list may be out of date. Where the repository holds the list's tag, the check
  requires that tag to point to the list's commit; a checkout that fetches no tags, as
  CI's `check` job does not, is told so in one line, and judged all the same. The list
  committed here is what `--list book-III` prints: on 29 October 2026, on the yard's
  machine, the script as at commit 022481000, as an untracked copy, was run at book-III's
  commit, 792082f0c, after `lake build`, and its output was byte for byte this file.
  Another script that reads names the same way, as the release notes'
  generator ([#702](https://github.com/dodecaplex-co/stoicheia/issues/702)) does, should
  call the script's `run_lean` and `read_probe` rather than copy them.

  The self-test. `--self-test`, which the registry runs, puts a namespace of declarations
  in the probe's own file and requires the probe to read each as planted: four theorems
  and an instance plain, three deprecated, a structure with its constructor and field
  plain; no row for a private theorem, for a notation's parser or for an infix's, one of
  each parser type, for the nine names Lean 4.35 makes for the structure that one filter
  each leaves out (its recursors, `noConfusion`, and the names with no declaration range),
  or for any other name of the namespace, the internal details the notation makes among
  them; no name outside `Elements`; and the real `Elements.BookI.Prop1` plain. Each name
  that must give no row is used by an `example` among the plants, so a plant removed stops
  Lean rather than reading as absent. On 29 October 2026, on the yard's machine, each of
  the probe's filters was taken out in turn, and the self-test then failed (exit 1, or 2
  when the module filter's absence filled the output with Lean's own names), save for
  `isPrivateName`, which `isInternalDetail` makes redundant for a private name. On that
  output it then judges seven lists made in memory: a name removed fails; a renamed name
  with its alias passes, and so does a name deprecated with nothing to replace it; beside
  a name with its alias, a name aliased nowhere fails alone; a namespace renamed fails
  once for each of its two names; a removed name that the tag marked deprecated passes;
  and a list that names nothing new on main passes. Any surprise fails it. Then it runs
  the check on the same output, the planted namespace left out, so the whole is one Lean
  file. Lean 4.35 warns at `@[deprecated (since := …)]` with neither a new name nor a
  message, and a warning is output the probe refuses, so the plant deprecated with nothing
  to replace it carries a message. `tests/test_check_released_names.py` holds the rule,
  the readers of the list and of the probe's output, the refusal of a stale build in each
  mode with `lake` stood in for, the modes with the probe and git stood in for, and the
  committed list, case by case, without Lean.

  Removals the owner approves (added on 30 October 2026, before the check landed). The
  coordinator's message of 30 October 2026 asks that the check allow one thing more: the
  owner decided that day that Metric 9, `Elements.Tacit.area_congruent`, a name tag
  `book-III` declares, leaves main this release with no alias (#517), and that the release
  notes list it as removed. This entry records no approval of that removal, and is not one.
  A released name may leave main with no alias when two things hold, and only then: a
  decision entry already on main approves its removal, and the release notes' list of
  names removed records it. The release notes are written at the release, so that list is
  kept until then in `tests/released_names_removed.txt`, for the notes to take it from
  (#702). Each row there is `removed`, the name, and the path of its decision entry under
  `docs/decisions/`. The check holds each row to three things: its name is one the list's
  tag declares and main does not; its entry is at the base the change is merged into,
  read out of Git, and the checkout holds it byte for byte the same; and that copy's
  header names it in a new key, `removes=`. The key is the approval. The entry's prose
  holds the owner's words, for people to read; the check does not parse it, since prose
  can be made to read as an approval in more ways than a reader can list, and the guard
  is that the entry landed on main through review, unchanged since. So the approval lands
  first, in a pull request of its own, and the removal comes after: a pull request that
  removes a name can neither bring its own approval nor change one already on main. A row
  that fails is a finding, naming its line, and a released name main lacks passes only
  when its row holds; with no row, or one that fails, it is the finding it always was.

  The base. Outside GitHub Actions it is origin/main, as the pre-flight and a contributor
  have it. In GitHub Actions it is the first parent of the commit the job checked out, and
  never origin/main, which there is absent or may stand elsewhere: for a pull request,
  whose base branch `GITHUB_BASE_REF` names, the checkout is GitHub's merge of the head
  into that branch, so its first parent is the exact base tested, and a checkout with any
  other number of parents gives none; for main's run after a merge, it is main before the
  merge. CI's `check` job checks out that one commit alone today (`actions/checkout` with
  no `fetch-depth`, so a depth of 1), which holds no parent, so there is no base in CI
  yet. The list is read before Lean, and a malformed or missing one stops the check (exit
  2); a row with no base to judge it against stops it too, and an empty list asks for no
  base. The list has no rows, so CI needs none now. Before the first row lands,
  `.github/workflows/ci.yml`'s `check` job must fetch the parent (`fetch-depth: 2` on its
  checkout), and the contract of that job in `scripts/test_safe_push.py` must say so, as
  it pins each job's checkout: a change of risk class R5, the coordinator's, in a pull
  request of its own; this one changes neither file. Metric 9's row comes in the pull
  request that removes Metric 9, after an entry on main whose header removes it; the list
  is emptied in the pull request that commits the next release's list of names.
  `tests/test_check_released_names.py` holds both sides: an approved, listed removal whose
  entry is at the base unchanged passes; one approved but not listed fails; a listed one
  fails when its entry is new in the pull request, changed there, or has no `removes=`
  naming it; and with no base, an empty list passes and a row stops the check.

  The header's `removes=` key. `scripts/render.py` reads every entry's header and refuses
  an unknown key, so it learns the key: it stands after `reverts` and before `line`, a
  list joined by commas like the others, each item a Lean name in full under `Elements`:
  segments joined by dots, each a Lean identifier or a `«…»` escape holding no `«`, `»`
  or line break, and nothing else. The check holds the same pattern, and an item outside
  it approves nothing there. The check reads the key only from the header's tokens before
  `line`, so words in the news cannot pass for it. `docs/WORKFLOW.md`, "Decision
  entries", gives the key in the header's form and says what it is for. This entry
  approves the change to `scripts/render.py`: the key, its place among the keys and its
  refusal of an item that is not a name under `Elements`.

  This entry approves the change to `tests/test_decision_entries.py`: the header with
  every key gains `removes=`, an escaped name among its items, the header with the
  required keys alone reads it as empty, and the refusals gain a removed name out of
  order, not under `Elements`, with an empty segment, a character no identifier holds, a
  leading digit or a broken escape, given twice, and an empty item; and a case holds
  render.py's pattern and the check's to one.

  This entry approves the new `tests/released_names_removed.txt`, the list of names removed
  with no alias. It has no rows yet, and each row it gains needs a decision entry already on
  main whose header removes that name.

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

  Both run alone, as the registry's rule of #608 has every new check run until a reviewed
  change declares it concurrent: neither declares `concurrent`, and each file says why in
  its line "Alone (#608)". This entry approves the change to
  `tests/test_concurrent_checks.py`: the two commands join the set its registry case
  expects to run alone.

  This entry claims no approval of the owner's.
