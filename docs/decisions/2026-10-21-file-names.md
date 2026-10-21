- **File names and types follow one standard
  ([#186](https://github.com/jackChallis/stoicheia/issues/186)).** The owner asked: "Can we
  standardize the file names and types so we don't have silliness with messy paths?" The
  standard writes down the conventions the tree already keeps, in six rules, stated in
  [WORKFLOW](../WORKFLOW.md#file-names), section 4, "File names", with their lists in
  [`scripts/check_paths.py`](../../scripts/check_paths.py), each a named constant. A path
  is ASCII letters, digits, `.`, `_`, `-` and `/`, with no empty, `.` or `..` segment, no
  segment beginning or ending with `.` or `-` save `.github`, `.gitignore` and `.gitkeep`,
  no Windows device name (`CON`, `PRN`, `AUX`, `NUL`, `COM0` to `COM9`, `LPT0` to `LPT9`,
  in any case), and at most 160 characters, 100 in a segment. No two paths, and no two of
  their folders, differ only in case or Unicode form, and no tree lists a path twice.
  Extensions are in lower case, from the fifteen the tree uses, and six named files have
  none. Each top-level folder, and the root, holds only its listed types and files, with
  further Markdown at the root named in capitals and digits, words joined by single
  hyphens (`LICENSE-PROSE.md`, never `NOTES-.md` or `A--B.md`). A book's pages, Heath's
  text, the mishnah, the reading lines, the review records, the figures and the briefs
  have mechanical names; a Lean file of the edition's libraries has Lean module names,
  with `BookR` and `PropNN` under `Elements/` and no `lakefile.lean`; a Python file's name
  can be imported, and its stem is not a Python keyword (soft keywords are allowed): a
  rule that, like `COM0`, `LPT0` and the single hyphens of the root's Markdown, refuses
  more than the standard as proposed wrote, and nothing in today's tree. A file is 100644,
  or 100755 for exactly six scripts, and there is no symbolic link and no submodule. A
  new book's paths already fit, Book X's 115
  propositions among them. The nine hand translations of the model's laws in
  `model/Model/Laws/` (`angles.lean`, `areas-p5.lean` and seven more, imported as
  `Model.Laws.«areas-p5»`) keep their lower-case names, the model's own convention, and
  the rule codifies it: a file directly in that folder is named in lower-case words
  joined by hyphens, every other Lean file keeps the module-name rule, and nothing was
  renamed. Every one of the 1,138 paths at origin/main `17369f92` passes; there were 1,137
  when the standard was written. The check reads Git's index, which is what is staged for
  the next commit: in CI and in the pre-flight's fresh worktree, the commit itself, and on
  a contributor's machine, what they have staged; never the working
  tree. `--rev` reads a commit's tree instead, entry by entry, so that a tree made by hand
  that lists a path twice is refused. The check runs first, before `lake build`, in CI's
  `check` job, in `scripts/safe_push.py`'s checks and in WORKFLOW, section 8:
  `python3 -I tests/test_check_paths.py`, then
  `python3 scripts/check_paths.py --self-test`. The self-test plants a fault of each rule
  in memory beside good paths, Book IV's and Book X's among them; the test file plants
  faults straight into the indexes of throwaway repositories, where a case-insensitive
  disk could not hold a twin as two files; and `scripts/negative_tests.py`
  plants eight (a case twin of `README.md` and one of a protected file,
  `Certificate/fields.md`, a space, an upper-case extension, a symbolic link, an
  executable bit, an svg under `book/` and a misnamed review record) in a copy of the
  edition's index that passes unplanted, under `--counts-only` too, leaving the real index
  and `git status` as they were. Every finding is one line of printable ASCII, naming its
  rule and its path, with any name inside the reason escaped as Git quotes a path. A
  module planted beside the script, such as `scripts/unicodedata.py`, is never read in
  place of the standard library's: the script takes its own folder off `sys.path` before
  any other import, and has no `from __future__` import, which would read a planted one
  first; the test file loads the script from its file, and plants such modules to show
  that they never run. The check independently discovers the script's worktree and its
  worktree-specific Git directory. It accepts an explicit `GIT_DIR` and `GIT_WORK_TREE`
  pair that identifies both, and refuses a foreign worktree or Git directory, and
  `GIT_DIR` set alone, as a Git alias run from a linked worktree sets it, with a message
  saying how to run the check
  (`env -u GIT_DIR -u GIT_WORK_TREE python3 scripts/check_paths.py`). The pre-flight's
  step 3 begins
  with two paths guards, which refuse outright, whatever the decisions record says, and run
  before the commit is checked out, so that a refusal comes before any worktree is made.
  The first refuses a commit whose tree, or the tree of any commit it brings since
  origin/main, holds a path or folder that collides with another under case folding and
  NFC normalisation, that is a protected path or a check input spelt otherwise
  (`LAKEFILE.lean`, `Scripts/x.py`, whether or not the tree holds the real one), or that
  is not plain printable ASCII, so that a twin of a protected path or a check input cannot
  change it by the back door. The second applies origin/main's own standard to the same
  trees: origin/main's `scripts/check_paths.py`, read from its blob and run by the harness
  itself, judges every commit's tree before any of the commit's code has run, so that
  nothing the commit runs (its `render.py`, say, taking a path out of the worktree's
  index) can keep a path from it; a copy that does not load, or fails on a tree, refuses,
  and when origin/main has none, as before the pull request that brings it, a note says
  so. They read each tree once and name, for each tree that
  holds a finding, the first commit with that tree, at most three and then "and N more";
  both run again at `--merge`, and their cases include the plainest twin,
  `Certificate/fields.md` beside `Certificate/FIELDS.md`, and a page in `.yaml` that only
  origin/main's standard refuses. `scripts/safe_push.py`, once it has found the
  repository, drops Git's location variables (`GIT_DIR`, `GIT_WORK_TREE`, `GIT_INDEX_FILE`
  and the rest; a Git alias run from a linked worktree sets `GIT_DIR`), so that every
  check in its fresh worktrees reads that worktree and never the caller's index or HEAD;
  when they name another repository, it refuses. In step 4, as a second line, a failure of
  origin/main's path check, or of its cases, refuses a pull request whatever else it
  changes, guides and protected paths alone included: every path is what the check judges,
  so a looser `scripts/check_paths.py` cannot land in the same pull request as the path it
  would let in. Each pass of the checks, in steps 3 and 4, begins with the worktree at the
  commit, or is refused: its HEAD the commit, its index the commit's tree, no file flagged
  skip-worktree or assume-unchanged, and `git status --porcelain --untracked-files=all`
  empty, each asked of Git with stat settings at their defaults, no fsmonitor, untracked
  cache or hook, and, as the worktrees are made, file modes compared and no conversion or
  attributes but the system's (`attr.tree` the empty tree), whatever the shared
  `.git/config` says, and refused while the shared `.git/info/attributes` exists; then
  every ignored file is removed but the build's caches, `.lake/` and `model/.lake/`, a
  channel the commit's build already has
  ([#197](https://github.com/jackChallis/stoicheia/issues/197)). This asks Git and
  compares no bytes, so routes past it remain (a hand-edited index, a process left
  running, a `.git` below the root among them;
  [#218](https://github.com/jackChallis/stoicheia/issues/218)), each needing code of this
  commit or one checked before to have run first, through a change to a protected script
  or its Lean at elaboration
  ([#197](https://github.com/jackChallis/stoicheia/issues/197)). origin/main's
  copies are taken out again by a reset to the commit, never to HEAD. A new
  extension, top-level folder, executable or named file is a change to the check, landing
  first, in a pull request of its own; and since step 3 judges every commit a pull request
  brings by origin/main's standard, an entry is taken out of a list only when no open
  branch's history still holds a path it allows, or once that branch is rebuilt without
  it.

  This entry approves each protected file the change touches, each in a sentence here.
  It approves the change to `.github/workflows/ci.yml`, whose check job runs the path
  check's cases and then the check itself, first of all.
  It approves the new script `scripts/check_paths.py`, which states the standard as code.
  It approves the change to `scripts/negative_tests.py`, which plants the eight path
  faults above in a copy of the index.
  It approves the change to `scripts/safe_push.py`, whose step 3 holds both paths guards
  and whose every pass of the checks begins at the commit.
  It approves the change to `scripts/test_safe_push.py`, which plants each twin, setting
  and file above in a throwaway clone.
  It approves the new test file `tests/test_check_paths.py`, the standard's own cases.
  It approves the change to `tests/test_decision_entries.py`, which verifies every
  baseline decision file remains byte-for-byte unchanged when the renderer runs.
