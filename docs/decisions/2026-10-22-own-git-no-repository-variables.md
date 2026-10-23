- **safe_push's own commands get no variable that ties git to one repository
  ([#357](https://github.com/jackChallis/stoicheia/issues/357)).** The
  [entry for #355](2026-10-22-tool-env-no-git-variables.md) took git's variables from the
  programs the pre-flight runs as checks, but safe_push's own commands still ran through
  `run()` in the caller's environment. Under a hook's `GIT_DIR` and `GIT_INDEX_FILE`
  naming a train's linked worktree, the review of #355 found `git worktree add`, which
  makes the pre-flight's temporary worktree, checking the commit out into the train's own
  index: a change staged there was lost. The `git status` check then read that index, and
  was right only because the commit had just been written into it. Now no command
  safe_push runs itself, git's or another's, gets one of `REPOSITORY_VARIABLES`: git's own
  list of the variables that tie it to one repository, as `git rev-parse
  --local-env-vars` prints it (`GIT_DIR`, `GIT_INDEX_FILE`, `GIT_WORK_TREE`,
  `GIT_COMMON_DIR`, `GIT_OBJECT_DIRECTORY` and the rest). Each finds its repository by
  its working directory, as the checks do. So do origin/main's `risk.py`, which classes
  the change, `gh pr checks --watch`, and origin/main's harness after a hand-over. git
  commands still get `GIT_NO_REPLACE_OBJECTS=1` and the `-c` of the
  [entry for #256](2026-10-21-scan-no-replace.md), whose rules stand. Other variables of
  git's, such as `GIT_SSH_COMMAND` for a push, are kept, since they say how git works
  rather than which repository it works on. safe_push finds its repository from the
  working directory it is run in, as `git rev-parse --show-toplevel` gives it there: run
  outside a repository with a `GIT_DIR` naming one, it refuses ("run it inside the
  repository"), and run inside one, it never follows a `GIT_DIR` naming another.

  This entry approves the change to `scripts/safe_push.py`, whose `run()`,
  `without_replacements()`, `risk_class()` launch and CI watch give no command any of the
  `REPOSITORY_VARIABLES` names.

  This entry approves the change to `scripts/test_safe_push.py`, whose new class
  `OwnGitUnderHook` runs a dry run from a train's linked worktree under a hook's
  `GIT_DIR` and `GIT_INDEX_FILE`, and again with `GIT_WORK_TREE`, and finds the train's
  HEAD, index, staged change and the shared configuration as they were, and checks
  `REPOSITORY_VARIABLES` against git's own list; and whose unit test of `run()` now
  expects a program other than git to get the caller's environment less those variables,
  where it expected the caller's environment as it was.
