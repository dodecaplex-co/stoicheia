- **safe_push's own commands get no variable that ties git to one repository, but
  `GIT_NO_REPLACE_OBJECTS`
  ([#357](https://github.com/jackChallis/stoicheia/issues/357)).** The
  [entry for #355](2026-10-22-tool-env-no-git-variables.md) took git's variables, all but
  `GIT_NO_REPLACE_OBJECTS`, from the programs the pre-flight runs as checks, but
  safe_push's own commands still ran through `run()` in the caller's environment. Under a
  hook's `GIT_DIR` and `GIT_INDEX_FILE` naming a train's linked worktree, the review of
  #355 found `git worktree add`, which makes the pre-flight's temporary worktree, checking
  the commit out into the train's own index: a change staged there was lost. The
  `git status` check then read that index, and was right only because the commit had just
  been written into it. Now no command safe_push runs itself, git's or another's, gets one
  of `REPOSITORY_VARIABLES` but `GIT_NO_REPLACE_OBJECTS`. That list is git's own list of
  the variables that tie it to one repository, as `git rev-parse --local-env-vars` prints
  it (`GIT_DIR`, `GIT_INDEX_FILE`, `GIT_WORK_TREE`, `GIT_COMMON_DIR`,
  `GIT_OBJECT_DIRECTORY` and the rest), with `GIT_INTERNAL_SUPER_PREFIX`, which older git
  printed too. Each command finds its repository by its working directory, as the checks
  do, and so do origin/main's `risk.py`, which classes the change, and origin/main's
  harness after a hand-over; `gh pr checks --watch`, which is given its repository by
  `-R`, gets none of them but `GIT_NO_REPLACE_OBJECTS` either. `GIT_NO_REPLACE_OBJECTS`
  stays where it was: every git command safe_push runs itself gets it set to 1, with the
  `-c` of the
  [entry for #256](2026-10-21-scan-no-replace.md), whose rules stand, and a check gets it
  as `tool_env()` keeps it, so under the launcher or after a hand-over the checks still
  have it, as that entry says. origin/main's `risk.py` now always gets it set to 1 too,
  where it inherited the caller's value. The list holds `GIT_CONFIG_PARAMETERS` and
  `GIT_CONFIG_COUNT` too, so a setting given as `git -c key=value safe-push` (a proxy for
  the fetch, say) no longer reaches safe_push's own git; one is set in the repository's
  configuration instead. Other variables of git's, such as `GIT_SSH_COMMAND` for a push,
  are kept, since they say how git works rather than which repository it works on.
  safe_push finds its repository from the working directory it is run in, as
  `git rev-parse --show-toplevel` gives it there: run outside a repository with a
  `GIT_DIR` naming one, it refuses ("run it inside the repository"), and run inside one,
  it never follows a `GIT_DIR` naming another. Besides `GIT_NO_REPLACE_OBJECTS`, the one
  such variable the harness sets on purpose, the temporary `GIT_INDEX_FILE` in which
  `base_tree` builds the base tree for the main-checks cache
  ([#392](https://github.com/jackChallis/stoicheia/pull/392)), is named to `run()` in
  `keep`, and its environment is otherwise built by `own_env()`; only `base_tree` names
  it, as a test of the source holds, and a test of its commands, run under the caller's
  repository variables, sees each index command use that temporary index alone.

  This entry approves the change to `scripts/safe_push.py`, whose `run()`,
  `without_replacements()`, `risk_class()` launch, CI watch and hand-over give no command
  any of the caller's `REPOSITORY_VARIABLES` but `GIT_NO_REPLACE_OBJECTS`, and the
  temporary `GIT_INDEX_FILE` that `base_tree` names to `run()` in `keep`.

  This entry approves the change to `scripts/test_safe_push.py`: its new class
  `OwnGitUnderHook` runs a dry run from a train's linked worktree under a hook's `GIT_DIR`
  and `GIT_INDEX_FILE`, and again with `GIT_WORK_TREE`, and finds the train's HEAD, index,
  staged change and the shared configuration as they were; checks `REPOSITORY_VARIABLES`
  against git's own list; checks with `test_run_gives_no_command_a_repository_variable`
  what `run()` gives a git command, another program and a check started with `tool_env()`,
  and that a variable named in `keep` passes while every other is dropped; checks, reading
  the source, that only `base_tree` names one in `keep`, its temporary `GIT_INDEX_FILE`;
  checks, reading the environments its commands are given, that `base_tree` makes the
  expected tree through its temporary index, leaves the caller's and the repository's
  indexes unchanged and passes no other repository variable; and checks, reading the
  source, that each place safe_push starts a process, `run()`'s own among them, gives it
  an environment built by `own_env()` or `without_replacements()`, directly or by a name
  every binding of which in its function is one of those calls and which nothing there
  changes afterwards (no item stored or deleted, no `update()` or the like), and that none
  uses a function that takes no environment. `HookEnvironment`'s planted check now also
  records the git variables it is started with, which must be `GIT_NO_REPLACE_OBJECTS=1`
  alone. And the unit test of `run()` now expects a program other than git to get the
  caller's environment less those variables but `GIT_NO_REPLACE_OBJECTS`, which it keeps
  as given, where it expected the caller's environment as it was.
