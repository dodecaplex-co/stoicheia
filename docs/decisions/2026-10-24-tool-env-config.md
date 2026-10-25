- **A train's checks keep the variables that name or shut out git's configuration and
  attributes files ([#430](https://github.com/jackChallis/stoicheia/issues/430)).** Since
  [#355](2026-10-22-tool-env-no-git-variables.md), `safe_push.tool_env()`, which builds
  the environment that each check of the pre-flight starts with, has kept no `GIT_*`
  variable but `GIT_NO_REPLACE_OBJECTS`, so that a hook's `GIT_DIR`, `GIT_INDEX_FILE`
  and their kin cannot send a check to the hook's repository. With them it dropped four
  variables that tie git to no repository: `GIT_CONFIG_GLOBAL` and `GIT_CONFIG_SYSTEM`,
  which name the global and system configuration files, and `GIT_CONFIG_NOSYSTEM` and
  `GIT_ATTR_NOSYSTEM`, which shut out the system configuration and the system attributes
  file. So a check read `~/.gitconfig` and the system configuration even where the
  caller had shut them out, as the landing tool's tests do with `hermetic_git()`, and
  the system attributes file even where the caller had set `GIT_ATTR_NOSYSTEM`. TS's
  review of [#376](https://github.com/jackChallis/stoicheia/issues/376), whose
  [entry](2026-10-24-hermetic-xdg.md) names the gap, found it on 24 October, and card
  #430 records it, as a gap in the tests' hermetic intent and not a known failure.

  Now `tool_env()` keeps those four as the caller gives them, named in a new set,
  `CONFIG_FILE_VARIABLES`, beside `GIT_NO_REPLACE_OBJECTS`. None of them is in
  `REPOSITORY_VARIABLES`, or in the list that `git rev-parse --local-env-vars` prints, so
  safe_push's own git, which drops only those, keeps all four, and a check now reads the
  same configuration files as that git. Each was weighed on its own:
  - `GIT_CONFIG_GLOBAL` is kept. The file it names may set `core.hooksPath`,
    `safe.directory`, a url rewrite or an `includeIf`; dropped, git reads `~/.gitconfig`
    in its place, which may set the same, and which the caller chooses as well, by the
    `HOME` and `XDG_CONFIG_HOME` that `tool_env()` keeps. A relative path in it is read
    from the top of the repository the check's git works in, and so is a relative `HOME`.
  - `GIT_CONFIG_SYSTEM` is kept, for the same reason: dropped, git reads the system file
    of the git that the caller's `PATH` finds.
  - `GIT_CONFIG_NOSYSTEM` and `GIT_ATTR_NOSYSTEM` are kept: each only takes a file away
    from what git reads.

  Every other variable of git's stays dropped. `GIT_CONFIG_COUNT` and
  `GIT_CONFIG_PARAMETERS`, which carry settings themselves, stay in
  `REPOSITORY_VARIABLES`, so neither reaches a check or any command safe_push runs
  itself. The main-checks cache's key still leaves git's own settings out, as the
  [cache's entry](2026-10-21-main-checks-cache.md) of 21 October records.

  The test module now sets `GIT_ATTR_NOSYSTEM=1` too, in `hermetic_git()`, which
  `setUpModule` calls, beside what #360 and #376 set; so do the environments that
  `HookEnvironment`, `OwnGitUnderHook` and the launcher's test of #359 build for the git
  they run. `HookEnvironment`, the class that tests the checks' environment, gains two
  tests. The first sets the four variables, each of `REPOSITORY_VARIABLES`, and a
  `GIT_CONFIG_KEY_0` with its value in the caller's environment, and finds that
  `tool_env()` keeps the four as given and `GIT_NO_REPLACE_OBJECTS`, and nothing else of
  git's, `GIT_DIR`, `GIT_INDEX_FILE` and `GIT_CONFIG_COUNT` among what it drops; and that
  none of the four is in `REPOSITORY_VARIABLES` or the list git prints. The second plants
  a setting in the `.gitconfig` of a `HOME` of the test's own, never the user's, another
  in a file that `GIT_CONFIG_SYSTEM` names, and the same two keys again, one through each
  of the caller's `GIT_CONFIG_COUNT` and `GIT_CONFIG_PARAMETERS`. It shows each plant live
  in a check started directly, then starts the check as the pre-flight starts one: under
  a `GIT_CONFIG_GLOBAL` naming an empty file, the check does not see the `HOME` setting;
  under `GIT_CONFIG_NOSYSTEM`, it does not see the system file's; it never sees the
  settings the caller's `GIT_CONFIG_COUNT` and `GIT_CONFIG_PARAMETERS` carry; and with no
  `GIT_CONFIG_GLOBAL`, it sees the `HOME` setting, as git reads it for any caller that
  names no file. The class's two tests of a check under a hook now expect it to keep, of
  git's variables, `GIT_NO_REPLACE_OBJECTS` and the three with which the class shuts
  git's configuration and attributes files out, where they expected
  `GIT_NO_REPLACE_OBJECTS` alone, an expectation as exact as before.

  `HermeticModule` gains a test that reads git's own report of the system attributes
  file it would read, `git var GIT_ATTR_SYSTEM`: none, for the module's git, for
  safe_push's own and for a check started through `tool_env()`; and, with the variable
  taken away, a file each time. It plants no system attributes file, for git reads that
  file from where it was built to look, `/etc/gitattributes` for Apple's git, which only
  root may write, and git documents no variable that names another in its place, as
  `GIT_CONFIG_SYSTEM` does for the system configuration. With `tool_env()` as it was, in
  a scratch clone, `HookEnvironment`'s four tests and that new test failed, the planted
  check reading the `HOME` setting under the empty `GIT_CONFIG_GLOBAL`. With
  `scripts/safe_push.py` as main holds it, the same five failed. With `GIT_ATTR_NOSYSTEM`
  taken out of `hermetic_git()` alone, the new test of `HermeticModule` failed. With the
  change in place, all five pass.

  This entry approves the change to `scripts/safe_push.py`, in which `tool_env()` keeps
  the variables of the new `CONFIG_FILE_VARIABLES` beside `KEPT_GIT_VARIABLES`, with the
  comments and docstrings that describe what the checks keep.

  This entry also approves the change to `scripts/test_safe_push.py`, in which
  `hermetic_git()` and three environments that tests build for themselves set
  `GIT_ATTR_NOSYSTEM`, `HookEnvironment` gains its two tests and its changed expectations,
  and `HermeticModule` gains its new test, with a `runner_env()` that takes
  `GIT_ATTR_NOSYSTEM` away too, and the docstrings that describe them.
