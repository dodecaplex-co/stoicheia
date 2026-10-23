- **A train's checks never inherit a hook's git variables
  ([#355](https://github.com/jackChallis/stoicheia/issues/355)).** `safe_push.tool_env()`,
  the environment every check of the pre-flight runs with, copied the caller's whole
  environment, so under a hook it carried `GIT_DIR`, `GIT_INDEX_FILE` and their kin, naming
  the repository the hook runs in. A check that builds a repository of its own, with
  `git init`, `git add` and `git commit`, then acted on that one unless it cleared them
  itself. On 22 October a test on one train's branch did exactly that: its fixture
  committed into the train's branch, and its `git init`, with `GIT_DIR` naming a linked
  worktree's git directory, took the repository for a bare one and wrote
  `core.bare = true` into the main clone's shared configuration. Every test on main that
  builds a repository clears those variables itself, so main was safe, but the tool should
  not depend on that. Now `tool_env()` keeps no variable of git's but
  `GIT_NO_REPLACE_OBJECTS`, which safe_push sets on purpose, so each check finds its
  repository by its working directory. The git commands safe_push runs itself are
  unchanged.

  This entry approves the change to `scripts/safe_push.py`, whose `tool_env()` drops every
  `GIT_*` variable but those `KEPT_GIT_VARIABLES` names.

  This entry approves the change to `scripts/test_safe_push.py`, whose new test runs a
  check that builds and commits to a repository of its own under a hook's `GIT_DIR`,
  `GIT_INDEX_FILE` and `GIT_WORK_TREE`, and finds the enclosing repository's HEAD, index,
  configuration and files as they were.
