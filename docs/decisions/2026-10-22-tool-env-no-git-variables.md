- **A train's checks discard a hook's repository variables
  ([#355](https://github.com/jackChallis/stoicheia/issues/355)).** `safe_push.tool_env()`,
  the environment of every program the pre-flight runs as a check, copied the caller's whole
  environment, so under a hook it carried `GIT_DIR`, `GIT_INDEX_FILE` and their kin, naming
  the repository the hook runs in. A check that builds a repository of its own, with
  `git init`, `git add` and `git commit`, then acted on that one unless it cleared them
  itself. On 22 October a test on one train's branch did exactly that: its fixture
  committed into the train's branch, and its `git init`, with `GIT_DIR` naming a linked
  worktree's git directory, took the repository for a bare one and wrote
  `core.bare = true` into the main clone's shared configuration. The safety boundary now
  sits at the pre-flight: `tool_env()` keeps no variable of git's but
  `GIT_NO_REPLACE_OBJECTS`, present under the launcher or after a hand-over and otherwise
  only if the caller set it, so every program it launches as a check finds its repository
  by its working directory. The git commands safe_push runs itself are unchanged. This
  replaces only the [earlier entry's](2026-10-21-scan-no-replace.md) account of the
  checks' inherited environment; its rules for safe_push's own git commands stand.

  This entry approves the change to `scripts/safe_push.py`, whose `tool_env()` drops every
  `GIT_*` variable but those `KEPT_GIT_VARIABLES` names.

  This entry approves the change to `scripts/test_safe_push.py`, whose new class
  `HookEnvironment` runs a check that builds and commits to a repository of its own under
  a hook's `GIT_DIR` and `GIT_INDEX_FILE` naming a linked worktree's git directory, the
  incident's shape, and again with `GIT_WORK_TREE`, and finds the enclosing repository's
  HEAD, index, shared configuration and files as they were.
