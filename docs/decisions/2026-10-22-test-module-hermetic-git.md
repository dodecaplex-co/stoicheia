- **The landing tool's tests read no git variable of the runner's
  ([#360](https://github.com/jackChallis/stoicheia/issues/360)).**
  `scripts/test_safe_push.py`'s own git (its `git()` helper, `clean_env()` and the
  commands it runs directly) inherited the runner's environment. Run under a hook, whose
  `GIT_DIR` and `GIT_INDEX_FILE` name the hook's repository, `setUpModule` cloned that
  repository in place of the checkout and committed "The harness under test" into it,
  with the test identity written into its configuration, as the review of
  [#355](https://github.com/jackChallis/stoicheia/issues/355) saw. A global
  `core.hooksPath` could reach them too: its hooks ran on the tests' commits, and
  `install_hooks.sh` installs where it points. Now `setUpModule` first
  removes every `GIT_*` variable from the test process's environment and shuts out the
  global and system configuration (`GIT_CONFIG_NOSYSTEM=1`, `GIT_CONFIG_GLOBAL` the null
  device), so the module's git and every process it starts find their repository by the
  working directory and read only that repository's configuration. Git's default global
  ignore and attributes files, under `XDG_CONFIG_HOME`, are still read; they are left to a
  card of their own. A test that needs one
  of git's variables, a replacement's `GIT_REPLACE_REF_BASE` or a hook's `GIT_DIR`, sets
  it itself, as each does. A new test runs the module itself, one test of it, from
  a linked worktree under a hook's `GIT_DIR` and `GIT_INDEX_FILE` with the machine's own
  configuration, and finds the repository's HEAD, index, files and shared configuration
  as they were; without the change, that run detached the worktree's HEAD, committed on
  it, and wrote the test identity into the shared configuration.

  This entry approves the change to `scripts/test_safe_push.py`, whose `setUpModule`
  calls the new `hermetic_git()` first and whose new class `HermeticModule` runs the
  planted test.
