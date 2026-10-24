- **The landing tool's tests read no global ignore or attributes file of the machine's
  ([#376](https://github.com/jackChallis/stoicheia/issues/376)).** Since
  [#360](https://github.com/jackChallis/stoicheia/issues/360),
  `scripts/test_safe_push.py` shuts out git's global and system configuration, but git
  reads its default global ignore and attributes files all the same:
  `$XDG_CONFIG_HOME/git/ignore` and `$XDG_CONFIG_HOME/git/attributes`, or those under
  `~/.config/git/` when `XDG_CONFIG_HOME` is unset. The
  [entry of 22 October](2026-10-22-test-module-hermetic-git.md) left them to a card of
  their own, and card #376, from the review of #360, asks for them to be shut out too,
  since a rule there could hide a file a test makes from `git status`, and so from the
  dirty-tree and freshness tests. Now `hermetic_git()`, which `setUpModule` calls before
  its first git command, points `XDG_CONFIG_HOME` at an empty directory of its own, made
  under the module's temporary directory and removed with it, and gives
  `core.excludesFile` and `core.attributesFile` the null device through
  `GIT_CONFIG_COUNT`, as `HookEnvironment` gives `core.excludesFile` with `-c`.
  `XDG_CONFIG_HOME` is no variable of git's, so every process the tests start inherits
  it, `safe_push.py`'s own git, its checks, the pre-push hook and the launcher among them.
  `GIT_CONFIG_COUNT` reaches every git started with the module's environment as it is,
  but `safe_push.py` and the launcher drop it with git's other repository variables, so
  there `XDG_CONFIG_HOME` alone shuts the files out. `HOME` stays the runner's.

  `HermeticModule`, the class that runs the module in a process of its own, gains a
  planted case. Under a `HOME` of the test's own, never the user's, a global ignore file
  and a global attributes file name `new.txt`, the file that `Registry`'s test of an
  `empty` check makes, whose `git status --porcelain` must list it; they are planted
  under a fake `XDG_CONFIG_HOME`, and then under the fake `HOME`'s `.config` with
  `XDG_CONFIG_HOME` unset. For each, the case first shows the plant live, git as #360
  left the module's ignoring the file and unsetting its `diff`, then runs that test and a
  new one, which finds a new file listed by the module's `git status` and by
  `safe_push.py`'s, matched by no ignore rule and given no attribute; both pass. With the
  change taken out, in a scratch clone, both placements failed, each with both tests
  failing. With `XDG_CONFIG_HOME` alone taken out, the new test failed on
  `safe_push.py`'s `git status`. With `GIT_CONFIG_COUNT` alone taken out, the case
  passed: that setting is a second guard, for a git that keeps the module's
  `GIT_CONFIG_COUNT` but is given another `XDG_CONFIG_HOME`, which no test does today.

  `safe.directory` is documented, not set. With the global and system configuration shut
  out, git takes it only from its command line or `GIT_CONFIG_COUNT`, so a checkout
  owned by another user stops `setUpModule` at its first git command, with git's
  "detected dubious ownership", and the docstring of `hermetic_git()` says to run the
  tests as the checkout's owner. A `safe.directory=*` in the module's environment would
  let every git the tests start use a repository another user owns, which is what git's
  check of ownership is there to prevent; the tests' own clones are made by the user who
  runs them and need none, and no workflow runs the tests in a container.

  This entry approves the change to `scripts/test_safe_push.py`: `hermetic_git()`, which
  now takes the directory it points `XDG_CONFIG_HOME` at; `setUpModule`, which makes its
  temporary directory before calling it; and `HermeticModule`, with its two new tests and
  the helper that rebuilds a runner's environment, which its first test now uses too.
