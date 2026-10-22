- **The harness reads git with replacement objects off
  ([#256](https://github.com/jackChallis/stoicheia/issues/256)).** Git honours replacement
  objects: given a ref under `refs/replace/`, or under the folder that
  `GIT_REPLACE_REF_BASE` names, `git show`, `git cat-file`, `git diff`, `git log -p` and
  the rest read a stand-in in place of the object it replaces, while `git push` sends the
  original. A token committed and then given a clean stand-in therefore passed the
  pre-push scan and the pre-flight's secret scan alike, and a stand-in for origin/main's
  `scripts/safe_push.py` could be run in its place by the pre-push hook, copied out and
  run by the launcher, or taken for origin/main's own by the hand-over. A trial in a
  throwaway repository bore out the push: with the token's blob replaced, the bare
  repository pushed to received the original blob, token and all, and neither the stand-in
  nor the replacement's ref. So every git command `safe_push.py` runs itself, through its
  `run()`, now reads with `GIT_NO_REPLACE_OBJECTS=1`, without `GIT_REPLACE_REF_BASE` and
  with `-c core.useReplaceRefs=false`, whatever the caller's environment holds, and so
  does every git command the pre-push hook and the launcher run: the scan reads what the
  push sends, and the harness that runs is origin/main's. The `-c` is for git from 2.19 to
  2.41, which let `core.useReplaceRefs=true` in any configuration git read, the
  repository's own among it, turn replacements back on despite the variable; git reads
  configuration given on its command line last. It was tested only with the git installed
  here, 2.50.1, on which the variable already wins: a trial with the variable taken out of
  `run()` and the hooks showed the `-c` alone refusing each planted token, but no git
  before 2.42 was run.
  In [`scripts/safe_push.py`](../../scripts/safe_push.py), `run()` gives every git command
  that environment and puts the `-c` right after `git`, and the hand-over to origin/main's
  harness passes on the variable, without `GIT_REPLACE_REF_BASE`, so that an older
  harness, whose `run()` does neither, inherits both.
  [`scripts/hooks/pre-push`](../../scripts/hooks/pre-push) exports the variable and unsets
  `GIT_REPLACE_REF_BASE` before its first git call, gives each of its git calls the `-c`,
  and runs origin/main's scan, which inherits the variable.
  [`scripts/hooks/safe-push`](../../scripts/hooks/safe-push), the launcher, does the same
  before it copies out origin/main's harness and runs it.
  [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) plants a token behind a
  stand-in, by `git replace` and by `GIT_REPLACE_REF_BASE`, for the hook and for the
  pre-flight, and again by `git replace` with `core.useReplaceRefs=true` in the clone's
  configuration; a commit whose message holds a token, behind a clean commit, and a
  stand-in for origin/main's allow-list that would allow a token by its SHA-256, for the
  pre-flight; a stand-in for origin/main's harness, for the hook, the launcher and the
  hand-over; and a clean push beside a replacement, which passes; each test removes what
  it planted. Its unit tests check that `run()` gives a git command, and no other program,
  the `-c` and that environment, and that `without_replacements` drops
  `GIT_REPLACE_REF_BASE` and sets the variable to 1 whatever it held.
  [`scripts/negative_tests.py`](../../scripts/negative_tests.py) gains a plant that needs
  no build: in a temporary repository of its own, a token behind either kind of stand-in
  is refused by `safe_push.py --scan-push`, and the repository's clean commit passes while
  each stand-in is live.
  [WORKFLOW](../WORKFLOW.md) says where the scan, the hook and the launcher read with
  replacements off, what the checks are given, and that an installed hook or launcher
  takes the change only when `sh scripts/install_hooks.sh` is run again from a checkout of
  origin/main.
  What remains is not this entry's. The programs the pre-flight runs as checks are not
  among the git commands `safe_push.py` runs itself, though its `git status` check is
  one: they keep the environment `tool_env()` copies, so under the launcher or after a
  hand-over they get the variable too, and otherwise only if the caller set it, and they
  are not given the `-c`; `check_acceptance.py`, the only check that reads git's objects
  for its verdict, is [#237](https://github.com/jackChallis/stoicheia/issues/237)'s. And
  [#218](https://github.com/jackChallis/stoicheia/issues/218) stays open. Its third item
  asks for replacement objects off in all of safe_push's own git calls, which `run()` now
  gives, and for `core.fsmonitor` pinned off there too, which this entry leaves to it. No
  check is loosened.
