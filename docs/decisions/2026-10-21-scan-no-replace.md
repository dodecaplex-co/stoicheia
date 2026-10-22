- **The harness reads git with replacement objects off
  ([#256](https://github.com/jackChallis/stoicheia/issues/256)).** Git honours
  replacement objects: given a ref under `refs/replace/`, or under the folder that
  `GIT_REPLACE_REF_BASE` names, `git show`, `git cat-file`, `git diff`, `git log -p` and
  the rest read a stand-in in place of the object it replaces, while `git push` sends the
  original. A token committed and then given a clean stand-in therefore passed the
  pre-push scan and the pre-flight's secret scan alike, and a stand-in for origin/main's
  `scripts/safe_push.py` could be run in its place by the pre-push hook, copied out and run
  by the launcher, or taken for origin/main's own by the hand-over. A trial in a throwaway
  repository bore out the push: with the token's blob replaced, the bare repository pushed
  to received the original blob, token and all, and neither the stand-in nor the
  replacement's ref. So every git process the harness starts now runs with
  `GIT_NO_REPLACE_OBJECTS=1` and without `GIT_REPLACE_REF_BASE`, whatever the caller's
  environment holds, and the hook and the launcher set the same before they read
  origin/main's harness: what is scanned is what is pushed, and the harness that runs is
  origin/main's.
  In [`scripts/safe_push.py`](../../scripts/safe_push.py), `run()` gives every git command
  that environment, and the hand-over to origin/main's harness passes it on, so that an
  older harness reads with replacements off too.
  [`scripts/hooks/pre-push`](../../scripts/hooks/pre-push) exports the setting and unsets
  the folder before it copies out origin/main's scan, which inherits both.
  [`scripts/hooks/safe-push`](../../scripts/hooks/safe-push), the launcher, does the same
  before it copies out origin/main's harness and runs it.
  [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) plants a token behind a
  stand-in, by `git replace` and by `GIT_REPLACE_REF_BASE`, for the hook and for the
  pre-flight; a stand-in for origin/main's harness, for the hook, the launcher and the
  hand-over; and a clean push beside a replacement, which passes; each test removes the
  refs it planted.
  [`scripts/negative_tests.py`](../../scripts/negative_tests.py) gains a plant that needs
  no build: in a temporary repository of its own, a token behind either kind of stand-in is
  refused by `safe_push.py --scan-push`, and the repository's clean commit passes.
  [WORKFLOW](../WORKFLOW.md) says where the scan, the hook and the launcher read with
  replacements off, and that an installed hook or launcher takes the change only when
  `sh scripts/install_hooks.sh` is run again.
  What remains is not this entry's. The checks the pre-flight runs keep the environment
  they are given, and their own reading of git is
  [#237](https://github.com/jackChallis/stoicheia/issues/237)'s; and
  [#218](https://github.com/jackChallis/stoicheia/issues/218) stays open. Its third item
  asks for replacement objects off in all of safe_push's own git calls, which `run()` now
  gives, and for `core.fsmonitor` pinned off there too, which this entry leaves to it. No
  check is loosened.
