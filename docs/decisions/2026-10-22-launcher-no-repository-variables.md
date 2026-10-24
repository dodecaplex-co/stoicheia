- **The launcher unsets git's repository variables before its first git command
  ([#359](https://github.com/jackChallis/stoicheia/issues/359)).**
  `scripts/hooks/safe-push`, the launcher behind `git safe-push`, runs `git rev-parse`,
  `git fetch` and `git cat-file` before it runs origin/main's `safe_push.py`, and they
  took the caller's environment. Under a `GIT_DIR` naming another repository it fetched
  that repository's origin into it and copied out and ran its origin/main harness: a test
  that sets up such a repository, with a harness of its own that only marks that it ran,
  saw the mark. The
  [entry for #357](2026-10-22-own-git-no-repository-variables.md) took these variables
  from every command `safe_push.py` runs itself, but the launcher runs before it, and
  `git safe-push` runs origin/main's harness, so that entry could reach launcher runs only
  once it had landed. Now the launcher unsets the same list, `safe_push.py`'s
  `REPOSITORY_VARIABLES` (git's `git rev-parse --local-env-vars`, with
  `GIT_INTERNAL_SUPER_PREFIX`), but `GIT_NO_REPLACE_OBJECTS`, which it sets, and
  `GIT_REPLACE_REF_BASE`, which it already unset (#256), before its first git command.
  Its git and the harness it runs then find the repository by the working directory, as
  `git safe-push` is run from inside it. As for `safe_push.py` since #357, a setting given
  as `git -c key=value safe-push` (a proxy for the fetch, say) no longer reaches the
  launcher's git; one is set in the repository's configuration instead. The change governs
  a launcher once it runs: which launcher `git safe-push` runs is still read from the
  configuration the caller's git finds, and an installed launcher changes only when it is
  installed again (`sh scripts/install_hooks.sh --force`), until when the pre-flight
  notes that it differs from origin/main's. The pre-push hook, `scripts/hooks/pre-push`,
  is unchanged: it runs under `git push`, in the repository pushed from, and the scan it
  runs is `safe_push.py`'s, which drops the variables itself since #357.

  This entry approves the change to `scripts/hooks/safe-push`, which unsets those
  variables before its first git command.

  This entry approves the change to `scripts/test_safe_push.py`, whose new tests run the
  launcher from the test clone under a foreign `GIT_DIR` and `GIT_INDEX_FILE` and find
  that it copied the clone's origin/main harness and never ran the foreign one. They also
  execute the launcher with every `REPOSITORY_VARIABLES` name planted and check the two
  explicit exceptions, `GIT_NO_REPLACE_OBJECTS` and `GIT_REPLACE_REF_BASE`: its first
  git command receives from that set only `GIT_NO_REPLACE_OBJECTS=1`.
