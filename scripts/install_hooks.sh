#!/bin/sh
# Install Stoicheia's git hook and launcher into the repository you run this in:
#
#     sh scripts/install_hooks.sh            # refuses to replace a hook of your own
#     sh scripts/install_hooks.sh --force    # keeps yours as pre-push.local-backup
#
# Run it from a checkout of origin/main: what it installs is copied from this checkout.
#
# scripts/hooks/pre-push refuses every push to main (main changes only by a pull request's
# merge commit), scans a push to any other branch for secrets with origin/main's scan, and
# refuses a tag pushed or deleted without the owner's OK, scanning one pushed with it
# (docs/WORKFLOW.md, "Landing work: pull requests"). It goes where git looks for hooks
# (`git rev-parse --git-path hooks`), shared by every worktree of the clone.
#
# scripts/hooks/safe-push, the launcher, goes outside the tracked tree, at
# $(git rev-parse --git-common-dir)/stoicheia/safe-push, with the alias `git safe-push`
# in the clone's config: it runs origin/main's scripts/safe_push.py, never the
# checkout's, so a branch cannot weaken the harness that judges it.
#
# Both are copied, not linked, so they keep working when the worktree they came from is
# removed; run this again after either changes (safe_push notes it when an installed copy
# differs from origin/main's).
set -eu

here=$(cd "$(dirname "$0")" && pwd)
force=0
[ "${1:-}" = "--force" ] && force=1

top=$(git rev-parse --show-toplevel)
hooks=$(cd "$top" && git rev-parse --git-path hooks)
case "$hooks" in
    /*) ;;
    *) hooks="$top/$hooks" ;;
esac
target="$hooks/pre-push"
mkdir -p "$hooks"

if [ -e "$target" ] && ! grep -q STOICHEIA_SAFE_PUSH "$target"; then
    if [ "$force" -ne 1 ]; then
        echo "install_hooks: $target exists and is not Stoicheia's; rerun with --force to" >&2
        echo "replace it (it is kept as pre-push.local-backup)." >&2
        exit 1
    fi
    mv "$target" "$target.local-backup"
fi

cp "$here/hooks/pre-push" "$target"
chmod +x "$target"
echo "install_hooks: installed $target"

common=$(cd "$top" && git rev-parse --path-format=absolute --git-common-dir)
launcher="$common/stoicheia/safe-push"
mkdir -p "$common/stoicheia"
cp "$here/hooks/safe-push" "$launcher"
chmod +x "$launcher"
# A shell alias runs at the top of the worktree, where --git-common-dir is right.
git -C "$top" config --local alias.safe-push \
    '!sh "$(git rev-parse --path-format=absolute --git-common-dir)/stoicheia/safe-push"'
echo "install_hooks: installed $launcher, run as git safe-push"
