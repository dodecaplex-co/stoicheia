#!/bin/sh
# Install Stoicheia's git hooks into the repository you run this in:
#
#     sh scripts/install_hooks.sh            # refuses to replace a hook of your own
#     sh scripts/install_hooks.sh --force    # keeps yours as pre-push.local-backup
#
# For now there is one, scripts/hooks/pre-push, which refuses a push to main that does not
# come from scripts/safe_push.py (docs/WORKFLOW.md, section 10). It goes where git looks
# for hooks (`git rev-parse --git-path hooks`), shared by every worktree of the clone. It
# is copied, not linked, so it keeps working when the worktree it came from is removed;
# run this again after the hook changes.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
source="$here/hooks/pre-push"
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

cp "$source" "$target"
chmod +x "$target"
echo "install_hooks: installed $target"
