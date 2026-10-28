#!/usr/bin/env bash
# Install Lean for a CI job on GitHub's ubuntu-latest, Linux on x86_64:
#
#     bash scripts/install_lean.sh
#
# Run it at the top of a checkout. It installs elan v4.2.4, checked against the SHA-256 of
# its release, with no default toolchain, and puts elan's bin/ on the job's PATH; then the
# toolchain that lean-toolchain names, and model/lean-toolchain's if that is another; and
# it ends by asking `lean --version`, in the checkout and in model/, for the version each
# file names. On any other system or machine, a toolchain that is not a release of
# leanprover/lean4, or another hash, it fails.
#
# The toolchains live in ~/.elan/toolchains, which the job's step before this one,
# actions/cache, restores, keyed on the two files, and saves after a job that passes. A
# toolchain found there is used as it is, and nothing is downloaded for it. One not found
# is installed by elan, from releases.lean-lang.org, in three tries at most, 15 and then
# 30 seconds apart, each stopped after 90 seconds; if all three fail, it is taken from
# GitHub's copy of the same file, the release asset releases.lean-lang.org redirects to,
# and unpacked where elan keeps it (#594; docs/decisions/2026-10-27-lean-install-outage.md).
# A stalled host therefore costs at most about five minutes before GitHub's copy, not a
# job's whole time: the 90 seconds bound too the two reads elan makes before the download
# and gives no limit of its own, a check for a newer elan and the index of releases, from
# release.lean-lang.org.
set -euo pipefail

elan_version=4.2.4
elan_sha256=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63
home="$HOME/.elan"

fail() {
    echo "install_lean: $*" >&2
    exit 1
}

# A download that gives up on a connection not made in 20 seconds, a transfer slower than
# 100 kB a second for 20 seconds (a stall), or a try longer than 5 minutes, and that tries
# again on any error, with curl's own growing pauses, starting no try after 10 minutes.
fetch() {
    curl -sSfL --connect-timeout 20 --speed-limit 100000 --speed-time 20 --max-time 300 \
        --retry 5 --retry-all-errors --retry-max-time 600 -o "$2" "$1"
}

if [ "$(uname -s)" != Linux ] || [ "$(uname -m)" != x86_64 ]; then
    fail "the pinned elan is for Linux on x86_64, not $(uname -s) on $(uname -m)"
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
fetch "https://github.com/leanprover/elan/releases/download/v$elan_version/elan-x86_64-unknown-linux-gnu.tar.gz" \
    "$work/elan.tar.gz"
echo "$elan_sha256  $work/elan.tar.gz" | sha256sum -c -
tar -xzf "$work/elan.tar.gz" -C "$work"
"$work/elan-init" -y --default-toolchain none
export PATH="$home/bin:$PATH"
if [ -n "${GITHUB_PATH:-}" ]; then
    echo "$home/bin" >> "$GITHUB_PATH"
fi
mkdir -p "$home/toolchains" "$home/tmp"

# Each file, the toolchain it names and that toolchain's version, the second only when it
# names another toolchain.
files=(lean-toolchain)
if [ "$(tr -d '[:space:]' < model/lean-toolchain)" != "$(tr -d '[:space:]' < lean-toolchain)" ]; then
    files+=(model/lean-toolchain)
fi
for file in "${files[@]}"; do
    name=$(tr -d '[:space:]' < "$file")
    if ! [[ $name =~ ^leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?)$ ]]; then
        fail "$file names '$name', which is not a release of leanprover/lean4"
    fi
    version=${BASH_REMATCH[1]}
    # Where elan keeps it: leanprover/lean4:v4.35.0 in leanprover--lean4---v4.35.0.
    dir=${name//\//--}
    dir="$home/toolchains/${dir//:/---}"
    if [ -x "$dir/bin/lean" ]; then
        echo "install_lean: $name restored from the cache; nothing downloaded for it"
        continue
    fi
    # elan locks and unpacks beside <dir>, under names that replace <dir>'s last dot and
    # what follows it (Rust's with_extension, which ${dir%.*} matches): for v4.35.0 or
    # v4.35.0-rc1, leanprover--lean4---v4.35.lock and leanprover--lean4---v4.35.tmp. It
    # renames the unpack into <dir>, so a try stopped part way leaves no part of a
    # toolchain in <dir>, but may leave those two beside it. GitHub's copy is taken
    # whenever no try succeeded; it replaces whatever is in <dir> and removes the two, so
    # that the cache saves the toolchain alone.
    installed=no
    for try in 1 2 3; do
        if timeout -k 10 90 elan toolchain install "$name"; then
            echo "install_lean: $name installed by elan, try $try"
            installed=yes
            break
        fi
        if [ "$try" -lt 3 ]; then
            sleep $((15 * try))
        fi
    done
    if [ "$installed" = no ]; then
        echo "install_lean: elan could not install $name in three tries; taking GitHub's copy"
        fetch "https://github.com/leanprover/lean4/releases/download/v$version/lean-$version-linux.tar.zst" \
            "$work/lean.tar.zst"
        unpacked=$(mktemp -d "$home/tmp/github.XXXXXX")
        zstd -dc "$work/lean.tar.zst" | tar -xf - -C "$unpacked"
        [ -x "$unpacked/lean-$version-linux/bin/lean" ] ||
            fail "GitHub's copy of $name has no bin/lean"
        rm -rf "$dir" "${dir%.*}.tmp" "${dir%.*}.lock"
        mv "$unpacked/lean-$version-linux" "$dir"
        rm -rf "$unpacked" "$work/lean.tar.zst"
        echo "install_lean: $name taken from GitHub's copy"
    fi
done

# The toolchain each file names, as elan resolves it where the file stands.
for file in lean-toolchain model/lean-toolchain; do
    name=$(tr -d '[:space:]' < "$file")
    version=${name#leanprover/lean4:v}
    said=$(cd "$(dirname "$file")" && lean --version)
    case "$said" in
        "Lean (version $version,"*) echo "install_lean: $file: $said" ;;
        *) fail "$file names $name, but lean --version says: $said" ;;
    esac
done
