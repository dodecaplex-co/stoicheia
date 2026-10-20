#!/bin/sh
set -eu

if [ "$#" -ne 2 ]; then
    echo "usage: $0 SOURCE TARGET" >&2
    exit 2
fi

source_tree=$1
target_tree=$2

rsync -a --delete "$source_tree/scripts/" "$target_tree/scripts/"
rsync -a --delete --exclude=/certificate_expectations.json \
    --exclude=/model/lock.sha256 --exclude=/model/laws.toml \
    --exclude=/model/MODEL.md --exclude=/model/results/ \
    "$source_tree/tests/" "$target_tree/tests/"
rsync -a --delete --exclude=/axioms.lock \
    "$source_tree/Certificate/" "$target_tree/Certificate/"
cp "$source_tree/review/SCHEMA.md" "$source_tree/review/terms.toml" \
    "$target_tree/review/"
