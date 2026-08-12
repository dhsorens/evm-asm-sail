#!/usr/bin/env bash
# One-time setup after cloning: provision submodules and the Sail Lean support
# library that the upstream evm-sail extraction requires as a path dependency.
#
# Upstream's `make extract-lean` clones lean-sail at the branch the backend
# expects (`v4`); we pin the exact revision instead so builds are reproducible.
# This is the same commit evm-asm pins for its own vendored Sail model.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

LEAN_SAIL_GIT="https://github.com/rems-project/lean-sail"
LEAN_SAIL_REV="79b4d08505af29d88b3918f32d29840fae1fa191" # branch v4
LEAN_SAIL_DEST="$REPO_ROOT/extraction/evm-sail/extractions/lean/src/.lake/packages/Sail"

git -C "$REPO_ROOT" submodule update --init extraction/evm-sail

if [ ! -f "$LEAN_SAIL_DEST/lakefile.toml" ]; then
    mkdir -p "$(dirname "$LEAN_SAIL_DEST")"
    git clone "$LEAN_SAIL_GIT" "$LEAN_SAIL_DEST"
fi
git -C "$LEAN_SAIL_DEST" fetch -q origin "$LEAN_SAIL_REV"
git -C "$LEAN_SAIL_DEST" checkout -q "$LEAN_SAIL_REV"

echo "setup: lean-sail @ $(git -C "$LEAN_SAIL_DEST" rev-parse --short HEAD) provisioned"
