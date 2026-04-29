#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-.}"

echo "Lean imports under $ROOT:"
grep -Rn --include='*.lean' --exclude-dir='.lake' --exclude-dir='.git' '^import ' "$ROOT" || true

echo
echo "Duplicate imports in top-level FloorSaving.lean, if any:"
if [[ -f "$ROOT/FloorSaving.lean" ]]; then
  sort "$ROOT/FloorSaving.lean" | uniq -d || true
fi
