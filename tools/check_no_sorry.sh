#!/usr/bin/env bash
set -euo pipefail

if grep -R --line-number --include='*.lean' -E '\b(sorry|admit|axiom|unsafe)\b' FloorSaving.lean FloorSaving; then
  echo "Found sorry/admit/axiom/unsafe occurrences." >&2
  exit 1
fi

echo "No sorry/admit/axiom/unsafe occurrences found in FloorSaving Lean files."
