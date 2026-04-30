#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-.}"

if ! find "$ROOT" \( -name .lake -o -name .git \) -prune -o \
    -name '*.lean' ! -name 'Challenge.lean' -print -quit | grep -q .; then
  echo "No Lean files found under $ROOT"
  exit 0
fi

matches=$(grep -RnwE --include='*.lean' --exclude-dir='.lake' --exclude-dir='.git' \
  --exclude='Challenge.lean' '\b(sorry|admit|axiom|unsafe)\b' "$ROOT" || true)
if [[ -n "$matches" ]]; then
  echo "$matches"
  echo
  echo "Placeholders found in proof Lean files."
  exit 1
fi

echo "No sorry/admit/axiom/unsafe placeholders found in proof Lean files."
