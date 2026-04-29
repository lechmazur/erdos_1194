#!/usr/bin/env bash
set -euo pipefail

PATTERN="${1:?usage: tools/list_decls.sh PATTERN}"
ROOT=".lake/packages/mathlib/Mathlib"

if [ ! -d "$ROOT" ]; then
  echo "Mathlib source directory not found at $ROOT" >&2
  exit 1
fi

grep -R --line-number "$PATTERN" "$ROOT" | head -100
