#!/usr/bin/env bash
set -euo pipefail

PROJECT_NAME="${1:-FloorSavingProject}"

if command -v elan >/dev/null 2>&1; then
  elan --version || true
else
  echo "elan is not installed. Install Lean using the current instructions at https://lean-lang.org/install/" >&2
  exit 1
fi

lake +leanprover-community/mathlib4:lean-toolchain new "$PROJECT_NAME" math
cd "$PROJECT_NAME"
lake exe cache get
lake build

echo "Project created at $PROJECT_NAME"
