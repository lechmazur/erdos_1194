#!/usr/bin/env bash
set -euo pipefail

echo "# Lean environment report"
date || true
pwd

echo "\n## Tool versions"
(command -v elan && elan --version) || echo "elan: not found"
(command -v lean && lean --version) || echo "lean: not found"
(command -v lake && lake --version) || echo "lake: not found"

echo "\n## Project files"
ls -la
[ -f lean-toolchain ] && { echo "\nlean-toolchain:"; cat lean-toolchain; }
[ -f lakefile.lean ] && { echo "\nlakefile.lean:"; sed -n '1,120p' lakefile.lean; }
[ -f lakefile.toml ] && { echo "\nlakefile.toml:"; sed -n '1,160p' lakefile.toml; }
[ -f lake-manifest.json ] && { echo "\nlake-manifest.json head:"; sed -n '1,80p' lake-manifest.json; }

echo "\n## Mathlib package location"
find .lake -maxdepth 4 -type d -name Mathlib 2>/dev/null | head -20 || true
