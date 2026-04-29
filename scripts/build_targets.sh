#!/usr/bin/env bash
set -euo pipefail

targets=(
  FloorSaving.Basic
  FloorSaving.UniqueDiff
  FloorSaving.PhiPsiData
  FloorSaving.AnalyticInterfaces
  FloorSaving.Counting
  FloorSaving.MainSkeleton
  FloorSaving
)

for target in "${targets[@]}"; do
  echo "== lake build $target"
  lake build "$target"
done
