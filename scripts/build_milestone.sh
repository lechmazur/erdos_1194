#!/usr/bin/env bash
set -euo pipefail

milestone="${1:?usage: scripts/build_milestone.sh M0|M1|M2|M3|M4|M5|M6|all}"

case "$milestone" in
  M0|M1)
    lake build FloorSaving.Basic
    ;;
  M2)
    lake build FloorSaving.UniqueDiff
    ;;
  M3)
    lake build FloorSaving.PhiPsiData
    lake build FloorSaving.AnalyticInterfaces
    lake build FloorSaving.Counting
    ;;
  M4|M5)
    lake build FloorSaving.Counting
    ;;
  M6)
    lake build FloorSaving.MainSkeleton
    ;;
  all)
    scripts/build_targets.sh
    ;;
  *)
    echo "Unknown milestone: $milestone" >&2
    exit 1
    ;;
esac
