#!/usr/bin/env bash
set -euo pipefail

if [ ! -f Scratch/Discovery.lean ]; then
  echo "Scratch/Discovery.lean not found. Run from the project root after copying the kit."
  exit 1
fi

lake env lean Scratch/Discovery.lean
