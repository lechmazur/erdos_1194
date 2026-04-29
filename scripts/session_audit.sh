#!/usr/bin/env bash
set -euo pipefail

echo "== Environment =="
tools/lean_env_report.sh || true

echo
echo "== Imports =="
scripts/audit_imports.sh . || true

echo
echo "== Placeholders =="
scripts/audit_sorries.sh . || true
