.PHONY: env discovery build-basic build-unique build-counting build-main build-all audit audit-imports no-sorry

env:
	tools/lean_env_report.sh

discovery:
	scripts/run_discovery.sh

build-basic:
	lake build FloorSaving.Basic

build-unique:
	lake build FloorSaving.UniqueDiff

build-counting:
	lake build FloorSaving.Counting

build-main:
	lake build FloorSaving.MainSkeleton

build-all:
	scripts/build_targets.sh

audit:
	scripts/audit_sorries.sh . || true

audit-imports:
	scripts/audit_imports.sh .

no-sorry:
	tools/check_no_sorry.sh
