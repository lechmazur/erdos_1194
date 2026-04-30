.PHONY: build challenge solution audit no-sorry comparator

build:
	lake build FloorSaving

challenge:
	lake build Challenge

solution:
	lake build Solution

audit:
	scripts/audit_sorries.sh .
	tools/check_no_sorry.sh

no-sorry:
	tools/check_no_sorry.sh

comparator:
	lake env comparator comparator.json
