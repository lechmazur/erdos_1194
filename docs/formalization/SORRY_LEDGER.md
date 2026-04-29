# Sorry ledger

Keep this synchronized with:

```bash
scripts/audit_sorries.sh . || true
python3 tools/update_sorry_ledger.py
```

## Policy

Temporary `sorry`s are allowed only to keep the architecture compiling while a lower layer is developed.

Every `sorry` must have:

- file;
- declaration;
- purpose;
- dependencies;
- next action;
- target milestone.

Do not replace `sorry` with `axiom`, `unsafe`, or hidden assumptions.

## Current `sorry`s

| File | Declaration | Purpose | Dependencies | Next action | Target milestone | Status |
|---|---|---|---|---|---|---|
| _none_ | _none_ | _none_ | _none_ | _none_ | _none_ | closed |

`FloorSaving/Basic.lean` and `FloorSaving/UniqueDiff.lean` should have no `sorry` after M2.

## Latest audit output

Generated after completing the M11 endpoint limsup on 2026-04-29 with
`scripts/audit_sorries.sh . || true`.

```text
No sorry/admit/axiom/unsafe placeholders found in Lean files.
```
