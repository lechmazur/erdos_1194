# Auditing this Lean proof

The trusted statement is [`Challenge.lean`](Challenge.lean). It imports only
`Mathlib`, defines the small amount of vocabulary used in the theorem statement,
and states the two comparator targets:

- `FloorSaving.floor_saving_lower_bound`
- `FloorSaving.endpoint_limsup`

The proof is the `FloorSaving` library. [`Solution.lean`](Solution.lean) imports
that library so comparator can verify that the proved declarations match the
trusted statements in `Challenge.lean`.

## Standard Lean check

```bash
lake exe cache get
lake build FloorSaving
tools/check_no_sorry.sh
```

`Challenge.lean` intentionally contains statement placeholders for comparator.
The no-sorry check is therefore scoped to the proof library, not the trusted
challenge file.

## Comparator check

Comparator is an external Lean proof checker harness. It compares a trusted
challenge module against a solution module, checks permitted axioms, and replays
the solution through the Lean kernel.

Install `landrun`, `lean4export`, and `comparator` so their binaries are on
`PATH`. Use versions compatible with the pinned Lean toolchain
`leanprover/lean4:v4.30.0-rc2`; the corresponding tags are available for
`lean4export` and `comparator`.

Then run from the repository root:

```bash
lake env comparator comparator.json
```

On success, comparator has checked that the theorem statements in
`Solution.lean` match `Challenge.lean`, use only the axioms listed in
`comparator.json`, and are accepted by the Lean kernel.

This bundle was validated with `comparator` and `lean4export` at tag
`v4.30.0-rc2` and `landrun` `0.1.15`. The successful comparator run ended with:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```
