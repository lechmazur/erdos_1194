# A Floor-Saving Logarithmic Lower Bound for Erdos Problem #1194

This repository contains a Lean 4/mathlib formalization and the accompanying
mathematical writeup for a logarithmic lower bound in the infinite perfect
difference set problem.

Let `A` be a set of positive integers such that every `n >= 1` has exactly one
ordered representation

```text
n = u(n) - v(n),    u(n), v(n) in A,    u(n) > v(n).
```

The main result proves that, with

```text
lambda = 1 / (2 log 2)
B_1 = 1/2 + gamma - log(log 2),
```

for every fixed `B > B_1` there are arbitrarily large `n` such that

```text
u(n) > lambda * n^2 / (log n - log log n + B).
```

It also proves the endpoint limsup consequence

```text
limsup_{n -> infinity} u(n) * (log n - log log n + B_1) / n^2
  >= 1 / (2 log 2).
```

The endpoint statement is a limsup consequence only; it does not assert the
pointwise infinitely-often inequality at `B = B_1`.

## Documents

- [Proof sketch (PDF)](docs/reference/floor_saving_proof_sketch.pdf)
- [Proof sketch (TeX)](docs/reference/floor_saving_proof_sketch.tex)
- [Full mathematical proof (PDF)](docs/reference/floor_saving_lower_bound_final_version.pdf)
- [Full mathematical proof (TeX)](docs/reference/floor_saving_lower_bound_final_version.tex)
- [Equation index](docs/reference/EQUATION_INDEX.md)

## Formalization

The Lean project is in the `FloorSaving` library. Important public declarations:

- `FloorSaving.floor_saving_lower_bound`
- `FloorSaving.not_eventually_upper_bound`
- `FloorSaving.endpoint_limsup`
- `FloorSaving.endpoint_frequently_lower_bound`
- `FloorSaving.denom_ratio_tendsto_one`

The main theorem is proved in
[`FloorSaving/MainSkeleton.lean`](FloorSaving/MainSkeleton.lean), using the
analytic and counting layers. The endpoint limsup packaging is proved in
[`FloorSaving/EndpointLimsup.lean`](FloorSaving/EndpointLimsup.lean).

The formalization-status notes are in [`docs/formalization`](docs/formalization).
They are included to make the proof architecture, interface boundaries, and
mathlib discovery decisions auditable.

## Checking

This project uses Lean `4.30.0-rc2` and mathlib, pinned by:

- [`lean-toolchain`](lean-toolchain)
- [`lakefile.toml`](lakefile.toml)
- [`lake-manifest.json`](lake-manifest.json)

To check the formalization:

```bash
lake exe cache get
lake build FloorSaving
scripts/audit_sorries.sh . || true
tools/check_no_sorry.sh
```

The publication bundle was prepared from source commit:

```text
c5d06adbe90f5d095a6b793349a118131443afe7
```

At bundle creation time, the root Lean build and the placeholder audits passed.

## Notes

The mathematical manuscript includes a disclosure that generative AI tools were
used for ideation, derivation assistance, drafting, internal-consistency checks,
and editing. The Lean formalization is included as the machine-checkable proof
artifact.
