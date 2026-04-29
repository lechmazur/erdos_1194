# Master plan

## Objective

Formalize the theorem from `docs/reference/floor_saving_lower_bound_final_version.tex` in Lean 4/mathlib.

The project has two goals:

1. prove the infinitely-often lower bound for every `B > B₁`;
2. then prove the endpoint limsup consequence.

The endpoint consequence is downstream. Do not work on it before the main theorem compiles.

## Main strategy

The TeX proof should be transformed before being coded. The transformation is not a rewrite for readability. It is a decomposition into Lean obligations with explicit thresholds, finite sets, coercions, error functions, and interfaces.

The formalization should be staged:

```text
Lean definitions
  -> unique-difference lemmas
  -> finite counting model
  -> spacing and counting inequalities
  -> fundamental upper bound
  -> final contradiction from analytic interfaces
  -> analytic construction and estimates
  -> endpoint limsup
```

This order prevents the agent from getting trapped in the hardest real-analysis section before the combinatorial skeleton and final contradiction are validated.

## Proof layers

### L0: representation layer

Files:

```text
FloorSaving/Basic.lean
FloorSaving/UniqueDiff.lean
```

Scope:

- `PosNat`, `PositiveSet`, `RepresentsDiff`, `UniquePositiveDiffs`;
- selected representative pair `repPair`;
- `top`, `bot`;
- constants `lam`, `B₁`, `denom`, scales;
- elementary uniqueness consequences.

Exit criterion:

```bash
lake build FloorSaving.Basic
lake build FloorSaving.UniqueDiff
```

with no `sorry` in these two files.

### L1: analytic interface layer

Files:

```text
FloorSaving/PhiPsiData.lean
FloorSaving/AnalyticInterfaces.lean
```

Scope:

- `H` and `PhiFormula`;
- tail inverse data `PhiPsiData`;
- `I`, `GX`, `JB`, `fract`, `Efloor`;
- named asymptotic interfaces.

Initial goal: compile the interfaces. Do not construct `PhiPsiData` yet.

### L2: finite counting layer

File:

```text
FloorSaving/Counting.lean
```

Scope:

- `natCut`, `Ncount`, `bottomWindow`;
- finite membership lemmas;
- spacing from eventual upper bound;
- gap-integral lower bound;
- counting function majorant;
- exact top-counting identity;
- fundamental upper bound as an explicit `o(X/log X)` inequality.

This is the first serious proof target after L0.

### L3: final contradiction from interfaces

File:

```text
FloorSaving/MainSkeleton.lean
```

Scope:

- denominator positivity on a tail;
- coefficient arithmetic;
- contradiction from:
  - `FundamentalUpperBound`;
  - continuous-majorant asymptotic;
  - floor-saving asymptotic.

This layer should be completed before proving the analytic asymptotics.

### L4: construction and first-order estimates

Files:

```text
FloorSaving/PhiPsiConstruction.lean
FloorSaving/FAsymptotics.lean
```

Scope:

- tail positivity for `H(log x)`;
- monotonicity and divergence of `PhiFormula`;
- inverse branch construction;
- constant extension of `f`;
- first-order estimates for `f` and `∫ f`;
- derivative/local-comparability estimates.

### L5: second-order analytic estimates

Files:

```text
FloorSaving/ContinuousMajorant.lean
FloorSaving/FloorSavingIntegral.lean
```

Scope:

- TeX Part 6 continuous-majorant asymptotic;
- TeX Part 7 floor-saving asymptotic;
- fractional-part integral identity.

### L6: endpoint limsup

File:

```text
FloorSaving/EndpointLimsup.lean
```

Scope:

- denominator-ratio limit at `B₁`;
- conversion of infinitely-often bounds into a limsup lower bound.

## Current milestone sequence

Use `docs/TASK_BOARD.md` as the active queue. The permanent order is:

```text
M0 environment and discovery
M1 core definitions
M2 unique-difference layer
M3 finite counting model
M4 spacing and gap integrals
M5 counting by tops and fundamental bound
M6 final contradiction from interfaces
M7 phi/psi construction
M8 first-order estimates
M9 continuous majorant
M10 floor saving
M11 endpoint limsup
```

## Acceptance standard

The final project is accepted only when:

```bash
lake build FloorSaving
scripts/audit_sorries.sh .
tools/check_no_sorry.sh
```

all succeed, and the endpoint theorem is present as a real theorem rather than a placeholder.
