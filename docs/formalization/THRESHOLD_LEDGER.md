# Threshold ledger

Lean must not use the TeX proof's informal threshold convention. Every threshold introduced in code should be recorded here.

## Rules

Use filters for analytic tail facts:

```lean
∀ᶠ x in Filter.atTop, P x
```

Use explicit thresholds for finite/combinatorial facts:

```lean
∃ N0 : ℕ, ∀ n, N0 ≤ n → P n
```

When a threshold is enlarged, record what it now dominates.

The current TeX reference uses the following order-of-limits convention, which Lean should encode
with quantifier order rather than prose:

- fix the contradiction data `A`, `B`, `hupper`, and the analytic data `D`;
- fix auxiliary truncation parameters such as `U` or `Q` before taking `X → ∞`;
- for floor-saving discontinuities, fix `Q`, choose finite integer-neighborhoods, take
  `X → ∞`, then shrink the neighborhoods;
- only after the fixed-parameter limit is proved should `U → ∞` or `Q → ∞` be taken;
- whenever a normalized tail estimate is later used as `U → ∞` or `Q → ∞`, the constant must be
  independent of that truncation parameter, although the lower `X` threshold may depend on its
  fixed value.

## Permanent analytic thresholds

### `x_B`

Type: `ℝ`.

Depends on: `B`.

Purpose: first real tail where:

```text
H(log x) > 0
2H(log x) - H'(log x) > 0
```

Lean status: represented as eventual filter facts in `FloorSaving/PhiPsiConstruction.lean`:

```lean
eventually_H_log_pos_atTop
eventually_two_mul_H_log_sub_Hderiv_log_pos_atTop
```

No named threshold value has been extracted yet; later monotonicity and inverse-branch proofs can
extract a concrete `N0` after combining these eventual facts with derivative and growth facts.

The strict-monotonicity helper now extracts an anonymous real threshold:

```lean
exists_PhiFormula_strictMonoOn_tail :
  ∃ T : ℝ, 1 < T ∧ StrictMonoOn (PhiFormula B) (Set.Ici T)
```

This `T` is not yet the final `D.N0`; after `PhiFormula → ∞`, choose a natural `N0` above it and
all remaining construction thresholds.

`exists_nat_PhiFormula_tail` now performs this first natural-threshold extraction:

```lean
∃ N0 : ℕ,
  3 ≤ N0 ∧
  0 < PhiFormula B (N0 : ℝ) ∧
  ContinuousOn (PhiFormula B) (Set.Ici (N0 : ℝ)) ∧
  StrictMonoOn (PhiFormula B) (Set.Ici (N0 : ℝ)) ∧
  MonotoneOn (PhiFormula B) (Set.Ici (N0 : ℝ)) ∧
  (∀ x, (N0 : ℝ) ≤ x → PhiFormula B (N0 : ℝ) ≤ PhiFormula B x) ∧
  Tendsto (PhiFormula B) Filter.atTop Filter.atTop
```

The final constructor may still enlarge this `N0` if inverse-branch or `f`-extension facts need
additional tail assumptions.

### `D.N0`

Type: `ℕ`, field of `PhiPsiData B`.

Depends on: `B` for pure analytic construction.

Required field:

```lean
D.N0_ge_three : 3 ≤ D.N0
```

Purpose:

- positivity of the analytic denominator on the tail;
- monotonicity of `Phi`;
- domain of the inverse branch;
- lower bound for `psi`.

Important: `D.N0` should stay analytic. Do not bake the eventual upper-bound threshold into `D.N0`; the spacing lemma should introduce a separate `Ncut`.

### `D.Tstar`

Type: `ℝ`, field of `PhiPsiData B`.

Depends on: `B`, `D.N0`.

Required fields:

```lean
D.Tstar_pos : 0 < D.Tstar
D.Tstar_eq : D.Tstar = D.Phi (D.N0 : ℝ)
```

Purpose:

- lower endpoint of the inverse-branch range;
- threshold after which `D.f t = 1 / D.psi t`.

## Contradiction thresholds

### `Nupper`

Type: `ℕ`.

Depends on: `A`, `hA`, `B`, `hupper`.

Purpose: threshold after which the assumed eventual upper bound applies.

Source:

```lean
hupper : EventuallyUpperBound A hA B
```

Lean extraction: use `Filter.eventually_atTop.mp hupper` to obtain
`∃ Nupper, ∀ n ≥ Nupper, UpperBoundAt A hA B n`. This was compiler-checked in the
`spacing` proof.

### `Ndenom`

Type: `ℕ`.

Depends on: `B`.

Purpose: threshold after which `0 < denom B n`.

Source:

```lean
eventually_denom_pos B
```

Lean status: proved as an analytic eventual fact in `FloorSaving/PhiPsiData.lean`. The explicit
natural threshold is extracted locally in `spacing` with
`Filter.eventually_atTop.mp (eventually_denom_pos B)`.

### `Ncut`

Type: `ℕ`.

Depends on: `D.N0`, `Nupper`, `Ndenom`.

Purpose: one natural threshold used in spacing.

Expected definition:

```text
Ncut = max D.N0 (max Nupper Ndenom)
```

May be enlarged to at least `1` if needed for finite ranges.

### `Z0`

Type: `ℕ`.

Depends on: `A`, `hA`, `B`, `hupper`, `D`, `Ncut`.

Purpose:

- dominate `D.Tstar`;
- dominate all exceptional small tops `top d` for `0 < d < Ncut`;
- later bound the short interval `(X, X + Z0]`.

Expected construction:

```text
Z0 > max(ceil D.Tstar, max_{1 ≤ d < Ncut} top d)
```

In Lean, use a `Finset.range Ncut` filtered by `0 < d`, then `Finset.max'` or a folded maximum. If the set is empty, use a default value.

## Continuous-majorant thresholds

### `X0_count`

Type: `ℕ` or `ℝ` depending on theorem.

Depends on: `A`, `hA`, `B`, `hupper`, `D`, `Z0`.

Purpose: threshold after which top-counting identity and fundamental bound estimates apply.

### `U`

Type: `ℝ`.

Depends on: chosen truncation in continuous correction term.

Limit order: fix `U`, send `X → ∞`, then send `U → ∞`.

Tail requirement from the current TeX proof: prove a normalized tail bound for `U ≥ 2` with a
constant independent of `U`, while allowing the eventual lower `X` threshold to depend on the
fixed `U`.

Lean status: proved as `Rcorr_tail_bound` in `FloorSaving/ContinuousMajorant.lean`. The proof
extracts the Lipschitz and square-upper-bound constants before `∀ U`; the eventual
`X` threshold then depends on the fixed `U` through `Phi_dominates_fixed_multiple`.

### Away-from-zero `gNorm` threshold

Type: anonymous real thresholds inside `∀ᶠ X in atTop`.

Depends on: fixed `ε`, fixed `U`, chosen tolerance `η`, and `D`.

Purpose: prove uniform convergence of `gNorm D X v` to `(sqrt v)⁻¹` on `v ∈ [ε,U]`.

Lean status: represented by filter facts in `FloorSaving/ContinuousMajorant.lean`:

```lean
log_div_log_mul_uniform_sub_one_le
gNorm_model_uniform_away_bound
gNorm_sub_model_uniform_relative_bound
gNorm_model_uniform_cap
gNorm_uniform_away_bound
gNorm_tendstoUniformlyOn_away
```

The extracted thresholds enforce:

- `1 < X` and `1 < X*ε`, hence `1 < X*v` for `v ∈ [ε,U]`;
- `T ≤ X*ε`, where `T` is extracted from `D.eventually_abs_f_sub_fModel_le`;
- uniform reciprocal-log control on `[ε,U]`.

These thresholds may depend on the fixed `ε` and `U`, which matches the TeX epsilon-split order.

### `Q`

Type: `ℝ`.

Depends on: floor-saving truncation.

Limit order: fix `Q`, send `X → ∞`, then send `Q → ∞`.

Tail requirement from the current TeX proof: prove
`Y * EfloorTail(Q,X) / (2λX) ≤ C / Q` for `Q ≥ 2`, with `C` independent of `Q`; the eventual
lower `X` threshold may depend on the fixed `Q`.

### `η`

Type: `ℝ`.

Depends on: finite integer-neighborhood removal in the floor-saving proof.

Limit order: for fixed `Q`, choose/remove neighborhoods of integers in `[1,Q]`, send `X → ∞`, then shrink neighborhoods or use their small measure.

## Update log

2026-04-28: Added the first M7 real-tail filter facts for `H(log x)>0` and
`2H(log x)-H'(log x)>0`; also proved existence of a closed real tail where `PhiFormula` is
strictly monotone. No final natural `N0` was extracted.

2026-04-28: Proved `PhiFormula_tendsto_atTop` and extracted the first natural branch threshold
with `exists_nat_PhiFormula_tail`.

2026-04-28: Built the inverse branch on the endpoint ray using `PhiFormula_surjOn_tail` and
`psiBranch`; this reuses the natural threshold from `exists_nat_PhiFormula_tail`.

2026-04-28: Defined `fBranch` with constant value `1 / N0` below `PhiFormula B N0` and
`1 / psiBranch` on the endpoint ray. No new threshold was introduced; the same natural `N0` and
endpoint `Tstar = PhiFormula B N0` now discharge `exists_phiPsiData`.
