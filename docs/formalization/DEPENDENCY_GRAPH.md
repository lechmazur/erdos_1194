# Dependency graph

Update this file when public theorem names or interfaces change.

## Module graph

```text
Basic
  -> UniqueDiff
  -> PhiPsiData

PhiPsiData
  -> AnalyticInterfaces

UniqueDiff + AnalyticInterfaces
  -> Counting

Counting
  -> MainSkeleton

Later additions:

AnalyticDefinitions
  -> holds I, GX, JB, fract, Efloor, and their basic integral-algebra helpers
  -> imported by AnalyticInterfaces and available to Counting, ContinuousMajorant,
     and FloorSavingIntegral without depending on analytic fact packaging

PhiPsiConstruction
  -> proves exists_phiPsiData

FAsymptotics
  -> proves f_asymptotic, integral_f_asymptotic, helper estimates

ContinuousMajorant
  -> proves continuous_majorant_asymptotic and nat version

FloorSavingIntegral
  -> proves floor_saving_asymptotic, nat version, integral_fract_div_sq
  -> internally uses fixed-Q q-change, discontinuity removal, large-q tail,
     normalized floor-saving limit

EndpointLimsup
  -> imports MainSkeleton
  -> proves endpointSeq, denom_ratio_tendsto_one, endpoint_frequently_lower_bound,
     endpoint_limsup
```

## Proof dependency graph

```text
repPair_spec
  -> top_mem, bot_mem, bot_lt_top, top_sub_bot
  -> same_diff_pair_unique
  -> spacing

H_log_nat_eq_denom
PhiFormula_nat_eq_lowerBoundRHS
EventuallyUpperBound
eventually_denom_pos
PhiPsiData.psi_le_of_le_Phi
  -> spacing

spacing
PhiPsiData.f_antitone
PhiPsiData.f_eq_tail
PhiPsiData.f_intervalIntegrable
  -> gap_integral_ge_one

gap_integral_ge_one
large_finset_card_le_one_add_integral
mem_natCut_iff
  -> counting_function_bound

same_diff_pair_unique
mem_natCut_iff
mem_bottomWindow_iff
EventuallyUpperBound
eventually_denom_pos
eventually_top_le_Phi
top_sub_cutoff_le_bot_of_sub_eq_of_le
sub_le_of_cutoff_sub_le
PhiPsiData.Phi_mono_tail
  -> top_counting_identity

top_counting_identity
counting_function_bound
first-order estimates
  -> fundamental_upper_bound

fundamental_upper_bound
FinalAnalyticFacts
coefficient_identity
  -> contradiction_from_interfaces
  -> not_eventually_upper_bound
  -> floor_saving_lower_bound
```

## Critical dependencies by theorem

### `spacing`

Depends on:

- `same_diff_pair_unique`;
- eventual upper-bound threshold;
- `eventually_denom_pos`;
- `PhiFormula_nat_eq_lowerBoundRHS`;
- `D.Phi_eq`;
- `D.psi_le_of_le_Phi`;
- finite maximum over exceptional small differences.

### `gap_integral_ge_one`

Depends on:

- `spacing`;
- `D.f_antitone`;
- `D.f_eq_tail`;
- `D.psi_pos_tail`;
- interval-integral lower bound for antitone functions.

### `counting_function_bound`

Depends on:

- `gap_integral_ge_one`;
- `large_finset_card_le_one_add_integral`;
- `mem_natCut_iff`;
- finite split at `a ≤ Z0`;
- max-erasure induction and interval additivity.

### `top_counting_identity`

Depends on:

- `same_diff_pair_unique`;
- `mem_natCut_iff`;
- `mem_bottomWindow_iff`;
- `eventually_top_le_Phi`;
- arithmetic helpers for bottom-window membership and `t - b ≤ X`;
- eventual upper bound and denominator positivity;
- `D.Phi_mono_tail`;
- finite bijection or sigma-cardinality theorem.

### `FundamentalUpperBound`

Depends on:

- `top_counting_identity`;
- `counting_function_bound`;
- first-order estimates for `f` and `I`;
- the `N(X+Z0)` short-interval bound;
- endpoint-loss and large-top floor domination;
- Riemann/integral replacement estimates;
- floor decomposition `x = floor x + fract x`.

### `contradiction_from_interfaces`

Depends on:

- `FundamentalUpperBound`;
- `FinalAnalyticFacts.continuous_majorant_nat`;
- `FinalAnalyticFacts.floor_saving_nat`;
- `coefficient_identity`;
- positivity of `lam`, `B-B₁`, and `scaleNat` on a tail;
- little-o arithmetic.
