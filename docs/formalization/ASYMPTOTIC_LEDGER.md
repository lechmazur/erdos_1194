# Asymptotic ledger

This file records all asymptotic claims used by the proof. Keep theorem names synchronized with Lean.

## APIs

Use mathlib asymptotic notation:

```lean
f =o[Filter.atTop] g
f =O[Filter.atTop] g
f ~[Filter.atTop] g
```

If this becomes awkward at a use site, replace the theorem by an explicit threshold statement and record the decision.

## Scales

Real scale:

```lean
def scaleReal (X : ℝ) : ℝ := X / Real.log X
```

Natural-indexed scale:

```lean
def scaleNat (X : ℕ) : ℝ := (X : ℝ) / Real.log (X : ℝ)
```

The final contradiction is over `ℕ` because `FundamentalUpperBound` is integer-indexed. Prove nat-indexed corollaries for the two major real asymptotics.

## A0: denominator positivity

Target:

```lean
theorem eventually_denom_pos (B : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < denom B n
```

Role:

- main theorem statement;
- spacing proof;
- extracting non-eventual strict violations.

Proof route:

```text
denom B n = log n - log(log n) + B
log(log n) = o(log n)
```

Implemented in `FloorSaving/PhiPsiData.lean` by composing `Real.isLittleO_log_id_atTop`
with `Real.tendsto_log_atTop` along `Nat.cast`, then using the small-o bound with constant
`1/2` and an eventual lower bound `log n > -2B`.

Status: proved, M4.

## A1: `f_asymptotic`

Source: TeX equation (5).

Target:

```lean
theorem f_asymptotic (D : PhiPsiData B) :
    D.f ~[Filter.atTop]
      (fun t : ℝ => Real.sqrt (2 * lam / (t * Real.log t)))
```

Used by:

- `f_bigO` or explicit eventual bound;
- `integral_f_asymptotic`;
- local comparability;
- tail estimates.

M8 setup proved in `FloorSaving/FAsymptotics.lean`:

```lean
theorem H_isEquivalent_atTop (B : ℝ) :
    (fun w : ℝ => H B w) ~[Filter.atTop] fun w : ℝ => w

theorem PhiPsiData.log_isEquivalent_two_log_psi :
    (fun t : ℝ => Real.log t) ~[Filter.atTop]
      fun t : ℝ => 2 * Real.log (D.psi t)

theorem PhiPsiData.f_sq_eq_lam_div_self_mul_H_log_psi_eventually :
    (fun t : ℝ => D.f t ^ 2)
      =ᶠ[Filter.atTop] fun t : ℝ => lam / (t * H B (Real.log (D.psi t)))

theorem PhiPsiData.f_sq_isEquivalent_model :
    (fun t : ℝ => D.f t ^ 2) ~[Filter.atTop]
      fun t : ℝ => 2 * lam / (t * Real.log t)

theorem PhiPsiData.f_asymptotic :
    D.f ~[Filter.atTop]
      (fun t : ℝ => Real.sqrt (2 * lam / (t * Real.log t)))

theorem PhiPsiData.eventually_abs_f_sub_fModel_le
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      |D.f t - fModel t| ≤ ε * fModel t

theorem PhiPsiData.f_upper_bound :
    ∃ C T : ℝ, 0 < C ∧
      ∀ t : ℝ, T ≤ t → D.f t ≤ C / Real.sqrt (t * Real.log t)

theorem PhiPsiData.f_sq_upper_bound :
    ∃ C T : ℝ, 0 < C ∧
      ∀ t : ℝ, T ≤ t → D.f t ^ 2 ≤ C / (t * Real.log t)
```

The public wrapper `FloorSaving.f_asymptotic` delegates to `PhiPsiData.f_asymptotic`.

Status: proved, M8. The explicit upper and square-upper bounds are derived from the proved
asymptotic equivalence by extracting a positive Big-O constant and rewriting the model square root.

## A2: first-order integral asymptotic and local tail controls

Source: TeX Part 2.

Target:

```lean
theorem integral_f_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ => I D X) ~[Filter.atTop]
      (fun X : ℝ => 2 * Real.sqrt (2 * lam * X / Real.log X))
```

M8 model calculus proved in `FloorSaving/FAsymptotics.lean`:

```lean
noncomputable def fModel (t : ℝ) : ℝ :=
  Real.sqrt (2 * lam / (t * Real.log t))

noncomputable def IModel (X : ℝ) : ℝ :=
  2 * Real.sqrt (2 * lam * X / Real.log X)

noncomputable def IModelDeriv (X : ℝ) : ℝ :=
  fModel X * (1 - 1 / Real.log X)

theorem eventually_IModel_eq_two_mul_self_mul_fModel :
    ∀ᶠ X : ℝ in Filter.atTop, IModel X = 2 * X * fModel X

theorem eventually_IModel_hasDerivAt :
    ∀ᶠ X : ℝ in Filter.atTop,
      HasDerivAt IModel (fModel X * (1 - 1 / Real.log X)) X

theorem IModel_derivFactor_isEquivalent_fModel :
    (fun X : ℝ => fModel X * (1 - (Real.log X)⁻¹)) ~[Filter.atTop] fModel

theorem integral_IModelDeriv_eq_IModel_sub_of_one_lt_of_le
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ x in a..b, IModelDeriv x = IModel b - IModel a

theorem PhiPsiData.eventually_integral_one_sub_mul_IModel_sub_le_f
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in Filter.atTop, ∀ᶠ b : ℝ in Filter.atTop,
      a ≤ b → (1 - ε) * (IModel b - IModel a) ≤ ∫ x in a..b, D.f x

theorem PhiPsiData.eventually_integral_f_le_one_add_mul_IModel_sub
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in Filter.atTop, ∀ᶠ b : ℝ in Filter.atTop,
      a ≤ b → ∫ x in a..b, D.f x ≤ (1 + ε) * (IModel b - IModel a)

theorem integral_f_isEquivalent_IModel (D : PhiPsiData B) :
    (fun X : ℝ => I D X) ~[Filter.atTop] IModel
```

Status: proved, M8. The public `integral_f_asymptotic` is obtained from
`integral_f_isEquivalent_IModel` by unfolding `IModel`.

The current TeX version also records the following Part 2 estimates, which are useful for the
counting-to-integral layer:

```text
(6) f upper bound               proved as `PhiPsiData.f_upper_bound`
(8) elementary integral bound    proved as `elementary_integral_bound`
(9) N(X+Z0) bound
(10) derivative bound             proved as `PhiPsiData.f_derivative_bound`
(11) local comparability             proved as `PhiPsiData.f_local_comparability`
(12) local Lipschitz              proved as `PhiPsiData.f_local_lipschitz`
```

The square-level corollary needed by later tails is also proved as
`PhiPsiData.f_sq_upper_bound`.

The elementary integral bound is proved on positive-log tails:

```lean
theorem elementary_integral_bound {T V : ℝ}
    (hT : Real.exp 2 ≤ T) (hTV : T ≤ V) :
    ∫ t in T..V, invSqrtLogModel t ≤ 4 * sqrtLogPrimitive V

theorem fModel_local_comparability {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ C T : ℝ, 0 < C ∧
      ∀ ⦃s t : ℝ⦄, T ≤ t → c * t ≤ s → s ≤ t →
        fModel s ≤ C * fModel t

theorem PhiPsiData.f_local_comparability
    {B : ℝ} (D : PhiPsiData B) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ C T : ℝ, 0 < C ∧
      ∀ ⦃s t : ℝ⦄, T ≤ t → c * t ≤ s → s ≤ t →
        D.f s ≤ C * D.f t

theorem eventually_inverse_derivative_model_le_f_over_Phi (B : ℝ) :
    ∀ᶠ r : ℝ in Filter.atTop,
      H B (Real.log r) ^ 2 /
          (lam * r ^ 3 *
            (2 * H B (Real.log r) - Hderiv (Real.log r))) ≤
        (1 / r) / PhiFormula B r
```

## A3: away-from-zero normalized `gNorm` convergence

Source: TeX Part 6 correction-term epsilon split.

For fixed `0 < ε ≤ U`, the normalized first-order profile now converges uniformly on
`Set.Icc ε U`:

```lean
theorem gNorm_uniform_away_bound
    (D : PhiPsiData B) {ε U η : ℝ} (hε : 0 < ε) (hεU : ε ≤ U) (hη : 0 < η) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ v ∈ Set.Icc ε U,
      |gNorm D X v - (Real.sqrt v)⁻¹| ≤ η

theorem gNorm_tendstoUniformlyOn_away
    (D : PhiPsiData B) {ε U : ℝ} (hε : 0 < ε) (hεU : ε ≤ U) :
    TendstoUniformlyOn
      (fun X v => gNorm D X v)
      (fun v => (Real.sqrt v)⁻¹)
      Filter.atTop
      (Set.Icc ε U)
```

Proof route:

- uniform control of `log X / log (X*v)` on `[ε,U]`;
- exact model algebra for `Real.sqrt (X log X / (2λ)) * fModel (X*v)`;
- uniform extraction of `D.eventually_abs_f_sub_fModel_le` by forcing `T ≤ X*ε ≤ X*v`;
- a model cap depending on `ε`, then a triangle inequality.

Status: proved in `FloorSaving/ContinuousMajorant.lean`, M9. Together with the small-endpoint
estimate below, this feeds the proved fixed-interval `gNorm_L1_convergence`.

## A4: small-endpoint normalized `gNorm` bound

Source: TeX Part 6 correction-term epsilon split, the `(0,ε)` endpoint estimate.

The endpoint contribution is now controlled uniformly in the scale parameter after `X` is
large enough for each fixed `ε`:

```lean
theorem gNorm_small_v_integral_eventual_bound
    (D : PhiPsiData B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃ε : ℝ⦄, 0 ≤ ε →
        ∀ᶠ X : ℝ in Filter.atTop,
          ∫ v in (0 : ℝ)..ε, gNorm D X v ≤ C * Real.sqrt ε

theorem gNorm_small_v_L1_eventual_bound
    (D : PhiPsiData B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃ε : ℝ⦄, 0 ≤ ε →
        ∀ᶠ X : ℝ in Filter.atTop,
          ∫ v in (0 : ℝ)..ε,
            |gNorm D X v - (Real.sqrt v)⁻¹| ≤ C * Real.sqrt ε
```

Proof route:

- change variables in `∫ gNorm` from `v` to `s = X*v`;
- split `∫₀^{Xε} f` into a fixed compact interval and a tail;
- bound the tail using `PhiPsiData.f_upper_bound` and `elementary_integral_bound`;
- normalize `sqrtLogPrimitive (Xε)` with checked square-root/log algebra;
- use `sqrt(log X) = o(sqrt X)` for the compact interval.

Status: proved in `FloorSaving/ContinuousMajorant.lean`, M9. The interval assembly is now
proved as `gNorm_L1_convergence`.

The immediate M5/M8-relevant one is the nat-indexed short-interval estimate:

```lean
theorem Ncount_X_plus_Z0_bound ... :
    (fun X : ℕ => (Ncount A ((X + Z0 : ℕ) : ℝ) : ℝ))
      =O[Filter.atTop] fun X : ℕ =>
        Real.sqrt ((X : ℝ) / Real.log (X : ℝ))
```

or an equivalent explicit-eventual bound strong enough to prove the short-top contribution is
`o[atTop] scaleNat`.

## A3: error bounds for counting layer

The fundamental upper bound needs several lower-order estimates. Prefer explicit error functions:

```lean
∃ err : ℕ → ℝ,
  err =o[Filter.atTop] scaleNat ∧
  ∀ᶠ X in Filter.atTop, lhs X ≤ rhs X + err X
```

Open subclaims:

- `Ncount A (X + Z0)` is controlled strongly enough for fixed-width short intervals;
- small-top replacement error is `o(X/log X)`; proved in `small_short_error_bound`;
- endpoint short interval contribution is `o(X/log X)`; proved in `small_short_error_bound`;
- Riemann-sum/integral replacement errors are `o(X/log X)`.

Current Lean targets packaging these subclaims:

```lean
theorem small_short_error_bound
    {B : ℝ} (A : Set ℕ) (_hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (_hupper : EventuallyUpperBound A _hA B)
    (Z0 : ℕ) :
    ∃ err : ℕ → ℝ,
      err =o[Filter.atTop] scaleNat ∧
      ∀ᶠ X : ℕ in Filter.atTop,
        smallShortMajorant A Z0 X ≤
          (1 / 2 : ℝ) * (I D (X : ℝ)) ^ 2 + err X

theorem large_floor_sum_error_bound
    {B : ℝ} (A : Set ℕ) (_hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (_hupper : EventuallyUpperBound A _hA B)
    (Z0 : ℕ) :
    ∃ err : ℕ → ℝ,
      err =o[Filter.atTop] scaleNat ∧
      ∀ᶠ X : ℕ in Filter.atTop,
        largeFloorSum A D Z0 X ≤
          JB D (X : ℝ) - Efloor D (X : ℝ) -
              (1 / 2 : ℝ) * (I D (X : ℝ)) ^ 2 + err X
```

The theorem `three_part_error_bound` is now only the assembly of these two estimates.
Both `small_short_error_bound` and `large_floor_sum_error_bound` are proved.

For `small_short_error_bound`, the counting inequalities reduce to explicit errors of the form:

```text
errSmall(X) = C * I(X) + C^2 / 2
errShort(X) = Z0 * (C + I(X+Z0))
```

The bridge lemmas now proved in `FloorSaving.Counting` for these errors are:

```lean
scaleNat_tendsto_atTop :
  Tendsto scaleNat Filter.atTop Filter.atTop

sqrt_scaleNat_isLittleO :
  (fun X : ℕ => Real.sqrt (scaleNat X)) =o[Filter.atTop] scaleNat

scaleNat_add_isBigO (Z0 : ℕ) :
  (fun X : ℕ => scaleNat (X + Z0)) =O[Filter.atTop] scaleNat

integral_nat_isLittleO_scaleNat (D : PhiPsiData B) :
  (fun X : ℕ => I D (X : ℝ)) =o[Filter.atTop] scaleNat

integral_nat_add_isLittleO_scaleNat (D : PhiPsiData B) (Z0 : ℕ) :
  (fun X : ℕ => I D (((X + Z0 : ℕ) : ℝ))) =o[Filter.atTop] scaleNat
```

## A4: continuous majorant asymptotic

Real form:

```lean
theorem continuous_majorant_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      JB D X -
        (X + lam * (3 - 2 * B - 2 * Real.log (Real.log 2)) * X / Real.log X))
      =o[Filter.atTop] scaleReal
```

Nat form:

```lean
theorem continuous_majorant_asymptotic_nat (D : PhiPsiData B) :
    (fun X : ℕ =>
      JB D (X : ℝ) -
        ((X : ℝ) +
          lam * (3 - 2 * B - 2 * Real.log (Real.log 2)) * (X : ℝ) /
            Real.log (X : ℝ)))
      =o[Filter.atTop] scaleNat
```

The current TeX reference incorporates the M9 decomposition:

```text
JB(X) = (1/2) I(X)^2
      + X * ∫_X^Phi(X) f(t)^2 dt
      + Rcorr(X)
```

where:

```lean
Rcorr D X =
  ∫ t in X..D.Phi X,
    D.f t * ∫ s in (t - X)..t, (D.f s - D.f t)
```

The continuous-majorant coefficient ledger is:

```text
Half-square:
  (1/2) I(X)^2 = 4λ X/Y + o(X/Y)
  contribution: +4

Square large-integral part:
  X∫_X^Phi(X) f(t)^2 dt
  = X + λ(1 - 2B + 2 log(λ/2)) X/Y + o(X/Y)
  contribution: +1 - 2B + 2 log(λ/2)

Correction:
  Rcorr(X) = 2λ(2 log 2 - 1) X/Y + o(X/Y)
  contribution: +2(2 log 2 - 1) = +4 log 2 - 2

Total:
  4 + 1 - 2B + 2 log(λ/2) + 4 log 2 - 2
  = 3 - 2B - 2 log(log 2)
```

The cancellation-sensitive square-integral subledger is:

```text
2∫ dw / w:
  -4 r_X

2∫ (log w - B) / w^2 dw:
  2 log Y - 4 log 2 + 2 - 2B

endpoint difference 1/H(Y) - 1/H(w0):
  -1

using r_X = (1/2) log Y - (1/2) log(2λ) + o(1):

(-2 log Y + 2 log(2λ))
+ (2 log Y - 4 log 2 + 2 - 2B)
- 1
= 1 - 2B + 2 log(λ/2).
```

Planned lemma cluster:

```text
half_square_asymptotic                         [proved]
GX_eq_X_mul_f_add_correction                   [proved]
continuous_integral_square_correction_split    [proved]
Phi_dominates_fixed_multiple                   [proved]
w0_tendsto_atTop / square-change endpoint ids  [proved]
exact rX identity / first-order w0,H(w0) eqvs  [proved]
lower_endpoint_asymptotic / rX_asymptotic     [proved]
PhiLog_hasDerivAt_eventually                  [proved]
PhiLog_deriv_nonneg_eventually                [proved]
f_Phi_exp_eq                                  [proved]
f_sq_integral_square_change_exact             [proved]
H_inv_hasDerivAt_eventually                  [proved]
transformed_square_integral_split_exact      [proved]
H_inv_remainder_integral_isLittleO            [proved]
two_inv_integral_w0_log_eq_eventually         [proved exact rewrite]
log_sub_const_div_sq_integral_w0_log_eq_eventually [proved exact rewrite]
two_inv_integral_asymptotic                   [proved]
log_sub_const_div_sq_integral_asymptotic      [proved]
H_inv_endpoint_diff_asymptotic                [proved]
rX_square_bracket_coefficient_asymptotic      [proved]
transformed_square_bracket_asymptotic_of_H_inv_remainder [proved conditional assembly]
transformed_square_bracket_asymptotic         [proved]
H_inverse_square_bracket_asymptotic
f_sq_integral_asymptotic                      [proved]
square_integral_term_asymptotic               [proved]
gNorm pointwise/integrability support          [proved]
gNorm small-endpoint L1 bound                  [proved]
gNorm_L1_convergence                         [proved]
RcorrTrunc_normalized_change                 [proved]
corrOperator_L1_convergence_fixed_U          [proved]
corrOperator_integral_tendsto_fixed_U        [proved]
RcorrTrunc_asymptotic                        [proved]
Rcorr tail split/nonnegativity support       [proved]
Rcorr_tail_bound                             [proved]
corrKernel_integral_tendsto                  [proved]
correction_asymptotic                        [proved]
large_continuous_integral_asymptotic         [proved]
continuous_coefficient_identity                  [proved]
continuous_majorant_asymptotic               [proved]
continuous_majorant_asymptotic_nat           [proved]
```

Needs local discovery before coding:

- exact interval-integral algebra APIs for `GX`; status: checked/proved for the current split;
- derivative and substitution APIs for `PhiFormula B (exp w)`; status: checked/proved for the
  square change;
- product/correction integrability facts;
- geometric-remainder strategy for `1 / H B w`; status: proved for the square-change window;
- epsilon-splitting APIs for the normalized correction, avoiding dominated convergence across
  the singular endpoint `v = 0`;
- later coefficient assembly can reuse the proved real-log algebra in
  `continuous_coefficient_identity`.

Status: M9 in progress. `half_square_asymptotic`, `GX_eq_X_mul_f_add_correction`,
`Phi_dominates_fixed_multiple`, `continuous_integral_square_correction_split`,
`w0_tendsto_atTop`, the square-change endpoint identities, `w0_isEquivalent_half_log`,
`H_w0_isEquivalent_half_log`, the exact `rX` identity,
`lower_endpoint_asymptotic`, `rX_asymptotic`, `f_Phi_exp_eq`,
`PhiLog_hasDerivAt_eventually`, `PhiLog_deriv_nonneg_eventually`,
`f_sq_integral_square_change_exact`, `H_inv_hasDerivAt_eventually`,
`transformed_square_integral_split_exact`, the exact primitive-integral rewrites for
`∫dw/w` and `∫(log w - B)/w²`, `two_inv_integral_asymptotic`,
`log_sub_const_div_sq_integral_asymptotic`, `H_inv_endpoint_diff_asymptotic`,
`rX_square_bracket_coefficient_asymptotic`,
`H_inv_remainder_integral_isLittleO`,
`transformed_square_bracket_asymptotic_of_H_inv_remainder`,
`transformed_square_bracket_asymptotic`, `f_sq_integral_asymptotic`,
`square_integral_term_asymptotic`, and
`continuous_coefficient_identity` are proved in
`FloorSaving/ContinuousMajorant.lean`.
`FloorSaving/ContinuousMajorant.lean` now also proves the exact normalized
`RcorrTrunc_normalized_change` and the pointwise limit-kernel identity
`corr_limit_integrand_eq_corrKernel`, the fixed-`U` correction-operator L1 convergence,
the derived un-absolute operator convergence, and `RcorrTrunc_asymptotic`.
`FloorSaving/KernelIntegral.lean` proves correction-kernel continuity/measurability support,
the finite transformed-kernel identity
`∫ x in 0..R, 2*x/(1+x)^2 = 2*(log(1+R)+1/(1+R)-1)` for `0 ≤ R`, the finite
correction-kernel closed form, `corrKernel_integral_tendsto`, `correction_asymptotic`, and
`large_continuous_integral_asymptotic`. The exact correction tail split, nonnegativity, tail
integrability, positive inverse-square integral support, pointwise inverse-square domination,
and uniform `Rcorr_tail_bound` are proved in `FloorSaving/ContinuousMajorant.lean`.
`FloorSaving/AnalyticInterfaces.lean` now proves the public `continuous_majorant_asymptotic`
and nat-indexed wrapper. M9 is complete, and A5 floor-saving asymptotics are complete.

## A5: floor-saving asymptotic

Real form:

```lean
theorem floor_saving_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      Efloor D X -
        2 * lam * (1 - Real.eulerMascheroniConstant) * X / Real.log X)
      =o[Filter.atTop] scaleReal
```

Nat form:

```lean
theorem floor_saving_asymptotic_nat (D : PhiPsiData B) :
    (fun X : ℕ =>
      Efloor D (X : ℝ) -
        2 * lam * (1 - Real.eulerMascheroniConstant) * (X : ℝ) /
          Real.log (X : ℝ))
      =o[Filter.atTop] scaleNat
```

The current TeX reference incorporates the M10 fixed-`Q` truncation and order-of-limits plan.
The first Lean scaffold is now present in `FloorSaving/FloorSavingIntegral.lean`.

Introduce truncations:

```lean
noncomputable def qOf {B : ℝ} (D : PhiPsiData B) (X t : ℝ) : ℝ :=
  X / D.psi t

noncomputable def EfloorMain {B : ℝ} (D : PhiPsiData B) (Q X : ℝ) : ℝ :=
  ∫ t in D.Phi (X / Q)..D.Phi X,
    D.f t * fract (GX D X t)

noncomputable def EfloorTail {B : ℝ} (D : PhiPsiData B) (Q X : ℝ) : ℝ :=
  ∫ t in X..D.Phi (X / Q),
    D.f t * fract (GX D X t)

noncomputable def IfractQ (Q : ℝ) : ℝ :=
  ∫ q in (1 : ℝ)..Q, fract q / q ^ 2

noncomputable def IfractInf : ℝ :=
  ∫ q in Set.Ioi (1 : ℝ), fract q / q ^ 2
```

Prove the normalized limit first:

```lean
theorem floor_saving_normalized_limit (D : PhiPsiData B) :
    Tendsto
      (fun X : ℝ =>
        Real.log X * Efloor D X / (2 * lam * X))
      Filter.atTop
      (𝓝 (1 - Real.eulerMascheroniConstant))
```

Then derive the small-o target from this normalized theorem.

Order of limits:

```text
For fixed Q > 1:
  prove EfloorMain(Q,X) =
    (2λX/log X) * IfractQ(Q) + o(X/log X).

For the fractional-part discontinuities:
  fix Q;
  choose epsilon-neighborhoods of the finitely many integers in [1,Q];
  send X -> infinity on the good set;
  let epsilon -> 0.

For the large-q tail:
  choose Q ≥ 2 so |IfractInf - IfractQ(Q)| and C/Q are small;
  then take X large for this fixed Q.
```

Main cut-point lemmas:

```lean
theorem eventually_q_change_exact_fixed_Q ...
theorem q_change_uniform_fixed_Q ...
theorem GX_Phi_X_div_q_uniform_fixed_Q ...
theorem fract_integral_convergence_fixed_Q ...
theorem floor_main_truncation_fixed_Q ...
theorem Efloor_split_fixed_Q ...
theorem EfloorTail_bound_uniform_Q ...
theorem IfractQ_tendsto_IfractInf ...
theorem floor_saving_normalized_limit ...
theorem floor_saving_asymptotic_of_normalized ...
```

The `q_change_uniform_fixed_Q` statement should quantify over bounded measurable `F` inside the
eventual statement, so it can be applied to the `X`-dependent function

```text
F_X q = fract (GX D X (D.Phi (X / q))).
```

The detailed 2026-04-29 TeX update makes the fixed-`Q` path more formalization-ready:

- define `qOf D X t = X / D.psi t`; on the inverse branch this equals `X * D.f t`, and
  `qOf D X (D.Phi (X / q)) = q`;
- prove `D.Phi (X / Q) > X` and `D.Phi (X / Q) < D.Phi X` eventually for fixed `Q > 1`;
- prove the q-change by two substitutions, `t = D.Phi r` and `q = X/r`, reducing the error to
  a supremum bound for
  `D.PhiDeriv (X/q) / (X/q) - 2 * lam / Real.log X`;
- package the fixed-`Q` derivative uniformity as
  `sup_{q ∈ [1,Q]} |Phi'(X/q)/(X/q) - 2λ/log X| = o(1/log X)`;
- prove `GX D X (D.Phi (X/q)) = q + O_Q(log X / X)` using `f_local_lipschitz` on `[t/2,t]`
  and `D.Phi (X/q) ≍_Q X^2 / log X`;
- for `fract`, remove finite neighborhoods of integers in `[1,Q]`, use a positive distance to
  `ℤ`, and apply a same-component Lipschitz lemma for `fract`;
- prove the large-`q` tail via `0 ≤ fract < 1`, the substitution `t = D.Phi r`, and a
  Q-independent bound `D.PhiDeriv r / r ≤ C_B / Real.log r` for large `r`, together with
  `D.psi X < X/Q` and `Real.log (D.psi X) ≥ Real.log X / 3` eventually.

Lean status as of 2026-04-29 05:00 EDT:

- uniform derivative/Jacobian control is proved as `eventually_jacobian_weight_uniform_fixed_Q`
  and `eventually_PhiDerivOverR_uniform_fixed_Q`;
- the correction-window growth helper is proved as
  `eventually_two_mul_X_le_Phi_X_div_q_on_Icc`; the uniform lower bound is proved as
  `eventually_Phi_X_div_q_lower_uniform_fixed_Q`;
- the fixed-`Q` `GX` branch estimate is proved as `GX_Phi_X_div_q_uniform_fixed_Q`;
- bounded-test-function q-change normalization has its integral core proved as
  `q_change_error_integral_bound` and `eventually_q_change_uniform_fixed_Q_core`; the dynamic
  `EfloorMain` wrapper is proved as `eventually_q_change_uniform_fixed_Q`;
- finite integer-neighborhood support is proved via `integerWindowIndex`, `integerWindow`,
  `integerWindowUnion`, `intBadSet`, `intGoodSet`, their measurability/membership lemmas, and
  `floor_eq_of_mem_intGoodSet_of_abs_sub_lt`,
  `fract_sub_fract_eq_of_mem_intGoodSet_of_abs_sub_lt`,
  `abs_fract_sub_fract_eq_of_mem_intGoodSet_of_abs_sub_lt`;
- fixed-`Q` fractional convergence is proved as `fract_integral_convergence_fixed_Q`;
- fixed-`Q` main truncation is proved as `floor_main_truncation_fixed_Q`;
- the order-of-limits normalized floor-saving theorem is proved as
  `floor_saving_normalized_limit`, and the small-o conversion is proved as
  `floor_saving_asymptotic_of_normalized`;
- model integral exhaustion is proved as `IfractQ_tendsto_IfractInf`, with
  `IfractInf_eq_one_sub_euler` connecting the limiting constant to Euler's constant.

The large-`q` tail must be normalized with a constant independent of `Q`:

```text
0 ≤ EfloorTail(Q,X)
Y * EfloorTail(Q,X) / (2λX) ≤ C_B / Q
```

where the lower threshold in `X` may depend on the fixed `Q`, but `C_B` may not.

Historical local-discovery checklist for this M10 route:

- change-of-variables theorem for bounded measurable integrands: resolved by the exact
  `EfloorMain` q-change and dynamic wrapper;
- measurability or continuity of `t ↦ GX D X t`: resolved by q-side measurability/integrability
  lemmas;
- finite integer-neighborhood and bad-set measure APIs: resolved by the good/bad split helpers;
- exact bridge from unit interval fractional-part integrals to
  `ZetaAsymptotics.term`;
- improper `Set.Ioi` integral exhaustion or a unit-interval `HasSum` route: resolved by
  `IfractQ_tendsto_IfractInf`;
- real-to-nat small-o transfer for `floor_saving_asymptotic_nat`: resolved in
  `AnalyticInterfaces.lean`.

Status: M10 complete. Proved declarations include `qOf`, `EfloorMain`, `EfloorTail`,
`IfractQ`, `IfractInf`, branch/order facts, exact split, nonnegativity helpers,
`EfloorTail_bound_uniform_Q`, `eventually_q_change_exact_fixed_Q`,
`eventually_jacobian_weight_uniform_fixed_Q`, `eventually_PhiDerivOverR_uniform_fixed_Q`,
`eventually_Phi_X_div_q_lower_uniform_fixed_Q`, `GX_Phi_X_div_q_uniform_fixed_Q`, finite
integer-window stability, `eventually_q_change_uniform_fixed_Q`, and
`IfractQ_tendsto_IfractInf`, plus `fract_integral_convergence_fixed_Q`,
`floor_main_truncation_fixed_Q`, `floor_saving_normalized_limit`, and
`floor_saving_asymptotic_of_normalized`. `AnalyticInterfaces.floor_saving_asymptotic` and
`floor_saving_asymptotic_nat` are now proved. M11 endpoint limsup packaging is proved in
`FloorSaving/EndpointLimsup.lean`.

## A6: fractional-part integral

Target:

```lean
theorem integral_fract_div_sq :
    ∫ q in Set.Ioi (1 : ℝ), fract q / q ^ 2 =
      1 - Real.eulerMascheroniConstant
```

Proof route options:

1. Search `Mathlib.NumberTheory.Harmonic.ZetaAsymp` for a close theorem.
2. Direct proof by splitting into intervals `[m,m+1]`:

```text
∫_m^{m+1} (q-m)/q² dq
```

and summing against the harmonic-limit characterization of Euler's constant.

Local discovery confirmed the `ZetaAsymptotics` shortcut exists:

```lean
ZetaAsymptotics.term
ZetaAsymptotics.term_one
ZetaAsymptotics.term_sum_one
ZetaAsymptotics.term_tsum_one
```

Preferred M10 route: prove a bridge from `fract q / q^2` on unit intervals to
`ZetaAsymptotics.term (n + 1) 1`, then use `term_tsum_one` and an interval-decomposition or
improper-integral exhaustion theorem.

Status: proved in `FloorSaving/FractionalIntegral.lean` as
`integral_fract_div_sq_Ioi`; `AnalyticInterfaces.integral_fract_div_sq` now reuses it.

## A7: final contradiction asymptotic algebra

Input:

```lean
hfund : FundamentalUpperBound D
hfacts : FinalAnalyticFacts D
```

Required derived fact:

```text
0 ≤ -2*lam*(B-B₁)*scaleNat X + o(scaleNat X)
```

Contradiction requirements:

- `0 < lam`;
- `0 < B - B₁`;
- `scaleNat X` eventually positive;
- little-o term eventually has absolute value ≤ half the negative coefficient times `scaleNat X`.

Status: proved in `FloorSaving/MainSkeleton.lean`, M6.
