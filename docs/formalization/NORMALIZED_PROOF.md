# Normalized proof blueprint

This file rewrites the TeX proof into Lean-targetable obligations. It is not a polished mathematical proof. It is a checklist of theorem statements and dependencies.

## N0. Contradiction setup

Fix:

```lean
(A : Set ℕ) (hA : UniquePositiveDiffs A)
(B : ℝ) (hB : B₁ < B)
```

Assume:

```lean
hupper : EventuallyUpperBound A hA B
```

Obtain analytic data:

```lean
D : PhiPsiData B
```

Goal: derive `False`.

## N1. Selected-pair facts

For every `n : PosNat`:

```lean
top_mem hA n : top A hA n ∈ A
bot_mem hA n : bot A hA n ∈ A
bot_lt_top hA n : bot A hA n < top A hA n
top_sub_bot hA n : top A hA n - bot A hA n = n.1
```

For any two representing pairs of the same positive difference:

```lean
same_diff_pair_unique hA hn hp hq : p = q
```

Status: should be fully proved by M2.

## N2. Denominator and Phi formula alignment

For every natural `n`:

```lean
H_log_nat_eq_denom B n :
  H B (Real.log (n : ℝ)) = denom B n

PhiFormula_nat_eq_lowerBoundRHS B n :
  PhiFormula B (n : ℝ) = lowerBoundRHS B n
```

Used in `spacing` to convert the assumed upper bound into `top ≤ D.Phi d`.

## N3. Eventual denominator positivity

Target:

```lean
theorem eventually_denom_pos (B : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < denom B n
```

This is analytic but elementary. It can be proved before the full phi/psi construction.

## N4. Spacing lemma

Target:

```lean
theorem spacing
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∃ Z0 : ℕ, ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        D.psi (z : ℝ) ≤ ((z - y : ℕ) : ℝ)
```

Proof model:

1. Extract `Nupper` from `hupper`.
2. Extract `Ndenom` from `eventually_denom_pos B`.
3. Let `Ncut = max D.N0 (max Nupper Ndenom)`.
4. Let `Z0` exceed `D.Tstar` and all `top d` for `0 < d < Ncut`.
5. Given `y < z` in `A`, set `d = z - y` and prove `0 < d`.
6. The pair `(z,y)` represents `d`.
7. By uniqueness, `top d = z`.
8. If `d < Ncut`, then `z = top d ≤ Z0`, contradiction.
9. Hence `Ncut ≤ d`, so the eventual upper bound applies to `d`.
10. Use `PhiFormula_nat_eq_lowerBoundRHS`, `D.Phi_eq`, and denominator positivity to get `(z : ℝ) ≤ D.Phi (d : ℝ)`.
11. Since `D.N0 ≤ d`, use `D.psi_le_of_le_Phi` to conclude `D.psi z ≤ d`.

Important coercions:

- `d = z - y : ℕ`;
- prove `z - y > 0` from `y < z`;
- use `Nat.cast_le`/`Nat.cast_lt` after discovery;
- convert `Z0 < z` to `D.Tstar ≤ z` by choosing `Z0` large enough.

## N5. Gap-integral domination

Target:

```lean
theorem gap_integral_ge_one
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∃ Z0 : ℕ, ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s
```

Proof model:

1. Use spacing to get `D.psi z ≤ z - y`.
2. Choose `Z0` so `(D.Tstar : ℝ) ≤ z` and `0 ≤ y`.
3. Use `D.f_eq_tail z` and `D.psi_pos_tail z` to get `D.f z = 1 / D.psi z`.
4. From `D.psi z ≤ z-y`, derive `1/(z-y) ≤ D.f z`.
5. From `D.f_antitone`, for `s ∈ [y,z]`, get `D.f z ≤ D.f s`.
6. Apply interval-integral monotonicity/lower-bound:

```text
∫_y^z f ≥ (z-y) * f(z) ≥ 1
```

Create a reusable helper lemma if mathlib does not have the exact statement.

## N6. Counting-function majorant

Target:

```lean
theorem counting_function_bound
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∃ C : ℝ, ∀ T : ℝ,
      0 ≤ T →
        (Ncount A T : ℝ) ≤ C + ∫ s in (0 : ℝ)..T, D.f s
```

Proof model:

- Use the ordered finite list of elements of `A` up to `T`.
- Consecutive large elements contribute at least `1` by N5.
- Finitely many initial elements are absorbed into `C`.
- Interval additivity gives sum of gap integrals ≤ total integral.

Avoid constructing a global enumeration of `A`; work with finite cuts.

## N7. Exact top-counting identity

Target:

```lean
theorem top_counting_identity
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∀ᶠ X : ℕ in Filter.atTop,
      X = ∑ t ∈ natCut A (D.Phi (X : ℝ)), (bottomWindow A X t).card
```

Proof model:

- The left side counts positive differences `n ∈ {1,...,X}`.
- The right side counts pairs `(t,b)` with:

```text
t ∈ A, t ≤ D.Phi X, b ∈ A, t - X ≤ b, b < t
```

- Map such a pair to `t - b`, a number in `{1,...,X}`.
- Injectivity follows from unique differences.
- Surjectivity: for each `1 ≤ n ≤ X`, the representative pair `(top n, bot n)` is counted because eventual upper bound gives `top n ≤ D.Phi n ≤ D.Phi X` once `X` is large.

This is the most coercion-heavy finite proof. Finish `mem_natCut_iff` and `mem_bottomWindow_iff` first.

## N8. Fundamental upper bound

Target:

```lean
def FundamentalUpperBound {B : ℝ} (D : PhiPsiData B) : Prop :=
  ∃ err : ℕ → ℝ,
    err =o[Filter.atTop] scaleNat ∧
    ∀ᶠ X : ℕ in Filter.atTop,
      (X : ℝ) ≤ JB D (X : ℝ) - Efloor D (X : ℝ) + err X
```

Proof model:

1. Start from N7.
2. Split tops into `t ≤ X`, the short integer interval `X < t ≤ X + Z0`, and
   large tops `X + Z0 < t ≤ D.Phi X`.
3. Use `Ncount` majorant for the small-top contribution.
4. Use the fixed-width short interval and the `N(X+Z0)` bound to make the short-top
   contribution `o(X/log X)`.
5. Replace large-top sums by integrals using gap domination, monotonicity of `f`, and the
   endpoint-loss estimate.
6. The floor in the large-top contribution gives `JB - Efloor`.
7. Put all lower-order terms into one explicit `err : ℕ → ℝ` and prove `err =o scaleNat`.

## N9. Continuous-majorant asymptotic

Target, real form:

```lean
(fun X : ℝ =>
  JB D X -
    (X + lam * (3 - 2 * B - 2 * Real.log (Real.log 2)) * X / Real.log X))
  =o[Filter.atTop] scaleReal
```

Nat-indexed version is required for the final contradiction.

The current TeX reference splits the proof with `Y = log X`, `M = Phi X`, and
`w0 X = log (psi X)`:

```text
JB(X) = (1/2) I(X)^2
      + X * ∫_X^M f(t)^2 dt
      + Rcorr(X)
```

where `Rcorr` is the correction term already defined in `ContinuousMajorant.lean`.

Break into cards:

- square term;
- lower endpoint expansion;
- exact square change `t = Phi(exp w)`;
- exact reciprocal-`H` split;
- `1/H` square-bracket expansion;
- normalized `gNorm` L¹ convergence on `(0,U)`;
- fixed-`U` correction substitution and limit;
- correction kernel convergence;
- correction tail with a constant independent of fixed `U ≥ 2`;
- assembly.

Detailed square-term subclaims from TeX Part 6.1:

```lean
theorem H_inv_remainder_integral_isLittleO
    (D : PhiPsiData B) :
    (fun X : ℝ =>
      ∫ w in w0 D X..Real.log X,
        ((H B w)⁻¹ - (w⁻¹ + (Real.log w - B) / w ^ 2)))
      =o[Filter.atTop] fun X : ℝ => (Real.log X)⁻¹

theorem two_inv_integral_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      Real.log X *
        ((2 : ℝ) * (∫ w in w0 D X..Real.log X, w⁻¹) - 2 * Real.log 2)
        + 4 * rX D X)
      =o[Filter.atTop] fun _ : ℝ => 1

theorem log_sub_const_div_sq_integral_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      Real.log X *
        ((2 : ℝ) *
          (∫ w in w0 D X..Real.log X, (Real.log w - B) / w ^ 2))
        - (2 * Real.log (Real.log X) - 4 * Real.log 2 + 2 - 2 * B))
      =o[Filter.atTop] fun _ : ℝ => 1

theorem H_inv_endpoint_diff_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      Real.log X *
        ((H B (Real.log X))⁻¹ - (H B (w0 D X))⁻¹) + 1)
      =o[Filter.atTop] fun _ : ℝ => 1
```

The combined bracket target is:

```lean
theorem transformed_square_bracket_asymptotic
    (D : PhiPsiData B) :
    (fun X : ℝ =>
      Real.log X *
        ((∫ w in w0 D X..Real.log X,
          (2 / H B w - Hderiv w / (H B w)^2)) - 2 * Real.log 2)
        - (1 - 2 * B + 2 * Real.log (lam / 2)))
      =o[Filter.atTop] fun _ : ℝ => 1
```

Then:

```lean
theorem f_sq_integral_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      (∫ t in X..D.Phi X, D.f t ^ 2) -
        (1 + lam * (1 - 2 * B + 2 * Real.log (lam / 2)) / Real.log X))
      =o[Filter.atTop] fun X : ℝ => (Real.log X)⁻¹

theorem square_integral_term_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      X * (∫ t in X..D.Phi X, D.f t ^ 2) -
        (X + lam * (1 - 2 * B + 2 * Real.log (lam / 2)) * X / Real.log X))
      =o[Filter.atTop] scaleReal
```

Detailed correction subclaims from TeX Part 6.2:

```lean
theorem gNorm_L1_convergence
    (D : PhiPsiData B) {U : ℝ} (hU : 0 ≤ U) :
    Tendsto (fun X : ℝ =>
      ∫ v in (0 : ℝ)..U, |gNorm D X v - 1 / Real.sqrt v|)
      Filter.atTop (𝓝 0)

theorem RcorrTrunc_normalized_change
    (D : PhiPsiData B) {U : ℝ} (hU : 1 ≤ U) :
    ∀ᶠ X : ℝ in Filter.atTop,
      RcorrTrunc D X U =
        (2 * lam * X / Real.log X) *
          ∫ u in (1 : ℝ)..U,
            gNorm D X u *
              ∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u)

theorem RcorrTrunc_asymptotic
    (D : PhiPsiData B) {U : ℝ} (hU : 1 ≤ U) :
    (fun X : ℝ =>
      RcorrTrunc D X U -
        2 * lam * (∫ u in (1 : ℝ)..U, corrKernel u) * X / Real.log X)
      =o[Filter.atTop] scaleReal

theorem Rcorr_tail_bound
    (D : PhiPsiData B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ U : ℝ, 2 ≤ U →
        ∀ᶠ X : ℝ in Filter.atTop,
          0 ≤ Rcorr D X - RcorrTrunc D X U ∧
          Rcorr D X - RcorrTrunc D X U ≤ C * X / (U * Real.log X)
```

The `gNorm` proof should follow the TeX epsilon split: prove uniform convergence on
`[ε,U]`, control `(0,ε)` using `f_upper_bound` and `elementary_integral_bound`, take
`X → ∞` for fixed `ε`, then let `ε ↓ 0`.

## N10. Floor-saving asymptotic

Target, real form:

```lean
(fun X : ℝ =>
  Efloor D X -
    2 * lam * (1 - Real.eulerMascheroniConstant) * X / Real.log X)
  =o[Filter.atTop] scaleReal
```

Break into cards:

- auxiliary definitions `qOf`, `EfloorMain`, `EfloorTail`, `IfractQ`, `IfractInf`;
- fixed-`Q` q-change theorem for bounded measurable `F_X`;
- uniform estimate `GX(Phi(X/q)) = q + O(Y/X)`;
- fractional-part convergence away from integer neighborhoods;
- truncation to `q ∈ [1,Q]`;
- large-q tail independent of fixed `Q`;
- identity `∫₁∞ {q}/q² dq = 1 - γ`.

Order of limits from the TeX proof:

```text
fix Q > 1
choose finite η-neighborhoods of integers in [1,Q]
send X → ∞ on the good set
send η ↓ 0
send Q → ∞ using a normalized O(1/Q) tail bound whose constant is independent of Q
```

The fixed-`Q` q-change should quantify over all bounded measurable functions
`F_X : [1,Q] → ℝ` with `|F_X| ≤ 1`, so it can later be applied to

```text
F_X(q) = fract (GX D X (D.Phi (X / q))).
```

The detailed TeX proof fixes the intended implementation shape:

- `qOf D X t = X / D.psi t`, and on the branch `qOf D X t = X * D.f t`;
- `qOf D X (D.Phi (X / q)) = q` for `X / q` on the `Phi` tail;
- the q-change error is controlled by the uniform derivative factor
  `Phi'(X/q)/(X/q) = 2*lam/log X + o_Q(1/log X)`;
- `GX D X (D.Phi (X/q)) = q + O_Q(log X / X)` uses the existing local Lipschitz estimate on
  `[t/2,t]`;
- `fract` convergence is proved by deleting finite neighborhoods of the integers in `[1,Q]`;
- the large-q tail uses `0 ≤ fract < 1`, `t = Phi r`, and a Q-independent bound
  `Phi'(r)/r ≤ C_B/log r`.

Main M10 targets:

```lean
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

Status: all listed M10 targets are proved in `FloorSaving/FloorSavingIntegral.lean`, with
`floor_saving_asymptotic` and `floor_saving_asymptotic_nat` discharged in
`FloorSaving/AnalyticInterfaces.lean`.

## N11. Final contradiction

Input:

```lean
hfund : FundamentalUpperBound D
hfacts : FinalAnalyticFacts D
hB : B₁ < B
```

Use:

```lean
coefficient_identity B :
  lam * (3 - 2 * B - 2 * Real.log (Real.log 2))
    - 2 * lam * (1 - Real.eulerMascheroniConstant)
    = -2 * lam * (B - B₁)
```

Combine:

```text
X ≤ JB(X) - Efloor(X) + o(X/log X)
JB(X) = X + c_cont X/log X + o(X/log X)
Efloor(X) = c_floor X/log X + o(X/log X)
```

Then:

```text
0 ≤ -2λ(B-B₁) X/log X + o(X/log X)
```

Since `B > B₁` and `λ > 0`, the coefficient is negative. For sufficiently large `X`, contradiction.

## N12. Main theorem from non-eventuality

Given:

```lean
not_eventually_upper_bound A hA B hB : ¬ EventuallyUpperBound A hA B
```

Show for every `N` there is `n ≥ N` violating the non-strict bound. Combine with `eventually_denom_pos B` to ensure denominator positivity.

## N13. Endpoint limsup

Endpoint packaging proved after the main theorem:

1. Fix `B > B₁` close to `B₁` or use a sequence `B_k ↓ B₁`.
2. Use the infinitely-often theorem to get arbitrarily large `n`.
3. Prove denominator ratio:

```text
(log n - log log n + B₁) / (log n - log log n + B) → 1
```

4. Convert infinitely-often lower bounds to the limsup lower bound.

Mathematical target from the current TeX proof:

```text
limsup_{n→∞}
  top(A,hA,n) * (log n - log log n + B₁) / n^2
  ≥ lam
```

The Lean statement uses the extended-real limsup of the totalized natural-index sequence
`endpointSeq`. The intermediate real statement is the frequent lower bound: for every `c < lam`,
`endpointSeq A hA n` is frequently greater than `c` along `Filter.atTop`. This avoids proving any
upper boundedness of the endpoint sequence, then `Filter.le_limsup_iff'` converts the frequent
lower bounds to the final `EReal` limsup inequality.
