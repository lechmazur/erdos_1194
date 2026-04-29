# Lemma index

This file maps the TeX proof to Lean obligations. Keep statements synchronized with the Lean files.

## L0: basic selected-pair lemmas

### `repPair_spec`

Source location: theorem statement, notation `(a_n,b_n)`.

Purpose: expose the specification of the selected representative pair.

Statement:

```lean
theorem repPair_spec {A : Set ℕ} (hA : UniquePositiveDiffs A) (n : PosNat) :
    RepresentsDiff A n.1 (repPair A hA n).1
```

Dependencies: definition of `repPair`.

Status: proved and compiler-checked in M2.

### `top_mem`, `bot_mem`, `bot_lt_top`, `top_sub_bot`

Source location: theorem statement.

Purpose: reusable projections from `repPair_spec`.

Statements:

```lean
theorem top_mem (hA : UniquePositiveDiffs A) (n : PosNat) : top A hA n ∈ A
theorem bot_mem (hA : UniquePositiveDiffs A) (n : PosNat) : bot A hA n ∈ A
theorem bot_lt_top (hA : UniquePositiveDiffs A) (n : PosNat) : bot A hA n < top A hA n
theorem top_sub_bot (hA : UniquePositiveDiffs A) (n : PosNat) : top A hA n - bot A hA n = n.1
```

Status: proved and compiler-checked in M2.

### `same_diff_pair_unique`

Source location: unique-difference hypothesis.

Purpose: identify arbitrary representing pairs with selected pairs.

Statement:

```lean
theorem same_diff_pair_unique
    {A : Set ℕ} (hA : UniquePositiveDiffs A)
    {n : ℕ} (hn : 0 < n) {p q : ℕ × ℕ}
    (hp : RepresentsDiff A n p) (hq : RepresentsDiff A n q) :
    p = q
```

Status: proved and compiler-checked in M2.

### `A_unbounded`

Source location: beginning of TeX Part 1.

Purpose: avoid constructing a global enumeration of `A`.

Statement:

```lean
theorem A_unbounded {A : Set ℕ} (hA : UniquePositiveDiffs A) :
    ∀ N : ℕ, ∃ a : ℕ, a ∈ A ∧ N ≤ a
```

Proof ingredient: represent `N+1`; the top of that pair is at least `N+1`.

Status: proved and compiler-checked in M2.

## L1: formula alignment

### `H_log_nat_eq_denom`

Source location: definition of `H` and denominator.

Purpose: convert analytic `H(log n)` into final denominator.

Statement:

```lean
theorem H_log_nat_eq_denom (B : ℝ) (n : ℕ) :
    H B (Real.log (n : ℝ)) = denom B n
```

Status: proved and compiler-checked in M3.

### `PhiFormula_nat_eq_lowerBoundRHS`

Source location: definition of `Φ` and final bound.

Purpose: convert the eventual upper-bound assumption to `top ≤ D.Phi n`.

Statement:

```lean
theorem PhiFormula_nat_eq_lowerBoundRHS (B : ℝ) (n : ℕ) :
    PhiFormula B (n : ℝ) = lowerBoundRHS B n
```

Status: proved and compiler-checked in M3.

## L2: finite-set wrappers

### `mem_bottomWindow_iff`

Source location: top-counting identity.

Purpose: simplify membership in bottom windows.

Statement:

```lean
theorem mem_bottomWindow_iff {A : Set ℕ} {X t b : ℕ} :
    b ∈ bottomWindow A X t ↔ b ∈ A ∧ t - X ≤ b ∧ b < t
```

Expected APIs: `Finset.mem_filter`, `Finset.mem_range`, `simp`.

Status: proved and compiler-checked in M3.

### `mem_natCut_iff`

Source location: all finite cuts by real bounds.

Purpose: bridge `Finset.range (Nat.floor T + 1)` and `(a : ℝ) ≤ T`.

Statement:

```lean
theorem mem_natCut_iff {A : Set ℕ} {T : ℝ} {a : ℕ} (hT : 0 ≤ T) :
    a ∈ natCut A T ↔ a ∈ A ∧ (a : ℝ) ≤ T
```

Used APIs: `Nat.le_floor`, `Nat.floor_le`, `Nat.lt_add_one_iff`, `Nat.cast_le`.

Lean notes: the statement is stable with hypothesis `0 ≤ T`; the forward direction uses
`Nat.floor_le hT`, and the reverse direction uses `Nat.le_floor`.

Status: proved and compiler-checked in M3.

## L3: spacing and gap domination

### `eventually_denom_pos`

Source location: threshold convention.

Purpose: make the denominator-positive range explicit.

Statement:

```lean
theorem eventually_denom_pos (B : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < denom B n
```

Dependencies: elementary logarithmic asymptotics.

Lean location: `FloorSaving/PhiPsiData.lean`.

Proof ingredients: `Real.isLittleO_log_id_atTop`, `Real.tendsto_log_atTop`,
`tendsto_natCast_atTop_atTop`, and `Tendsto.eventually_gt_atTop`.

Status: proved and compiler-checked in M4.

### `spacing`

Source location: TeX equation (2).

Purpose: convert eventual upper bound into spacing of elements of `A`.

Statement: see `FloorSaving/Counting.lean`.

Proof ingredients:

- extract thresholds from `hupper` and `eventually_denom_pos`;
- finite maximum over small differences;
- uniqueness of representing pairs;
- `PhiFormula_nat_eq_lowerBoundRHS`;
- `D.psi_le_of_le_Phi`.

Lean notes:

- finite maximum is implemented by imaging `Finset.range Ncut` through the selected top function and taking `Finset.max'` after inserting `0`;
- the selected-pair identification uses `repPair_eq_of_represents`;
- the real threshold uses `exists_nat_gt D.Tstar`.

Status: proved and compiler-checked in M4.

### `gap_integral_ge_one`

Source location: TeX Part 1 after spacing.

Purpose: each large gap contributes at least one unit of integral.

Proof ingredients:

- `spacing`;
- `D.f_antitone`;
- `D.f_eq_tail`;
- `D.psi_pos_tail`;
- interval-integral monotone lower bound.

Helper:

```lean
theorem intervalIntegral_const_mul_le_of_forall_le
    {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (h : ∀ x ∈ Set.Icc a b, c ≤ f x) :
    (b - a) * c ≤ ∫ x in a..b, f x
```

Used APIs: `intervalIntegral.integral_mono_on`,
`intervalIntegral.intervalIntegrable_const`, `intervalIntegral.integral_const`.

Lean notes: `gap_integral_ge_one` chooses a threshold large enough for both `spacing` and
`D.Tstar ≤ z`, uses `D.f_antitone` on `Set.Ici 0` to compare `D.f z` against all interval
values, and converts `(z - y : ℕ)` to `(z : ℝ) - (y : ℝ)` with `Nat.cast_sub`.

Status: proved and compiler-checked in M4.

### `counting_function_bound`

Source location: TeX Part 1, equation after gap domination.

Purpose: bound `N(T)` by a constant plus `∫₀ᵀ f`.

Proof ingredients:

- max-erasure induction over the large finite set;
- `gap_integral_ge_one`;
- interval-additivity;
- absorb initial elements into `C`.

Helper:

```lean
theorem large_finset_card_le_one_add_integral
    {B : ℝ} {A : Set ℕ} {Z0 : ℕ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s) :
    ∀ S : Finset ℕ,
      (∀ a ∈ S, a ∈ A) →
      (∀ a ∈ S, Z0 < a) →
      ∀ T : ℝ,
        0 ≤ T →
        (∀ a ∈ S, (a : ℝ) ≤ T) →
          (S.card : ℝ) ≤ 1 + ∫ s in (0 : ℝ)..T, D.f s
```

Used APIs: `Finset.induction_on_max`, `Finset.card_filter_add_card_filter_not`,
`Finset.card_le_card`, `Finset.card_range`,
`intervalIntegral.integral_add_adjacent_intervals`, `intervalIntegral.integral_nonneg`.

Lean notes: the final proof splits `natCut A T` into `a ≤ Z0` and `¬ a ≤ Z0`.
The small side injects into `Finset.range (Z0 + 1)`. The large side uses the helper,
with membership and upper bounds supplied by `mem_natCut_iff`.

Status: proved and compiler-checked in M4.

## L4: exact counting by tops

### `top_counting_identity`

Source location: TeX Part 3.

Purpose: exact finite identity before analytic bounding.

Statement: see `FloorSaving/Counting.lean`.

Proof ingredients:

- bijection between `n ∈ {1,...,X}` and counted pairs `(t,b)`;
- uniqueness of differences;
- eventual upper bound plus monotonicity of `D.Phi`.

Recommended finite model:

```lean
let S : Finset ℕ := Finset.Icc 1 X
let P : Finset (Sigma fun t : ℕ => ℕ) :=
  (natCut A (D.Phi (X : ℝ))).sigma fun t => bottomWindow A X t
```

The implementation proves `S.card = P.card` by `Finset.card_bij`, then uses the
`Finset.Icc 1 X` cardinality simplification and `Finset.card_sigma` to rewrite the right side to
`∑ t ∈ natCut A (D.Phi (X : ℝ)), (bottomWindow A X t).card`.

Threshold subgoal:

```lean
theorem eventually_top_le_Phi
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∀ᶠ X : ℕ in Filter.atTop,
  0 ≤ D.Phi (X : ℝ) ∧
  ∀ n : ℕ, 0 < n → n ≤ X →
    (top A hA ⟨n, ‹0 < n›⟩ : ℝ) ≤ D.Phi (X : ℝ)
```

Large `n` should use `hupper`, `eventually_denom_pos`, formula alignment, `D.Phi_eq`, and
`D.Phi_mono_tail`; small `n` should use a finite maximum plus
`D.Phi_tendsto_atTop.eventually_ge_atTop`.

Status: proved and compiler-checked as `eventually_top_le_Phi` in M5.

Consequence:

```lean
theorem eventually_natCast_le_Phi
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (X : ℝ) ≤ D.Phi (X : ℝ)
```

This uses `diff_le_top`, since the selected top representing the positive difference `X` is at
least `X`.

Arithmetic helpers:

```lean
theorem diff_le_top (hA : UniquePositiveDiffs A) (n : PosNat) :
    n.1 ≤ top A hA n

theorem top_sub_cutoff_le_bot_of_sub_eq_of_le
    {t b n X : ℕ} (hsub : t - b = n) (hnpos : 0 < n) (hnX : n ≤ X) :
    t - X ≤ b

theorem sub_le_of_cutoff_sub_le
    {t b X : ℕ} (hwin : t - X ≤ b) :
    t - b ≤ X
```

Status: proved and compiler-checked in M5.

Implementation notes:

- the bijection is written from `Finset.Icc 1 X` to the sigma finset, with
  `n ↦ (top n, bot n)`;
- surjectivity sends a sigma element `(t, b)` to `t - b` and uses
  `repPair_eq_of_represents`;
- the real cutoff is discharged by `eventually_top_le_Phi`;
- bottom-window arithmetic is handled by `top_sub_cutoff_le_bot_of_sub_eq_of_le`
  and `sub_le_of_cutoff_sub_le`;
- equality in the sigma type uses `Sigma.ext` with `heq_of_eq` for the constant
  second coordinate.

Status: proved and compiler-checked in M5.

### Small-top finite contribution

Source location: TeX equations (14)--(15), finite part.

Purpose: identify the contribution of tops `t ≤ X` and preserve the required factor `1 / 2`.

Statements:

```lean
theorem sum_card_filter_lt_eq_choose_two (S : Finset ℕ) :
    (∑ t ∈ S, (S.filter fun b : ℕ => b < t).card) = S.card.choose 2

theorem bottomWindow_eq_filter_natCut_of_le
    {A : Set ℕ} {X t : ℕ} (htX : t ≤ X) :
    bottomWindow A X t = (natCut A (X : ℝ)).filter (fun b : ℕ => b < t)

theorem small_top_sum_eq_choose (A : Set ℕ) (X : ℕ) :
    (∑ t ∈ natCut A (X : ℝ), (bottomWindow A X t).card) =
      (Ncount A (X : ℝ)).choose 2

theorem small_top_sum_le_half_ncount_sq (A : Set ℕ) (X : ℕ) :
    ((∑ t ∈ natCut A (X : ℝ), (bottomWindow A X t).card : ℕ) : ℝ) ≤
      (1 / 2 : ℝ) * (Ncount A (X : ℝ) : ℝ) ^ 2
```

Used APIs: `Finset.induction_on_max`, `Finset.sum_insert`, `Nat.choose_succ_succ'`,
`Nat.choose_one_right`, and `Nat.choose_le_pow_div`.

Status: finite identity and half-square bound proved and compiler-checked in M5. The
`o(X/log X)` error form against `(1 / 2) * (I D X)^2` is proved through
`small_short_error_bound`.

### Short-interval finite contribution

Source location: TeX Part 5, short interval after equation (18).

Purpose: isolate the fixed-width interval `X < t ≤ X + Z0` before the large-top floor
argument.

Statements:

```lean
theorem bottomWindow_card_le_ncount_of_top_le
    (A : Set ℕ) {X T t : ℕ} (htT : t ≤ T) :
    (bottomWindow A X t).card ≤ Ncount A (T : ℝ)

theorem short_top_count_le (A : Set ℕ) (X Z : ℕ) (M : ℝ) :
    ((natCut A M).filter (fun t : ℕ => X < t ∧ t ≤ X + Z)).card ≤ Z

theorem short_top_sum_le_mul_ncount (A : Set ℕ) (X Z : ℕ) (M : ℝ) :
    (∑ t ∈ (natCut A M).filter (fun t : ℕ => X < t ∧ t ≤ X + Z),
        (bottomWindow A X t).card) ≤
      Z * Ncount A ((X + Z : ℕ) : ℝ)
```

Used APIs: `Nat.card_Ioc`, `Finset.card_le_card`, `Finset.sum_le_sum`, and
`Nat.mul_le_mul_right`.

Status: finite bound proved and compiler-checked in M5. The `o(X/log X)` consequence is proved
through `small_short_error_bound`.

### Large-top finite floor contribution

Source location: TeX Part 5, range `X + Z0 < t ≤ Phi X`.

Purpose: use gap-integral domination to bound each large bottom window by
`floor(G_X(t))`, then sum the pointwise inequality over the finite top cutoff.

Statements:

```lean
theorem finite_chain_card_le_integral_min_to_endpoint
    {B : ℝ} {A : Set ℕ} {Z0 : ℕ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s) :
    ∀ S : Finset ℕ,
      ∀ hS : S.Nonempty,
      (∀ a ∈ S, a ∈ A) →
      (∀ a ∈ S, Z0 < a) →
      ∀ z : ℕ,
        z ∈ A →
        (∀ a ∈ S, a < z) →
          (S.card : ℝ) ≤ ∫ s in (S.min' hS : ℝ)..(z : ℝ), D.f s

theorem finite_chain_card_le_integral_lower_to_endpoint
    {B : ℝ} {A : Set ℕ} {Z0 z : ℕ} {L : ℝ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s)
    (S : Finset ℕ)
    (hmem : ∀ a ∈ S, a ∈ A)
    (hlarge : ∀ a ∈ S, Z0 < a)
    (hzA : z ∈ A)
    (hSz : ∀ a ∈ S, a < z)
    (hL_nonneg : 0 ≤ L)
    (hLz : L ≤ (z : ℝ))
    (hL_le : ∀ a ∈ S, L ≤ (a : ℝ)) :
    (S.card : ℝ) ≤ ∫ s in L..(z : ℝ), D.f s

theorem bottomWindow_card_le_GX_of_large_top
    {B : ℝ} {A : Set ℕ} {Z0 X t : ℕ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s)
    (htA : t ∈ A) (hlarge : X + Z0 < t) :
    ((bottomWindow A X t).card : ℝ) ≤ GX D (X : ℝ) (t : ℝ)

theorem bottomWindow_card_le_floor_GX_of_large_top
    {B : ℝ} {A : Set ℕ} {Z0 X t : ℕ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s)
    (htA : t ∈ A) (hlarge : X + Z0 < t) :
    ((bottomWindow A X t).card : ℤ) ≤
      ⌊GX D (X : ℝ) (t : ℝ)⌋

theorem large_top_sum_le_sum_floor_GX_of_gap
    {B : ℝ} {A : Set ℕ} {Z0 : ℕ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s)
    (X : ℕ) (M : ℝ) :
    ((∑ t ∈ (natCut A M).filter (fun t : ℕ => X + Z0 < t),
        (bottomWindow A X t).card : ℕ) : ℝ) ≤
      ∑ t ∈ (natCut A M).filter (fun t : ℕ => X + Z0 < t),
        ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ)
```

Used APIs: `Finset.induction_on_max`, `Finset.min'_insert`, `Finset.min'_mem`,
`Nat.lt_sub_iff_add_lt`, `Nat.cast_sub`, `intervalIntegral.integral_add_adjacent_intervals`,
`intervalIntegral.integral_nonneg`, `Int.le_floor`, `Finset.sum_le_sum`, and `exact_mod_cast`.

Lean notes: `finite_chain_card_le_integral_min_to_endpoint` inducts by inserting a new maximum.
`finite_chain_card_le_integral_lower_to_endpoint` extends the lower endpoint with nonnegativity
of `D.f`. The large-top hypothesis `X + Z0 < t` implies every bottom in `bottomWindow A X t`
is beyond `Z0`, because `Z0 < t - X` follows from `Nat.lt_sub_iff_add_lt`.

Status: finite pointwise and summed bounds proved and compiler-checked in M5. The later analytic
step still has to convert the floor sum into the `JB - Efloor` contribution with controlled error.

### Three-part top-counting bound

Source location: TeX Parts 3--5, after the small/short/large top estimates.

Purpose: combine the exact top-counting identity with the finite small, short, and large top
bounds, leaving only analytic error control and the conversion of the large floor sum to
`JB - Efloor`.

Statements:

```lean
theorem finset_sum_nat_split_three
    (S : Finset ℕ) (X Z : ℕ) (f : ℕ → ℕ) :
    (∑ t ∈ S, f t) =
      (∑ t ∈ S.filter (fun t : ℕ => t ≤ X), f t) +
        (∑ t ∈ S.filter (fun t : ℕ => X < t ∧ t ≤ X + Z), f t) +
          (∑ t ∈ S.filter (fun t : ℕ => X + Z < t), f t)

theorem top_counting_three_part_bound
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B)
    {Z0 : ℕ}
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (X : ℝ) ≤
        (1 / 2 : ℝ) * (Ncount A (X : ℝ) : ℝ) ^ 2 +
          (Z0 : ℝ) * (Ncount A (((X + Z0 : ℕ) : ℝ)) : ℝ) +
            ∑ t ∈ (natCut A (D.Phi (X : ℝ))).filter (fun t : ℕ => X + Z0 < t),
              ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ)
```

Used APIs: `Finset.sum_filter_add_sum_filter_not`,
`Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.mem_filter`, `Nat.lt_of_not_ge`,
`Nat.not_le_of_gt`, `Nat.le_add_right`, `exact_mod_cast`, and `norm_num [Nat.cast_add]`.

Lean notes: the small filtered sum is only a subset of `natCut A X`; this is enough because all
terms are nonnegative. The large range predicate uses `X + Z0 < t`, and the implication
`X + Z0 < t → X < t` is discharged by `Nat.le_add_right`.

Status: proved and compiler-checked in M5.

### `smallShortMajorant`, `largeFloorSum`, `threePartMajorant`

Source location: final M5 assembly after the finite three-part bound.

Purpose: name the remaining analytic/counting error package needed to turn the finite majorant
into the explicit `FundamentalUpperBound` error-function form.

Statements:

```lean
noncomputable def smallShortMajorant
    (A : Set ℕ) (Z0 X : ℕ) : ℝ

noncomputable def largeFloorSum
    {B : ℝ} (A : Set ℕ) (D : PhiPsiData B) (Z0 X : ℕ) : ℝ

noncomputable def threePartMajorant
    {B : ℝ} (A : Set ℕ) (D : PhiPsiData B) (Z0 X : ℕ) : ℝ
```

Status: definitions added and compiler-checked in M5.

### Continuous floor-integral algebra

Source location: final M5 large floor-sum bridge and the M10 floor-saving setup.

Purpose: expose the continuous contribution `JB - Efloor - (1/2)I^2` as the integral of the
integer floor of `GX`.

Statements:

```lean
noncomputable def fract (x : ℝ) : ℝ := Int.fract x

theorem fract_nonneg (x : ℝ) : 0 ≤ fract x
theorem fract_lt_one (x : ℝ) : fract x < 1
theorem fract_mem_Ico (x : ℝ) : fract x ∈ Set.Ico (0 : ℝ) 1
theorem fract_measurable : Measurable fract

theorem floor_GX_eq_GX_sub_fract
    {B : ℝ} (D : PhiPsiData B) (X t : ℝ) :
    ((⌊GX D X t⌋ : ℤ) : ℝ) = GX D X t - fract (GX D X t)

theorem floor_integrand_eq_sub
    {B : ℝ} (D : PhiPsiData B) (X t : ℝ) :
    D.f t * ((⌊GX D X t⌋ : ℤ) : ℝ) =
      D.f t * GX D X t - D.f t * fract (GX D X t)

theorem GX_nonneg_of_nonneg_window
    {B : ℝ} (D : PhiPsiData B) {X t : ℝ}
    (hX : 0 ≤ X) (hlower : 0 ≤ t - X) :
    0 ≤ GX D X t

theorem GX_antitoneOn_Ici
    {B : ℝ} (D : PhiPsiData B) {X : ℝ} (hX : 0 ≤ X) :
    AntitoneOn (fun t : ℝ => GX D X t) (Set.Ici X)

theorem floor_GX_nonneg_of_nonneg_window
    {B : ℝ} (D : PhiPsiData B) {X t : ℝ}
    (hX : 0 ≤ X) (hlower : 0 ≤ t - X) :
    0 ≤ ((⌊GX D X t⌋ : ℤ) : ℝ)

theorem floor_GX_antitoneOn_Ici
    {B : ℝ} (D : PhiPsiData B) {X : ℝ} (hX : 0 ≤ X) :
    AntitoneOn (fun t : ℝ => ((⌊GX D X t⌋ : ℤ) : ℝ)) (Set.Ici X)

theorem f_mul_GX_intervalIntegrable
    {B : ℝ} (D : PhiPsiData B) {X Y : ℝ}
    (hX : 0 ≤ X) (hXY : X ≤ Y) :
    IntervalIntegrable (fun t : ℝ => D.f t * GX D X t)
      MeasureTheory.volume X Y

theorem f_mul_floor_GX_intervalIntegrable
    {B : ℝ} (D : PhiPsiData B) {X Y : ℝ}
    (hX : 0 ≤ X) (hXY : X ≤ Y) :
    IntervalIntegrable
      (fun t : ℝ => D.f t * ((⌊GX D X t⌋ : ℤ) : ℝ))
      MeasureTheory.volume X Y

theorem I_continuous {B : ℝ} (D : PhiPsiData B) :
    Continuous (fun X : ℝ => I D X)

theorem GX_eq_primitive_sub {B : ℝ} (D : PhiPsiData B) (X t : ℝ) :
    GX D X t = I D t - I D (t - X)

theorem GX_continuous_in_t {B : ℝ} (D : PhiPsiData B) (X : ℝ) :
    Continuous (fun t : ℝ => GX D X t)

theorem GX_measurable_in_t {B : ℝ} (D : PhiPsiData B) (X : ℝ) :
    Measurable (fun t : ℝ => GX D X t)

theorem fract_GX_measurable {B : ℝ} (D : PhiPsiData B) (X : ℝ) :
    Measurable (fun t : ℝ => fract (GX D X t))

theorem f_mul_fract_GX_intervalIntegrable
    {B : ℝ} (D : PhiPsiData B) {X Y : ℝ}
    (hX : 0 ≤ X) (hXY : X ≤ Y) :
    IntervalIntegrable
      (fun t : ℝ => D.f t * fract (GX D X t))
      MeasureTheory.volume X Y

theorem JB_sub_Efloor_sub_half_I_sq_eq_floor_integral_of_nonneg
    {B : ℝ} (D : PhiPsiData B) {X : ℝ}
    (hX : 0 ≤ X) (hXPhi : X ≤ D.Phi X) :
    JB D X - Efloor D X - (1 / 2 : ℝ) * (I D X) ^ 2 =
      ∫ t in X..D.Phi X, D.f t * ((⌊GX D X t⌋ : ℤ) : ℝ)

theorem JB_sub_Efloor_sub_half_I_sq_eq_floor_integral
    {B : ℝ} (D : PhiPsiData B) (X : ℝ)
    (hGX :
      IntervalIntegrable (fun t : ℝ => D.f t * GX D X t)
        MeasureTheory.volume X (D.Phi X))
    (hfract :
      IntervalIntegrable (fun t : ℝ => D.f t * fract (GX D X t))
        MeasureTheory.volume X (D.Phi X)) :
    JB D X - Efloor D X - (1 / 2 : ℝ) * (I D X) ^ 2 =
      ∫ t in X..D.Phi X, D.f t * ((⌊GX D X t⌋ : ℤ) : ℝ)
```

Used APIs: `Int.fract`, `Int.fract_nonneg`, `Int.fract_lt_one`, `Int.self_sub_fract`,
`Int.floor_le`, `Int.floor_nonneg`, `Int.floor_le_floor`, `measurable_fract`,
`IntervalIntegrable.comp_add_right`, `intervalIntegral.integral_comp_add_right`,
`intervalIntegral.integral_mono_on`, `AntitoneOn.intervalIntegrable`, `Set.uIcc_of_le`,
`intervalIntegral.continuous_primitive`, `intervalIntegral.integral_interval_sub_left`,
`IntervalIntegrable.mono_fun'`, `MeasureTheory.ae_restrict_iff'`,
`intervalIntegral.integral_sub`, and `intervalIntegral.integral_congr`.

Lean notes: the integral identity deliberately carries product-integrability hypotheses rather
than adding them to `PhiPsiData`. The `D.f * GX`, `D.f * floor(GX)`, and
`D.f * fract(GX)` integrability hypotheses are now discharged on nonnegative intervals. The M5
large-floor bridge is reduced to the weighted finite-chain integral comparison and endpoint loss.

Status: proved and compiler-checked in `FloorSaving.AnalyticDefinitions`.

### `small_short_error_bound`, `large_floor_sum_error_bound`, `three_part_error_bound`

Source location: final M5 assembly after the finite three-part bound.

Purpose: split the remaining error package into a small/short contribution and a large floor-sum
replacement contribution.

Statements:

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
    (Z0 : ℕ)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s) :
    ∃ err : ℕ → ℝ,
      err =o[Filter.atTop] scaleNat ∧
      ∀ᶠ X : ℕ in Filter.atTop,
        largeFloorSum A D Z0 X ≤
          JB D (X : ℝ) - Efloor D (X : ℝ) -
              (1 / 2 : ℝ) * (I D (X : ℝ)) ^ 2 + err X

theorem three_part_error_bound
    {B : ℝ} (A : Set ℕ) (_hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (_hupper : EventuallyUpperBound A _hA B)
    (Z0 : ℕ)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s) :
    ∃ err : ℕ → ℝ,
      err =o[Filter.atTop] scaleNat ∧
      ∀ᶠ X : ℕ in Filter.atTop,
        threePartMajorant A D Z0 X ≤
          JB D (X : ℝ) - Efloor D (X : ℝ) + err X
```

Dependencies:

- small-top replacement, discharged in `small_short_error_bound`:
  `(1/2) * N(X)^2 ≤ (1/2) * (I D X)^2 + o(scaleNat)`;
- short-top estimate, discharged in `small_short_error_bound`:
  `Z0 * N(X+Z0) = o(scaleNat)`;
- large floor-sum/integral replacement, discharged in `large_floor_sum_error_bound`:
  after applying `JB_sub_Efloor_sub_half_I_sq_eq_floor_integral`, the finite floor sum is bounded
  by the weighted floor integral plus endpoint loss `I D X = o(scaleNat X)`.

Large-floor finite-sum helpers:

```lean
theorem largeFloorSum_nonneg
    {B : ℝ} (A : Set ℕ) (D : PhiPsiData B) (Z0 X : ℕ) :
    0 ≤ largeFloorSum A D Z0 X

theorem largeFloorSum_le_largeGXSum
    {B : ℝ} (A : Set ℕ) (D : PhiPsiData B) (Z0 X : ℕ) :
    largeFloorSum A D Z0 X ≤
      ∑ t ∈ (natCut A (D.Phi (X : ℝ))).filter (fun t : ℕ => X + Z0 < t),
        GX D (X : ℝ) (t : ℝ)

theorem floor_GX_le_floor_integral_on_gap
    {B : ℝ} (D : PhiPsiData B) {X y z : ℕ}
    (hXy : X ≤ y) (hyz : y < z)
    (hgap : 1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s) :
    ((⌊GX D (X : ℝ) (z : ℝ)⌋ : ℤ) : ℝ) ≤
      ∫ s in (y : ℝ)..(z : ℝ),
        D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ)

theorem finite_chain_floor_sum_le_endpoint_add_integral_min_to_max ...

theorem largeFloorSum_le_I_add_floor_integral
    {B : ℝ} {A : Set ℕ} {Z0 X : ℕ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s)
    (hXPhi : (X : ℝ) ≤ D.Phi (X : ℝ)) :
    largeFloorSum A D Z0 X ≤
      I D (X : ℝ) +
        ∫ s in (X : ℝ)..D.Phi (X : ℝ),
          D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ)

theorem eventually_JB_sub_Efloor_nat_eq_floor_integral
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∀ᶠ X : ℕ in Filter.atTop,
      JB D (X : ℝ) - Efloor D (X : ℝ) -
          (1 / 2 : ℝ) * (I D (X : ℝ)) ^ 2 =
        ∫ t in (X : ℝ)..D.Phi (X : ℝ),
          D.f t * ((⌊GX D (X : ℝ) t⌋ : ℤ) : ℝ)
```

Status: `small_short_error_bound`, `largeFloorSum_nonneg`,
`largeFloorSum_le_largeGXSum`, `eventually_natCast_le_Phi`,
`eventually_JB_sub_Efloor_nat_eq_floor_integral`, the weighted finite-chain helpers,
`large_floor_sum_error_bound`, and `three_part_error_bound` are proved and compiler-checked in M5.

### `fundamental_upper_bound`

Source location: TeX equation (19).

Purpose: deliver the combinatorial inequality used in final contradiction.

Statement:

```lean
theorem fundamental_upper_bound
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    FundamentalUpperBound D
```

Proof ingredients:

- `top_counting_identity`;
- small-top contribution;
- large-top floor decomposition;
- first-order estimates for error terms.

Lean notes: `fundamental_upper_bound` now obtains `Z0` and `hgap` directly from
`gap_integral_ge_one`, then applies `top_counting_three_part_bound` and
`three_part_error_bound` with that same threshold.

Status: proved and compiler-checked in M5.

## L5: final contradiction

### `coefficient_identity`

Source location: constant ledger.

Purpose: exact coefficient cancellation.

Statement: in `MainSkeleton.lean`.

Status: proved and compiler-checked in M6.

### `lam_pos`, `eventually_scaleNat_pos`

Source location: final comparison.

Purpose: support the final contradiction by making the negative second-order coefficient
strictly negative on the eventually positive scale.

Statements:

```lean
theorem lam_pos : 0 < lam

theorem eventually_scaleNat_pos :
    ∀ᶠ X : ℕ in Filter.atTop, 0 < scaleNat X
```

Used APIs: `positivity`, `tendsto_natCast_atTop_atTop`, `Real.tendsto_log_atTop`,
`Filter.Tendsto.eventually_gt_atTop`, and `div_pos`.

Status: proved and compiler-checked in M6.

### `contradiction_from_interfaces`

Source location: final comparison.

Purpose: prove contradiction from `FundamentalUpperBound` and `FinalAnalyticFacts`.

Statement:

```lean
theorem contradiction_from_interfaces
    {B : ℝ} (D : PhiPsiData B)
    (hB : B₁ < B)
    (hfund : FundamentalUpperBound D)
    (hfacts : FinalAnalyticFacts D) :
    False
```

Proof ingredients:

- extract explicit `err` from `hfund`;
- combine little-o terms;
- coefficient identity;
- positivity of `lam` and eventual positivity of `scaleNat`.

Lean notes: the proof combines the continuous-majorant, floor-saving, and `fundamental_upper_bound`
error terms into a single `o(scaleNat)` remainder. Taking the little-o bound with coefficient
`k / 2`, where `k = 2 * lam * (B - B₁) > 0`, contradicts the eventual inequality
`k * scaleNat X ≤ remainder X`.

Status: proved and compiler-checked in M6.

### `floor_saving_lower_bound`

Source location: theorem statement.

Purpose: main theorem.

Proof ingredients:

- `not_eventually_upper_bound`;
- conversion from not-eventual upper bound to arbitrarily large strict violations.

Lean notes: no separate denominator-positivity tail is needed here: the negation of
`UpperBoundAt n` directly supplies `0 < denom B n` and the strict violation.

Status: proved and compiler-checked in M6.

## L6: analytic construction and estimates

### `eventually_H_pos_atTop` / `eventually_H_log_pos_atTop`

Source location: TeX setup for the tail inverse of `Phi`.

Purpose: establish that the denominator in `PhiFormula` is positive on the real tail.

Statements:

```lean
theorem eventually_H_pos_atTop (B : ℝ) :
    ∀ᶠ w : ℝ in Filter.atTop, 0 < H B w

theorem eventually_H_log_pos_atTop (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, 0 < H B (Real.log x)
```

Dependencies: `Real.isLittleO_log_id_atTop`, `Real.tendsto_log_atTop`, and elementary
filter threshold arithmetic.

Status: proved and compiler-checked in M7.

### `eventually_two_mul_H_sub_Hderiv_pos_atTop`

Source location: TeX monotonicity calculation for `Phi`.

Purpose: isolate the numerator sign needed for positivity of the eventual derivative of
`PhiFormula`.

Statements:

```lean
def Hderiv (w : ℝ) : ℝ := 1 - 1 / w

theorem eventually_two_mul_H_sub_Hderiv_pos_atTop (B : ℝ) :
    ∀ᶠ w : ℝ in Filter.atTop, 0 < 2 * H B w - Hderiv w

theorem eventually_two_mul_H_log_sub_Hderiv_log_pos_atTop (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      0 < 2 * H B (Real.log x) - Hderiv (Real.log x)
```

Dependencies: same tail `log w = o(w)` comparison as `eventually_H_pos_atTop`, plus
eventual positivity of `w` for the `1 / w` term.

Status: proved and compiler-checked in M7.

### `eventually_PhiFormula_pos_atTop`

Source location: TeX setup for the inverse range.

Purpose: record that `PhiFormula B x` is positive on the real tail, using positivity of
`lam`, `x ^ 2`, and `H B (log x)`.

Statement:

```lean
theorem eventually_PhiFormula_pos_atTop (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, 0 < PhiFormula B x
```

Status: proved and compiler-checked in M7.

### `PhiFormula_hasDerivAt` / `exists_PhiFormula_strictMonoOn_tail`

Source location: TeX construction of the tail inverse branch.

Purpose: make the monotone branch of `PhiFormula` available without committing yet to the final
integer threshold `D.N0`.

Statements:

```lean
theorem H_log_hasDerivAt {B x : ℝ}
    (hx : x ≠ 0) (hlogx : Real.log x ≠ 0) :
    HasDerivAt (fun y : ℝ => H B (Real.log y))
      (Hderiv (Real.log x) / x) x

theorem PhiFormula_hasDerivAt {B x : ℝ}
    (hx : x ≠ 0) (hlogx : Real.log x ≠ 0)
    (hH : H B (Real.log x) ≠ 0) :
    HasDerivAt (PhiFormula B)
      (lam * x * (2 * H B (Real.log x) - Hderiv (Real.log x)) /
        (H B (Real.log x)) ^ 2) x

theorem eventually_PhiFormula_deriv_pos_atTop (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, 0 < deriv (PhiFormula B) x

theorem exists_PhiFormula_strictMonoOn_tail (B : ℝ) :
    ∃ T : ℝ, 1 < T ∧ StrictMonoOn (PhiFormula B) (Set.Ici T)
```

Dependencies: `Real.hasDerivAt_log`, derivative algebra for subtraction/division, `HasDerivAt.deriv`,
`strictMonoOn_of_deriv_pos`, `convex_Ici`, and `interior_Ici`.

Status: proved and compiler-checked in M7.

### `PhiFormula_tendsto_atTop` / `exists_nat_PhiFormula_tail`

Source location: TeX construction of the inverse branch.

Purpose: prove that the monotone branch has unbounded range and choose a natural threshold with
the endpoint positivity and mapping facts needed by `PhiPsiData`.

Statements:

```lean
theorem eventually_H_log_le_self_atTop (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, H B (Real.log x) ≤ x

theorem eventually_lam_mul_self_le_PhiFormula (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, lam * x ≤ PhiFormula B x

theorem PhiFormula_tendsto_atTop (B : ℝ) :
    Tendsto (PhiFormula B) Filter.atTop Filter.atTop

theorem exists_nat_PhiFormula_tail (B : ℝ) :
    ∃ N0 : ℕ,
      3 ≤ N0 ∧
        0 < PhiFormula B (N0 : ℝ) ∧
          ContinuousOn (PhiFormula B) (Set.Ici (N0 : ℝ)) ∧
          StrictMonoOn (PhiFormula B) (Set.Ici (N0 : ℝ)) ∧
            MonotoneOn (PhiFormula B) (Set.Ici (N0 : ℝ)) ∧
              (∀ x : ℝ, (N0 : ℝ) ≤ x →
                PhiFormula B (N0 : ℝ) ≤ PhiFormula B x) ∧
                Tendsto (PhiFormula B) Filter.atTop Filter.atTop
```

Proof route: use `log x = o(x)` and `log (log x) → ∞` to get `H B (log x) ≤ x` eventually;
combine denominator positivity with `lam > 0` to prove the eventual lower bound
`lam * x ≤ PhiFormula B x`; then compare against `lam * x → ∞`.

Status: proved and compiler-checked in M7.

### `psiBranch`

Source location: TeX construction of the inverse branch `ψ`.

Purpose: construct the inverse of `PhiFormula` on the checked natural tail and prove the exact
fields later needed by `PhiPsiData`.

Definitions and statements:

```lean
theorem PhiFormula_surjOn_tail {B : ℝ} {N0 : ℕ}
    (hcont : ContinuousOn (PhiFormula B) (Set.Ici (N0 : ℝ)))
    (htendsto : Tendsto (PhiFormula B) Filter.atTop Filter.atTop) :
    Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
      (Set.Ici (PhiFormula B (N0 : ℝ)))

noncomputable def psiBranch (B : ℝ) (N0 : ℕ) : ℝ → ℝ :=
  Function.invFunOn (PhiFormula B) (Set.Ici (N0 : ℝ))

theorem PhiFormula_psiBranch_eq ...
theorem psiBranch_maps_tail ...
theorem psiBranch_right_inv ...
theorem psiBranch_le_of_le_Phi ...
theorem psiBranch_mono_tail ...
```

Proof route: choose an upper endpoint from `PhiFormula_tendsto_atTop`, use
`ContinuousOn.surjOn_Icc` on `[N0,X]`, and then use `Function.invFunOn` plus strict
monotonicity for uniqueness/order transport.

Status: proved and compiler-checked in M7.

### `fBranch`

Source location: TeX construction of the majorant `f`.

Purpose: extend the inverse-branch formula `f(t) = 1 / psi(t)` below the endpoint while keeping
the global function positive, nonincreasing on `[0,∞)`, measurable, and interval integrable.

Definitions and statements:

```lean
noncomputable def fBranch (B : ℝ) (N0 : ℕ) (t : ℝ) : ℝ :=
  if t < PhiFormula B (N0 : ℝ) then 1 / (N0 : ℝ) else 1 / psiBranch B N0 t

theorem fBranch_eq_tail ...
theorem psiBranch_pos_tail ...
theorem fBranch_pos ...
theorem fBranch_antitone ...
theorem fBranch_measurable ...
theorem fBranch_intervalIntegrable ...
```

Proof route: use the checked `psiBranch` maps-to-tail and monotonicity facts. The constant value
`1 / N0` matches the left endpoint value order-wise, so reciprocal antitonicity proves global
antitonicity. Mathlib's monotone-function APIs then provide measurability and interval
integrability.

Status: proved and compiler-checked in M7.

### `exists_phiPsiData`

Source location: TeX setup before Part 1.

Purpose: construct the analytic data package.

Dependencies:

- positivity of `H(log x)` on a tail;
- derivative of `PhiFormula`;
- strict monotonicity and tendsto atTop;
- inverse branch construction;
- constant extension of `f`.

Status: proved and compiler-checked in M7 via `exists_phiPsiData_constructed`; the public
`AnalyticInterfaces.exists_phiPsiData` now delegates to that construction.

### `PhiPsiData` tail consequences

Source location: generic consequences of the `PhiPsiData` interface.

Purpose: make M8 proofs work against the interface rather than the concrete construction.

Statements:

```lean
theorem PhiPsiData.eventually_Tstar_le ...
theorem PhiPsiData.f_eq_tail_eventually ...
theorem PhiPsiData.psi_pos_eventually ...
theorem PhiPsiData.eventually_N0_le_psi ...
theorem PhiPsiData.Phi_psi_eq_eventually ...
theorem PhiPsiData.PhiFormula_psi_eq_eventually ...
theorem PhiPsiData.psi_tendsto_atTop ...
theorem PhiPsiData.inv_psi_tendsto_zero ...
theorem PhiPsiData.f_tendsto_zero ...
```

Proof route: use eventual branch membership for the left-inverse identities; use
`Phi_tendsto_atTop` to choose a large `Phi X`, then compare `psi (Phi X)` and `psi t` through
`psi_mono_tail`; reciprocal convergence follows from `tendsto_inv_atTop_zero`.

Status: proved and compiler-checked in M8 setup.

### `FAsymptotics` inverse-branch algebra

Source location: TeX Part 2, inverse branch of `Phi`.

Purpose: provide exact algebraic and first-order logarithmic setup for the eventual
`f_asymptotic` proof.

Lean module: `FloorSaving/FAsymptotics.lean`.

Statements now available:

```lean
noncomputable def fModel (t : ℝ) : ℝ :=
  Real.sqrt (2 * lam / (t * Real.log t))

noncomputable def IModel (X : ℝ) : ℝ :=
  2 * Real.sqrt (2 * lam * X / Real.log X)

noncomputable def IModelDeriv (X : ℝ) : ℝ :=
  fModel X * (1 - 1 / Real.log X)

theorem fModel_pos_of_one_lt {t : ℝ} (ht : 1 < t) :
    0 < fModel t

theorem fModel_sq_of_one_lt {t : ℝ} (ht : 1 < t) :
    fModel t ^ 2 = 2 * lam / (t * Real.log t)

theorem H_isEquivalent_atTop (B : ℝ) :
    (fun w : ℝ => H B w) ~[Filter.atTop] fun w : ℝ => w

theorem scaleReal_tendsto_atTop :
    Tendsto scaleReal Filter.atTop Filter.atTop

theorem eventually_IModel_eq_two_mul_self_mul_fModel :
    ∀ᶠ X : ℝ in Filter.atTop, IModel X = 2 * X * fModel X

theorem IModel_tendsto_atTop :
    Tendsto IModel Filter.atTop Filter.atTop

theorem const_isLittleO_IModel (c : ℝ) :
    (fun _ : ℝ => c) =o[Filter.atTop] IModel

theorem IModel_pos_of_one_lt {X : ℝ} (hX : 1 < X) :
    0 < IModel X

theorem IModel_hasDerivAt_of_one_lt {X : ℝ} (hX : 1 < X) :
    HasDerivAt IModel (fModel X * (1 - 1 / Real.log X)) X

theorem eventually_IModel_hasDerivAt :
    ∀ᶠ X : ℝ in Filter.atTop,
      HasDerivAt IModel (fModel X * (1 - 1 / Real.log X)) X

theorem one_sub_inv_log_isEquivalent_one :
    (fun X : ℝ => 1 - (Real.log X)⁻¹) ~[Filter.atTop] fun _X : ℝ => 1

theorem IModel_derivFactor_isEquivalent_fModel :
    (fun X : ℝ => fModel X * (1 - (Real.log X)⁻¹)) ~[Filter.atTop] fModel

theorem IModelDeriv_isEquivalent_fModel :
    IModelDeriv ~[Filter.atTop] fModel

theorem integral_IModelDeriv_eq_IModel_sub_of_one_lt_of_le
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ x in a..b, IModelDeriv x = IModel b - IModel a

theorem PhiPsiData.log_psi_tendsto_atTop :
    Tendsto (fun t : ℝ => Real.log (D.psi t)) Filter.atTop Filter.atTop

theorem PhiPsiData.H_log_psi_isEquivalent_log_psi :
    (fun t : ℝ => H B (Real.log (D.psi t))) ~[Filter.atTop]
      fun t : ℝ => Real.log (D.psi t)

theorem PhiPsiData.log_eq_log_lam_add_two_log_psi_sub_log_H_eventually :
    (fun t : ℝ => Real.log t) =ᶠ[Filter.atTop]
      fun t : ℝ =>
        Real.log lam + 2 * Real.log (D.psi t) -
          Real.log (H B (Real.log (D.psi t)))

theorem PhiPsiData.log_isEquivalent_two_log_psi :
    (fun t : ℝ => Real.log t) ~[Filter.atTop]
      fun t : ℝ => 2 * Real.log (D.psi t)

theorem PhiPsiData.f_sq_mul_self_mul_H_log_psi_eq_lam_eventually :
    (fun t : ℝ => D.f t ^ 2 * t * H B (Real.log (D.psi t)))
      =ᶠ[Filter.atTop] fun _t : ℝ => lam

theorem PhiPsiData.f_sq_eq_lam_div_self_mul_H_log_psi_eventually :
    (fun t : ℝ => D.f t ^ 2)
      =ᶠ[Filter.atTop] fun t : ℝ => lam / (t * H B (Real.log (D.psi t)))

theorem PhiPsiData.f_sq_isEquivalent_lam_div_self_mul_log_psi :
    (fun t : ℝ => D.f t ^ 2) ~[Filter.atTop]
      fun t : ℝ => lam / (t * Real.log (D.psi t))

theorem PhiPsiData.f_sq_isEquivalent_model :
    (fun t : ℝ => D.f t ^ 2) ~[Filter.atTop]
      fun t : ℝ => 2 * lam / (t * Real.log t)

theorem PhiPsiData.f_asymptotic :
    D.f ~[Filter.atTop]
      (fun t : ℝ => Real.sqrt (2 * lam / (t * Real.log t)))

theorem PhiPsiData.f_isBigO_model :
    D.f =O[Filter.atTop]
      (fun t : ℝ => Real.sqrt (2 * lam / (t * Real.log t)))

theorem PhiPsiData.eventually_abs_f_sub_fModel_le
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      |D.f t - fModel t| ≤ ε * fModel t

theorem PhiPsiData.eventually_one_sub_mul_fModel_le_f
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      (1 - ε) * fModel t ≤ D.f t

theorem PhiPsiData.eventually_f_le_one_add_mul_fModel
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      D.f t ≤ (1 + ε) * fModel t

theorem PhiPsiData.f_le_const_mul_fModel :
    ∃ C T : ℝ, 0 < C ∧ ∀ t : ℝ, T ≤ t → D.f t ≤ C * fModel t

theorem PhiPsiData.f_upper_bound :
    ∃ C T : ℝ, 0 < C ∧
      ∀ t : ℝ, T ≤ t → D.f t ≤ C / Real.sqrt (t * Real.log t)

theorem PhiPsiData.f_sq_upper_bound :
    ∃ C T : ℝ, 0 < C ∧
      ∀ t : ℝ, T ≤ t → D.f t ^ 2 ≤ C / (t * Real.log t)

theorem PhiPsiData.f_isEquivalent_IModelDeriv :
    D.f ~[Filter.atTop] IModelDeriv

theorem PhiPsiData.eventually_integral_one_sub_mul_IModel_sub_le_f
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in Filter.atTop, ∀ᶠ b : ℝ in Filter.atTop,
      a ≤ b → (1 - ε) * (IModel b - IModel a) ≤ ∫ x in a..b, D.f x

theorem PhiPsiData.eventually_integral_f_le_one_add_mul_IModel_sub
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in Filter.atTop, ∀ᶠ b : ℝ in Filter.atTop,
      a ≤ b → ∫ x in a..b, D.f x ≤ (1 + ε) * (IModel b - IModel a)
```

Dependencies: generic `PhiPsiData` tail consequences, `eventually_H_pos_atTop`, real-log
asymptotics, and eventual positivity/nonzero facts for the implicit denominator.

Square-root transfer note: mathlib's `Asymptotics.IsEquivalent.rpow` requires pointwise
nonnegativity of the right-hand model. The Lean proof uses the eventually equal clipped model
`fun t => max (2 * lam / (t * Real.log t)) 0`, then rewrites back to the unclipped expression
on the tail.

Status: proved and compiler-checked in M8 setup.

### `f_asymptotic`, `integral_f_asymptotic`

Source location: TeX Part 2.

Purpose: first-order analytic estimates.

Status: `f_asymptotic` and `integral_f_asymptotic` are proved in
`FloorSaving/FAsymptotics.lean` and packaged through `FloorSaving/AnalyticInterfaces.lean`. The
integral proof compares `D.f` with the named derivative
model `IModelDeriv`, integrates the two-sided squeeze over a tail interval, splits off the fixed
initial segment of `I D X`, and absorbs it with `const_isLittleO_IModel`.

### `elementary_integral_bound`

Source location: TeX Part 2, equation (8).

Purpose: bound the model tail integral used with `f_upper_bound`.

Lean location: `FloorSaving/FAsymptotics.lean`.

Statements:

```lean
noncomputable def invSqrtLogModel (t : ℝ) : ℝ :=
  1 / Real.sqrt (t * Real.log t)

noncomputable def sqrtLogPrimitive (V : ℝ) : ℝ :=
  Real.sqrt (V / Real.log V)

noncomputable def sqrtLogPrimitiveDeriv (V : ℝ) : ℝ :=
  ((Real.log V - 1) / (2 * Real.log V)) * invSqrtLogModel V

theorem sqrtLogPrimitive_hasDerivAt_of_one_lt {V : ℝ} (hV : 1 < V) :
    HasDerivAt sqrtLogPrimitive (sqrtLogPrimitiveDeriv V) V

theorem elementary_integral_bound {T V : ℝ}
    (hT : Real.exp 2 ≤ T) (hTV : T ≤ V) :
    ∫ t in T..V, invSqrtLogModel t ≤ 4 * sqrtLogPrimitive V
```

Dependencies: `Real.hasDerivAt_log`, `HasDerivAt.sqrt`,
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`,
`intervalIntegral.integral_mono_on`, and continuity of log/sqrt/division on a closed positive
tail.

Status: proved and compiler-checked in M8.

### `eventually_inverse_derivative_model_le_f_over_Phi`

Source location: TeX Part 2, equation (10), algebra after differentiating the inverse branch.

Purpose: isolate the non-inverse-function-theorem part of the derivative bound. If
`t = PhiFormula B r` and `f(t) = 1 / r`, the exact derivative calculation gives the model

```text
H(log r)^2 / (λ r^3 (2H(log r)-H'(log r))).
```

This lemma proves that this expression is eventually bounded by
`(1 / r) / PhiFormula B r`, which is exactly the `f(t) / t` scale on the branch.

Lean location: `FloorSaving/PhiPsiConstruction.lean`.

Statements:

```lean
theorem eventually_H_le_two_mul_H_sub_Hderiv_atTop (B : ℝ) :
    ∀ᶠ w : ℝ in Filter.atTop, H B w ≤ 2 * H B w - Hderiv w

theorem eventually_H_log_le_two_mul_H_log_sub_Hderiv_log_atTop (B : ℝ) :
    ∀ᶠ r : ℝ in Filter.atTop,
      H B (Real.log r) ≤ 2 * H B (Real.log r) - Hderiv (Real.log r)

theorem eventually_inverse_derivative_model_le_f_over_Phi (B : ℝ) :
    ∀ᶠ r : ℝ in Filter.atTop,
      H B (Real.log r) ^ 2 /
          (lam * r ^ 3 *
            (2 * H B (Real.log r) - Hderiv (Real.log r))) ≤
        (1 / r) / PhiFormula B r
```

Dependencies: `eventually_H_log_pos_atTop`, `eventually_H_le_two_mul_H_sub_Hderiv_atTop`,
`Real.isLittleO_log_id_atTop`, and ordered division algebra.

Status: proved and compiler-checked in M8. This does not yet prove differentiability of
`psiBranch`/`fBranch`; it is the algebraic estimate needed once the inverse derivative is in hand.

### `psiBranch_continuousAt_tail_interior`, `fBranch_hasDerivAt_tail_interior`

Source location: TeX Part 2 smooth-tail discussion before equation (10).

Purpose: provide the continuity hypothesis needed by the inverse-derivative theorem for the
constructed inverse branch, then transfer it through the tail definition
`fBranch t = (psiBranch t)⁻¹`.

Lean location: `FloorSaving/PhiPsiConstruction.lean`.

Statements:

```lean
theorem psiBranch_gt_tail_endpoint
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    {t : ℝ} (ht : PhiFormula B (N0 : ℝ) < t) :
    (N0 : ℝ) < psiBranch B N0 t

theorem psiBranch_tail_image_mem_nhds
    (hstrict : StrictMonoOn (PhiFormula B) (Set.Ici (N0 : ℝ)))
    (hmaps : ∀ x : ℝ, (N0 : ℝ) ≤ x →
      PhiFormula B (N0 : ℝ) ≤ PhiFormula B x)
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    {t : ℝ} (ht : PhiFormula B (N0 : ℝ) < t) :
    psiBranch B N0 '' Set.Ici (PhiFormula B (N0 : ℝ)) ∈
      𝓝 (psiBranch B N0 t)

theorem psiBranch_continuousAt_tail_interior
    (hstrict : StrictMonoOn (PhiFormula B) (Set.Ici (N0 : ℝ)))
    (hmaps : ∀ x : ℝ, (N0 : ℝ) ≤ x →
      PhiFormula B (N0 : ℝ) ≤ PhiFormula B x)
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    {t : ℝ} (ht : PhiFormula B (N0 : ℝ) < t) :
    ContinuousAt (psiBranch B N0) t

theorem eventually_psiBranch_continuousAt_tail
    ... :
    ∀ᶠ t : ℝ in Filter.atTop, ContinuousAt (psiBranch B N0) t

theorem psiBranch_hasDerivAt_tail_interior
    (hN0 : 3 ≤ N0)
    (hstrict : StrictMonoOn (PhiFormula B) (Set.Ici (N0 : ℝ)))
    (hmaps : ∀ x : ℝ, (N0 : ℝ) ≤ x →
      PhiFormula B (N0 : ℝ) ≤ PhiFormula B x)
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    {t : ℝ} (ht : PhiFormula B (N0 : ℝ) < t)
    (hH : H B (Real.log (psiBranch B N0 t)) ≠ 0)
    (hnum :
      0 < 2 * H B (Real.log (psiBranch B N0 t)) -
        Hderiv (Real.log (psiBranch B N0 t))) :
    HasDerivAt (psiBranch B N0)
      (lam * psiBranch B N0 t *
        (2 * H B (Real.log (psiBranch B N0 t)) -
          Hderiv (Real.log (psiBranch B N0 t))) /
          (H B (Real.log (psiBranch B N0 t))) ^ 2)⁻¹ t

theorem fBranch_hasDerivAt_tail_interior
    ... :
    HasDerivAt (fBranch B N0)
      (-(lam * psiBranch B N0 t *
        (2 * H B (Real.log (psiBranch B N0 t)) -
          Hderiv (Real.log (psiBranch B N0 t))) /
          (H B (Real.log (psiBranch B N0 t))) ^ 2)⁻¹ /
          (psiBranch B N0 t) ^ 2) t
```

Dependencies: `psiBranch_mono_tail`, `psiBranch_right_inv`, `PhiFormula_psiBranch_eq`,
`Ici_mem_nhds`, `mem_of_superset`, and
`continuousAt_of_monotoneOn_of_image_mem_nhds`; derivative transfer uses
`HasDerivAt.of_local_left_inverse`, `HasDerivAt.inv`, and
`HasDerivAt.congr_of_eventuallyEq`.

Status: proved and compiler-checked in M8. This construction-specific card is retained as
supporting evidence; the generic `PhiPsiData` packaging is now recorded in the next card.

### `PhiPsiData.f_derivative_bound`, `PhiPsiData.f_local_lipschitz`

Source location: TeX Part 2, equations (10) and (12).

Purpose: expose derivative and local Lipschitz control through the stable `PhiPsiData` interface,
so later M9/M10 files can use the estimates without depending on the concrete `psiBranch`
construction.

Lean location: `FloorSaving/FAsymptotics.lean`.

Statements:

```lean
theorem PhiPsiData.psi_gt_tail_endpoint
    (D : PhiPsiData B) {t : ℝ} (ht : D.Tstar < t) :
    (D.N0 : ℝ) < D.psi t

theorem PhiPsiData.psi_continuousAt_tail_interior
    (D : PhiPsiData B) {t : ℝ} (ht : D.Tstar < t) :
    ContinuousAt D.psi t

theorem PhiPsiData.psi_hasDerivAt_tail_interior
    (D : PhiPsiData B) {t : ℝ} (ht : D.Tstar < t)
    (hH : H B (Real.log (D.psi t)) ≠ 0)
    (hnum :
      0 < 2 * H B (Real.log (D.psi t)) -
        Hderiv (Real.log (D.psi t))) :
    HasDerivAt D.psi
      (lam * D.psi t *
        (2 * H B (Real.log (D.psi t)) -
          Hderiv (Real.log (D.psi t))) /
          (H B (Real.log (D.psi t))) ^ 2)⁻¹ t

theorem PhiPsiData.f_hasDerivAt_tail_interior
    (D : PhiPsiData B) {t : ℝ} (ht : D.Tstar < t)
    (hH : H B (Real.log (D.psi t)) ≠ 0)
    (hnum :
      0 < 2 * H B (Real.log (D.psi t)) -
        Hderiv (Real.log (D.psi t))) :
    HasDerivAt D.f
      (-(lam * D.psi t *
        (2 * H B (Real.log (D.psi t)) -
          Hderiv (Real.log (D.psi t))) /
          (H B (Real.log (D.psi t))) ^ 2)⁻¹ /
          (D.psi t) ^ 2) t

theorem PhiPsiData.eventually_f_hasDerivAt_bound
    (D : PhiPsiData B) :
    ∀ᶠ t : ℝ in Filter.atTop,
      ∃ f' : ℝ, HasDerivAt D.f f' t ∧ |f'| ≤ D.f t / t

theorem PhiPsiData.f_derivative_bound
    (D : PhiPsiData B) :
    ∃ C T : ℝ, 0 < C ∧
      ∀ t : ℝ, T ≤ t →
        ∃ f' : ℝ, HasDerivAt D.f f' t ∧ |f'| ≤ C * D.f t / t

theorem PhiPsiData.f_local_lipschitz
    (D : PhiPsiData B) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ C T : ℝ, 0 < C ∧
      ∀ ⦃s t : ℝ⦄, T ≤ t → c * t ≤ s → s ≤ t →
        |D.f s - D.f t| ≤ C * D.f t / t * |t - s|
```

Dependencies: `PhiPsiData` inverse fields, `PhiFormula_hasDerivAt`,
`HasDerivAt.of_local_left_inverse`, `HasDerivAt.inv`,
`eventually_inverse_derivative_model_le_f_over_Phi`,
`PhiPsiData.f_local_comparability`, and
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`.

Status: proved and compiler-checked in M8.

### `fModel_local_comparability`, `PhiPsiData.f_local_comparability`

Source location: TeX Part 2, local comparability estimate before the correction/tail arguments.

Purpose: uniformly compare `f` at two points in a fixed multiplicative window `c * t ≤ s ≤ t`.
This is needed later for M9/M10 tail estimates and for local uniformity in fixed-`Q`
substitutions.

Lean location: `FloorSaving/FAsymptotics.lean`.

Statements:

```lean
theorem fModel_local_comparability {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ C T : ℝ, 0 < C ∧
      ∀ ⦃s t : ℝ⦄, T ≤ t → c * t ≤ s → s ≤ t →
        fModel s ≤ C * fModel t

theorem PhiPsiData.f_local_comparability
    {B : ℝ} (D : PhiPsiData B) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ C T : ℝ, 0 < C ∧
      ∀ ⦃s t : ℝ⦄, T ≤ t → c * t ≤ s → s ≤ t →
        D.f s ≤ C * D.f t
```

Dependencies: `fModel_sq_of_one_lt`, `Real.log_le_log`, `Real.log_mul`,
`Real.le_log_iff_exp_le`, square-root monotonicity through `sq_le_sq₀`, and the existing
eventual squeeze lemmas `PhiPsiData.eventually_f_le_one_add_mul_fModel` and
`PhiPsiData.eventually_one_sub_mul_fModel_le_f`.

Domain issues: the proof chooses a large explicit tail depending on `c` so that
`1 < s`, `1 < t`, and `Real.log s ≥ (1 / 2) * Real.log t`. No theorem is added to
`PhiPsiData`; the estimate is derived from the existing asymptotic interface.

Status: proved and compiler-checked in M8.

### `continuous_majorant_asymptotic`

Source location: TeX Part 6.

Purpose: second-order continuous majorant coefficient.

The current TeX reference now contains the detailed M9 decomposition; the external review remains
background only.

Recommended auxiliary definitions:

```lean
noncomputable def w0 {B : ℝ} (D : PhiPsiData B) (X : ℝ) : ℝ :=
  Real.log (D.psi X)

noncomputable def rX {B : ℝ} (D : PhiPsiData B) (X : ℝ) : ℝ :=
  w0 D X - Real.log X / 2

noncomputable def Rcorr {B : ℝ} (D : PhiPsiData B) (X : ℝ) : ℝ :=
  ∫ t in X..D.Phi X,
    D.f t * ∫ s in (t - X)..t, (D.f s - D.f t)

noncomputable def RcorrTrunc {B : ℝ} (D : PhiPsiData B) (X U : ℝ) : ℝ :=
  ∫ t in X..(U * X),
    D.f t * ∫ s in (t - X)..t, (D.f s - D.f t)

noncomputable def gNorm {B : ℝ} (D : PhiPsiData B) (X v : ℝ) : ℝ :=
  Real.sqrt (X * Real.log X / (2 * lam)) * D.f (X * v)

noncomputable def corrKernel (u : ℝ) : ℝ :=
  2 * (1 - Real.sqrt (1 - 1 / u)) - 1 / u
```

Lemma cards to add before formalizing the final theorem:

- `half_square_asymptotic`: derive
  `(1 / 2) * (I D X)^2 = 4 * lam * X / log X + o(scaleReal)` from
  `integral_f_asymptotic`; status: proved in `FloorSaving/ContinuousMajorant.lean`;
- `GX_eq_X_mul_f_add_correction`: exact interval-integral algebra for `GX`;
- `continuous_integral_square_correction_split`: split the large integral into
  `X * ∫ f^2 + Rcorr`; status: proved in `FloorSaving/ContinuousMajorant.lean` via the
  tail-conditioned split and `Phi_dominates_fixed_multiple`;
- `Phi_dominates_fixed_multiple`: prove `U * X ≤ D.Phi X` eventually for fixed `U`; status:
  proved in `FloorSaving/ContinuousMajorant.lean`;
- branch endpoint helpers: `w0_tendsto_atTop`, `exp_w0_eq_psi_eventually`,
  `Phi_exp_w0_eq_self_eventually`, and `Phi_exp_log_eq_Phi_eventually`; status:
  proved in `FloorSaving/ContinuousMajorant.lean`;
- lower-endpoint support helpers: `w0_isEquivalent_half_log`,
  `H_w0_isEquivalent_half_log`, `log_eq_log_lam_add_two_w0_sub_log_H_w0_eventually`,
  and `rX_eq_half_log_H_w0_sub_log_lam_eventually`; status: proved in
  `FloorSaving/ContinuousMajorant.lean`;
- `lower_endpoint_asymptotic` and `rX_asymptotic`: expand
  `log (D.psi X)`; status: proved in `FloorSaving/ContinuousMajorant.lean`;
- `PhiLog_hasDerivAt_eventually`: derivative of `PhiFormula B (exp w)`; status:
  proved in `FloorSaving/ContinuousMajorant.lean`;
- `PhiLog_deriv_nonneg_eventually`: nonnegativity of the square-change derivative on a tail;
  status: proved in `FloorSaving/ContinuousMajorant.lean`;
- `f_Phi_exp_eq`: branch identity `D.f (D.Phi (exp w)) = exp (-w)` eventually; status:
  proved in `FloorSaving/ContinuousMajorant.lean`;
- `f_sq_integral_square_change_exact`: exact `t = Phi(exp w)` substitution; status:
  proved in `FloorSaving/ContinuousMajorant.lean`;
- reciprocal-`H` derivative support: `H_hasDerivAt`, `H_inv_hasDerivAt`, and
  `H_inv_hasDerivAt_eventually`; status: proved in `FloorSaving/ContinuousMajorant.lean`;
- `transformed_square_integral_split_exact`: exact split of
  `∫ (2 / H - Hderiv / H^2)` into `2∫ 1/H` plus the endpoint reciprocal difference; status:
  proved in `FloorSaving/ContinuousMajorant.lean` using
  `H_inverse_integral_split_of_tail`;
- `inv_integral_w0_log_eq_eventually` and `two_inv_integral_w0_log_eq_eventually`: exact
  rewrites of the `∫dw/w` primitive on the square-change window; status: proved in
  `FloorSaving/ContinuousMajorant.lean`;
- `log_sub_const_div_sq_hasDerivAt`,
  `log_sub_const_div_sq_integral_eq_of_pos`, and
  `log_sub_const_div_sq_integral_w0_log_eq_eventually`: antiderivative and exact primitive
  rewrite for `∫(log w - B)/w²`; status: proved in `FloorSaving/ContinuousMajorant.lean`;
- `H_inv_remainder_integral_isLittleO`: geometric-expansion remainder for
  `(H B w)⁻¹ = w⁻¹ + (log w - B)/w^2 + error` integrated over `[w0,Y]`;
  status: proved in `FloorSaving/ContinuousMajorant.lean` using a moving-window bound from
  `(log w - B)^2 = o(w)`, `H B w ≥ w/2` on a tail, and
  `intervalIntegral.norm_integral_le_of_norm_le_const`;
- `two_inv_integral_asymptotic`: contribution of `2∫dw/w`, retaining the `-4*rX` term;
  status: proved in `FloorSaving/ContinuousMajorant.lean` using
  `two_inv_integral_remainder_identity_eventually`,
  `two_inv_integral_log_remainder_isLittleO`, and the helper estimate
  `rX_sq_div_log_tendsto_zero`;
- `log_sub_const_div_sq_integral_asymptotic`: contribution of
  `2∫(log w - B)/w^2`; status: proved in `FloorSaving/ContinuousMajorant.lean`
  using `log_w0_sub_loglog_tendsto_neg_log_two`, `log_div_w0_tendsto_two`,
  `log_w0_add_const_div_sqrt_log_tendsto_zero`,
  `log_div_w0_sub_two_mul_log_w0_add_const_tendsto_zero`, and
  `log_sub_const_div_sq_integral_algebra`;
- `H_inv_endpoint_diff_asymptotic`: endpoint reciprocal contribution
  `(H(Y))⁻¹ - (H(w0))⁻¹ = -1/Y + o(1/Y)`; status: proved in
  `FloorSaving/ContinuousMajorant.lean`;
- `rX_square_bracket_coefficient_asymptotic`: coefficient cancellation after substituting
  the `rX` expansion; status: proved in `FloorSaving/ContinuousMajorant.lean`;
- `transformed_square_bracket_asymptotic_of_H_inv_remainder`: conditional assembly of the
  square bracket from the named geometric `1/H` remainder; status: proved in
  `FloorSaving/ContinuousMajorant.lean`;
- `transformed_square_bracket_asymptotic` / `H_inverse_square_bracket_asymptotic`:
  cancellation-sensitive assembly of the transformed square bracket; status:
  `transformed_square_bracket_asymptotic` proved in `FloorSaving/ContinuousMajorant.lean`;
- `f_sq_integral_asymptotic` and `square_integral_term_asymptotic`: status proved in
  `FloorSaving/ContinuousMajorant.lean`;
- `gNorm_L1_convergence`: normalized first-order convergence on fixed intervals, proved by
  splitting `(0,U)` into `(0,ε)` and `[ε,U]`; current support proved in
  `FloorSaving/ContinuousMajorant.lean`: `inv_sqrt_intervalIntegrable_zero`,
  `integral_inv_sqrt_zero_eq`, `gNorm_intervalIntegrable`,
  `gNorm_sub_inv_sqrt_abs_intervalIntegrable`, `log_mul_const_div_log_tendsto_one`,
  `log_div_log_mul_const_tendsto_one`, `log_div_log_mul_uniform_sub_one_le`,
  `gNorm_model_eq_inv_sqrt_mul_log_ratio`, `gNorm_model_tendsto_inv_sqrt`,
  `gNorm_tendsto_inv_sqrt`, `gNorm_integral_change_of_variables`,
  `abs_sqrt_sub_one_le_abs_sub_one`, `gNorm_model_uniform_away_bound`,
  `gNorm_sub_model_uniform_relative_bound`, `gNorm_model_uniform_cap`,
  `gNorm_sub_model_uniform_away_bound`, `gNorm_uniform_away_bound`, and
  `gNorm_tendstoUniformlyOn_away`, plus the small-endpoint support
  `gNorm_nonneg`, `abs_sub_le_add_of_nonneg`,
  `gNorm_small_v_L1_bound_of_integral_bound`,
  `gNorm_small_v_L1_eventual_bound_of_integral_eventual_bound`,
  `f_integral_tail_sqrtLogPrimitive_bound`, `gNorm_scale_sqrtLogPrimitive_eq`,
  `gNorm_scale_sqrtLogPrimitive_le`, `eventually_sqrt_log_ratio_mul_const_le_two`,
  `sqrt_log_isLittleO_sqrt_self`, `gNorm_compact_prefactor_tendsto_zero`,
  `gNorm_compact_prefactor_eventually_le_sqrt`,
  `gNorm_small_v_integral_eventual_bound`, and
  `gNorm_small_v_L1_eventual_bound`;
- `RcorrTrunc_normalized_change`: fixed-`U` correction substitution; status proved in
  `FloorSaving/ContinuousMajorant.lean` using `RcorrTrunc_inner_change`,
  `RcorrTrunc_outer_change`, and `RcorrTrunc_normalized_change_of_gt_one`;
- `corrOperator_L1_convergence_fixed_U`: fixed-interval L1 convergence of the normalized
  correction operator to the limiting kernel; status proved in
  `FloorSaving/ContinuousMajorant.lean` using the window L1 helpers and
  `gNorm_L1_convergence`;
- `corrOperator_integral_tendsto_fixed_U`: un-absolute fixed-`U` operator convergence; status
  proved in `FloorSaving/ContinuousMajorant.lean` using
  `corrOperator_L1_convergence_fixed_U`, `corrKernel_intervalIntegrable_of_one_le`, and
  `corrOperator_integrand_intervalIntegrable_of_gt_one`;
- `RcorrTrunc_asymptotic`: fixed-`U` correction limit; status proved in
  `FloorSaving/ContinuousMajorant.lean` from `RcorrTrunc_normalized_change` and
  `corrOperator_integral_tendsto_fixed_U`;
- correction-tail support: status proved in `FloorSaving/ContinuousMajorant.lean`; available
  lemmas are `Rcorr_inner_nonneg_of_le`, `Rcorr_integrand_nonneg_of_le`,
  `Rcorr_tail_integrand_intervalIntegrable_of_order`, `Rcorr_sub_RcorrTrunc_eq_tail`,
  `Rcorr_tail_integral_nonneg_of_order`, `Rcorr_sub_RcorrTrunc_nonneg_of_order`,
  `one_div_sq_intervalIntegrable_of_pos`, `integral_one_div_sq_eq_inv_sub_inv`, and
  `integral_one_div_sq_le_inv_left`;
- `Rcorr_tail_bound`: tail estimate uniform in fixed `U ≥ 2`, with a constant independent of
  `U`; status proved in `FloorSaving/ContinuousMajorant.lean` using
  `Rcorr_inner_lipschitz_bound`, `Rcorr_tail_integrand_le_inv_sq`, and
  `Rcorr_tail_integral_le_of_constants`;
- `corrKernel_integral_tendsto`: kernel integral tends to `2 * log 2 - 1`; status proved in
  `FloorSaving/KernelIntegral.lean`; upstream support includes
  `integral_inv_sqrt_eq_of_nonneg` and `corr_limit_integrand_eq_corrKernel` in
  `FloorSaving/ContinuousMajorant.lean`, plus `corrKernel_continuousOn_Ici_one`,
  `corrKernel_continuousOn_Icc`,
  `corrKernel_aemeasurable_Icc`, `corrKernel_intervalIntegrable`,
  `corrKernel_one_add_eq`, `transformedKernel_antideriv_hasDerivAt`,
  `transformedKernel_integral_eq`, `transformedKernel_integral_eq_two_mul`,
  `corrKernel_integral_eq_transformed`, and `corrKernel_integral_eq_closed`;
- `correction_asymptotic`;
- `large_continuous_integral_asymptotic`;
- `continuous_coefficient_identity`: status proved in `FloorSaving/ContinuousMajorant.lean`;
- `continuous_majorant_asymptotic`;
- `continuous_majorant_asymptotic_nat`.

Needs local discovery:

- exact `intervalIntegral` subtraction/constant algebra for `GX`; status: checked for
  `GX_eq_X_mul_f_add_correction`;
- derivative simplification and substitution theorem names; status: checked locally for
  `f_sq_integral_square_change_exact`;
- unordered FTC and interval-integral algebra for the reciprocal-`H` split; status: checked
  locally and proved as `H_inverse_integral_split_of_tail` and
  `transformed_square_integral_split_exact`;
- product and correction-integrand interval-integrability;
- Taylor/log expansion approach for `1 / H B w`;
- whether to use explicit epsilon splitting rather than dominated convergence for
  `gNorm_L1_convergence`; status: explicit epsilon split retained, with the uniform log-ratio
  and small-`v` change-of-variables support now checked locally and assembled;
- real-log algebra for `continuous_coefficient_identity`; status: checked locally and proved.
- correction-kernel continuity, transformed-kernel antiderivative, monotone substitution, and
  limit APIs; status: checked locally and proved in `FloorSaving/KernelIntegral.lean`.

Status: M9 in progress. `continuous_coefficient_identity`, the exact square-integral
substitution, the lower-endpoint constant expansion, the reciprocal-`H` split, the exact
primitive-integral rewrites, the `2∫dw/w` asymptotic, the `2∫(log w-B)/w²` asymptotic,
the endpoint reciprocal asymptotic, the geometric `1/H` remainder, the square-bracket
assembly, `f_sq_integral_asymptotic`, the square-integral term, and the pointwise/integrability
support for `gNorm` are proved; the away-from-zero uniform convergence piece is proved, and the
small-`v` integral, small-`v` L1 piece, and full fixed-interval `L¹` assembly are proved.
The fixed-`U` correction substitution is proved, including the pointwise limit-kernel identity.
The fixed-`U` correction operator convergence, `RcorrTrunc_asymptotic`,
`corrKernel_integral_tendsto`, `Rcorr_tail_bound`, `correction_asymptotic`,
`large_continuous_integral_asymptotic`, and the public `continuous_majorant_asymptotic`
interfaces are proved. M9 is complete; the next proof block is `floor_saving_asymptotic`.

### `floor_saving_asymptotic`

Source location: TeX Part 7.

Purpose: floor-saving coefficient.

The current TeX reference now contains the detailed M10 fixed-`Q` truncation and order-of-limits
plan; the external review remains background only.

Recommended auxiliary definitions:

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

Recommended proof cut points:

- fractional-part infrastructure: bridge project `fract` to `Int.fract`, prove
  nonnegativity, `< 1`, measurability, and an away-from-integers Lipschitz lemma;
- `qOf_eq_X_mul_f_of_tail` and `qOf_Phi_X_div_q` on the inverse branch; status:
  proved in `FloorSaving/FloorSavingIntegral.lean`;
- fixed-`Q` order and branch facts: eventually `X / Q ≥ D.N0`,
  `D.Tstar ≤ D.Phi (X / Q)`, `X ≤ D.Phi (X / Q)`, `D.Phi (X / Q) ≤ D.Phi X`,
  and `1 ≤ qOf D X t ≤ Q` on the truncated interval; status: proved as
  `eventually_fixedQ_branch_order` and `eventually_qOf_mem_Icc_on_main_interval`;
- `PhiDerivOverR`, `Phi_hasDerivAt_tail`, and fixed-`Q` derivative uniformity:
  `D.PhiDeriv (X/q) / (X/q) = 2 * lam / Real.log X + o_Q(1 / Real.log X)`
  uniformly for `q ∈ [1,Q]`; status: derivative formula, q-parametrized differentiability,
  continuity, and eventual nonnegative derivative are proved as `PhiDerivFormula`,
  `PhiDerivOverR`, `eventually_Phi_hasDerivAt_X_div_q_on_Icc`,
  `eventually_Phi_comp_X_div_continuousOn`, and
  `eventually_PhiDerivFormula_nonneg_X_div_q_on_Icc`; uniform estimates are proved as
  `eventually_jacobian_weight_uniform_fixed_Q` and
  `eventually_PhiDerivOverR_uniform_fixed_Q`;
- fixed-`Q` growth of `D.Phi (X / q)` and branch facts for `q ∈ [1,Q]`; status:
  branch facts, `eventually_two_mul_X_le_Phi_X_div_q_on_Icc`, and
  `eventually_Phi_X_div_q_lower_uniform_fixed_Q` are proved;
- local Lipschitz estimate for `D.f` on `[t/2,t]`;
- measurability/integrability of `GX` and the `Efloor` integrand;
- `q_change_uniform_fixed_Q`, with bounded measurable `F` quantified inside the
  eventual statement; status: the exact `EfloorMain` q-change is proved as
  `eventually_q_change_exact_fixed_Q`, with Jacobian
  `X / q^2 * PhiDerivOverR B (X/q)`; bounded-test-function normalization core is proved as
  `q_change_error_integral_bound` and `eventually_q_change_uniform_fixed_Q_core`; the dynamic
  `EfloorMain` wrapper is proved as `eventually_q_change_uniform_fixed_Q`;
- uniform estimate `GX D X (D.Phi (X / q)) = q + O(log X / X)` for fixed `Q`; status: proved
  as `GX_Phi_X_div_q_uniform_fixed_Q`;
- finite good/bad integer-neighborhood decomposition on `[1,Q]`; status: proved as
  `integerWindowIndex`, `integerWindow`, `integerWindowUnion`, `intBadSet`, `intGoodSet`, with
  membership and measurability lemmas;
- same-component Lipschitz lemma for `fract` away from the integer-neighborhood bad set; status:
  proved as `floor_eq_of_mem_intGoodSet_of_abs_sub_lt`,
  `fract_sub_fract_eq_of_mem_intGoodSet_of_abs_sub_lt`, and
  `abs_fract_sub_fract_eq_of_mem_intGoodSet_of_abs_sub_lt`;
- fixed-`Q` convergence of
  `∫_1^Q fract (GX D X (D.Phi (X/q))) / q^2`; status: proved as
  `fract_integral_convergence_fixed_Q`, using `fract_integral_close_fixed_Q_of_uniform_close`
  and `eventually_GX_Phi_X_div_q_close_fixed_Q`;
- `floor_main_truncation_fixed_Q`; status: proved from the q-change wrapper and fixed-`Q`
  fractional convergence;
- `Efloor_split_fixed_Q`; status: proved as
  `eventually_Efloor_eq_tail_add_main_fixed_Q` and
  `eventually_Efloor_eq_main_add_tail_fixed_Q`;
- nonnegative large-q tail and `EfloorTail_bound_uniform_Q`, normalized as `O(1/Q)` with a
  constant independent of `Q`; status: proved in `FloorSaving/FloorSavingIntegral.lean` via
  the `f_upper_bound` / `elementary_integral_bound` route;
- `IfractQ_tendsto_IfractInf`; status: proved, with `IfractInf_eq_one_sub_euler`;
- `floor_saving_normalized_limit`; status: proved by the fixed-`Q` main truncation,
  Q-independent tail bound, and `IfractQ_tendsto_IfractInf`;
- `floor_saving_asymptotic_of_normalized`; status: proved;
- `floor_saving_asymptotic`; status: proved in `AnalyticInterfaces.lean`;
- `floor_saving_asymptotic_nat`; status: proved in `AnalyticInterfaces.lean`.

Order of limits:

```text
fix Q > 1
choose epsilon-neighborhoods of integers in [1,Q]
take X -> infinity on the good set
then epsilon -> 0
then Q -> infinity using a uniform O(1/Q) tail bound
```

Status: M10 complete. The fixed-`Q` scaffold, endpoint/range/order lemmas, exact split,
nonnegativity helpers, uniform large-`q` tail bound, exact q-change, uniform Jacobian estimate,
uniform `GX(Phi(X/q))` estimate, bounded-test q-change core, finite integer-window stability,
dynamic `EfloorMain` q-change wrapper, fixed-`Q` fractional convergence, fixed-`Q` main
truncation, final normalized sandwich, `IfractQ_tendsto_IfractInf`, and Euler
fractional-integral identity are proved. M11 endpoint limsup packaging is now proved below.

## L11: endpoint limsup packaging

### `endpointSeq`

Source location: TeX endpoint theorem.

Purpose: totalize the normalized endpoint expression over `ℕ`, with the value at `0` irrelevant
for `Filter.atTop`.

Statement:

```lean
noncomputable def endpointSeq
    (A : Set ℕ) (hA : UniquePositiveDiffs A) (n : ℕ) : ℝ :=
  if hn : 0 < n then
    (top A hA ⟨n, hn⟩ : ℝ) * denom B₁ n / (n : ℝ)^2
  else 0
```

### `denom_ratio_tendsto_one`

Purpose: compare the final denominator at `B₁` with the already proved lower-bound denominator
at a fixed `B > B₁`.

Statement:

```lean
theorem denom_ratio_tendsto_one (B : ℝ) :
    Tendsto (fun n : ℕ => denom B₁ n / denom B n) Filter.atTop (𝓝 (1 : ℝ))
```

Dependencies: `H_log_div_log_tendsto_one`, `H_log_nat_eq_denom`,
`tendsto_natCast_atTop_atTop`, eventual positivity of `Real.log n`.

### `endpoint_frequently_lower_bound`

Purpose: convert the infinitely-often lower bound with any fixed `B > B₁` into the endpoint
normalization at `B₁`.

Statement:

```lean
theorem endpoint_frequently_lower_bound
    (A : Set ℕ) (hA : UniquePositiveDiffs A) {c : ℝ} (hc : c < lam) :
    ∃ᶠ n : ℕ in Filter.atTop, c < endpointSeq A hA n
```

Proof route: take `B = B₁ + 1`; use `denom_ratio_tendsto_one B` and `hc` to get eventually
`c < lam * denom B₁ n / denom B n`; combine this eventual condition with
`floor_saving_lower_bound A hA B` at an arbitrarily large threshold; multiply the strict lower
bound by the positive factor `denom B₁ n / n^2`.

### `endpoint_limsup`

Purpose: final endpoint consequence.

Statement:

```lean
theorem endpoint_limsup
    (A : Set ℕ) (hA : UniquePositiveDiffs A) :
    (lam : EReal) ≤ Filter.limsup
      (fun n : ℕ => (endpointSeq A hA n : EReal)) Filter.atTop
```

Proof route: use `Filter.le_limsup_iff'` in `EReal`. For a real `y < lam`, apply
`endpoint_frequently_lower_bound` and coerce with `EReal.coe_le_coe_iff`; the `⊥` case is
immediate and the `⊤` case is impossible from `y < (lam : EReal)`.

Status: proved and compiler-checked in `FloorSaving/EndpointLimsup.lean`.

### `integral_fract_div_sq`

Source location: floor-saving constant.

Purpose: prove `∫₁∞ {q}/q² dq = 1 - γ`.

Expected APIs: local discovery confirmed the relevant `ZetaAsymptotics` declarations:

```lean
ZetaAsymptotics.term
ZetaAsymptotics.term_one
ZetaAsymptotics.term_sum_one
ZetaAsymptotics.term_tsum_one
```

Preferred proof route:

1. Prove the project `fract` agrees with `Int.fract`, or bridge just on unit intervals.
2. On each interval `[n,n+1]`, rewrite `fract q` as `q - n`.
3. Identify the unit integral with `ZetaAsymptotics.term n 1`.
4. Use `ZetaAsymptotics.term_tsum_one`.
5. Connect the unit-interval sum to the `Set.Ioi (1 : ℝ)` integral.

Status: proved in `FloorSaving/FractionalIntegral.lean` as
`integral_fract_div_sq_Ioi`, and exposed through `AnalyticInterfaces.integral_fract_div_sq`.
