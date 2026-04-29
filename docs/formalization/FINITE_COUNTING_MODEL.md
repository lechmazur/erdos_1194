# Finite counting model

This proof uses exact finite counting identities. Do not formalize them with raw set cardinality until the finite wrappers are stable.

## Current wrappers

Location: `FloorSaving/Counting.lean`.

```lean
noncomputable def natCut (A : Set ℕ) (T : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor T + 1)).filter (fun a : ℕ => a ∈ A)

noncomputable def Ncount (A : Set ℕ) (T : ℝ) : ℕ :=
  (natCut A T).card

noncomputable def bottomWindow (A : Set ℕ) (X t : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun b : ℕ => b ∈ A ∧ t - X ≤ b)
```

The wrapper `bottomWindow A X t` represents:

```text
{ b ∈ A : t - X ≤ b < t }
```

Natural subtraction is saturated. This is intentional: when `t < X`, the real condition `t - X ≤ b` is automatic for natural `b`, and the saturated lower bound `0` has the same effect.

## Membership lemmas

Proved:

```lean
theorem mem_bottomWindow_iff {A : Set ℕ} {X t b : ℕ} :
    b ∈ bottomWindow A X t ↔ b ∈ A ∧ t - X ≤ b ∧ b < t
```

Proved:

```lean
theorem mem_natCut_iff {A : Set ℕ} {T : ℝ} {a : ℕ} (hT : 0 ≤ T) :
    a ∈ natCut A T ↔ a ∈ A ∧ (a : ℝ) ≤ T
```

If the `Nat.floor` API makes this statement awkward, use the following alternative wrapper:

```lean
noncomputable def natCutNat (A : Set ℕ) (M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter (fun a : ℕ => a ∈ A)
```

and bridge real cutoffs with `Nat.floor` only at the API boundary.

Record any switch in `docs/DECISIONS.md`.

No wrapper switch was needed. The proof uses `Nat.le_floor`, `Nat.floor_le`, and
`Nat.lt_add_one_iff`.

## Exact top-counting identity

Current target:

```lean
theorem top_counting_identity
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∀ᶠ X : ℕ in Filter.atTop,
      X = ∑ t ∈ natCut A (D.Phi (X : ℝ)), (bottomWindow A X t).card
```

This is equivalent to a cardinality statement for a sigma-type:

```text
Σ t ∈ natCut A (D.Phi X), bottomWindow A X t
```

The Lean proof now proves the sigma-type cardinality first and derives the sum identity
with `Finset.card_sigma`.

## Bijection model

For sufficiently large `X`, define:

```text
S_X = {n : ℕ | 1 ≤ n ∧ n ≤ X}
P_X = {(t,b) | t ∈ A, t ≤ Phi X, b ∈ A, t - X ≤ b, b < t}
```

Cardinality proof maps:

```text
S_X → P_X,    n ↦ (top n, bot n)
```

Surjectivity uses the reverse assignment `(t,b) ↦ t - b`.

Key facts:

- positivity: `b < t` gives `0 < t - b`;
- upper bound: `t - X ≤ b` gives `t - b ≤ X`;
- injectivity: equal selected pairs have equal represented differences;
- surjectivity: every `(t,b) ∈ P_X` is the selected pair for `t - b`, by uniqueness;
- top counted: eventual upper bound gives `top n ≤ Phi n`; monotonicity gives `Phi n ≤ Phi X` for `n ≤ X`.

## Small-top contribution

For `t ≤ X`, the lower condition `t - X ≤ b` is automatic. The small-top sum should be controlled by roughly:

```text
choose(Ncount A X, 2)
```

In Lean, avoid relying on a closed-form binomial identity until necessary. It is enough to prove the upper bound needed for `fundamental_upper_bound`.

Current finite results:

```lean
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

The next step is the analytic error version that replaces `Ncount A X` using
`counting_function_bound` and absorbs the cross/constant terms into `o(X / log X)`.

The current TeX notation writes this integral as `F(X)`. The Lean API keeps the earlier name
`I D X` for the same quantity.

## Counting-function majorant

The M4 proof avoids constructing a global enumeration of `A`.

Given the threshold `Z0` from `gap_integral_ge_one`, split the finite cut
`S = natCut A T` into:

```lean
Ssmall = S.filter (fun a => a ≤ Z0)
Slarge = S.filter (fun a => ¬ a ≤ Z0)
```

The small side is bounded by `Z0 + 1` because it maps into `Finset.range (Z0 + 1)`.

For the large side, use `Finset.induction_on_max`. If the current finite set is nonempty and
`a` is inserted above all previous elements, let `y` be the maximum of the previous set. The
induction hypothesis bounds the previous set by `1 + ∫₀ʸ f`, and `gap_integral_ge_one y a`
adds one unit on `∫ᵧᵃ f`. Interval additivity gives the bound up to `a`, and nonnegativity of
`f` extends it from `a` to the ambient cutoff `T`.

## Large-top contribution

For `X < t ≤ Phi X`, the bottom window length is controlled by:

```text
floor(G_X(t))
```

The continuous majorant is obtained by replacing floors with values, and the floor-saving term is the fractional-part correction.

The current TeX separates the large-top range from the fixed short interval:

```text
t ≤ X,    X < t ≤ X + Z0,    X + Z0 < t ≤ Phi X.
```

This helps the Lean plan: the short interval has at most `Z0` integer tops and can be handled
with a separate `Ncount A (X + Z0)` estimate before proving the large-top floor/integral
domination.

Current finite short-interval results:

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

The analytic `o(X/log X)` form still needs the `N(X+Z0)` estimate from the current TeX Part 2.

Current finite large-top floor results:

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

The next finite assembly step is to split the `top_counting_identity` sum into
`t ≤ X`, `X < t ≤ X + Z0`, and `X + Z0 < t`, then connect the last floor sum to
`JB D X - Efloor D X` through the analytic counting/majorant estimates.

Current finite split assembly:

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

theorem exists_top_counting_three_part_bound
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∃ Z0 : ℕ,
      ∀ᶠ X : ℕ in Filter.atTop,
        (X : ℝ) ≤
          (1 / 2 : ℝ) * (Ncount A (X : ℝ) : ℝ) ^ 2 +
            (Z0 : ℝ) * (Ncount A (((X + Z0 : ℕ) : ℝ)) : ℝ) +
              ∑ t ∈ (natCut A (D.Phi (X : ℝ))).filter (fun t : ℕ => X + Z0 < t),
                ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ)
```

This is the current M5 bridge from exact top-counting to analytic error management. The small
filtered part is bounded by the full `natCut A X` contribution, so no separate proof of
`X ≤ D.Phi X` is needed for this finite split.

The common right side is named:

```lean
noncomputable def smallShortMajorant
    (A : Set ℕ) (Z0 X : ℕ) : ℝ

noncomputable def largeFloorSum
    {B : ℝ} (A : Set ℕ) (D : PhiPsiData B) (Z0 X : ℕ) : ℝ

noncomputable def threePartMajorant
    {B : ℝ} (A : Set ℕ) (D : PhiPsiData B) (Z0 X : ℕ) : ℝ
```

The M5 estimates are isolated as:

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
```

`small_short_error_bound` and `large_floor_sum_error_bound` are proved. The large-floor estimate
uses the same `Z0` and `hgap` supplied by `gap_integral_ge_one`. `three_part_error_bound` and
`fundamental_upper_bound` are proved by combining these estimates with
`top_counting_three_part_bound`.

The natural-tail continuous floor-integral rewrite is now compiler-checked:

```lean
theorem eventually_natCast_le_Phi
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (X : ℝ) ≤ D.Phi (X : ℝ)

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

The endpoint loss support is also checked:

```lean
theorem GX_le_I_of_nonneg_window ...
theorem floor_GX_le_I_of_nonneg_window ...
```

The weighted finite-chain domination of the large finite floor sum by this continuous floor
integral is now proved, with endpoint loss absorbed by `I D X = o(scaleNat X)`.

## Coercion checklist

Before proving counting identities, discover and record theorem names for:

```lean
Nat.cast_le
Nat.cast_lt
Nat.cast_sub
Nat.sub_pos_of_lt
Nat.sub_le_iff_le_add
Finset.sum_bij
Finset.card_sigma
Finset.mem_filter
Finset.mem_range
```

Add exact local theorem names to `docs/MATHLIB_DISCOVERY.md`.
