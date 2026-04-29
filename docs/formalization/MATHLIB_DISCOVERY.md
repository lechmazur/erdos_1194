# Mathlib discovery log

Populate this file with local `#check`, `#find`, `#print`, grep, and build results. Local mathlib source is the authority.

## Setup commands

After copying this kit into a Lean project, run:

```bash
lake env lean Scratch/Discovery.lean
```

If a `#check` fails, comment it out in `Scratch/Discovery.lean`, rerun, and record the replacement theorem name here.

## Required discovery topics

### Euler constant and harmonic asymptotics

Initial checks:

```lean
#check Real.eulerMascheroniConstant
#check Real.tendsto_harmonic_sub_log
```

Search paths:

```text
Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean
Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean
```

Need for:

- `B₁`;
- `integral_fract_div_sq`.

### Asymptotics

Initial checks:

```lean
#check Asymptotics.IsBigO
#check Asymptotics.IsLittleO
#check Asymptotics.IsEquivalent
```

Need theorem names for:

- little-o addition/subtraction;
- multiplying by constants;
- eventual inequality from little-o;
- restriction from real `atTop` to natural sequence if deriving nat versions.

### Interval integrals

Initial checks:

```lean
#check intervalIntegral.integral_comp_mul_deriv''
#check intervalIntegral.integral_add_adjacent_intervals
```

Need theorem names for:

- interval integral monotonicity;
- lower bound for monotone/antitone functions;
- integrability of monotone functions;
- substitution on intervals;
- splitting integrals over adjacent intervals.

### Floors and fractional part

Initial checks:

```lean
#check Int.floor
#check Nat.floor
```

Need theorem names for:

- `a ∈ range (Nat.floor T + 1) ↔ (a : ℝ) ≤ T` under `0 ≤ T`;
- integer floor inequalities;
- measurability of floor/fract;
- decomposition `x = floor x + fract x`.

### Filters and atTop extraction

Initial checks:

```lean
#check Filter.Eventually
#check Filter.atTop
```

Need theorem names for:

- extracting a natural threshold from `∀ᶠ n : ℕ in atTop, P n`;
- combining eventual properties;
- converting `¬ ∀ᶠ` to arbitrarily large counterexamples.

### Finsets

Initial checks:

```lean
#check Finset.card
#check Finset.sum_bij
#check Finset.card_filter
#check Finset.mem_filter
#check Finset.mem_range
```

Need theorem names for:

- sigma/cardinality of dependent finite sets;
- finite maximum over a filtered range;
- sum/cardinality relation for bottom windows.

### Limsup

Run later, near M11:

```lean
#check Filter.limsup
#check Filter.limsInf
#check Filter.limsSup
```

Record exact endpoint API before stating the endpoint theorem.

## Discovery results

### 2026-04-28 M0 setup smoke discovery

Command:

```bash
PATH="$HOME/.elan/bin:$PATH" lake env lean Scratch/Discovery.lean
```

Result: succeeded with `import Mathlib` under Lean `4.30.0-rc2` and mathlib rev
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

Confirmed declarations:

```lean
Real.eulerMascheroniConstant : ℝ
Real.tendsto_harmonic_sub_log :
  Filter.Tendsto (fun n => ↑(harmonic n) - Real.log ↑n) Filter.atTop
    (nhds Real.eulerMascheroniConstant)

Asymptotics.IsBigO
Asymptotics.IsLittleO
Asymptotics.IsEquivalent

intervalIntegral.integral_comp_mul_deriv''
intervalIntegral.integral_add_adjacent_intervals

Int.floor
Nat.floor

Filter.Eventually
Filter.atTop

StrictMonoOn
MonotoneOn
AntitoneOn

Set.ncard
Finset.card
Finset.sum_bij
Fintype.card_congr
Finset.card_filter
Finset.mem_filter
Finset.mem_range

Nat.sub_le
Nat.sub_pos_of_lt
Nat.le_sub_iff_add_le'
```

No initial `#check` failed. The commented candidate groups in `Scratch/Discovery.lean` still need
targeted discovery before the relevant proof cards.

### 2026-04-28 finite wrapper APIs

For `mem_natCut_iff`, these local checks succeeded:

```lean
#check Nat.floor_le
#check Nat.lt_floor_add_one
#check Nat.le_floor
#check Nat.cast_le
#check Nat.cast_lt
#check Nat.lt_add_one_iff
```

Used declarations:

```lean
Nat.floor_le {a : ℝ} (ha : 0 ≤ a) : (Nat.floor a : ℝ) ≤ a
Nat.le_floor {a : ℝ} {n : ℕ} (h : (n : ℝ) ≤ a) : n ≤ Nat.floor a
Nat.lt_add_one_iff : m < n + 1 ↔ m ≤ n
Nat.cast_le : (m : ℝ) ≤ (n : ℝ) ↔ m ≤ n
```

For finite sums over a finset, this Lean version accepts:

```lean
∑ t ∈ s, f t
```

The form `∑ t in s, f t` does not parse under the current toolchain.

### 2026-04-28 denominator positivity APIs

For `eventually_denom_pos`, these local checks were used:

```lean
#check tendsto_natCast_atTop_atTop
#check Real.tendsto_log_atTop
#check Real.isLittleO_log_id_atTop
#check Tendsto.eventually_ge_atTop
#check Tendsto.eventually_gt_atTop
```

Useful declarations:

```lean
Real.tendsto_log_atTop : Tendsto Real.log Filter.atTop Filter.atTop
Real.isLittleO_log_id_atTop : Real.log =o[Filter.atTop] id
tendsto_natCast_atTop_atTop : Tendsto Nat.cast Filter.atTop Filter.atTop
Filter.Tendsto.eventually_ge_atTop
Filter.Tendsto.eventually_gt_atTop
```

### 2026-04-28 spacing APIs

For `spacing`, a targeted scratch check showed that the rough `Finset.sup` plan was not the right
local API: `Finset.sup_of_mem` is a `WithBot` existence lemma in this mathlib snapshot. The proof
uses a concrete nonempty finite set and `Finset.max'` instead.

Useful declarations:

```lean
Filter.eventually_atTop :
  (∀ᶠ x in Filter.atTop, p x) ↔ ∃ a, ∀ b ≥ a, p b

Finset.max' : (s : Finset α) → s.Nonempty → α
Finset.le_max' : (s : Finset α) → (x : α) → x ∈ s → x ≤ s.max' _
Finset.insert_nonempty
Finset.mem_insert
Finset.mem_image

exists_nat_gt
Nat.sub_pos_of_lt
Nat.lt_of_not_ge
Nat.cast_le
Nat.cast_lt
```

Project declarations used with those mathlib APIs:

```lean
repPair_eq_of_represents
PhiFormula_nat_eq_lowerBoundRHS
PhiPsiData.psi_le_of_le_Phi
```

### 2026-04-28 interval-integral lower bound APIs

For `gap_integral_ge_one`, these local declarations were used:

```lean
intervalIntegral.integral_mono_on :
  a ≤ b →
  IntervalIntegrable f μ a b →
  IntervalIntegrable g μ a b →
  (∀ x ∈ Set.Icc a b, f x ≤ g x) →
  ∫ u in a..b, f u ∂μ ≤ ∫ u in a..b, g u ∂μ

intervalIntegral.intervalIntegrable_const :
  IntervalIntegrable (fun _ : ℝ => c) μ a b

intervalIntegral.integral_const :
  ∫ x in a..b, c = (b - a) • c
```

Related order/cast declarations:

```lean
AntitoneOn
Set.Icc
Set.Ici
one_div_le_one_div_of_le
mul_le_mul_of_nonneg_left
mul_inv_cancel₀
Nat.cast_sub
Nat.cast_lt
Nat.cast_nonneg
```

### 2026-04-28 finite max-induction counting APIs

For `counting_function_bound`, the finite cut is split at the gap threshold, and the large side is
handled by max-erasure induction rather than a sorted list.

Useful declarations:

```lean
Finset.induction_on_max :
  (s : Finset α) →
  motive ∅ →
  (∀ a s, (∀ x ∈ s, x < a) → motive s → motive (insert a s)) →
  motive s

Finset.max' : (s : Finset α) → s.Nonempty → α
Finset.max'_mem
Finset.le_max'
Finset.not_nonempty_iff_eq_empty
Finset.card_insert_of_notMem

Finset.card_filter_add_card_filter_not
Finset.card_le_card
Finset.card_range
Finset.mem_filter
Finset.mem_range

intervalIntegral.integral_add_adjacent_intervals
intervalIntegral.integral_nonneg
```

Related arithmetic/cast declarations:

```lean
Nat.lt_add_one_iff
Nat.lt_of_not_ge
Nat.cast_add
Nat.cast_le
Nat.cast_nonneg
```

### 2026-04-28 top-counting finite-cardinality APIs

For `top_counting_identity`, the recommended model is to prove a cardinality equality for a sigma
finset and then rewrite it to the target sum.

Useful declarations verified locally by a read-only explorer:

```lean
Finset.sigma
Finset.mem_sigma
Finset.card_sigma
Finset.sum_sigma
Finset.sum_sigma'
Finset.sum_attach
Finset.card_attach
Finset.card_bij
Finset.card_bij'
Finset.sum_bij
Finset.sum_bij'
Finset.card_eq_sum_ones
Finset.mem_attach
Nat.card_Icc
Nat.sub_le_iff_le_add
Filter.eventually_atTop
Tendsto.eventually_ge_atTop
```

### 2026-04-28 small-top finite-counting APIs

For the finite small-top identity, `Finset.induction_on_max` gives a direct proof that summing
the number of predecessors in a finite set counts two-element subsets.

Useful declarations:

```lean
Finset.induction_on_max
Finset.sum_insert
Finset.sum_congr
Finset.mem_filter
Finset.mem_insert
Finset.card_insert_of_notMem
Nat.choose_succ_succ'
Nat.choose_one_right
Nat.choose_le_pow_div
```

Alternative APIs found but not used in the committed proof:

```lean
Finset.offDiag
Finset.mem_offDiag
Finset.card_sym2
Finset.sum_sym2_filter_not_isDiag
Finset.powersetCard
Finset.card_powersetCard
```

### 2026-04-28 short-interval finite-counting APIs

For the finite short-top contribution in `(X, X+Z]`, the useful interval cardinality theorem is
the natural-number theorem:

```lean
Nat.card_Ioc :
  (Finset.Ioc a b).card = b - a

Finset.sum_le_sum
Finset.card_le_card
Nat.mul_le_mul_right
```

The simplifier can close `(Finset.Ioc X (X + Z)).card = Z`, but `Nat.card_Ioc` is the
explicit theorem to use in robust proofs.

This local example compiles:

```lean
example (A : Set ℕ) (X : ℕ) (T : ℝ) :
    (Finset.sigma (natCut A T) (fun t => bottomWindow A X t)).card =
      ∑ t ∈ natCut A T, (bottomWindow A X t).card := by
  simpa using
    (Finset.card_sigma (natCut A T) (fun t => bottomWindow A X t))
```

For the final cardinal rewrite, use `Nat.card_Icc`, not `Finset.card_Icc`:

```lean
Nat.card_Icc (a b : ℕ) :
  (Finset.Icc a b).card = b + 1 - a
```

The following local shape compiles:

```lean
example {B : ℝ} (A : Set ℕ) (D : PhiPsiData B) (X : ℕ)
    (hcard :
      (Finset.Icc 1 X).card =
        ((natCut A (D.Phi (X : ℝ))).sigma
          (fun t : ℕ => bottomWindow A X t)).card) :
    X = (∑ t ∈ natCut A (D.Phi (X : ℝ)), (bottomWindow A X t).card) := by
  calc
    X = (Finset.Icc 1 X).card := by
      simp
    _ = ((natCut A (D.Phi (X : ℝ))).sigma
          (fun t : ℕ => bottomWindow A X t)).card := hcard
    _ = (∑ t ∈ natCut A (D.Phi (X : ℝ)), (bottomWindow A X t).card) := by
      rw [Finset.card_sigma]
```

### 2026-04-28 fractional part and Euler constant APIs

Local source search confirmed that mathlib has `Int.fract` and the basic fractional-part
lemmas in `Mathlib/Algebra/Order/Floor/Defs.lean` and
`Mathlib/Algebra/Order/Floor/Ring.lean`:

```lean
Int.fract
Int.fract_nonneg
Int.fract_lt_one
Int.self_sub_fract
Int.floor_le
Int.floor_nonneg
Int.floor_le_floor
Int.abs_fract
Int.fract_add_intCast
Int.fract_eq_fract
```

`Mathlib/MeasureTheory/Function/Floor.lean` also provides:

```lean
measurable_fract : Measurable (Int.fract : R → R)
Measurable.fract
```

The project definition in `FloorSaving/AnalyticInterfaces.lean` now uses:

```lean
noncomputable def fract (x : ℝ) : ℝ := Int.fract x
```

Checked project bridge lemmas:

```lean
fract_nonneg
fract_lt_one
fract_mem_Ico
fract_measurable
sub_fract_eq_floor
floor_GX_eq_GX_sub_fract
floor_GX_le_GX
floor_GX_le_I_of_nonneg_window
floor_GX_nonneg_of_nonneg_window
floor_GX_antitoneOn_Ici
floor_integrand_eq_sub
```

For sliding-window monotonicity of `GX`, local interval-integral APIs used were:

```lean
IntervalIntegrable.comp_add_right
intervalIntegral.integral_comp_add_right
intervalIntegral.integral_mono_on
```

For primitive continuity and measurability of the moving-window integral, local APIs used were:

```lean
intervalIntegral.continuous_primitive
intervalIntegral.integral_interval_sub_left
Continuous.measurable
Measurable.comp
```

These prove:

```lean
I_continuous
GX_eq_primitive_sub
GX_continuous_in_t
GX_measurable_in_t
fract_GX_measurable
```

For product integrability of monotone tail integrands, local APIs used were:

```lean
AntitoneOn.intervalIntegrable
Set.uIcc_of_le
mul_le_mul
```

For the bounded fractional-part product, local APIs used were:

```lean
IntervalIntegrable.mono_fun'
Measurable.aestronglyMeasurable
MeasureTheory.ae_restrict_iff'
Filter.EventuallyLE
measurableSet_uIoc
```

Checked project lemmas:

```lean
GX_nonneg_of_nonneg_window
GX_le_I_of_nonneg_window
GX_antitoneOn_Ici
f_mul_GX_intervalIntegrable
f_mul_floor_GX_intervalIntegrable
f_mul_fract_GX_intervalIntegrable
```

For the algebraic continuous floor contribution, local interval-integral APIs used were:

```lean
intervalIntegral.integral_sub
intervalIntegral.integral_congr
```

These prove:

```lean
JB_sub_Efloor_sub_half_I_sq_eq_floor_integral
JB_sub_Efloor_sub_half_I_sq_eq_floor_integral_of_nonneg
```

For the M5 weighted finite-chain comparison, local APIs used were:

```lean
intervalIntegral.integral_const_mul
intervalIntegral.integral_mono_on
intervalIntegral.integral_mono_interval
IntervalIntegrable.mul_const
Finset.induction_on_max
Finset.min'_insert
Finset.max'_insert
Finset.min'_le_max'
```

These prove:

```lean
floor_GX_le_floor_integral_on_gap
finite_chain_floor_sum_le_endpoint_add_integral_min_to_max
largeFloorSum_le_I_add_floor_integral
large_floor_sum_error_bound
```

Local source search in `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean` confirmed a likely shortcut
for `integral_fract_div_sq`:

```lean
namespace ZetaAsymptotics

noncomputable def term (n : ℕ) (s : ℝ) : ℝ :=
  ∫ x : ℝ in n..(n + 1), (x - n) / x ^ (s + 1)

noncomputable def term_sum (s : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, term (n + 1) s

noncomputable def term_tsum (s : ℝ) : ℝ :=
  ∑' n, term (n + 1) s

lemma term_one {n : ℕ} (hn : 0 < n) :
  term n 1 = (log (n + 1) - log n) - 1 / (n + 1)

lemma term_sum_one (N : ℕ) :
  term_sum 1 N = log (N + 1) - harmonic (N + 1) + 1

lemma term_tsum_one :
  HasSum (fun n ↦ term (n + 1) 1) (1 - Real.eulerMascheroniConstant)
```

The remaining M10 work is to bridge the project's `fract q / q ^ 2` on unit intervals to
`ZetaAsymptotics.term (n + 1) 1`, then connect the unit-interval `HasSum` to the `Set.Ioi`
integral.

### 2026-04-28 top-counting threshold and arithmetic APIs

For `eventually_top_le_Phi`, the proof uses the same threshold extraction pattern as `spacing`:

```lean
Filter.eventually_atTop
eventually_denom_pos
PhiFormula_nat_eq_lowerBoundRHS
PhiPsiData.Phi_mono_tail
PhiPsiData.Phi_tendsto_atTop
Filter.Tendsto.eventually_ge_atTop
tendsto_natCast_atTop_atTop
Finset.mem_image
Finset.le_max'
Nat.cast_le
```

For bottom-window arithmetic, these declarations were verified:

```lean
Nat.sub_le_iff_le_add
Nat.sub_pos_of_lt
Nat.lt_of_sub_pos
Nat.eq_add_of_sub_eq
```

### 2026-04-28 large-top floor APIs

For the pointwise large-top floor bound, the useful finite-chain route was max induction rather
than a sorted-list telescope.

Useful declarations:

```lean
Finset.induction_on_max
Finset.min'_insert
Finset.min'_mem
Finset.card_insert_of_notMem
Finset.not_nonempty_iff_eq_empty

intervalIntegral.integral_add_adjacent_intervals
intervalIntegral.integral_nonneg

Nat.lt_sub_iff_add_lt
Nat.cast_sub
Nat.cast_le
Nat.cast_nonneg
```

The integer floor bridge is exactly:

```lean
Int.le_floor :
  z ≤ ⌊a⌋ ↔ (z : ℝ) ≤ a
```

This local shape compiled:

```lean
example {B : ℝ} (A : Set ℕ) (D : PhiPsiData B) (X t : ℕ)
    (hGX : ((bottomWindow A X t).card : ℝ) ≤ GX D (X : ℝ) (t : ℝ)) :
    ((bottomWindow A X t).card : ℤ) ≤ ⌊GX D (X : ℝ) (t : ℝ)⌋ := by
  exact Int.le_floor.mpr hGX
```

For summing the pointwise floor bound, the checked APIs are:

```lean
Finset.sum_le_sum
Finset.mem_filter
exact_mod_cast
```

### 2026-04-28 three-part finite-sum split APIs

For splitting the top-counting sum into `t ≤ X`, `X < t ≤ X + Z0`, and `X + Z0 < t`,
the core filter identity is:

```lean
Finset.sum_filter_add_sum_filter_not :
  ∑ x ∈ s with p x, f x + ∑ x ∈ s with ¬p x, f x = ∑ x ∈ s, f x
```

To compare the small filtered sum against the full `natCut A X` sum, use:

```lean
Finset.sum_le_sum_of_subset_of_nonneg :
  s ⊆ t →
  (∀ i ∈ t, i ∉ s → 0 ≤ f i) →
  ∑ i ∈ s, f i ≤ ∑ i ∈ t, f i
```

Other declarations used:

```lean
Finset.mem_filter
Nat.lt_of_not_ge
Nat.not_le_of_gt
Nat.le_add_right
lt_of_le_of_lt
not_le
Nat.cast_add
```

### 2026-04-28 final contradiction APIs

For combining the final little-o remainders, these methods and declarations were used:

```lean
Asymptotics.IsLittleO.sub
Asymptotics.IsLittleO.add
Asymptotics.IsLittleO.def
Filter.eventually_atTop
```

For positivity of the natural scale:

```lean
tendsto_natCast_atTop_atTop
Real.tendsto_log_atTop
Filter.Tendsto.eventually_gt_atTop
div_pos
```

For unpacking the non-eventual upper-bound negation in the main theorem:

```lean
push Not
Filter.eventually_atTop
```

### 2026-04-28 small/short asymptotic bridge APIs

For `small_short_error_bound`, the natural-scale bridge uses these locally verified APIs:

```lean
Real.isLittleO_log_id_atTop
Asymptotics.IsLittleO.tendsto_div_nhds_zero
tendsto_inf
tendsto_principal
Filter.Tendsto.inv_tendsto_nhdsGT_zero
tendsto_natCast_atTop_atTop
tendsto_norm_atTop_atTop
Asymptotics.isLittleO_const_left
Asymptotics.IsLittleO.const_mul_left
Asymptotics.IsLittleO.const_smul_left
Asymptotics.IsLittleO.add
Asymptotics.IsLittleO.comp_tendsto
Asymptotics.IsLittleO.trans_isBigO
Asymptotics.IsEquivalent.comp_tendsto
Asymptotics.IsEquivalent.trans_isLittleO
Real.tendsto_sqrt_atTop
Real.sqrt_ne_zero'
Real.sq_sqrt
Real.sqrt_mul
Filter.tendsto_add_atTop_nat
Asymptotics.IsBigO.of_bound
Real.log_le_log
div_le_div_of_nonneg_right
div_le_div_of_nonneg_left
```

For the pointwise small/short inequality, useful arithmetic APIs were:

```lean
sq_le_sq₀
mul_le_mul_of_nonneg_left
Nat.cast_nonneg
```

### 2026-04-28 M7 tail positivity APIs

The first `PhiPsiConstruction` tail lemmas reuse the same asymptotic comparison as
`eventually_denom_pos`, but over real `w` instead of natural indices:

```lean
Real.isLittleO_log_id_atTop : Real.log =o[Filter.atTop] id
Real.tendsto_log_atTop : Tendsto Real.log Filter.atTop Filter.atTop
Filter.Tendsto.eventually
eventually_ge_atTop
eventually_gt_atTop
```

Useful proof pattern:

```lean
have hsmall : Real.log =o[Filter.atTop] (fun w : ℝ => w) :=
  Real.isLittleO_log_id_atTop
filter_upwards [hsmall.def (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (0 : ℝ),
    eventually_gt_atTop (-2 * B)] with w hsmallw hw_nonneg hw_gt
```

Composition through `x ↦ log x` works directly with:

```lean
Real.tendsto_log_atTop.eventually (eventually_H_pos_atTop B)
```

The positivity proof for `PhiFormula` used local positivity automation after unfolding `lam` and
`PhiFormula`; no theorem was moved out of `MainSkeleton`.

For the derivative and strict-monotonicity slice, the locally checked declarations were:

```lean
Real.hasDerivAt_log
HasDerivAt.comp
HasDerivAt.sub
HasDerivAt.const_add
HasDerivAt.div
HasDerivAt.deriv
HasDerivAt.continuousAt
ContinuousAt.continuousWithinAt
Filter.eventually_atTop
strictMonoOn_of_deriv_pos
convex_Ici
interior_Ici
```

The closed-tail strict-monotonicity proof extracts real thresholds from eventual facts with
`Filter.eventually_atTop.mp`, proves continuity on `Set.Ici T` from the explicit derivative
formula, and applies `strictMonoOn_of_deriv_pos` on `convex_Ici T`.

### 2026-04-28 M7 divergence and natural-tail APIs

For `PhiFormula_tendsto_atTop`, the useful comparison declarations were:

```lean
tendsto_atTop_mono'
Tendsto.const_mul_atTop
tendsto_id
Filter.Tendsto.eventually_ge_atTop
```

The proof uses the coarse eventual bounds

```lean
H B (Real.log x) ≤ x
lam * x ≤ PhiFormula B x
```

rather than a full asymptotic expansion of `H`.

For choosing the natural threshold in `exists_nat_PhiFormula_tail`, the locally checked APIs were:

```lean
exists_nat_ge
StrictMonoOn.monotoneOn
Nat.cast_le
exact_mod_cast
```

The chosen `N0` is above the real strict-monotonicity tail, the positivity tail for
`PhiFormula`, and `3`.

### 2026-04-28 M7 inverse-branch APIs

For the endpoint-ray surjectivity of `PhiFormula`, the useful local APIs were:

```lean
ContinuousOn.surjOn_Icc
Set.Icc_subset_Ici_self
Set.left_mem_Icc
Set.right_mem_Icc
Filter.Tendsto.eventually_ge_atTop
Filter.Eventually.and
Filter.Eventually.exists
```

The inverse branch uses mathlib's set-restricted inverse:

```lean
Function.invFunOn
SurjOn.rightInvOn_invFunOn
SurjOn.mapsTo_invFunOn
```

Uniqueness and order transport were proved directly from `StrictMonoOn`; no order-isomorphism
helper was needed.

### 2026-04-28 M7 `fBranch` construction APIs

The constant/tail extension uses elementary reciprocal order:

```lean
one_div_pos.mpr
one_div_le_one_div_of_le
Antitone.antitoneOn
```

After proving global antitonicity of `fBranch`, the useful measure/integrability APIs were:

```lean
Antitone.measurable
Antitone.intervalIntegrable
```

These avoided proving explicit continuity of `psiBranch` for the M7 data package.

### 2026-04-28 M8 tail-consequence APIs

Useful atTop and convergence declarations:

```lean
tendsto_atTop_atTop
eventually_ge_atTop
tendsto_inv_atTop_zero
Filter.Tendsto.congr'
```

For eventual equalities, state reusable facts with `=ᶠ[Filter.atTop]` rather than
`∀ᶠ ...`; this makes `.symm` and `Tendsto.congr'` work directly.

### 2026-04-28 M8 asymptotic algebra APIs

For the `FAsymptotics` inverse-branch setup, the locally checked asymptotic declarations were:

```lean
Real.isLittleO_log_id_atTop
isLittleO_const_id_atTop
Asymptotics.IsEquivalent
IsLittleO.add
IsLittleO.sub
IsLittleO.neg_left
IsLittleO.const_mul_right
IsLittleO.trans_isEquivalent
IsLittleO.congr'
IsEquivalent.comp_tendsto
IsEquivalent.tendsto_atTop
Asymptotics.IsEquivalent.rpow
IsEquivalent.congr_left
IsEquivalent.congr_right
IsEquivalent.trans
isLittleO_const_left
tendsto_norm_atTop_atTop
EventuallyEq.of_eq
```

The useful real-log simplification declarations were:

```lean
Real.log_div
Real.log_mul
Real.log_pow
```

`IsEquivalent.tendsto_atTop` transports in the direction of the right-hand function, so the
proof of `H_log_psi_tendsto_atTop` uses
`D.H_log_psi_isEquivalent_log_psi.symm.tendsto_atTop D.log_psi_tendsto_atTop`.

For the `f_asymptotic` square-root transfer, `Asymptotics.IsEquivalent.rpow` requires a
pointwise nonnegative right-hand model. The proof handles this by replacing
`2 * lam / (t * Real.log t)` with the eventually equal clipped model
`max (2 * lam / (t * Real.log t)) 0`, using:

```lean
Real.sqrt_eq_rpow
Real.sqrt_sq
Real.log_pos
le_max_right
max_eq_left
```

### 2026-04-28 M8 model-primitive calculus APIs

For the primitive model

```lean
IModel X = 2 * Real.sqrt (2 * lam * X / Real.log X)
```

the local proof used direct `HasDerivAt` calculus rather than a named derivative theorem:

```lean
hasDerivAt_id
HasDerivAt.const_mul
Real.hasDerivAt_log
HasDerivAt.div
HasDerivAt.sqrt
Real.sqrt_mul
Real.sqrt_sq
Real.sq_sqrt
isEquivalent_const_iff_tendsto
tendsto_const_nhds
tendsto_inv_atTop_zero
```

`HasDerivAt.sqrt` requires the inner argument to be nonzero at the point; the proof supplies
strict positivity of `2 * lam * X / log X` on the tail `X > 1`. The final derivative simplification
is field algebra plus the square identity
`fModel X ^ 2 * X * Real.log X = 2 * lam`.

For nat-indexed analytic wrappers, the real-to-nat transfer is:

```lean
Asymptotics.IsLittleO.comp_tendsto
tendsto_natCast_atTop_atTop
```

followed by `simpa [scaleReal, scaleNat]`.

### 2026-04-28 M8 integral squeeze APIs

The proof of `integral_f_asymptotic` uses a derivative model

```lean
IModelDeriv X = fModel X * (1 - 1 / Real.log X)
```

and avoids a nonexistent one-line “integral preserves asymptotic equivalence” theorem. The local
route is an explicit squeeze.

Useful APIs:

```lean
ContinuousOn.intervalIntegrable_of_Icc
Real.continuousOn_log
ContinuousOn.div
ContinuousOn.sqrt
ContinuousOn.mul
ContinuousOn.sub
HasDerivAt.continuousOn
intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
IntervalIntegrable.const_mul
intervalIntegral.integral_const_mul
intervalIntegral.integral_mono_on
intervalIntegral.integral_add_adjacent_intervals
Filter.eventually_atTop
Filter.Tendsto.eventually_ge_atTop
Asymptotics.isLittleO_iff
Asymptotics.IsLittleO.def
abs_le
abs_add_le
```

The proof structure is:

```text
D.f ~ IModelDeriv
  -> eventual pointwise `(1-ε) IModelDeriv ≤ D.f ≤ (1+ε) IModelDeriv`
  -> integrate over `[a,X]` for fixed large `a`
  -> use `∫_a^X IModelDeriv = IModel X - IModel a`
  -> split `I D X = I D a + ∫_a^X D.f`
  -> absorb the fixed constant by `const_isLittleO_IModel`
```

### 2026-04-28 M8 explicit upper-bound APIs

The explicit TeX (6) upper bound is obtained from the already proved asymptotic equivalence and
Big-O corollary. Useful declarations:

```lean
Asymptotics.IsBigO.exists_pos
Asymptotics.IsBigOWith.bound
Real.sqrt_div
Real.sq_sqrt
sq_le_sq₀
```

The proof route is:

```text
D.f =O fModel
  -> extract `C > 0` and an eventual norm bound
  -> use positivity of `D.f` and `fModel` on the tail
  -> rewrite `fModel t = sqrt(2λ) / sqrt(t log t)`
  -> square the explicit bound on a stricter positive-log tail
```

Checked theorem names now in `FloorSaving/FAsymptotics.lean`:

```lean
fModel_pos_of_one_lt
fModel_sq_of_one_lt
PhiPsiData.eventually_abs_f_sub_fModel_le
PhiPsiData.eventually_one_sub_mul_fModel_le_f
PhiPsiData.eventually_f_le_one_add_mul_fModel
PhiPsiData.f_le_const_mul_fModel
PhiPsiData.f_upper_bound
PhiPsiData.f_sq_upper_bound
```

### 2026-04-28 M8 elementary integral-bound APIs

The TeX (8) elementary integral bound is proved by the primitive
`sqrtLogPrimitive V = sqrt (V / log V)`. Useful declarations:

```lean
Real.hasDerivAt_log
HasDerivAt.div
HasDerivAt.sqrt
Real.sqrt_mul
Real.sqrt_sq
Real.le_log_iff_exp_le
Real.log_pos_iff
ContinuousOn.intervalIntegrable_of_Icc
intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
intervalIntegral.integral_mono_on
intervalIntegral.integral_const_mul
IntervalIntegrable.const_mul
```

Checked theorem names now in `FloorSaving/FAsymptotics.lean`:

```lean
invSqrtLogModel
sqrtLogPrimitive
sqrtLogPrimitiveDeriv
invSqrtLogModel_continuousOn_Icc_of_exp_two_le
sqrtLogPrimitive_continuousOn_Icc_of_exp_two_le
sqrtLogPrimitiveDeriv_continuousOn_Icc_of_exp_two_le
sqrtLogPrimitive_hasDerivAt_of_one_lt
invSqrtLogModel_le_four_mul_deriv
elementary_integral_bound
```

The pointwise comparison uses

```text
1/sqrt(V log V) ≤ 4 * d/dV sqrt(V/log V)
```

on `V ≥ exp 2`; the final theorem is

```lean
theorem elementary_integral_bound {T V : ℝ}
    (hT : Real.exp 2 ≤ T) (hTV : T ≤ V) :
    ∫ t in T..V, invSqrtLogModel t ≤ 4 * sqrtLogPrimitive V
```

### 2026-04-28 M8 local-comparability APIs

The local-comparability estimate is proved by first comparing the explicit model on
`c * t ≤ s ≤ t`, then applying the existing eventual two-sided squeeze between `D.f` and
`fModel`.

Useful local APIs:

```lean
Real.log_le_log
Real.log_mul
Real.le_log_iff_exp_le
div_le_div_of_nonneg_left
le_div_iff₀
div_le_iff₀
mul_le_mul
mul_le_mul_of_nonneg_left
mul_le_mul_of_nonneg_right
sq_le_sq₀
```

Checked theorem names now in `FloorSaving/FAsymptotics.lean`:

```lean
fModel_local_comparability
PhiPsiData.f_local_comparability
```

### 2026-04-28 M8 derivative-bound algebra APIs

The algebraic core of TeX (10) is now separated from the still-open inverse-branch
differentiability proof. The key observation is that `H ≤ 2H - H'` eventually, so the exact
inverse derivative model is bounded by the branch scale `(1 / r) / PhiFormula B r`.

Useful local APIs:

```lean
Real.isLittleO_log_id_atTop
Real.tendsto_log_atTop.eventually
div_le_div_of_nonneg_left
mul_le_mul_of_nonneg_left
field_simp
```

Checked theorem names now in `FloorSaving/PhiPsiConstruction.lean`:

```lean
eventually_H_le_two_mul_H_sub_Hderiv_atTop
eventually_H_log_le_two_mul_H_log_sub_Hderiv_log_atTop
eventually_inverse_derivative_model_le_f_over_Phi
```

### 2026-04-28 M8 inverse-branch differentiability APIs

The constructed inverse branch is handled as a monotone function on the target tail. Local
continuity is obtained from monotonicity plus a neighborhood image condition, avoiding an
unavailable `OrderTopology` route through interval subtypes. The derivative then uses the local
left-inverse theorem with `PhiFormula_psiBranch_eq`.

Useful local APIs:

```lean
Ici_mem_nhds
mem_of_superset
continuousAt_of_monotoneOn_of_image_mem_nhds
HasDerivAt.of_local_left_inverse
HasDerivAt.inv
HasDerivAt.congr_of_eventuallyEq
```

Checked theorem names now in `FloorSaving/PhiPsiConstruction.lean`:

```lean
psiBranch_gt_tail_endpoint
psiBranch_tail_image_mem_nhds
psiBranch_continuousAt_tail_interior
eventually_psiBranch_continuousAt_tail
psiBranch_hasDerivAt_tail_interior
fBranch_hasDerivAt_tail_interior
```

### 2026-04-28 M8 generic derivative and local-Lipschitz APIs

The derivative support is now repackaged for arbitrary `D : PhiPsiData B`, using only the
interface inverse fields and `D.Phi_eq`. The eventual derivative bound composes tail facts along
`D.psi_tendsto_atTop`; local Lipschitz then follows from the derivative bound, local
comparability, and the one-dimensional mean value inequality on `Set.Icc s t`.

Useful local APIs:

```lean
Filter.Tendsto.eventually
Filter.eventually_atTop.mp
HasDerivAt.hasDerivWithinAt
Classical.choose
Classical.choose_spec
Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
Set.left_mem_Icc
Set.right_mem_Icc
div_le_div_of_nonneg_left
div_le_div_of_nonneg_right
one_div_le_one_div_of_le
```

Checked theorem names now in `FloorSaving/FAsymptotics.lean`:

```lean
PhiPsiData.psi_gt_tail_endpoint
PhiPsiData.psi_tail_image_mem_nhds
PhiPsiData.psi_continuousAt_tail_interior
PhiPsiData.eventually_psi_continuousAt_tail
PhiPsiData.psi_hasDerivAt_tail_interior
PhiPsiData.f_hasDerivAt_tail_interior
PhiPsiData.eventually_f_hasDerivAt_bound
PhiPsiData.f_derivative_bound
PhiPsiData.f_local_lipschitz
```

### 2026-04-28 M9 half-square asymptotic APIs

The half-square contribution is proved by squaring the first-order primitive equivalence, replacing
`(1 / 2) * IModel X ^ 2` with `4 * lam * scaleReal X` on the tail, then removing the nonzero
constant on the right-hand little-o scale.

Useful local APIs:

```lean
Asymptotics.IsEquivalent.mul
Asymptotics.IsEquivalent.congr_right
Asymptotics.IsEquivalent.isLittleO
Asymptotics.IsLittleO.of_const_mul_right
Asymptotics.IsLittleO.congr'
EventuallyEq.rfl
Real.sq_sqrt
field_simp
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
half_square_asymptotic
```

### 2026-04-28 M9 `GX` split APIs

The exact `GX` algebra and the tail-conditioned continuous-integral split use only interval
integral algebra and monotone integrability. A parser issue was found locally: write
`X * (∫ t in X..D.Phi X, (D.f t)^2) + Rcorr D X` with parentheses; otherwise the integral
notation can absorb the trailing `+ Rcorr D X`.

Useful local APIs:

```lean
intervalIntegral.integral_sub
intervalIntegral.integral_const
intervalIntegral.integral_congr
intervalIntegral.integral_add
intervalIntegral.integral_const_mul
intervalIntegral.intervalIntegrable_const
IntervalIntegrable.const_mul
IntervalIntegrable.sub
IntervalIntegrable.congr
AntitoneOn.intervalIntegrable
Set.uIcc_of_le
sq_le_sq₀
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
GX_eq_X_mul_f_add_correction
f_sq_intervalIntegrable_of_nonneg
Rcorr_integrand_intervalIntegrable_of_nonneg
continuous_integral_square_correction_split_of_nonneg
```

### 2026-04-28 M9 `Phi` growth APIs

`Phi_dominates_fixed_multiple` is proved from the formula by showing
`H B (log X) = o(X)`, then using denominator positivity to compare
`U * X` with `lam * X^2 / H B (log X)`. The proof splits on `0 < U`; the nonpositive case uses
eventual positivity of `PhiFormula`.

Useful local APIs:

```lean
Real.isLittleO_log_id_atTop
Real.tendsto_log_atTop
IsLittleO.comp_tendsto
IsLittleO.trans
IsLittleO.sub
IsLittleO.add
IsLittleO.def
eventually_H_log_pos_atTop
eventually_PhiFormula_pos_atTop
field_simp
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
H_log_isLittleO_self
PhiFormula_dominates_fixed_multiple
Phi_dominates_fixed_multiple
continuous_integral_square_correction_split
```

### 2026-04-28 M9 branch endpoint APIs

The square-change endpoint facts reuse the inverse-branch package already proved in
`PhiPsiData`/`FAsymptotics`; no new structure fields were needed.

Useful local APIs:

```lean
PhiPsiData.log_psi_tendsto_atTop
PhiPsiData.psi_pos_eventually
PhiPsiData.Phi_psi_eq_eventually
PhiPsiData.Phi_maps_tail
PhiPsiData.psi_right_inv
Real.tendsto_exp_atTop.eventually_ge_atTop
Real.exp_log
Real.exp_neg
EventuallyEq
filter_upwards
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
w0_tendsto_atTop
exp_w0_eq_psi_eventually
Phi_exp_w0_eq_self_eventually
Phi_exp_log_eq_Phi_eventually
f_Phi_exp_eq
```

### 2026-04-28 M9 `PhiLog` derivative APIs

The logarithmic parametrization derivative is a direct composition of the existing
`PhiFormula_hasDerivAt` theorem with the real exponential derivative. The final derivative is
normalized by rewriting `exp w * exp w` as `exp (2*w)` and using `field_simp` with the eventual
nonzero `H B w`.

Useful local APIs:

```lean
PhiFormula_hasDerivAt
Real.hasDerivAt_exp
HasDerivAt.comp
Real.log_exp
Real.exp_ne_zero
Real.exp_add
eventually_H_pos_atTop
field_simp
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
PhiLog
PhiLog_hasDerivAt_eventually
```

The derivative nonnegativity card reuses the positivity tails for `H` and `2H-H'`, plus
field-normalization of the bracket:

```lean
2 / H B w - Hderiv w / (H B w)^2 =
  (2 * H B w - Hderiv w) / (H B w)^2
```

Checked theorem name now in `FloorSaving/ContinuousMajorant.lean`:

```lean
PhiLog_deriv_nonneg_eventually
```

### 2026-04-28 M9 lower-endpoint exact identities

The lower endpoint now has exact identities and first-order equivalences before the
cancellation-sensitive constant expansion.

Useful local APIs:

```lean
PhiPsiData.log_eq_log_lam_add_two_log_psi_sub_log_H_eventually
PhiPsiData.log_isEquivalent_two_log_psi
H_isEquivalent_atTop
IsEquivalent.mul
IsEquivalent.comp_tendsto
IsEquivalent.trans
IsEquivalent.congr_right
EventuallyEq
filter_upwards
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
w0_isEquivalent_half_log
H_w0_isEquivalent_half_log
log_eq_log_lam_add_two_w0_sub_log_H_w0_eventually
rX_eq_half_log_H_w0_sub_log_lam_eventually
```

### 2026-04-28 M9 continuous coefficient APIs

The pure constant assembly uses `lam = 1 / (2 * log 2)` to rewrite
`log (lam / 2)` as `-log 4 - log (log 2)`, then `log 4 = 2 * log 2`.

Useful local APIs:

```lean
Real.log_pos
Real.log_inv
Real.log_mul
Real.log_pow
field_simp
ring
norm_num
```

Checked theorem name now in `FloorSaving/ContinuousMajorant.lean`:

```lean
continuous_coefficient_identity
```

### 2026-04-28 M9 correction-kernel elementary APIs

`FloorSaving/KernelIntegral.lean` proves standalone support for the future
`corrKernel_integral_tendsto` argument. The finite transformed-kernel identity uses the FTC for

```lean
fun x : ℝ => 2 * Real.log (1 + x) + 2 / (1 + x)
```

whose derivative is `2 * x / (1 + x)^2` away from `x = -1`.

Useful local APIs:

```lean
ContinuousOn.aemeasurable
ContinuousOn.intervalIntegrable
ContinuousOn.log
ContinuousOn.div
ContinuousOn.sqrt
intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
Real.hasDerivAt_log
HasDerivAt.comp
HasDerivAt.inv
HasDerivAt.const_mul
HasDerivAt.add
Set.uIcc_of_le
```

Checked theorem names now in `FloorSaving/KernelIntegral.lean`:

```lean
corrKernel_continuousOn_Ici_one
corrKernel_continuousOn_Icc
corrKernel_aemeasurable_Icc
corrKernel_intervalIntegrable
corrKernel_one_add_eq
transformedKernel_antideriv_hasDerivAt
transformedKernel_integral_eq
transformedKernel_integral_eq_two_mul
```

### 2026-04-28 M9 square-change substitution API

The exact square-integral substitution uses the monotone interval-integral change-of-variables
theorem rather than the stronger smooth-continuous-integrand variants. This avoids a separate
continuity proof for `fun t => D.f t ^ 2`.

Useful local APIs:

```lean
intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
intervalIntegral.integral_congr
intervalIntegral.integral_const_mul
Set.uIcc
Set.mem_uIcc
```

Small local interval helpers added in `FloorSaving/ContinuousMajorant.lean`:

```lean
le_of_endpoints_le_of_mem_uIcc
mem_uIcc_of_mem_Ioo_min_max
```

Checked theorem name now in `FloorSaving/ContinuousMajorant.lean`:

```lean
f_sq_integral_square_change_exact
```

### 2026-04-28 M9 lower-endpoint constant expansion APIs

The lower endpoint is easiest to normalize through the ratio
`H B (w0 D X) / Real.log X`, then take logs. The exact `rX` formula supplies the final
rewriting step.

Useful local APIs:

```lean
isEquivalent_iff_tendsto_one
Filter.Tendsto.log
Asymptotics.isLittleO_one_iff
Real.log_div
Real.log_mul
Tendsto.congr'
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
H_w0_div_log_tendsto_half
log_H_w0_sub_loglog_tendsto_neg_log_two
rX_tendsto_sub_model
rX_asymptotic
lower_endpoint_asymptotic
```

### 2026-04-28 M9 reciprocal-H derivative APIs

The exact transformed-square split needs the derivative of `(H B w)⁻¹`, where
`Hderiv w = 1 - 1 / w`.

Useful local APIs:

```lean
Real.hasDerivAt_log
HasDerivAt.sub
HasDerivAt.const_add
HasDerivAt.inv
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
H_hasDerivAt
H_inv_hasDerivAt
H_inv_hasDerivAt_eventually
```

### 2026-04-28 M9 reciprocal-H split APIs

The exact split of

```lean
∫ w in a..b, (2 / H B w - Hderiv w / (H B w)^2)
```

uses the unordered FTC theorem, so the proof does not need a separate comparison between the two
endpoints.

Useful local APIs:

```lean
intervalIntegral.integral_eq_sub_of_hasDerivAt
intervalIntegral.integral_add
intervalIntegral.integral_const_mul
intervalIntegral.integral_congr
ContinuousOn.intervalIntegrable
ContinuousAt.inv₀
ContinuousAt.div
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
H_inverse_integral_split_of_tail
transformed_square_integral_split_exact
```

### 2026-04-28 M9 primitive square-bracket integral APIs

The elementary primitives in the transformed square bracket are now proved by the unordered FTC
on positive `Set.uIcc` windows. Local discovery also confirmed that mathlib has shorter
`integral_inv`/`integral_inv_of_pos` routes, but the FTC route matches the neighboring
`H`-reciprocal split proof.

Useful local APIs:

```lean
intervalIntegral.integral_eq_sub_of_hasDerivAt
Real.hasDerivAt_log
HasDerivAt.mul
HasDerivAt.neg
HasDerivAt.add_const
HasDerivAt.inv
ContinuousOn.intervalIntegrable
ContinuousAt.div
ContinuousAt.inv₀
pow_ne_zero
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
inv_integral_eq_log_sub_of_pos
inv_integral_w0_log_eq_eventually
two_inv_integral_w0_log_eq_eventually
log_sub_const_div_sq_hasDerivAt
log_sub_const_div_sq_integral_eq_of_pos
log_sub_const_div_sq_integral_w0_log_eq_eventually
```

### 2026-04-28 M9 endpoint reciprocal asymptotic APIs

The endpoint contribution is easiest after normalizing both reciprocals by `Real.log X`.
The upper endpoint uses `H_isEquivalent_atTop` composed with `Real.tendsto_log_atTop`; the
lower endpoint reuses `H_w0_div_log_tendsto_half`.

Useful local APIs:

```lean
isEquivalent_iff_tendsto_one
Filter.Tendsto.inv₀
Filter.Tendsto.congr'
Filter.Tendsto.sub
Filter.Tendsto.add
Asymptotics.isLittleO_one_iff
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
H_log_div_log_tendsto_one
log_mul_H_log_inv_tendsto_one
log_mul_H_w0_inv_tendsto_two
H_inv_endpoint_diff_asymptotic
```

### 2026-04-28 M9 `2∫dw/w` asymptotic APIs

The cancellation-sensitive reciprocal integral is reduced exactly to a `log(1+u)` remainder with
`u = 2*rX/log X`. The remainder estimate is proved from elementary real-log inequalities, not a
Taylor-series API.

Useful local APIs:

```lean
Real.log_le_sub_one_of_pos
Real.one_sub_inv_le_log_of_pos
Metric.tendsto_nhds
Real.dist_eq
IsBigO.of_bound
IsBigO.trans_isLittleO
isLittleO_log_rpow_atTop
isLittleO_const_left
IsLittleO.pow
IsLittleO.tendsto_div_nhds_zero
Real.tendsto_sqrt_atTop
Real.sqrt_eq_rpow
Real.sq_sqrt
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
w0_div_log_tendsto_half
two_rX_div_log_tendsto_zero
two_inv_integral_remainder_identity_eventually
loglog_isLittleO_sqrt_log
const_isLittleO_sqrt_log
sqrt_log_isLittleO_log
rX_isLittleO_sqrt_log
rX_sq_div_log_tendsto_zero
log_one_add_remainder_abs_le_two_sq
isLittleO_mul_log_one_add_remainder
two_inv_integral_log_remainder_isLittleO
two_inv_integral_asymptotic
```

### 2026-04-28 M9 `2∫(log w - B)/w²` and square-bracket assembly APIs

The second primitive contribution is easiest as a Tendsto calculation after the exact primitive
rewrite: take logs of `w0/log X → 1/2`, prove `log X / w0 → 2`, and factor the endpoint product as
`(rX/sqrt(log X)) * ((log w0 + 1 - B)/sqrt(log X)) * (log X / w0)`.

Useful local APIs:

```lean
Filter.Tendsto.log
Filter.Tendsto.inv₀
Filter.Tendsto.div_atTop
Filter.Tendsto.congr'
Asymptotics.isLittleO_one_iff
Asymptotics.IsLittleO.tendsto_div_nhds_zero
Real.log_div
Real.log_inv
Real.tendsto_sqrt_atTop
Real.sqrt_ne_zero'.mpr
Real.sq_sqrt
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
log_w0_sub_loglog_tendsto_neg_log_two
log_div_w0_tendsto_two
log_w0_add_const_div_sqrt_log_tendsto_zero
log_div_w0_sub_two_mul_log_w0_add_const_tendsto_zero
log_sub_const_div_sq_integral_algebra
log_sub_const_div_sq_integral_asymptotic
rX_square_bracket_coefficient_asymptotic
transformed_square_bracket_asymptotic_of_H_inv_remainder
```

### 2026-04-28 M9 geometric `1/H` remainder APIs

The integrated remainder is proved by a uniform bound on the moving interval
`[w0 D X, log X]`. The proof avoids a separate exact integral of `(log w)^2 / w^3`: for each
small constant `δ`, eventually `(log w - B)^2 ≤ δ*w` and `H B w ≥ w/2`; together with
`w0/log X → 1/2`, this bounds the remainder by `18*δ/(log X)^2` on the window.

Useful local/mathlib APIs:

```lean
Filter.Tendsto.eventually_const_le
Filter.Tendsto.eventually_lt_const
Set.uIoc_of_le
Set.uIoc_subset_uIcc
intervalIntegral.norm_integral_le_of_norm_le_const
div_le_div_of_nonneg_left
div_le_div_of_nonneg_right
mul_div_cancel_right₀
IsLittleO.of_bound
IsLittleO.def
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
const_isLittleO_sqrt_self
log_sub_const_sq_isLittleO_self
eventually_half_self_le_H
H_inv_remainder_eq
H_inv_remainder_abs_le
H_inv_remainder_integral_isLittleO
H_inv_remainder_linear_combination_isLittleO
transformed_square_bracket_asymptotic
```

### 2026-04-29 M9 square-integral asymptotic transport APIs

The square-integral asymptotic is proved directly from the exact square-change identity and
the transformed square-bracket estimate. Keeping the transformed integral as a local function
`A` avoids unfolding the interval integral during pure algebra.

Useful local/mathlib APIs:

```lean
IsLittleO.of_bound
IsLittleO.def
filter_upwards
eventually_gt_atTop
Real.log_pos
field_simp
nlinarith
congrArg
norm_mul
Real.norm_of_nonneg
gcongr
Real.norm_eq_abs
abs_of_pos
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
lam_mul_two_log_two
f_sq_integral_asymptotic
square_integral_term_asymptotic
```

### 2026-04-29 M9 `gNorm` pointwise and integrability APIs

The first correction-term support slice proves the limiting profile integrability, the exact
small singular integral, finite-interval integrability for `gNorm`, and fixed-`v` pointwise
normalization.

Useful local/mathlib APIs:

```lean
intervalIntegral.intervalIntegrable_rpow'
integral_rpow
intervalIntegral.integral_congr
IntervalIntegrable.comp_mul_left
IntervalIntegrable.const_mul
IntervalIntegrable.sub
IntervalIntegrable.abs
Filter.Tendsto.atTop_mul_const
Filter.Tendsto.div
Filter.Tendsto.sqrt
Asymptotics.IsEquivalent.comp_tendsto
Asymptotics.IsEquivalent.mul
Asymptotics.IsEquivalent.tendsto_nhds
Real.rpow_neg
Real.sqrt_eq_rpow
Real.sqrt_mul
Real.sqrt_div
Real.log_mul
tendsto_inv_atTop_zero
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
inv_sqrt_intervalIntegrable_zero
integral_inv_sqrt_zero_eq
gNorm_intervalIntegrable
gNorm_sub_inv_sqrt_abs_intervalIntegrable
log_mul_const_div_log_tendsto_one
log_div_log_mul_const_tendsto_one
gNorm_model_tendsto_inv_sqrt
gNorm_tendsto_inv_sqrt
```

### 2026-04-29 M9 `gNorm` epsilon-split support APIs

The second correction-term support slice added the uniform reciprocal-log estimate on compact
intervals away from zero, factored the exact model normalization algebra, and proved the exact
small-`v` change of variables.

Useful local/mathlib APIs:

```lean
intervalIntegral.integral_const_mul
intervalIntegral.integral_comp_mul_left
Real.tendsto_log_atTop.eventually_ge_atTop
eventually_gt_atTop
Real.log_mul
Real.log_le_log
abs_le
div_le_iff₀
Real.sqrt_mul
Real.sqrt_div
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
gNorm_integral_change_of_variables
log_div_log_mul_uniform_sub_one_le
gNorm_model_eq_inv_sqrt_mul_log_ratio
```

### 2026-04-29 M9 away-from-zero `gNorm` APIs

The away-from-zero part of the `gNorm` epsilon split is now proved as a uniform bound and as a
`TendstoUniformlyOn` wrapper on each compact interval `[ε,U]` with `0 < ε ≤ U`.

Useful local/mathlib APIs:

```lean
Metric.tendstoUniformlyOn_iff
Real.dist_eq
abs_add_le
abs_sub_comm
Real.sqrt_pos
Real.sqrt_le_sqrt
inv_le_inv₀
mul_le_mul
mul_le_mul_of_nonneg_left
eventually_ge_atTop
eventually_gt_atTop
Filter.eventually_atTop
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
abs_sqrt_sub_one_le_abs_sub_one
gNorm_model_uniform_away_bound
gNorm_sub_model_uniform_relative_bound
gNorm_model_uniform_cap
gNorm_sub_model_uniform_away_bound
gNorm_uniform_away_bound
gNorm_tendstoUniformlyOn_away
```

### 2026-04-29 M9 small-endpoint `gNorm` APIs

The small-endpoint half of the `gNorm` epsilon split is now proved as an integral bound and as
the corresponding L1 bound. The proof uses the existing elementary tail model for
`∫ dt / sqrt(t log t)`, a fixed compact-interval decay estimate, and square-root/log algebra
for `sqrtLogPrimitive (X*ε)`.

Useful local/mathlib APIs:

```lean
PhiPsiData.f_upper_bound
elementary_integral_bound
intervalIntegral.integral_add_adjacent_intervals
intervalIntegral.integral_mono_on
Filter.Tendsto.atTop_mul_const
Filter.Tendsto.eventually_le_const
Real.le_log_iff_exp_le
Real.sqrt_div
Real.sqrt_mul
Real.sqrt_ne_zero'.mpr
Asymptotics.IsLittleO.sqrt
Asymptotics.IsLittleO.tendsto_div_nhds_zero
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
gNorm_nonneg
abs_sub_le_add_of_nonneg
gNorm_small_v_L1_bound_of_integral_bound
gNorm_small_v_L1_eventual_bound_of_integral_eventual_bound
gNorm_small_v_L1_eventual_bound_of_integral_eventual_bound_exists
f_integral_tail_sqrtLogPrimitive_bound
gNorm_scale_sqrtLogPrimitive_eq
gNorm_scale_sqrtLogPrimitive_le
eventually_sqrt_log_ratio_mul_const_le_two
sqrt_log_isLittleO_sqrt_self
gNorm_compact_prefactor_tendsto_zero
gNorm_compact_prefactor_eventually_le_sqrt
gNorm_small_v_integral_eventual_bound
gNorm_small_v_L1_eventual_bound
```

### 2026-04-29 M9 `gNorm` L1 assembly APIs

The fixed-interval L1 convergence is now proved by choosing a small split point `δ`, using the
small-endpoint L1 bound on `(0,δ)`, using away-from-zero uniform convergence on `[δ,U]`, and
then recombining the interval integrals.

Useful local/mathlib APIs:

```lean
Metric.tendsto_atTop
Filter.eventually_atTop.mp
eventually_gt_atTop
intervalIntegral.integral_add_adjacent_intervals
intervalIntegral.integral_mono_on
intervalIntegral.integral_const
intervalIntegral.integral_nonneg
intervalIntegral.intervalIntegrable_const
IntervalIntegrable.mono_set
Set.uIcc_of_le
Real.sqrt_le_sqrt
Real.sqrt_sq
```

Checked theorem name now in `FloorSaving/ContinuousMajorant.lean`:

```lean
gNorm_L1_convergence
```

### 2026-04-29 M9 normalized correction substitution APIs

The fixed-`U` truncated correction is now rewritten exactly in normalized variables. The proof
uses an inner change of variables `s = X*v`, an outer change of variables `t = X*u`, and the
normalization algebra
`(2 * lam * X / log X) * (X⁻¹ * A * A) = X` with
`A = sqrt (X * log X / (2 * lam))`.

Useful local/mathlib APIs:

```lean
intervalIntegral.integral_comp_mul_left
intervalIntegral.smul_integral_comp_mul_left
intervalIntegral.integral_const_mul
intervalIntegral.integral_congr
eventually_gt_atTop
Real.log_pos
Real.sq_sqrt
field_simp
ring_nf
```

The pointwise limiting kernel identity was also moved upstream of `KernelIntegral` to avoid an
import cycle. It uses the general nonnegative interval integral of the singular limiting profile.

```lean
integral_rpow
intervalIntegral.integral_sub
intervalIntegral.integral_const
IntervalIntegrable.mono_set
Real.sqrt_eq_rpow
Real.rpow_neg
Real.sqrt_div
Real.sqrt_pos
Real.sq_sqrt
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
integral_inv_sqrt_eq_of_nonneg
corr_limit_integrand_eq_corrKernel
RcorrTrunc_inner_change
RcorrTrunc_outer_change
RcorrTrunc_normalized_change_of_gt_one
RcorrTrunc_normalized_change
```

Correction-tail support now implemented in `FloorSaving/ContinuousMajorant.lean`:

```lean
Rcorr_inner_nonneg_of_le
Rcorr_integrand_nonneg_of_le
Rcorr_tail_integrand_intervalIntegrable_of_order
Rcorr_sub_RcorrTrunc_eq_tail
Rcorr_tail_integral_nonneg_of_order
Rcorr_sub_RcorrTrunc_nonneg_of_order
one_div_sq_intervalIntegrable_of_pos
integral_one_div_sq_eq_inv_sub_inv
integral_one_div_sq_le_inv_left
```

The quantitative tail bound is now implemented in `FloorSaving/ContinuousMajorant.lean`:

```lean
Rcorr_inner_lipschitz_bound
Rcorr_tail_integrand_le_inv_sq
Rcorr_tail_integral_le_of_constants
Rcorr_tail_bound
```

The proof combines the local Lipschitz estimate on the window `[t/2,t]`, the square upper bound
for `f`, monotonicity of `Real.log`, `intervalIntegral.integral_mono_on`, and
`integral_one_div_sq_le_inv_left`.

APIs used:

```lean
Phi_dominates_fixed_multiple
PhiPsiData.f_local_lipschitz
PhiPsiData.f_sq_upper_bound
intervalIntegral.integral_add_adjacent_intervals
intervalIntegral.integral_mono_on
intervalIntegral.norm_integral_le_of_norm_le_const
intervalIntegral.intervalIntegrable_zpow
integral_zpow
Set.notMem_uIcc_of_lt
Real.log_le_log
Real.log_pos
one_div_le_one_div_of_le
```

The sidecar-checked route for `Rcorr_sub_RcorrTrunc_eq_tail` restricts integrability from
`X..D.Phi X` using `IntervalIntegrable.mono_set`; proving the integrability directly on
`U*X..D.Phi X` with `Rcorr_integrand_intervalIntegrable_of_nonneg` would incorrectly change the
inner window parameter. The intended `Rcorr_tail_bound` quantifier shape chooses the constant
before `∀ U`; the eventual `X` threshold may still depend on the fixed `U ≥ 2`.

### 2026-04-29 M9 fixed-U correction operator APIs

The normalized correction operator now has both an L1 convergence theorem and the un-absolute
fixed-`U` integral convergence needed for `RcorrTrunc_asymptotic`. The proof first bounds the
pointwise operator error by the away-from-zero uniform `gNorm` error plus the global
`gNorm_L1_convergence` error on `(0,U)`, then converts L1 convergence into convergence of the
signed interval integral.

Useful local/mathlib APIs:

```lean
intervalIntegral.integral_mono_interval
intervalIntegral.abs_integral_le_integral_abs
intervalIntegral.integral_sub
intervalIntegral.integral_const
intervalIntegral.integral_nonneg
intervalIntegral.norm_integral_le_of_norm_le_const
IntervalIntegrable.mono_set
IntervalIntegrable.comp_mul_left
Metric.tendsto_atTop
Set.uIoc_of_le
Set.uIcc_of_le
Real.sqrt_le_sqrt
Real.sqrt_pos
Real.norm_eq_abs
abs_add_le
abs_mul
isLittleO_one_iff
isBigO_refl
IsLittleO.mul_isBigO
IsLittleO.congr'
```

Checked theorem names now in `FloorSaving/ContinuousMajorant.lean`:

```lean
window_abs_integral_le_global_L1
abs_window_integral_le_global_L1
inv_sqrt_abs_integral_zero_eq
corrOperator_pointwise_error_bound
corrOperator_L1_convergence_fixed_U
corrKernel_intervalIntegrable_of_one_le
corrOperator_integrand_intervalIntegrable_of_gt_one
corrOperator_integral_tendsto_fixed_U
RcorrTrunc_asymptotic
```

The correction-kernel integral limit is now proved in `FloorSaving/KernelIntegral.lean`.

```lean
corrKernel_integral_tendsto
corrKernel_integral_eq_transformed
corrKernel_integral_eq_closed
intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
tendsto_inv_atTop_zero
Filter.Tendsto.sqrt
Filter.Tendsto.log
Filter.Tendsto.inv₀
```

The finite integral uses the monotone substitution `u = (1 - x^2)⁻¹` on
`x ∈ [0, sqrt (1 - 1/U)]`, then reuses `transformedKernel_integral_eq_two_mul`.

### 2026-04-29 M9 correction and continuous-majorant assembly

The correction asymptotic and continuous-majorant assembly are now implemented. `KernelIntegral`
is the assembly location for correction because it imports `ContinuousMajorant` and contains
`corrKernel_integral_tendsto`; importing it back into `ContinuousMajorant` would create a cycle.
`AnalyticInterfaces` imports `KernelIntegral` to discharge the public
`continuous_majorant_asymptotic` placeholder.

Useful local declarations:

```lean
Rcorr_tail_bound
RcorrTrunc_asymptotic
corrKernel_integral_tendsto
correction_asymptotic
large_continuous_integral_asymptotic
continuous_majorant_asymptotic
continuous_majorant_asymptotic_nat
```

Assembly APIs that compiled locally:

```lean
Metric.tendsto_atTop
IsLittleO.of_bound
Asymptotics.IsLittleO.add
Asymptotics.IsLittleO.congr'
continuous_integral_square_correction_split
continuous_coefficient_identity
```

### 2026-04-29 detailed M10 proof update

The refreshed TeX reference is useful for formalization because it replaces the vague
floor-saving plan with three bounded fixed-`Q` lemmas plus a final two-limit sandwich.

Concrete Lean discovery targets:

```lean
qOf_eq_X_mul_f_of_tail
qOf_Phi_X_div_q
Phi_X_div_Q_order_eventually
Phi_deriv_over_self_uniform_fixed_Q
q_change_uniform_fixed_Q
GX_Phi_X_div_q_uniform_fixed_Q
fract_lipschitz_on_same_unit_interval
fract_integral_convergence_fixed_Q
EfloorTail_bound_uniform_Q
floor_saving_normalized_limit
```

The q-change proof should avoid requiring continuity of the test function. Quantify over
bounded measurable `F : ℝ → ℝ` with `∀ q ∈ Set.Icc 1 Q, |F q| ≤ 1`, perform the monotone
substitution `t = D.Phi r` on the tail branch and then `q = X/r`, and bound the remaining error
by

```text
X * sup_{q ∈ [1,Q]} |D.PhiDeriv (X/q) / (X/q) - 2*lam / Real.log X|
  * ∫ q in 1..Q, 1/q^2.
```

The TeX tail proof suggests a separate reusable derivative bound:

```lean
eventually_Phi_deriv_over_self_le_const_div_log
```

with constant depending only on `B`; combine it with `D.psi X < X / Q` and
`Real.log (D.psi X) ≥ Real.log X / 3` eventually to get the Q-independent normalized
`EfloorTail` bound.

### 2026-04-29 first M10 Lean scaffold

The first fixed-`Q` decomposition slice is implemented in
`FloorSaving/FloorSavingIntegral.lean`.

Checked local declarations:

```lean
qOf
EfloorMain
EfloorTail
IfractQ
IfractInf
qOf_eq_X_mul_f_of_tail
qOf_Phi_X_div_q
eventually_X_div_Q_ge_N0
eventually_Tstar_le_Phi_X_div_Q
eventually_X_le_Phi_X_div_Q
eventually_Phi_X_div_Q_le_Phi_X
eventually_fixedQ_branch_order
qOf_mem_Icc_of_mem_main_interval
eventually_qOf_mem_Icc_on_main_interval
Efloor_eq_tail_add_main_of_order
eventually_Efloor_eq_tail_add_main_fixed_Q
eventually_EfloorTail_nonneg_fixed_Q
eventually_EfloorMain_nonneg_fixed_Q
IfractQ_nonneg
```

Substitution APIs confirmed by local source inspection:

```lean
intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
```

The first is suited to `t = D.Phi r`; the second is suited to the decreasing
change `r = X / q`. The q-change proof still needs a derivative formula package and uniform
error bound for `Phi'(X/q)/(X/q)`.

For the large-`q` tail, prefer the simpler route suggested by the M10 tail sidecar:
combine `EfloorTail_le_f_integral_of_order` with `PhiPsiData.f_upper_bound` and
`elementary_integral_bound`, rather than using the derivative substitution in the tail.

The Euler fractional-integral identity is proved in `FloorSaving/FractionalIntegral.lean`.
Useful declarations:

```lean
integrableOn_fract_div_sq_Ioi_one
iUnion_Ioc_nat_units_above_one
pairwise_disjoint_Ioc_nat_units_above_one
integral_fract_div_sq_Ioi
hasSum_integral_fract_div_sq_units
```

### 2026-04-29 M10 tail estimate

The normalized large-`q` tail estimate is implemented in
`FloorSaving/FloorSavingIntegral.lean`.

Checked declarations:

```lean
eventually_half_log_le_log_X_div_Q
Phi_X_div_Q_upper_uniform
sqrtLogPrimitive_Phi_X_div_Q_bound_uniform
integral_f_X_to_Phi_X_div_Q_bound_uniform
EfloorTail_bound_uniform_Q
```

The proof avoids a derivative substitution for the tail. It uses:

```lean
PhiPsiData.f_upper_bound
elementary_integral_bound
eventually_half_self_le_H
eventually_X_le_Phi_X_div_Q
EfloorTail_le_f_integral_of_order
EfloorTail_nonneg_of_order
```

For fixed `Q ≥ 2`, `log (X/Q) ≥ (1/2) log X` eventually, and
`H B (log (X/Q)) ≥ (1/4) log X` eventually. This gives a uniform
`D.Phi (X/Q) = O(X^2/(Q^2 log X))`, hence
`sqrtLogPrimitive (D.Phi (X/Q)) = O(X/(Q log X))`, and finally the normalized
`EfloorTail` bound.

Read-only sidecar discoveries queued for the main term:

```lean
PhiDerivFormula
PhiDerivOverR
D_Phi_hasDerivAt
f_Phi_eq_inv_of_tail
qOf_Phi_eq_div_of_tail
q_change_exact_fixed_Q
GX_Phi_X_div_q_uniform_fixed_Q
integerWindow
intBadSet
intGoodSet
PhiFormula_measurable
Phi_measurable
q_fract_GX_Phi_measurable
```

### 2026-04-29 M10 exact q-change

The exact fixed-`Q` q-change theorem is implemented in
`FloorSaving/FloorSavingIntegral.lean`. The substitution is decreasing with
`tau q = D.Phi (X/q)`, so the usable mathlib API is:

```lean
intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
intervalIntegral.integral_symm
intervalIntegral.integral_neg
intervalIntegral.integral_congr
hasDerivAt_inv
HasDerivAt.const_mul
HasDerivAt.comp
ContinuousOn.div
ContinuousOn.comp
```

Checked declarations added for the q-change slice:

```lean
PhiDerivFormula
PhiDerivOverR
H_measurable
PhiFormula_measurable
PhiPsiData.Phi_measurable
PhiDerivFormula_measurable
H_log_continuousOn
PhiFormula_continuousOn
PhiDerivFormula_hasDerivAt
PhiPsiData.Phi_hasDerivAt
PhiDerivOverR_eq
PhiDerivFormula_eq_mul_PhiDerivOverR
eventually_Phi_hasDerivAt
eventually_Phi_hasDerivAt_X_div_q_on_Icc
eventually_Phi_comp_X_div_continuousOn
eventually_PhiDerivFormula_nonneg_X_div_q_on_Icc
hasDerivAt_X_div
Phi_comp_X_div_hasDerivAt
eventually_X_div_q_ge_N0_on_Icc
eventually_Phi_X_div_q_between_on_Icc
f_Phi_eq_inv_of_tail
qOf_Phi_eq_div_of_tail
f_Phi_X_div_q_eq_q_div_X
X_mul_f_Phi_X_div_q_eq_q
GX_Phi_X_div_q_eq_q_add_correction
GX_Phi_X_div_q_sub_eq_correction
q_fract_GX_Phi_measurable
q_fract_GX_Phi_intervalIntegrable
q_change_exact_fixed_Q_of_deriv_nonpos
eventually_q_change_exact_fixed_Q
```

The exact Jacobian after reversing orientation is

```lean
X / q ^ 2 * PhiDerivOverR B (X / q)
```

not a constant. The next main-term step is a uniform fixed-`Q` estimate replacing this factor by
`(2 * lam * X / Real.log X) / q ^ 2`.

### 2026-04-29 M10 uniform Jacobian and integer windows

The uniform fixed-`Q` Jacobian estimate is implemented in
`FloorSaving/FloorSavingIntegral.lean`.

Checked declarations:

```lean
eventually_abs_H_sub_self_le_mul
log_div_log_X_div_q_uniform_sub_one_le
eventually_abs_H_log_X_div_q_sub_le_mul
eventually_jacobian_weight_uniform_fixed_Q
eventually_PhiDerivOverR_uniform_fixed_Q
eventually_two_mul_X_le_Phi_X_div_q_on_Icc
IfractQ_tendsto_IfractInf
IfractInf_eq_one_sub_euler
```

Useful local APIs for this slice:

```lean
Real.isLittleO_log_id_atTop
isLittleO_const_id_atTop
log_div_log_mul_uniform_sub_one_le
eventually_half_log_le_log_X_div_Q
eventually_abs_H_sub_self_le_mul
PhiDerivOverR_eq
one_div_le_one_div_of_le
inv_le_inv₀
Filter.Tendsto.atTop_div_const
Phi_dominates_fixed_multiple
intervalIntegral_tendsto_integral_Ioi
```

The finite integer-neighborhood infrastructure for fractional-part stability is also implemented.
The index set uses `⌈Q⌉`, not `⌊Q⌋`, because floor stability near the top endpoint needs the next
integer after `q`.

Checked declarations:

```lean
integerWindowIndex
integerWindow
integerWindowUnion
intBadSet
intGoodSet
mem_integerWindow
mem_integerWindowUnion
measurableSet_integerWindow
measurableSet_integerWindowUnion
measurableSet_intBadSet
measurableSet_intGoodSet
mem_intBadSet
mem_intGoodSet
floor_mem_integerWindowIndex_of_mem_intGoodSet
ceil_mem_integerWindowIndex_of_mem_intGoodSet
floor_eq_of_mem_intGoodSet_of_abs_sub_lt
fract_sub_fract_eq_of_mem_intGoodSet_of_abs_sub_lt
abs_fract_sub_fract_eq_of_mem_intGoodSet_of_abs_sub_lt
```

Useful local APIs:

```lean
Int.floor_eq_iff
Int.le_floor
Int.floor_le
Int.lt_floor_add_one
Int.le_ceil
Int.ceil_mono
Int.ceil_le_floor_add_one
Int.floor_le_floor
Int.floor_le_ceil
Finset.mem_Icc
MeasurableSet.iUnion
abs_sub_lt_iff
```

The `GX` route is now implemented. Additional checked declarations:

```lean
eventually_Phi_X_div_q_lower_uniform_fixed_Q
GX_Phi_X_div_q_uniform_fixed_Q
q_change_error_integral_bound
eventually_q_change_uniform_fixed_Q_core
```

`GX_Phi_X_div_q_uniform_fixed_Q` reuses `f_local_lipschitz (c := 1/2)`,
`Rcorr_inner_lipschitz_bound`, `GX_Phi_X_div_q_sub_eq_correction`,
`f_Phi_X_div_q_eq_q_div_X`, `eventually_two_mul_X_le_Phi_X_div_q_on_Icc`, and
`eventually_Phi_X_div_q_lower_uniform_fixed_Q`.

Useful APIs for the bounded-test q-change core:

```lean
intervalIntegral.norm_integral_le_of_norm_le_const
Set.uIoc_of_le
sq_le_sq₀
div_le_iff₀
abs_mul
mul_le_mul
```

The dynamic `EfloorMain` q-change wrapper is now implemented. Additional checked
declarations:

```lean
PhiDerivOverR_measurable
q_fract_GX_Phi_raw_measurable
q_fract_GX_Phi_weight_intervalIntegrable_of_jacobian_bound
theorem eventually_q_change_uniform_fixed_Q
    (D : PhiPsiData B) {Q ε : ℝ} (hQ : (1 : ℝ) ≤ Q) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      |(Real.log X / (2 * lam * X)) * EfloorMain D Q X -
        ∫ q in (1 : ℝ)..Q,
          fract (GX D X (D.Phi (X / q))) / q ^ 2| ≤ ε
```

The wrapper uses the exact q-change, rewrites the normalized exact Jacobian integral with
`intervalIntegral.integral_const_mul`, justifies subtracting the model integral with
`intervalIntegral.integral_sub`, and applies `q_change_error_integral_bound` directly to the
`X`-dependent fractional test function. The earlier fixed-`F` core remains useful, but the
dynamic wrapper should not instantiate it with an `X`-dependent function outside the filter.

Useful APIs for the wrapper:

```lean
PhiDerivFormula_measurable
MeasureTheory.Measure.integrableOn_of_bounded
intervalIntegrable_iff_integrableOn_Ioc_of_le
intervalIntegral.integral_const_mul
intervalIntegral.integral_sub
intervalIntegral.integral_congr
abs_add_le
pow_ne_zero
field_simp
```

Read-only sidecars returned later proof routes:

```lean

theorem eventually_q_change_uniform_fixed_Q
    {B Q ε : ℝ} (hQ : (1 : ℝ) ≤ Q) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ F : ℝ → ℝ,
        Measurable F →
        (∀ q ∈ Set.Icc (1 : ℝ) Q, |F q| ≤ 1) →
        |(Real.log X / (2 * lam * X)) *
          ∫ q in (1 : ℝ)..Q,
              F q * (X / q ^ 2 * PhiDerivOverR B (X / q)) -
          ∫ q in (1 : ℝ)..Q, F q / q ^ 2| ≤ ε
```

The general bounded-measurable wrapper remains optional; the current proof path only needs the
proved `EfloorMain` specialization.

The first good/bad split helpers for fractional convergence are now implemented:

```lean
intGoodSet_union_intBadSet
disjoint_intGoodSet_intBadSet
volume_intBadSet_toReal_le
fract_integrand_close_on_good
```

Useful APIs for these helpers:

```lean
MeasureTheory.measure_biUnion_finset_le
Real.volume_Ioo
ENNReal.toReal_mono
ENNReal.toReal_sum
Set.disjoint_left
abs_fract_sub_fract_eq_of_mem_intGoodSet_of_abs_sub_lt
```

The fixed-`Q` fractional convergence, fixed-`Q` main truncation, and final normalized
floor-saving asymptotic are now implemented. Additional checked declarations:

```lean
q_fract_intervalIntegrable
fract_integrand_diff_le_two
volume_Ioc_inter_intGoodSet_toReal_le
volume_Ioc_inter_intBadSet_toReal_le
Ioc_inter_intGood_union_intBad
fract_integral_close_fixed_Q_of_uniform_close
eventually_GX_Phi_X_div_q_close_fixed_Q
fract_integral_convergence_fixed_Q
floor_main_truncation_fixed_Q
floor_saving_normalized_limit_to_IfractInf
floor_saving_normalized_limit
floor_saving_asymptotic_of_normalized
```

Useful APIs for the convergence and normalized-limit assembly:

```lean
intervalIntegral.integral_of_le
MeasureTheory.setIntegral_union
MeasureTheory.norm_setIntegral_le_of_norm_le_const
MeasureTheory.Measure.integrableOn_of_bounded
IntervalIntegrable.sub
MeasureTheory.IntegrableOn.mono_set
Metric.tendsto_nhds
Filter.Eventually.exists
tendsto_const_nhds.div_atTop
Real.isLittleO_log_id_atTop
Asymptotics.isLittleO_of_tendsto'
Filter.Tendsto.congr'
```

The final `floor_saving_asymptotic` in `FloorSaving/AnalyticInterfaces.lean` is discharged by
`floor_saving_asymptotic_of_normalized D (floor_saving_normalized_limit D)`. The sorry audit is
now clean.

### 2026-04-29 M11 endpoint limsup APIs

Use `EReal` for the final endpoint limsup. The real-valued `Filter.limsup` API requires an upper
boundedness proof to use `Filter.le_limsup_of_frequently_le`; without such a proof, mathlib has
real special cases for unbounded sequences that are not the intended extended limsup. The final
statement is:

```lean
theorem endpoint_limsup
    (A : Set ℕ) (hA : UniquePositiveDiffs A) :
    (lam : EReal) ≤ Filter.limsup
      (fun n : ℕ => (endpointSeq A hA n : EReal)) Filter.atTop
```

Checked local APIs:

```lean
Filter.limsup
Filter.le_limsup_iff'
Filter.le_limsup_of_frequently_le
Filter.frequently_atTop
Filter.eventually_atTop
Filter.Frequently.mono
Filter.Tendsto.eventually
eventually_gt_nhds
EReal.coe_le_coe_iff
```

The denominator-ratio lemma reuses the already proved continuous-majorant asymptotic:

```lean
H_log_div_log_tendsto_one
  (B : ℝ) : Tendsto (fun X => H B (Real.log X) / Real.log X) atTop (𝓝 1)
```

After composing with `tendsto_natCast_atTop_atTop`, field simplification under eventual
`0 < Real.log n` proves:

```lean
theorem denom_ratio_tendsto_one (B : ℝ) :
    Tendsto (fun n : ℕ => denom B₁ n / denom B n) Filter.atTop (𝓝 (1 : ℝ))
```

Status: implemented in `FloorSaving/EndpointLimsup.lean` together with
`endpoint_frequently_lower_bound` and `endpoint_limsup`.
