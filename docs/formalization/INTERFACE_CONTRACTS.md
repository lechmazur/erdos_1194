# Interface contracts

This file records the black-box interfaces that allow the project to prove the final contradiction before completing all analytic details.

## `PhiPsiData`

Location: `FloorSaving/PhiPsiData.lean`.

Purpose: package the tail branch of

```text
Φ(x) = λ x² / (log x - log log x + B)
```

and its inverse `ψ`, together with the majorant `f = 1/ψ` on the branch.

Essential fields:

```lean
structure PhiPsiData (B : ℝ) where
  N0 : ℕ
  Tstar : ℝ
  Phi : ℝ → ℝ
  psi : ℝ → ℝ
  f : ℝ → ℝ

  N0_ge_three : 3 ≤ N0
  Tstar_pos : 0 < Tstar

  Phi_eq : ∀ x : ℝ, Phi x = PhiFormula B x
  Tstar_eq : Tstar = Phi (N0 : ℝ)
  Phi_strictMono_tail : StrictMonoOn Phi (Set.Ici (N0 : ℝ))
  Phi_mono_tail : MonotoneOn Phi (Set.Ici (N0 : ℝ))
  Phi_maps_tail : ∀ x : ℝ, (N0 : ℝ) ≤ x → Tstar ≤ Phi x
  Phi_tendsto_atTop : Tendsto Phi Filter.atTop Filter.atTop

  psi_left_inv : ∀ t : ℝ, Tstar ≤ t → Phi (psi t) = t
  psi_right_inv : ∀ x : ℝ, (N0 : ℝ) ≤ x → psi (Phi x) = x
  psi_maps_tail : ∀ t : ℝ, Tstar ≤ t → (N0 : ℝ) ≤ psi t
  psi_pos_tail : ∀ t : ℝ, Tstar ≤ t → 0 < psi t
  psi_mono_tail : MonotoneOn psi (Set.Ici Tstar)
  psi_le_of_le_Phi :
    ∀ {t x : ℝ}, Tstar ≤ t → (N0 : ℝ) ≤ x → t ≤ Phi x → psi t ≤ x

  f_eq_tail : ∀ t : ℝ, Tstar ≤ t → f t = 1 / psi t
  f_pos : ∀ t : ℝ, 0 ≤ t → 0 < f t
  f_antitone : AntitoneOn f (Set.Ici (0 : ℝ))
  f_measurable : Measurable f
  f_intervalIntegrable : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b
```

Review trigger: if `spacing`, `gap_integral_ge_one`, or the q-change proof repeatedly needs facts not in this structure, add fields deliberately and record the decision.

## Construction theorem

Location: public wrapper in `FloorSaving/AnalyticInterfaces.lean`; construction in
`FloorSaving/PhiPsiConstruction.lean`.

```lean
theorem exists_phiPsiData (B : ℝ) :
    ∃ _D : PhiPsiData B, True
```

Status: proved in M7. The wrapper delegates to `exists_phiPsiData_constructed`, which builds the
tail data from `PhiFormula`, `psiBranch`, and the constant/tail extension `fBranch`.

## Integral quantities

Location: `FloorSaving/AnalyticDefinitions.lean`.
`FloorSaving/AnalyticInterfaces.lean` imports these definitions and packages only the analytic
facts consumed by the contradiction layer.

```lean
noncomputable def I (D : PhiPsiData B) (X : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..X, D.f t

noncomputable def GX (D : PhiPsiData B) (X t : ℝ) : ℝ :=
  ∫ s in (t - X)..t, D.f s

noncomputable def JB (D : PhiPsiData B) (X : ℝ) : ℝ :=
  (1 / 2) * (I D X) ^ 2 +
    ∫ t in X..D.Phi X, D.f t * GX D X t

noncomputable def fract (x : ℝ) : ℝ :=
  Int.fract x

noncomputable def Efloor (D : PhiPsiData B) (X : ℝ) : ℝ :=
  ∫ t in X..D.Phi X, D.f t * fract (GX D X t)
```

The continuous floor contribution is exposed by the checked algebraic lemma:

```lean
theorem JB_sub_Efloor_sub_half_I_sq_eq_floor_integral
    (D : PhiPsiData B) (X : ℝ)
    (hGX :
      IntervalIntegrable (fun t : ℝ => D.f t * GX D X t)
        MeasureTheory.volume X (D.Phi X))
    (hfract :
      IntervalIntegrable (fun t : ℝ => D.f t * fract (GX D X t))
        MeasureTheory.volume X (D.Phi X)) :
    JB D X - Efloor D X - (1 / 2 : ℝ) * (I D X) ^ 2 =
      ∫ t in X..D.Phi X, D.f t * ((⌊GX D X t⌋ : ℤ) : ℝ)
```

On nonnegative tails the integrability side conditions are now discharged by:

```lean
theorem JB_sub_Efloor_sub_half_I_sq_eq_floor_integral_of_nonneg
    (D : PhiPsiData B) (hX : 0 ≤ X) (hXPhi : X ≤ D.Phi X) :
    JB D X - Efloor D X - (1 / 2 : ℝ) * (I D X) ^ 2 =
      ∫ t in X..D.Phi X, D.f t * ((⌊GX D X t⌋ : ℤ) : ℝ)
```

The M5 large floor-sum proof targets this integral form.

Checked tail monotonicity and integrability helpers now available:

```lean
theorem GX_nonneg_of_nonneg_window ...
theorem GX_le_I_of_nonneg_window ...
theorem GX_antitoneOn_Ici ...
theorem I_continuous ...
theorem GX_eq_primitive_sub ...
theorem GX_continuous_in_t ...
theorem GX_measurable_in_t ...
theorem floor_GX_nonneg_of_nonneg_window ...
theorem floor_GX_le_I_of_nonneg_window ...
theorem floor_GX_antitoneOn_Ici ...

theorem f_mul_GX_intervalIntegrable
    (D : PhiPsiData B) (hX : 0 ≤ X) (hXY : X ≤ Y) :
    IntervalIntegrable (fun t : ℝ => D.f t * GX D X t)
      MeasureTheory.volume X Y

theorem f_mul_floor_GX_intervalIntegrable
    (D : PhiPsiData B) (hX : 0 ≤ X) (hXY : X ≤ Y) :
    IntervalIntegrable
      (fun t : ℝ => D.f t * ((⌊GX D X t⌋ : ℤ) : ℝ))
      MeasureTheory.volume X Y

theorem fract_GX_measurable
    (D : PhiPsiData B) (X : ℝ) :
    Measurable (fun t : ℝ => fract (GX D X t))

theorem f_mul_fract_GX_intervalIntegrable
    (D : PhiPsiData B) (hX : 0 ≤ X) (hXY : X ≤ Y) :
    IntervalIntegrable
      (fun t : ℝ => D.f t * fract (GX D X t))
      MeasureTheory.volume X Y
```

The weighted finite-chain comparison and endpoint loss are now proved in `Counting.lean`.

## Final analytic facts

Only these are needed for the final contradiction:

```lean
structure FinalAnalyticFacts (D : PhiPsiData B) : Prop where
  continuous_majorant_nat : ... =o[Filter.atTop] scaleNat
  floor_saving_nat : ... =o[Filter.atTop] scaleNat
```

The final contradiction theorem must use this package, not the full internal analytic proofs.

## Full analytic package

The later analytic files should prove:

```lean
structure AnalyticFacts (D : PhiPsiData B) : Prop extends FinalAnalyticFacts D where
  f_asymptotic : ...
  integral_f_asymptotic : ...
  continuous_majorant_real : ...
  floor_saving_real : ...
```

## Fundamental upper bound

Location: `FloorSaving/Counting.lean`.

The fundamental upper bound should remain in explicit error-function form:

```lean
def FundamentalUpperBound {B : ℝ} (D : PhiPsiData B) : Prop :=
  ∃ err : ℕ → ℝ,
    err =o[Filter.atTop] scaleNat ∧
    ∀ᶠ X : ℕ in Filter.atTop,
      (X : ℝ) ≤ JB D (X : ℝ) - Efloor D (X : ℝ) + err X
```

This form is preferred because it avoids informal `+ o(X/log X)` manipulation in Lean.

The current M5 assembly isolates the error work in two named estimates. Both are proved. The
large floor-sum estimate carries the gap threshold hypothesis for the same `Z0` used in the
top-counting split:

```lean
theorem small_short_error_bound ... :
    ∃ err : ℕ → ℝ,
      err =o[Filter.atTop] scaleNat ∧
      ∀ᶠ X : ℕ in Filter.atTop,
        smallShortMajorant A Z0 X ≤
          (1 / 2 : ℝ) * (I D (X : ℝ)) ^ 2 + err X

theorem large_floor_sum_error_bound ...
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

`three_part_error_bound` and `fundamental_upper_bound` are proved from these estimates. In
`fundamental_upper_bound`, `Z0` and `hgap` are obtained directly from `gap_integral_ge_one` so the
finite split and the large-floor comparison use the same threshold.

## Final contradiction interface

Location: `FloorSaving/MainSkeleton.lean`.

```lean
theorem contradiction_from_interfaces
    {B : ℝ} (D : PhiPsiData B)
    (hB : B₁ < B)
    (hfund : FundamentalUpperBound D)
    (hfacts : FinalAnalyticFacts D) :
    False
```

M6 is complete when this theorem and `not_eventually_upper_bound` are proved.
