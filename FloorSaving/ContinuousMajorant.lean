import FloorSaving.FAsymptotics
import FloorSaving.AnalyticDefinitions

noncomputable section

open Filter Topology MeasureTheory Asymptotics
open scoped Real BigOperators

namespace FloorSaving

variable {B : ℝ}

/-- Lower square-change endpoint `log (ψ X)`. -/
noncomputable def w0 (D : PhiPsiData B) (X : ℝ) : ℝ :=
  Real.log (D.psi X)

/-- Offset of `w0` from the main scale `(log X) / 2`. -/
noncomputable def rX (D : PhiPsiData B) (X : ℝ) : ℝ :=
  w0 D X - Real.log X / 2

/-- The correction term after splitting `GX` into its constant and fluctuation parts. -/
noncomputable def Rcorr (D : PhiPsiData B) (X : ℝ) : ℝ :=
  ∫ t in X..D.Phi X, D.f t * ∫ s in (t - X)..t, (D.f s - D.f t)

/-- Fixed-multiple truncation of `Rcorr`. -/
noncomputable def RcorrTrunc (D : PhiPsiData B) (X U : ℝ) : ℝ :=
  ∫ t in X..(U * X), D.f t * ∫ s in (t - X)..t, (D.f s - D.f t)

/-- Normalized first-order profile used in the correction limit. -/
noncomputable def gNorm (D : PhiPsiData B) (X v : ℝ) : ℝ :=
  Real.sqrt (X * Real.log X / (2 * lam)) * D.f (X * v)

/-- Limiting kernel for the normalized correction term. -/
noncomputable def corrKernel (u : ℝ) : ℝ :=
  2 * (1 - Real.sqrt (1 - 1 / u)) - 1 / u

/-- The singular profile `v ↦ (sqrt v)⁻¹` is integrable on `[0,U]`. -/
theorem inv_sqrt_intervalIntegrable_zero {U : ℝ} (hU : 0 ≤ U) :
    IntervalIntegrable (fun v : ℝ => (Real.sqrt v)⁻¹) MeasureTheory.volume (0 : ℝ) U := by
  have hpow :
      IntervalIntegrable (fun v : ℝ => v ^ (-(1 / 2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) U := by
    exact intervalIntegral.intervalIntegrable_rpow'
      (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))
  refine hpow.congr ?_
  intro v hv
  rw [Set.uIoc_of_le hU] at hv
  have hvpos : 0 < v := hv.1
  calc
    v ^ (-(1 / 2 : ℝ)) = (v ^ (1 / 2 : ℝ))⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hvpos)]
    _ = (Real.sqrt v)⁻¹ := by rw [Real.sqrt_eq_rpow]

/-- Exact integral of the limiting singular profile on `[0,ε]`. -/
theorem integral_inv_sqrt_zero_eq {ε : ℝ} (hε : 0 ≤ ε) :
    ∫ v in (0 : ℝ)..ε, (Real.sqrt v)⁻¹ = 2 * Real.sqrt ε := by
  have hcongr :
      ∫ v in (0 : ℝ)..ε, (Real.sqrt v)⁻¹ =
        ∫ v in (0 : ℝ)..ε, v ^ (-(1 / 2 : ℝ)) := by
    refine intervalIntegral.integral_congr ?_
    intro v hv
    rw [Set.uIcc_of_le hε] at hv
    by_cases hvzero : v = 0
    · subst v
      norm_num
    · have hvpos : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hvzero)
      calc
        (Real.sqrt v)⁻¹ = (v ^ (1 / 2 : ℝ))⁻¹ := by rw [Real.sqrt_eq_rpow]
        _ = v ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_neg (le_of_lt hvpos)]
  rw [hcongr]
  have h := integral_rpow (a := (0 : ℝ)) (b := ε)
    (r := (-(1 / 2 : ℝ))) (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))
  rw [h]
  have hzero : (0 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1) = 0 := by norm_num
  rw [hzero, Real.sqrt_eq_rpow]
  ring_nf

/-- Exact integral of the limiting singular profile on a nonnegative ordered interval. -/
theorem integral_inv_sqrt_eq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ v in a..b, (Real.sqrt v)⁻¹ = 2 * Real.sqrt b - 2 * Real.sqrt a := by
  have hcongr :
      ∫ v in a..b, (Real.sqrt v)⁻¹ =
        ∫ v in a..b, v ^ (-(1 / 2 : ℝ)) := by
    refine intervalIntegral.integral_congr ?_
    intro v hv
    rw [Set.uIcc_of_le hab] at hv
    by_cases hvzero : v = 0
    · subst v
      norm_num
    · have hvpos : 0 < v := lt_of_le_of_ne (le_trans ha hv.1) (Ne.symm hvzero)
      calc
        (Real.sqrt v)⁻¹ = (v ^ (1 / 2 : ℝ))⁻¹ := by rw [Real.sqrt_eq_rpow]
        _ = v ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_neg (le_of_lt hvpos)]
  rw [hcongr]
  have h := integral_rpow (a := a) (b := b)
    (r := (-(1 / 2 : ℝ))) (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))
  rw [h]
  have ha_rpow : a ^ ((-(1 / 2 : ℝ)) + 1) = Real.sqrt a := by
    norm_num
    rw [Real.sqrt_eq_rpow]
  have hb_rpow : b ^ ((-(1 / 2 : ℝ)) + 1) = Real.sqrt b := by
    norm_num
    rw [Real.sqrt_eq_rpow]
  rw [ha_rpow, hb_rpow]
  ring

/-- The pointwise limiting correction integrand is exactly `corrKernel`. -/
theorem corr_limit_integrand_eq_corrKernel {u : ℝ} (hu : 1 ≤ u) :
    (Real.sqrt u)⁻¹ *
        (∫ v in (u - 1)..u, ((Real.sqrt v)⁻¹ - (Real.sqrt u)⁻¹)) =
      corrKernel u := by
  have hu_nonneg : 0 ≤ u := le_trans zero_le_one hu
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hum1_nonneg : 0 ≤ u - 1 := sub_nonneg.mpr hu
  have hum1_le : u - 1 ≤ u := by linarith
  have hsqrtu_ne : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu_pos)
  have hint_inv : IntervalIntegrable (fun v : ℝ => (Real.sqrt v)⁻¹)
      MeasureTheory.volume (u - 1) u :=
    (inv_sqrt_intervalIntegrable_zero hu_nonneg).mono_set (by
      rw [Set.uIcc_of_le hum1_le, Set.uIcc_of_le hu_nonneg]
      intro v hv
      exact ⟨le_trans hum1_nonneg hv.1, hv.2⟩)
  have hint_const : IntervalIntegrable (fun _v : ℝ => (Real.sqrt u)⁻¹)
      MeasureTheory.volume (u - 1) u :=
    intervalIntegral.intervalIntegrable_const
  have hinner :
      ∫ v in (u - 1)..u, ((Real.sqrt v)⁻¹ - (Real.sqrt u)⁻¹) =
        2 * Real.sqrt u - 2 * Real.sqrt (u - 1) - (Real.sqrt u)⁻¹ := by
    rw [intervalIntegral.integral_sub hint_inv hint_const]
    rw [integral_inv_sqrt_eq_of_nonneg hum1_nonneg hum1_le]
    rw [intervalIntegral.integral_const]
    simp
  have hsqrt_ratio : Real.sqrt (1 - 1 / u) = Real.sqrt (u - 1) / Real.sqrt u := by
    have hratio : 1 - 1 / u = (u - 1) / u := by
      field_simp [ne_of_gt hu_pos]
    rw [hratio, Real.sqrt_div hum1_nonneg]
  rw [hinner]
  unfold corrKernel
  rw [hsqrt_ratio]
  field_simp [hsqrtu_ne]
  nlinarith [Real.sq_sqrt hu_nonneg]

/-- `gNorm` is interval-integrable on every finite interval when `X ≠ 0`. -/
theorem gNorm_intervalIntegrable (D : PhiPsiData B) {X a b : ℝ} (hX : X ≠ 0) :
    IntervalIntegrable (fun v : ℝ => gNorm D X v) MeasureTheory.volume a b := by
  have hf : IntervalIntegrable D.f MeasureTheory.volume (X * a) (X * b) :=
    D.f_intervalIntegrable (X * a) (X * b)
  have hcomp := hf.comp_mul_left (c := X)
  have hcomp_ab :
      IntervalIntegrable (fun v : ℝ => D.f (X * v)) MeasureTheory.volume a b := by
    convert hcomp using 4 <;> field_simp [hX]
  simpa [gNorm] using hcomp_ab.const_mul (Real.sqrt (X * Real.log X / (2 * lam)))

/-- Change variables in the small-`v` integral of the normalized profile. -/
theorem gNorm_integral_change_of_variables
    (D : PhiPsiData B) {X ε : ℝ} (hX : X ≠ 0) :
    ∫ v in (0 : ℝ)..ε, gNorm D X v =
      X⁻¹ * Real.sqrt (X * Real.log X / (2 * lam)) *
        ∫ s in (0 : ℝ)..(X * ε), D.f s := by
  simp_rw [gNorm]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left D.f hX]
  simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Inner change of variables for the normalized truncated correction window. -/
theorem RcorrTrunc_inner_change
    (D : PhiPsiData B) {X u : ℝ} (hX : X ≠ 0) :
    ∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u) =
      X⁻¹ * Real.sqrt (X * Real.log X / (2 * lam)) *
        ∫ s in (X * u - X)..(X * u), (D.f s - D.f (X * u)) := by
  let A : ℝ := Real.sqrt (X * Real.log X / (2 * lam))
  have hcongr :
      ∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u) =
        ∫ v in (u - 1)..u, A * (D.f (X * v) - D.f (X * u)) := by
    refine intervalIntegral.integral_congr ?_
    intro v _hv
    dsimp [gNorm, A]
    ring
  rw [hcongr]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left
    (fun s : ℝ => D.f s - D.f (X * u)) hX]
  rw [show X * (u - 1) = X * u - X by ring]
  dsimp [A]
  ring

/-- Outer change of variables for the truncated correction. -/
theorem RcorrTrunc_outer_change
    (D : PhiPsiData B) (X U : ℝ) :
    RcorrTrunc D X U =
      X * ∫ u in (1 : ℝ)..U,
        D.f (X * u) *
          ∫ s in (X * u - X)..(X * u), (D.f s - D.f (X * u)) := by
  let F : ℝ → ℝ := fun t =>
    D.f t * ∫ s in (t - X)..t, (D.f s - D.f t)
  have h := intervalIntegral.smul_integral_comp_mul_left
    (f := F) (a := (1 : ℝ)) (b := U) X
  rw [RcorrTrunc]
  change ∫ t in X..U * X, F t = X • ∫ u in (1 : ℝ)..U, F (X * u)
  convert h.symm using 1
  ring_nf

/-- Pointwise exact normalized form of `RcorrTrunc`, valid once `X > 1`. -/
theorem RcorrTrunc_normalized_change_of_gt_one
    (D : PhiPsiData B) {X U : ℝ} (hX_gt : 1 < X) :
    RcorrTrunc D X U =
      (2 * lam * X / Real.log X) *
        ∫ u in (1 : ℝ)..U,
          gNorm D X u *
            ∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u) := by
  let A : ℝ := Real.sqrt (X * Real.log X / (2 * lam))
  have hX_pos : 0 < X := lt_trans zero_lt_one hX_gt
  have hX_ne : X ≠ 0 := ne_of_gt hX_pos
  have hlog_pos : 0 < Real.log X := Real.log_pos hX_gt
  have hlog_ne : Real.log X ≠ 0 := ne_of_gt hlog_pos
  have hlam_pos : 0 < lam := by
    unfold lam
    positivity
  have htwo_lam_pos : 0 < 2 * lam := by positivity
  have harg_nonneg : 0 ≤ X * Real.log X / (2 * lam) := by positivity
  have hA_sq : A * A = X * Real.log X / (2 * lam) := by
    dsimp [A]
    rw [← pow_two, Real.sq_sqrt harg_nonneg]
  have hscale :
      (2 * lam * X / Real.log X) * (X⁻¹ * A * A) = X := by
    rw [show X⁻¹ * A * A = X⁻¹ * (A * A) by ring]
    rw [hA_sq]
    field_simp [hX_ne, hlog_ne, ne_of_gt htwo_lam_pos, ne_of_gt hlam_pos]
  rw [RcorrTrunc_outer_change]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr ?_
  intro u _hu
  change X * (D.f (X * u) *
      ∫ s in (X * u - X)..(X * u), (D.f s - D.f (X * u))) =
    (2 * lam * X / Real.log X) *
      (gNorm D X u * ∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u))
  rw [RcorrTrunc_inner_change D hX_ne]
  dsimp [gNorm, A]
  calc
    X * (D.f (X * u) *
        ∫ s in (X * u - X)..(X * u), (D.f s - D.f (X * u)))
        = ((2 * lam * X / Real.log X) * (X⁻¹ * A * A)) *
            (D.f (X * u) *
              ∫ s in (X * u - X)..(X * u), (D.f s - D.f (X * u))) := by
          rw [hscale]
    _ = (2 * lam * X / Real.log X) *
          (A * D.f (X * u) *
            (X⁻¹ * A *
              ∫ s in (X * u - X)..(X * u), (D.f s - D.f (X * u)))) := by
          ring

/-- Eventual exact normalized form of the fixed-`U` truncated correction. -/
theorem RcorrTrunc_normalized_change
    (D : PhiPsiData B) {U : ℝ} (_hU : 1 ≤ U) :
    ∀ᶠ X : ℝ in Filter.atTop,
      RcorrTrunc D X U =
        (2 * lam * X / Real.log X) *
          ∫ u in (1 : ℝ)..U,
            gNorm D X u *
              ∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  exact RcorrTrunc_normalized_change_of_gt_one D hX

/-- The normalized error profile is interval-integrable on `[0,U]`. -/
theorem gNorm_sub_inv_sqrt_abs_intervalIntegrable
    (D : PhiPsiData B) {X U : ℝ} (hX : X ≠ 0) (hU : 0 ≤ U) :
    IntervalIntegrable
      (fun v : ℝ => |gNorm D X v - (Real.sqrt v)⁻¹|)
      MeasureTheory.volume (0 : ℝ) U := by
  exact ((gNorm_intervalIntegrable D (a := (0 : ℝ)) (b := U) hX).sub
    (inv_sqrt_intervalIntegrable_zero hU)).abs

/-- The normalized profile is nonnegative on the nonnegative quadrant. -/
theorem gNorm_nonneg (D : PhiPsiData B) {X v : ℝ} (hX : 0 ≤ X) (hv : 0 ≤ v) :
    0 ≤ gNorm D X v := by
  have hXv : 0 ≤ X * v := mul_nonneg hX hv
  have hf : 0 ≤ D.f (X * v) := le_of_lt (D.f_pos (X * v) hXv)
  rw [gNorm]
  exact mul_nonneg (Real.sqrt_nonneg _) hf

/-- For nonnegative reals, the absolute difference is bounded by the sum. -/
theorem abs_sub_le_add_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| ≤ a + b := by
  rw [abs_le]
  constructor <;> linarith

/-- A small-interval bound for `∫ gNorm` implies the corresponding small-interval L¹ bound. -/
theorem gNorm_small_v_L1_bound_of_integral_bound
    (D : PhiPsiData B) {C ε X : ℝ}
    (hX_ne : X ≠ 0) (hX_nonneg : 0 ≤ X) (hε : 0 ≤ ε)
    (hbound : ∫ v in (0 : ℝ)..ε, gNorm D X v ≤ C * Real.sqrt ε) :
    ∫ v in (0 : ℝ)..ε, |gNorm D X v - (Real.sqrt v)⁻¹| ≤
      (C + 2) * Real.sqrt ε := by
  have herr_int :
      IntervalIntegrable
        (fun v : ℝ => |gNorm D X v - (Real.sqrt v)⁻¹|)
        MeasureTheory.volume (0 : ℝ) ε :=
    gNorm_sub_inv_sqrt_abs_intervalIntegrable D hX_ne hε
  have hg_int :
      IntervalIntegrable (fun v : ℝ => gNorm D X v)
        MeasureTheory.volume (0 : ℝ) ε :=
    gNorm_intervalIntegrable D hX_ne
  have hinv_int :
      IntervalIntegrable (fun v : ℝ => (Real.sqrt v)⁻¹)
        MeasureTheory.volume (0 : ℝ) ε :=
    inv_sqrt_intervalIntegrable_zero hε
  have hsum_int :
      IntervalIntegrable (fun v : ℝ => gNorm D X v + (Real.sqrt v)⁻¹)
        MeasureTheory.volume (0 : ℝ) ε :=
    hg_int.add hinv_int
  have hpoint :
      ∀ v ∈ Set.Icc (0 : ℝ) ε,
        |gNorm D X v - (Real.sqrt v)⁻¹| ≤
          gNorm D X v + (Real.sqrt v)⁻¹ := by
    intro v hv
    exact abs_sub_le_add_of_nonneg (gNorm_nonneg D hX_nonneg hv.1)
      (inv_nonneg.mpr (Real.sqrt_nonneg v))
  have hmono :
      ∫ v in (0 : ℝ)..ε, |gNorm D X v - (Real.sqrt v)⁻¹| ≤
        ∫ v in (0 : ℝ)..ε, (gNorm D X v + (Real.sqrt v)⁻¹) :=
    intervalIntegral.integral_mono_on hε herr_int hsum_int hpoint
  calc
    ∫ v in (0 : ℝ)..ε, |gNorm D X v - (Real.sqrt v)⁻¹|
        ≤ ∫ v in (0 : ℝ)..ε, (gNorm D X v + (Real.sqrt v)⁻¹) := hmono
    _ = (∫ v in (0 : ℝ)..ε, gNorm D X v) +
          ∫ v in (0 : ℝ)..ε, (Real.sqrt v)⁻¹ := by
          rw [intervalIntegral.integral_add hg_int hinv_int]
    _ ≤ C * Real.sqrt ε + 2 * Real.sqrt ε := by
          rw [integral_inv_sqrt_zero_eq hε]
          exact add_le_add hbound le_rfl
    _ = (C + 2) * Real.sqrt ε := by ring

/-- Eventual version of `gNorm_small_v_L1_bound_of_integral_bound`. -/
theorem gNorm_small_v_L1_eventual_bound_of_integral_eventual_bound
    (D : PhiPsiData B) {C ε : ℝ} (hε : 0 ≤ ε)
    (hbound :
      ∀ᶠ X : ℝ in Filter.atTop,
        ∫ v in (0 : ℝ)..ε, gNorm D X v ≤ C * Real.sqrt ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∫ v in (0 : ℝ)..ε, |gNorm D X v - (Real.sqrt v)⁻¹| ≤
        (C + 2) * Real.sqrt ε := by
  filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with X hXbound hX_pos
  exact gNorm_small_v_L1_bound_of_integral_bound D (ne_of_gt hX_pos)
    (le_of_lt hX_pos) hε hXbound

/-- Existential form of the small-`v` L¹ bridge. -/
theorem gNorm_small_v_L1_eventual_bound_of_integral_eventual_bound_exists
    (D : PhiPsiData B)
    (hbound :
      ∃ C : ℝ, 0 < C ∧
        ∀ ⦃ε : ℝ⦄, 0 ≤ ε →
          ∀ᶠ X : ℝ in Filter.atTop,
            ∫ v in (0 : ℝ)..ε, gNorm D X v ≤ C * Real.sqrt ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃ε : ℝ⦄, 0 ≤ ε →
        ∀ᶠ X : ℝ in Filter.atTop,
          ∫ v in (0 : ℝ)..ε, |gNorm D X v - (Real.sqrt v)⁻¹| ≤
            C * Real.sqrt ε := by
  rcases hbound with ⟨C, hC_pos, hC⟩
  refine ⟨C + 2, by positivity, ?_⟩
  intro ε hε
  exact gNorm_small_v_L1_eventual_bound_of_integral_eventual_bound D hε (hC hε)

/-- Tail integral bound for `f`, in the form needed for the small-`v` estimate. -/
theorem f_integral_tail_sqrtLogPrimitive_bound
    (D : PhiPsiData B) :
    ∃ C T : ℝ, 0 < C ∧ Real.exp 2 ≤ T ∧
      ∀ ⦃V : ℝ⦄, T ≤ V →
        ∫ t in T..V, D.f t ≤ C * sqrtLogPrimitive V := by
  rcases D.f_upper_bound with ⟨C₀, T₀, hC₀_pos, hbound⟩
  let T : ℝ := max T₀ (Real.exp 2)
  let C : ℝ := 4 * C₀
  refine ⟨C, T, ?_, ?_, ?_⟩
  · dsimp [C]
    positivity
  · exact le_max_right T₀ (Real.exp 2)
  · intro V hTV
    have hT_exp : Real.exp 2 ≤ T := le_max_right T₀ (Real.exp 2)
    have hT₀T : T₀ ≤ T := le_max_left T₀ (Real.exp 2)
    have hf_int : IntervalIntegrable D.f MeasureTheory.volume T V :=
      D.f_intervalIntegrable T V
    have hmodel_int :
        IntervalIntegrable (fun t : ℝ => C₀ * invSqrtLogModel t)
          MeasureTheory.volume T V := by
      have hcont : ContinuousOn invSqrtLogModel (Set.Icc T V) :=
        invSqrtLogModel_continuousOn_Icc_of_exp_two_le hT_exp
      exact (hcont.intervalIntegrable_of_Icc hTV).const_mul C₀
    have hmono :
        ∫ t in T..V, D.f t ≤ ∫ t in T..V, C₀ * invSqrtLogModel t := by
      refine intervalIntegral.integral_mono_on hTV hf_int hmodel_int ?_
      intro t ht
      have hT₀t : T₀ ≤ t := hT₀T.trans ht.1
      have hdf := hbound t hT₀t
      simpa [invSqrtLogModel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdf
    have htail := elementary_integral_bound (T := T) (V := V) hT_exp hTV
    calc
      ∫ t in T..V, D.f t ≤ ∫ t in T..V, C₀ * invSqrtLogModel t := hmono
      _ = C₀ * ∫ t in T..V, invSqrtLogModel t := by
            rw [intervalIntegral.integral_const_mul]
      _ ≤ C₀ * (4 * sqrtLogPrimitive V) :=
            mul_le_mul_of_nonneg_left htail (le_of_lt hC₀_pos)
      _ = C * sqrtLogPrimitive V := by
            dsimp [C]
            ring

/-- Algebraic normalization for the tail primitive in the small-`v` estimate. -/
theorem gNorm_scale_sqrtLogPrimitive_eq
    {X ε : ℝ} (hX : 0 < X) (hε : 0 ≤ ε)
    (hlogX : 0 < Real.log X) (hlogXε : 0 < Real.log (X * ε)) :
    X⁻¹ * Real.sqrt (X * Real.log X / (2 * lam)) * sqrtLogPrimitive (X * ε) =
      Real.sqrt ε / Real.sqrt (2 * lam) *
        Real.sqrt (Real.log X / Real.log (X * ε)) := by
  have hX_nonneg : 0 ≤ X := le_of_lt hX
  have hlogX_nonneg : 0 ≤ Real.log X := le_of_lt hlogX
  have hlam_pos : 0 < 2 * lam := by
    unfold lam
    positivity
  have hXε_nonneg : 0 ≤ X * ε := mul_nonneg hX_nonneg hε
  rw [sqrtLogPrimitive]
  rw [Real.sqrt_div (mul_nonneg hX_nonneg hlogX_nonneg)]
  rw [Real.sqrt_mul hX_nonneg]
  rw [Real.sqrt_div hXε_nonneg]
  rw [Real.sqrt_mul hX_nonneg]
  rw [Real.sqrt_div hlogX_nonneg]
  field_simp [Real.sqrt_ne_zero'.mpr hX, Real.sqrt_ne_zero'.mpr hlam_pos,
    Real.sqrt_ne_zero'.mpr hlogXε]
  rw [Real.sq_sqrt hX_nonneg]

/-- Inequality form of `gNorm_scale_sqrtLogPrimitive_eq`. -/
theorem gNorm_scale_sqrtLogPrimitive_le
    {X ε K : ℝ} (hX : 0 < X) (hε : 0 ≤ ε)
    (hlogX : 0 < Real.log X) (hlogXε : 0 < Real.log (X * ε))
    (hratio : Real.sqrt (Real.log X / Real.log (X * ε)) ≤ K) :
    X⁻¹ * Real.sqrt (X * Real.log X / (2 * lam)) * sqrtLogPrimitive (X * ε) ≤
      (K / Real.sqrt (2 * lam)) * Real.sqrt ε := by
  calc
    X⁻¹ * Real.sqrt (X * Real.log X / (2 * lam)) * sqrtLogPrimitive (X * ε)
        =
        Real.sqrt ε / Real.sqrt (2 * lam) *
          Real.sqrt (Real.log X / Real.log (X * ε)) :=
          gNorm_scale_sqrtLogPrimitive_eq hX hε hlogX hlogXε
    _ ≤ Real.sqrt ε / Real.sqrt (2 * lam) * K :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (K / Real.sqrt (2 * lam)) * Real.sqrt ε := by ring

/-- For fixed positive `v`, `log (Xv) / log X → 1`. -/
theorem log_mul_const_div_log_tendsto_one {v : ℝ} (hv : 0 < v) :
    Tendsto (fun X : ℝ => Real.log (X * v) / Real.log X) Filter.atTop (𝓝 (1 : ℝ)) := by
  have hdiff_eq :
      (fun X : ℝ => Real.log (X * v) - Real.log X) =ᶠ[Filter.atTop]
        fun _X : ℝ => Real.log v := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hX_ne : X ≠ 0 := ne_of_gt hX
    have hv_ne : v ≠ 0 := ne_of_gt hv
    rw [Real.log_mul hX_ne hv_ne]
    ring
  have hdiff : Tendsto (fun X : ℝ => Real.log (X * v) - Real.log X)
      Filter.atTop (𝓝 (Real.log v)) := by
    exact tendsto_const_nhds.congr' hdiff_eq.symm
  have hratio_diff :
      Tendsto (fun X : ℝ => (Real.log (X * v) - Real.log X) / Real.log X)
        Filter.atTop (𝓝 0) := by
    have hinv : Tendsto (fun X : ℝ => (Real.log X)⁻¹) Filter.atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    simpa [div_eq_mul_inv] using hdiff.mul hinv
  have hsum : Tendsto
      (fun X : ℝ => 1 + (Real.log (X * v) - Real.log X) / Real.log X)
      Filter.atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add hratio_diff
  have htarget : Tendsto (fun X : ℝ => Real.log (X * v) / Real.log X)
      Filter.atTop (𝓝 (1 + 0)) := by
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hlog_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
    field_simp [hlog_ne]
    ring
  simpa using htarget

/-- For fixed positive `v`, the reciprocal log ratio also tends to `1`. -/
theorem log_div_log_mul_const_tendsto_one {v : ℝ} (hv : 0 < v) :
    Tendsto (fun X : ℝ => Real.log X / Real.log (X * v)) Filter.atTop (𝓝 (1 : ℝ)) := by
  have hratio := log_mul_const_div_log_tendsto_one hv
  have hinv_ratio :
      Tendsto (fun X : ℝ => (1 : ℝ) / (Real.log (X * v) / Real.log X))
        Filter.atTop (𝓝 ((1 : ℝ) / 1)) :=
    tendsto_const_nhds.div hratio (by norm_num : (1 : ℝ) ≠ 0)
  have htarget : Tendsto (fun X : ℝ => Real.log X / Real.log (X * v))
      Filter.atTop (𝓝 ((1 : ℝ) / 1)) := by
    refine hinv_ratio.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ),
        (Filter.Tendsto.atTop_mul_const hv tendsto_id).eventually_gt_atTop (1 : ℝ)] with
      X hX hXv
    have hlogX_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
    have hlogXv_ne : Real.log (X * v) ≠ 0 := ne_of_gt (Real.log_pos hXv)
    field_simp [hlogX_ne, hlogXv_ne]
  simpa using htarget

/-- For a fixed positive multiplier, the square-root log ratio is eventually bounded by `2`. -/
theorem eventually_sqrt_log_ratio_mul_const_le_two {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      Real.sqrt (Real.log X / Real.log (X * ε)) ≤ 2 := by
  filter_upwards [
      (log_div_log_mul_const_tendsto_one hε).eventually_le_const
        (by norm_num : (1 : ℝ) < 4)] with X hratio
  calc
    Real.sqrt (Real.log X / Real.log (X * ε)) ≤ Real.sqrt 4 :=
      Real.sqrt_le_sqrt hratio
    _ = 2 := by norm_num

/-- `sqrt (log X)` is negligible compared with `sqrt X`. -/
theorem sqrt_log_isLittleO_sqrt_self :
    (fun X : ℝ => Real.sqrt (Real.log X)) =o[Filter.atTop]
      fun X : ℝ => Real.sqrt X := by
  simpa using
    (Real.isLittleO_log_id_atTop.sqrt (eventually_ge_atTop (0 : ℝ)))

/-- The fixed compact part in the small-`v` estimate is killed by the normalization. -/
theorem gNorm_compact_prefactor_tendsto_zero (A : ℝ) :
    Tendsto
      (fun X : ℝ =>
        X⁻¹ * Real.sqrt (X * Real.log X / (2 * lam)) * A)
      Filter.atTop (𝓝 0) := by
  have hratio :
      Tendsto (fun X : ℝ => Real.sqrt (Real.log X) / Real.sqrt X)
        Filter.atTop (𝓝 0) := by
    simpa using sqrt_log_isLittleO_sqrt_self.tendsto_div_nhds_zero
  have hmul :
      Tendsto
        (fun X : ℝ =>
          (A / Real.sqrt (2 * lam)) * (Real.sqrt (Real.log X) / Real.sqrt X))
        Filter.atTop (𝓝 ((A / Real.sqrt (2 * lam)) * 0)) :=
    tendsto_const_nhds.mul hratio
  have htarget :
      Tendsto
        (fun X : ℝ =>
          X⁻¹ * Real.sqrt (X * Real.log X / (2 * lam)) * A)
        Filter.atTop (𝓝 ((A / Real.sqrt (2 * lam)) * 0)) := by
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hX_pos : 0 < X := lt_trans zero_lt_one hX
    have hX_nonneg : 0 ≤ X := le_of_lt hX_pos
    have hlog_pos : 0 < Real.log X := Real.log_pos hX
    have hlog_nonneg : 0 ≤ Real.log X := le_of_lt hlog_pos
    have hlam_pos : 0 < 2 * lam := by
      unfold lam
      positivity
    rw [Real.sqrt_div (mul_nonneg hX_nonneg hlog_nonneg)]
    rw [Real.sqrt_mul hX_nonneg]
    field_simp [Real.sqrt_ne_zero'.mpr hX_pos, Real.sqrt_ne_zero'.mpr hlam_pos]
    rw [Real.sq_sqrt hX_nonneg]
  simpa using htarget

/-- Eventual inequality form of `gNorm_compact_prefactor_tendsto_zero`. -/
theorem gNorm_compact_prefactor_eventually_le_sqrt
    {ε A : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      X⁻¹ * Real.sqrt (X * Real.log X / (2 * lam)) * A ≤ Real.sqrt ε :=
  (gNorm_compact_prefactor_tendsto_zero A).eventually_le_const (Real.sqrt_pos.mpr hε)

/-- Small-`v` integral bound for the normalized profile. -/
theorem gNorm_small_v_integral_eventual_bound
    (D : PhiPsiData B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃ε : ℝ⦄, 0 ≤ ε →
        ∀ᶠ X : ℝ in Filter.atTop,
          ∫ v in (0 : ℝ)..ε, gNorm D X v ≤ C * Real.sqrt ε := by
  rcases f_integral_tail_sqrtLogPrimitive_bound D with
    ⟨Cf, T, hCf_pos, hT_exp, hf_tail⟩
  let A : ℝ := ∫ t in (0 : ℝ)..T, D.f t
  let C : ℝ := 1 + Cf * (2 / Real.sqrt (2 * lam))
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro ε hε_nonneg
  by_cases hε_zero : ε = 0
  · subst ε
    filter_upwards [] with X
    simp
  · have hε_pos : 0 < ε := lt_of_le_of_ne hε_nonneg (Ne.symm hε_zero)
    filter_upwards [eventually_gt_atTop (1 : ℝ),
        (Filter.Tendsto.atTop_mul_const hε_pos tendsto_id).eventually_ge_atTop T,
        eventually_sqrt_log_ratio_mul_const_le_two hε_pos,
        gNorm_compact_prefactor_eventually_le_sqrt (ε := ε) (A := A) hε_pos] with
      X hX_gt_one hT_le_Xε hratio hcompact
    have hX_pos : 0 < X := lt_trans zero_lt_one hX_gt_one
    have hX_ne : X ≠ 0 := ne_of_gt hX_pos
    have hlogX_pos : 0 < Real.log X := Real.log_pos hX_gt_one
    have hXε_exp : Real.exp 2 ≤ X * ε := hT_exp.trans hT_le_Xε
    have hXε_pos : 0 < X * ε := lt_of_lt_of_le (Real.exp_pos 2) hXε_exp
    have hlogXε_pos : 0 < Real.log (X * ε) := by
      have hlog_ge_two : (2 : ℝ) ≤ Real.log (X * ε) :=
        (Real.le_log_iff_exp_le hXε_pos).2 hXε_exp
      linarith
    let S : ℝ := X⁻¹ * Real.sqrt (X * Real.log X / (2 * lam))
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt hX_pos)) (Real.sqrt_nonneg _)
    have hf0T : IntervalIntegrable D.f MeasureTheory.volume (0 : ℝ) T :=
      D.f_intervalIntegrable (0 : ℝ) T
    have hfTX : IntervalIntegrable D.f MeasureTheory.volume T (X * ε) :=
      D.f_intervalIntegrable T (X * ε)
    have hsplit :
        (∫ t in (0 : ℝ)..T, D.f t) + (∫ t in T..(X * ε), D.f t) =
          ∫ t in (0 : ℝ)..(X * ε), D.f t :=
      intervalIntegral.integral_add_adjacent_intervals hf0T hfTX
    have htail :
        ∫ t in T..(X * ε), D.f t ≤ Cf * sqrtLogPrimitive (X * ε) :=
      hf_tail hT_le_Xε
    have hInt :
        ∫ t in (0 : ℝ)..(X * ε), D.f t ≤ A + Cf * sqrtLogPrimitive (X * ε) := by
      calc
        ∫ t in (0 : ℝ)..(X * ε), D.f t =
            (∫ t in (0 : ℝ)..T, D.f t) + ∫ t in T..(X * ε), D.f t := by
              rw [← hsplit]
        _ ≤ A + Cf * sqrtLogPrimitive (X * ε) := by
              dsimp [A]
              exact add_le_add_right htail _
    have hcompactS : S * A ≤ Real.sqrt ε := by
      simpa [S] using hcompact
    have hprim :
        S * sqrtLogPrimitive (X * ε) ≤
          (2 / Real.sqrt (2 * lam)) * Real.sqrt ε := by
      simpa [S] using
        gNorm_scale_sqrtLogPrimitive_le (X := X) (ε := ε) (K := 2)
          hX_pos hε_nonneg hlogX_pos hlogXε_pos hratio
    calc
      ∫ v in (0 : ℝ)..ε, gNorm D X v =
          S * ∫ t in (0 : ℝ)..(X * ε), D.f t := by
            rw [gNorm_integral_change_of_variables D hX_ne]
      _ ≤ S * (A + Cf * sqrtLogPrimitive (X * ε)) :=
            mul_le_mul_of_nonneg_left hInt hS_nonneg
      _ = S * A + Cf * (S * sqrtLogPrimitive (X * ε)) := by ring
      _ ≤ Real.sqrt ε + Cf * ((2 / Real.sqrt (2 * lam)) * Real.sqrt ε) :=
            add_le_add hcompactS
              (mul_le_mul_of_nonneg_left hprim (le_of_lt hCf_pos))
      _ = C * Real.sqrt ε := by
            dsimp [C]
            ring

/-- Small-`v` L¹ bound for the normalized profile. -/
theorem gNorm_small_v_L1_eventual_bound
    (D : PhiPsiData B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃ε : ℝ⦄, 0 ≤ ε →
        ∀ᶠ X : ℝ in Filter.atTop,
          ∫ v in (0 : ℝ)..ε,
            |gNorm D X v - (Real.sqrt v)⁻¹| ≤ C * Real.sqrt ε :=
  gNorm_small_v_L1_eventual_bound_of_integral_eventual_bound_exists D
    (gNorm_small_v_integral_eventual_bound D)

/-- Uniform control of `log X / log (Xv)` on compact intervals away from zero. -/
theorem log_div_log_mul_uniform_sub_one_le
    {ε U c : ℝ} (hε : 0 < ε) (hεU : ε ≤ U) (hc : 0 < c) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ v ∈ Set.Icc ε U,
      |Real.log X / Real.log (X * v) - 1| ≤ c := by
  let M : ℝ := |Real.log ε| + |Real.log U| + 1
  have hM_pos : 0 < M := by
    dsimp [M]
    positivity
  have hU_pos : 0 < U := lt_of_lt_of_le hε hεU
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (max (2 * M) (2 * M / c)),
      eventually_gt_atTop (0 : ℝ)] with X hlogX_ge hX_pos v hv
  let L : ℝ := Real.log X
  let lv : ℝ := Real.log v
  have hv_pos : 0 < v := lt_of_lt_of_le hε hv.1
  have hX_ne : X ≠ 0 := ne_of_gt hX_pos
  have hv_ne : v ≠ 0 := ne_of_gt hv_pos
  have hlog_mul : Real.log (X * v) = L + lv := by
    dsimp [L, lv]
    rw [Real.log_mul hX_ne hv_ne]
  have hlogε_le : Real.log ε ≤ lv := by
    dsimp [lv]
    exact Real.log_le_log hε hv.1
  have hlogv_le_U : lv ≤ Real.log U := by
    dsimp [lv]
    exact Real.log_le_log hv_pos hv.2
  have hlv_abs : |lv| ≤ M := by
    rw [abs_le]
    constructor
    · calc
        -M ≤ -|Real.log ε| := by
          dsimp [M]
          linarith [abs_nonneg (Real.log U)]
        _ ≤ Real.log ε := neg_abs_le (Real.log ε)
        _ ≤ lv := hlogε_le
    · calc
        lv ≤ Real.log U := hlogv_le_U
        _ ≤ |Real.log U| := le_abs_self (Real.log U)
        _ ≤ M := by
          dsimp [M]
          linarith [abs_nonneg (Real.log ε)]
  have hL_ge_2M : 2 * M ≤ L := by
    dsimp [L]
    exact le_trans (le_max_left _ _) hlogX_ge
  have hL_ge_2M_div : 2 * M / c ≤ L := by
    dsimp [L]
    exact le_trans (le_max_right _ _) hlogX_ge
  have hL_pos : 0 < L := by nlinarith
  have hden_lower : L / 2 ≤ L + lv := by
    have hneg : -M ≤ lv := (abs_le.mp hlv_abs).1
    nlinarith
  have hden_pos : 0 < L + lv := by nlinarith
  have hden_ne : L + lv ≠ 0 := ne_of_gt hden_pos
  have hM_le : M ≤ c * (L + lv) := by
    have hM_le_half : M ≤ c * (L / 2) := by
      have hmul := mul_le_mul_of_nonneg_left hL_ge_2M_div (le_of_lt hc)
      have hc_ne : c ≠ 0 := ne_of_gt hc
      field_simp [hc_ne] at hmul
      nlinarith
    have hhalf_le : c * (L / 2) ≤ c * (L + lv) :=
      mul_le_mul_of_nonneg_left hden_lower (le_of_lt hc)
    exact le_trans hM_le_half hhalf_le
  have hdiff : Real.log X / Real.log (X * v) - 1 = -lv / (L + lv) := by
    have hden_ne' : Real.log X + lv ≠ 0 := by simpa [L] using hden_ne
    rw [hlog_mul]
    dsimp [L]
    field_simp [hden_ne']
    ring
  rw [hdiff]
  rw [abs_div, abs_neg, abs_of_pos hden_pos]
  rw [div_le_iff₀ hden_pos]
  exact le_trans hlv_abs hM_le

/-- Square root is 1-Lipschitz against `x ↦ x` at `1` on the nonnegative line. -/
theorem abs_sqrt_sub_one_le_abs_sub_one {r : ℝ} (hr : 0 ≤ r) :
    |Real.sqrt r - 1| ≤ |r - 1| := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hsqrt_add_ge_one : 1 ≤ Real.sqrt r + 1 := by linarith
  have hfactor : r - 1 = (Real.sqrt r - 1) * (Real.sqrt r + 1) := by
    rw [sub_mul, one_mul, mul_add, mul_one, ← pow_two, Real.sq_sqrt hr]
    ring
  calc
    |Real.sqrt r - 1| = |Real.sqrt r - 1| * 1 := by ring
    _ ≤ |Real.sqrt r - 1| * (Real.sqrt r + 1) :=
      mul_le_mul_of_nonneg_left hsqrt_add_ge_one (abs_nonneg _)
    _ = |(Real.sqrt r - 1) * (Real.sqrt r + 1)| := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.sqrt r + 1)]
    _ = |r - 1| := by rw [← hfactor]

/-- Exact model algebra for the normalized profile. -/
theorem gNorm_model_eq_inv_sqrt_mul_log_ratio
    {X v : ℝ} (hv : 0 < v) (hX : 1 < X) (hXv : 1 < X * v) :
    Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v) =
      Real.sqrt (Real.log X / Real.log (X * v)) * (Real.sqrt v)⁻¹ := by
  rw [show Real.sqrt (Real.log X / Real.log (X * v)) * (Real.sqrt v)⁻¹ =
      Real.sqrt (Real.log X / Real.log (X * v)) / Real.sqrt v by ring]
  have hlam_pos : 0 < lam := by
    unfold lam
    positivity
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hX_pos : 0 < X := lt_trans zero_lt_one hX
  have hX_ne : X ≠ 0 := ne_of_gt hX_pos
  have hlogX_pos : 0 < Real.log X := Real.log_pos hX
  have hXv_pos : 0 < X * v := lt_trans zero_lt_one hXv
  have hlogXv_pos : 0 < Real.log (X * v) := Real.log_pos hXv
  have hlogXv_ne : Real.log (X * v) ≠ 0 := ne_of_gt hlogXv_pos
  have hv_ne : v ≠ 0 := ne_of_gt hv
  have hleft_nonneg : 0 ≤ X * Real.log X / (2 * lam) := by positivity
  calc
    Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v)
        = Real.sqrt (X * Real.log X / (2 * lam)) *
            Real.sqrt (2 * lam / ((X * v) * Real.log (X * v))) := by
          rfl
    _ = Real.sqrt ((X * Real.log X / (2 * lam)) *
            (2 * lam / ((X * v) * Real.log (X * v)))) := by
          rw [Real.sqrt_mul hleft_nonneg]
    _ = Real.sqrt ((Real.log X / Real.log (X * v)) / v) := by
          congr 1
          field_simp [hlam_ne, hX_ne, hv_ne, hlogXv_ne]
    _ = Real.sqrt (Real.log X / Real.log (X * v)) / Real.sqrt v := by
          have hratio_nonneg : 0 ≤ Real.log X / Real.log (X * v) := by positivity
          rw [Real.sqrt_div hratio_nonneg]

/-- Uniform model convergence of the normalized first-order profile away from zero. -/
theorem gNorm_model_uniform_away_bound
    {ε U η : ℝ} (hε : 0 < ε) (hεU : ε ≤ U) (hη : 0 < η) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ v ∈ Set.Icc ε U,
      |Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v) -
        (Real.sqrt v)⁻¹| ≤ η := by
  let c : ℝ := η * Real.sqrt ε
  have hc : 0 < c := by
    dsimp [c]
    positivity
  filter_upwards [log_div_log_mul_uniform_sub_one_le hε hεU hc,
      eventually_gt_atTop (1 : ℝ), eventually_gt_atTop (ε⁻¹)] with
    X hlog hX_gt_one hX_gt_inv v hv
  have hv_pos : 0 < v := lt_of_lt_of_le hε hv.1
  have hX_pos : 0 < X := lt_trans zero_lt_one hX_gt_one
  have hXε_gt_one : 1 < X * ε := by
    have hmul := mul_lt_mul_of_pos_right hX_gt_inv hε
    rwa [inv_mul_cancel₀ (ne_of_gt hε)] at hmul
  have hXv_gt : 1 < X * v := by
    have hXε_le_Xv : X * ε ≤ X * v :=
      mul_le_mul_of_nonneg_left hv.1 (le_of_lt hX_pos)
    exact lt_of_lt_of_le hXε_gt_one hXε_le_Xv
  have hmodel := gNorm_model_eq_inv_sqrt_mul_log_ratio hv_pos hX_gt_one hXv_gt
  rw [hmodel]
  let r : ℝ := Real.log X / Real.log (X * v)
  have hlogX_pos : 0 < Real.log X := Real.log_pos hX_gt_one
  have hlogXv_pos : 0 < Real.log (X * v) := Real.log_pos hXv_gt
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hsqrt_sub_le : |Real.sqrt r - 1| ≤ c :=
    le_trans (abs_sqrt_sub_one_le_abs_sub_one hr_nonneg) (hlog v hv)
  have hsqrtε_pos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hsqrtv_pos : 0 < Real.sqrt v := Real.sqrt_pos.2 hv_pos
  have hsqrtε_le_sqrtv : Real.sqrt ε ≤ Real.sqrt v :=
    Real.sqrt_le_sqrt hv.1
  have hinv_le : (Real.sqrt v)⁻¹ ≤ (Real.sqrt ε)⁻¹ := by
    exact (inv_le_inv₀ hsqrtv_pos hsqrtε_pos).2 hsqrtε_le_sqrtv
  have hinv_nonneg : 0 ≤ (Real.sqrt v)⁻¹ := le_of_lt (inv_pos.2 hsqrtv_pos)
  calc
    |Real.sqrt r * (Real.sqrt v)⁻¹ - (Real.sqrt v)⁻¹|
        = |Real.sqrt r - 1| * (Real.sqrt v)⁻¹ := by
          rw [show Real.sqrt r * (Real.sqrt v)⁻¹ - (Real.sqrt v)⁻¹ =
              (Real.sqrt r - 1) * (Real.sqrt v)⁻¹ by ring]
          rw [abs_mul, abs_of_pos (inv_pos.2 hsqrtv_pos)]
    _ ≤ c * (Real.sqrt ε)⁻¹ :=
          mul_le_mul hsqrt_sub_le hinv_le hinv_nonneg (le_of_lt hc)
    _ = η := by
          dsimp [c]
          field_simp [ne_of_gt hsqrtε_pos]

/-- Uniform relative error between `gNorm` and its first-order model away from zero. -/
theorem gNorm_sub_model_uniform_relative_bound
    (D : PhiPsiData B) {ε U η : ℝ} (hε : 0 < ε) (_hεU : ε ≤ U) (hη : 0 < η) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ v ∈ Set.Icc ε U,
      |gNorm D X v - Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v)|
        ≤ η * (Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v)) := by
  rcases Filter.eventually_atTop.mp (D.eventually_abs_f_sub_fModel_le hη) with ⟨T, hT⟩
  filter_upwards [eventually_ge_atTop (max 0 (T / ε))] with X hX v hv
  have hX_nonneg : 0 ≤ X := le_trans (le_max_left 0 (T / ε)) hX
  have hT_div_le : T / ε ≤ X := le_trans (le_max_right 0 (T / ε)) hX
  have hT_le_Xε : T ≤ X * ε := by
    have hmul := mul_le_mul_of_nonneg_right hT_div_le (le_of_lt hε)
    have hleft : T / ε * ε = T := by field_simp [ne_of_gt hε]
    have hright : ε * X = X * ε := by ring
    simpa [hleft, hright] using hmul
  have hXε_le_Xv : X * ε ≤ X * v :=
    mul_le_mul_of_nonneg_left hv.1 hX_nonneg
  have htail : T ≤ X * v := le_trans hT_le_Xε hXε_le_Xv
  have hf : |D.f (X * v) - fModel (X * v)| ≤ η * fModel (X * v) :=
    hT (X * v) htail
  have hscale_nonneg : 0 ≤ Real.sqrt (X * Real.log X / (2 * lam)) :=
    Real.sqrt_nonneg _
  have hdiff :
      gNorm D X v - Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v) =
        Real.sqrt (X * Real.log X / (2 * lam)) *
          (D.f (X * v) - fModel (X * v)) := by
    simp [gNorm]
    ring
  calc
    |gNorm D X v - Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v)|
        = Real.sqrt (X * Real.log X / (2 * lam)) *
            |D.f (X * v) - fModel (X * v)| := by
          rw [hdiff, abs_mul, abs_of_nonneg hscale_nonneg]
    _ ≤ Real.sqrt (X * Real.log X / (2 * lam)) * (η * fModel (X * v)) :=
          mul_le_mul_of_nonneg_left hf hscale_nonneg
    _ = η * (Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v)) := by
          ring

/-- The first-order normalized model is uniformly bounded on compact intervals away from zero. -/
theorem gNorm_model_uniform_cap
    {ε U : ℝ} (hε : 0 < ε) (hεU : ε ≤ U) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ v ∈ Set.Icc ε U,
      Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v) ≤
        Real.sqrt 2 * (Real.sqrt ε)⁻¹ := by
  filter_upwards [log_div_log_mul_uniform_sub_one_le hε hεU (by norm_num : (0 : ℝ) < 1),
      eventually_gt_atTop (max (1 : ℝ) (2 / ε))] with X hlog hX v hv
  have hv_pos : 0 < v := lt_of_lt_of_le hε hv.1
  have hX_gt_one : 1 < X := lt_of_le_of_lt (le_max_left (1 : ℝ) (2 / ε)) hX
  have hX_pos : 0 < X := lt_trans zero_lt_one hX_gt_one
  have htwo_div_lt : 2 / ε < X := lt_of_le_of_lt (le_max_right (1 : ℝ) (2 / ε)) hX
  have htwo_lt_Xε : 2 < X * ε := by
    have hmul := mul_lt_mul_of_pos_right htwo_div_lt hε
    have hleft : 2 / ε * ε = 2 := by field_simp [ne_of_gt hε]
    have hright : ε * X = X * ε := by ring
    simpa [hleft, hright] using hmul
  have hXv_gt : 1 < X * v := by
    have hXε_le_Xv : X * ε ≤ X * v :=
      mul_le_mul_of_nonneg_left hv.1 (le_of_lt hX_pos)
    exact lt_of_lt_of_le (by linarith : 1 < X * ε) hXε_le_Xv
  have hmodel := gNorm_model_eq_inv_sqrt_mul_log_ratio hv_pos hX_gt_one hXv_gt
  have hratio_le_two :
      Real.log X / Real.log (X * v) ≤ 2 := by
    have habs := hlog v hv
    have hupper := (abs_le.mp habs).2
    linarith
  have hsqrt_ratio :
      Real.sqrt (Real.log X / Real.log (X * v)) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt hratio_le_two
  have hsqrtε_pos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hsqrtv_pos : 0 < Real.sqrt v := Real.sqrt_pos.2 hv_pos
  have hsqrtε_le_sqrtv : Real.sqrt ε ≤ Real.sqrt v :=
    Real.sqrt_le_sqrt hv.1
  have hinv_le : (Real.sqrt v)⁻¹ ≤ (Real.sqrt ε)⁻¹ := by
    exact (inv_le_inv₀ hsqrtv_pos hsqrtε_pos).2 hsqrtε_le_sqrtv
  rw [hmodel]
  exact mul_le_mul hsqrt_ratio hinv_le
    (le_of_lt (inv_pos.2 hsqrtv_pos)) (Real.sqrt_nonneg 2)

/-- Uniform absolute error between `gNorm` and its first-order model away from zero. -/
theorem gNorm_sub_model_uniform_away_bound
    (D : PhiPsiData B) {ε U η : ℝ} (hε : 0 < ε) (hεU : ε ≤ U) (hη : 0 < η) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ v ∈ Set.Icc ε U,
      |gNorm D X v - Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v)| ≤ η := by
  let C : ℝ := Real.sqrt 2 * (Real.sqrt ε)⁻¹
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  let δ : ℝ := η / C
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  filter_upwards [gNorm_sub_model_uniform_relative_bound D hε hεU hδ_pos,
      gNorm_model_uniform_cap hε hεU] with X hrel hcap v hv
  calc
    |gNorm D X v - Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v)|
        ≤ δ * (Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v)) :=
          hrel v hv
    _ ≤ δ * C := mul_le_mul_of_nonneg_left (hcap v hv) (le_of_lt hδ_pos)
    _ = η := by
          dsimp [δ]
          field_simp [ne_of_gt hC_pos]

/-- Uniform convergence of `gNorm` away from the singular endpoint. -/
theorem gNorm_uniform_away_bound
    (D : PhiPsiData B) {ε U η : ℝ} (hε : 0 < ε) (hεU : ε ≤ U) (hη : 0 < η) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ v ∈ Set.Icc ε U,
      |gNorm D X v - (Real.sqrt v)⁻¹| ≤ η := by
  have hhalf_pos : 0 < η / 2 := by positivity
  filter_upwards [gNorm_sub_model_uniform_away_bound D hε hεU hhalf_pos,
      gNorm_model_uniform_away_bound hε hεU hhalf_pos] with X hf hmodel v hv
  have hsum :
      |gNorm D X v - (Real.sqrt v)⁻¹| ≤
        |gNorm D X v - Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v)| +
          |Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v) -
            (Real.sqrt v)⁻¹| := by
    have hdecomp :
        gNorm D X v - (Real.sqrt v)⁻¹ =
          (gNorm D X v - Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v)) +
            (Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v) -
              (Real.sqrt v)⁻¹) := by
      ring
    rw [hdecomp]
    exact abs_add_le _ _
  calc
    |gNorm D X v - (Real.sqrt v)⁻¹|
        ≤ |gNorm D X v - Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v)| +
          |Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v) -
            (Real.sqrt v)⁻¹| := hsum
    _ ≤ η / 2 + η / 2 := add_le_add (hf v hv) (hmodel v hv)
    _ = η := by ring

/-- Uniform convergence of `gNorm` on compact intervals away from the singular endpoint. -/
theorem gNorm_tendstoUniformlyOn_away
    (D : PhiPsiData B) {ε U : ℝ} (hε : 0 < ε) (hεU : ε ≤ U) :
    TendstoUniformlyOn
      (fun X v => gNorm D X v)
      (fun v => (Real.sqrt v)⁻¹)
      Filter.atTop
      (Set.Icc ε U) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have hhalf_pos : 0 < η / 2 := by positivity
  filter_upwards [gNorm_uniform_away_bound D hε hεU hhalf_pos] with X hX v hv
  rw [Real.dist_eq]
  have hle : |(Real.sqrt v)⁻¹ - gNorm D X v| ≤ η / 2 := by
    simpa [abs_sub_comm] using hX v hv
  linarith

/-- L¹ convergence of the normalized profile on fixed compact intervals from the singular
endpoint. -/
theorem gNorm_L1_convergence
    (D : PhiPsiData B) {U : ℝ} (hU : 0 ≤ U) :
    Tendsto (fun X : ℝ =>
      ∫ v in (0 : ℝ)..U, |gNorm D X v - (Real.sqrt v)⁻¹|)
      Filter.atTop (𝓝 0) := by
  by_cases hU_zero : U = 0
  · subst U
    simp
  · have hU_pos : 0 < U := lt_of_le_of_ne hU (Ne.symm hU_zero)
    rcases gNorm_small_v_L1_eventual_bound D with ⟨C, hC_pos, hsmall⟩
    rw [Metric.tendsto_atTop]
    intro η hη
    let δ : ℝ := min U ((η / (4 * C)) ^ 2)
    have hη_div_pos : 0 < η / (4 * C) := by positivity
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact lt_min hU_pos (sq_pos_of_pos hη_div_pos)
    have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
    have hδ_le_U : δ ≤ U := by
      dsimp [δ]
      exact min_le_left _ _
    have hδ_le_sq : δ ≤ (η / (4 * C)) ^ 2 := by
      dsimp [δ]
      exact min_le_right _ _
    have hsqrtδ_le : Real.sqrt δ ≤ η / (4 * C) := by
      calc
        Real.sqrt δ ≤ Real.sqrt ((η / (4 * C)) ^ 2) := Real.sqrt_le_sqrt hδ_le_sq
        _ = η / (4 * C) := by rw [Real.sqrt_sq (le_of_lt hη_div_pos)]
    have hsmall_quarter : C * Real.sqrt δ ≤ η / 4 := by
      calc
        C * Real.sqrt δ ≤ C * (η / (4 * C)) :=
          mul_le_mul_of_nonneg_left hsqrtδ_le (le_of_lt hC_pos)
        _ = η / 4 := by
          field_simp [ne_of_gt hC_pos]
    let α : ℝ := η / (4 * (U + 1))
    have hU1_pos : 0 < U + 1 := by linarith
    have hα_pos : 0 < α := by
      dsimp [α]
      positivity
    have haway_quarter : α * U ≤ η / 4 := by
      calc
        α * U ≤ α * (U + 1) :=
          mul_le_mul_of_nonneg_left (by linarith : U ≤ U + 1) (le_of_lt hα_pos)
        _ = η / 4 := by
          dsimp [α]
          field_simp [ne_of_gt hU1_pos]
    have hsmall_ev := hsmall hδ_nonneg
    have haway_ev := gNorm_uniform_away_bound D hδ_pos hδ_le_U hα_pos
    have hpos_ev : ∀ᶠ X : ℝ in Filter.atTop, 0 < X := eventually_gt_atTop (0 : ℝ)
    rcases Filter.eventually_atTop.mp (hsmall_ev.and (haway_ev.and hpos_ev)) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro X hXN
    rcases hN X hXN with ⟨hsmallX, hawayX, hX_pos⟩
    let err : ℝ → ℝ := fun v => |gNorm D X v - (Real.sqrt v)⁻¹|
    have hX_ne : X ≠ 0 := ne_of_gt hX_pos
    have herr0δ : IntervalIntegrable err MeasureTheory.volume (0 : ℝ) δ := by
      simpa [err] using gNorm_sub_inv_sqrt_abs_intervalIntegrable D hX_ne hδ_nonneg
    have herr0U : IntervalIntegrable err MeasureTheory.volume (0 : ℝ) U := by
      simpa [err] using gNorm_sub_inv_sqrt_abs_intervalIntegrable D hX_ne hU
    have hsubset : Set.uIcc δ U ⊆ Set.uIcc (0 : ℝ) U := by
      rw [Set.uIcc_of_le hδ_le_U, Set.uIcc_of_le hU]
      intro v hv
      exact ⟨le_trans hδ_nonneg hv.1, hv.2⟩
    have herrδU : IntervalIntegrable err MeasureTheory.volume δ U :=
      herr0U.mono_set hsubset
    have hconst_int : IntervalIntegrable (fun _ : ℝ => α) MeasureTheory.volume δ U :=
      intervalIntegral.intervalIntegrable_const
    have haway_int_le :
        ∫ v in δ..U, err v ≤ ∫ v in δ..U, α := by
      refine intervalIntegral.integral_mono_on hδ_le_U herrδU hconst_int ?_
      intro v hv
      exact hawayX v hv
    have haway_len : ∫ v in δ..U, err v ≤ α * U := by
      calc
        ∫ v in δ..U, err v ≤ ∫ v in δ..U, α := haway_int_le
        _ = α * (U - δ) := by
          rw [intervalIntegral.integral_const]
          ring
        _ ≤ α * U := by
          exact mul_le_mul_of_nonneg_left (by linarith : U - δ ≤ U) (le_of_lt hα_pos)
    have hsplit :
        (∫ v in (0 : ℝ)..δ, err v) + (∫ v in δ..U, err v) =
          ∫ v in (0 : ℝ)..U, err v :=
      intervalIntegral.integral_add_adjacent_intervals herr0δ herrδU
    have htotal_le : ∫ v in (0 : ℝ)..U, err v ≤ η / 2 := by
      calc
        ∫ v in (0 : ℝ)..U, err v =
            (∫ v in (0 : ℝ)..δ, err v) + ∫ v in δ..U, err v := by
              rw [← hsplit]
        _ ≤ C * Real.sqrt δ + α * U := add_le_add hsmallX haway_len
        _ ≤ η / 4 + η / 4 := add_le_add hsmall_quarter haway_quarter
        _ = η / 2 := by ring
    have hnonneg : 0 ≤ ∫ v in (0 : ℝ)..U, err v := by
      refine intervalIntegral.integral_nonneg hU ?_
      intro v _hv
      exact abs_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    exact lt_of_le_of_lt htotal_le (by linarith)

/-- A window integral of a nonnegative absolute value is bounded by the global L¹ norm. -/
theorem window_abs_integral_le_global_L1
    {f : ℝ → ℝ} {U u : ℝ}
    (hu : u ∈ Set.Icc (1 : ℝ) U)
    (hf : IntervalIntegrable (fun v : ℝ => |f v|)
      MeasureTheory.volume (0 : ℝ) U) :
    ∫ v in (u - 1)..u, |f v| ≤ ∫ v in (0 : ℝ)..U, |f v| := by
  have h0_le : 0 ≤ u - 1 := by linarith [hu.1]
  have hwin : u - 1 ≤ u := by linarith
  exact intervalIntegral.integral_mono_interval h0_le hwin hu.2
    (Eventually.of_forall (fun x => abs_nonneg (f x))) hf

/-- The absolute value of a window integral is bounded by the global L¹ norm. -/
theorem abs_window_integral_le_global_L1
    {f : ℝ → ℝ} {U u : ℝ}
    (hu : u ∈ Set.Icc (1 : ℝ) U)
    (hf_abs_global : IntervalIntegrable (fun v : ℝ => |f v|)
      MeasureTheory.volume (0 : ℝ) U) :
    |∫ v in (u - 1)..u, f v| ≤ ∫ v in (0 : ℝ)..U, |f v| := by
  have hwin : u - 1 ≤ u := by linarith [hu.1]
  calc
    |∫ v in (u - 1)..u, f v| ≤ ∫ v in (u - 1)..u, |f v| :=
      intervalIntegral.abs_integral_le_integral_abs hwin
    _ ≤ ∫ v in (0 : ℝ)..U, |f v| :=
      window_abs_integral_le_global_L1 hu hf_abs_global

/-- Absolute-value form of the exact singular-profile integral on `[0,U]`. -/
theorem inv_sqrt_abs_integral_zero_eq {U : ℝ} (hU : 0 ≤ U) :
    ∫ v in (0 : ℝ)..U, |(Real.sqrt v)⁻¹| = 2 * Real.sqrt U := by
  have hcongr :
      ∫ v in (0 : ℝ)..U, |(Real.sqrt v)⁻¹| =
        ∫ v in (0 : ℝ)..U, (Real.sqrt v)⁻¹ := by
    refine intervalIntegral.integral_congr ?_
    intro v _hv
    change |(Real.sqrt v)⁻¹| = (Real.sqrt v)⁻¹
    exact abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg v))
  rw [hcongr, integral_inv_sqrt_zero_eq hU]

/-- Pointwise error bound for the normalized correction operator on a fixed interval. -/
theorem corrOperator_pointwise_error_bound
    (D : PhiPsiData B) {U X η L u : ℝ}
    (hU : 1 ≤ U) (hX_ne : X ≠ 0) (hη_nonneg : 0 ≤ η) (hη_le_one : η ≤ 1)
    (hL1 : ∫ v in (0 : ℝ)..U, |gNorm D X v - (Real.sqrt v)⁻¹| ≤ L)
    (hu : u ∈ Set.Icc (1 : ℝ) U)
    (haway : ∀ v ∈ Set.Icc (1 : ℝ) U,
      |gNorm D X v - (Real.sqrt v)⁻¹| ≤ η) :
    |gNorm D X u *
        (∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u)) - corrKernel u| ≤
      (2 * Real.sqrt U + 3) * η + 2 * L := by
  let g : ℝ → ℝ := fun v => (Real.sqrt v)⁻¹
  let e : ℝ → ℝ := fun v => gNorm D X v - g v
  let innerX : ℝ := ∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u)
  let innerG : ℝ := ∫ v in (u - 1)..u, (g v - g u)
  have hU_nonneg : 0 ≤ U := le_trans zero_le_one hU
  have hu_nonneg : 0 ≤ u := le_trans zero_le_one hu.1
  have hum1_nonneg : 0 ≤ u - 1 := sub_nonneg.mpr hu.1
  have hum1_le : u - 1 ≤ u := by linarith
  have hg_win : IntervalIntegrable g MeasureTheory.volume (u - 1) u := by
    have hg0u : IntervalIntegrable g MeasureTheory.volume (0 : ℝ) u := by
      simpa [g] using inv_sqrt_intervalIntegrable_zero hu_nonneg
    refine hg0u.mono_set ?_
    rw [Set.uIcc_of_le hum1_le, Set.uIcc_of_le hu_nonneg]
    intro v hv
    exact ⟨le_trans hum1_nonneg hv.1, hv.2⟩
  have hg_const : IntervalIntegrable (fun _v : ℝ => g u) MeasureTheory.volume (u - 1) u :=
    intervalIntegral.intervalIntegrable_const
  have hg_abs_global : IntervalIntegrable (fun v : ℝ => |g v|) MeasureTheory.volume (0 : ℝ) U := by
    simpa [g] using (inv_sqrt_intervalIntegrable_zero hU_nonneg).abs
  have he_abs_global : IntervalIntegrable (fun v : ℝ => |e v|) MeasureTheory.volume (0 : ℝ) U := by
    simpa [e, g] using gNorm_sub_inv_sqrt_abs_intervalIntegrable D hX_ne hU_nonneg
  have hsqrtu_one : 1 ≤ Real.sqrt u := by
    have hs := Real.sqrt_le_sqrt hu.1
    simpa using hs
  have hgu_nonneg : 0 ≤ g u := by
    dsimp [g]
    exact inv_nonneg.mpr (Real.sqrt_nonneg u)
  have hgu_le_one : g u ≤ 1 := by
    dsimp [g]
    exact inv_le_one_of_one_le₀ hsqrtu_one
  have hgu_abs_le_one : |g u| ≤ 1 := by
    rw [abs_of_nonneg hgu_nonneg]
    exact hgu_le_one
  have hglobal_nonneg : 0 ≤ ∫ v in (0 : ℝ)..U, |e v| := by
    refine intervalIntegral.integral_nonneg hU_nonneg ?_
    intro v _hv
    exact abs_nonneg _
  have hL_nonneg : 0 ≤ L := le_trans hglobal_nonneg (by simpa [e, g] using hL1)
  have haway_u : |e u| ≤ η := by simpa [e, g] using haway u hu
  have hgX_abs_le_two : |gNorm D X u| ≤ 2 := by
    calc
      |gNorm D X u| = |e u + g u| := by
        congr 1
        dsimp [e, g]
        ring
      _ ≤ |e u| + |g u| := abs_add_le _ _
      _ ≤ η + 1 := add_le_add haway_u hgu_abs_le_one
      _ ≤ 2 := by linarith
  have hinnerG_abs : |innerG| ≤ 2 * Real.sqrt U + 1 := by
    have hinnerG_rw : innerG =
        (∫ v in (u - 1)..u, g v) - ∫ v in (u - 1)..u, g u := by
      dsimp [innerG]
      rw [intervalIntegral.integral_sub hg_win hg_const]
    rw [hinnerG_rw]
    have hwin_g_abs : |∫ v in (u - 1)..u, g v| ≤ ∫ v in (0 : ℝ)..U, |g v| :=
      abs_window_integral_le_global_L1 hu hg_abs_global
    have hglobal_g : ∫ v in (0 : ℝ)..U, |g v| = 2 * Real.sqrt U := by
      simpa [g] using inv_sqrt_abs_integral_zero_eq hU_nonneg
    have hconst_abs : |∫ v in (u - 1)..u, g u| ≤ 1 := by
      rw [intervalIntegral.integral_const]
      ring_nf
      rw [abs_of_nonneg hgu_nonneg]
      exact hgu_le_one
    have hsub_abs : |(∫ v in (u - 1)..u, g v) - ∫ v in (u - 1)..u, g u| ≤
        |∫ v in (u - 1)..u, g v| + |∫ v in (u - 1)..u, g u| := by
      simpa [sub_eq_add_neg] using
        (abs_add_le (∫ v in (u - 1)..u, g v) (-(∫ v in (u - 1)..u, g u)))
    calc
      |(∫ v in (u - 1)..u, g v) - ∫ v in (u - 1)..u, g u| ≤
          |∫ v in (u - 1)..u, g v| + |∫ v in (u - 1)..u, g u| := hsub_abs
      _ ≤ (∫ v in (0 : ℝ)..U, |g v|) + 1 := add_le_add hwin_g_abs hconst_abs
      _ = 2 * Real.sqrt U + 1 := by rw [hglobal_g]
  have hinner_diff_abs : |innerX - innerG| ≤ L + η := by
    have hgX_win : IntervalIntegrable (fun v : ℝ => gNorm D X v) MeasureTheory.volume (u - 1) u :=
      gNorm_intervalIntegrable D hX_ne
    have hgX_const : IntervalIntegrable (fun _v : ℝ => gNorm D X u)
        MeasureTheory.volume (u - 1) u :=
      intervalIntegral.intervalIntegrable_const
    have hIX : IntervalIntegrable (fun v : ℝ => gNorm D X v - gNorm D X u)
        MeasureTheory.volume (u - 1) u :=
      hgX_win.sub hgX_const
    have hIG : IntervalIntegrable (fun v : ℝ => g v - g u)
        MeasureTheory.volume (u - 1) u :=
      hg_win.sub hg_const
    have he_win : IntervalIntegrable e MeasureTheory.volume (u - 1) u := by
      simpa [e, g] using hgX_win.sub hg_win
    have he_const : IntervalIntegrable (fun _v : ℝ => e u) MeasureTheory.volume (u - 1) u :=
      intervalIntegral.intervalIntegrable_const
    have hdiff_eq : innerX - innerG = ∫ v in (u - 1)..u, (e v - e u) := by
      dsimp [innerX, innerG]
      rw [← intervalIntegral.integral_sub hIX hIG]
      refine intervalIntegral.integral_congr ?_
      intro v _hv
      dsimp [e, g]
      ring
    rw [hdiff_eq]
    rw [intervalIntegral.integral_sub he_win he_const]
    have hwin_e_abs : |∫ v in (u - 1)..u, e v| ≤ ∫ v in (0 : ℝ)..U, |e v| :=
      abs_window_integral_le_global_L1 hu he_abs_global
    have hconst_e_abs : |∫ v in (u - 1)..u, e u| ≤ η := by
      rw [intervalIntegral.integral_const]
      ring_nf
      exact haway_u
    have hsub_abs : |(∫ v in (u - 1)..u, e v) - ∫ v in (u - 1)..u, e u| ≤
        |∫ v in (u - 1)..u, e v| + |∫ v in (u - 1)..u, e u| := by
      simpa [sub_eq_add_neg] using
        (abs_add_le (∫ v in (u - 1)..u, e v) (-(∫ v in (u - 1)..u, e u)))
    calc
      |(∫ v in (u - 1)..u, e v) - ∫ v in (u - 1)..u, e u| ≤
          |∫ v in (u - 1)..u, e v| + |∫ v in (u - 1)..u, e u| := hsub_abs
      _ ≤ (∫ v in (0 : ℝ)..U, |e v|) + η := add_le_add hwin_e_abs hconst_e_abs
      _ ≤ L + η := add_le_add (by simpa [e, g] using hL1) le_rfl
  rw [← corr_limit_integrand_eq_corrKernel hu.1]
  change |gNorm D X u * innerX - g u * innerG| ≤ (2 * Real.sqrt U + 3) * η + 2 * L
  have hdecomp : gNorm D X u * innerX - g u * innerG =
      e u * innerG + gNorm D X u * (innerX - innerG) := by
    dsimp [e, g, innerX, innerG]
    ring
  rw [hdecomp]
  calc
    |e u * innerG + gNorm D X u * (innerX - innerG)| ≤
        |e u * innerG| + |gNorm D X u * (innerX - innerG)| := abs_add_le _ _
    _ = |e u| * |innerG| + |gNorm D X u| * |innerX - innerG| := by
      rw [abs_mul, abs_mul]
    _ ≤ η * (2 * Real.sqrt U + 1) + 2 * (L + η) := by
      refine add_le_add ?_ ?_
      · exact mul_le_mul haway_u hinnerG_abs (abs_nonneg _) hη_nonneg
      · exact mul_le_mul hgX_abs_le_two hinner_diff_abs (abs_nonneg _) (by norm_num)
    _ = (2 * Real.sqrt U + 3) * η + 2 * L := by ring

/-- Fixed-`U` L¹ convergence of the normalized correction operator. -/
theorem corrOperator_L1_convergence_fixed_U
    (D : PhiPsiData B) {U : ℝ} (hU : 1 ≤ U) :
    Tendsto (fun X : ℝ =>
      ∫ u in (1 : ℝ)..U,
        |gNorm D X u *
            (∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u)) -
          corrKernel u|)
      Filter.atTop (𝓝 0) := by
  let C : ℝ := 2 * Real.sqrt U + 3
  have hU_nonneg : 0 ≤ U := le_trans zero_le_one hU
  have hU1_pos : 0 < U + 1 := by linarith
  have hC2_pos : 0 < C + 2 := by
    dsimp [C]
    positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  let α : ℝ := min 1 (ε / (4 * (C + 2) * (U + 1)))
  have hfrac_pos : 0 < ε / (4 * (C + 2) * (U + 1)) := by positivity
  have hα_pos : 0 < α := by
    dsimp [α]
    exact lt_min zero_lt_one hfrac_pos
  have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
  have hα_le_one : α ≤ 1 := by
    dsimp [α]
    exact min_le_left _ _
  have hα_le_frac : α ≤ ε / (4 * (C + 2) * (U + 1)) := by
    dsimp [α]
    exact min_le_right _ _
  have haway_ev := gNorm_uniform_away_bound D zero_lt_one hU hα_pos
  have hL_tend := gNorm_L1_convergence D hU_nonneg
  have hL_ev : ∀ᶠ X : ℝ in Filter.atTop,
      ∫ v in (0 : ℝ)..U, |gNorm D X v - (Real.sqrt v)⁻¹| ≤ α := by
    rw [Metric.tendsto_atTop] at hL_tend
    rcases hL_tend α hα_pos with ⟨N, hN⟩
    refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
    intro X hXN
    have hdist := hN X hXN
    rw [Real.dist_eq, sub_zero] at hdist
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hdist)
  have hpos_ev : ∀ᶠ X : ℝ in Filter.atTop, 0 < X := eventually_gt_atTop (0 : ℝ)
  rcases Filter.eventually_atTop.mp (haway_ev.and (hL_ev.and hpos_ev)) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro X hXN
  rcases hN X hXN with ⟨hawayX, hLX, hX_pos⟩
  let Lx : ℝ := ∫ v in (0 : ℝ)..U, |gNorm D X v - (Real.sqrt v)⁻¹|
  have hX_ne : X ≠ 0 := ne_of_gt hX_pos
  have hLx_le : Lx ≤ α := by simpa [Lx] using hLX
  have hpoint : ∀ u ∈ Set.uIoc (1 : ℝ) U,
      ‖|gNorm D X u *
          (∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u)) - corrKernel u|‖ ≤
        (C + 2) * α := by
    intro u huI
    have huIcc : u ∈ Set.Icc (1 : ℝ) U := by
      rw [Set.uIoc_of_le hU] at huI
      exact ⟨le_of_lt huI.1, huI.2⟩
    have hp := corrOperator_pointwise_error_bound D hU hX_ne hα_nonneg hα_le_one
      (L := Lx) (show ∫ v in (0 : ℝ)..U,
        |gNorm D X v - (Real.sqrt v)⁻¹| ≤ Lx from le_rfl) huIcc hawayX
    have hbound : (2 * Real.sqrt U + 3) * α + 2 * Lx ≤ (C + 2) * α := by
      calc
        (2 * Real.sqrt U + 3) * α + 2 * Lx ≤
            (2 * Real.sqrt U + 3) * α + 2 * α := by
              exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hLx_le (by norm_num))
        _ = (C + 2) * α := by
              dsimp [C]
              ring
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact le_trans hp hbound
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 : ℝ)) (b := U) (C := (C + 2) * α) hpoint
  have hnorm_abs :
      |(∫ u in (1 : ℝ)..U,
        |gNorm D X u *
            (∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u)) - corrKernel u|)| ≤
        ((C + 2) * α) * |U - 1| := by
    simpa [Real.norm_eq_abs] using hnorm
  have hlen_le : |U - 1| ≤ U + 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hU)]
    linarith
  have hconst_nonneg : 0 ≤ (C + 2) * α := mul_nonneg (le_of_lt hC2_pos) hα_nonneg
  have hsmall : ((C + 2) * α) * |U - 1| < ε := by
    calc
      ((C + 2) * α) * |U - 1| ≤ ((C + 2) * α) * (U + 1) :=
        mul_le_mul_of_nonneg_left hlen_le hconst_nonneg
      _ = (C + 2) * α * (U + 1) := by ring
      _ ≤ (C + 2) * (ε / (4 * (C + 2) * (U + 1))) * (U + 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hα_le_frac (le_of_lt hC2_pos)) (le_of_lt hU1_pos)
      _ = ε / 4 := by
        field_simp [ne_of_gt hC2_pos, ne_of_gt hU1_pos]
      _ < ε := by linarith
  rw [Real.dist_eq, sub_zero]
  exact lt_of_le_of_lt hnorm_abs hsmall

/-- The correction kernel is interval-integrable on every ordered fixed tail interval. -/
theorem corrKernel_intervalIntegrable_of_one_le {U : ℝ} (hU : 1 ≤ U) :
    IntervalIntegrable corrKernel MeasureTheory.volume (1 : ℝ) U := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hU]
  change ContinuousOn (fun u : ℝ => 2 * (1 - √(1 - 1 / u)) - 1 / u)
    (Set.Icc (1 : ℝ) U)
  have hdiv : ContinuousOn (fun u : ℝ => (1 : ℝ) / u) (Set.Icc (1 : ℝ) U) := by
    exact continuousOn_const.div continuousOn_id (by
      intro u hu
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1))
  have hsqrt : ContinuousOn (fun u : ℝ => Real.sqrt (1 - 1 / u))
      (Set.Icc (1 : ℝ) U) := by
    exact (continuousOn_const.sub hdiv).sqrt
  have hleft :
      ContinuousOn (fun u : ℝ => (2 : ℝ) * (1 - Real.sqrt (1 - 1 / u)))
        (Set.Icc (1 : ℝ) U) := by
    exact continuousOn_const.mul (continuousOn_const.sub hsqrt)
  exact hleft.sub hdiv

/-- The normalized pointwise model tends to the limiting profile. -/
theorem gNorm_model_tendsto_inv_sqrt {v : ℝ} (hv : 0 < v) :
    Tendsto (fun X : ℝ => Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v))
      Filter.atTop (𝓝 ((Real.sqrt v)⁻¹)) := by
  have hratio :
      Tendsto (fun X : ℝ => Real.log X / Real.log (X * v)) Filter.atTop (𝓝 (1 : ℝ)) :=
    log_div_log_mul_const_tendsto_one hv
  have hsqrt : Tendsto (fun X : ℝ => Real.sqrt (Real.log X / Real.log (X * v)))
      Filter.atTop (𝓝 (Real.sqrt (1 : ℝ))) :=
    hratio.sqrt
  have hprod :
      Tendsto (fun X : ℝ =>
        Real.sqrt (Real.log X / Real.log (X * v)) * (Real.sqrt v)⁻¹)
        Filter.atTop (𝓝 (Real.sqrt (1 : ℝ) * (Real.sqrt v)⁻¹)) :=
    hsqrt.mul tendsto_const_nhds
  have hXv : Tendsto (fun X : ℝ => X * v) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hv tendsto_id
  have hEq :
      (fun X : ℝ => Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v))
        =ᶠ[Filter.atTop]
          fun X : ℝ => Real.sqrt (Real.log X / Real.log (X * v)) * (Real.sqrt v)⁻¹ := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hXv.eventually_gt_atTop (1 : ℝ)] with
      X hX hXv_gt
    exact gNorm_model_eq_inv_sqrt_mul_log_ratio hv hX hXv_gt
  have htarget :
      Tendsto (fun X : ℝ => Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v))
        Filter.atTop (𝓝 (Real.sqrt (1 : ℝ) * (Real.sqrt v)⁻¹)) :=
    hprod.congr' hEq.symm
  simpa using htarget

/-- Pointwise convergence of the normalized correction profile at every fixed `v > 0`. -/
theorem gNorm_tendsto_inv_sqrt (D : PhiPsiData B) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun X : ℝ => gNorm D X v) Filter.atTop (𝓝 ((Real.sqrt v)⁻¹)) := by
  have hXv : Tendsto (fun X : ℝ => X * v) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hv tendsto_id
  have hfcomp : (fun X : ℝ => D.f (X * v)) ~[Filter.atTop]
      fun X : ℝ => fModel (X * v) := by
    simpa [Function.comp_def] using D.f_asymptotic.comp_tendsto hXv
  have hscale : (fun X : ℝ => Real.sqrt (X * Real.log X / (2 * lam))) ~[Filter.atTop]
      fun X : ℝ => Real.sqrt (X * Real.log X / (2 * lam)) :=
    IsEquivalent.refl
  have hgnorm_equiv : (fun X : ℝ => gNorm D X v) ~[Filter.atTop]
      fun X : ℝ => Real.sqrt (X * Real.log X / (2 * lam)) * fModel (X * v) := by
    simpa [gNorm] using hscale.mul hfcomp
  exact hgnorm_equiv.symm.tendsto_nhds (gNorm_model_tendsto_inv_sqrt hv)

/-- Logarithmic parametrization of `PhiFormula`, used in the square substitution. -/
noncomputable def PhiLog (B w : ℝ) : ℝ :=
  PhiFormula B (Real.exp w)

/-- The half-square contribution to the continuous majorant. -/
theorem half_square_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      (1 / 2 : ℝ) * (I D X) ^ 2 - 4 * lam * X / Real.log X)
      =o[Filter.atTop] scaleReal := by
  have hI : (fun X : ℝ => I D X) ~[Filter.atTop] IModel :=
    integral_f_isEquivalent_IModel D
  have hsq :
      (fun X : ℝ => (1 / 2 : ℝ) * (I D X) ^ 2) ~[Filter.atTop]
        fun X : ℝ => (1 / 2 : ℝ) * (IModel X) ^ 2 := by
    have hmul : (fun X : ℝ => I D X * I D X) ~[Filter.atTop]
        fun X : ℝ => IModel X * IModel X := hI.mul hI
    have hconst :
        (fun _X : ℝ => (1 / 2 : ℝ)) ~[Filter.atTop]
          fun _X : ℝ => (1 / 2 : ℝ) := IsEquivalent.refl
    simpa [pow_two] using hconst.mul hmul
  have hmodel_eq :
      (fun X : ℝ => (1 / 2 : ℝ) * (IModel X) ^ 2) =ᶠ[Filter.atTop]
        fun X : ℝ => 4 * lam * scaleReal X := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hX_pos : 0 < X := lt_trans zero_lt_one hX
    have hlog_pos : 0 < Real.log X := Real.log_pos hX
    have harg_nonneg : 0 ≤ 2 * lam * X / Real.log X := by
      have hlam : 0 < lam := by
        unfold lam
        positivity
      positivity
    calc
      (1 / 2 : ℝ) * (IModel X) ^ 2 =
          (1 / 2 : ℝ) * (2 * Real.sqrt (2 * lam * X / Real.log X)) ^ 2 := by
        rfl
      _ = (1 / 2 : ℝ) * (4 * (2 * lam * X / Real.log X)) := by
        rw [show (2 * Real.sqrt (2 * lam * X / Real.log X)) ^ 2 =
            4 * (Real.sqrt (2 * lam * X / Real.log X)) ^ 2 by ring]
        rw [Real.sq_sqrt harg_nonneg]
      _ = 4 * lam * scaleReal X := by
        rw [scaleReal]
        field_simp [ne_of_gt hlog_pos]
  have hmain_equiv :
      (fun X : ℝ => (1 / 2 : ℝ) * (I D X) ^ 2) ~[Filter.atTop]
        fun X : ℝ => 4 * lam * scaleReal X :=
    hsq.congr_right hmodel_eq
  have hsmall :
      (fun X : ℝ =>
        (1 / 2 : ℝ) * (I D X) ^ 2 - 4 * lam * scaleReal X)
        =o[Filter.atTop] fun X : ℝ => 4 * lam * scaleReal X := by
    simpa using hmain_equiv.isLittleO
  refine hsmall.of_const_mul_right.congr' ?_ (EventuallyEq.rfl)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hlog_pos : 0 < Real.log X := Real.log_pos hX
  rw [scaleReal]
  field_simp [ne_of_gt hlog_pos]

/-- Exact algebraic split of `GX` into its constant part plus a correction. -/
theorem GX_eq_X_mul_f_add_correction
    (D : PhiPsiData B) (X t : ℝ) :
    GX D X t =
      X * D.f t + ∫ s in (t - X)..t, (D.f s - D.f t) := by
  have hf : IntervalIntegrable D.f MeasureTheory.volume (t - X) t :=
    D.f_intervalIntegrable (t - X) t
  have hconst :
      IntervalIntegrable (fun _s : ℝ => D.f t) MeasureTheory.volume (t - X) t :=
    intervalIntegral.intervalIntegrable_const
  unfold GX
  rw [intervalIntegral.integral_sub hf hconst]
  rw [intervalIntegral.integral_const]
  ring

/-- Square integrability of `f` on nonnegative ordered intervals. -/
theorem f_sq_intervalIntegrable_of_nonneg
    (D : PhiPsiData B) {X Y : ℝ}
    (hX : 0 ≤ X) (hXY : X ≤ Y) :
    IntervalIntegrable (fun t : ℝ => (D.f t) ^ 2)
      MeasureTheory.volume X Y := by
  refine AntitoneOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hXY]
  intro x hx y hy hxy
  have hx_nonneg : 0 ≤ x := hX.trans hx.1
  have hy_nonneg : 0 ≤ y := hX.trans hy.1
  have hf_anti : D.f y ≤ D.f x :=
    D.f_antitone hx_nonneg hy_nonneg hxy
  have hfy_nonneg : 0 ≤ D.f y := D.f_nonneg hy_nonneg
  have hfx_nonneg : 0 ≤ D.f x := D.f_nonneg hx_nonneg
  exact (sq_le_sq₀ hfy_nonneg hfx_nonneg).2 hf_anti

/-- Correction-integrand integrability, derived from the `GX` product and `f²` integrability. -/
theorem Rcorr_integrand_intervalIntegrable_of_nonneg
    (D : PhiPsiData B) {X Y : ℝ}
    (hX : 0 ≤ X) (hXY : X ≤ Y) :
    IntervalIntegrable
      (fun t : ℝ => D.f t * ∫ s in (t - X)..t, (D.f s - D.f t))
      MeasureTheory.volume X Y := by
  have hGX : IntervalIntegrable (fun t : ℝ => D.f t * GX D X t)
      MeasureTheory.volume X Y :=
    f_mul_GX_intervalIntegrable D hX hXY
  have hsq : IntervalIntegrable (fun t : ℝ => (D.f t) ^ 2)
      MeasureTheory.volume X Y :=
    f_sq_intervalIntegrable_of_nonneg D hX hXY
  have hscaled : IntervalIntegrable (fun t : ℝ => X * (D.f t) ^ 2)
      MeasureTheory.volume X Y :=
    hsq.const_mul X
  have hsub : IntervalIntegrable
      (fun t : ℝ => D.f t * GX D X t - X * (D.f t) ^ 2)
      MeasureTheory.volume X Y :=
    hGX.sub hscaled
  refine hsub.congr ?_
  intro t _ht
  change D.f t * GX D X t - X * (D.f t) ^ 2 =
    D.f t * ∫ s in (t - X)..t, (D.f s - D.f t)
  rw [GX_eq_X_mul_f_add_correction D X t]
  ring

/-- The inner correction integral is nonnegative once the whole window lies in the nonnegative
tail. -/
theorem Rcorr_inner_nonneg_of_le
    (D : PhiPsiData B) {X t : ℝ}
    (hX : 0 ≤ X) (hXt : X ≤ t) :
    0 ≤ ∫ s in (t - X)..t, (D.f s - D.f t) := by
  have ht_nonneg : 0 ≤ t := hX.trans hXt
  have hleft_nonneg : 0 ≤ t - X := sub_nonneg.mpr hXt
  have hleft_le : t - X ≤ t := by linarith
  have hf_int : IntervalIntegrable D.f MeasureTheory.volume (t - X) t :=
    D.f_intervalIntegrable (t - X) t
  have hconst_int :
      IntervalIntegrable (fun _s : ℝ => D.f t) MeasureTheory.volume (t - X) t :=
    intervalIntegral.intervalIntegrable_const
  have hdiff_int :
      IntervalIntegrable (fun s : ℝ => D.f s - D.f t)
        MeasureTheory.volume (t - X) t :=
    hf_int.sub hconst_int
  exact intervalIntegral.integral_nonneg hleft_le (fun s hs => by
    have hs_nonneg : 0 ≤ s := hleft_nonneg.trans hs.1
    have hmono : D.f t ≤ D.f s := D.f_antitone hs_nonneg ht_nonneg hs.2
    linarith)

/-- Pointwise nonnegativity of the correction integrand on nonnegative tail windows. -/
theorem Rcorr_integrand_nonneg_of_le
    (D : PhiPsiData B) {X t : ℝ}
    (hX : 0 ≤ X) (hXt : X ≤ t) :
    0 ≤ D.f t * ∫ s in (t - X)..t, (D.f s - D.f t) := by
  have ht_nonneg : 0 ≤ t := hX.trans hXt
  exact mul_nonneg (D.f_nonneg ht_nonneg) (Rcorr_inner_nonneg_of_le D hX hXt)

/-- Tail-interval integrability for the correction integrand.  The inner window parameter remains
`X`; this is why the proof restricts the full `X..Phi X` integrability result. -/
theorem Rcorr_tail_integrand_intervalIntegrable_of_order
    (D : PhiPsiData B) {X U : ℝ}
    (hX : 0 ≤ X) (hXUX : X ≤ U * X) (hUXPhi : U * X ≤ D.Phi X) :
    IntervalIntegrable
      (fun t : ℝ => D.f t * ∫ s in (t - X)..t, (D.f s - D.f t))
      MeasureTheory.volume (U * X) (D.Phi X) := by
  have hXPhi : X ≤ D.Phi X := hXUX.trans hUXPhi
  have hfull :
      IntervalIntegrable
        (fun t : ℝ => D.f t * ∫ s in (t - X)..t, (D.f s - D.f t))
        MeasureTheory.volume X (D.Phi X) :=
    Rcorr_integrand_intervalIntegrable_of_nonneg D hX hXPhi
  exact hfull.mono_set (by
    rw [Set.uIcc_of_le hUXPhi, Set.uIcc_of_le hXPhi]
    intro t ht
    exact ⟨hXUX.trans ht.1, ht.2⟩)

/-- Exact subtraction of the fixed-multiple truncation leaves the correction tail. -/
theorem Rcorr_sub_RcorrTrunc_eq_tail
    (D : PhiPsiData B) {X U : ℝ}
    (hX : 0 ≤ X) (hXUX : X ≤ U * X) (hUXPhi : U * X ≤ D.Phi X) :
    Rcorr D X - RcorrTrunc D X U =
      ∫ t in (U * X)..D.Phi X,
        D.f t * ∫ s in (t - X)..t, (D.f s - D.f t) := by
  let F : ℝ → ℝ := fun t =>
    D.f t * ∫ s in (t - X)..t, (D.f s - D.f t)
  have hXPhi : X ≤ D.Phi X := hXUX.trans hUXPhi
  have htrunc : IntervalIntegrable F MeasureTheory.volume X (U * X) := by
    simpa [F] using Rcorr_integrand_intervalIntegrable_of_nonneg D hX hXUX
  have htail : IntervalIntegrable F MeasureTheory.volume (U * X) (D.Phi X) := by
    simpa [F] using Rcorr_tail_integrand_intervalIntegrable_of_order D hX hXUX hUXPhi
  have hsplit :
      (∫ t in X..(U * X), F t) +
          ∫ t in (U * X)..D.Phi X, F t =
        ∫ t in X..D.Phi X, F t :=
    intervalIntegral.integral_add_adjacent_intervals htrunc htail
  rw [Rcorr, RcorrTrunc]
  change (∫ t in X..D.Phi X, F t) - (∫ t in X..(U * X), F t) =
    ∫ t in (U * X)..D.Phi X, F t
  rw [← hsplit]
  ring

/-- Nonnegativity of the correction tail on an ordered nonnegative truncation interval. -/
theorem Rcorr_tail_integral_nonneg_of_order
    (D : PhiPsiData B) {X U : ℝ}
    (hX : 0 ≤ X) (hXUX : X ≤ U * X) (hUXPhi : U * X ≤ D.Phi X) :
    0 ≤ ∫ t in (U * X)..D.Phi X,
      D.f t * ∫ s in (t - X)..t, (D.f s - D.f t) := by
  exact intervalIntegral.integral_nonneg hUXPhi (fun t ht => by
    exact Rcorr_integrand_nonneg_of_le D hX (hXUX.trans ht.1))

/-- Nonnegativity of `Rcorr - RcorrTrunc` under the same ordered-tail hypotheses. -/
theorem Rcorr_sub_RcorrTrunc_nonneg_of_order
    (D : PhiPsiData B) {X U : ℝ}
    (hX : 0 ≤ X) (hXUX : X ≤ U * X) (hUXPhi : U * X ≤ D.Phi X) :
    0 ≤ Rcorr D X - RcorrTrunc D X U := by
  rw [Rcorr_sub_RcorrTrunc_eq_tail D hX hXUX hUXPhi]
  exact Rcorr_tail_integral_nonneg_of_order D hX hXUX hUXPhi

/-- Integrability of `t ↦ 1/t²` on positive ordered intervals. -/
theorem one_div_sq_intervalIntegrable_of_pos {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (1 / t ^ 2 : ℝ)) MeasureTheory.volume a b := by
  have hnot : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h0
    exact (not_lt_of_ge h0.1) ha
  have hz : IntervalIntegrable (fun t : ℝ => t ^ (-2 : ℤ)) MeasureTheory.volume a b :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr hnot)
  refine hz.congr ?_
  intro t ht
  have ht_uIcc : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
  rw [Set.uIcc_of_le hab] at ht_uIcc
  have ht_pos : 0 < t := lt_of_lt_of_le ha ht_uIcc.1
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  field_simp [ht_ne]

/-- Exact primitive for `t ↦ 1/t²` on positive ordered intervals. -/
theorem integral_one_div_sq_eq_inv_sub_inv {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, (1 / t ^ 2 : ℝ) = 1 / a - 1 / b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hnot : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h0
    exact (not_lt_of_ge h0.1) ha
  have hcongr :
      (∫ t in a..b, (1 / t ^ 2 : ℝ)) = ∫ t in a..b, t ^ (-2 : ℤ) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht_pos : 0 < t := lt_of_lt_of_le ha ht.1
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    field_simp [ht_ne]
  rw [hcongr]
  rw [integral_zpow (n := (-2 : ℤ)) (a := a) (b := b)
    (Or.inr ⟨by norm_num, hnot⟩)]
  norm_num
  field_simp [ne_of_gt ha, ne_of_gt hb]
  ring

/-- The positive-tail inverse-square integral is bounded by the reciprocal of its left endpoint. -/
theorem integral_one_div_sq_le_inv_left {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, (1 / t ^ 2 : ℝ) ≤ 1 / a := by
  rw [integral_one_div_sq_eq_inv_sub_inv ha hab]
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hinv_nonneg : 0 ≤ 1 / b := by positivity
  linarith

/-- Lipschitz control of the inner correction window once it lies in `[t/2,t]`. -/
theorem Rcorr_inner_lipschitz_bound
    (D : PhiPsiData B) {C T X t : ℝ}
    (hC : 0 < C) (hX : 0 < X) (hTt : T ≤ t) (h2X : 2 * X ≤ t)
    (hLip : ∀ ⦃s t : ℝ⦄, T ≤ t → (1 / 2 : ℝ) * t ≤ s → s ≤ t →
        |D.f s - D.f t| ≤ C * D.f t / t * |t - s|) :
    ∫ s in (t - X)..t, (D.f s - D.f t) ≤ C * D.f t / t * X ^ 2 := by
  have hX_nonneg : 0 ≤ X := le_of_lt hX
  have ht_pos : 0 < t := by nlinarith
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  have hleft_le : t - X ≤ t := by linarith
  have hXt : X ≤ t := by nlinarith
  have hinner_nonneg : 0 ≤ ∫ s in (t - X)..t, (D.f s - D.f t) :=
    Rcorr_inner_nonneg_of_le D hX_nonneg hXt
  let K : ℝ := C * D.f t / t * X
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    have hf_nonneg : 0 ≤ D.f t := D.f_nonneg ht_nonneg
    positivity
  have hnorm_bound :
      ‖∫ s in (t - X)..t, (D.f s - D.f t)‖ ≤ K * |t - (t - X)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (a := t - X) (b := t)
      (C := K) ?_
    intro s hs
    have hsI : s ∈ Set.Icc (t - X) t := by
      rw [Set.uIoc_of_le hleft_le] at hs
      exact ⟨le_of_lt hs.1, hs.2⟩
    have hs_half : (1 / 2 : ℝ) * t ≤ s := by
      have hleft_half : (1 / 2 : ℝ) * t ≤ t - X := by nlinarith
      exact hleft_half.trans hsI.1
    have hLip_st := hLip hTt hs_half hsI.2
    have hdist_le : |t - s| ≤ X := by
      rw [abs_of_nonneg (sub_nonneg.mpr hsI.2)]
      linarith [hsI.1]
    calc
      ‖D.f s - D.f t‖ = |D.f s - D.f t| := Real.norm_eq_abs _
      _ ≤ C * D.f t / t * |t - s| := hLip_st
      _ ≤ K := by
        dsimp [K]
        have hcoef_nonneg : 0 ≤ C * D.f t / t := by
          have hf_nonneg : 0 ≤ D.f t := D.f_nonneg ht_nonneg
          positivity
        exact mul_le_mul_of_nonneg_left hdist_le hcoef_nonneg
  have hnorm_eq : ‖∫ s in (t - X)..t, (D.f s - D.f t)‖ =
      ∫ s in (t - X)..t, (D.f s - D.f t) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hinner_nonneg]
  calc
    ∫ s in (t - X)..t, (D.f s - D.f t)
        = ‖∫ s in (t - X)..t, (D.f s - D.f t)‖ := hnorm_eq.symm
    _ ≤ K * |t - (t - X)| := hnorm_bound
    _ = C * D.f t / t * X ^ 2 := by
      dsimp [K]
      rw [show |t - (t - X)| = X by
        ring_nf
        exact abs_of_pos hX]
      ring

/-- Pointwise inverse-square bound for the correction tail integrand. -/
theorem Rcorr_tail_integrand_le_inv_sq
    (D : PhiPsiData B) {CL TL CS TS X U t : ℝ}
    (hCL : 0 < CL) (hCS : 0 < CS) (hX : 1 < X) (hU : 2 ≤ U)
    (hTLX : TL ≤ X) (hTSX : TS ≤ X) (hUXt : U * X ≤ t)
    (hLip : ∀ ⦃s t : ℝ⦄, TL ≤ t → (1 / 2 : ℝ) * t ≤ s → s ≤ t →
        |D.f s - D.f t| ≤ CL * D.f t / t * |t - s|)
    (hSq : ∀ t : ℝ, TS ≤ t → D.f t ^ 2 ≤ CS / (t * Real.log t)) :
    D.f t * ∫ s in (t - X)..t, (D.f s - D.f t) ≤
      (CL * CS * X ^ 2 / Real.log X) * (1 / t ^ 2) := by
  have hX_pos : 0 < X := lt_trans zero_lt_one hX
  have hX_nonneg : 0 ≤ X := le_of_lt hX_pos
  have hU_one : 1 ≤ U := le_trans (by norm_num : (1 : ℝ) ≤ 2) hU
  have hX_le_UX : X ≤ U * X := by
    have := mul_le_mul_of_nonneg_right hU_one hX_nonneg
    simpa [one_mul] using this
  have hXt : X ≤ t := hX_le_UX.trans hUXt
  have ht_pos : 0 < t := hX_pos.trans_le hXt
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  have hTLt : TL ≤ t := hTLX.trans hXt
  have hTSt : TS ≤ t := hTSX.trans hXt
  have h2X_le_t : 2 * X ≤ t := by
    exact (mul_le_mul_of_nonneg_right hU hX_nonneg).trans hUXt
  have hinner_le := Rcorr_inner_lipschitz_bound D hCL hX_pos hTLt h2X_le_t hLip
  have hf_nonneg : 0 ≤ D.f t := D.f_nonneg ht_nonneg
  have hsq := hSq t hTSt
  have hlogX_pos : 0 < Real.log X := Real.log_pos hX
  have hlog_le : Real.log X ≤ Real.log t := Real.log_le_log hX_pos hXt
  have hlogt_pos : 0 < Real.log t := lt_of_lt_of_le hlogX_pos hlog_le
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have hlogt_ne : Real.log t ≠ 0 := ne_of_gt hlogt_pos
  have hinv_log_le : 1 / Real.log t ≤ 1 / Real.log X :=
    one_div_le_one_div_of_le hlogX_pos hlog_le
  calc
    D.f t * ∫ s in (t - X)..t, (D.f s - D.f t)
        ≤ D.f t * (CL * D.f t / t * X ^ 2) :=
      mul_le_mul_of_nonneg_left hinner_le hf_nonneg
    _ = CL * X ^ 2 / t * (D.f t ^ 2) := by ring
    _ ≤ CL * X ^ 2 / t * (CS / (t * Real.log t)) := by
      have hcoef_nonneg : 0 ≤ CL * X ^ 2 / t := by positivity
      exact mul_le_mul_of_nonneg_left hsq hcoef_nonneg
    _ = (CL * CS * X ^ 2 / Real.log t) * (1 / t ^ 2) := by
      field_simp [ht_ne, hlogt_ne]
    _ ≤ (CL * CS * X ^ 2 / Real.log X) * (1 / t ^ 2) := by
      have hcoef_nonneg : 0 ≤ CL * CS * X ^ 2 := by positivity
      have hinv_sq_nonneg : 0 ≤ 1 / t ^ 2 := by positivity
      calc
        (CL * CS * X ^ 2 / Real.log t) * (1 / t ^ 2)
            = (CL * CS * X ^ 2) * (1 / Real.log t) * (1 / t ^ 2) := by ring
        _ ≤ (CL * CS * X ^ 2) * (1 / Real.log X) * (1 / t ^ 2) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hinv_log_le hcoef_nonneg) hinv_sq_nonneg
        _ = (CL * CS * X ^ 2 / Real.log X) * (1 / t ^ 2) := by ring

/-- Integrated correction-tail bound from fixed Lipschitz and square-model constants. -/
theorem Rcorr_tail_integral_le_of_constants
    (D : PhiPsiData B) {CL TL CS TS X U : ℝ}
    (hCL : 0 < CL) (hCS : 0 < CS) (hX : 1 < X) (hU : 2 ≤ U)
    (hTLX : TL ≤ X) (hTSX : TS ≤ X) (hUXPhi : U * X ≤ D.Phi X)
    (hLip : ∀ ⦃s t : ℝ⦄, TL ≤ t → (1 / 2 : ℝ) * t ≤ s → s ≤ t →
        |D.f s - D.f t| ≤ CL * D.f t / t * |t - s|)
    (hSq : ∀ t : ℝ, TS ≤ t → D.f t ^ 2 ≤ CS / (t * Real.log t)) :
    Rcorr D X - RcorrTrunc D X U ≤ CL * CS * X / (U * Real.log X) := by
  have hX_pos : 0 < X := lt_trans zero_lt_one hX
  have hX_nonneg : 0 ≤ X := le_of_lt hX_pos
  have hU_pos : 0 < U := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hU
  have hU_one : 1 ≤ U := le_trans (by norm_num : (1 : ℝ) ≤ 2) hU
  have hXUX : X ≤ U * X := by
    have := mul_le_mul_of_nonneg_right hU_one hX_nonneg
    simpa [one_mul] using this
  have hUX_pos : 0 < U * X := mul_pos hU_pos hX_pos
  have hlogX_pos : 0 < Real.log X := Real.log_pos hX
  have hlogX_ne : Real.log X ≠ 0 := ne_of_gt hlogX_pos
  let K : ℝ := CL * CS * X ^ 2 / Real.log X
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  let F : ℝ → ℝ := fun t =>
    D.f t * ∫ s in (t - X)..t, (D.f s - D.f t)
  let G : ℝ → ℝ := fun t => K * (1 / t ^ 2)
  have hF_int : IntervalIntegrable F MeasureTheory.volume (U * X) (D.Phi X) := by
    simpa [F] using Rcorr_tail_integrand_intervalIntegrable_of_order D hX_nonneg hXUX hUXPhi
  have hG_int : IntervalIntegrable G MeasureTheory.volume (U * X) (D.Phi X) := by
    have hbase := one_div_sq_intervalIntegrable_of_pos (a := U * X) (b := D.Phi X)
      hUX_pos hUXPhi
    simpa [G] using hbase.const_mul K
  have hmono : ∫ t in (U * X)..D.Phi X, F t ≤ ∫ t in (U * X)..D.Phi X, G t := by
    refine intervalIntegral.integral_mono_on hUXPhi hF_int hG_int ?_
    intro t ht
    dsimp [F, G, K]
    exact Rcorr_tail_integrand_le_inv_sq D hCL hCS hX hU hTLX hTSX ht.1 hLip hSq
  have hinv_bound : ∫ t in (U * X)..D.Phi X, (1 / t ^ 2 : ℝ) ≤ 1 / (U * X) :=
    integral_one_div_sq_le_inv_left hUX_pos hUXPhi
  have hG_bound : ∫ t in (U * X)..D.Phi X, G t ≤ K * (1 / (U * X)) := by
    dsimp [G]
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hinv_bound hK_nonneg
  have htail_eq := Rcorr_sub_RcorrTrunc_eq_tail D hX_nonneg hXUX hUXPhi
  calc
    Rcorr D X - RcorrTrunc D X U = ∫ t in (U * X)..D.Phi X, F t := by
      simpa [F] using htail_eq
    _ ≤ ∫ t in (U * X)..D.Phi X, G t := hmono
    _ ≤ K * (1 / (U * X)) := hG_bound
    _ = CL * CS * X / (U * Real.log X) := by
      dsimp [K]
      field_simp [ne_of_gt hU_pos, ne_of_gt hX_pos, hlogX_ne]

/-- Integrability of the normalized correction-operator integrand for eventual `X > 1`. -/
theorem corrOperator_integrand_intervalIntegrable_of_gt_one
    (D : PhiPsiData B) {X U : ℝ} (hX_gt : 1 < X) (hU : 1 ≤ U) :
    IntervalIntegrable
      (fun u : ℝ =>
        gNorm D X u *
          ∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u))
      MeasureTheory.volume (1 : ℝ) U := by
  let F : ℝ → ℝ := fun t =>
    D.f t * ∫ s in (t - X)..t, (D.f s - D.f t)
  let A : ℝ := Real.sqrt (X * Real.log X / (2 * lam))
  have hX_pos : 0 < X := lt_trans zero_lt_one hX_gt
  have hX_nonneg : 0 ≤ X := le_of_lt hX_pos
  have hX_ne : X ≠ 0 := ne_of_gt hX_pos
  have hX_le_UX : X ≤ U * X := by
    have := mul_le_mul_of_nonneg_right hU hX_nonneg
    simpa [one_mul] using this
  have hF : IntervalIntegrable F MeasureTheory.volume X (U * X) := by
    simpa [F] using Rcorr_integrand_intervalIntegrable_of_nonneg D hX_nonneg hX_le_UX
  have hcomp0 : IntervalIntegrable (fun u : ℝ => F (X * u))
      MeasureTheory.volume (X / X) ((U * X) / X) := by
    simpa using hF.comp_mul_left (c := X)
  have hcomp : IntervalIntegrable (fun u : ℝ => F (X * u))
      MeasureTheory.volume (1 : ℝ) U := by
    convert hcomp0 using 1 <;> field_simp [hX_ne]
  have hscaled : IntervalIntegrable
      (fun u : ℝ => (X⁻¹ * A * A) * F (X * u)) MeasureTheory.volume (1 : ℝ) U :=
    hcomp.const_mul (X⁻¹ * A * A)
  refine hscaled.congr ?_
  intro u _hu
  dsimp [F, A]
  rw [RcorrTrunc_inner_change D hX_ne]
  dsimp [gNorm]
  ring

/-- Fixed-`U` convergence of the normalized correction operator without absolute values. -/
theorem corrOperator_integral_tendsto_fixed_U
    (D : PhiPsiData B) {U : ℝ} (hU : 1 ≤ U) :
    Tendsto (fun X : ℝ =>
      ∫ u in (1 : ℝ)..U,
        gNorm D X u *
          (∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u)))
      Filter.atTop
      (𝓝 (∫ u in (1 : ℝ)..U, corrKernel u)) := by
  let op : ℝ → ℝ → ℝ := fun X u =>
    gNorm D X u *
      (∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u))
  let C : ℝ := ∫ u in (1 : ℝ)..U, corrKernel u
  have hL1 := corrOperator_L1_convergence_fixed_U D hU
  rw [Metric.tendsto_atTop] at hL1 ⊢
  intro ε hε
  rcases hL1 ε hε with ⟨N₀, hN₀⟩
  refine ⟨max N₀ 2, ?_⟩
  intro X hXN
  have hX_gt : 1 < X :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_trans (le_max_right N₀ (2 : ℝ)) hXN)
  have hN₀X : N₀ ≤ X := le_trans (le_max_left N₀ (2 : ℝ)) hXN
  have hdist := hN₀ X hN₀X
  rw [Real.dist_eq, sub_zero] at hdist
  have hdiff_le :
      |(∫ u in (1 : ℝ)..U, op X u) - C| ≤
        ∫ u in (1 : ℝ)..U, (|op X u - corrKernel u|) := by
    have hop_int := corrOperator_integrand_intervalIntegrable_of_gt_one D hX_gt hU
    have hcorr_int := corrKernel_intervalIntegrable_of_one_le hU
    calc
      |(∫ u in (1 : ℝ)..U, op X u) - C| =
          |∫ u in (1 : ℝ)..U, op X u - corrKernel u| := by
            dsimp [C]
            rw [intervalIntegral.integral_sub hop_int hcorr_int]
      _ ≤ ∫ u in (1 : ℝ)..U, (|op X u - corrKernel u|) :=
          intervalIntegral.abs_integral_le_integral_abs hU
  have hnonneg : 0 ≤ ∫ u in (1 : ℝ)..U, (|op X u - corrKernel u|) :=
    intervalIntegral.integral_nonneg hU (fun _u _hu => abs_nonneg _)
  have habs_rhs : |(∫ u in (1 : ℝ)..U, (|op X u - corrKernel u|))| < ε := by
    simpa [op] using hdist
  have hrhs_lt : ∫ u in (1 : ℝ)..U, (|op X u - corrKernel u|) < ε := by
    simpa [abs_of_nonneg hnonneg] using habs_rhs
  rw [Real.dist_eq]
  simpa [op, C] using lt_of_le_of_lt hdiff_le hrhs_lt

/-- Fixed-`U` truncated correction asymptotic. -/
theorem RcorrTrunc_asymptotic
    (D : PhiPsiData B) {U : ℝ} (hU : 1 ≤ U) :
    (fun X : ℝ =>
      RcorrTrunc D X U -
        2 * lam * (∫ u in (1 : ℝ)..U, corrKernel u) * X / Real.log X)
      =o[Filter.atTop] scaleReal := by
  let op : ℝ → ℝ := fun X : ℝ =>
    ∫ u in (1 : ℝ)..U,
      gNorm D X u *
        (∫ v in (u - 1)..u, (gNorm D X v - gNorm D X u))
  let C : ℝ := ∫ u in (1 : ℝ)..U, corrKernel u
  have hop : Tendsto op Filter.atTop (𝓝 C) := by
    simpa [op, C] using corrOperator_integral_tendsto_fixed_U D hU
  have hcoeff_tendsto :
      Tendsto (fun X : ℝ => 2 * lam * (op X - C)) Filter.atTop (𝓝 0) := by
    have hsub : Tendsto (fun X : ℝ => op X - C) Filter.atTop (𝓝 (C - C)) :=
      hop.sub tendsto_const_nhds
    have hmul : Tendsto (fun X : ℝ => (2 * lam) * (op X - C))
        Filter.atTop (𝓝 ((2 * lam) * (C - C))) :=
      (tendsto_const_nhds (x := 2 * lam)).mul hsub
    simpa using hmul
  have hcoeff_o :
      (fun X : ℝ => 2 * lam * (op X - C)) =o[Filter.atTop] (fun _ : ℝ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 hcoeff_tendsto
  have hprod :
      (fun X : ℝ => (2 * lam * (op X - C)) * scaleReal X)
        =o[Filter.atTop] scaleReal := by
    have hscaleO : scaleReal =O[Filter.atTop] scaleReal :=
      isBigO_refl scaleReal Filter.atTop
    simpa using hcoeff_o.mul_isBigO hscaleO
  refine hprod.congr' ?_ EventuallyEq.rfl
  filter_upwards [RcorrTrunc_normalized_change D hU, eventually_gt_atTop (1 : ℝ)] with
    X hX hX_gt
  have hlog_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX_gt)
  dsimp [op, C]
  rw [hX, scaleReal]
  field_simp [hlog_ne]

/-- Exact split of the large continuous integral into the square term and correction term. -/
theorem continuous_integral_square_correction_split_of_nonneg
    (D : PhiPsiData B) {X : ℝ}
    (hX : 0 ≤ X) (hXPhi : X ≤ D.Phi X) :
    ∫ t in X..D.Phi X, D.f t * GX D X t =
      X * (∫ t in X..D.Phi X, (D.f t) ^ 2) + Rcorr D X := by
  have hsq : IntervalIntegrable (fun t : ℝ => (D.f t) ^ 2)
      MeasureTheory.volume X (D.Phi X) :=
    f_sq_intervalIntegrable_of_nonneg D hX hXPhi
  have hscaled : IntervalIntegrable (fun t : ℝ => X * (D.f t) ^ 2)
      MeasureTheory.volume X (D.Phi X) :=
    hsq.const_mul X
  have hcorr : IntervalIntegrable
      (fun t : ℝ => D.f t * ∫ s in (t - X)..t, (D.f s - D.f t))
      MeasureTheory.volume X (D.Phi X) :=
    Rcorr_integrand_intervalIntegrable_of_nonneg D hX hXPhi
  calc
    ∫ t in X..D.Phi X, D.f t * GX D X t =
        ∫ t in X..D.Phi X,
          X * (D.f t) ^ 2 + D.f t * ∫ s in (t - X)..t, (D.f s - D.f t) := by
      refine intervalIntegral.integral_congr ?_
      intro t _ht
      change D.f t * GX D X t =
        X * (D.f t) ^ 2 + D.f t * ∫ s in (t - X)..t, (D.f s - D.f t)
      rw [GX_eq_X_mul_f_add_correction D X t]
      ring
    _ =
        (∫ t in X..D.Phi X, X * (D.f t) ^ 2) +
          ∫ t in X..D.Phi X, D.f t * ∫ s in (t - X)..t, (D.f s - D.f t) := by
      exact intervalIntegral.integral_add hscaled hcorr
    _ = X * (∫ t in X..D.Phi X, (D.f t) ^ 2) + Rcorr D X := by
      rw [intervalIntegral.integral_const_mul]
      rw [Rcorr]

/-- The composed denominator `H B (log X)` is negligible compared with `X`. -/
theorem H_log_isLittleO_self (B : ℝ) :
    (fun X : ℝ => H B (Real.log X)) =o[Filter.atTop] fun X : ℝ => X := by
  have hlog : (fun X : ℝ => Real.log X) =o[Filter.atTop] fun X : ℝ => X :=
    Real.isLittleO_log_id_atTop
  have hloglog_log :
      (fun X : ℝ => Real.log (Real.log X)) =o[Filter.atTop]
        fun X : ℝ => Real.log X :=
    Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  have hloglog : (fun X : ℝ => Real.log (Real.log X)) =o[Filter.atTop]
      fun X : ℝ => X :=
    hloglog_log.trans hlog
  have hconst : (fun _X : ℝ => B) =o[Filter.atTop] fun X : ℝ => X :=
    isLittleO_const_id_atTop B
  have hmain :
      (fun X : ℝ => Real.log X - Real.log (Real.log X) + B) =o[Filter.atTop]
        fun X : ℝ => X :=
    (hlog.sub hloglog).add hconst
  convert hmain using 1

/-- `PhiFormula` eventually dominates every fixed multiple of the identity. -/
theorem PhiFormula_dominates_fixed_multiple (B U : ℝ) :
    ∀ᶠ X : ℝ in Filter.atTop, U * X ≤ PhiFormula B X := by
  have hlam : 0 < lam := by
    unfold lam
    positivity
  by_cases hU : 0 < U
  · have hscale_pos : 0 < lam / U := div_pos hlam hU
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_H_log_pos_atTop B,
        (H_log_isLittleO_self B).def hscale_pos] with X hX_pos hH_pos hsmall
    have hH_le : H B (Real.log X) ≤ (lam / U) * X := by
      calc
        H B (Real.log X) ≤ ‖H B (Real.log X)‖ := by
          simpa [Real.norm_eq_abs] using le_abs_self (H B (Real.log X))
        _ ≤ (lam / U) * ‖X‖ := hsmall
        _ = (lam / U) * X := by
          rw [Real.norm_eq_abs, abs_of_pos hX_pos]
    have hmul :
        U * H B (Real.log X) ≤ X * lam := by
      calc
        U * H B (Real.log X) ≤ U * ((lam / U) * X) :=
          mul_le_mul_of_nonneg_left hH_le (le_of_lt hU)
        _ = X * lam := by
          field_simp [ne_of_gt hU]
    rw [PhiFormula]
    field_simp [ne_of_gt hH_pos]
    exact hmul
  · have hU_nonpos : U ≤ 0 := le_of_not_gt hU
    filter_upwards [eventually_ge_atTop (0 : ℝ), eventually_PhiFormula_pos_atTop B] with
      X hX_nonneg hPhi_pos
    exact (mul_nonpos_of_nonpos_of_nonneg hU_nonpos hX_nonneg).trans hPhi_pos.le

/-- `D.Phi` eventually dominates every fixed multiple of the identity. -/
theorem Phi_dominates_fixed_multiple
    (D : PhiPsiData B) (U : ℝ) :
    ∀ᶠ X : ℝ in Filter.atTop, U * X ≤ D.Phi X := by
  filter_upwards [PhiFormula_dominates_fixed_multiple B U] with X hX
  simpa [D.Phi_eq X] using hX

/-- Uniform correction-tail bound; the constant is independent of fixed `U ≥ 2`. -/
theorem Rcorr_tail_bound (D : PhiPsiData B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ U : ℝ, 2 ≤ U →
        ∀ᶠ X : ℝ in Filter.atTop,
          0 ≤ Rcorr D X - RcorrTrunc D X U ∧
          Rcorr D X - RcorrTrunc D X U ≤ C * X / (U * Real.log X) := by
  rcases D.f_local_lipschitz (by norm_num : 0 < (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1) with ⟨CL, TL, hCL, hLip⟩
  rcases D.f_sq_upper_bound with ⟨CS, TS, hCS, hSq⟩
  refine ⟨CL * CS, mul_pos hCL hCS, ?_⟩
  intro U hU
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop TL,
    eventually_ge_atTop TS, Phi_dominates_fixed_multiple D U] with X hX hTLX hTSX hUXPhi
  have hX_pos : 0 < X := lt_trans zero_lt_one hX
  have hX_nonneg : 0 ≤ X := le_of_lt hX_pos
  have hU_one : 1 ≤ U := le_trans (by norm_num : (1 : ℝ) ≤ 2) hU
  have hXUX : X ≤ U * X := by
    have := mul_le_mul_of_nonneg_right hU_one hX_nonneg
    simpa [one_mul] using this
  constructor
  · exact Rcorr_sub_RcorrTrunc_nonneg_of_order D hX_nonneg hXUX hUXPhi
  · simpa [mul_assoc] using
      Rcorr_tail_integral_le_of_constants D hCL hCS hX hU hTLX hTSX hUXPhi hLip hSq

/-- The lower square-change endpoint tends to infinity. -/
theorem w0_tendsto_atTop (D : PhiPsiData B) :
    Tendsto (w0 D) Filter.atTop Filter.atTop := by
  simpa [w0] using D.log_psi_tendsto_atTop

/-- First-order size of the lower square-change endpoint. -/
theorem w0_isEquivalent_half_log (D : PhiPsiData B) :
    (fun X : ℝ => w0 D X) ~[Filter.atTop]
      fun X : ℝ => (1 / 2 : ℝ) * Real.log X := by
  have hconst :
      (fun _X : ℝ => (1 / 2 : ℝ)) ~[Filter.atTop]
        fun _X : ℝ => (1 / 2 : ℝ) := IsEquivalent.refl
  have hhalf :
      (fun X : ℝ => (1 / 2 : ℝ) * Real.log X) ~[Filter.atTop]
        fun X : ℝ => (1 / 2 : ℝ) * (2 * Real.log (D.psi X)) :=
    hconst.mul D.log_isEquivalent_two_log_psi
  exact (hhalf.congr_right (by
    filter_upwards [] with X
    simp [w0])).symm

/-- Ratio form of the first-order size of `w0`. -/
theorem w0_div_log_tendsto_half (D : PhiPsiData B) :
    Tendsto (fun X : ℝ => w0 D X / Real.log X)
      Filter.atTop (𝓝 (1 / 2 : ℝ)) := by
  have hden_ne :
      ∀ᶠ X : ℝ in Filter.atTop, ((1 / 2 : ℝ) * Real.log X) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hlog_pos : 0 < Real.log X := Real.log_pos hX
    positivity
  have hratio :
      Tendsto (fun X : ℝ => w0 D X / ((1 / 2 : ℝ) * Real.log X))
        Filter.atTop (𝓝 1) := by
    simpa [Pi.div_apply] using
      (isEquivalent_iff_tendsto_one hden_ne).mp (w0_isEquivalent_half_log D)
  have hscaled :
      Tendsto
        (fun X : ℝ =>
          (1 / 2 : ℝ) * (w0 D X / ((1 / 2 : ℝ) * Real.log X)))
        Filter.atTop (𝓝 ((1 / 2 : ℝ) * 1)) :=
    tendsto_const_nhds.mul hratio
  have hcongr :
      Tendsto (fun X : ℝ => w0 D X / Real.log X)
        Filter.atTop (𝓝 ((1 / 2 : ℝ) * 1)) := by
    refine hscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hlog_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
    field_simp [hlog_ne]
  simpa using hcongr

/-- The endpoint offset is negligible on the main logarithmic scale. -/
theorem two_rX_div_log_tendsto_zero (D : PhiPsiData B) :
    Tendsto (fun X : ℝ => 2 * rX D X / Real.log X)
      Filter.atTop (𝓝 0) := by
  have hw0 := w0_div_log_tendsto_half D
  have htwo :
      Tendsto (fun X : ℝ => (2 : ℝ) * (w0 D X / Real.log X))
        Filter.atTop (𝓝 ((2 : ℝ) * (1 / 2 : ℝ))) :=
    tendsto_const_nhds.mul hw0
  have hsub :
      Tendsto (fun X : ℝ => (2 : ℝ) * (w0 D X / Real.log X) - 1)
        Filter.atTop (𝓝 (((2 : ℝ) * (1 / 2 : ℝ)) - 1)) :=
    htwo.sub tendsto_const_nhds
  have hzero :
      Tendsto (fun X : ℝ => (2 : ℝ) * (w0 D X / Real.log X) - 1)
        Filter.atTop (𝓝 0) := by
    simpa using hsub
  refine hzero.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hlog_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
  dsimp [rX]
  field_simp [hlog_ne]

/-- The denominator at the lower endpoint has the same first-order size as `(log X)/2`. -/
theorem H_w0_isEquivalent_half_log (D : PhiPsiData B) :
    (fun X : ℝ => H B (w0 D X)) ~[Filter.atTop]
      fun X : ℝ => (1 / 2 : ℝ) * Real.log X :=
  ((H_isEquivalent_atTop B).comp_tendsto (w0_tendsto_atTop D)).trans
    (w0_isEquivalent_half_log D)

/-- Exact logarithmic inverse equation rewritten with the square-change endpoint `w0`. -/
theorem log_eq_log_lam_add_two_w0_sub_log_H_w0_eventually
    (D : PhiPsiData B) :
    (fun X : ℝ => Real.log X) =ᶠ[Filter.atTop]
      fun X : ℝ => Real.log lam + 2 * w0 D X - Real.log (H B (w0 D X)) := by
  filter_upwards [D.log_eq_log_lam_add_two_log_psi_sub_log_H_eventually] with X hX
  simpa [w0] using hX

/-- Exact relation reducing the endpoint offset `rX` to `log H(w0)`. -/
theorem rX_eq_half_log_H_w0_sub_log_lam_eventually
    (D : PhiPsiData B) :
    (fun X : ℝ => rX D X) =ᶠ[Filter.atTop]
      fun X : ℝ => (Real.log (H B (w0 D X)) - Real.log lam) / 2 := by
  filter_upwards [log_eq_log_lam_add_two_w0_sub_log_H_w0_eventually D] with X hX
  dsimp [rX]
  rw [hX]
  ring

/-- The lower-endpoint denominator is asymptotically half of `log X`. -/
theorem H_w0_div_log_tendsto_half (D : PhiPsiData B) :
    Tendsto (fun X : ℝ => H B (w0 D X) / Real.log X)
      Filter.atTop (𝓝 (1 / 2 : ℝ)) := by
  have hden_ne :
      ∀ᶠ X : ℝ in Filter.atTop, ((1 / 2 : ℝ) * Real.log X) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hlog_pos : 0 < Real.log X := Real.log_pos hX
    positivity
  have hratio :
      Tendsto
        (fun X : ℝ => H B (w0 D X) / ((1 / 2 : ℝ) * Real.log X))
        Filter.atTop (𝓝 1) := by
    simpa [Pi.div_apply] using
      (isEquivalent_iff_tendsto_one hden_ne).mp (H_w0_isEquivalent_half_log D)
  have hscaled :
      Tendsto
        (fun X : ℝ =>
          (1 / 2 : ℝ) *
            (H B (w0 D X) / ((1 / 2 : ℝ) * Real.log X)))
        Filter.atTop (𝓝 ((1 / 2 : ℝ) * 1)) :=
    tendsto_const_nhds.mul hratio
  have hcongr :
      Tendsto (fun X : ℝ => H B (w0 D X) / Real.log X)
        Filter.atTop (𝓝 ((1 / 2 : ℝ) * 1)) := by
    refine hscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hlog_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
    field_simp [hlog_ne]
  simpa using hcongr

/-- The logarithmic lower-endpoint denominator has the expected constant shift. -/
theorem log_H_w0_sub_loglog_tendsto_neg_log_two (D : PhiPsiData B) :
    Tendsto
      (fun X : ℝ => Real.log (H B (w0 D X)) - Real.log (Real.log X))
      Filter.atTop (𝓝 (-Real.log 2)) := by
  have hratio := H_w0_div_log_tendsto_half D
  have hlog_ratio :
      Tendsto
        (fun X : ℝ => Real.log (H B (w0 D X) / Real.log X))
        Filter.atTop (𝓝 (Real.log (1 / 2 : ℝ))) :=
    hratio.log (by norm_num)
  have htarget :
      Tendsto
        (fun X : ℝ => Real.log (H B (w0 D X)) - Real.log (Real.log X))
        Filter.atTop (𝓝 (Real.log (1 / 2 : ℝ))) := by
    refine hlog_ratio.congr' ?_
    filter_upwards [(w0_tendsto_atTop D).eventually (eventually_H_pos_atTop B),
        eventually_gt_atTop (1 : ℝ)] with X hH_pos hX
    have hH_ne : H B (w0 D X) ≠ 0 := ne_of_gt hH_pos
    have hlog_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
    rw [Real.log_div hH_ne hlog_ne]
  have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    rw [Real.log_inv]
  simpa [hlog_half] using htarget

/-- Constant-precision asymptotic for the offset `rX`. -/
theorem rX_tendsto_sub_model (D : PhiPsiData B) :
    Tendsto
      (fun X : ℝ =>
        rX D X -
          ((Real.log (Real.log X) - Real.log 2 - Real.log lam) / 2))
      Filter.atTop (𝓝 0) := by
  have hlog := log_H_w0_sub_loglog_tendsto_neg_log_two D
  have hplus :
      Tendsto
        (fun X : ℝ =>
          (Real.log (H B (w0 D X)) - Real.log (Real.log X)) + Real.log 2)
        Filter.atTop (𝓝 ((-Real.log 2) + Real.log 2)) :=
    hlog.add tendsto_const_nhds
  have hhalf :
      Tendsto
        (fun X : ℝ =>
          (1 / 2 : ℝ) *
            ((Real.log (H B (w0 D X)) - Real.log (Real.log X)) + Real.log 2))
        Filter.atTop (𝓝 ((1 / 2 : ℝ) * ((-Real.log 2) + Real.log 2))) :=
    tendsto_const_nhds.mul hplus
  have hzero :
      Tendsto
        (fun X : ℝ =>
          (1 / 2 : ℝ) *
            ((Real.log (H B (w0 D X)) - Real.log (Real.log X)) + Real.log 2))
        Filter.atTop (𝓝 0) := by
    simpa using hhalf
  refine hzero.congr' ?_
  filter_upwards [rX_eq_half_log_H_w0_sub_log_lam_eventually D] with X hX
  rw [hX]
  ring

/-- Constant-precision asymptotic for `rX`, in the paper's normalized form. -/
theorem rX_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      rX D X -
        (Real.log (Real.log X) / 2 - Real.log (2 * lam) / 2))
      =o[Filter.atTop] (fun _ : ℝ => (1 : ℝ)) := by
  have hmodel :
      (fun X : ℝ =>
        rX D X -
          ((Real.log (Real.log X) - Real.log 2 - Real.log lam) / 2))
        =o[Filter.atTop] (fun _ : ℝ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (rX_tendsto_sub_model D)
  have hlam_pos : 0 < lam := by
    unfold lam
    positivity
  have hlog_mul : Real.log (2 * lam) = Real.log 2 + Real.log lam := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hlam_pos)]
  exact hmodel.congr_left (fun X => by
    rw [hlog_mul]
    ring)

/-- Lower-endpoint expansion for `w0 = log (psi X)`. -/
theorem lower_endpoint_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      w0 D X -
        (Real.log X / 2 + Real.log (Real.log X) / 2 -
          Real.log (2 * lam) / 2))
      =o[Filter.atTop] (fun _ : ℝ => (1 : ℝ)) := by
  exact (rX_asymptotic D).congr_left (fun X => by
    dsimp [rX]
    ring)

/-- `log log X` is negligible compared with `sqrt (log X)`. -/
theorem loglog_isLittleO_sqrt_log :
    (fun X : ℝ => Real.log (Real.log X)) =o[Filter.atTop]
      fun X : ℝ => Real.sqrt (Real.log X) := by
  have h :
      (fun X : ℝ => Real.log (Real.log X)) =o[Filter.atTop]
        fun X : ℝ => (Real.log X) ^ (1 / 2 : ℝ) :=
    (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp_tendsto
      Real.tendsto_log_atTop
  simpa [Real.sqrt_eq_rpow] using h

/-- Constants are negligible compared with `sqrt (log X)`. -/
theorem const_isLittleO_sqrt_log (c : ℝ) :
    (fun _X : ℝ => c) =o[Filter.atTop]
      fun X : ℝ => Real.sqrt (Real.log X) := by
  exact isLittleO_const_left.mpr
    (Or.inr (tendsto_norm_atTop_atTop.comp
      (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)))

/-- Constants are negligible compared with `sqrt X` on the real tail. -/
theorem const_isLittleO_sqrt_self (c : ℝ) :
    (fun _X : ℝ => c) =o[Filter.atTop] fun X : ℝ => Real.sqrt X := by
  exact isLittleO_const_left.mpr
    (Or.inr (tendsto_norm_atTop_atTop.comp Real.tendsto_sqrt_atTop))

/-- `sqrt (log X)` is negligible compared with `log X`. -/
theorem sqrt_log_isLittleO_log :
    (fun X : ℝ => Real.sqrt (Real.log X)) =o[Filter.atTop]
      fun X : ℝ => Real.log X := by
  have hsqrt : Real.sqrt =o[Filter.atTop] (fun x : ℝ => x) := by
    refine IsLittleO.of_tendsto_div_atTop ?_
    refine Real.tendsto_sqrt_atTop.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h : x / Real.sqrt x = Real.sqrt x := by
      rw [div_eq_iff (Real.sqrt_ne_zero'.mpr hx)]
      rw [mul_comm, ← sq]
      exact (Real.sq_sqrt hx.le).symm
    exact h.symm
  exact hsqrt.comp_tendsto Real.tendsto_log_atTop

/-- The lower endpoint offset is smaller than `sqrt (log X)`. -/
theorem rX_isLittleO_sqrt_log (D : PhiPsiData B) :
    (fun X : ℝ => rX D X) =o[Filter.atTop]
      fun X : ℝ => Real.sqrt (Real.log X) := by
  have hrem :
      (fun X : ℝ =>
        rX D X -
          (Real.log (Real.log X) / 2 - Real.log (2 * lam) / 2))
        =o[Filter.atTop] fun X : ℝ => Real.sqrt (Real.log X) :=
    (rX_asymptotic D).trans (const_isLittleO_sqrt_log 1)
  have hloglog :
      (fun X : ℝ => (1 / 2 : ℝ) * Real.log (Real.log X))
        =o[Filter.atTop] fun X : ℝ => Real.sqrt (Real.log X) :=
    loglog_isLittleO_sqrt_log.const_mul_left (1 / 2 : ℝ)
  have hconst :
      (fun _X : ℝ => -Real.log (2 * lam) / 2)
        =o[Filter.atTop] fun X : ℝ => Real.sqrt (Real.log X) :=
    const_isLittleO_sqrt_log (-Real.log (2 * lam) / 2)
  have hmodel :
      (fun X : ℝ => Real.log (Real.log X) / 2 - Real.log (2 * lam) / 2)
        =o[Filter.atTop] fun X : ℝ => Real.sqrt (Real.log X) := by
    refine (hloglog.add hconst).congr_left ?_
    intro X
    ring
  refine (hrem.add hmodel).congr_left ?_
  intro X
  ring

/-- The square of the lower endpoint offset is negligible compared with `log X`. -/
theorem rX_sq_div_log_tendsto_zero (D : PhiPsiData B) :
    Tendsto (fun X : ℝ => (rX D X) ^ 2 / Real.log X)
      Filter.atTop (𝓝 0) := by
  have hsq := (rX_isLittleO_sqrt_log D).pow (by norm_num : 0 < 2)
  have hsqlog :
      (fun X : ℝ => (rX D X) ^ 2) =o[Filter.atTop]
        fun X : ℝ => Real.log X := by
    refine hsq.congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact Real.sq_sqrt (le_of_lt (Real.log_pos hX))
  exact hsqlog.tendsto_div_nhds_zero

theorem log_sub_const_sq_isLittleO_self (B : ℝ) :
    (fun w : ℝ => (Real.log w - B) ^ 2) =o[Filter.atTop] fun w : ℝ => w := by
  have hlog :
      (fun w : ℝ => Real.log w) =o[Filter.atTop] fun w : ℝ => Real.sqrt w := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ)))
  have hdiff :
      (fun w : ℝ => Real.log w - B) =o[Filter.atTop] fun w : ℝ => Real.sqrt w :=
    hlog.sub (const_isLittleO_sqrt_self B)
  have hsq := hdiff.mul hdiff
  refine hsq.congr' ?_ ?_
  · exact EventuallyEq.of_eq (by
      funext w
      rw [pow_two])
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with w hw
    simpa [pow_two] using Real.sq_sqrt hw

/-- On the real tail, `H B w` is at least half of `w`. -/
theorem eventually_half_self_le_H (B : ℝ) :
    ∀ᶠ w : ℝ in Filter.atTop, (1 / 2 : ℝ) * w ≤ H B w := by
  have hden_ne : ∀ᶠ w : ℝ in Filter.atTop, (fun w : ℝ => w) w ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    exact ne_of_gt hw
  have hratio : Tendsto (fun w : ℝ => H B w / w) Filter.atTop (𝓝 (1 : ℝ)) :=
    (isEquivalent_iff_tendsto_one hden_ne).mp (H_isEquivalent_atTop B)
  filter_upwards [hratio.eventually_const_le (by norm_num : (1 / 2 : ℝ) < 1),
      eventually_gt_atTop (0 : ℝ)] with w hratio_le hw
  have hmul := mul_le_mul_of_nonneg_right hratio_le (le_of_lt hw)
  calc
    (1 / 2 : ℝ) * w ≤ (H B w / w) * w := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    _ = H B w := by
      field_simp [ne_of_gt hw]

/-- On the target tail, exponentiating `w0 = log (psi X)` recovers `psi X`. -/
theorem exp_w0_eq_psi_eventually (D : PhiPsiData B) :
    (fun X : ℝ => Real.exp (w0 D X)) =ᶠ[Filter.atTop] D.psi := by
  filter_upwards [D.psi_pos_eventually] with X hpsi_pos
  simp [w0, Real.exp_log hpsi_pos]

/-- Lower endpoint identity for the square change of variables. -/
theorem Phi_exp_w0_eq_self_eventually (D : PhiPsiData B) :
    (fun X : ℝ => D.Phi (Real.exp (w0 D X))) =ᶠ[Filter.atTop] fun X : ℝ => X := by
  filter_upwards [exp_w0_eq_psi_eventually D, D.Phi_psi_eq_eventually] with X hexp hPhi
  rw [hexp]
  exact hPhi

/-- Upper endpoint identity for the square change of variables. -/
theorem Phi_exp_log_eq_Phi_eventually (D : PhiPsiData B) :
    (fun X : ℝ => D.Phi (Real.exp (Real.log X))) =ᶠ[Filter.atTop]
      fun X : ℝ => D.Phi X := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [Real.exp_log hX]

/-- On the inverse branch, `f (Phi (exp w)) = exp (-w)`. -/
theorem f_Phi_exp_eq (D : PhiPsiData B) :
    ∀ᶠ w : ℝ in Filter.atTop,
      D.f (D.Phi (Real.exp w)) = Real.exp (-w) := by
  filter_upwards [Real.tendsto_exp_atTop.eventually_ge_atTop (D.N0 : ℝ)] with w hw_tail
  have htarget : D.Tstar ≤ D.Phi (Real.exp w) :=
    D.Phi_maps_tail (Real.exp w) hw_tail
  rw [D.f_eq_tail (D.Phi (Real.exp w)) htarget]
  rw [D.psi_right_inv (Real.exp w) hw_tail]
  rw [one_div, ← Real.exp_neg]

/-- Derivative of the logarithmic parametrization `w ↦ PhiFormula B (exp w)` on a tail. -/
theorem PhiLog_hasDerivAt_eventually (B : ℝ) :
    ∀ᶠ w : ℝ in Filter.atTop,
      HasDerivAt (PhiLog B)
        (lam * Real.exp (2 * w) *
          (2 / H B w - Hderiv w / (H B w) ^ 2)) w := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_H_pos_atTop B] with w hw hH_pos
  have hexp_ne : Real.exp w ≠ 0 := Real.exp_ne_zero w
  have hw_ne : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  have hH_ne : H B w ≠ 0 := ne_of_gt hH_pos
  have houter : HasDerivAt (PhiFormula B)
      (lam * Real.exp w * (2 * H B w - Hderiv w) / (H B w) ^ 2) (Real.exp w) := by
    simpa [Real.log_exp] using
      (PhiFormula_hasDerivAt (B := B) (x := Real.exp w) hexp_ne (by simpa using hw_ne)
        (by simpa [Real.log_exp] using hH_ne))
  have hcomp : HasDerivAt (PhiLog B)
      ((lam * Real.exp w * (2 * H B w - Hderiv w) / (H B w) ^ 2) * Real.exp w) w := by
    simpa [PhiLog] using houter.comp w (Real.hasDerivAt_exp w)
  convert hcomp using 1
  have hexp_sq : Real.exp w * Real.exp w = Real.exp (2 * w) := by
    rw [← Real.exp_add]
    ring_nf
  rw [← hexp_sq]
  field_simp [hH_ne]

/-- The logarithmic parametrization has nonnegative derivative on a tail. -/
theorem PhiLog_deriv_nonneg_eventually (B : ℝ) :
    ∀ᶠ w : ℝ in Filter.atTop,
      0 ≤ lam * Real.exp (2 * w) *
        (2 / H B w - Hderiv w / (H B w) ^ 2) := by
  have hlam : 0 < lam := by
    unfold lam
    positivity
  filter_upwards [eventually_H_pos_atTop B,
      eventually_two_mul_H_sub_Hderiv_pos_atTop B] with w hH_pos hnum_pos
  have hH_ne : H B w ≠ 0 := ne_of_gt hH_pos
  have hbracket :
      2 / H B w - Hderiv w / (H B w) ^ 2 =
        (2 * H B w - Hderiv w) / (H B w) ^ 2 := by
    field_simp [hH_ne]
  rw [hbracket]
  positivity

/-- Derivative of the denominator `H B w = w - log w + B`. -/
theorem H_hasDerivAt {B w : ℝ} (hw : w ≠ 0) :
    HasDerivAt (H B) (Hderiv w) w := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 w := hasDerivAt_id w
  have hlog : HasDerivAt Real.log w⁻¹ w := Real.hasDerivAt_log hw
  convert (hid.sub hlog).const_add B using 1
  · funext y
    simp [H]
    ring
  · rw [Hderiv]
    ring

/-- Derivative of the reciprocal denominator. -/
theorem H_inv_hasDerivAt {B w : ℝ} (hw : w ≠ 0) (hH : H B w ≠ 0) :
    HasDerivAt (fun z : ℝ => (H B z)⁻¹)
      (-(Hderiv w) / (H B w) ^ 2) w := by
  have h := (H_hasDerivAt (B := B) hw).inv hH
  convert h using 1

/-- The reciprocal denominator derivative is available on the real tail. -/
theorem H_inv_hasDerivAt_eventually (B : ℝ) :
    ∀ᶠ w : ℝ in Filter.atTop,
      HasDerivAt (fun z : ℝ => (H B z)⁻¹)
        (-(Hderiv w) / (H B w) ^ 2) w := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_H_pos_atTop B] with w hw hH_pos
  exact H_inv_hasDerivAt (B := B) (ne_of_gt (lt_trans zero_lt_one hw)) (ne_of_gt hH_pos)

/-- If both endpoints of an unordered interval lie above `T`, every point in it lies above `T`. -/
theorem le_of_endpoints_le_of_mem_uIcc {T a b x : ℝ}
    (ha : T ≤ a) (hb : T ≤ b) (hx : x ∈ Set.uIcc a b) : T ≤ x := by
  rw [Set.mem_uIcc] at hx
  rcases hx with hx | hx
  · exact ha.trans hx.1
  · exact hb.trans hx.1

/-- Interior points between `min a b` and `max a b` lie in the unordered interval. -/
theorem mem_uIcc_of_mem_Ioo_min_max {a b x : ℝ}
    (hx : x ∈ Set.Ioo (min a b) (max a b)) : x ∈ Set.uIcc a b := by
  rw [Set.mem_uIcc]
  by_cases hab : a ≤ b
  · left
    have hmin : min a b = a := min_eq_left hab
    have hmax : max a b = b := max_eq_right hab
    rw [hmin, hmax] at hx
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  · right
    have hba : b ≤ a := le_of_not_ge hab
    have hmin : min a b = b := min_eq_right hba
    have hmax : max a b = a := max_eq_left hba
    rw [hmin, hmax] at hx
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩

/-- Exact integral of `w⁻¹` on a positive unordered interval. -/
theorem inv_integral_eq_log_sub_of_pos {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∫ w in a..b, w⁻¹ = Real.log b - Real.log a := by
  have hpos_of_mem : ∀ w : ℝ, w ∈ Set.uIcc a b → 0 < w := by
    intro w hw
    rcases Set.mem_uIcc.mp hw with hwab | hwba
    · exact lt_of_lt_of_le ha hwab.1
    · exact lt_of_lt_of_le hb hwba.1
  have hcont : ContinuousOn (fun w : ℝ => w⁻¹) (Set.uIcc a b) := by
    intro w hw
    have hw_ne : w ≠ 0 := ne_of_gt (hpos_of_mem w hw)
    exact (continuousAt_id.inv₀ hw_ne).continuousWithinAt
  have hint : IntervalIntegrable (fun w : ℝ => w⁻¹) MeasureTheory.volume a b :=
    hcont.intervalIntegrable
  have hderiv : ∀ w ∈ Set.uIcc a b,
      HasDerivAt Real.log ((fun y : ℝ => y⁻¹) w) w := by
    intro w hw
    exact Real.hasDerivAt_log (ne_of_gt (hpos_of_mem w hw))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Exact reciprocal integral over the square-change window. -/
theorem inv_integral_w0_log_eq_eventually
    (D : PhiPsiData B) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∫ w in w0 D X..Real.log X, w⁻¹ =
        Real.log (Real.log X) - Real.log (w0 D X) := by
  filter_upwards [(w0_tendsto_atTop D).eventually_gt_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with X hw0 hlog
  exact inv_integral_eq_log_sub_of_pos (a := w0 D X) (b := Real.log X) hw0 hlog

/-- Exact doubled reciprocal integral over the square-change window. -/
theorem two_inv_integral_w0_log_eq_eventually
    (D : PhiPsiData B) :
    ∀ᶠ X : ℝ in Filter.atTop,
      (2 : ℝ) * (∫ w in w0 D X..Real.log X, w⁻¹) =
        2 * (Real.log (Real.log X) - Real.log (w0 D X)) := by
  filter_upwards [inv_integral_w0_log_eq_eventually D] with X hX
  rw [hX]

/-- Exact cancellation form of the `2∫dw/w` contribution. -/
theorem two_inv_integral_remainder_identity_eventually
    (D : PhiPsiData B) :
    ∀ᶠ X : ℝ in Filter.atTop,
      Real.log X *
          ((2 : ℝ) * (∫ w in w0 D X..Real.log X, w⁻¹) - 2 * Real.log 2) +
          4 * rX D X =
        2 * Real.log X *
          (2 * rX D X / Real.log X -
            Real.log (1 + 2 * rX D X / Real.log X)) := by
  filter_upwards [two_inv_integral_w0_log_eq_eventually D,
      (w0_tendsto_atTop D).eventually_gt_atTop (0 : ℝ),
      eventually_gt_atTop (1 : ℝ)] with X hint hw0 hX
  have hY_pos : 0 < Real.log X := Real.log_pos hX
  have hY_ne : Real.log X ≠ 0 := ne_of_gt hY_pos
  have hw0_ne : w0 D X ≠ 0 := ne_of_gt hw0
  have harg_eq :
      1 + 2 * rX D X / Real.log X = (2 * w0 D X) / Real.log X := by
    dsimp [rX]
    field_simp [hY_ne]
    ring
  have htwo_w0_pos : 0 < 2 * w0 D X := by positivity
  have hlog_arg :
      Real.log (1 + 2 * rX D X / Real.log X) =
        Real.log 2 + Real.log (w0 D X) - Real.log (Real.log X) := by
    rw [harg_eq]
    rw [Real.log_div (ne_of_gt htwo_w0_pos) (ne_of_gt hY_pos)]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hw0_ne]
  rw [hint, hlog_arg]
  field_simp [hY_ne]
  ring

/-- Uniform elementary bound for the real `log (1+u)` remainder near zero. -/
theorem log_one_add_remainder_abs_le_two_sq {u : ℝ}
    (hu : |u| ≤ (1 / 2 : ℝ)) :
    |u - Real.log (1 + u)| ≤ 2 * u ^ 2 := by
  have hneg : -(1 / 2 : ℝ) ≤ u := (abs_le.mp hu).1
  have hpos : 0 < 1 + u := by linarith
  have hlog_le : Real.log (1 + u) ≤ u := by
    simpa [add_sub_cancel_left] using Real.log_le_sub_one_of_pos hpos
  have hnonneg : 0 ≤ u - Real.log (1 + u) := sub_nonneg.mpr hlog_le
  have hlog_lower_raw := Real.one_sub_inv_le_log_of_pos hpos
  have hlog_lower : u / (1 + u) ≤ Real.log (1 + u) := by
    calc
      u / (1 + u) = 1 - (1 + u)⁻¹ := by
        field_simp [ne_of_gt hpos]
        ring
      _ ≤ Real.log (1 + u) := hlog_lower_raw
  have hupper1 : u - Real.log (1 + u) ≤ u - u / (1 + u) := by
    linarith
  have halg : u - u / (1 + u) = u ^ 2 / (1 + u) := by
    field_simp [ne_of_gt hpos]
    ring
  have hpos_half : (1 / 2 : ℝ) ≤ 1 + u := by linarith
  have hfrac_le : u ^ 2 / (1 + u) ≤ 2 * u ^ 2 := by
    calc
      u ^ 2 / (1 + u) ≤ u ^ 2 / (1 / 2 : ℝ) := by
        gcongr
      _ = 2 * u ^ 2 := by ring
  rw [abs_of_nonneg hnonneg]
  exact hupper1.trans (by rw [halg]; exact hfrac_le)

/-- If `Y*u² = o(1)` and `u → 0`, then `Y * (u - log(1+u)) = o(1)`. -/
theorem isLittleO_mul_log_one_add_remainder
    {α : Type*} {l : Filter α} {Y u : α → ℝ}
    (hu : Tendsto u l (𝓝 0))
    (hYu2 : (fun x => Y x * (u x) ^ 2) =o[l] fun _ => (1 : ℝ)) :
    (fun x => Y x * (u x - Real.log (1 + u x))) =o[l] fun _ => (1 : ℝ) := by
  have hsmall : ∀ᶠ x in l, |u x| ≤ (1 / 2 : ℝ) := by
    have hdist : ∀ᶠ x in l, dist (u x) 0 < (1 / 2 : ℝ) :=
      (Metric.tendsto_nhds.mp hu) (1 / 2) (by norm_num)
    filter_upwards [hdist] with x hx
    rw [Real.dist_eq, sub_zero] at hx
    exact le_of_lt hx
  have hbig :
      (fun x => Y x * (u x - Real.log (1 + u x))) =O[l]
        fun x => Y x * (u x) ^ 2 := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [hsmall] with x hx
    have hrem := log_one_add_remainder_abs_le_two_sq hx
    calc
      ‖Y x * (u x - Real.log (1 + u x))‖ =
          ‖Y x‖ * |u x - Real.log (1 + u x)| := by
        rw [norm_mul]
        simp [Real.norm_eq_abs]
      _ ≤ ‖Y x‖ * (2 * (u x) ^ 2) := by
        gcongr
      _ = 2 * ‖Y x * (u x) ^ 2‖ := by
        rw [norm_mul, Real.norm_of_nonneg (sq_nonneg (u x))]
        ring
  exact hbig.trans_isLittleO hYu2

/-- The Taylor-remainder part of the `2∫dw/w` contribution is negligible. -/
theorem two_inv_integral_log_remainder_isLittleO
    (D : PhiPsiData B) :
    (fun X : ℝ =>
      Real.log X *
        (2 * rX D X / Real.log X -
          Real.log (1 + 2 * rX D X / Real.log X)))
      =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
  let u : ℝ → ℝ := fun X => 2 * rX D X / Real.log X
  have hu : Tendsto u Filter.atTop (𝓝 0) := by
    simpa [u] using two_rX_div_log_tendsto_zero D
  have hYu2_tendsto :
      Tendsto (fun X : ℝ => Real.log X * (u X) ^ 2)
        Filter.atTop (𝓝 0) := by
    have hsq := (rX_sq_div_log_tendsto_zero D).const_mul (4 : ℝ)
    have htarget :
        Tendsto (fun X : ℝ => Real.log X * (u X) ^ 2)
          Filter.atTop (𝓝 (4 * 0)) := by
      refine hsq.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
      have hlog_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
      dsimp [u]
      field_simp [hlog_ne]
      ring
    simpa using htarget
  have hYu2 :
      (fun X : ℝ => Real.log X * (u X) ^ 2)
        =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) :=
    (isLittleO_one_iff ℝ).mpr hYu2_tendsto
  simpa [u] using isLittleO_mul_log_one_add_remainder
    (Y := fun X : ℝ => Real.log X) (u := u) hu hYu2

/-- Contribution of `2∫dw/w`, after cancellation with the lower endpoint offset. -/
theorem two_inv_integral_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      Real.log X *
        ((2 : ℝ) * (∫ w in w0 D X..Real.log X, w⁻¹) - 2 * Real.log 2) +
        4 * rX D X)
      =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
  have hrem := (two_inv_integral_log_remainder_isLittleO D).const_mul_left (2 : ℝ)
  refine hrem.congr' ?_ EventuallyEq.rfl
  filter_upwards [two_inv_integral_remainder_identity_eventually D] with X hX
  rw [hX]
  ring

/-- Antiderivative support for `(log w - B) / w²`. -/
theorem log_sub_const_div_sq_hasDerivAt {B w : ℝ} (hw : w ≠ 0) :
    HasDerivAt (fun z : ℝ => -((Real.log z + 1 - B) * z⁻¹))
      ((Real.log w - B) / w ^ 2) w := by
  have hnum : HasDerivAt (fun z : ℝ => Real.log z + 1 - B) (w⁻¹) w := by
    simpa using ((Real.hasDerivAt_log hw).add_const (1 - B))
  have hinv : HasDerivAt (fun z : ℝ => z⁻¹) (-(1 : ℝ) / w ^ 2) w := by
    simpa using (hasDerivAt_id w).inv hw
  have hmul : HasDerivAt (fun z : ℝ => (Real.log z + 1 - B) * z⁻¹)
      (w⁻¹ * w⁻¹ + (Real.log w + 1 - B) * (-(1 : ℝ) / w ^ 2)) w := by
    exact hnum.mul hinv
  convert hmul.neg using 1
  field_simp [hw]
  ring

/-- Exact integral of `(log w - B) / w²` on a positive unordered interval. -/
theorem log_sub_const_div_sq_integral_eq_of_pos {B a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∫ w in a..b, (Real.log w - B) / w ^ 2 =
      -((Real.log b + 1 - B) * b⁻¹) -
        -((Real.log a + 1 - B) * a⁻¹) := by
  have hpos_of_mem : ∀ w : ℝ, w ∈ Set.uIcc a b → 0 < w := by
    intro w hw
    rcases Set.mem_uIcc.mp hw with hwab | hwba
    · exact lt_of_lt_of_le ha hwab.1
    · exact lt_of_lt_of_le hb hwba.1
  have hcont :
      ContinuousOn (fun w : ℝ => (Real.log w - B) / w ^ 2) (Set.uIcc a b) := by
    intro w hw
    have hw_ne : w ≠ 0 := ne_of_gt (hpos_of_mem w hw)
    have hlog : ContinuousAt Real.log w := Real.continuousAt_log hw_ne
    have hnum : ContinuousAt (fun y : ℝ => Real.log y - B) w :=
      hlog.sub continuousAt_const
    have hden_ne : w ^ 2 ≠ 0 := pow_ne_zero 2 hw_ne
    exact (hnum.div (continuousAt_id.pow 2) hden_ne).continuousWithinAt
  have hint : IntervalIntegrable (fun w : ℝ => (Real.log w - B) / w ^ 2)
      MeasureTheory.volume a b :=
    hcont.intervalIntegrable
  have hderiv : ∀ w ∈ Set.uIcc a b,
      HasDerivAt (fun z : ℝ => -((Real.log z + 1 - B) * z⁻¹))
        ((Real.log w - B) / w ^ 2) w := by
    intro w hw
    exact log_sub_const_div_sq_hasDerivAt (B := B) (ne_of_gt (hpos_of_mem w hw))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Exact `(log w - B) / w²` integral over the square-change window. -/
theorem log_sub_const_div_sq_integral_w0_log_eq_eventually
    (D : PhiPsiData B) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∫ w in w0 D X..Real.log X, (Real.log w - B) / w ^ 2 =
        -((Real.log (Real.log X) + 1 - B) * (Real.log X)⁻¹) -
          -((Real.log (w0 D X) + 1 - B) * (w0 D X)⁻¹) := by
  filter_upwards [(w0_tendsto_atTop D).eventually_gt_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with X hw0 hlog
  exact log_sub_const_div_sq_integral_eq_of_pos (B := B) (a := w0 D X)
    (b := Real.log X) hw0 hlog

/-- The logarithmic lower endpoint differs from `log log X` by `-log 2 + o(1)`. -/
theorem log_w0_sub_loglog_tendsto_neg_log_two (D : PhiPsiData B) :
    Tendsto
      (fun X : ℝ => Real.log (w0 D X) - Real.log (Real.log X))
      Filter.atTop (𝓝 (-Real.log 2)) := by
  have hratio := w0_div_log_tendsto_half D
  have hlogratio : Tendsto (fun X : ℝ => Real.log (w0 D X / Real.log X))
      Filter.atTop (𝓝 (Real.log (1 / 2 : ℝ))) := by
    exact hratio.log (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have htarget : Tendsto
      (fun X : ℝ => Real.log (w0 D X) - Real.log (Real.log X))
      Filter.atTop (𝓝 (Real.log (1 / 2 : ℝ))) := by
    refine hlogratio.congr' ?_
    filter_upwards [(w0_tendsto_atTop D).eventually_gt_atTop (0 : ℝ),
        eventually_gt_atTop (1 : ℝ)] with X hw0 hX
    have hw0_ne : w0 D X ≠ 0 := ne_of_gt hw0
    have hlog_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
    rw [Real.log_div hw0_ne hlog_ne]
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    rw [Real.log_inv]
  simpa [hhalf] using htarget

/-- The inverse lower-endpoint ratio tends to `2`. -/
theorem log_div_w0_tendsto_two (D : PhiPsiData B) :
    Tendsto (fun X : ℝ => Real.log X / w0 D X)
      Filter.atTop (𝓝 (2 : ℝ)) := by
  have hratio := w0_div_log_tendsto_half D
  have hinv : Tendsto (fun X : ℝ => (w0 D X / Real.log X)⁻¹)
      Filter.atTop (𝓝 (((1 / 2 : ℝ))⁻¹)) :=
    hratio.inv₀ (by norm_num)
  have htarget : Tendsto (fun X : ℝ => Real.log X / w0 D X)
      Filter.atTop (𝓝 (((1 / 2 : ℝ))⁻¹)) := by
    refine hinv.congr' ?_
    filter_upwards [(w0_tendsto_atTop D).eventually_gt_atTop (0 : ℝ),
        eventually_gt_atTop (1 : ℝ)] with X hw0 hX
    have hw0_ne : w0 D X ≠ 0 := ne_of_gt hw0
    have hlog_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
    field_simp [hw0_ne, hlog_ne]
  simpa using htarget

/-- The shifted lower-endpoint logarithm is negligible on the `sqrt(log X)` scale. -/
theorem log_w0_add_const_div_sqrt_log_tendsto_zero (D : PhiPsiData B) :
    Tendsto (fun X : ℝ => (Real.log (w0 D X) + 1 - B) / Real.sqrt (Real.log X))
      Filter.atTop (𝓝 0) := by
  have hsqrt_atTop : Tendsto (fun X : ℝ => Real.sqrt (Real.log X))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hconst : Tendsto (fun _X : ℝ => (1 - B : ℝ)) Filter.atTop
      (𝓝 (1 - B : ℝ)) :=
    tendsto_const_nhds
  have hdiff : Tendsto
      (fun X : ℝ => (Real.log (w0 D X) - Real.log (Real.log X)) + (1 - B))
      Filter.atTop (𝓝 ((-Real.log 2) + (1 - B))) :=
    (log_w0_sub_loglog_tendsto_neg_log_two D).add hconst
  have hdiff_div : Tendsto
      (fun X : ℝ => ((Real.log (w0 D X) - Real.log (Real.log X)) + (1 - B)) /
        Real.sqrt (Real.log X)) Filter.atTop (𝓝 0) :=
    hdiff.div_atTop hsqrt_atTop
  have hloglog_div : Tendsto
      (fun X : ℝ => Real.log (Real.log X) / Real.sqrt (Real.log X))
      Filter.atTop (𝓝 0) :=
    loglog_isLittleO_sqrt_log.tendsto_div_nhds_zero
  have hsum := hloglog_div.add hdiff_div
  have hsum0 : Tendsto
      (fun X : ℝ => Real.log (Real.log X) / Real.sqrt (Real.log X) +
        ((Real.log (w0 D X) - Real.log (Real.log X)) + (1 - B)) /
          Real.sqrt (Real.log X)) Filter.atTop (𝓝 0) := by
    simpa using hsum
  refine hsum0.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hsqrt_ne : Real.sqrt (Real.log X) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (Real.log_pos hX)
  field_simp [hsqrt_ne]
  ring

/-- Product estimate needed in the `(log w - B)/w²` contribution. -/
theorem log_div_w0_sub_two_mul_log_w0_add_const_tendsto_zero
    (D : PhiPsiData B) :
    Tendsto
      (fun X : ℝ =>
        (Real.log X / w0 D X - 2) *
          (Real.log (w0 D X) + 1 - B))
      Filter.atTop (𝓝 0) := by
  have h_r : Tendsto (fun X : ℝ => rX D X / Real.sqrt (Real.log X))
      Filter.atTop (𝓝 0) :=
    (rX_isLittleO_sqrt_log D).tendsto_div_nhds_zero
  have h_log := log_w0_add_const_div_sqrt_log_tendsto_zero D
  have h_ratio := log_div_w0_tendsto_two D
  have hprod : Tendsto
      (fun X : ℝ =>
        (-2 : ℝ) * (rX D X / Real.sqrt (Real.log X)) *
          ((Real.log (w0 D X) + 1 - B) / Real.sqrt (Real.log X)) *
            (Real.log X / w0 D X))
      Filter.atTop (𝓝 (((-2 : ℝ) * 0 * 0) * 2)) :=
    ((tendsto_const_nhds.mul h_r).mul h_log).mul h_ratio
  have hzero : Tendsto
      (fun X : ℝ =>
        (-2 : ℝ) * (rX D X / Real.sqrt (Real.log X)) *
          ((Real.log (w0 D X) + 1 - B) / Real.sqrt (Real.log X)) *
            (Real.log X / w0 D X))
      Filter.atTop (𝓝 0) := by
    simpa using hprod
  refine hzero.congr' ?_
  filter_upwards [(w0_tendsto_atTop D).eventually_gt_atTop (0 : ℝ),
      eventually_gt_atTop (1 : ℝ)] with X hw0 hX
  have hlog_pos : 0 < Real.log X := Real.log_pos hX
  have hlog_ne : Real.log X ≠ 0 := ne_of_gt hlog_pos
  have hw0_ne : w0 D X ≠ 0 := ne_of_gt hw0
  have hsqrt_ne : Real.sqrt (Real.log X) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hlog_pos
  dsimp [rX]
  field_simp [hlog_ne, hw0_ne, hsqrt_ne]
  rw [show (Real.sqrt (Real.log X)) ^ 2 = Real.log X by
    exact Real.sq_sqrt hlog_pos.le]
  ring

/-- Algebraic cancellation after inserting the exact primitive. -/
theorem log_sub_const_div_sq_integral_algebra
    (D : PhiPsiData B) (X : ℝ)
    (hw0 : w0 D X ≠ 0) (hlog : Real.log X ≠ 0) :
    Real.log X *
        ((2 : ℝ) *
          (-((Real.log (Real.log X) + 1 - B) * (Real.log X)⁻¹) -
            -((Real.log (w0 D X) + 1 - B) * (w0 D X)⁻¹))) -
        (2 * Real.log (Real.log X) - 4 * Real.log 2 + 2 - 2 * B)
      =
        4 * (Real.log (w0 D X) - Real.log (Real.log X) + Real.log 2) +
          2 * (Real.log X / w0 D X - 2) *
            (Real.log (w0 D X) + 1 - B) := by
  field_simp [hw0, hlog]
  ring

/-- Contribution of `2∫(log w - B)/w²`, after first-order endpoint cancellation. -/
theorem log_sub_const_div_sq_integral_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      Real.log X *
        ((2 : ℝ) *
          (∫ w in w0 D X..Real.log X, (Real.log w - B) / w ^ 2))
        - (2 * Real.log (Real.log X) - 4 * Real.log 2 + 2 - 2 * B))
      =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
  have hlogterm : Tendsto
      (fun X : ℝ => Real.log (w0 D X) - Real.log (Real.log X) + Real.log 2)
      Filter.atTop (𝓝 0) := by
    have hconst : Tendsto (fun _X : ℝ => (Real.log 2 : ℝ)) Filter.atTop
        (𝓝 (Real.log 2)) :=
      tendsto_const_nhds
    have h := (log_w0_sub_loglog_tendsto_neg_log_two D).add hconst
    have h0 : Tendsto
        (fun X : ℝ => (Real.log (w0 D X) - Real.log (Real.log X)) + Real.log 2)
        Filter.atTop (𝓝 0) := by
      simpa using h
    simpa [add_assoc] using h0
  have hprod := log_div_w0_sub_two_mul_log_w0_add_const_tendsto_zero D
  have hsum : Tendsto
      (fun X : ℝ =>
        4 * (Real.log (w0 D X) - Real.log (Real.log X) + Real.log 2) +
          2 * (Real.log X / w0 D X - 2) *
            (Real.log (w0 D X) + 1 - B))
      Filter.atTop (𝓝 0) := by
    have hfour : Tendsto (fun _X : ℝ => (4 : ℝ)) Filter.atTop (𝓝 (4 : ℝ)) :=
      tendsto_const_nhds
    have htwo : Tendsto (fun _X : ℝ => (2 : ℝ)) Filter.atTop (𝓝 (2 : ℝ)) :=
      tendsto_const_nhds
    have h1 := hfour.mul hlogterm
    have h2 := htwo.mul hprod
    have h := h1.add h2
    simpa [mul_assoc] using h
  refine (isLittleO_one_iff ℝ).mpr ?_
  refine hsum.congr' ?_
  filter_upwards [log_sub_const_div_sq_integral_w0_log_eq_eventually D,
      (w0_tendsto_atTop D).eventually_gt_atTop (0 : ℝ),
      eventually_gt_atTop (1 : ℝ)] with X hInt hw0 hX
  have hw0_ne : w0 D X ≠ 0 := ne_of_gt hw0
  have hlog_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
  rw [hInt]
  exact (log_sub_const_div_sq_integral_algebra (D := D) (X := X) hw0_ne hlog_ne).symm

/-- Pointwise algebra for the geometric `1/H` expansion remainder. -/
theorem H_inv_remainder_eq {B w : ℝ}
    (hw : w ≠ 0) (hH : H B w ≠ 0) :
    (H B w)⁻¹ - (w⁻¹ + (Real.log w - B) / w ^ 2) =
      (Real.log w - B) ^ 2 / (w ^ 2 * H B w) := by
  rw [H] at hH ⊢
  field_simp [hw, hH]
  ring

/-- Pointwise bound for the geometric `1/H` remainder on a positive tail. -/
theorem H_inv_remainder_abs_le {B w δ : ℝ}
    (hw : 0 < w)
    (hH : (1 / 2 : ℝ) * w ≤ H B w)
    (hsmall : (Real.log w - B) ^ 2 ≤ δ * w) :
    |(H B w)⁻¹ - (w⁻¹ + (Real.log w - B) / w ^ 2)| ≤
      2 * δ / w ^ 2 := by
  have hH_pos : 0 < H B w := by
    have hhalf_pos : 0 < (1 / 2 : ℝ) * w := by positivity
    exact lt_of_lt_of_le hhalf_pos hH
  have hden_small_pos : 0 < w ^ 2 * ((1 / 2 : ℝ) * w) := by positivity
  have hden_le : w ^ 2 * ((1 / 2 : ℝ) * w) ≤ w ^ 2 * H B w := by
    gcongr
  rw [H_inv_remainder_eq (B := B) (w := w) (ne_of_gt hw) (ne_of_gt hH_pos)]
  have hden_pos : 0 < w ^ 2 * H B w := by positivity
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hden_pos.le)]
  calc
    (Real.log w - B) ^ 2 / (w ^ 2 * H B w)
        ≤ (Real.log w - B) ^ 2 / (w ^ 2 * ((1 / 2 : ℝ) * w)) :=
          div_le_div_of_nonneg_left (sq_nonneg _) hden_small_pos hden_le
    _ ≤ (δ * w) / (w ^ 2 * ((1 / 2 : ℝ) * w)) :=
          div_le_div_of_nonneg_right hsmall hden_small_pos.le
    _ = 2 * δ / w ^ 2 := by
          field_simp [ne_of_gt hw]

private theorem H_inv_remainder_integral_bound_eventually
    (D : PhiPsiData B) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ‖∫ w in w0 D X..Real.log X,
        ((H B w)⁻¹ - (w⁻¹ + (Real.log w - B) / w ^ 2))‖ ≤
        c * ‖(Real.log X)⁻¹‖ := by
  let δ : ℝ := c / 18
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  rcases Filter.eventually_atTop.mp
      ((log_sub_const_sq_isLittleO_self B).def hδ_pos) with ⟨Tsq, hsqT⟩
  rcases Filter.eventually_atTop.mp (eventually_half_self_le_H B) with ⟨TH, hHT⟩
  let T : ℝ := max 1 (max Tsq TH)
  have hT_one : 1 ≤ T := le_max_left 1 (max Tsq TH)
  have hT_sq : Tsq ≤ T := (le_max_left Tsq TH).trans (le_max_right 1 (max Tsq TH))
  have hT_H : TH ≤ T := (le_max_right Tsq TH).trans (le_max_right 1 (max Tsq TH))
  have hratio_low :
      ∀ᶠ X : ℝ in Filter.atTop, (1 / 3 : ℝ) ≤ w0 D X / Real.log X :=
    (w0_div_log_tendsto_half D).eventually_const_le
      (by norm_num : (1 / 3 : ℝ) < 1 / 2)
  have hratio_high :
      ∀ᶠ X : ℝ in Filter.atTop, w0 D X / Real.log X < (2 / 3 : ℝ) :=
    (w0_div_log_tendsto_half D).eventually_lt_const
      (by norm_num : (1 / 2 : ℝ) < 2 / 3)
  filter_upwards [(w0_tendsto_atTop D).eventually_ge_atTop T,
      hratio_low, hratio_high, eventually_gt_atTop (1 : ℝ)] with
    X hw0T hlow hhigh hX
  let Y : ℝ := Real.log X
  let a : ℝ := w0 D X
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hX
  have hY_ne : Y ≠ 0 := ne_of_gt hY_pos
  have ha_lower : Y / 3 ≤ a := by
    have hmul := mul_le_mul_of_nonneg_right hlow (le_of_lt hY_pos)
    calc
      Y / 3 = (1 / 3 : ℝ) * Real.log X := by
        dsimp [Y]
        ring
      _ ≤ (w0 D X / Real.log X) * Real.log X := hmul
      _ = a := by
        dsimp [a]
        field_simp [hY_ne]
        rw [mul_div_cancel_right₀ _ hY_ne]
  have ha_upper : a ≤ (2 / 3 : ℝ) * Y := by
    have hmul := mul_lt_mul_of_pos_right hhigh hY_pos
    exact le_of_lt <| calc
      a = (w0 D X / Real.log X) * Real.log X := by
        dsimp [a]
        field_simp [hY_ne]
        rw [mul_div_cancel_right₀ _ hY_ne]
      _ < (2 / 3 : ℝ) * Real.log X := hmul
      _ = (2 / 3 : ℝ) * Y := by
        dsimp [Y]
  have hab : a ≤ Y := by
    nlinarith [hY_pos]
  have ha_nonneg : 0 ≤ a := by
    have hthird_nonneg : 0 ≤ Y / 3 := by positivity
    exact hthird_nonneg.trans ha_lower
  have hdist : |Y - a| ≤ Y := by
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    linarith
  have hC_nonneg : 0 ≤ 18 * δ / Y ^ 2 := by positivity
  have hnorm_bound :
      ‖∫ w in a..Y,
        ((H B w)⁻¹ - (w⁻¹ + (Real.log w - B) / w ^ 2))‖ ≤
        (18 * δ / Y ^ 2) * |Y - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro w hw
    have hwI : w ∈ Set.Ioc a Y := by
      simpa [Set.uIoc_of_le hab] using hw
    have hw_ge_a : a ≤ w := le_of_lt hwI.1
    have hw_le_Y : w ≤ Y := hwI.2
    have hwT : T ≤ w := hw0T.trans hw_ge_a
    have hw_pos : 0 < w := lt_of_lt_of_le zero_lt_one (hT_one.trans hwT)
    have hw_nonneg : 0 ≤ w := le_of_lt hw_pos
    have hsq_norm := hsqT w (hT_sq.trans hwT)
    have hsq :
        (Real.log w - B) ^ 2 ≤ δ * w := by
      have hsq_nonneg : 0 ≤ (Real.log w - B) ^ 2 := sq_nonneg _
      simpa [Real.norm_eq_abs, abs_of_nonneg hsq_nonneg, abs_of_nonneg hw_nonneg]
        using hsq_norm
    have hH : (1 / 2 : ℝ) * w ≤ H B w := hHT w (hT_H.trans hwT)
    have hrem := H_inv_remainder_abs_le (B := B) (w := w) hw_pos hH hsq
    have hw_lower : Y / 3 ≤ w := ha_lower.trans hw_ge_a
    have hw_sq_lower : (Y / 3) ^ 2 ≤ w ^ 2 := by
      nlinarith [hY_pos, hw_lower]
    have htail :
        2 * δ / w ^ 2 ≤ 18 * δ / Y ^ 2 := by
      have hYthird_pos : 0 < Y / 3 := by positivity
      calc
        2 * δ / w ^ 2 ≤ 2 * δ / ((Y / 3) ^ 2) := by
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hw_sq_lower
        _ = 18 * δ / Y ^ 2 := by
          field_simp [hY_ne]
          ring
    rw [Real.norm_eq_abs]
    exact hrem.trans htail
  calc
    ‖∫ w in w0 D X..Real.log X,
        ((H B w)⁻¹ - (w⁻¹ + (Real.log w - B) / w ^ 2))‖
        = ‖∫ w in a..Y,
            ((H B w)⁻¹ - (w⁻¹ + (Real.log w - B) / w ^ 2))‖ := by
          rfl
    _ ≤ (18 * δ / Y ^ 2) * |Y - a| := hnorm_bound
    _ ≤ (18 * δ / Y ^ 2) * Y := by
          gcongr
    _ = c * ‖(Real.log X)⁻¹‖ := by
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hY_pos)]
          dsimp [δ, Y]
          field_simp [hY_ne]

/-- The integrated geometric remainder in the `1/H` expansion is `o(1 / log X)`. -/
theorem H_inv_remainder_integral_isLittleO (D : PhiPsiData B) :
    (fun X : ℝ =>
      ∫ w in w0 D X..Real.log X,
        ((H B w)⁻¹ - (w⁻¹ + (Real.log w - B) / w ^ 2)))
      =o[Filter.atTop] fun X : ℝ => (Real.log X)⁻¹ := by
  exact IsLittleO.of_bound fun c hc =>
    H_inv_remainder_integral_bound_eventually (D := D) hc

/-- Continuity-derived integrability of the three terms in the `1/H` expansion. -/
private theorem H_inv_remainder_terms_intervalIntegrable_of_tail {B a b T : ℝ}
    (ha : T ≤ a) (hb : T ≤ b) (hT_one : 1 ≤ T)
    (hT_H : ∀ w : ℝ, T ≤ w → 0 < H B w) :
    IntervalIntegrable (fun w : ℝ => (H B w)⁻¹) MeasureTheory.volume a b ∧
      IntervalIntegrable (fun w : ℝ => w⁻¹) MeasureTheory.volume a b ∧
        IntervalIntegrable (fun w : ℝ => (Real.log w - B) / w ^ 2)
          MeasureTheory.volume a b := by
  have hT_of_mem : ∀ w : ℝ, w ∈ Set.uIcc a b → T ≤ w := by
    intro w hw
    exact le_of_endpoints_le_of_mem_uIcc (a := a) (b := b) ha hb hw
  have hpos_of_mem : ∀ w : ℝ, w ∈ Set.uIcc a b → 0 < w := by
    intro w hw
    exact lt_of_lt_of_le zero_lt_one (hT_one.trans (hT_of_mem w hw))
  have hHinv_cont : ContinuousOn (fun w : ℝ => (H B w)⁻¹) (Set.uIcc a b) := by
    intro w hw
    have hw_ne : w ≠ 0 := ne_of_gt (hpos_of_mem w hw)
    have hH_ne : H B w ≠ 0 := ne_of_gt (hT_H w (hT_of_mem w hw))
    have hH_cont : ContinuousAt (H B) w := by
      have hlog : ContinuousAt Real.log w := Real.continuousAt_log hw_ne
      simpa [H] using (continuousAt_id.sub hlog).add continuousAt_const
    exact (hH_cont.inv₀ hH_ne).continuousWithinAt
  have hinv_cont : ContinuousOn (fun w : ℝ => w⁻¹) (Set.uIcc a b) := by
    intro w hw
    exact (continuousAt_id.inv₀ (ne_of_gt (hpos_of_mem w hw))).continuousWithinAt
  have hlog_cont :
      ContinuousOn (fun w : ℝ => (Real.log w - B) / w ^ 2) (Set.uIcc a b) := by
    intro w hw
    have hw_ne : w ≠ 0 := ne_of_gt (hpos_of_mem w hw)
    have hlog : ContinuousAt Real.log w := Real.continuousAt_log hw_ne
    have hnum : ContinuousAt (fun y : ℝ => Real.log y - B) w :=
      hlog.sub continuousAt_const
    have hden_ne : w ^ 2 ≠ 0 := pow_ne_zero 2 hw_ne
    exact (hnum.div (continuousAt_id.pow 2) hden_ne).continuousWithinAt
  exact ⟨hHinv_cont.intervalIntegrable, hinv_cont.intervalIntegrable,
    hlog_cont.intervalIntegrable⟩

private theorem H_inv_remainder_linear_combination_eq_eventually
    (D : PhiPsiData B) :
    ∀ᶠ X : ℝ in Filter.atTop,
      (2 : ℝ) * (∫ w in w0 D X..Real.log X, (H B w)⁻¹) -
          ((2 : ℝ) * (∫ w in w0 D X..Real.log X, w⁻¹) +
            (2 : ℝ) *
              (∫ w in w0 D X..Real.log X, (Real.log w - B) / w ^ 2)) =
        2 * (∫ w in w0 D X..Real.log X,
          ((H B w)⁻¹ - (w⁻¹ + (Real.log w - B) / w ^ 2))) := by
  rcases Filter.eventually_atTop.mp (eventually_H_pos_atTop B) with ⟨TH, hH⟩
  let T : ℝ := max 1 TH
  have hT_one : 1 ≤ T := le_max_left 1 TH
  have hT_H : ∀ w : ℝ, T ≤ w → 0 < H B w := by
    intro w hw
    exact hH w ((le_max_right 1 TH).trans hw)
  filter_upwards [(w0_tendsto_atTop D).eventually_ge_atTop T,
      Real.tendsto_log_atTop.eventually_ge_atTop T] with X hw0 hlog
  rcases H_inv_remainder_terms_intervalIntegrable_of_tail
      (B := B) (a := w0 D X) (b := Real.log X) (T := T)
      hw0 hlog hT_one hT_H with ⟨hHinv, hinv, hlogterm⟩
  have htwoH : IntervalIntegrable (fun w : ℝ => (2 : ℝ) * (H B w)⁻¹)
      MeasureTheory.volume (w0 D X) (Real.log X) := hHinv.const_mul 2
  have htwoInv : IntervalIntegrable (fun w : ℝ => (2 : ℝ) * w⁻¹)
      MeasureTheory.volume (w0 D X) (Real.log X) := hinv.const_mul 2
  have htwoLog :
      IntervalIntegrable (fun w : ℝ => (2 : ℝ) * ((Real.log w - B) / w ^ 2))
        MeasureTheory.volume (w0 D X) (Real.log X) := hlogterm.const_mul 2
  calc
    (2 : ℝ) * (∫ w in w0 D X..Real.log X, (H B w)⁻¹) -
          ((2 : ℝ) * (∫ w in w0 D X..Real.log X, w⁻¹) +
            (2 : ℝ) *
              (∫ w in w0 D X..Real.log X, (Real.log w - B) / w ^ 2))
        =
        (∫ w in w0 D X..Real.log X, (2 : ℝ) * (H B w)⁻¹) -
          ((∫ w in w0 D X..Real.log X, (2 : ℝ) * w⁻¹) +
            (∫ w in w0 D X..Real.log X,
              (2 : ℝ) * ((Real.log w - B) / w ^ 2))) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul]
    _ =
        ∫ w in w0 D X..Real.log X,
          ((2 : ℝ) * (H B w)⁻¹ -
            ((2 : ℝ) * w⁻¹ + (2 : ℝ) * ((Real.log w - B) / w ^ 2))) := by
          rw [← intervalIntegral.integral_add htwoInv htwoLog,
            ← intervalIntegral.integral_sub htwoH (htwoInv.add htwoLog)]
    _ =
        2 * (∫ w in w0 D X..Real.log X,
          ((H B w)⁻¹ - (w⁻¹ + (Real.log w - B) / w ^ 2))) := by
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr ?_
          intro w _hw
          ring

theorem H_inv_remainder_linear_combination_isLittleO (D : PhiPsiData B) :
    (fun X : ℝ =>
      Real.log X *
        ((2 : ℝ) * (∫ w in w0 D X..Real.log X, (H B w)⁻¹) -
          ((2 : ℝ) * (∫ w in w0 D X..Real.log X, w⁻¹) +
            (2 : ℝ) *
              (∫ w in w0 D X..Real.log X, (Real.log w - B) / w ^ 2))))
      =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
  refine IsLittleO.of_bound fun c hc => ?_
  have hc_half : 0 < c / 2 := by positivity
  filter_upwards [H_inv_remainder_integral_bound_eventually (D := D) hc_half,
      H_inv_remainder_linear_combination_eq_eventually D,
      eventually_gt_atTop (1 : ℝ)] with X hbound hlin hX
  have hY_pos : 0 < Real.log X := Real.log_pos hX
  have hY_nonneg : 0 ≤ Real.log X := le_of_lt hY_pos
  have hY_inv_abs : ‖(Real.log X)⁻¹‖ = (Real.log X)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hY_pos)]
  calc
    ‖Real.log X *
        ((2 : ℝ) * (∫ w in w0 D X..Real.log X, (H B w)⁻¹) -
          ((2 : ℝ) * (∫ w in w0 D X..Real.log X, w⁻¹) +
            (2 : ℝ) *
              (∫ w in w0 D X..Real.log X, (Real.log w - B) / w ^ 2)))‖
        =
        ‖Real.log X *
          (2 * (∫ w in w0 D X..Real.log X,
            ((H B w)⁻¹ - (w⁻¹ + (Real.log w - B) / w ^ 2))))‖ := by
          rw [hlin]
    _ = Real.log X *
        (2 * ‖∫ w in w0 D X..Real.log X,
          ((H B w)⁻¹ - (w⁻¹ + (Real.log w - B) / w ^ 2))‖) := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hY_nonneg]
          norm_num
    _ ≤ Real.log X * (2 * ((c / 2) * ‖(Real.log X)⁻¹‖)) := by
          gcongr
    _ = c * ‖(fun _ : ℝ => (1 : ℝ)) X‖ := by
          rw [hY_inv_abs]
          simp
          field_simp [ne_of_gt hY_pos]

/-- Exact reciprocal-denominator split on intervals contained in a positive tail. -/
theorem H_inverse_integral_split_of_tail {B a b T : ℝ}
    (ha : T ≤ a) (hb : T ≤ b) (hT_one : 1 ≤ T)
    (hT_H : ∀ w : ℝ, T ≤ w → 0 < H B w) :
    ∫ w in a..b, (2 / H B w - Hderiv w / (H B w) ^ 2) =
      2 * (∫ w in a..b, (H B w)⁻¹) + (H B b)⁻¹ - (H B a)⁻¹ := by
  have hT_of_mem : ∀ w : ℝ, w ∈ Set.uIcc a b → T ≤ w := by
    intro w hw
    exact le_of_endpoints_le_of_mem_uIcc (a := a) (b := b) ha hb hw
  have hcontInv : ContinuousOn (fun w : ℝ => (H B w)⁻¹) (Set.uIcc a b) := by
    intro w hw
    have hwT : T ≤ w := hT_of_mem w hw
    have hw_ne : w ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hT_one.trans hwT))
    have hH_ne : H B w ≠ 0 := ne_of_gt (hT_H w hwT)
    have hH_cont : ContinuousAt (H B) w := by
      have hlog : ContinuousAt Real.log w := Real.continuousAt_log hw_ne
      simpa [H] using (continuousAt_id.sub hlog).add continuousAt_const
    exact (hH_cont.inv₀ hH_ne).continuousWithinAt
  have hcontNegDeriv :
      ContinuousOn (fun w : ℝ => -(Hderiv w) / (H B w) ^ 2) (Set.uIcc a b) := by
    intro w hw
    have hwT : T ≤ w := hT_of_mem w hw
    have hw_ne : w ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hT_one.trans hwT))
    have hH_ne : H B w ≠ 0 := ne_of_gt (hT_H w hwT)
    have hH_cont : ContinuousAt (H B) w := by
      have hlog : ContinuousAt Real.log w := Real.continuousAt_log hw_ne
      simpa [H] using (continuousAt_id.sub hlog).add continuousAt_const
    have hderiv_cont : ContinuousAt Hderiv w := by
      change ContinuousAt (fun y : ℝ => 1 - 1 / y) w
      have hone : ContinuousAt (fun _ : ℝ => (1 : ℝ)) w := continuousAt_const
      have hinv : ContinuousAt (fun y : ℝ => 1 / y) w :=
        hone.div continuousAt_id hw_ne
      exact hone.sub hinv
    have hden_ne : (H B w) ^ 2 ≠ 0 := pow_ne_zero 2 hH_ne
    exact (hderiv_cont.neg.div (hH_cont.pow 2) hden_ne).continuousWithinAt
  have hinv_int : IntervalIntegrable (fun w : ℝ => (H B w)⁻¹) MeasureTheory.volume a b :=
    hcontInv.intervalIntegrable
  have htwo_int : IntervalIntegrable (fun w : ℝ => 2 / H B w) MeasureTheory.volume a b := by
    simpa [div_eq_mul_inv] using hinv_int.const_mul (2 : ℝ)
  have hneg_int :
      IntervalIntegrable (fun w : ℝ => -(Hderiv w) / (H B w) ^ 2)
        MeasureTheory.volume a b :=
    hcontNegDeriv.intervalIntegrable
  have hFTC :
      ∫ w in a..b, (-(Hderiv w) / (H B w) ^ 2) = (H B b)⁻¹ - (H B a)⁻¹ := by
    have hderiv : ∀ w ∈ Set.uIcc a b,
        HasDerivAt (fun z : ℝ => (H B z)⁻¹) (-(Hderiv w) / (H B w) ^ 2) w := by
      intro w hw
      have hwT : T ≤ w := hT_of_mem w hw
      have hw_ne : w ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hT_one.trans hwT))
      have hH_ne : H B w ≠ 0 := ne_of_gt (hT_H w hwT)
      exact H_inv_hasDerivAt (B := B) hw_ne hH_ne
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hneg_int
  have htwo_eq :
      (∫ w in a..b, 2 / H B w) = 2 * (∫ w in a..b, (H B w)⁻¹) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro w _hw
    simp [div_eq_mul_inv]
  calc
    ∫ w in a..b, (2 / H B w - Hderiv w / (H B w) ^ 2) =
        ∫ w in a..b, (2 / H B w + (-(Hderiv w) / (H B w) ^ 2)) := by
      refine intervalIntegral.integral_congr ?_
      intro w _hw
      ring
    _ = (∫ w in a..b, 2 / H B w) +
          (∫ w in a..b, (-(Hderiv w) / (H B w) ^ 2)) := by
      exact intervalIntegral.integral_add htwo_int hneg_int
    _ = 2 * (∫ w in a..b, (H B w)⁻¹) + ((H B b)⁻¹ - (H B a)⁻¹) := by
      rw [htwo_eq, hFTC]
    _ = 2 * (∫ w in a..b, (H B w)⁻¹) + (H B b)⁻¹ - (H B a)⁻¹ := by
      ring

/-- Exact `(1/H)'` split for the transformed square-integral bracket. -/
theorem transformed_square_integral_split_exact
    (D : PhiPsiData B) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∫ w in w0 D X..Real.log X,
          (2 / H B w - Hderiv w / (H B w) ^ 2) =
        2 * (∫ w in w0 D X..Real.log X, (H B w)⁻¹) +
          (H B (Real.log X))⁻¹ - (H B (w0 D X))⁻¹ := by
  rcases Filter.eventually_atTop.mp (eventually_H_pos_atTop B) with ⟨TH, hH⟩
  let T : ℝ := max 1 TH
  have hT_one : 1 ≤ T := le_max_left 1 TH
  have hT_H : ∀ w : ℝ, T ≤ w → 0 < H B w := by
    intro w hw
    exact hH w ((le_max_right 1 TH).trans hw)
  filter_upwards [(w0_tendsto_atTop D).eventually_ge_atTop T,
      Real.tendsto_log_atTop.eventually_ge_atTop T] with X hw0 hlog
  exact H_inverse_integral_split_of_tail (B := B) (a := w0 D X)
    (b := Real.log X) (T := T) hw0 hlog hT_one hT_H

/-- The upper transformed endpoint reciprocal is asymptotic to `1 / log X`. -/
theorem H_log_div_log_tendsto_one (B : ℝ) :
    Tendsto (fun X : ℝ => H B (Real.log X) / Real.log X)
      Filter.atTop (𝓝 (1 : ℝ)) := by
  have hden_ne : ∀ᶠ X : ℝ in Filter.atTop, Real.log X ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact ne_of_gt (Real.log_pos hX)
  have heqv :
      (fun X : ℝ => H B (Real.log X)) ~[Filter.atTop]
        fun X : ℝ => Real.log X :=
    (H_isEquivalent_atTop B).comp_tendsto Real.tendsto_log_atTop
  simpa [Pi.div_apply] using (isEquivalent_iff_tendsto_one hden_ne).mp heqv

/-- Normalized upper-endpoint reciprocal limit. -/
theorem log_mul_H_log_inv_tendsto_one (B : ℝ) :
    Tendsto (fun X : ℝ => Real.log X * (H B (Real.log X))⁻¹)
      Filter.atTop (𝓝 (1 : ℝ)) := by
  have hratio := H_log_div_log_tendsto_one B
  have hinv :
      Tendsto (fun X : ℝ => (H B (Real.log X) / Real.log X)⁻¹)
        Filter.atTop (𝓝 ((1 : ℝ)⁻¹)) :=
    hratio.inv₀ (by norm_num)
  have htarget :
      Tendsto (fun X : ℝ => Real.log X * (H B (Real.log X))⁻¹)
        Filter.atTop (𝓝 ((1 : ℝ)⁻¹)) := by
    refine hinv.congr' ?_
    filter_upwards [eventually_H_log_pos_atTop B, eventually_gt_atTop (1 : ℝ)] with
      X hH hX
    have hH_ne : H B (Real.log X) ≠ 0 := ne_of_gt hH
    have hlog_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
    field_simp [hH_ne, hlog_ne]
  simpa using htarget

/-- Normalized lower-endpoint reciprocal limit. -/
theorem log_mul_H_w0_inv_tendsto_two (D : PhiPsiData B) :
    Tendsto (fun X : ℝ => Real.log X * (H B (w0 D X))⁻¹)
      Filter.atTop (𝓝 (2 : ℝ)) := by
  have hratio := H_w0_div_log_tendsto_half D
  have hinv :
      Tendsto (fun X : ℝ => (H B (w0 D X) / Real.log X)⁻¹)
        Filter.atTop (𝓝 (((1 / 2 : ℝ))⁻¹)) :=
    hratio.inv₀ (by norm_num)
  have htarget :
      Tendsto (fun X : ℝ => Real.log X * (H B (w0 D X))⁻¹)
        Filter.atTop (𝓝 (((1 / 2 : ℝ))⁻¹)) := by
    refine hinv.congr' ?_
    filter_upwards [(w0_tendsto_atTop D).eventually (eventually_H_pos_atTop B),
        eventually_gt_atTop (1 : ℝ)] with X hH hX
    have hH_ne : H B (w0 D X) ≠ 0 := ne_of_gt hH
    have hlog_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
    field_simp [hH_ne, hlog_ne]
  simpa using htarget

/-- Endpoint contribution in the transformed square bracket. -/
theorem H_inv_endpoint_diff_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      Real.log X * ((H B (Real.log X))⁻¹ - (H B (w0 D X))⁻¹) + 1)
      =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
  have hupper := log_mul_H_log_inv_tendsto_one B
  have hlower := log_mul_H_w0_inv_tendsto_two D
  have hdiff :
      Tendsto
        (fun X : ℝ => Real.log X * (H B (Real.log X))⁻¹ -
          Real.log X * (H B (w0 D X))⁻¹)
        Filter.atTop (𝓝 ((1 : ℝ) - 2)) :=
    hupper.sub hlower
  have hmain :
      Tendsto
        (fun X : ℝ =>
          (Real.log X * (H B (Real.log X))⁻¹ -
            Real.log X * (H B (w0 D X))⁻¹) + 1)
        Filter.atTop (𝓝 (((1 : ℝ) - 2) + 1)) :=
    hdiff.add tendsto_const_nhds
  refine (isLittleO_one_iff ℝ).mpr ?_
  have hmain0 :
      Tendsto
        (fun X : ℝ =>
          (Real.log X * (H B (Real.log X))⁻¹ -
            Real.log X * (H B (w0 D X))⁻¹) + 1)
        Filter.atTop (𝓝 0) := by
    have hlim : ((1 : ℝ) - 2) + 1 = 0 := by norm_num
    simpa [hlim] using hmain
  refine hmain0.congr' ?_
  filter_upwards [] with X
  ring

/-- Cancellation of the explicit endpoint-displacement coefficient in the square bracket. -/
theorem rX_square_bracket_coefficient_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      -4 * rX D X +
        (2 * Real.log (Real.log X) - 4 * Real.log 2 + 2 - 2 * B) - 1 -
          (1 - 2 * B + 2 * Real.log (lam / 2)))
      =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
  have h := (rX_asymptotic D).const_mul_left (-4 : ℝ)
  refine h.congr_left ?_
  intro X
  have hlam : 0 < lam := by
    unfold lam
    positivity
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hlam)]
  rw [Real.log_div (ne_of_gt hlam) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/--
Assembly of the transformed square bracket from the named geometric `1/H` remainder.

This keeps the only missing estimate explicit: the expansion of `1/H` into
`1/w + (log w - B)/w^2` on the square-change window.
-/
theorem transformed_square_bracket_asymptotic_of_H_inv_remainder
    (D : PhiPsiData B)
    (hrem :
      (fun X : ℝ =>
        Real.log X *
          ((2 : ℝ) * (∫ w in w0 D X..Real.log X, (H B w)⁻¹) -
            ((2 : ℝ) * (∫ w in w0 D X..Real.log X, w⁻¹) +
              (2 : ℝ) *
                (∫ w in w0 D X..Real.log X, (Real.log w - B) / w ^ 2))))
        =o[Filter.atTop] fun _ : ℝ => (1 : ℝ)) :
    (fun X : ℝ =>
      Real.log X *
        ((∫ w in w0 D X..Real.log X,
          (2 / H B w - Hderiv w / (H B w)^2)) - 2 * Real.log 2)
        - (1 - 2 * B + 2 * Real.log (lam / 2)))
      =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
  let invTerm : ℝ → ℝ := fun X => ∫ w in w0 D X..Real.log X, w⁻¹
  let logTerm : ℝ → ℝ := fun X =>
    ∫ w in w0 D X..Real.log X, (Real.log w - B) / w ^ 2
  let HinvTerm : ℝ → ℝ := fun X => ∫ w in w0 D X..Real.log X, (H B w)⁻¹
  let endpoint : ℝ → ℝ := fun X => (H B (Real.log X))⁻¹ - (H B (w0 D X))⁻¹
  have htwo := two_inv_integral_asymptotic D
  have hlog := log_sub_const_div_sq_integral_asymptotic D
  have hend := H_inv_endpoint_diff_asymptotic D
  have hcoef := rX_square_bracket_coefficient_asymptotic D
  have hsum :
      (fun X : ℝ =>
        Real.log X *
          ((2 : ℝ) * HinvTerm X - ((2 : ℝ) * invTerm X + (2 : ℝ) * logTerm X)) +
          (Real.log X * ((2 : ℝ) * invTerm X - 2 * Real.log 2) + 4 * rX D X) +
          (Real.log X * ((2 : ℝ) * logTerm X) -
            (2 * Real.log (Real.log X) - 4 * Real.log 2 + 2 - 2 * B)) +
          (Real.log X * endpoint X + 1) +
          (-4 * rX D X +
            (2 * Real.log (Real.log X) - 4 * Real.log 2 + 2 - 2 * B) - 1 -
              (1 - 2 * B + 2 * Real.log (lam / 2))))
        =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
    have hrem' :
        (fun X : ℝ =>
          Real.log X *
            ((2 : ℝ) * HinvTerm X - ((2 : ℝ) * invTerm X + (2 : ℝ) * logTerm X)))
          =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
      simpa [HinvTerm, invTerm, logTerm] using hrem
    have htwo' :
        (fun X : ℝ => Real.log X * ((2 : ℝ) * invTerm X - 2 * Real.log 2) +
          4 * rX D X) =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
      simpa [invTerm] using htwo
    have hlog' :
        (fun X : ℝ => Real.log X * ((2 : ℝ) * logTerm X) -
          (2 * Real.log (Real.log X) - 4 * Real.log 2 + 2 - 2 * B))
          =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
      simpa [logTerm] using hlog
    have hend' :
        (fun X : ℝ => Real.log X * endpoint X + 1)
          =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
      simpa [endpoint] using hend
    exact (((hrem'.add htwo').add hlog').add hend').add hcoef
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards [transformed_square_integral_split_exact D] with X hsplit
  rw [hsplit]
  dsimp [HinvTerm, invTerm, logTerm, endpoint]
  ring

/-- The transformed square bracket after the `1/H` expansion and endpoint cancellation. -/
theorem transformed_square_bracket_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      Real.log X *
        ((∫ w in w0 D X..Real.log X,
          (2 / H B w - Hderiv w / (H B w)^2)) - 2 * Real.log 2)
        - (1 - 2 * B + 2 * Real.log (lam / 2)))
      =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) :=
  transformed_square_bracket_asymptotic_of_H_inv_remainder D
    (H_inv_remainder_linear_combination_isLittleO D)

/-- Exact square-change formula for the square part of the large continuous integral. -/
theorem f_sq_integral_square_change_exact
    (D : PhiPsiData B) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∫ t in X..D.Phi X, (D.f t) ^ 2 =
        lam * ∫ w in w0 D X..Real.log X,
          (2 / H B w - Hderiv w / (H B w) ^ 2) := by
  let phiDeriv : ℝ → ℝ := fun w =>
    lam * Real.exp (2 * w) * (2 / H B w - Hderiv w / (H B w) ^ 2)
  have hderiv_ev :
      ∀ᶠ w : ℝ in Filter.atTop, HasDerivAt (PhiLog B) (phiDeriv w) w := by
    simpa [phiDeriv] using PhiLog_hasDerivAt_eventually B
  have hnonneg_ev :
      ∀ᶠ w : ℝ in Filter.atTop, 0 ≤ phiDeriv w := by
    simpa [phiDeriv] using PhiLog_deriv_nonneg_eventually B
  rcases Filter.eventually_atTop.mp hderiv_ev with ⟨Tder, hderT⟩
  rcases Filter.eventually_atTop.mp hnonneg_ev with ⟨Tpos, hposT⟩
  rcases Filter.eventually_atTop.mp (f_Phi_exp_eq D) with ⟨Tf, hfT⟩
  let T : ℝ := max Tder (max Tpos Tf)
  have hT_der : ∀ w : ℝ, T ≤ w → HasDerivAt (PhiLog B) (phiDeriv w) w := by
    intro w hw
    exact hderT w ((le_max_left Tder (max Tpos Tf)).trans hw)
  have hT_nonneg : ∀ w : ℝ, T ≤ w → 0 ≤ phiDeriv w := by
    intro w hw
    exact hposT w ((le_max_left Tpos Tf).trans
      ((le_max_right Tder (max Tpos Tf)).trans hw))
  have hT_f : ∀ w : ℝ, T ≤ w → D.f (D.Phi (Real.exp w)) = Real.exp (-w) := by
    intro w hw
    exact hfT w ((le_max_right Tpos Tf).trans
      ((le_max_right Tder (max Tpos Tf)).trans hw))
  filter_upwards [(w0_tendsto_atTop D).eventually_ge_atTop T,
      Real.tendsto_log_atTop.eventually_ge_atTop T,
      Phi_exp_w0_eq_self_eventually D,
      Phi_exp_log_eq_Phi_eventually D] with X hw0T hlogT hlow hup
  let a : ℝ := w0 D X
  let b : ℝ := Real.log X
  have hge_uIcc : ∀ w : ℝ, w ∈ Set.uIcc a b → T ≤ w := by
    intro w hw
    exact le_of_endpoints_le_of_mem_uIcc (a := a) (b := b) hw0T hlogT hw
  have hcont : ContinuousOn (PhiLog B) (Set.uIcc a b) := by
    intro w hw
    exact (hT_der w (hge_uIcc w hw)).continuousAt.continuousWithinAt
  have hderiv :
      ∀ w ∈ Set.Ioo (min a b) (max a b), HasDerivAt (PhiLog B) (phiDeriv w) w := by
    intro w hw
    exact hT_der w (hge_uIcc w (mem_uIcc_of_mem_Ioo_min_max hw))
  have hnonneg :
      ∀ w ∈ Set.Ioo (min a b) (max a b), 0 ≤ phiDeriv w := by
    intro w hw
    exact hT_nonneg w (hge_uIcc w (mem_uIcc_of_mem_Ioo_min_max hw))
  have hsubst :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := a) (b := b) (f := PhiLog B) (f' := phiDeriv)
      (g := fun t : ℝ => (D.f t) ^ 2) hcont hderiv hnonneg
  have hlow' : PhiLog B a = X := by
    dsimp [a]
    rw [PhiLog, ← D.Phi_eq (Real.exp (w0 D X))]
    exact hlow
  have hup' : PhiLog B b = D.Phi X := by
    dsimp [b]
    rw [PhiLog, ← D.Phi_eq (Real.exp (Real.log X))]
    exact hup
  have hleft :
      ∫ w in a..b, ((fun t : ℝ => (D.f t) ^ 2) ∘ PhiLog B) w * phiDeriv w =
        lam * ∫ w in a..b, (2 / H B w - Hderiv w / (H B w) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro w hw
    have hwu : w ∈ Set.uIcc a b := hw
    have hf : D.f (D.Phi (Real.exp w)) = Real.exp (-w) :=
      hT_f w (hge_uIcc w hwu)
    have hexp : (Real.exp (-w)) ^ 2 * Real.exp (2 * w) = 1 := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      ring_nf
      simp
    dsimp [Function.comp, PhiLog, phiDeriv]
    rw [← D.Phi_eq (Real.exp w), hf]
    calc
      (Real.exp (-w)) ^ 2 *
          (lam * Real.exp (2 * w) * (2 / H B w - Hderiv w / (H B w) ^ 2)) =
          lam * (((Real.exp (-w)) ^ 2 * Real.exp (2 * w)) *
            (2 / H B w - Hderiv w / (H B w) ^ 2)) := by
        ring
      _ = lam * (1 * (2 / H B w - Hderiv w / (H B w) ^ 2)) := by
        rw [hexp]
      _ = lam * (2 / H B w - Hderiv w / (H B w) ^ 2) := by
        ring
  calc
    ∫ t in X..D.Phi X, (D.f t) ^ 2 =
        ∫ t in PhiLog B a..PhiLog B b, (D.f t) ^ 2 := by
      rw [hlow', hup']
    _ = ∫ w in a..b, ((fun t : ℝ => (D.f t) ^ 2) ∘ PhiLog B) w * phiDeriv w :=
      hsubst.symm
    _ = lam * ∫ w in a..b, (2 / H B w - Hderiv w / (H B w) ^ 2) :=
      hleft

/-- Constant identity behind the leading term in the square integral. -/
theorem lam_mul_two_log_two : lam * (2 * Real.log 2) = 1 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  unfold lam
  field_simp [hlog]

/-- The square part of the large continuous integral has the required second-order expansion. -/
theorem f_sq_integral_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      (∫ t in X..D.Phi X, (D.f t) ^ 2) -
        (1 + lam * (1 - 2 * B + 2 * Real.log (lam / 2)) / Real.log X))
      =o[Filter.atTop] fun X : ℝ => (Real.log X)⁻¹ := by
  let C : ℝ := 1 - 2 * B + 2 * Real.log (lam / 2)
  let A : ℝ → ℝ := fun X =>
    ∫ w in w0 D X..Real.log X, (2 / H B w - Hderiv w / (H B w) ^ 2)
  let e : ℝ → ℝ := fun X => Real.log X * (A X - 2 * Real.log 2) - C
  have hbr : e =o[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
    simpa [e, A, C] using transformed_square_bracket_asymptotic D
  have hlam_pos : 0 < lam := by
    unfold lam
    positivity
  refine IsLittleO.of_bound fun c hc => ?_
  have hc_lam : 0 < c / lam := div_pos hc hlam_pos
  filter_upwards [hbr.def hc_lam, f_sq_integral_square_change_exact D,
      eventually_gt_atTop (1 : ℝ)] with X he hsq hX
  have hlog_pos : 0 < Real.log X := Real.log_pos hX
  have hlog_ne : Real.log X ≠ 0 := ne_of_gt hlog_pos
  rw [hsq]
  have halg :
      lam * A X - (1 + lam * C / Real.log X) =
        lam * (e X * (Real.log X)⁻¹) := by
    dsimp [e, C]
    field_simp [hlog_ne]
    nlinarith [congrArg (fun z : ℝ => z * Real.log X) lam_mul_two_log_two]
  calc
    ‖lam * A X - (1 + lam * C / Real.log X)‖
        = ‖lam * (e X * (Real.log X)⁻¹)‖ := by rw [halg]
    _ = lam * ‖e X‖ * ‖(Real.log X)⁻¹‖ := by
          rw [norm_mul, norm_mul, Real.norm_of_nonneg (le_of_lt hlam_pos)]
          ring_nf
    _ ≤ lam * ((c / lam) * ‖(fun _ : ℝ => (1 : ℝ)) X‖) *
          ‖(Real.log X)⁻¹‖ := by
          gcongr
    _ = c * ‖(Real.log X)⁻¹‖ := by
          rw [show ‖(fun _ : ℝ => (1 : ℝ)) X‖ = 1 by norm_num]
          field_simp [ne_of_gt hlam_pos]

/-- The square-integral contribution after multiplying by `X`. -/
theorem square_integral_term_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      X * (∫ t in X..D.Phi X, (D.f t) ^ 2) -
        (X + lam * (1 - 2 * B + 2 * Real.log (lam / 2)) * X / Real.log X))
      =o[Filter.atTop] scaleReal := by
  let C : ℝ := 1 - 2 * B + 2 * Real.log (lam / 2)
  have hsq := f_sq_integral_asymptotic (D := D)
  refine IsLittleO.of_bound fun c hc => ?_
  filter_upwards [hsq.def hc, eventually_gt_atTop (1 : ℝ)] with X hbound hX
  have hX_pos : 0 < X := lt_trans zero_lt_one hX
  have hlog_pos : 0 < Real.log X := Real.log_pos hX
  have hlog_ne : Real.log X ≠ 0 := ne_of_gt hlog_pos
  have hscale_pos : 0 < scaleReal X := by
    rw [scaleReal]
    exact div_pos hX_pos hlog_pos
  have halg :
      X * (∫ t in X..D.Phi X, (D.f t) ^ 2) -
          (X + lam * C * X / Real.log X) =
        X * ((∫ t in X..D.Phi X, (D.f t) ^ 2) -
          (1 + lam * C / Real.log X)) := by
    field_simp [hlog_ne]
  calc
    ‖X * (∫ t in X..D.Phi X, (D.f t) ^ 2) -
        (X + lam * (1 - 2 * B + 2 * Real.log (lam / 2)) * X / Real.log X)‖
        =
        ‖X * ((∫ t in X..D.Phi X, (D.f t) ^ 2) -
          (1 + lam * C / Real.log X))‖ := by
          rw [halg]
    _ = X * ‖(∫ t in X..D.Phi X, (D.f t) ^ 2) -
          (1 + lam * C / Real.log X)‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos hX_pos]
    _ ≤ X * (c * ‖(Real.log X)⁻¹‖) := by
          gcongr
    _ = c * ‖scaleReal X‖ := by
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlog_pos)]
          rw [show ‖scaleReal X‖ = scaleReal X by
            rw [Real.norm_eq_abs, abs_of_pos hscale_pos]]
          rw [scaleReal]
          field_simp [hlog_ne]

/-- Eventual wrapper for the continuous integral split. -/
theorem continuous_integral_square_correction_split
    (D : PhiPsiData B) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∫ t in X..D.Phi X, D.f t * GX D X t =
        X * (∫ t in X..D.Phi X, (D.f t) ^ 2) + Rcorr D X := by
  filter_upwards [eventually_ge_atTop (0 : ℝ), Phi_dominates_fixed_multiple D 1] with
    X hX_nonneg hXPhi
  have hXPhi' : X ≤ D.Phi X := by
    simpa using hXPhi
  simpa using continuous_integral_square_correction_split_of_nonneg D hX_nonneg hXPhi'

/-- Constant algebra for assembling the three continuous-majorant contributions. -/
theorem continuous_coefficient_identity (B : ℝ) :
    4 * lam + lam * (1 - 2 * B + 2 * Real.log (lam / 2)) +
        2 * lam * (2 * Real.log 2 - 1) =
      lam * (3 - 2 * B - 2 * Real.log (Real.log 2)) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hfour_ne : (4 : ℝ) ≠ 0 := by norm_num
  have hlog_lam_div_two : Real.log (lam / 2) = -Real.log 4 - Real.log (Real.log 2) := by
    unfold lam
    calc
      Real.log ((1 / (2 * Real.log 2)) / 2) = Real.log (((4 : ℝ) * Real.log 2)⁻¹) := by
        congr 1
        field_simp [hlog2_ne]
        ring
      _ = -Real.log ((4 : ℝ) * Real.log 2) := by
        rw [Real.log_inv]
      _ = -(Real.log 4 + Real.log (Real.log 2)) := by
        rw [Real.log_mul hfour_ne hlog2_ne]
      _ = -Real.log 4 - Real.log (Real.log 2) := by ring
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [Real.log_pow]
    norm_num
  rw [hlog_lam_div_two, hlog4]
  ring

end FloorSaving
