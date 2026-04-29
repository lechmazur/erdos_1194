import FloorSaving.PhiPsiConstruction
import FloorSaving.AnalyticDefinitions

noncomputable section

open Filter Topology Asymptotics
open scoped Real

namespace FloorSaving

/-- On the real tail, `H B w = w - log w + B` is asymptotic to `w`. -/
theorem H_isEquivalent_atTop (B : ℝ) :
    (fun w : ℝ => H B w) ~[Filter.atTop] fun w : ℝ => w := by
  have hlog : (fun w : ℝ => Real.log w) =o[Filter.atTop] fun w : ℝ => w :=
    Real.isLittleO_log_id_atTop
  have hsmall :
      (fun w : ℝ => -Real.log w + B) =o[Filter.atTop] fun w : ℝ => w :=
    hlog.neg_left.add (isLittleO_const_id_atTop B)
  rw [Asymptotics.IsEquivalent]
  convert hsmall using 1
  funext w
  simp [H]
  ring

/-- First-order pointwise model for `f`. -/
noncomputable def fModel (t : ℝ) : ℝ :=
  Real.sqrt (2 * lam / (t * Real.log t))

/-- First-order primitive model for `∫₀ˣ f`. -/
noncomputable def IModel (X : ℝ) : ℝ :=
  2 * Real.sqrt (2 * lam * X / Real.log X)

/-- Eventual derivative model for `IModel`. -/
noncomputable def IModelDeriv (X : ℝ) : ℝ :=
  fModel X * (1 - 1 / Real.log X)

/-- The square of the model function in `f_asymptotic` is eventually nonnegative. -/
theorem eventually_f_sq_model_nonneg :
    ∀ᶠ t : ℝ in Filter.atTop, 0 ≤ 2 * lam / (t * Real.log t) := by
  have hlam : 0 < lam := by
    unfold lam
    positivity
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have ht_pos : 0 < t := lt_trans zero_lt_one ht
  have hlog_pos : 0 < Real.log t := Real.log_pos ht
  positivity

/-- The pointwise model for `f` is positive on the tail `1 < t`. -/
theorem fModel_pos_of_one_lt {t : ℝ} (ht : 1 < t) :
    0 < fModel t := by
  have ht_pos : 0 < t := lt_trans zero_lt_one ht
  have hlog_pos : 0 < Real.log t := Real.log_pos ht
  rw [fModel, Real.sqrt_pos]
  have hlam : 0 < lam := by
    unfold lam
    positivity
  positivity

/-- The pointwise model for `f` is eventually positive. -/
theorem eventually_fModel_pos :
    ∀ᶠ t : ℝ in Filter.atTop, 0 < fModel t := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  exact fModel_pos_of_one_lt ht

/-- Square of the pointwise model on the tail `1 < t`. -/
theorem fModel_sq_of_one_lt {t : ℝ} (ht : 1 < t) :
    fModel t ^ 2 = 2 * lam / (t * Real.log t) := by
  have ht_pos : 0 < t := lt_trans zero_lt_one ht
  have hlog_pos : 0 < Real.log t := Real.log_pos ht
  rw [fModel, Real.sq_sqrt]
  have hlam : 0 < lam := by
    unfold lam
    positivity
  positivity

/-- The pointwise model is uniformly comparable on any fixed multiplicative window. -/
theorem fModel_local_comparability {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ C T : ℝ, 0 < C ∧
      ∀ ⦃s t : ℝ⦄, T ≤ t → c * t ≤ s → s ≤ t →
        fModel s ≤ C * fModel t := by
  let C : ℝ := 2 / c
  let T : ℝ := max (Real.exp (-2 * Real.log c)) (max (2 / c) 2)
  refine ⟨C, T, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro s t ht hcts _hst
    have hT_exp : Real.exp (-2 * Real.log c) ≤ t := by
      exact le_trans (le_max_left _ _) ht
    have hT_c : 2 / c ≤ t := by
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
    have hT_two : (2 : ℝ) ≤ t := by
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
    have ht_one : 1 < t := by linarith
    have ht_pos : 0 < t := lt_trans zero_lt_one ht_one
    have hct_ge_two : (2 : ℝ) ≤ c * t := by
      have hmul := mul_le_mul_of_nonneg_left hT_c (le_of_lt hc0)
      have hc_ne : c ≠ 0 := ne_of_gt hc0
      have hleft : c * (2 / c) = 2 := by field_simp [hc_ne]
      nlinarith
    have hs_ge_two : (2 : ℝ) ≤ s := le_trans hct_ge_two hcts
    have hs_one : 1 < s := by linarith
    have hs_pos : 0 < s := lt_trans zero_lt_one hs_one
    have hlog_t_pos : 0 < Real.log t := Real.log_pos ht_one
    have hlog_t_ge : -2 * Real.log c ≤ Real.log t :=
      (Real.le_log_iff_exp_le ht_pos).2 hT_exp
    have hlog_ct_ge_half :
        (1 / 2 : ℝ) * Real.log t ≤ Real.log (c * t) := by
      have hc_ne : c ≠ 0 := ne_of_gt hc0
      have ht_ne : t ≠ 0 := ne_of_gt ht_pos
      rw [Real.log_mul hc_ne ht_ne]
      nlinarith
    have hct_pos : 0 < c * t := mul_pos hc0 ht_pos
    have hlog_ct_le_s : Real.log (c * t) ≤ Real.log s :=
      Real.log_le_log hct_pos hcts
    have hlog_s_ge_half :
        (1 / 2 : ℝ) * Real.log t ≤ Real.log s :=
      le_trans hlog_ct_ge_half hlog_ct_le_s
    have hden_lower :
        (c / 2) * (t * Real.log t) ≤ s * Real.log s := by
      have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) * Real.log t := by positivity
      have hmul := mul_le_mul hcts hlog_s_ge_half hhalf_nonneg (le_of_lt hs_pos)
      convert hmul using 1
      ring
    have hden_t_pos : 0 < t * Real.log t := by positivity
    have hden_lower_pos : 0 < (c / 2) * (t * Real.log t) := by positivity
    have hA_nonneg : 0 ≤ 2 * lam := by
      unfold lam
      positivity
    have hratio :
        2 * lam / (s * Real.log s) ≤ C * (2 * lam / (t * Real.log t)) := by
      calc
        2 * lam / (s * Real.log s)
            ≤ 2 * lam / ((c / 2) * (t * Real.log t)) :=
              div_le_div_of_nonneg_left hA_nonneg hden_lower_pos hden_lower
        _ = C * (2 * lam / (t * Real.log t)) := by
          dsimp [C]
          field_simp [ne_of_gt hc0, ne_of_gt hden_t_pos]
    have hC_ge_one : 1 ≤ C := by
      dsimp [C]
      rw [le_div_iff₀ hc0]
      linarith
    have hC_sq_ge : C ≤ C ^ 2 := by
      nlinarith
    have hf_t_sq_nonneg : 0 ≤ fModel t ^ 2 := sq_nonneg _
    have hs_sq := fModel_sq_of_one_lt hs_one
    have ht_sq := fModel_sq_of_one_lt ht_one
    have hsq_le : fModel s ^ 2 ≤ (C * fModel t) ^ 2 := by
      calc
        fModel s ^ 2 = 2 * lam / (s * Real.log s) := hs_sq
        _ ≤ C * (2 * lam / (t * Real.log t)) := hratio
        _ = C * fModel t ^ 2 := by rw [ht_sq]
        _ ≤ C ^ 2 * fModel t ^ 2 :=
          mul_le_mul_of_nonneg_right hC_sq_ge hf_t_sq_nonneg
        _ = (C * fModel t) ^ 2 := by ring
    have hs_nonneg : 0 ≤ fModel s := le_of_lt (fModel_pos_of_one_lt hs_one)
    have hright_nonneg : 0 ≤ C * fModel t := by
      have hC_pos : 0 < C := by
        dsimp [C]
        positivity
      exact mul_nonneg (le_of_lt hC_pos) (le_of_lt (fModel_pos_of_one_lt ht_one))
    exact (sq_le_sq₀ hs_nonneg hright_nonneg).1 hsq_le

/-- Model integrand for the elementary tail integral bound. -/
noncomputable def invSqrtLogModel (t : ℝ) : ℝ :=
  1 / Real.sqrt (t * Real.log t)

/-- Primitive model used to bound `∫ dt / sqrt(t log t)`. -/
noncomputable def sqrtLogPrimitive (V : ℝ) : ℝ :=
  Real.sqrt (V / Real.log V)

/-- Derivative model for `sqrtLogPrimitive` on the positive-log tail. -/
noncomputable def sqrtLogPrimitiveDeriv (V : ℝ) : ℝ :=
  ((Real.log V - 1) / (2 * Real.log V)) * invSqrtLogModel V

/-- `invSqrtLogModel` is continuous on closed intervals contained in `[exp 2, ∞)`. -/
theorem invSqrtLogModel_continuousOn_Icc_of_exp_two_le {a b : ℝ}
    (ha : Real.exp 2 ≤ a) :
    ContinuousOn invSqrtLogModel (Set.Icc a b) := by
  let s : Set ℝ := Set.Icc a b
  have hlog : ContinuousOn Real.log s := by
    refine Real.continuousOn_log.mono ?_
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) (le_trans ha hx.1)
    simpa using ne_of_gt hx_pos
  have hprod : ContinuousOn (fun x : ℝ => x * Real.log x) s :=
    continuousOn_id.mul hlog
  have hsqrt : ContinuousOn (fun x : ℝ => Real.sqrt (x * Real.log x)) s :=
    hprod.sqrt
  have hden_ne : ∀ x ∈ s, Real.sqrt (x * Real.log x) ≠ 0 := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) (le_trans ha hx.1)
    have hx_exp : Real.exp 2 ≤ x := le_trans ha hx.1
    have hlog_ge_two : (2 : ℝ) ≤ Real.log x :=
      (Real.le_log_iff_exp_le hx_pos).2 hx_exp
    have hlog_pos : 0 < Real.log x := by linarith
    exact ne_of_gt (Real.sqrt_pos.mpr (mul_pos hx_pos hlog_pos))
  change ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt (x * Real.log x)) s
  exact continuousOn_const.div hsqrt hden_ne

/-- `sqrtLogPrimitive` is continuous on closed intervals contained in `[exp 2, ∞)`. -/
theorem sqrtLogPrimitive_continuousOn_Icc_of_exp_two_le {a b : ℝ}
    (ha : Real.exp 2 ≤ a) :
    ContinuousOn sqrtLogPrimitive (Set.Icc a b) := by
  let s : Set ℝ := Set.Icc a b
  have hlog : ContinuousOn Real.log s := by
    refine Real.continuousOn_log.mono ?_
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) (le_trans ha hx.1)
    simpa using ne_of_gt hx_pos
  have hlog_ne : ∀ x ∈ s, Real.log x ≠ 0 := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) (le_trans ha hx.1)
    have hx_exp : Real.exp 2 ≤ x := le_trans ha hx.1
    have hlog_ge_two : (2 : ℝ) ≤ Real.log x :=
      (Real.le_log_iff_exp_le hx_pos).2 hx_exp
    exact ne_of_gt (by linarith : 0 < Real.log x)
  have hquot : ContinuousOn (fun x : ℝ => x / Real.log x) s :=
    continuousOn_id.div hlog hlog_ne
  change ContinuousOn (fun x : ℝ => Real.sqrt (x / Real.log x)) s
  exact hquot.sqrt

/-- `sqrtLogPrimitiveDeriv` is continuous on closed intervals contained in `[exp 2, ∞)`. -/
theorem sqrtLogPrimitiveDeriv_continuousOn_Icc_of_exp_two_le {a b : ℝ}
    (ha : Real.exp 2 ≤ a) :
    ContinuousOn sqrtLogPrimitiveDeriv (Set.Icc a b) := by
  let s : Set ℝ := Set.Icc a b
  have hlog : ContinuousOn Real.log s := by
    refine Real.continuousOn_log.mono ?_
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) (le_trans ha hx.1)
    simpa using ne_of_gt hx_pos
  have hden_ne : ∀ x ∈ s, 2 * Real.log x ≠ 0 := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) (le_trans ha hx.1)
    have hx_exp : Real.exp 2 ≤ x := le_trans ha hx.1
    have hlog_ge_two : (2 : ℝ) ≤ Real.log x :=
      (Real.le_log_iff_exp_le hx_pos).2 hx_exp
    have hlog_pos : 0 < Real.log x := by linarith
    exact mul_ne_zero two_ne_zero (ne_of_gt hlog_pos)
  have hfactor : ContinuousOn
      (fun x : ℝ => (Real.log x - 1) / (2 * Real.log x)) s :=
    (hlog.sub continuousOn_const).div (continuousOn_const.mul hlog) hden_ne
  change ContinuousOn
    (fun x : ℝ =>
      ((Real.log x - 1) / (2 * Real.log x)) * invSqrtLogModel x) s
  exact hfactor.mul (invSqrtLogModel_continuousOn_Icc_of_exp_two_le ha)

/-- Derivative of the elementary tail-integral primitive on the positive-log tail. -/
theorem sqrtLogPrimitive_hasDerivAt_of_one_lt {V : ℝ} (hV : 1 < V) :
    HasDerivAt sqrtLogPrimitive (sqrtLogPrimitiveDeriv V) V := by
  have hV_pos : 0 < V := lt_trans zero_lt_one hV
  have hV_ne : V ≠ 0 := ne_of_gt hV_pos
  have hlog_pos : 0 < Real.log V := Real.log_pos hV
  have hlog_ne : Real.log V ≠ 0 := ne_of_gt hlog_pos
  have hinner_pos : 0 < V / Real.log V := div_pos hV_pos hlog_pos
  have hinner : HasDerivAt (fun y : ℝ => y / Real.log y)
      ((Real.log V - 1) / (Real.log V) ^ 2) V := by
    have hid : HasDerivAt (fun y : ℝ => y) 1 V := hasDerivAt_id V
    have hlog : HasDerivAt (fun y : ℝ => Real.log y) (1 / V) V := by
      simpa using Real.hasDerivAt_log hV_ne
    convert hid.div hlog hlog_ne using 1
    field_simp [hV_ne, hlog_ne]
  have hsqrt : HasDerivAt sqrtLogPrimitive
      (((Real.log V - 1) / (Real.log V) ^ 2) /
        (2 * Real.sqrt (V / Real.log V))) V := by
    simpa [sqrtLogPrimitive] using hinner.sqrt (ne_of_gt hinner_pos)
  convert hsqrt using 1
  rw [sqrtLogPrimitiveDeriv, invSqrtLogModel]
  have hsqrt_mul :
      Real.sqrt (V * Real.log V) =
        Real.log V * Real.sqrt (V / Real.log V) := by
    calc
      Real.sqrt (V * Real.log V)
          = Real.sqrt ((Real.log V) ^ 2 * (V / Real.log V)) := by
            congr 1
            field_simp [hlog_ne]
      _ = Real.sqrt ((Real.log V) ^ 2) * Real.sqrt (V / Real.log V) := by
            rw [Real.sqrt_mul]
            positivity
      _ = Real.log V * Real.sqrt (V / Real.log V) := by
            rw [Real.sqrt_sq (le_of_lt hlog_pos)]
  rw [hsqrt_mul]
  field_simp [hlog_ne, ne_of_gt hinner_pos, ne_of_gt (Real.sqrt_pos.mpr hinner_pos)]

/-- On `[exp 2, ∞)`, the primitive derivative dominates the model integrand. -/
theorem invSqrtLogModel_le_four_mul_deriv {V : ℝ} (hV : Real.exp 2 ≤ V) :
    invSqrtLogModel V ≤ 4 * sqrtLogPrimitiveDeriv V := by
  have hV_pos : 0 < V := lt_of_lt_of_le (Real.exp_pos 2) hV
  have hlog_ge_two : (2 : ℝ) ≤ Real.log V :=
    (Real.le_log_iff_exp_le hV_pos).2 hV
  have hlog_pos : 0 < Real.log V := by linarith
  have hinv_nonneg : 0 ≤ invSqrtLogModel V := by
    rw [invSqrtLogModel]
    positivity
  have hfactor_ge_one : (1 : ℝ) ≤ 4 * ((Real.log V - 1) / (2 * Real.log V)) := by
    field_simp [ne_of_gt hlog_pos]
    nlinarith
  calc
    invSqrtLogModel V = 1 * invSqrtLogModel V := by ring
    _ ≤ (4 * ((Real.log V - 1) / (2 * Real.log V))) * invSqrtLogModel V :=
      mul_le_mul_of_nonneg_right hfactor_ge_one hinv_nonneg
    _ = 4 * sqrtLogPrimitiveDeriv V := by
      rw [sqrtLogPrimitiveDeriv]
      ring

/-- TeX (8): elementary bound for `∫ dt / sqrt(t log t)` on positive-log tails. -/
theorem elementary_integral_bound {T V : ℝ}
    (hT : Real.exp 2 ≤ T) (hTV : T ≤ V) :
    ∫ t in T..V, invSqrtLogModel t ≤ 4 * sqrtLogPrimitive V := by
  have hcont_prim : ContinuousOn sqrtLogPrimitive (Set.Icc T V) :=
    sqrtLogPrimitive_continuousOn_Icc_of_exp_two_le hT
  have hinv_int : IntervalIntegrable invSqrtLogModel MeasureTheory.volume T V :=
    (invSqrtLogModel_continuousOn_Icc_of_exp_two_le hT).intervalIntegrable_of_Icc hTV
  have hderiv_int : IntervalIntegrable sqrtLogPrimitiveDeriv MeasureTheory.volume T V :=
    (sqrtLogPrimitiveDeriv_continuousOn_Icc_of_exp_two_le hT).intervalIntegrable_of_Icc hTV
  have hderiv4_int :
      IntervalIntegrable (fun x : ℝ => 4 * sqrtLogPrimitiveDeriv x)
        MeasureTheory.volume T V := by
    simpa only [smul_eq_mul] using hderiv_int.const_mul (4 : ℝ)
  have hmono :
      ∫ t in T..V, invSqrtLogModel t ≤
        ∫ t in T..V, 4 * sqrtLogPrimitiveDeriv t := by
    refine intervalIntegral.integral_mono_on hTV hinv_int hderiv4_int ?_
    intro x hx
    exact invSqrtLogModel_le_four_mul_deriv (le_trans hT hx.1)
  have hftc :
      ∫ t in T..V, sqrtLogPrimitiveDeriv t =
        sqrtLogPrimitive V - sqrtLogPrimitive T :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hTV hcont_prim
      (fun x hx =>
        sqrtLogPrimitive_hasDerivAt_of_one_lt
          (by
            have hx_exp : Real.exp 2 ≤ x := le_trans hT (le_of_lt hx.1)
            have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) hx_exp
            have hlog_ge_two : (2 : ℝ) ≤ Real.log x :=
              (Real.le_log_iff_exp_le hx_pos).2 hx_exp
            have hlog_pos : 0 < Real.log x := by linarith
            exact (Real.log_pos_iff (le_of_lt hx_pos)).1 hlog_pos))
      hderiv_int
  have hprim_T_nonneg : 0 ≤ sqrtLogPrimitive T := Real.sqrt_nonneg _
  calc
    ∫ t in T..V, invSqrtLogModel t
        ≤ ∫ t in T..V, 4 * sqrtLogPrimitiveDeriv t := hmono
    _ = 4 * (sqrtLogPrimitive V - sqrtLogPrimitive T) := by
          rw [intervalIntegral.integral_const_mul, hftc]
    _ ≤ 4 * sqrtLogPrimitive V := by nlinarith

/-- On the tail, the primitive model is exactly `2 X fModel X`. -/
theorem eventually_IModel_eq_two_mul_self_mul_fModel :
    ∀ᶠ X : ℝ in Filter.atTop, IModel X = 2 * X * fModel X := by
  have hlam_nonneg : 0 ≤ 2 * lam := by
    unfold lam
    positivity
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hX_pos : 0 < X := lt_trans zero_lt_one hX
  have hX_nonneg : 0 ≤ X := le_of_lt hX_pos
  have hlog_pos : 0 < Real.log X := Real.log_pos hX
  calc
    IModel X = 2 * Real.sqrt ((2 * lam) * (X / Real.log X)) := by
      simp [IModel]
      ring_nf
    _ = 2 * Real.sqrt (X ^ 2 * (2 * lam / (X * Real.log X))) := by
      congr 1
      congr 1
      field_simp [ne_of_gt hX_pos, ne_of_gt hlog_pos]
    _ = 2 * (Real.sqrt (X ^ 2) * Real.sqrt (2 * lam / (X * Real.log X))) := by
      rw [Real.sqrt_mul]
      positivity
    _ = 2 * X * fModel X := by
      rw [Real.sqrt_sq hX_nonneg]
      simp [fModel]
      ring

/-- The real second-order scale `X / log X` tends to infinity. -/
theorem scaleReal_tendsto_atTop :
    Tendsto scaleReal Filter.atTop Filter.atTop := by
  have hratio0 : Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hratio_pos : ∀ᶠ x : ℝ in Filter.atTop, 0 < Real.log x / x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  have hratioGT : Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (𝓝[>] 0) :=
    tendsto_inf.2 ⟨hratio0, tendsto_principal.mpr hratio_pos⟩
  have hinv : Tendsto (fun x : ℝ => (Real.log x / x)⁻¹) Filter.atTop Filter.atTop :=
    hratioGT.inv_tendsto_nhdsGT_zero
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := by linarith
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  rw [scaleReal]
  field_simp [hx0, hlog0]

/-- The primitive model is a square-root of the real scale. -/
theorem IModel_eq_two_mul_sqrt_scaleReal (X : ℝ) :
    IModel X = 2 * Real.sqrt ((2 * lam) * scaleReal X) := by
  simp [IModel, scaleReal]
  ring_nf

/-- The primitive model tends to infinity. -/
theorem IModel_tendsto_atTop :
    Tendsto IModel Filter.atTop Filter.atTop := by
  have hlam : 0 < 2 * lam := by
    unfold lam
    positivity
  have hmul :
      Tendsto (fun X : ℝ => (2 * lam) * scaleReal X) Filter.atTop Filter.atTop :=
    scaleReal_tendsto_atTop.const_mul_atTop hlam
  have hsqrt :
      Tendsto (fun X : ℝ => Real.sqrt ((2 * lam) * scaleReal X))
        Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hmul
  exact (hsqrt.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).congr'
    (EventuallyEq.of_eq (by
      funext X
      exact (IModel_eq_two_mul_sqrt_scaleReal X).symm))

/-- Fixed constants are negligible compared with the primitive model. -/
theorem const_isLittleO_IModel (c : ℝ) :
    (fun _ : ℝ => c) =o[Filter.atTop] IModel := by
  exact isLittleO_const_left.mpr
    (Or.inr (tendsto_norm_atTop_atTop.comp IModel_tendsto_atTop))

/-- The primitive model is positive on the tail `1 < X`. -/
theorem IModel_pos_of_one_lt {X : ℝ} (hX : 1 < X) :
    0 < IModel X := by
  have hX_pos : 0 < X := lt_trans zero_lt_one hX
  have hlog_pos : 0 < Real.log X := Real.log_pos hX
  have hlam : 0 < lam := by
    unfold lam
    positivity
  rw [IModel]
  have harg : 0 < 2 * lam * X / Real.log X := by positivity
  have hsqrt : 0 < Real.sqrt (2 * lam * X / Real.log X) :=
    Real.sqrt_pos.mpr harg
  positivity

/-- The primitive model is eventually positive. -/
theorem eventually_IModel_pos :
    ∀ᶠ X : ℝ in Filter.atTop, 0 < IModel X := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  exact IModel_pos_of_one_lt hX

/-- Derivative formula for the primitive model on the tail `1 < X`. -/
theorem IModel_hasDerivAt_of_one_lt {X : ℝ} (hX : 1 < X) :
    HasDerivAt IModel (fModel X * (1 - 1 / Real.log X)) X := by
  have hlam_pos : 0 < 2 * lam := by
    unfold lam
    positivity
  have hX_pos : 0 < X := lt_trans zero_lt_one hX
  have hX_ne : X ≠ 0 := ne_of_gt hX_pos
  have hlog_pos : 0 < Real.log X := Real.log_pos hX
  have hlog_ne : Real.log X ≠ 0 := ne_of_gt hlog_pos
  have hu_pos : 0 < 2 * lam * X / Real.log X := by positivity
  have hinner :
      HasDerivAt (fun X : ℝ => 2 * lam * X / Real.log X)
        ((2 * lam) * (Real.log X - 1) / (Real.log X) ^ 2) X := by
    have hnum : HasDerivAt (fun X : ℝ => (2 * lam) * X) (2 * lam) X := by
      simpa using (hasDerivAt_id X).const_mul (2 * lam)
    have hlog : HasDerivAt (fun X : ℝ => Real.log X) (1 / X) X := by
      simpa using Real.hasDerivAt_log hX_ne
    convert hnum.div hlog hlog_ne using 1
    field_simp [hlog_ne, hX_ne]
  have hsqrt :
      HasDerivAt (fun X : ℝ => Real.sqrt (2 * lam * X / Real.log X))
        (((2 * lam) * (Real.log X - 1) / (Real.log X) ^ 2) /
          (2 * Real.sqrt (2 * lam * X / Real.log X))) X := by
    simpa using hinner.sqrt (ne_of_gt hu_pos)
  unfold IModel
  convert hsqrt.const_mul 2 using 1
  have hsqrt_arg : Real.sqrt (2 * lam * X / Real.log X) = X * fModel X := by
    calc
      Real.sqrt (2 * lam * X / Real.log X)
          = Real.sqrt (X ^ 2 * (2 * lam / (X * Real.log X))) := by
            congr 1
            field_simp [hX_ne, hlog_ne]
      _ = Real.sqrt (X ^ 2) * Real.sqrt (2 * lam / (X * Real.log X)) := by
            rw [Real.sqrt_mul]
            positivity
      _ = X * fModel X := by
            rw [Real.sqrt_sq (le_of_lt hX_pos)]
            simp [fModel]
  have hfModel_sq : fModel X ^ 2 = 2 * lam / (X * Real.log X) := by
    rw [fModel, Real.sq_sqrt]
    positivity
  have hfModel_pos : 0 < fModel X := by
    rw [fModel, Real.sqrt_pos]
    positivity
  have hfModel_ne : fModel X ≠ 0 := ne_of_gt hfModel_pos
  have hfModel_sq_mul : fModel X ^ 2 * X * Real.log X = 2 * lam := by
    rw [hfModel_sq]
    field_simp [hX_ne, hlog_ne]
  rw [hsqrt_arg]
  field_simp [hX_ne, hlog_ne, hfModel_ne]
  nlinarith [hfModel_sq_mul]

/-- Eventual derivative formula for the primitive model. -/
theorem eventually_IModel_hasDerivAt :
    ∀ᶠ X : ℝ in Filter.atTop,
      HasDerivAt IModel (fModel X * (1 - 1 / Real.log X)) X := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  exact IModel_hasDerivAt_of_one_lt hX

/-- The derivative correction factor in `IModel` tends to `1`. -/
theorem one_sub_inv_log_isEquivalent_one :
    (fun X : ℝ => 1 - (Real.log X)⁻¹) ~[Filter.atTop] fun _X : ℝ => 1 := by
  change (fun X : ℝ => 1 - (Real.log X)⁻¹) ~[Filter.atTop]
    Function.const ℝ (1 : ℝ)
  rw [isEquivalent_const_iff_tendsto (by norm_num : (1 : ℝ) ≠ 0)]
  convert (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop) using 1
  ext X
  ring_nf

/-- The eventual derivative of `IModel` is asymptotic to the pointwise model `fModel`. -/
theorem IModel_derivFactor_isEquivalent_fModel :
    (fun X : ℝ => fModel X * (1 - (Real.log X)⁻¹)) ~[Filter.atTop] fModel := by
  have h := (IsEquivalent.refl : fModel ~[Filter.atTop] fModel).mul
    one_sub_inv_log_isEquivalent_one
  convert h using 1
  funext X
  simp

/-- The named derivative model is eventually the derivative of `IModel`. -/
theorem eventually_IModel_hasDerivAt_derivModel :
    ∀ᶠ X : ℝ in Filter.atTop,
      HasDerivAt IModel (IModelDeriv X) X := by
  simpa [IModelDeriv] using eventually_IModel_hasDerivAt

/-- The named derivative model is asymptotic to `fModel`. -/
theorem IModelDeriv_isEquivalent_fModel :
    IModelDeriv ~[Filter.atTop] fModel := by
  refine IModel_derivFactor_isEquivalent_fModel.congr_left ?_
  exact EventuallyEq.of_eq (by
    funext X
    simp [IModelDeriv, one_div])

/-- The derivative model is eventually positive. -/
theorem eventually_IModelDeriv_pos :
    ∀ᶠ X : ℝ in Filter.atTop, 0 < IModelDeriv X :=
  IModelDeriv_isEquivalent_fModel.eventually_pos eventually_fModel_pos

/-- The derivative model is continuous on closed intervals contained in `(1, ∞)`. -/
theorem IModelDeriv_continuousOn_Icc_of_one_lt {a b : ℝ} (ha : 1 < a) :
    ContinuousOn IModelDeriv (Set.Icc a b) := by
  let s : Set ℝ := Set.Icc a b
  have hlog : ContinuousOn Real.log s := by
    refine Real.continuousOn_log.mono ?_
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le (lt_trans zero_lt_one ha) hx.1
    simpa using ne_of_gt hxpos
  have hden : ContinuousOn (fun X : ℝ => X * Real.log X) s :=
    continuousOn_id.mul hlog
  have hden_ne : ∀ X ∈ s, X * Real.log X ≠ 0 := by
    intro X hX
    have hXpos : 0 < X := lt_of_lt_of_le (lt_trans zero_lt_one ha) hX.1
    have hlogpos : 0 < Real.log X := Real.log_pos (lt_of_lt_of_le ha hX.1)
    exact mul_ne_zero (ne_of_gt hXpos) (ne_of_gt hlogpos)
  have hquot : ContinuousOn (fun X : ℝ => (2 * lam) / (X * Real.log X)) s :=
    continuousOn_const.div hden hden_ne
  have hlog_ne : ∀ X ∈ s, Real.log X ≠ 0 := by
    intro X hX
    exact ne_of_gt (Real.log_pos (lt_of_lt_of_le ha hX.1))
  have hfactor : ContinuousOn (fun X : ℝ => 1 - 1 / Real.log X) s :=
    continuousOn_const.sub (continuousOn_const.div hlog hlog_ne)
  change ContinuousOn
    (fun X : ℝ => Real.sqrt (2 * lam / (X * Real.log X)) * (1 - 1 / Real.log X)) s
  exact hquot.sqrt.mul hfactor

/-- The derivative model is integrable on ordered tail intervals. -/
theorem IModelDeriv_intervalIntegrable_of_one_lt_of_le
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable IModelDeriv MeasureTheory.volume a b :=
  (IModelDeriv_continuousOn_Icc_of_one_lt ha).intervalIntegrable_of_Icc hab

/-- Exact integral of the derivative model over ordered tail intervals. -/
theorem integral_IModelDeriv_eq_IModel_sub_of_one_lt_of_le
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ x in a..b, IModelDeriv x = IModel b - IModel a := by
  have hderivIcc : ∀ x ∈ Set.Icc a b, HasDerivAt IModel (IModelDeriv x) x := by
    intro x hx
    have hx1 : 1 < x := lt_of_lt_of_le ha hx.1
    simpa [IModelDeriv] using IModel_hasDerivAt_of_one_lt hx1
  have hcont : ContinuousOn IModel (Set.Icc a b) :=
    HasDerivAt.continuousOn hderivIcc
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
    (fun x hx => hderivIcc x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    (IModelDeriv_intervalIntegrable_of_one_lt_of_le ha hab)

namespace PhiPsiData

variable {B : ℝ} (D : PhiPsiData B)

/-- Interior target points have inverse values strictly above the left endpoint. -/
theorem psi_gt_tail_endpoint {t : ℝ} (ht : D.Tstar < t) :
    (D.N0 : ℝ) < D.psi t := by
  have ht_le : D.Tstar ≤ t := le_of_lt ht
  have hpsi_tail : (D.N0 : ℝ) ≤ D.psi t := D.psi_maps_tail t ht_le
  by_contra hnot
  have hpsi_le_N : D.psi t ≤ (D.N0 : ℝ) := le_of_not_gt hnot
  have hpsi_eq : D.psi t = (D.N0 : ℝ) := le_antisymm hpsi_le_N hpsi_tail
  have hPhi : D.Phi (D.psi t) = t := D.psi_left_inv t ht_le
  have hPhi_N : D.Phi (D.N0 : ℝ) = D.Tstar := by rw [D.Tstar_eq]
  rw [hpsi_eq, hPhi_N] at hPhi
  linarith

/-- The inverse branch maps a tail-neighborhood of an interior target point onto a neighborhood
of the inverse value. -/
theorem psi_tail_image_mem_nhds {t : ℝ} (ht : D.Tstar < t) :
    D.psi '' Set.Ici D.Tstar ∈ 𝓝 (D.psi t) := by
  have htpsi : (D.N0 : ℝ) < D.psi t := D.psi_gt_tail_endpoint ht
  have hIci : Set.Ici (D.N0 : ℝ) ∈ 𝓝 (D.psi t) := Ici_mem_nhds htpsi
  refine mem_of_superset hIci ?_
  intro x hx
  refine ⟨D.Phi x, D.Phi_maps_tail x hx, ?_⟩
  exact D.psi_right_inv x hx

/-- The inverse branch is continuous at every interior point of the target tail. -/
theorem psi_continuousAt_tail_interior {t : ℝ} (ht : D.Tstar < t) :
    ContinuousAt D.psi t := by
  have hs : Set.Ici D.Tstar ∈ 𝓝 t := Ici_mem_nhds ht
  have himage : D.psi '' Set.Ici D.Tstar ∈ 𝓝 (D.psi t) :=
    D.psi_tail_image_mem_nhds ht
  exact continuousAt_of_monotoneOn_of_image_mem_nhds D.psi_mono_tail hs himage

/-- The inverse branch is eventually continuous on the real tail. -/
theorem eventually_psi_continuousAt_tail :
    ∀ᶠ t : ℝ in Filter.atTop, ContinuousAt D.psi t := by
  filter_upwards [eventually_gt_atTop D.Tstar] with t ht
  exact D.psi_continuousAt_tail_interior ht

/-- Derivative of the inverse branch at interior target-tail points. -/
theorem psi_hasDerivAt_tail_interior {t : ℝ} (ht : D.Tstar < t)
    (hH : H B (Real.log (D.psi t)) ≠ 0)
    (hnum :
      0 < 2 * H B (Real.log (D.psi t)) - Hderiv (Real.log (D.psi t))) :
    HasDerivAt D.psi
      (lam * D.psi t *
        (2 * H B (Real.log (D.psi t)) - Hderiv (Real.log (D.psi t))) /
          (H B (Real.log (D.psi t))) ^ 2)⁻¹ t := by
  let r : ℝ := D.psi t
  have hcont : ContinuousAt D.psi t := D.psi_continuousAt_tail_interior ht
  have hr_gt_N0 : (D.N0 : ℝ) < r := by
    simpa [r] using D.psi_gt_tail_endpoint ht
  have hN0_three : (3 : ℝ) ≤ (D.N0 : ℝ) := by
    exact_mod_cast D.N0_ge_three
  have hr_gt_one : 1 < r := by linarith
  have hr_pos : 0 < r := lt_trans zero_lt_one hr_gt_one
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hlog_ne : Real.log r ≠ 0 := ne_of_gt (Real.log_pos hr_gt_one)
  have hderPhiFormula : HasDerivAt (PhiFormula B)
      (lam * r * (2 * H B (Real.log r) - Hderiv (Real.log r)) /
        (H B (Real.log r)) ^ 2) r :=
    PhiFormula_hasDerivAt hr_ne hlog_ne (by simpa [r] using hH)
  have hderPhi : HasDerivAt D.Phi
      (lam * r * (2 * H B (Real.log r) - Hderiv (Real.log r)) /
        (H B (Real.log r)) ^ 2) r := by
    exact hderPhiFormula.congr_of_eventuallyEq (by
      filter_upwards [] with y
      exact D.Phi_eq y)
  have hder_ne :
      lam * r * (2 * H B (Real.log r) - Hderiv (Real.log r)) /
          (H B (Real.log r)) ^ 2 ≠ 0 := by
    have hlam : 0 < lam := by
      unfold lam
      positivity
    have hnum' : 0 < 2 * H B (Real.log r) - Hderiv (Real.log r) := by
      simpa [r] using hnum
    positivity
  have hleft : ∀ᶠ y in 𝓝 t, D.Phi (D.psi y) = y := by
    filter_upwards [Ici_mem_nhds ht] with y hy
    exact D.psi_left_inv y hy
  exact hderPhi.of_local_left_inverse hcont hder_ne hleft

/-- Derivative of the majorant `f = 1 / psi` at interior target-tail points. -/
theorem f_hasDerivAt_tail_interior {t : ℝ} (ht : D.Tstar < t)
    (hH : H B (Real.log (D.psi t)) ≠ 0)
    (hnum :
      0 < 2 * H B (Real.log (D.psi t)) - Hderiv (Real.log (D.psi t))) :
    HasDerivAt D.f
      (-(lam * D.psi t *
        (2 * H B (Real.log (D.psi t)) - Hderiv (Real.log (D.psi t))) /
          (H B (Real.log (D.psi t))) ^ 2)⁻¹ /
          (D.psi t) ^ 2) t := by
  let dPhi : ℝ :=
    lam * D.psi t *
      (2 * H B (Real.log (D.psi t)) - Hderiv (Real.log (D.psi t))) /
        (H B (Real.log (D.psi t))) ^ 2
  have hpsi : HasDerivAt D.psi dPhi⁻¹ t := by
    dsimp [dPhi]
    exact D.psi_hasDerivAt_tail_interior ht hH hnum
  have hpsi_pos : 0 < D.psi t := D.psi_pos_tail t (le_of_lt ht)
  have hinv : HasDerivAt (fun y : ℝ => (D.psi y)⁻¹)
      (-(dPhi⁻¹) / (D.psi t) ^ 2) t := by
    simpa using hpsi.inv (ne_of_gt hpsi_pos)
  have heq : D.f =ᶠ[𝓝 t] fun y : ℝ => (D.psi y)⁻¹ := by
    filter_upwards [Ici_mem_nhds ht] with y hy
    rw [D.f_eq_tail y hy]
    ring
  exact hinv.congr_of_eventuallyEq heq

/-- TeX (10): eventual pointwise derivative bound `|f'| ≤ f(t) / t`. -/
theorem eventually_f_hasDerivAt_bound :
    ∀ᶠ t : ℝ in Filter.atTop,
      ∃ f' : ℝ, HasDerivAt D.f f' t ∧ |f'| ≤ D.f t / t := by
  filter_upwards [eventually_gt_atTop D.Tstar,
    D.psi_tendsto_atTop.eventually (eventually_H_log_pos_atTop B),
    D.psi_tendsto_atTop.eventually (eventually_two_mul_H_log_sub_Hderiv_log_pos_atTop B),
    D.psi_tendsto_atTop.eventually (eventually_inverse_derivative_model_le_f_over_Phi B)]
    with t ht hHpos hnumpos hmodel
  let f' : ℝ :=
    -(lam * D.psi t *
      (2 * H B (Real.log (D.psi t)) - Hderiv (Real.log (D.psi t))) /
        (H B (Real.log (D.psi t))) ^ 2)⁻¹ /
        (D.psi t) ^ 2
  refine ⟨f', ?_, ?_⟩
  · dsimp [f']
    exact D.f_hasDerivAt_tail_interior ht (ne_of_gt hHpos) hnumpos
  · let r : ℝ := D.psi t
    let N : ℝ := 2 * H B (Real.log r) - Hderiv (Real.log r)
    have hr_pos : 0 < r := D.psi_pos_tail t (le_of_lt ht)
    have hHpos' : 0 < H B (Real.log r) := by simpa [r] using hHpos
    have hNpos : 0 < N := by
      dsimp [N, r]
      exact hnumpos
    have hlam_pos : 0 < lam := by
      unfold lam
      positivity
    have h_abs :
        |f'| = H B (Real.log r) ^ 2 / (lam * r ^ 3 * N) := by
      dsimp [f', N, r]
      have hnonneg : 0 ≤
          (lam * D.psi t *
            (2 * H B (Real.log (D.psi t)) - Hderiv (Real.log (D.psi t))) /
              (H B (Real.log (D.psi t))) ^ 2)⁻¹ / (D.psi t) ^ 2 := by
        positivity
      rw [show
          -(lam * D.psi t *
            (2 * H B (Real.log (D.psi t)) - Hderiv (Real.log (D.psi t))) /
              (H B (Real.log (D.psi t))) ^ 2)⁻¹ / (D.psi t) ^ 2 =
            -((lam * D.psi t *
              (2 * H B (Real.log (D.psi t)) - Hderiv (Real.log (D.psi t))) /
                (H B (Real.log (D.psi t))) ^ 2)⁻¹ / (D.psi t) ^ 2) by ring]
      rw [abs_neg, abs_of_nonneg hnonneg]
      field_simp [ne_of_gt hr_pos, ne_of_gt hHpos', ne_of_gt hNpos,
        ne_of_gt hlam_pos]
    have hPhiFormula : PhiFormula B r = t := by
      have hPhi := D.psi_left_inv t (le_of_lt ht)
      rw [D.Phi_eq (D.psi t)] at hPhi
      simpa [r] using hPhi
    have hf_tail : D.f t = 1 / r := by
      simpa [r] using D.f_eq_tail t (le_of_lt ht)
    calc
      |f'| = H B (Real.log r) ^ 2 / (lam * r ^ 3 * N) := h_abs
      _ ≤ (1 / r) / PhiFormula B r := by
        simpa [r, N] using hmodel
      _ = D.f t / t := by
        rw [hf_tail, hPhiFormula]

/-- Packaged derivative bound with an explicit tail threshold. -/
theorem f_derivative_bound :
    ∃ C T : ℝ, 0 < C ∧
      ∀ t : ℝ, T ≤ t →
        ∃ f' : ℝ, HasDerivAt D.f f' t ∧ |f'| ≤ C * D.f t / t := by
  rcases Filter.eventually_atTop.mp D.eventually_f_hasDerivAt_bound with ⟨T, hT⟩
  refine ⟨1, T, by norm_num, ?_⟩
  intro t ht
  simpa using hT t ht

/-- The logarithm of the inverse branch tends to infinity. -/
theorem log_psi_tendsto_atTop :
    Tendsto (fun t : ℝ => Real.log (D.psi t)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp D.psi_tendsto_atTop

/-- The implicit denominator evaluated at `log (psi t)` is eventually positive. -/
theorem eventually_H_log_psi_pos :
    ∀ᶠ t : ℝ in Filter.atTop, 0 < H B (Real.log (D.psi t)) :=
  D.log_psi_tendsto_atTop.eventually (eventually_H_pos_atTop B)

/-- The implicit denominator evaluated at `log (psi t)` is eventually nonzero. -/
theorem eventually_H_log_psi_ne_zero :
    ∀ᶠ t : ℝ in Filter.atTop, H B (Real.log (D.psi t)) ≠ 0 := by
  filter_upwards [D.eventually_H_log_psi_pos] with t ht
  exact ne_of_gt ht

/-- Along the inverse branch, `H(log (psi t))` is asymptotic to `log (psi t)`. -/
theorem H_log_psi_isEquivalent_log_psi :
    (fun t : ℝ => H B (Real.log (D.psi t))) ~[Filter.atTop]
      fun t : ℝ => Real.log (D.psi t) :=
  (H_isEquivalent_atTop B).comp_tendsto D.log_psi_tendsto_atTop

/-- The implicit denominator along the inverse branch tends to infinity. -/
theorem H_log_psi_tendsto_atTop :
    Tendsto (fun t : ℝ => H B (Real.log (D.psi t))) Filter.atTop Filter.atTop :=
  D.H_log_psi_isEquivalent_log_psi.symm.tendsto_atTop D.log_psi_tendsto_atTop

/-- The logarithm of the implicit denominator is lower order than `log (psi t)`. -/
theorem log_H_log_psi_isLittleO_log_psi :
    (fun t : ℝ => Real.log (H B (Real.log (D.psi t)))) =o[Filter.atTop]
      fun t : ℝ => Real.log (D.psi t) := by
  have hlogH :
      (fun t : ℝ => Real.log (H B (Real.log (D.psi t)))) =o[Filter.atTop]
        fun t : ℝ => H B (Real.log (D.psi t)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto D.H_log_psi_tendsto_atTop
  exact hlogH.trans_isEquivalent D.H_log_psi_isEquivalent_log_psi

/-- Exact logarithmic form of the inverse-branch equation. -/
theorem log_eq_log_lam_add_two_log_psi_sub_log_H_eventually :
    (fun t : ℝ => Real.log t) =ᶠ[Filter.atTop]
      fun t : ℝ =>
        Real.log lam + 2 * Real.log (D.psi t) -
          Real.log (H B (Real.log (D.psi t))) := by
  have hlam_pos : 0 < lam := by
    unfold lam
    positivity
  filter_upwards [D.PhiFormula_psi_eq_eventually, D.psi_pos_eventually,
      D.eventually_H_log_psi_pos] with t hPhi hpsi_pos hH_pos
  set y : ℝ := D.psi t with hy
  have hy_pos : 0 < y := by simpa [hy] using hpsi_pos
  have hH_y : 0 < H B (Real.log y) := by simpa [hy] using hH_pos
  have hPhi_y : PhiFormula B y = t := by simpa [hy] using hPhi
  rw [← hPhi_y, PhiFormula]
  rw [Real.log_div (mul_ne_zero (ne_of_gt hlam_pos) (pow_ne_zero 2 (ne_of_gt hy_pos)))
    (ne_of_gt hH_y)]
  rw [Real.log_mul (ne_of_gt hlam_pos) (pow_ne_zero 2 (ne_of_gt hy_pos))]
  rw [Real.log_pow]
  ring

/-- The inverse-branch logarithm gives the first-order relation `log t ~ 2 log (psi t)`. -/
theorem log_isEquivalent_two_log_psi :
    (fun t : ℝ => Real.log t) ~[Filter.atTop]
      fun t : ℝ => 2 * Real.log (D.psi t) := by
  rw [Asymptotics.IsEquivalent]
  have hconst :
      (fun _t : ℝ => Real.log lam) =o[Filter.atTop]
        fun t : ℝ => Real.log (D.psi t) := by
    rw [isLittleO_const_left]
    exact Or.inr (tendsto_norm_atTop_atTop.comp D.log_psi_tendsto_atTop)
  have hsmall :
      (fun t : ℝ =>
        Real.log lam - Real.log (H B (Real.log (D.psi t)))) =o[Filter.atTop]
        fun t : ℝ => Real.log (D.psi t) :=
    hconst.sub D.log_H_log_psi_isLittleO_log_psi
  have hsmall_two :
      (fun t : ℝ =>
        Real.log lam - Real.log (H B (Real.log (D.psi t)))) =o[Filter.atTop]
        fun t : ℝ => 2 * Real.log (D.psi t) :=
    hsmall.const_mul_right (by norm_num : (2 : ℝ) ≠ 0)
  refine hsmall_two.congr' ?_ EventuallyEq.rfl
  filter_upwards [D.log_eq_log_lam_add_two_log_psi_sub_log_H_eventually] with t ht
  change Real.log lam - Real.log (H B (Real.log (D.psi t))) =
    Real.log t - 2 * Real.log (D.psi t)
  rw [ht]
  ring

/-- Exact algebraic normalization from the inverse identity:
`f(t)^2 * t * H(log (psi t)) = lambda` eventually. -/
theorem f_sq_mul_self_mul_H_log_psi_eq_lam_eventually :
    (fun t : ℝ => D.f t ^ 2 * t * H B (Real.log (D.psi t)))
      =ᶠ[Filter.atTop] fun _t : ℝ => lam := by
  filter_upwards [D.f_eq_tail_eventually, D.PhiFormula_psi_eq_eventually,
      D.psi_pos_eventually, D.eventually_H_log_psi_pos] with t hf hPhi hpsi_pos hH_pos
  set y : ℝ := D.psi t with hy
  have hy_pos : 0 < y := by simpa [hy] using hpsi_pos
  have hH_y : 0 < H B (Real.log y) := by simpa [hy] using hH_pos
  have hPhi_y : PhiFormula B y = t := by simpa [hy] using hPhi
  have hf_y : D.f t = 1 / y := by simpa [hy] using hf
  rw [hf_y, ← hPhi_y, PhiFormula]
  field_simp [ne_of_gt hy_pos, ne_of_gt hH_y]

/-- Equivalent exact normalization with `f(t)^2` isolated. -/
theorem f_sq_eq_lam_div_self_mul_H_log_psi_eventually :
    (fun t : ℝ => D.f t ^ 2)
      =ᶠ[Filter.atTop] fun t : ℝ => lam / (t * H B (Real.log (D.psi t))) := by
  filter_upwards [D.f_sq_mul_self_mul_H_log_psi_eq_lam_eventually,
      D.eventually_H_log_psi_ne_zero, eventually_gt_atTop (0 : ℝ)] with t hmain hH_ne ht_pos
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have hden : t * H B (Real.log (D.psi t)) ≠ 0 := mul_ne_zero ht_ne hH_ne
  calc
    D.f t ^ 2 = (D.f t ^ 2 * (t * H B (Real.log (D.psi t)))) /
        (t * H B (Real.log (D.psi t))) := by
      field_simp [hden]
    _ = lam / (t * H B (Real.log (D.psi t))) := by
      rw [← hmain]
      ring

/-- First square-level asymptotic for the inverse-branch expression of `f`. -/
theorem f_sq_isEquivalent_lam_div_self_mul_log_psi :
    (fun t : ℝ => D.f t ^ 2) ~[Filter.atTop]
      fun t : ℝ => lam / (t * Real.log (D.psi t)) := by
  have hden :
      (fun t : ℝ => t * H B (Real.log (D.psi t))) ~[Filter.atTop]
        fun t : ℝ => t * Real.log (D.psi t) :=
    (IsEquivalent.refl : (fun t : ℝ => t) ~[Filter.atTop] fun t : ℝ => t).mul
      D.H_log_psi_isEquivalent_log_psi
  have hdiv :
      (fun t : ℝ => lam / (t * H B (Real.log (D.psi t)))) ~[Filter.atTop]
        fun t : ℝ => lam / (t * Real.log (D.psi t)) :=
    (IsEquivalent.refl : (fun _t : ℝ => lam) ~[Filter.atTop] fun _t : ℝ => lam).div hden
  exact hdiv.congr_left D.f_sq_eq_lam_div_self_mul_H_log_psi_eventually.symm

/-- Square-level form of the first-order asymptotic for `f`. -/
theorem f_sq_isEquivalent_model :
    (fun t : ℝ => D.f t ^ 2) ~[Filter.atTop]
      fun t : ℝ => 2 * lam / (t * Real.log t) := by
  have hpsi := D.f_sq_isEquivalent_lam_div_self_mul_log_psi
  have hden :
      (fun t : ℝ => t * Real.log t) ~[Filter.atTop]
        fun t : ℝ => t * (2 * Real.log (D.psi t)) :=
    (IsEquivalent.refl : (fun t : ℝ => t) ~[Filter.atTop] fun t : ℝ => t).mul
      D.log_isEquivalent_two_log_psi
  have hdiv :
      (fun t : ℝ => 2 * lam / (t * Real.log t)) ~[Filter.atTop]
        fun t : ℝ => 2 * lam / (t * (2 * Real.log (D.psi t))) :=
    (IsEquivalent.refl :
        (fun _t : ℝ => 2 * lam) ~[Filter.atTop] fun _t : ℝ => 2 * lam).div hden
  have htarget :
      (fun t : ℝ => 2 * lam / (t * (2 * Real.log (D.psi t)))) =
        fun t : ℝ => lam / (t * Real.log (D.psi t)) := by
    funext t
    ring_nf
  exact hpsi.trans (hdiv.congr_right (EventuallyEq.of_eq htarget)).symm

/-- First-order asymptotic for the constructed majorant `f`. -/
theorem f_asymptotic :
    D.f ~[Filter.atTop]
      (fun t : ℝ => Real.sqrt (2 * lam / (t * Real.log t))) := by
  let g : ℝ → ℝ := fun t => 2 * lam / (t * Real.log t)
  let gNN : ℝ → ℝ := fun t => max (g t) 0
  have hg_nonneg : ∀ t : ℝ, 0 ≤ gNN t := by
    intro t
    exact le_max_right (g t) 0
  have hg_eq : g =ᶠ[Filter.atTop] gNN := by
    filter_upwards [eventually_f_sq_model_nonneg] with t ht
    have ht' : 0 ≤ g t := by simpa [g] using ht
    simp [gNN, ht']
  have hf_nonneg : ∀ᶠ t : ℝ in Filter.atTop, 0 ≤ D.f t := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact le_of_lt (D.f_pos t ht)
  have hf_sqrt_eq : (fun t : ℝ => Real.sqrt (D.f t ^ 2)) =ᶠ[Filter.atTop] D.f := by
    filter_upwards [hf_nonneg] with t ht
    exact Real.sqrt_sq ht
  have hg_sqrt_eq :
      (fun t : ℝ => Real.sqrt (gNN t)) =ᶠ[Filter.atTop]
        fun t : ℝ => Real.sqrt (g t) := by
    filter_upwards [hg_eq] with t ht
    rw [← ht]
  have hsqNN : (fun t : ℝ => D.f t ^ 2) ~[Filter.atTop] gNN :=
    D.f_sq_isEquivalent_model.congr_right hg_eq
  have hsqrt :
      (fun t : ℝ => Real.sqrt (D.f t ^ 2)) ~[Filter.atTop]
        fun t : ℝ => Real.sqrt (gNN t) := by
    have hrpow :
        (fun t : ℝ => (D.f t ^ 2) ^ (1 / 2 : ℝ)) ~[Filter.atTop]
          fun t : ℝ => (gNN t) ^ (1 / 2 : ℝ) :=
      Asymptotics.IsEquivalent.rpow hg_nonneg hsqNN
    simpa [Real.sqrt_eq_rpow] using hrpow
  exact (hsqrt.congr_left hf_sqrt_eq).congr_right hg_sqrt_eq

/-- Big-O corollary of the first-order asymptotic for `f`. -/
theorem f_isBigO_model :
    D.f =O[Filter.atTop]
      (fun t : ℝ => Real.sqrt (2 * lam / (t * Real.log t))) :=
  D.f_asymptotic.isBigO

/-- Quantitative eventual bound for the difference between `f` and `fModel`. -/
theorem eventually_abs_f_sub_fModel_le
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      |D.f t - fModel t| ≤ ε * fModel t := by
  filter_upwards [D.f_asymptotic.isLittleO.def hε] with t ht
  have hraw_nonneg :
      0 ≤ Real.sqrt (2 * lam / (t * Real.log t)) := Real.sqrt_nonneg _
  simpa [fModel, Real.norm_eq_abs, abs_of_nonneg hraw_nonneg] using ht

/-- Eventual lower squeeze comparing `f` to the pointwise model. -/
theorem eventually_one_sub_mul_fModel_le_f
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      (1 - ε) * fModel t ≤ D.f t := by
  filter_upwards [D.eventually_abs_f_sub_fModel_le hε,
      eventually_fModel_pos] with t ht hpos
  have hnonneg : 0 ≤ ε * fModel t := by positivity
  have hle := (abs_le.mp ht).1
  nlinarith

/-- Eventual upper squeeze comparing `f` to the pointwise model. -/
theorem eventually_f_le_one_add_mul_fModel
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      D.f t ≤ (1 + ε) * fModel t := by
  filter_upwards [D.eventually_abs_f_sub_fModel_le hε,
      eventually_fModel_pos] with t ht hpos
  have hnonneg : 0 ≤ ε * fModel t := by positivity
  have hle := (abs_le.mp ht).2
  nlinarith

/-- Explicit eventual upper bound by the named pointwise model. -/
theorem f_le_const_mul_fModel :
    ∃ C T : ℝ, 0 < C ∧ ∀ t : ℝ, T ≤ t → D.f t ≤ C * fModel t := by
  rcases D.f_isBigO_model.exists_pos with ⟨C, hC_pos, hC_bound⟩
  rcases Filter.eventually_atTop.mp hC_bound.bound with ⟨T₀, hT₀⟩
  refine ⟨C, max T₀ 2, hC_pos, ?_⟩
  intro t ht
  have hT₀t : T₀ ≤ t := le_trans (le_max_left T₀ 2) ht
  have ht_one : 1 < t := by
    linarith [le_trans (le_max_right T₀ 2) ht]
  have ht_nonneg : 0 ≤ t := le_of_lt (lt_trans zero_lt_one ht_one)
  have hf_nonneg : 0 ≤ D.f t := D.f_nonneg ht_nonneg
  have hmodel_raw_nonneg :
      0 ≤ Real.sqrt (2 * lam / (t * Real.log t)) := Real.sqrt_nonneg _
  have hbound := hT₀ t hT₀t
  simpa [fModel, Real.norm_eq_abs, abs_of_nonneg hf_nonneg,
    abs_of_nonneg hmodel_raw_nonneg] using hbound

/-- TeX (6): `f(t) = O(1 / sqrt(t log t))` as an explicit eventual bound. -/
theorem f_upper_bound :
    ∃ C T : ℝ, 0 < C ∧
      ∀ t : ℝ, T ≤ t → D.f t ≤ C / Real.sqrt (t * Real.log t) := by
  rcases D.f_le_const_mul_fModel with ⟨C₀, T, hC₀_pos, hbound⟩
  let C : ℝ := C₀ * Real.sqrt (2 * lam)
  have hlam_pos : 0 < 2 * lam := by
    unfold lam
    positivity
  refine ⟨C, T, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro t ht
    calc
      D.f t ≤ C₀ * fModel t := hbound t ht
      _ = C / Real.sqrt (t * Real.log t) := by
        dsimp [C, fModel]
        rw [Real.sqrt_div (le_of_lt hlam_pos)]
        ring

/-- Square-level corollary of the explicit upper bound for `f`. -/
theorem f_sq_upper_bound :
    ∃ C T : ℝ, 0 < C ∧
      ∀ t : ℝ, T ≤ t → D.f t ^ 2 ≤ C / (t * Real.log t) := by
  rcases D.f_upper_bound with ⟨C₀, T₀, hC₀_pos, hbound⟩
  let C : ℝ := C₀ ^ 2
  refine ⟨C, max T₀ 2, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro t ht
    have hT₀t : T₀ ≤ t := le_trans (le_max_left T₀ 2) ht
    have ht_one : 1 < t := by
      linarith [le_trans (le_max_right T₀ 2) ht]
    have ht_pos : 0 < t := lt_trans zero_lt_one ht_one
    have hlog_pos : 0 < Real.log t := Real.log_pos ht_one
    have hden_pos : 0 < t * Real.log t := by positivity
    have hf_nonneg : 0 ≤ D.f t := D.f_nonneg (le_of_lt ht_pos)
    have hright_nonneg : 0 ≤ C₀ / Real.sqrt (t * Real.log t) := by
      positivity
    have hsq :
        D.f t ^ 2 ≤ (C₀ / Real.sqrt (t * Real.log t)) ^ 2 :=
      (sq_le_sq₀ hf_nonneg hright_nonneg).2 (hbound t hT₀t)
    calc
      D.f t ^ 2 ≤ (C₀ / Real.sqrt (t * Real.log t)) ^ 2 := hsq
      _ = C / (t * Real.log t) := by
        dsimp [C]
        rw [div_pow, Real.sq_sqrt (le_of_lt hden_pos)]

/-- The constructed `f` is uniformly comparable on any fixed multiplicative window. -/
theorem f_local_comparability {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ C T : ℝ, 0 < C ∧
      ∀ ⦃s t : ℝ⦄, T ≤ t → c * t ≤ s → s ≤ t →
        D.f s ≤ C * D.f t := by
  rcases fModel_local_comparability hc0 hc1 with ⟨C₀, T₀, hC₀_pos, hmodel⟩
  rcases Filter.eventually_atTop.mp
      (D.eventually_f_le_one_add_mul_fModel (by norm_num : (0 : ℝ) < 1)) with
    ⟨Tup, hTup⟩
  rcases Filter.eventually_atTop.mp
      (D.eventually_one_sub_mul_fModel_le_f (by norm_num : (0 : ℝ) < 1 / 2)) with
    ⟨Tlow, hTlow⟩
  let C : ℝ := 4 * C₀
  let T : ℝ := max T₀ (max Tlow (Tup / c))
  refine ⟨C, T, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro s t ht hcts hst
    have hT₀t : T₀ ≤ t := by
      exact le_trans (le_max_left _ _) ht
    have hTlowt : Tlow ≤ t := by
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
    have hTup_div_t : Tup / c ≤ t := by
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
    have hTup_s : Tup ≤ s := by
      have hTup_le_tc : Tup ≤ t * c := (div_le_iff₀ hc0).1 hTup_div_t
      nlinarith
    have hupper : D.f s ≤ (1 + (1 : ℝ)) * fModel s := hTup s hTup_s
    have hlower :
        (1 - (1 / 2 : ℝ)) * fModel t ≤ D.f t := hTlow t hTlowt
    have hfModel_t_le : fModel t ≤ 2 * D.f t := by
      nlinarith
    have hupper_two : D.f s ≤ 2 * fModel s := by
      norm_num at hupper ⊢
      exact hupper
    calc
      D.f s ≤ 2 * fModel s := hupper_two
      _ ≤ 2 * (C₀ * fModel t) :=
        mul_le_mul_of_nonneg_left (hmodel hT₀t hcts hst) (by norm_num)
      _ = (2 * C₀) * fModel t := by ring
      _ ≤ (2 * C₀) * (2 * D.f t) := by
        exact mul_le_mul_of_nonneg_left hfModel_t_le (by positivity)
      _ = C * D.f t := by
        dsimp [C]
        ring

/-- TeX (12): local Lipschitz estimate for `f` on fixed multiplicative windows. -/
theorem f_local_lipschitz {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ C T : ℝ, 0 < C ∧
      ∀ ⦃s t : ℝ⦄, T ≤ t → c * t ≤ s → s ≤ t →
        |D.f s - D.f t| ≤ C * D.f t / t * |t - s| := by
  rcases D.f_derivative_bound with ⟨Cd, Td, hCd_pos, hderiv⟩
  rcases D.f_local_comparability hc0 hc1 with ⟨Cc, Tc, hCc_pos, hcomp⟩
  let C : ℝ := Cd * Cc / c
  let T : ℝ := max 1 (max Tc (Td / c))
  refine ⟨C, T, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro s t ht hcts hst
    have hT_one : (1 : ℝ) ≤ T := by simp [T]
    have hTcT : Tc ≤ T := by
      dsimp [T]
      exact le_trans (le_max_left Tc (Td / c)) (le_max_right 1 (max Tc (Td / c)))
    have hTd_div_T : Td / c ≤ T := by
      dsimp [T]
      exact le_trans (le_max_right Tc (Td / c)) (le_max_right 1 (max Tc (Td / c)))
    have ht_pos : 0 < t := by linarith
    have hct_pos : 0 < c * t := mul_pos hc0 ht_pos
    have hTd_le_ct : Td ≤ c * t := by
      nlinarith [(div_le_iff₀ hc0).1 (le_trans hTd_div_T ht)]
    let fp : ℝ → ℝ :=
      fun x => if hx : Td ≤ x then Classical.choose (hderiv x hx) else 0
    have hhas : ∀ x ∈ Set.Icc s t, HasDerivWithinAt D.f (fp x) (Set.Icc s t) x := by
      intro x hx
      have htdx : Td ≤ x := le_trans hTd_le_ct (le_trans hcts hx.1)
      dsimp [fp]
      rw [dif_pos htdx]
      exact (Classical.choose_spec (hderiv x htdx)).1.hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Icc s t, ‖fp x‖ ≤ C * D.f t / t := by
      intro x hx
      have htdx : Td ≤ x := le_trans hTd_le_ct (le_trans hcts hx.1)
      have hcx : c * t ≤ x := le_trans hcts hx.1
      have hxt : x ≤ t := hx.2
      have hx_pos : 0 < x := lt_of_lt_of_le hct_pos hcx
      have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
      have htf_nonneg : 0 ≤ D.f t := D.f_nonneg (le_of_lt ht_pos)
      have hcomp_xt : D.f x ≤ Cc * D.f t :=
        hcomp (le_trans hTcT ht) hcx hxt
      have hderiv_bound := (Classical.choose_spec (hderiv x htdx)).2
      have hfp_abs : |fp x| = |Classical.choose (hderiv x htdx)| := by
        dsimp [fp]
        rw [dif_pos htdx]
      have hfp_le : ‖fp x‖ ≤ Cd * D.f x / x := by
        rw [Real.norm_eq_abs, hfp_abs]
        exact hderiv_bound
      have hmono_fx : Cd * D.f x / x ≤ Cd * (Cc * D.f t) / x := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcomp_xt (le_of_lt hCd_pos)) (le_of_lt hx_pos)
      have hmono_inv :
          Cd * (Cc * D.f t) / x ≤ Cd * (Cc * D.f t) / (c * t) := by
        have hnum_nonneg : 0 ≤ Cd * (Cc * D.f t) := by positivity
        exact div_le_div_of_nonneg_left hnum_nonneg hct_pos hcx
      calc
        ‖fp x‖ ≤ Cd * D.f x / x := hfp_le
        _ ≤ Cd * (Cc * D.f t) / x := hmono_fx
        _ ≤ Cd * (Cc * D.f t) / (c * t) := hmono_inv
        _ = C * D.f t / t := by
          dsimp [C]
          field_simp [ne_of_gt hc0, ne_of_gt ht_pos]
    have hmvt := (convex_Icc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
      hhas hbound (Set.left_mem_Icc.2 hst) (Set.right_mem_Icc.2 hst)
    have hnorm_eq : ‖D.f t - D.f s‖ = |D.f s - D.f t| := by
      rw [Real.norm_eq_abs, abs_sub_comm]
    calc
      |D.f s - D.f t| = ‖D.f t - D.f s‖ := hnorm_eq.symm
      _ ≤ C * D.f t / t * ‖t - s‖ := hmvt
      _ = C * D.f t / t * |t - s| := by rw [Real.norm_eq_abs]

/-- First-order comparison of `f` with the derivative model for `IModel`. -/
theorem f_isEquivalent_IModelDeriv :
    D.f ~[Filter.atTop] IModelDeriv :=
  D.f_asymptotic.trans IModelDeriv_isEquivalent_fModel.symm

/-- Quantitative eventual bound for the difference between `f` and `IModelDeriv`. -/
theorem eventually_abs_f_sub_IModelDeriv_le
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      |D.f t - IModelDeriv t| ≤ ε * IModelDeriv t := by
  filter_upwards [D.f_isEquivalent_IModelDeriv.isLittleO.def hε,
      eventually_IModelDeriv_pos] with t ht hpos
  simpa [Real.norm_eq_abs, abs_of_pos hpos] using ht

/-- Eventual lower squeeze bound comparing `f` to the derivative model. -/
theorem eventually_one_sub_mul_IModelDeriv_le_f
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      (1 - ε) * IModelDeriv t ≤ D.f t := by
  filter_upwards [D.eventually_abs_f_sub_IModelDeriv_le hε,
      eventually_IModelDeriv_pos] with t ht hpos
  have hnonneg : 0 ≤ ε * IModelDeriv t := by positivity
  have hle := (abs_le.mp ht).1
  nlinarith

/-- Eventual upper squeeze bound comparing `f` to the derivative model. -/
theorem eventually_f_le_one_add_mul_IModelDeriv
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      D.f t ≤ (1 + ε) * IModelDeriv t := by
  filter_upwards [D.eventually_abs_f_sub_IModelDeriv_le hε,
      eventually_IModelDeriv_pos] with t ht hpos
  have hnonneg : 0 ≤ ε * IModelDeriv t := by positivity
  have hle := (abs_le.mp ht).2
  nlinarith

/-- Integrated lower squeeze for `I` on tail intervals. -/
theorem eventually_integral_one_sub_mul_IModel_sub_le_f
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in Filter.atTop, ∀ᶠ b : ℝ in Filter.atTop,
      a ≤ b → (1 - ε) * (IModel b - IModel a) ≤ ∫ x in a..b, D.f x := by
  rcases Filter.eventually_atTop.mp (D.eventually_one_sub_mul_IModelDeriv_le_f hε) with
    ⟨T₁, hT₁⟩
  let T : ℝ := max 2 T₁
  filter_upwards [eventually_ge_atTop T] with a ha
  filter_upwards [eventually_ge_atTop a] with b _hb hab
  have hT_two : (2 : ℝ) ≤ T := by simp [T]
  have hT_T₁ : T₁ ≤ T := by simp [T]
  have ha_one : 1 < a := by linarith
  have hpoint : ∀ x ∈ Set.Icc a b, (1 - ε) * IModelDeriv x ≤ D.f x := by
    intro x hx
    exact hT₁ x (le_trans hT_T₁ (le_trans ha hx.1))
  have hderiv_int : IntervalIntegrable IModelDeriv MeasureTheory.volume a b :=
    IModelDeriv_intervalIntegrable_of_one_lt_of_le ha_one hab
  have hmul_int : IntervalIntegrable (fun x : ℝ => (1 - ε) * IModelDeriv x)
      MeasureTheory.volume a b := by
    simpa only [smul_eq_mul] using hderiv_int.const_mul (1 - ε)
  have hle : ∫ x in a..b, (1 - ε) * IModelDeriv x ≤ ∫ x in a..b, D.f x :=
    intervalIntegral.integral_mono_on hab hmul_int (D.f_intervalIntegrable a b) hpoint
  calc
    (1 - ε) * (IModel b - IModel a) = (1 - ε) * ∫ x in a..b, IModelDeriv x := by
      rw [integral_IModelDeriv_eq_IModel_sub_of_one_lt_of_le ha_one hab]
    _ = ∫ x in a..b, (1 - ε) * IModelDeriv x := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ x in a..b, D.f x := hle

/-- Integrated upper squeeze for `I` on tail intervals. -/
theorem eventually_integral_f_le_one_add_mul_IModel_sub
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in Filter.atTop, ∀ᶠ b : ℝ in Filter.atTop,
      a ≤ b → ∫ x in a..b, D.f x ≤ (1 + ε) * (IModel b - IModel a) := by
  rcases Filter.eventually_atTop.mp (D.eventually_f_le_one_add_mul_IModelDeriv hε) with
    ⟨T₁, hT₁⟩
  let T : ℝ := max 2 T₁
  filter_upwards [eventually_ge_atTop T] with a ha
  filter_upwards [eventually_ge_atTop a] with b _hb hab
  have hT_two : (2 : ℝ) ≤ T := by simp [T]
  have hT_T₁ : T₁ ≤ T := by simp [T]
  have ha_one : 1 < a := by linarith
  have hpoint : ∀ x ∈ Set.Icc a b, D.f x ≤ (1 + ε) * IModelDeriv x := by
    intro x hx
    exact hT₁ x (le_trans hT_T₁ (le_trans ha hx.1))
  have hderiv_int : IntervalIntegrable IModelDeriv MeasureTheory.volume a b :=
    IModelDeriv_intervalIntegrable_of_one_lt_of_le ha_one hab
  have hmul_int : IntervalIntegrable (fun x : ℝ => (1 + ε) * IModelDeriv x)
      MeasureTheory.volume a b := by
    simpa only [smul_eq_mul] using hderiv_int.const_mul (1 + ε)
  have hle : ∫ x in a..b, D.f x ≤ ∫ x in a..b, (1 + ε) * IModelDeriv x :=
    intervalIntegral.integral_mono_on hab (D.f_intervalIntegrable a b) hmul_int hpoint
  calc
    ∫ x in a..b, D.f x ≤ ∫ x in a..b, (1 + ε) * IModelDeriv x := hle
    _ = (1 + ε) * ∫ x in a..b, IModelDeriv x := by
      rw [intervalIntegral.integral_const_mul]
    _ = (1 + ε) * (IModel b - IModel a) := by
      rw [integral_IModelDeriv_eq_IModel_sub_of_one_lt_of_le ha_one hab]

end PhiPsiData

/-- First-order asymptotic for `I` against the named primitive model. -/
theorem integral_f_isEquivalent_IModel {B : ℝ} (D : PhiPsiData B) :
    (fun X : ℝ => I D X) ~[Filter.atTop] IModel := by
  rw [Asymptotics.IsEquivalent]
  rw [isLittleO_iff]
  intro c hc
  let δ : ℝ := c / 4
  have hδ : 0 < δ := by positivity
  rcases Filter.eventually_atTop.mp
      (D.eventually_integral_one_sub_mul_IModel_sub_le_f hδ) with ⟨Alow, hAlow⟩
  rcases Filter.eventually_atTop.mp
      (D.eventually_integral_f_le_one_add_mul_IModel_sub hδ) with ⟨Aup, hAup⟩
  let a : ℝ := max (max Alow Aup) 2
  have ha_low : Alow ≤ a := by simp [a]
  have ha_up : Aup ≤ a := by simp [a]
  have ha_two : (2 : ℝ) ≤ a := by simp [a]
  have ha_one : 1 < a := by linarith
  have hlower_event := hAlow a ha_low
  have hupper_event := hAup a ha_up
  let C : ℝ := |I D a - IModel a|
  have hconst_event := (const_isLittleO_IModel C).def hδ
  filter_upwards [hlower_event, hupper_event, eventually_ge_atTop a,
      hconst_event, IModel_tendsto_atTop.eventually_ge_atTop (IModel a),
      eventually_IModel_pos] with X hlower hupper hXa hC hIX_ge hIX_pos
  have htail_lower :
      (1 - δ) * (IModel X - IModel a) ≤ ∫ x in a..X, D.f x :=
    hlower hXa
  have htail_upper :
      ∫ x in a..X, D.f x ≤ (1 + δ) * (IModel X - IModel a) :=
    hupper hXa
  have hmodel_nonneg : 0 ≤ IModel X - IModel a := sub_nonneg.mpr hIX_ge
  have hδmodel_nonneg : 0 ≤ δ * (IModel X - IModel a) := by positivity
  have htail_abs :
      |(∫ x in a..X, D.f x) - (IModel X - IModel a)| ≤
        δ * (IModel X - IModel a) := by
    rw [abs_le]
    constructor <;> nlinarith
  have hIa_nonneg : 0 ≤ IModel a := le_of_lt (IModel_pos_of_one_lt ha_one)
  have hmodel_le : IModel X - IModel a ≤ IModel X := by linarith
  have hI_split := I_eq_I_add_integral D a X
  have hdecomp :
      I D X - IModel X =
        (I D a - IModel a) + ((∫ x in a..X, D.f x) - (IModel X - IModel a)) := by
    rw [hI_split]
    ring
  have hC_abs : ‖C‖ = C := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact abs_nonneg _
  have hIX_abs : ‖IModel X‖ = IModel X := by
    rw [Real.norm_eq_abs, abs_of_pos hIX_pos]
  have hmain : ‖I D X - IModel X‖ ≤ 2 * δ * ‖IModel X‖ := by
    rw [Real.norm_eq_abs, hdecomp]
    calc
      |(I D a - IModel a) + ((∫ x in a..X, D.f x) - (IModel X - IModel a))|
          ≤ |I D a - IModel a| +
              |(∫ x in a..X, D.f x) - (IModel X - IModel a)| :=
            abs_add_le _ _
      _ ≤ C + δ * (IModel X - IModel a) := by
            exact add_le_add le_rfl htail_abs
      _ ≤ δ * ‖IModel X‖ + δ * IModel X := by
            have hC_le : C ≤ δ * ‖IModel X‖ := by
              rw [← hC_abs]
              exact hC
            exact add_le_add hC_le
              (mul_le_mul_of_nonneg_left hmodel_le (le_of_lt hδ))
      _ = 2 * δ * ‖IModel X‖ := by
            rw [hIX_abs]
            ring
  have htwoδ_le : 2 * δ ≤ c := by
    dsimp [δ]
    linarith
  calc
    ‖I D X - IModel X‖ ≤ 2 * δ * ‖IModel X‖ := hmain
    _ ≤ c * ‖IModel X‖ :=
      mul_le_mul_of_nonneg_right htwoδ_le (norm_nonneg _)

/-- First-order asymptotic for `∫₀ˣ f`. -/
theorem integral_f_asymptotic {B : ℝ} (D : PhiPsiData B) :
    (fun X : ℝ => I D X) ~[Filter.atTop]
      (fun X : ℝ => 2 * Real.sqrt (2 * lam * X / Real.log X)) := by
  simpa [IModel] using integral_f_isEquivalent_IModel D

end FloorSaving
