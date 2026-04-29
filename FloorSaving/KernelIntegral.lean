import FloorSaving.ContinuousMajorant

noncomputable section

open Filter Topology MeasureTheory Asymptotics
open scoped Real BigOperators

namespace FloorSaving

/-- The correction kernel is continuous on its natural tail `u ≥ 1`. -/
theorem corrKernel_continuousOn_Ici_one :
    ContinuousOn corrKernel (Set.Ici (1 : ℝ)) := by
  change ContinuousOn (fun u : ℝ => 2 * (1 - √(1 - 1 / u)) - 1 / u) (Set.Ici (1 : ℝ))
  have hdiv : ContinuousOn (fun u : ℝ => (1 : ℝ) / u) (Set.Ici (1 : ℝ)) := by
    exact continuousOn_const.div continuousOn_id (by
      intro u hu
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hu))
  have hsqrt : ContinuousOn (fun u : ℝ => Real.sqrt (1 - 1 / u)) (Set.Ici (1 : ℝ)) := by
    exact (continuousOn_const.sub hdiv).sqrt
  have hleft :
      ContinuousOn (fun u : ℝ => (2 : ℝ) * (1 - Real.sqrt (1 - 1 / u)))
        (Set.Ici (1 : ℝ)) := by
    exact continuousOn_const.mul (continuousOn_const.sub hsqrt)
  exact hleft.sub hdiv

/-- Continuity of `corrKernel` on each finite tail interval `[1,U]`. -/
theorem corrKernel_continuousOn_Icc (U : ℝ) :
    ContinuousOn corrKernel (Set.Icc (1 : ℝ) U) :=
  corrKernel_continuousOn_Ici_one.mono (by
    intro u hu
    exact hu.1)

/-- A.e. measurability of `corrKernel` on each finite tail interval `[1,U]`. -/
theorem corrKernel_aemeasurable_Icc (U : ℝ) :
    AEMeasurable corrKernel (MeasureTheory.volume.restrict (Set.Icc (1 : ℝ) U)) :=
  (corrKernel_continuousOn_Icc U).aemeasurable measurableSet_Icc

/-- Interval integrability of `corrKernel` on each ordered finite tail interval. -/
theorem corrKernel_intervalIntegrable {U : ℝ} (hU : 1 ≤ U) :
    IntervalIntegrable corrKernel MeasureTheory.volume (1 : ℝ) U :=
  ContinuousOn.intervalIntegrable (by
    rw [Set.uIcc_of_le hU]
    exact corrKernel_continuousOn_Icc U)

/-- A substitution-ready form of `corrKernel (1+x)`. -/
theorem corrKernel_one_add_eq {x : ℝ} (hx : x ≠ -1) :
    corrKernel (1 + x) = 2 * (1 - Real.sqrt (x / (1 + x))) - 1 / (1 + x) := by
  unfold corrKernel
  have hden : 1 + x ≠ 0 := by
    intro h
    apply hx
    linarith
  congr 2
  · congr 1
    field_simp [hden]
    ring_nf

/-- Change of variables used for the correction-kernel integral. -/
noncomputable def corrKernelChange (x : ℝ) : ℝ :=
  (1 - x ^ 2)⁻¹

/-- Derivative of `corrKernelChange`. -/
noncomputable def corrKernelChangeDeriv (x : ℝ) : ℝ :=
  2 * x / (1 - x ^ 2) ^ 2

/-- Derivative of the correction-kernel change of variables. -/
theorem corrKernel_change_hasDerivAt {x : ℝ} (hden : 1 - x ^ 2 ≠ 0) :
    HasDerivAt corrKernelChange (corrKernelChangeDeriv x) x := by
  unfold corrKernelChange corrKernelChangeDeriv
  have hbase : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_id x).pow 2
    simpa using (hasDerivAt_const x (1 : ℝ)).sub hpow
  have hinv := hbase.inv hden
  convert hinv using 1
  ring

/-- Pointwise simplification of the transformed correction-kernel integrand. -/
theorem corrKernel_change_integrand_eq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    corrKernel (corrKernelChange x) * corrKernelChangeDeriv x = 2 * x / (1 + x) ^ 2 := by
  have hsq_lt : x ^ 2 < 1 := by nlinarith [mul_self_lt_mul_self hx0 hx1]
  have hden_pos : 0 < 1 - x ^ 2 := by linarith
  have hden_ne : 1 - x ^ 2 ≠ 0 := ne_of_gt hden_pos
  have hsqrt_arg : 1 - 1 / corrKernelChange x = x ^ 2 := by
    unfold corrKernelChange
    field_simp [hden_ne]
    ring
  have hsqrt : Real.sqrt (1 - 1 / (1 - x ^ 2)⁻¹) = x := by
    have hs : Real.sqrt (1 - 1 / corrKernelChange x) = x := by
      rw [hsqrt_arg, Real.sqrt_sq_eq_abs, abs_of_nonneg hx0]
    simpa [corrKernelChange] using hs
  unfold corrKernel corrKernelChange corrKernelChangeDeriv
  rw [hsqrt]
  field_simp [hden_ne, show 1 + x ≠ 0 by nlinarith]
  ring

/-- Antiderivative used for the transformed correction kernel. -/
theorem transformedKernel_antideriv_hasDerivAt {x : ℝ} (hx : x ≠ -1) :
    HasDerivAt (fun x : ℝ => 2 * Real.log (1 + x) + 2 / (1 + x))
      (2 * x / (1 + x) ^ 2) x := by
  have harg : 1 + x ≠ 0 := by
    intro h
    apply hx
    linarith
  have hlog :
      HasDerivAt (fun x : ℝ => Real.log (1 + x)) ((1 + x)⁻¹) x := by
    simpa using
      (Real.hasDerivAt_log harg).comp x
        ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x))
  have hinv :
      HasDerivAt (fun x : ℝ => (1 + x)⁻¹) (-(1 : ℝ) / (1 + x) ^ 2) x := by
    have hbase : HasDerivAt (fun x : ℝ => 1 + x) (1 : ℝ) x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
    simpa using hbase.inv harg
  have hdiv :
      HasDerivAt (fun x : ℝ => 2 / (1 + x))
        (2 * (-(1 : ℝ) / (1 + x) ^ 2)) x := by
    simpa [div_eq_mul_inv] using hinv.const_mul (2 : ℝ)
  have hmain := (hlog.const_mul (2 : ℝ)).add hdiv
  convert hmain using 1
  field_simp [harg]
  ring

/-- Closed form for the finite transformed-kernel integral. -/
theorem transformedKernel_integral_eq {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in (0 : ℝ)..R, 2 * x / (1 + x) ^ 2 =
      2 * Real.log (1 + R) + 2 / (1 + R) - 2 := by
  let F : ℝ → ℝ := fun x => 2 * Real.log (1 + x) + 2 / (1 + x)
  let K : ℝ → ℝ := fun x => 2 * x / (1 + x) ^ 2
  have hden_pos_Icc : ∀ x ∈ Set.Icc (0 : ℝ) R, 0 < 1 + x := by
    intro x hx
    linarith [hx.1]
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) R) := by
    have hbase : ContinuousOn (fun x : ℝ => 1 + x) (Set.Icc (0 : ℝ) R) :=
      continuousOn_const.add continuousOn_id
    have hbase_ne : ∀ x ∈ Set.Icc (0 : ℝ) R, (1 + x : ℝ) ≠ 0 := by
      intro x hx
      exact ne_of_gt (hden_pos_Icc x hx)
    have hlog : ContinuousOn (fun x : ℝ => Real.log (1 + x)) (Set.Icc (0 : ℝ) R) :=
      hbase.log hbase_ne
    have hdiv : ContinuousOn (fun x : ℝ => (2 : ℝ) / (1 + x)) (Set.Icc (0 : ℝ) R) := by
      exact continuousOn_const.div hbase hbase_ne
    simpa [F] using (continuousOn_const.mul hlog).add hdiv
  have hKcont : ContinuousOn K (Set.uIcc (0 : ℝ) R) := by
    rw [Set.uIcc_of_le hR]
    have hbase : ContinuousOn (fun x : ℝ => 1 + x) (Set.Icc (0 : ℝ) R) :=
      continuousOn_const.add continuousOn_id
    have hden_ne : ∀ x ∈ Set.Icc (0 : ℝ) R, (1 + x : ℝ) ^ 2 ≠ 0 := by
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (hden_pos_Icc x hx))
    have hnum : ContinuousOn (fun x : ℝ => (2 : ℝ) * x) (Set.Icc (0 : ℝ) R) :=
      continuousOn_const.mul continuousOn_id
    have hden : ContinuousOn (fun x : ℝ => (1 + x) ^ 2) (Set.Icc (0 : ℝ) R) :=
      hbase.pow 2
    simpa [K] using hnum.div hden hden_ne
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) R, HasDerivAt F (K x) x := by
    intro x hx
    exact transformedKernel_antideriv_hasDerivAt (by linarith [hx.1])
  have hint : IntervalIntegrable K MeasureTheory.volume (0 : ℝ) R :=
    hKcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR hFcont hderiv hint
  simpa [F, K] using hFTC

/-- Factored version of `transformedKernel_integral_eq`. -/
theorem transformedKernel_integral_eq_two_mul {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in (0 : ℝ)..R, 2 * x / (1 + x) ^ 2 =
      2 * (Real.log (1 + R) + 1 / (1 + R) - 1) := by
  rw [transformedKernel_integral_eq hR]
  ring

/-- Finite correction-kernel integral after the substitution `u = (1 - x²)⁻¹`. -/
theorem corrKernel_integral_eq_transformed {U : ℝ} (hU : 1 ≤ U) :
    ∫ u in (1 : ℝ)..U, corrKernel u =
      ∫ x in (0 : ℝ)..Real.sqrt (1 - 1 / U), 2 * x / (1 + x) ^ 2 := by
  let R : ℝ := Real.sqrt (1 - 1 / U)
  have hU_pos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hU_ne : U ≠ 0 := ne_of_gt hU_pos
  have hinv_pos : 0 < 1 / U := by positivity
  have harg_nonneg : 0 ≤ 1 - 1 / U := by
    rw [sub_nonneg]
    exact by
      simpa [one_div] using inv_le_one_of_one_le₀ hU
  have hR_nonneg : 0 ≤ R := Real.sqrt_nonneg _
  have hR_lt_one : R < 1 := by
    dsimp [R]
    rw [Real.sqrt_lt' zero_lt_one]
    nlinarith [hinv_pos]
  have hR_sq : R ^ 2 = 1 - 1 / U := by
    dsimp [R]
    rw [Real.sq_sqrt harg_nonneg]
  have hden_pos_uIcc : ∀ x ∈ Set.uIcc (0 : ℝ) R, 0 < 1 - x ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := by
      rw [Set.uIcc_of_le hR_nonneg] at hx
      exact hx.1
    have hxR : x ≤ R := by
      rw [Set.uIcc_of_le hR_nonneg] at hx
      exact hx.2
    have hx_lt_one : x < 1 := lt_of_le_of_lt hxR hR_lt_one
    have hsq_lt : x ^ 2 < 1 := by nlinarith [mul_self_lt_mul_self hx0 hx_lt_one]
    linarith
  have hcont : ContinuousOn corrKernelChange (Set.uIcc (0 : ℝ) R) := by
    have hbase : ContinuousOn (fun x : ℝ => 1 - x ^ 2) (Set.uIcc (0 : ℝ) R) :=
      continuousOn_const.sub (continuousOn_id.pow 2)
    exact hbase.inv₀ (fun x hx => ne_of_gt (hden_pos_uIcc x hx))
  have hderiv : ∀ x ∈ Set.Ioo (min (0 : ℝ) R) (max (0 : ℝ) R),
      HasDerivAt corrKernelChange (corrKernelChangeDeriv x) x := by
    intro x hx
    have hx_u : x ∈ Set.uIcc (0 : ℝ) R := mem_uIcc_of_mem_Ioo_min_max hx
    exact corrKernel_change_hasDerivAt (ne_of_gt (hden_pos_uIcc x hx_u))
  have hderiv_nonneg : ∀ x ∈ Set.Ioo (min (0 : ℝ) R) (max (0 : ℝ) R),
      0 ≤ corrKernelChangeDeriv x := by
    intro x hx
    have hx_u : x ∈ Set.uIcc (0 : ℝ) R := mem_uIcc_of_mem_Ioo_min_max hx
    have hx0 : 0 ≤ x := by
      rw [Set.uIcc_of_le hR_nonneg] at hx_u
      exact hx_u.1
    unfold corrKernelChangeDeriv
    positivity
  have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := R) (f := corrKernelChange) (f' := corrKernelChangeDeriv)
    (g := corrKernel) hcont hderiv hderiv_nonneg
  have hphi0 : corrKernelChange 0 = 1 := by simp [corrKernelChange]
  have hphiR : corrKernelChange R = U := by
    unfold corrKernelChange
    rw [hR_sq]
    field_simp [hU_ne]
    ring
  have hleft_congr :
      ∫ x in (0 : ℝ)..R, (corrKernel ∘ corrKernelChange) x * corrKernelChangeDeriv x =
        ∫ x in (0 : ℝ)..R, 2 * x / (1 + x) ^ 2 := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) R := by
      rw [Set.uIcc_of_le hR_nonneg] at hx
      exact hx
    have hx_lt_one : x < 1 := lt_of_le_of_lt hxI.2 hR_lt_one
    simpa [Function.comp_def] using corrKernel_change_integrand_eq hxI.1 hx_lt_one
  calc
    ∫ u in (1 : ℝ)..U, corrKernel u =
        ∫ u in corrKernelChange 0..corrKernelChange R, corrKernel u := by
      rw [hphi0, hphiR]
    _ = ∫ x in (0 : ℝ)..R, (corrKernel ∘ corrKernelChange) x * corrKernelChangeDeriv x :=
      hsubst.symm
    _ = ∫ x in (0 : ℝ)..R, 2 * x / (1 + x) ^ 2 := hleft_congr
    _ = ∫ x in (0 : ℝ)..Real.sqrt (1 - 1 / U), 2 * x / (1 + x) ^ 2 := by rfl

/-- Closed form for the finite correction-kernel integral. -/
theorem corrKernel_integral_eq_closed {U : ℝ} (hU : 1 ≤ U) :
    ∫ u in (1 : ℝ)..U, corrKernel u =
      2 * (Real.log (1 + Real.sqrt (1 - 1 / U)) +
        1 / (1 + Real.sqrt (1 - 1 / U)) - 1) := by
  have hR : 0 ≤ Real.sqrt (1 - 1 / U) := Real.sqrt_nonneg _
  rw [corrKernel_integral_eq_transformed hU, transformedKernel_integral_eq_two_mul hR]

/-- The correction-kernel integral tends to the constant used in the correction asymptotic. -/
theorem corrKernel_integral_tendsto :
    Tendsto (fun U : ℝ => ∫ u in (1 : ℝ)..U, corrKernel u)
      Filter.atTop (𝓝 (2 * Real.log 2 - 1)) := by
  let R : ℝ → ℝ := fun U => Real.sqrt (1 - 1 / U)
  have hbase : Tendsto (fun U : ℝ => 1 - U⁻¹) Filter.atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub tendsto_inv_atTop_zero
  have hR : Tendsto R Filter.atTop (𝓝 1) := by
    have hs := hbase.sqrt
    simpa [R, one_div] using hs
  have hden : Tendsto (fun U : ℝ => 1 + R U) Filter.atTop (𝓝 (1 + 1)) :=
    tendsto_const_nhds.add hR
  have hlog : Tendsto (fun U : ℝ => Real.log (1 + R U)) Filter.atTop (𝓝 (Real.log 2)) := by
    have h := hden.log (by norm_num : (1 + 1 : ℝ) ≠ 0)
    convert h using 2
    norm_num
  have hinv : Tendsto (fun U : ℝ => 1 / (1 + R U)) Filter.atTop (𝓝 (1 / 2)) := by
    have h := hden.inv₀ (by norm_num : (1 + 1 : ℝ) ≠ 0)
    have h' : Tendsto (fun U : ℝ => 1 / (1 + R U)) Filter.atTop (𝓝 ((1 + 1 : ℝ)⁻¹)) := by
      simpa [one_div] using h
    convert h' using 2
    norm_num
  have hinside : Tendsto (fun U : ℝ =>
      Real.log (1 + R U) + 1 / (1 + R U) - 1) Filter.atTop
      (𝓝 (Real.log 2 + 1 / 2 - 1)) :=
    (hlog.add hinv).sub tendsto_const_nhds
  have hclosed : Tendsto (fun U : ℝ =>
      2 * (Real.log (1 + R U) + 1 / (1 + R U) - 1)) Filter.atTop
      (𝓝 (2 * (Real.log 2 + 1 / 2 - 1))) :=
    tendsto_const_nhds.mul hinside
  have hclosed' : Tendsto (fun U : ℝ =>
      2 * (Real.log (1 + R U) + 1 / (1 + R U) - 1)) Filter.atTop
      (𝓝 (2 * Real.log 2 - 1)) := by
    have htarget : 2 * (Real.log 2 + (2 : ℝ)⁻¹ - 1) = 2 * Real.log 2 - 1 := by
      norm_num
      ring
    simpa [htarget] using hclosed
  have heq : (fun U : ℝ => ∫ u in (1 : ℝ)..U, corrKernel u) =ᶠ[Filter.atTop]
      fun U : ℝ => 2 * (Real.log (1 + R U) + 1 / (1 + R U) - 1) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with U hU
    simpa [R] using corrKernel_integral_eq_closed hU
  exact hclosed'.congr' heq.symm

/-- The full correction term has the coefficient obtained from the correction kernel. -/
theorem correction_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      Rcorr D X - 2 * lam * (2 * Real.log 2 - 1) * X / Real.log X)
      =o[Filter.atTop] scaleReal := by
  rcases Rcorr_tail_bound D with ⟨Ctail, hCtail_pos, htail⟩
  refine IsLittleO.of_bound fun c hc => ?_
  have hquarter_pos : 0 < c / 4 := by positivity
  have hlam_pos : 0 < lam := by
    unfold lam
    positivity
  have htwo_lam_pos : 0 < 2 * lam := by positivity
  have hdelta_pos : 0 < c / (4 * (2 * lam)) := by positivity
  have hkernel_tendsto := corrKernel_integral_tendsto
  rw [Metric.tendsto_atTop] at hkernel_tendsto
  rcases hkernel_tendsto (c / (4 * (2 * lam))) hdelta_pos with ⟨Nker, hNker⟩
  let U : ℝ := max (2 : ℝ) (max Nker (4 * Ctail / c))
  have hU_two : 2 ≤ U := le_max_left _ _
  have hU_one : 1 ≤ U := le_trans (by norm_num : (1 : ℝ) ≤ 2) hU_two
  have hU_pos : 0 < U := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hU_two
  have hNkerU : Nker ≤ U := by
    exact (le_max_left Nker (4 * Ctail / c)).trans
      (le_max_right (2 : ℝ) (max Nker (4 * Ctail / c)))
  have hU_tail_ge : 4 * Ctail / c ≤ U := by
    exact (le_max_right Nker (4 * Ctail / c)).trans
      (le_max_right (2 : ℝ) (max Nker (4 * Ctail / c)))
  have hCtail_div_U_le : Ctail / U ≤ c / 4 := by
    have hC_le : Ctail ≤ (c / 4) * U := by
      calc
        Ctail = (c / 4) * (4 * Ctail / c) := by
          field_simp [ne_of_gt hc]
        _ ≤ (c / 4) * U :=
          mul_le_mul_of_nonneg_left hU_tail_ge (le_of_lt hquarter_pos)
    exact (div_le_iff₀ hU_pos).2 hC_le
  let K : ℝ := 2 * Real.log 2 - 1
  let IU : ℝ := ∫ u in (1 : ℝ)..U, corrKernel u
  have hkernel_dist := hNker U hNkerU
  rw [Real.dist_eq] at hkernel_dist
  have hcoeff_abs : |2 * lam * IU - 2 * lam * K| ≤ c / 4 := by
    calc
      |2 * lam * IU - 2 * lam * K| = |2 * lam * (IU - K)| := by ring_nf
      _ = |2 * lam| * |IU - K| := abs_mul _ _
      _ = (2 * lam) * |IU - K| := by rw [abs_of_pos htwo_lam_pos]
      _ ≤ (2 * lam) * (c / (4 * (2 * lam))) :=
        mul_le_mul_of_nonneg_left (le_of_lt hkernel_dist) (le_of_lt htwo_lam_pos)
      _ = c / 4 := by
        field_simp [ne_of_gt htwo_lam_pos]
  have htrunc_o := RcorrTrunc_asymptotic D hU_one
  filter_upwards [htrunc_o.def hquarter_pos, htail U hU_two, eventually_gt_atTop (1 : ℝ)] with
    X htruncX htailX hX_gt
  have hX_pos : 0 < X := lt_trans zero_lt_one hX_gt
  have hlog_pos : 0 < Real.log X := Real.log_pos hX_gt
  have hlog_ne : Real.log X ≠ 0 := ne_of_gt hlog_pos
  have hscale_pos : 0 < scaleReal X := by
    rw [scaleReal]
    exact div_pos hX_pos hlog_pos
  have htail_norm : ‖Rcorr D X - RcorrTrunc D X U‖ ≤ (c / 4) * ‖scaleReal X‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg htailX.1]
    rw [Real.norm_eq_abs, abs_of_pos hscale_pos]
    have htail_le_scale : Rcorr D X - RcorrTrunc D X U ≤ (Ctail / U) * scaleReal X := by
      calc
        Rcorr D X - RcorrTrunc D X U ≤ Ctail * X / (U * Real.log X) := htailX.2
        _ = (Ctail / U) * scaleReal X := by
          rw [scaleReal]
          field_simp [ne_of_gt hU_pos, hlog_ne]
    exact htail_le_scale.trans
      (mul_le_mul_of_nonneg_right hCtail_div_U_le (le_of_lt hscale_pos))
  have hcoeff_norm : ‖(2 * lam * IU - 2 * lam * K) * scaleReal X‖ ≤
      (c / 4) * ‖scaleReal X‖ := by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hcoeff_abs (norm_nonneg _)
  let Ttail : ℝ := Rcorr D X - RcorrTrunc D X U
  let Terr : ℝ := RcorrTrunc D X U - 2 * lam * IU * X / Real.log X
  let Ecoeff : ℝ := (2 * lam * IU - 2 * lam * K) * scaleReal X
  have htail_norm' : ‖Ttail‖ ≤ (c / 4) * ‖scaleReal X‖ := by
    simpa [Ttail] using htail_norm
  have htrunc_norm' : ‖Terr‖ ≤ (c / 4) * ‖scaleReal X‖ := by
    simpa [Terr, IU] using htruncX
  have hcoeff_norm' : ‖Ecoeff‖ ≤ (c / 4) * ‖scaleReal X‖ := by
    simpa [Ecoeff] using hcoeff_norm
  have hdecomp :
      Rcorr D X - 2 * lam * K * X / Real.log X =
        Ttail + Terr + Ecoeff := by
    dsimp [Ttail, Terr, Ecoeff]
    rw [scaleReal]
    ring
  calc
    ‖Rcorr D X - 2 * lam * K * X / Real.log X‖
        = ‖Ttail + Terr + Ecoeff‖ := by rw [hdecomp]
    _ ≤ ‖Ttail‖ + ‖Terr‖ + ‖Ecoeff‖ := by
      calc
        ‖Ttail + Terr + Ecoeff‖ ≤ ‖Ttail + Terr‖ + ‖Ecoeff‖ := norm_add_le _ _
        _ ≤ (‖Ttail‖ + ‖Terr‖) + ‖Ecoeff‖ := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right (norm_add_le Ttail Terr) ‖Ecoeff‖
        _ = ‖Ttail‖ + ‖Terr‖ + ‖Ecoeff‖ := by ring
    _ ≤ (c / 4) * ‖scaleReal X‖ + (c / 4) * ‖scaleReal X‖ +
          (c / 4) * ‖scaleReal X‖ := by
      gcongr
    _ ≤ c * ‖scaleReal X‖ := by
      have hs : 0 ≤ ‖scaleReal X‖ := norm_nonneg _
      nlinarith

/-- The large continuous-integral contribution after the square/correction split. -/
theorem large_continuous_integral_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      (∫ t in X..D.Phi X, D.f t * GX D X t) -
        (X +
          (lam * (1 - 2 * B + 2 * Real.log (lam / 2)) +
            2 * lam * (2 * Real.log 2 - 1)) * X / Real.log X))
      =o[Filter.atTop] scaleReal := by
  have hsquare := square_integral_term_asymptotic D
  have hcorr := correction_asymptotic D
  have hsum := hsquare.add hcorr
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards [continuous_integral_square_correction_split D] with X hsplit
  rw [hsplit]
  ring

end FloorSaving
