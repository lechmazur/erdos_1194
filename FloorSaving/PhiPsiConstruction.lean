import FloorSaving.PhiPsiData

noncomputable section

open Filter Topology Asymptotics
open scoped Real

namespace FloorSaving

/-- The derivative of `w - log w + B` on the positive tail. -/
def Hderiv (w : ℝ) : ℝ :=
  1 - 1 / w

/-- `H B w = w - log w + B` is positive on a real tail. -/
theorem eventually_H_pos_atTop (B : ℝ) :
    ∀ᶠ w : ℝ in Filter.atTop, 0 < H B w := by
  have hsmall : Real.log =o[Filter.atTop] (fun w : ℝ => w) :=
    Real.isLittleO_log_id_atTop
  filter_upwards [hsmall.def (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_ge_atTop (0 : ℝ),
      eventually_gt_atTop (-2 * B)] with w hsmallw hw_nonneg hw_gt
  have hlog_le : Real.log w ≤ (1 / 2 : ℝ) * w := by
    calc
      Real.log w ≤ ‖Real.log w‖ := by
        simpa [Real.norm_eq_abs] using le_abs_self (Real.log w)
      _ ≤ (1 / 2 : ℝ) * ‖w‖ := hsmallw
      _ = (1 / 2 : ℝ) * w := by
        rw [Real.norm_eq_abs, abs_of_nonneg hw_nonneg]
  rw [H]
  nlinarith

/-- The derivative numerator for `PhiFormula` is positive on a real tail. -/
theorem eventually_two_mul_H_sub_Hderiv_pos_atTop (B : ℝ) :
    ∀ᶠ w : ℝ in Filter.atTop, 0 < 2 * H B w - Hderiv w := by
  have hsmall : Real.log =o[Filter.atTop] (fun w : ℝ => w) :=
    Real.isLittleO_log_id_atTop
  filter_upwards [hsmall.def (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_gt_atTop (0 : ℝ),
      eventually_gt_atTop (1 - 2 * B)] with w hsmallw hw_pos hw_gt
  have hw_nonneg : 0 ≤ w := le_of_lt hw_pos
  have hlog_le : Real.log w ≤ (1 / 2 : ℝ) * w := by
    calc
      Real.log w ≤ ‖Real.log w‖ := by
        simpa [Real.norm_eq_abs] using le_abs_self (Real.log w)
      _ ≤ (1 / 2 : ℝ) * ‖w‖ := hsmallw
      _ = (1 / 2 : ℝ) * w := by
        rw [Real.norm_eq_abs, abs_of_nonneg hw_nonneg]
  have hinv_pos : 0 < 1 / w := one_div_pos.mpr hw_pos
  rw [H, Hderiv]
  nlinarith

/-- Eventually `2H-H'` dominates `H`; this is the algebraic core of the derivative bound. -/
theorem eventually_H_le_two_mul_H_sub_Hderiv_atTop (B : ℝ) :
    ∀ᶠ w : ℝ in Filter.atTop, H B w ≤ 2 * H B w - Hderiv w := by
  have hsmall : Real.log =o[Filter.atTop] (fun w : ℝ => w) :=
    Real.isLittleO_log_id_atTop
  filter_upwards [hsmall.def (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_gt_atTop (0 : ℝ),
      eventually_gt_atTop (2 * (1 - B))] with w hsmallw hw_pos hw_gt
  have hw_nonneg : 0 ≤ w := le_of_lt hw_pos
  have hlog_le : Real.log w ≤ (1 / 2 : ℝ) * w := by
    calc
      Real.log w ≤ ‖Real.log w‖ := by
        simpa [Real.norm_eq_abs] using le_abs_self (Real.log w)
      _ ≤ (1 / 2 : ℝ) * ‖w‖ := hsmallw
      _ = (1 / 2 : ℝ) * w := by
        rw [Real.norm_eq_abs, abs_of_nonneg hw_nonneg]
  have hH_ge_one : (1 : ℝ) ≤ H B w := by
    rw [H]
    nlinarith
  have hderiv_le_one : Hderiv w ≤ 1 := by
    rw [Hderiv]
    have hinv_nonneg : 0 ≤ 1 / w := by positivity
    nlinarith
  nlinarith

/-- `H B (log x)` is positive on an `x → ∞` tail. -/
theorem eventually_H_log_pos_atTop (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, 0 < H B (Real.log x) :=
  Real.tendsto_log_atTop.eventually (eventually_H_pos_atTop B)

/-- The derivative numerator for `PhiFormula` is positive after composing with `log`. -/
theorem eventually_two_mul_H_log_sub_Hderiv_log_pos_atTop (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      0 < 2 * H B (Real.log x) - Hderiv (Real.log x) :=
  Real.tendsto_log_atTop.eventually (eventually_two_mul_H_sub_Hderiv_pos_atTop B)

/-- After composing with `log`, `2H-H'` eventually dominates `H`. -/
theorem eventually_H_log_le_two_mul_H_log_sub_Hderiv_log_atTop (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      H B (Real.log x) ≤ 2 * H B (Real.log x) - Hderiv (Real.log x) :=
  Real.tendsto_log_atTop.eventually (eventually_H_le_two_mul_H_sub_Hderiv_atTop B)

/-- The denominator of `PhiFormula` is nonzero on a real tail. -/
theorem eventually_H_log_ne_zero_atTop (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, H B (Real.log x) ≠ 0 := by
  filter_upwards [eventually_H_log_pos_atTop B] with x hx
  exact ne_of_gt hx

/-- `PhiFormula B x` is positive on a real tail. -/
theorem eventually_PhiFormula_pos_atTop (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, 0 < PhiFormula B x := by
  have hlam : 0 < lam := by
    unfold lam
    positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_H_log_pos_atTop B] with x hx hH
  rw [PhiFormula]
  positivity

/-- On a real tail, the denominator of `PhiFormula` is at most `x` itself. -/
theorem eventually_H_log_le_self_atTop (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, H B (Real.log x) ≤ x := by
  have hsmall : Real.log =o[Filter.atTop] (fun x : ℝ => x) :=
    Real.isLittleO_log_id_atTop
  have hloglog : Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hsmall.def (by norm_num : (0 : ℝ) < 1),
      eventually_ge_atTop (0 : ℝ),
      hloglog.eventually_ge_atTop B] with x hsmallx hx_nonneg hB
  have hlog_le : Real.log x ≤ x := by
    calc
      Real.log x ≤ ‖Real.log x‖ := by
        simpa [Real.norm_eq_abs] using le_abs_self (Real.log x)
      _ ≤ (1 : ℝ) * ‖x‖ := hsmallx
      _ = x := by
        rw [Real.norm_eq_abs, abs_of_nonneg hx_nonneg]
        ring
  rw [H]
  nlinarith

/-- `PhiFormula` eventually dominates the linear function `lam * x`. -/
theorem eventually_lam_mul_self_le_PhiFormula (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, lam * x ≤ PhiFormula B x := by
  have hlam : 0 < lam := by
    unfold lam
    positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_H_log_pos_atTop B,
      eventually_H_log_le_self_atTop B] with x hx hH hHle
  have hx_le : x ≤ x ^ 2 / H B (Real.log x) := by
    field_simp [ne_of_gt hH]
    nlinarith
  calc
    lam * x ≤ lam * (x ^ 2 / H B (Real.log x)) :=
      mul_le_mul_of_nonneg_left hx_le (le_of_lt hlam)
    _ = PhiFormula B x := by
      rw [PhiFormula]
      ring

/-- `PhiFormula B x` tends to infinity on the real tail. -/
theorem PhiFormula_tendsto_atTop (B : ℝ) :
    Tendsto (PhiFormula B) Filter.atTop Filter.atTop := by
  have hlam : 0 < lam := by
    unfold lam
    positivity
  refine tendsto_atTop_mono' Filter.atTop (eventually_lam_mul_self_le_PhiFormula B) ?_
  exact tendsto_id.const_mul_atTop hlam

/-- Derivative of the composed denominator `H B (log x)` on the positive tail. -/
theorem H_log_hasDerivAt {B x : ℝ} (hx : x ≠ 0) (hlogx : Real.log x ≠ 0) :
    HasDerivAt (fun y : ℝ => H B (Real.log y))
      (Hderiv (Real.log x) / x) x := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx
  have hloglog : HasDerivAt (fun y : ℝ => Real.log (Real.log y))
      ((Real.log x)⁻¹ * x⁻¹) x :=
    (Real.hasDerivAt_log hlogx).comp x hlog
  convert (hlog.sub hloglog).const_add B using 1
  · funext y
    simp [H, Pi.sub_apply]
    ring_nf
  · rw [Hderiv]
    ring

/-- Derivative of `PhiFormula`; the sign-critical factor is `2H-H'`. -/
theorem PhiFormula_hasDerivAt {B x : ℝ}
    (hx : x ≠ 0) (hlogx : Real.log x ≠ 0) (hH : H B (Real.log x) ≠ 0) :
    HasDerivAt (PhiFormula B)
      (lam * x * (2 * H B (Real.log x) - Hderiv (Real.log x)) /
        (H B (Real.log x)) ^ 2) x := by
  have hnum : HasDerivAt (fun y : ℝ => lam * y ^ 2) (lam * (2 * x)) x := by
    simpa [mul_assoc] using ((hasDerivAt_id x).pow 2).const_mul lam
  have hden : HasDerivAt (fun y : ℝ => H B (Real.log y))
      (Hderiv (Real.log x) / x) x :=
    H_log_hasDerivAt hx hlogx
  convert hnum.div hden hH using 1
  field_simp [hx, hH]

/-- The derivative formula for `PhiFormula` is available on a real tail. -/
theorem eventually_PhiFormula_hasDerivAt (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      HasDerivAt (PhiFormula B)
        (lam * x * (2 * H B (Real.log x) - Hderiv (Real.log x)) /
          (H B (Real.log x)) ^ 2) x := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_H_log_ne_zero_atTop B] with x hx hH
  have hx_ne : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog_ne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  exact PhiFormula_hasDerivAt hx_ne hlog_ne hH

/-- The derivative value of `PhiFormula` is positive on a real tail. -/
theorem eventually_PhiFormula_deriv_value_pos_atTop (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      0 < lam * x * (2 * H B (Real.log x) - Hderiv (Real.log x)) /
        (H B (Real.log x)) ^ 2 := by
  have hlam : 0 < lam := by
    unfold lam
    positivity
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_H_log_pos_atTop B,
      eventually_two_mul_H_log_sub_Hderiv_log_pos_atTop B] with x hx hH hnum
  positivity

/-- Algebraic estimate behind `|f'| ≪ f/t` on the inverse branch. -/
theorem eventually_inverse_derivative_model_le_f_over_Phi (B : ℝ) :
    ∀ᶠ r : ℝ in Filter.atTop,
      H B (Real.log r) ^ 2 /
          (lam * r ^ 3 * (2 * H B (Real.log r) - Hderiv (Real.log r))) ≤
        (1 / r) / PhiFormula B r := by
  have hlam_pos : 0 < lam := by
    unfold lam
    positivity
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_H_log_pos_atTop B,
      eventually_H_log_le_two_mul_H_log_sub_Hderiv_log_atTop B] with r hr hH hHle
  have hr_pos : 0 < r := lt_trans zero_lt_one hr
  have hN_pos : 0 < 2 * H B (Real.log r) - Hderiv (Real.log r) :=
    lt_of_lt_of_le hH hHle
  have hdenH_pos : 0 < lam * r ^ 3 * H B (Real.log r) := by positivity
  have hden_le :
      lam * r ^ 3 * H B (Real.log r) ≤
        lam * r ^ 3 * (2 * H B (Real.log r) - Hderiv (Real.log r)) := by
    exact mul_le_mul_of_nonneg_left hHle (by positivity)
  calc
    H B (Real.log r) ^ 2 /
          (lam * r ^ 3 * (2 * H B (Real.log r) - Hderiv (Real.log r)))
        ≤ H B (Real.log r) ^ 2 / (lam * r ^ 3 * H B (Real.log r)) :=
          div_le_div_of_nonneg_left (sq_nonneg _) hdenH_pos hden_le
    _ = (1 / r) / PhiFormula B r := by
      rw [PhiFormula]
      field_simp [ne_of_gt hr_pos, ne_of_gt hH, ne_of_gt hlam_pos]

/-- The actual derivative of `PhiFormula` is positive on a real tail. -/
theorem eventually_PhiFormula_deriv_pos_atTop (B : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, 0 < deriv (PhiFormula B) x := by
  filter_upwards [eventually_PhiFormula_hasDerivAt B,
      eventually_PhiFormula_deriv_value_pos_atTop B] with x hder hpos
  rw [hder.deriv]
  exact hpos

/-- `PhiFormula` is strictly increasing on some closed real tail. -/
theorem exists_PhiFormula_strictMonoOn_tail (B : ℝ) :
    ∃ T : ℝ, 1 < T ∧ StrictMonoOn (PhiFormula B) (Set.Ici T) := by
  rcases Filter.eventually_atTop.mp (eventually_PhiFormula_deriv_pos_atTop B) with
    ⟨Tder, hder⟩
  rcases Filter.eventually_atTop.mp (eventually_H_log_ne_zero_atTop B) with
    ⟨TH, hH⟩
  let T : ℝ := max (max Tder TH) 2
  have hTder : Tder ≤ T := by
    dsimp [T]
    exact le_trans (le_max_left Tder TH) (le_max_left (max Tder TH) 2)
  have hTH : TH ≤ T := by
    dsimp [T]
    exact le_trans (le_max_right Tder TH) (le_max_left (max Tder TH) 2)
  have hTone : 1 < T := by
    dsimp [T]
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right (max Tder TH) 2)
  refine ⟨T, hTone, strictMonoOn_of_deriv_pos (convex_Ici T) ?_ ?_⟩
  · intro x hx
    have hx_ge : T ≤ x := by
      simpa using hx
    have hx_gt_one : 1 < x := lt_of_lt_of_le hTone hx_ge
    have hx_ne : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx_gt_one)
    have hlog_ne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx_gt_one)
    have hH_ne : H B (Real.log x) ≠ 0 := hH x (le_trans hTH hx_ge)
    exact (PhiFormula_hasDerivAt hx_ne hlog_ne hH_ne).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    exact hder x (le_trans hTder (le_of_lt hx))

/-- Choose a natural threshold for the monotone/divergent branch of `PhiFormula`. -/
theorem exists_nat_PhiFormula_tail (B : ℝ) :
    ∃ N0 : ℕ,
      3 ≤ N0 ∧
        0 < PhiFormula B (N0 : ℝ) ∧
          ContinuousOn (PhiFormula B) (Set.Ici (N0 : ℝ)) ∧
          StrictMonoOn (PhiFormula B) (Set.Ici (N0 : ℝ)) ∧
            MonotoneOn (PhiFormula B) (Set.Ici (N0 : ℝ)) ∧
              (∀ x : ℝ, (N0 : ℝ) ≤ x →
                PhiFormula B (N0 : ℝ) ≤ PhiFormula B x) ∧
                Tendsto (PhiFormula B) Filter.atTop Filter.atTop := by
  rcases exists_PhiFormula_strictMonoOn_tail B with ⟨T, _hTone, hstrictT⟩
  rcases Filter.eventually_atTop.mp (eventually_PhiFormula_pos_atTop B) with ⟨Tpos, hpos⟩
  rcases Filter.eventually_atTop.mp (eventually_H_log_ne_zero_atTop B) with ⟨TH, hH⟩
  rcases exists_nat_ge (max T (max Tpos (max TH (3 : ℝ)))) with ⟨N0, hN0⟩
  have hT_N0 : T ≤ (N0 : ℝ) :=
    le_trans (le_max_left T (max Tpos (max TH (3 : ℝ)))) hN0
  have hTpos_N0 : Tpos ≤ (N0 : ℝ) :=
    le_trans
      (le_trans (le_max_left Tpos (max TH (3 : ℝ)))
        (le_max_right T (max Tpos (max TH (3 : ℝ))))) hN0
  have hTH_N0 : TH ≤ (N0 : ℝ) :=
    le_trans
      (le_trans (le_trans (le_max_left TH (3 : ℝ)) (le_max_right Tpos (max TH (3 : ℝ))))
        (le_max_right T (max Tpos (max TH (3 : ℝ))))) hN0
  have hthree_N0_real : (3 : ℝ) ≤ (N0 : ℝ) :=
    le_trans
      (le_trans (le_trans (le_max_right TH (3 : ℝ)) (le_max_right Tpos (max TH (3 : ℝ))))
        (le_max_right T (max Tpos (max TH (3 : ℝ))))) hN0
  have hthree_N0 : 3 ≤ N0 := by
    exact_mod_cast hthree_N0_real
  have hposN0 : 0 < PhiFormula B (N0 : ℝ) := hpos (N0 : ℝ) hTpos_N0
  have hcontN : ContinuousOn (PhiFormula B) (Set.Ici (N0 : ℝ)) := by
    intro x hx
    have hx_ge : (N0 : ℝ) ≤ x := by
      simpa using hx
    have hx_gt_one : 1 < x := by
      nlinarith
    have hx_ne : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx_gt_one)
    have hlog_ne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx_gt_one)
    have hH_ne : H B (Real.log x) ≠ 0 := hH x (le_trans hTH_N0 hx_ge)
    exact (PhiFormula_hasDerivAt hx_ne hlog_ne hH_ne).continuousAt.continuousWithinAt
  have hstrictN : StrictMonoOn (PhiFormula B) (Set.Ici (N0 : ℝ)) := by
    intro x hx y hy hxy
    exact hstrictT (le_trans hT_N0 (by simpa using hx))
      (le_trans hT_N0 (by simpa using hy)) hxy
  have hmonoN : MonotoneOn (PhiFormula B) (Set.Ici (N0 : ℝ)) := hstrictN.monotoneOn
  have hmapsN :
      ∀ x : ℝ, (N0 : ℝ) ≤ x → PhiFormula B (N0 : ℝ) ≤ PhiFormula B x := by
    intro x hx
    exact hmonoN (by simp) (by simpa using hx) hx
  exact ⟨N0, hthree_N0, hposN0, hcontN, hstrictN, hmonoN, hmapsN,
    PhiFormula_tendsto_atTop B⟩

/-- The checked monotone branch of `PhiFormula` maps `[N0,∞)` onto its endpoint ray. -/
theorem PhiFormula_surjOn_tail {B : ℝ} {N0 : ℕ}
    (hcont : ContinuousOn (PhiFormula B) (Set.Ici (N0 : ℝ)))
    (htendsto : Tendsto (PhiFormula B) Filter.atTop Filter.atTop) :
    Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
      (Set.Ici (PhiFormula B (N0 : ℝ))) := by
  intro t ht
  have hEventually :
      ∀ᶠ x : ℝ in Filter.atTop, t ≤ PhiFormula B x ∧ (N0 : ℝ) ≤ x :=
    (htendsto.eventually_ge_atTop t).and (eventually_ge_atTop (N0 : ℝ))
  rcases hEventually.exists with ⟨X, hX_t, hX_tail⟩
  have hcontIcc : ContinuousOn (PhiFormula B) (Set.Icc (N0 : ℝ) X) :=
    hcont.mono Set.Icc_subset_Ici_self
  have hsurj :
      Set.SurjOn (PhiFormula B) (Set.Icc (N0 : ℝ) X)
        (Set.Icc (PhiFormula B (N0 : ℝ)) (PhiFormula B X)) :=
    hcontIcc.surjOn_Icc (Set.left_mem_Icc.mpr hX_tail) (Set.right_mem_Icc.mpr hX_tail)
  rcases hsurj ⟨ht, hX_t⟩ with ⟨x, hx, hxt⟩
  exact ⟨x, hx.1, hxt⟩

/-- Inverse branch for the monotone tail of `PhiFormula`. Its behavior is specified only on
the endpoint ray. -/
noncomputable def psiBranch (B : ℝ) (N0 : ℕ) : ℝ → ℝ :=
  Function.invFunOn (PhiFormula B) (Set.Ici (N0 : ℝ))

theorem PhiFormula_psiBranch_eq {B : ℝ} {N0 : ℕ}
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    {t : ℝ} (ht : PhiFormula B (N0 : ℝ) ≤ t) :
    PhiFormula B (psiBranch B N0 t) = t := by
  simpa [psiBranch] using hsurj.rightInvOn_invFunOn ht

theorem psiBranch_maps_tail {B : ℝ} {N0 : ℕ}
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    {t : ℝ} (ht : PhiFormula B (N0 : ℝ) ≤ t) :
    (N0 : ℝ) ≤ psiBranch B N0 t := by
  simpa [psiBranch] using hsurj.mapsTo_invFunOn ht

theorem psiBranch_right_inv {B : ℝ} {N0 : ℕ}
    (hstrict : StrictMonoOn (PhiFormula B) (Set.Ici (N0 : ℝ)))
    (hmaps : ∀ x : ℝ, (N0 : ℝ) ≤ x →
      PhiFormula B (N0 : ℝ) ≤ PhiFormula B x)
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    {x : ℝ} (hx : (N0 : ℝ) ≤ x) :
    psiBranch B N0 (PhiFormula B x) = x := by
  have htarget : PhiFormula B (N0 : ℝ) ≤ PhiFormula B x := hmaps x hx
  have hpsi_tail : (N0 : ℝ) ≤ psiBranch B N0 (PhiFormula B x) :=
    psiBranch_maps_tail hsurj htarget
  have hPhi :
      PhiFormula B (psiBranch B N0 (PhiFormula B x)) = PhiFormula B x :=
    PhiFormula_psiBranch_eq hsurj htarget
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hltPhi := hstrict hpsi_tail hx hlt
    rw [hPhi] at hltPhi
    exact (lt_irrefl (PhiFormula B x)) hltPhi
  · have hltPhi := hstrict hx hpsi_tail hgt
    rw [hPhi] at hltPhi
    exact (lt_irrefl (PhiFormula B x)) hltPhi

theorem psiBranch_le_of_le_Phi {B : ℝ} {N0 : ℕ}
    (hstrict : StrictMonoOn (PhiFormula B) (Set.Ici (N0 : ℝ)))
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    {t x : ℝ}
    (ht : PhiFormula B (N0 : ℝ) ≤ t)
    (hx : (N0 : ℝ) ≤ x)
    (htx : t ≤ PhiFormula B x) :
    psiBranch B N0 t ≤ x := by
  have hpsi_tail : (N0 : ℝ) ≤ psiBranch B N0 t := psiBranch_maps_tail hsurj ht
  have hPhi : PhiFormula B (psiBranch B N0 t) = t :=
    PhiFormula_psiBranch_eq hsurj ht
  by_contra hnot
  have hx_lt : x < psiBranch B N0 t := lt_of_not_ge hnot
  have hltPhi := hstrict hx hpsi_tail hx_lt
  rw [hPhi] at hltPhi
  exact (not_lt_of_ge htx) hltPhi

theorem psiBranch_mono_tail {B : ℝ} {N0 : ℕ}
    (hstrict : StrictMonoOn (PhiFormula B) (Set.Ici (N0 : ℝ)))
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ)))) :
    MonotoneOn (psiBranch B N0) (Set.Ici (PhiFormula B (N0 : ℝ))) := by
  intro t ht u hu htu
  exact psiBranch_le_of_le_Phi hstrict hsurj ht (psiBranch_maps_tail hsurj hu)
    (by rw [PhiFormula_psiBranch_eq hsurj hu]; exact htu)

/-- Interior target points have inverse values strictly above the left endpoint. -/
theorem psiBranch_gt_tail_endpoint {B : ℝ} {N0 : ℕ}
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    {t : ℝ} (ht : PhiFormula B (N0 : ℝ) < t) :
    (N0 : ℝ) < psiBranch B N0 t := by
  have ht_le : PhiFormula B (N0 : ℝ) ≤ t := le_of_lt ht
  have hpsi_tail : (N0 : ℝ) ≤ psiBranch B N0 t := psiBranch_maps_tail hsurj ht_le
  by_contra hnot
  have hpsi_le_N : psiBranch B N0 t ≤ (N0 : ℝ) := le_of_not_gt hnot
  have hpsi_eq : psiBranch B N0 t = (N0 : ℝ) := le_antisymm hpsi_le_N hpsi_tail
  have hPhi : PhiFormula B (psiBranch B N0 t) = t :=
    PhiFormula_psiBranch_eq hsurj ht_le
  rw [hpsi_eq] at hPhi
  linarith

/-- The inverse branch maps a tail-neighborhood of an interior target point onto a neighborhood
of the inverse value. -/
theorem psiBranch_tail_image_mem_nhds {B : ℝ} {N0 : ℕ}
    (hstrict : StrictMonoOn (PhiFormula B) (Set.Ici (N0 : ℝ)))
    (hmaps : ∀ x : ℝ, (N0 : ℝ) ≤ x →
      PhiFormula B (N0 : ℝ) ≤ PhiFormula B x)
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    {t : ℝ} (ht : PhiFormula B (N0 : ℝ) < t) :
    psiBranch B N0 '' Set.Ici (PhiFormula B (N0 : ℝ)) ∈
      𝓝 (psiBranch B N0 t) := by
  have htpsi : (N0 : ℝ) < psiBranch B N0 t :=
    psiBranch_gt_tail_endpoint hsurj ht
  have hIci : Set.Ici (N0 : ℝ) ∈ 𝓝 (psiBranch B N0 t) := Ici_mem_nhds htpsi
  refine mem_of_superset hIci ?_
  intro x hx
  refine ⟨PhiFormula B x, hmaps x hx, ?_⟩
  exact psiBranch_right_inv hstrict hmaps hsurj hx

/-- The inverse branch is continuous at every interior point of the target tail. -/
theorem psiBranch_continuousAt_tail_interior {B : ℝ} {N0 : ℕ}
    (hstrict : StrictMonoOn (PhiFormula B) (Set.Ici (N0 : ℝ)))
    (hmaps : ∀ x : ℝ, (N0 : ℝ) ≤ x →
      PhiFormula B (N0 : ℝ) ≤ PhiFormula B x)
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    {t : ℝ} (ht : PhiFormula B (N0 : ℝ) < t) :
    ContinuousAt (psiBranch B N0) t := by
  have hs : Set.Ici (PhiFormula B (N0 : ℝ)) ∈ 𝓝 t := Ici_mem_nhds ht
  have himage :
      psiBranch B N0 '' Set.Ici (PhiFormula B (N0 : ℝ)) ∈
        𝓝 (psiBranch B N0 t) :=
    psiBranch_tail_image_mem_nhds hstrict hmaps hsurj ht
  exact continuousAt_of_monotoneOn_of_image_mem_nhds
    (psiBranch_mono_tail hstrict hsurj) hs himage

/-- The inverse branch is eventually continuous on the real tail. -/
theorem eventually_psiBranch_continuousAt_tail {B : ℝ} {N0 : ℕ}
    (hstrict : StrictMonoOn (PhiFormula B) (Set.Ici (N0 : ℝ)))
    (hmaps : ∀ x : ℝ, (N0 : ℝ) ≤ x →
      PhiFormula B (N0 : ℝ) ≤ PhiFormula B x)
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ)))) :
    ∀ᶠ t : ℝ in Filter.atTop, ContinuousAt (psiBranch B N0) t := by
  filter_upwards [eventually_gt_atTop (PhiFormula B (N0 : ℝ))] with t ht
  exact psiBranch_continuousAt_tail_interior hstrict hmaps hsurj ht

/-- Derivative of the inverse branch at interior target-tail points where the formula derivative
of `PhiFormula` is nonzero. -/
theorem psiBranch_hasDerivAt_tail_interior {B : ℝ} {N0 : ℕ}
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
          (H B (Real.log (psiBranch B N0 t))) ^ 2)⁻¹ t := by
  let r : ℝ := psiBranch B N0 t
  have hcont : ContinuousAt (psiBranch B N0) t :=
    psiBranch_continuousAt_tail_interior hstrict hmaps hsurj ht
  have hr_gt_N0 : (N0 : ℝ) < r := by
    simpa [r] using psiBranch_gt_tail_endpoint hsurj ht
  have hN0_three : (3 : ℝ) ≤ (N0 : ℝ) := by
    exact_mod_cast hN0
  have hr_gt_one : 1 < r := by linarith
  have hr_pos : 0 < r := lt_trans zero_lt_one hr_gt_one
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hlog_ne : Real.log r ≠ 0 := ne_of_gt (Real.log_pos hr_gt_one)
  have hderPhi : HasDerivAt (PhiFormula B)
      (lam * r * (2 * H B (Real.log r) - Hderiv (Real.log r)) /
        (H B (Real.log r)) ^ 2) r :=
    PhiFormula_hasDerivAt hr_ne hlog_ne (by simpa [r] using hH)
  have hder_ne :
      lam * r * (2 * H B (Real.log r) - Hderiv (Real.log r)) /
          (H B (Real.log r)) ^ 2 ≠ 0 := by
    have hlam : 0 < lam := by
      unfold lam
      positivity
    have hnum' : 0 < 2 * H B (Real.log r) - Hderiv (Real.log r) := by
      simpa [r] using hnum
    positivity
  have hleft : ∀ᶠ y in 𝓝 t, PhiFormula B (psiBranch B N0 y) = y := by
    filter_upwards [Ici_mem_nhds ht] with y hy
    exact PhiFormula_psiBranch_eq hsurj hy
  exact hderPhi.of_local_left_inverse hcont hder_ne hleft

/-- The nonincreasing majorant attached to the selected inverse branch, with a constant extension
below the endpoint. -/
noncomputable def fBranch (B : ℝ) (N0 : ℕ) (t : ℝ) : ℝ :=
  if t < PhiFormula B (N0 : ℝ) then 1 / (N0 : ℝ) else 1 / psiBranch B N0 t

theorem fBranch_eq_tail {B : ℝ} {N0 : ℕ} {t : ℝ}
    (ht : PhiFormula B (N0 : ℝ) ≤ t) :
    fBranch B N0 t = 1 / psiBranch B N0 t := by
  simp [fBranch, not_lt_of_ge ht]

theorem psiBranch_pos_tail {B : ℝ} {N0 : ℕ}
    (hN0 : 3 ≤ N0)
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    {t : ℝ} (ht : PhiFormula B (N0 : ℝ) ≤ t) :
    0 < psiBranch B N0 t := by
  have hN0_pos : 0 < (N0 : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 0 < 3) hN0
  have hpsi_tail : (N0 : ℝ) ≤ psiBranch B N0 t := psiBranch_maps_tail hsurj ht
  exact lt_of_lt_of_le hN0_pos hpsi_tail

/-- Derivative of the majorant branch at interior target-tail points. -/
theorem fBranch_hasDerivAt_tail_interior {B : ℝ} {N0 : ℕ}
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
    HasDerivAt (fBranch B N0)
      (-(lam * psiBranch B N0 t *
        (2 * H B (Real.log (psiBranch B N0 t)) -
          Hderiv (Real.log (psiBranch B N0 t))) /
          (H B (Real.log (psiBranch B N0 t))) ^ 2)⁻¹ /
          (psiBranch B N0 t) ^ 2) t := by
  let dPhi : ℝ :=
    lam * psiBranch B N0 t *
      (2 * H B (Real.log (psiBranch B N0 t)) -
        Hderiv (Real.log (psiBranch B N0 t))) /
        (H B (Real.log (psiBranch B N0 t))) ^ 2
  have hpsi : HasDerivAt (psiBranch B N0) dPhi⁻¹ t := by
    dsimp [dPhi]
    exact psiBranch_hasDerivAt_tail_interior hN0 hstrict hmaps hsurj ht hH hnum
  have hpsi_pos : 0 < psiBranch B N0 t :=
    psiBranch_pos_tail hN0 hsurj (le_of_lt ht)
  have hinv : HasDerivAt (fun y : ℝ => (psiBranch B N0 y)⁻¹)
      (-(dPhi⁻¹) / (psiBranch B N0 t) ^ 2) t := by
    simpa using hpsi.inv (ne_of_gt hpsi_pos)
  have heq : fBranch B N0 =ᶠ[𝓝 t] fun y : ℝ => (psiBranch B N0 y)⁻¹ := by
    filter_upwards [Ici_mem_nhds ht] with y hy
    rw [fBranch_eq_tail hy]
    ring
  exact hinv.congr_of_eventuallyEq heq

theorem fBranch_pos {B : ℝ} {N0 : ℕ}
    (hN0 : 3 ≤ N0)
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    (t : ℝ) :
    0 < fBranch B N0 t := by
  have hN0_pos : 0 < (N0 : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 0 < 3) hN0
  by_cases ht : t < PhiFormula B (N0 : ℝ)
  · rw [fBranch, if_pos ht]
    exact one_div_pos.mpr hN0_pos
  · have htail : PhiFormula B (N0 : ℝ) ≤ t := le_of_not_gt ht
    have hpsi_pos : 0 < psiBranch B N0 t := psiBranch_pos_tail hN0 hsurj htail
    rw [fBranch, if_neg ht]
    exact one_div_pos.mpr hpsi_pos

theorem fBranch_antitone {B : ℝ} {N0 : ℕ}
    (hN0 : 3 ≤ N0)
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    (hpsi_mono : MonotoneOn (psiBranch B N0) (Set.Ici (PhiFormula B (N0 : ℝ)))) :
    Antitone (fBranch B N0) := by
  intro x y hxy
  have hN0_pos : 0 < (N0 : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 0 < 3) hN0
  by_cases hy : y < PhiFormula B (N0 : ℝ)
  · have hx : x < PhiFormula B (N0 : ℝ) := lt_of_le_of_lt hxy hy
    simp [fBranch, hx, hy]
  · have hy_tail : PhiFormula B (N0 : ℝ) ≤ y := le_of_not_gt hy
    by_cases hx : x < PhiFormula B (N0 : ℝ)
    · have hpsi_y_tail : (N0 : ℝ) ≤ psiBranch B N0 y :=
        psiBranch_maps_tail hsurj hy_tail
      have hle : 1 / psiBranch B N0 y ≤ 1 / (N0 : ℝ) :=
        one_div_le_one_div_of_le hN0_pos hpsi_y_tail
      simpa [fBranch, hx, hy] using hle
    · have hx_tail : PhiFormula B (N0 : ℝ) ≤ x := le_of_not_gt hx
      have hpsi_x_pos : 0 < psiBranch B N0 x := psiBranch_pos_tail hN0 hsurj hx_tail
      have hpsi_le : psiBranch B N0 x ≤ psiBranch B N0 y :=
        hpsi_mono hx_tail hy_tail hxy
      have hle : 1 / psiBranch B N0 y ≤ 1 / psiBranch B N0 x :=
        one_div_le_one_div_of_le hpsi_x_pos hpsi_le
      simpa [fBranch, hx, hy] using hle

theorem fBranch_measurable {B : ℝ} {N0 : ℕ}
    (hN0 : 3 ≤ N0)
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    (hpsi_mono : MonotoneOn (psiBranch B N0) (Set.Ici (PhiFormula B (N0 : ℝ)))) :
    Measurable (fBranch B N0) :=
  (fBranch_antitone hN0 hsurj hpsi_mono).measurable

theorem fBranch_intervalIntegrable {B : ℝ} {N0 : ℕ}
    (hN0 : 3 ≤ N0)
    (hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))))
    (hpsi_mono : MonotoneOn (psiBranch B N0) (Set.Ici (PhiFormula B (N0 : ℝ))))
    (a b : ℝ) :
    IntervalIntegrable (fBranch B N0) MeasureTheory.volume a b :=
  (fBranch_antitone hN0 hsurj hpsi_mono).intervalIntegrable

/-- The analytic inverse/majorant data constructed from the tail branch of `PhiFormula`. -/
theorem exists_phiPsiData_constructed (B : ℝ) :
    ∃ _D : PhiPsiData B, True := by
  rcases exists_nat_PhiFormula_tail B with
    ⟨N0, hN0, hTstar_pos, hcont, hstrict, hmono, hmaps, htendsto⟩
  let Tstar : ℝ := PhiFormula B (N0 : ℝ)
  have hsurj :
      Set.SurjOn (PhiFormula B) (Set.Ici (N0 : ℝ))
        (Set.Ici (PhiFormula B (N0 : ℝ))) :=
    PhiFormula_surjOn_tail hcont htendsto
  have hpsi_mono :
      MonotoneOn (psiBranch B N0) (Set.Ici (PhiFormula B (N0 : ℝ))) :=
    psiBranch_mono_tail hstrict hsurj
  refine ⟨{
    N0 := N0
    Tstar := Tstar
    Phi := PhiFormula B
    psi := psiBranch B N0
    f := fBranch B N0
    N0_ge_three := hN0
    Tstar_pos := by
      dsimp [Tstar]
      exact hTstar_pos
    Phi_eq := by
      intro x
      rfl
    Tstar_eq := by
      rfl
    Phi_strictMono_tail := hstrict
    Phi_mono_tail := hmono
    Phi_maps_tail := by
      intro x hx
      exact hmaps x hx
    Phi_tendsto_atTop := htendsto
    psi_left_inv := by
      intro t ht
      exact PhiFormula_psiBranch_eq hsurj ht
    psi_right_inv := by
      intro x hx
      exact psiBranch_right_inv hstrict hmaps hsurj hx
    psi_maps_tail := by
      intro t ht
      exact psiBranch_maps_tail hsurj ht
    psi_pos_tail := by
      intro t ht
      exact psiBranch_pos_tail hN0 hsurj ht
    psi_mono_tail := hpsi_mono
    psi_le_of_le_Phi := by
      intro t x ht hx htx
      exact psiBranch_le_of_le_Phi hstrict hsurj ht hx htx
    f_eq_tail := by
      intro t ht
      exact fBranch_eq_tail ht
    f_pos := by
      intro t _ht
      exact fBranch_pos hN0 hsurj t
    f_antitone := (fBranch_antitone hN0 hsurj hpsi_mono).antitoneOn _
    f_measurable := fBranch_measurable hN0 hsurj hpsi_mono
    f_intervalIntegrable := fBranch_intervalIntegrable hN0 hsurj hpsi_mono
  }, trivial⟩

end FloorSaving
