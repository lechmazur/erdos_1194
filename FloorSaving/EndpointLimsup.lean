import FloorSaving.MainSkeleton

noncomputable section

open Classical
open Filter Topology MeasureTheory Asymptotics
open scoped Real BigOperators

namespace FloorSaving

/-- The normalized endpoint sequence, totalized at `0` for a natural-number limsup. -/
noncomputable def endpointSeq (A : Set ℕ) (hA : UniquePositiveDiffs A) (n : ℕ) : ℝ :=
  if hn : 0 < n then
    (top A hA ⟨n, hn⟩ : ℝ) * denom B₁ n / (n : ℝ) ^ 2
  else 0

/-- The final denominator at `B₁` is asymptotic to the denominator at any fixed `B`. -/
theorem denom_ratio_tendsto_one (B : ℝ) :
    Tendsto (fun n : ℕ => denom B₁ n / denom B n) Filter.atTop (𝓝 (1 : ℝ)) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlog_pos : ∀ᶠ n : ℕ in Filter.atTop, 0 < Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp hnat).eventually_gt_atTop (0 : ℝ)
  have hB₁ : Tendsto (fun n : ℕ => denom B₁ n / Real.log (n : ℝ))
      Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa [denom, H_log_nat_eq_denom] using
      (H_log_div_log_tendsto_one B₁).comp hnat
  have hB : Tendsto (fun n : ℕ => denom B n / Real.log (n : ℝ))
      Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa [denom, H_log_nat_eq_denom] using
      (H_log_div_log_tendsto_one B).comp hnat
  have hdiv : Tendsto (fun n : ℕ =>
      (denom B₁ n / Real.log (n : ℝ)) /
        (denom B n / Real.log (n : ℝ))) Filter.atTop (𝓝 (1 / 1 : ℝ)) :=
    hB₁.div hB (by norm_num)
  have hcongr : (fun n : ℕ =>
      (denom B₁ n / Real.log (n : ℝ)) /
        (denom B n / Real.log (n : ℝ))) =ᶠ[Filter.atTop]
      (fun n : ℕ => denom B₁ n / denom B n) := by
    filter_upwards [hlog_pos] with n hlog
    field_simp [hlog.ne']
  simpa using hdiv.congr' hcongr

/-- The endpoint sequence is frequently above every constant strictly below `lam`. -/
theorem endpoint_frequently_lower_bound
    (A : Set ℕ) (hA : UniquePositiveDiffs A) {c : ℝ} (hc : c < lam) :
    ∃ᶠ n : ℕ in Filter.atTop, c < endpointSeq A hA n := by
  let B : ℝ := B₁ + 1
  have hBgt : B₁ < B := by
    dsimp [B]
    linarith
  have hratio_tendsto : Tendsto (fun n : ℕ => lam * (denom B₁ n / denom B n))
      Filter.atTop (𝓝 (lam * 1)) :=
    (denom_ratio_tendsto_one B).const_mul lam
  have hratio_event : ∀ᶠ n : ℕ in Filter.atTop,
      c < lam * (denom B₁ n / denom B n) := by
    exact hratio_tendsto.eventually (eventually_gt_nhds (by simpa using hc))
  have hall_event : ∀ᶠ n : ℕ in Filter.atTop,
      c < lam * (denom B₁ n / denom B n) ∧ 0 < denom B₁ n := by
    exact hratio_event.and (eventually_denom_pos B₁)
  rw [Filter.frequently_atTop]
  intro N
  rcases Filter.eventually_atTop.mp hall_event with ⟨N₀, hN₀⟩
  rcases floor_saving_lower_bound A hA B hBgt (max N N₀) with
    ⟨n, hn_ge, hdenB_pos, htop_gt⟩
  have hn_ge_N : N ≤ n.1 := le_trans (le_max_left N N₀) hn_ge
  have hn_ge_N₀ : N₀ ≤ n.1 := le_trans (le_max_right N N₀) hn_ge
  rcases hN₀ n.1 hn_ge_N₀ with ⟨hratio_gt, hdenB₁_pos⟩
  refine ⟨n.1, hn_ge_N, ?_⟩
  have hn_pos_real : 0 < (n.1 : ℝ) := Nat.cast_pos.mpr n.2
  have hn_sq_pos : 0 < (n.1 : ℝ) ^ 2 := sq_pos_of_pos hn_pos_real
  have hscale_pos : 0 < denom B₁ n.1 / (n.1 : ℝ) ^ 2 :=
    div_pos hdenB₁_pos hn_sq_pos
  have hscaled_gt :
      lowerBoundRHS B n.1 * (denom B₁ n.1 / (n.1 : ℝ) ^ 2) <
        (top A hA n : ℝ) * (denom B₁ n.1 / (n.1 : ℝ) ^ 2) :=
    mul_lt_mul_of_pos_right htop_gt hscale_pos
  have hratio_eq :
      lam * (denom B₁ n.1 / denom B n.1) =
        lowerBoundRHS B n.1 * (denom B₁ n.1 / (n.1 : ℝ) ^ 2) := by
    rw [lowerBoundRHS]
    field_simp [hdenB_pos.ne', hn_sq_pos.ne']
  calc
    c < lam * (denom B₁ n.1 / denom B n.1) := hratio_gt
    _ = lowerBoundRHS B n.1 * (denom B₁ n.1 / (n.1 : ℝ) ^ 2) := hratio_eq
    _ < (top A hA n : ℝ) * (denom B₁ n.1 / (n.1 : ℝ) ^ 2) := hscaled_gt
    _ = endpointSeq A hA n.1 := by
      simp [endpointSeq, n.2]
      ring

/-- Endpoint limsup consequence of the floor-saving lower bound. -/
theorem endpoint_limsup
    (A : Set ℕ) (hA : UniquePositiveDiffs A) :
    (lam : EReal) ≤ Filter.limsup
      (fun n : ℕ => (endpointSeq A hA n : EReal)) Filter.atTop := by
  rw [Filter.le_limsup_iff']
  intro y hy
  by_cases hybot : y = ⊥
  · exact Filter.Frequently.of_forall (f := Filter.atTop) fun _ => by simp [hybot]
  · have hytop : y ≠ ⊤ := ne_top_of_lt hy
    lift y to ℝ using ⟨hytop, hybot⟩
    have hyr : y < lam := by exact_mod_cast hy
    exact (endpoint_frequently_lower_bound A hA hyr).mono fun _ hn =>
      EReal.coe_le_coe_iff.mpr (le_of_lt hn)

end FloorSaving
