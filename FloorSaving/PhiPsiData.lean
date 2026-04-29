import FloorSaving.Basic

noncomputable section

open Classical
open Filter Topology MeasureTheory Asymptotics
open scoped Real BigOperators

namespace FloorSaving

/-- `H(w) = w - log w + B`. -/
def H (B w : ℝ) : ℝ :=
  w - Real.log w + B

/-- The formula for `Φ`. Tail/domain hypotheses are carried separately. -/
noncomputable def PhiFormula (B x : ℝ) : ℝ :=
  lam * x ^ 2 / H B (Real.log x)

/-- The formula `H B (log n)` matches the final denominator. -/
theorem H_log_nat_eq_denom (B : ℝ) (n : ℕ) :
    H B (Real.log (n : ℝ)) = denom B n := by
  rw [H, denom]

/-- The formula for `Φ(n)` matches the final right-hand side. -/
theorem PhiFormula_nat_eq_lowerBoundRHS (B : ℝ) (n : ℕ) :
    PhiFormula B (n : ℝ) = lowerBoundRHS B n := by
  rw [PhiFormula, lowerBoundRHS, H_log_nat_eq_denom]

/-- Positivity of the final denominator on a natural-number tail. -/
theorem eventually_denom_pos (B : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < denom B n := by
  have hlog_nat :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop := by
    exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall :
      (fun n : ℕ => Real.log (Real.log (n : ℝ))) =o[Filter.atTop]
        (fun n : ℕ => Real.log (n : ℝ)) := by
    simpa only [Function.comp_apply, id_eq] using
      (Real.isLittleO_log_id_atTop.comp_tendsto hlog_nat)
  filter_upwards [hsmall.def (by norm_num : (0 : ℝ) < 1 / 2),
      hlog_nat.eventually_ge_atTop (0 : ℝ),
      hlog_nat.eventually_gt_atTop (-2 * B)] with n hsmalln hlog_nonneg hlog_gt
  have hloglog_le :
      Real.log (Real.log (n : ℝ)) ≤ (1 / 2 : ℝ) * Real.log (n : ℝ) := by
    calc
      Real.log (Real.log (n : ℝ)) ≤ ‖Real.log (Real.log (n : ℝ))‖ := by
        simpa [Real.norm_eq_abs] using le_abs_self (Real.log (Real.log (n : ℝ)))
      _ ≤ (1 / 2 : ℝ) * ‖Real.log (n : ℝ)‖ := hsmalln
      _ = (1 / 2 : ℝ) * Real.log (n : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hlog_nonneg]
  rw [denom]
  nlinarith

/--
Analytic data used by the combinatorial contradiction.

This is an interface. The first formalization pass should prove the contradiction assuming such
objects and their properties. Later work constructs this structure from `PhiFormula` on a tail.
-/
structure PhiPsiData (B : ℝ) where
  /-- Integer lower tail threshold. The TeX proof eventually takes this at least `3`. -/
  N0 : ℕ
  /-- Lower endpoint of the real range of `Phi` on the selected tail. -/
  Tstar : ℝ
  /-- Tail function `Phi`, extension outside the tail irrelevant. -/
  Phi : ℝ → ℝ
  /-- Inverse branch of `Phi` on `[Tstar,∞)`, extension outside the branch irrelevant. -/
  psi : ℝ → ℝ
  /-- Positive nonincreasing majorant function, equal to `1/psi` on the branch. -/
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
  /-- Order-transport lemma for the inverse branch. Useful in the spacing proof. -/
  psi_le_of_le_Phi :
    ∀ {t x : ℝ}, Tstar ≤ t → (N0 : ℝ) ≤ x → t ≤ Phi x → psi t ≤ x

  f_eq_tail : ∀ t : ℝ, Tstar ≤ t → f t = 1 / psi t
  f_pos : ∀ t : ℝ, 0 ≤ t → 0 < f t
  f_antitone : AntitoneOn f (Set.Ici (0 : ℝ))
  f_measurable : Measurable f
  f_intervalIntegrable : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b

namespace PhiPsiData

variable {B : ℝ} (D : PhiPsiData B)

/-- Convenience consequence of `N0_ge_three`. -/
theorem N0_pos : 0 < D.N0 := by
  exact Nat.lt_of_lt_of_le (by norm_num : 0 < 3) D.N0_ge_three

/-- Convenience nonnegativity of `f` on `[0,∞)`. -/
theorem f_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ D.f t := by
  exact le_of_lt (D.f_pos t ht)

/-- Eventually, the real variable lies in the inverse branch range. -/
theorem eventually_Tstar_le :
    ∀ᶠ t : ℝ in Filter.atTop, D.Tstar ≤ t :=
  eventually_ge_atTop D.Tstar

/-- The tail formula for `f` is available eventually. -/
theorem f_eq_tail_eventually :
    D.f =ᶠ[Filter.atTop] fun t : ℝ => 1 / D.psi t := by
  filter_upwards [D.eventually_Tstar_le] with t ht
  exact D.f_eq_tail t ht

/-- The inverse branch is eventually positive. -/
theorem psi_pos_eventually :
    ∀ᶠ t : ℝ in Filter.atTop, 0 < D.psi t := by
  filter_upwards [D.eventually_Tstar_le] with t ht
  exact D.psi_pos_tail t ht

/-- Eventually, `psi` lands in the selected tail. -/
theorem eventually_N0_le_psi :
    ∀ᶠ t : ℝ in Filter.atTop, (D.N0 : ℝ) ≤ D.psi t := by
  filter_upwards [D.eventually_Tstar_le] with t ht
  exact D.psi_maps_tail t ht

/-- The left inverse identity is available eventually. -/
theorem Phi_psi_eq_eventually :
    (fun t : ℝ => D.Phi (D.psi t)) =ᶠ[Filter.atTop] fun t : ℝ => t := by
  filter_upwards [D.eventually_Tstar_le] with t ht
  exact D.psi_left_inv t ht

/-- The eventual inverse identity with `Phi` unfolded to its explicit formula. -/
theorem PhiFormula_psi_eq_eventually :
    (fun t : ℝ => PhiFormula B (D.psi t)) =ᶠ[Filter.atTop] fun t : ℝ => t := by
  filter_upwards [D.Phi_psi_eq_eventually] with t ht
  simpa [D.Phi_eq (D.psi t)] using ht

/-- The inverse branch tends to infinity. -/
theorem psi_tendsto_atTop :
    Tendsto D.psi Filter.atTop Filter.atTop := by
  rw [tendsto_atTop_atTop]
  intro R
  let X : ℝ := max R (D.N0 : ℝ)
  have hX_tail : (D.N0 : ℝ) ≤ X := by
    dsimp [X]
    exact le_max_right R (D.N0 : ℝ)
  refine ⟨max D.Tstar (D.Phi X), ?_⟩
  intro t ht
  have hTstar_t : D.Tstar ≤ t := le_trans (le_max_left _ _) ht
  have hPhi_t : D.Phi X ≤ t := le_trans (le_max_right _ _) ht
  have hTstar_phi : D.Tstar ≤ D.Phi X := D.Phi_maps_tail X hX_tail
  have hpsi_mono : D.psi (D.Phi X) ≤ D.psi t :=
    D.psi_mono_tail hTstar_phi hTstar_t hPhi_t
  calc
    R ≤ X := by
      dsimp [X]
      exact le_max_left R (D.N0 : ℝ)
    _ = D.psi (D.Phi X) := (D.psi_right_inv X hX_tail).symm
    _ ≤ D.psi t := hpsi_mono

/-- The reciprocal of the inverse branch tends to zero. -/
theorem inv_psi_tendsto_zero :
    Tendsto (fun t : ℝ => 1 / D.psi t) Filter.atTop (𝓝 0) := by
  simpa [one_div] using tendsto_inv_atTop_zero.comp D.psi_tendsto_atTop

/-- The majorant itself tends to zero. -/
theorem f_tendsto_zero :
    Tendsto D.f Filter.atTop (𝓝 0) :=
  D.inv_psi_tendsto_zero.congr' D.f_eq_tail_eventually.symm

end PhiPsiData

end FloorSaving
