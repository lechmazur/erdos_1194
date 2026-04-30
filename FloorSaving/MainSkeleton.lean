import FloorSaving.Counting

noncomputable section

open Classical
open Filter Topology MeasureTheory Asymptotics
open scoped Real BigOperators

namespace FloorSaving

/-- Constant identity used in the final contradiction. -/
theorem coefficient_identity (B : ℝ) :
    lam * (3 - 2 * B - 2 * Real.log (Real.log 2))
      - 2 * lam * (1 - Real.eulerMascheroniConstant)
      = -2 * lam * (B - B₁) := by
  rw [B₁]
  ring

/-- Positivity of the leading constant `λ`. -/
theorem lam_pos : 0 < lam := by
  unfold lam
  positivity

/-- The natural second-order scale is eventually positive. -/
theorem eventually_scaleNat_pos :
    ∀ᶠ X : ℕ in Filter.atTop, 0 < scaleNat X := by
  have hcast : Tendsto (fun X : ℕ => (X : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hcast
  filter_upwards [hcast.eventually_gt_atTop (0 : ℝ),
      hlog.eventually_gt_atTop (0 : ℝ)] with X hX hlogX
  exact div_pos hX hlogX

/--
Final contradiction once the analytic and counting interfaces are available.

The argument uses only the two final analytic asymptotics packaged in
`FinalAnalyticFacts` and the counting upper bound `FundamentalUpperBound`.
-/
theorem contradiction_from_interfaces
    {B : ℝ} (D : PhiPsiData B)
    (hB : B₁ < B)
    (hfund : FundamentalUpperBound D)
    (hfacts : FinalAnalyticFacts D) :
    False := by
  let c : ℝ := lam * (3 - 2 * B - 2 * Real.log (Real.log 2))
  let d : ℝ := 2 * lam * (1 - Real.eulerMascheroniConstant)
  let k : ℝ := 2 * lam * (B - B₁)
  have hBdiff_pos : 0 < B - B₁ := sub_pos.mpr hB
  have hlam_pos : 0 < lam := lam_pos
  have hk_pos : 0 < k := by
    dsimp [k]
    positivity
  have hk_half_pos : 0 < k / 2 := by
    positivity
  rcases hfund with ⟨err, herr_o, hfund_event⟩
  have hcoef : c - d = -k := by
    dsimp [c, d, k]
    rw [coefficient_identity B]
    ring
  have hrem_o :
      (fun X : ℕ =>
        (JB D (X : ℝ) - ((X : ℝ) + c * scaleNat X)) -
          (Efloor D (X : ℝ) - d * scaleNat X) + err X) =o[Filter.atTop] scaleNat := by
    have hbase := (hfacts.continuous_majorant_nat.sub hfacts.floor_saving_nat).add herr_o
    simpa [c, d, scaleNat, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbase
  have hsmall_event := hrem_o.def hk_half_pos
  have hall : ∀ᶠ X : ℕ in Filter.atTop,
      (X : ℝ) ≤ JB D (X : ℝ) - Efloor D (X : ℝ) + err X ∧
      ‖(JB D (X : ℝ) - ((X : ℝ) + c * scaleNat X)) -
          (Efloor D (X : ℝ) - d * scaleNat X) + err X‖ ≤
        (k / 2) * ‖scaleNat X‖ ∧
      0 < scaleNat X := by
    filter_upwards [hfund_event, hsmall_event, eventually_scaleNat_pos] with
      X hfundX hsmallX hscaleX
    exact ⟨hfundX, hsmallX, hscaleX⟩
  rcases Filter.eventually_atTop.mp hall with ⟨N, hN⟩
  rcases hN N le_rfl with ⟨hfundN, hsmallN, hscaleN⟩
  let s : ℝ := scaleNat N
  let j : ℝ := JB D (N : ℝ)
  let e : ℝ := Efloor D (N : ℝ)
  let r : ℝ := (j - ((N : ℝ) + c * s)) - (e - d * s) + err N
  have hs_pos : 0 < s := by
    simpa [s] using hscaleN
  have hr_small : r ≤ (k / 2) * s := by
    have hr_le_abs : r ≤ ‖r‖ := by
      simpa [Real.norm_eq_abs] using le_abs_self r
    have hs_norm : ‖s‖ = s := by
      rw [Real.norm_eq_abs, abs_of_pos hs_pos]
    calc
      r ≤ ‖r‖ := hr_le_abs
      _ ≤ (k / 2) * ‖s‖ := by
        simpa [r, s, j, e] using hsmallN
      _ = (k / 2) * s := by
        rw [hs_norm]
  have hmain : k * s ≤ r := by
    have hfund_nonneg : 0 ≤ j - e + err N - (N : ℝ) :=
      sub_nonneg.mpr (by simpa [j, e] using hfundN)
    have hr_eq : r = j - e + err N - (N : ℝ) - (c - d) * s := by
      ring
    rw [hr_eq, hcoef]
    nlinarith
  nlinarith

/-- Final contradiction from the eventual upper-bound assumption. -/
theorem not_eventually_upper_bound
    (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (B : ℝ) (hB : B₁ < B) :
    ¬ EventuallyUpperBound A hA B := by
  intro hupper
  rcases exists_phiPsiData B with ⟨D, _hD⟩
  exact contradiction_from_interfaces D hB
    (fundamental_upper_bound A hA D hupper)
    (final_analytic_facts D)

/-- Main infinitely-often lower-bound theorem. -/
theorem floor_saving_lower_bound
    (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (B : ℝ) (hB : B₁ < B) :
    ∀ N : ℕ, ∃ n : PosNat,
      N ≤ n.1 ∧
      0 < denom B n.1 ∧
      (top A hA n : ℝ) > lowerBoundRHS B n.1 := by
  classical
  have hnot_upper := not_eventually_upper_bound A hA B hB
  intro N
  by_contra hno
  apply hnot_upper
  unfold EventuallyUpperBound
  rw [Filter.eventually_atTop]
  refine ⟨N, ?_⟩
  intro n hnN
  by_contra hnotAt
  unfold UpperBoundAt at hnotAt
  push Not at hnotAt
  rcases hnotAt with ⟨hnpos, hden, hgt⟩
  exact hno ⟨⟨n, hnpos⟩, hnN, hden, hgt⟩

end FloorSaving
