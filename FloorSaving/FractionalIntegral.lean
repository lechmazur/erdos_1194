import FloorSaving.AnalyticDefinitions
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

noncomputable section

open Filter MeasureTheory Real Set
open scoped BigOperators

namespace FloorSaving

/-- On the unit interval `[n,n+1)`, the project fractional part is `x - n`. -/
theorem fract_eq_sub_nat_on_Ico (n : ℕ) :
    ∀ x ∈ Set.Ico ((n : ℝ)) (n + 1), fract x = x - n := by
  intro x hx
  have hfloor : (⌊x⌋ : ℤ) = (n : ℤ) :=
    Int.floor_eq_on_Ico (R := ℝ) (n : ℤ) x (by simpa using hx)
  rw [fract, Int.fract, hfloor]
  norm_num

/--
On each positive unit interval, the fractional-part integral is exactly the corresponding
`ZetaAsymptotics.term` at `s = 1`.

The endpoint mismatch at `n + 1` is handled by `intervalIntegral.integral_congr_ae`.
-/
theorem integral_fract_div_sq_unit_eq_zeta_term {n : ℕ} (hn : 0 < n) :
    ∫ q in (n : ℝ)..(n + 1), fract q / q ^ 2 =
      ZetaAsymptotics.term n 1 := by
  rw [ZetaAsymptotics.term]
  refine intervalIntegral.integral_congr_ae ?_
  have hne_right : ∀ᵐ q : ℝ, q ≠ (n : ℝ) + 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne_right] with q hq_ne hq
  have hle_interval : (n : ℝ) ≤ (n : ℝ) + 1 := by
    have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hqIco : q ∈ Set.Ico (n : ℝ) (n + 1) := by
    have hqIoc : q ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1) := by
      simpa [uIoc_of_le hle_interval] using hq
    exact ⟨hqIoc.1.le, lt_of_le_of_ne hqIoc.2 hq_ne⟩
  have hfract : fract q = q - n :=
    fract_eq_sub_nat_on_Ico n q hqIco
  have hpow : q ^ (1 + 1 : ℝ) = q ^ 2 := by
    norm_num
  rw [hfract, hpow]

/-- The unit-interval pieces for `fract q / q^2` sum to `1 - γ`. -/
theorem hasSum_integral_fract_div_sq_units :
    HasSum
      (fun n : ℕ =>
        ∫ q in ((n + 1 : ℕ) : ℝ)..(((n + 1 : ℕ) : ℝ) + 1), fract q / q ^ 2)
      (1 - Real.eulerMascheroniConstant) := by
  refine ZetaAsymptotics.term_tsum_one.congr_fun fun n => ?_
  simpa using integral_fract_div_sq_unit_eq_zeta_term (n := n + 1) (by positivity)

/-- The integrand `fract q / q^2` is integrable on `(1,∞)`. -/
theorem integrableOn_fract_div_sq_Ioi_one :
    IntegrableOn (fun q : ℝ => fract q / q ^ 2) (Set.Ioi (1 : ℝ)) := by
  have hg : IntegrableOn (fun q : ℝ => q ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt (a := -2) (c := (1 : ℝ)) (by norm_num) zero_lt_one
  rw [IntegrableOn] at hg ⊢
  refine Integrable.mono' hg ?_ ?_
  · exact (fract_measurable.div (measurable_id.pow_const (2 : ℕ))).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    have hqpos : 0 < q := lt_trans zero_lt_one hq
    have hqnonneg : 0 ≤ q := hqpos.le
    have hq2pos : 0 < q ^ 2 := sq_pos_of_pos hqpos
    have hfract_nonneg : 0 ≤ fract q := fract_nonneg q
    have hfract_le_one : fract q ≤ 1 := (fract_lt_one q).le
    have hnonneg : 0 ≤ fract q / q ^ 2 := div_nonneg hfract_nonneg hq2pos.le
    rw [Real.norm_of_nonneg hnonneg]
    have hdiv : fract q / q ^ 2 ≤ 1 / q ^ 2 := by
      exact div_le_div_of_nonneg_right hfract_le_one hq2pos.le
    have hrpow : q ^ (-2 : ℝ) = 1 / q ^ 2 := by
      rw [Real.rpow_neg hqnonneg]
      norm_num
    rwa [hrpow]

/-- The intervals `(n+1,n+2]`, indexed by `n : ℕ`, cover `(1,∞)`. -/
theorem iUnion_Ioc_nat_units_above_one :
    (⋃ n : ℕ, Set.Ioc (((n + 1 : ℕ) : ℝ)) ((((n + 1 : ℕ) : ℝ) + 1))) =
      Set.Ioi (1 : ℝ) := by
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
    (iUnion_Ioc_map_succ_eq_Ioi
      (α := ℕ) (β := ℝ) (f := fun n : ℕ => (n : ℝ) + 1)
      (by intro n; norm_num)
      (by
        rw [not_bddAbove_iff]
        intro a
        rcases exists_nat_gt (a - 1) with ⟨n, hn⟩
        refine ⟨(n : ℝ) + 1, ?_, ?_⟩
        · exact ⟨n, rfl⟩
        · linarith))

/-- The intervals `(n+1,n+2]`, indexed by `n : ℕ`, are pairwise disjoint. -/
theorem pairwise_disjoint_Ioc_nat_units_above_one :
    Pairwise (Function.onFun Disjoint
      (fun n : ℕ => Set.Ioc (((n + 1 : ℕ) : ℝ)) ((((n + 1 : ℕ) : ℝ) + 1)))) := by
  intro m n hmn
  unfold Function.onFun
  rw [Set.Ioc_disjoint_Ioc]
  by_cases hlt : m < n
  · have hle : ((m + 1 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) := by
      have hleNat : m + 2 ≤ n + 1 := Nat.succ_le_succ (Nat.succ_le_of_lt hlt)
      exact_mod_cast hleNat
    exact le_trans (min_le_left _ _) (le_trans hle (le_max_right _ _))
  · have hgt : n < m := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) hmn.symm
    have hle : ((n + 1 : ℕ) : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by
      have hleNat : n + 2 ≤ m + 1 := Nat.succ_le_succ (Nat.succ_le_of_lt hgt)
      exact_mod_cast hleNat
    exact le_trans (min_le_right _ _) (le_trans hle (le_max_left _ _))

/-- Euler's constant identity for the fractional-part integral on `(1,∞)`. -/
theorem integral_fract_div_sq_Ioi :
    ∫ q in Set.Ioi (1 : ℝ), fract q / q ^ 2 =
      1 - Real.eulerMascheroniConstant := by
  let s : ℕ → Set ℝ := fun n =>
    Set.Ioc (((n + 1 : ℕ) : ℝ)) ((((n + 1 : ℕ) : ℝ) + 1))
  have hs_union : (⋃ n : ℕ, s n) = Set.Ioi (1 : ℝ) := by
    simpa [s] using iUnion_Ioc_nat_units_above_one
  have hInt_union : IntegrableOn (fun q : ℝ => fract q / q ^ 2) (⋃ n : ℕ, s n) := by
    rw [hs_union]
    exact integrableOn_fract_div_sq_Ioi_one
  have hsum_set : HasSum (fun n : ℕ => ∫ q in s n, fract q / q ^ 2)
      (∫ q in ⋃ n : ℕ, s n, fract q / q ^ 2) := by
    exact hasSum_integral_iUnion (μ := volume)
      (f := fun q : ℝ => fract q / q ^ 2)
      (s := s)
      (fun _ => measurableSet_Ioc)
      (by simpa [s] using pairwise_disjoint_Ioc_nat_units_above_one)
      hInt_union
  have hsum_units_set : HasSum (fun n : ℕ => ∫ q in s n, fract q / q ^ 2)
      (1 - Real.eulerMascheroniConstant) := by
    refine hasSum_integral_fract_div_sq_units.congr_fun fun n => ?_
    have hle : (((n + 1 : ℕ) : ℝ)) ≤ ((((n + 1 : ℕ) : ℝ) + 1)) := by linarith
    rw [intervalIntegral.integral_of_le hle]
  have h_eq_union : ∫ q in ⋃ n : ℕ, s n, fract q / q ^ 2 =
      1 - Real.eulerMascheroniConstant := hsum_set.unique hsum_units_set
  rwa [hs_union] at h_eq_union

end FloorSaving
