import FloorSaving.FAsymptotics
import FloorSaving.FloorSavingIntegral
import FloorSaving.FractionalIntegral
import FloorSaving.KernelIntegral

noncomputable section

open Classical
open Filter Topology MeasureTheory Asymptotics
open scoped Real BigOperators

namespace FloorSaving

variable {B : ℝ}

/-- Facts needed only for the final contradiction layer. -/
structure FinalAnalyticFacts (D : PhiPsiData B) : Prop where
  continuous_majorant_nat :
    (fun X : ℕ =>
      JB D (X : ℝ) -
        ((X : ℝ) +
          lam * (3 - 2 * B - 2 * Real.log (Real.log 2)) * (X : ℝ) /
            Real.log (X : ℝ)))
      =o[Filter.atTop] scaleNat
  floor_saving_nat :
    (fun X : ℕ =>
      Efloor D (X : ℝ) -
        2 * lam * (1 - Real.eulerMascheroniConstant) * (X : ℝ) /
          Real.log (X : ℝ))
      =o[Filter.atTop] scaleNat

/-- Full analytic facts produced by the later analytic files. -/
structure AnalyticFacts (D : PhiPsiData B) : Prop extends FinalAnalyticFacts D where
  f_asymptotic :
    D.f ~[Filter.atTop]
      (fun t : ℝ => Real.sqrt (2 * lam / (t * Real.log t)))
  integral_f_asymptotic :
    (fun X : ℝ => I D X) ~[Filter.atTop]
      (fun X : ℝ => 2 * Real.sqrt (2 * lam * X / Real.log X))
  continuous_majorant_real :
    (fun X : ℝ =>
      JB D X -
        (X + lam * (3 - 2 * B - 2 * Real.log (Real.log 2)) * X / Real.log X))
      =o[Filter.atTop] scaleReal
  floor_saving_real :
    (fun X : ℝ =>
      Efloor D X -
        2 * lam * (1 - Real.eulerMascheroniConstant) * X / Real.log X)
      =o[Filter.atTop] scaleReal

/-- Existence of the analytic inverse/majorant data. Proved later from the formula for `Phi`. -/
theorem exists_phiPsiData (B : ℝ) :
    ∃ _D : PhiPsiData B, True := by
  exact exists_phiPsiData_constructed B

/-- First-order asymptotic for `f`. -/
theorem f_asymptotic (D : PhiPsiData B) :
    D.f ~[Filter.atTop]
      (fun t : ℝ => Real.sqrt (2 * lam / (t * Real.log t))) := by
  exact PhiPsiData.f_asymptotic D

/-- Second-order asymptotic for the continuous majorant `J_B`. -/
theorem continuous_majorant_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      JB D X -
        (X + lam * (3 - 2 * B - 2 * Real.log (Real.log 2)) * X / Real.log X))
      =o[Filter.atTop] scaleReal := by
  have hhalf := half_square_asymptotic D
  have hlarge := large_continuous_integral_asymptotic D
  have hsum := hhalf.add hlarge
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards [] with X
  rw [JB]
  rw [← continuous_coefficient_identity B]
  ring

/-- Nat-indexed version of `continuous_majorant_asymptotic`, useful for integer `X`. -/
theorem continuous_majorant_asymptotic_nat (D : PhiPsiData B) :
    (fun X : ℕ =>
      JB D (X : ℝ) -
        ((X : ℝ) +
          lam * (3 - 2 * B - 2 * Real.log (Real.log 2)) * (X : ℝ) /
            Real.log (X : ℝ)))
      =o[Filter.atTop] scaleNat := by
  simpa [scaleReal, scaleNat] using
    (continuous_majorant_asymptotic D).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Floor-saving asymptotic. -/
theorem floor_saving_asymptotic (D : PhiPsiData B) :
    (fun X : ℝ =>
      Efloor D X -
        2 * lam * (1 - Real.eulerMascheroniConstant) * X / Real.log X)
      =o[Filter.atTop] scaleReal := by
  exact floor_saving_asymptotic_of_normalized D (floor_saving_normalized_limit D)

/-- Nat-indexed version of `floor_saving_asymptotic`, useful for integer `X`. -/
theorem floor_saving_asymptotic_nat (D : PhiPsiData B) :
    (fun X : ℕ =>
      Efloor D (X : ℝ) -
        2 * lam * (1 - Real.eulerMascheroniConstant) * (X : ℝ) /
          Real.log (X : ℝ))
      =o[Filter.atTop] scaleNat := by
  simpa [scaleReal, scaleNat] using
    (floor_saving_asymptotic D).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Final analytic facts packaged for `MainSkeleton`. -/
theorem final_analytic_facts (D : PhiPsiData B) :
    FinalAnalyticFacts D := by
  refine ⟨?_, ?_⟩
  · exact continuous_majorant_asymptotic_nat D
  · exact floor_saving_asymptotic_nat D

/-- Full analytic package, eventually proved from the analytic files. -/
theorem analytic_facts (D : PhiPsiData B) :
    AnalyticFacts D := by
  refine ⟨final_analytic_facts D, ?_, ?_, ?_, ?_⟩
  · exact f_asymptotic D
  · exact integral_f_asymptotic D
  · exact continuous_majorant_asymptotic D
  · exact floor_saving_asymptotic D

/-- The fractional-part integral used in the floor-saving term. -/
theorem integral_fract_div_sq :
    ∫ q in Set.Ioi (1 : ℝ), fract q / q ^ 2 =
      1 - Real.eulerMascheroniConstant := by
  exact integral_fract_div_sq_Ioi

end FloorSaving
