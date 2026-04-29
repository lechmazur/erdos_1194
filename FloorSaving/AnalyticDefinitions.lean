import FloorSaving.PhiPsiData

noncomputable section

open Classical
open Filter Topology MeasureTheory Asymptotics
open scoped Real BigOperators

namespace FloorSaving

variable {B : ℝ}

/-- `I(X) = ∫₀ˣ f`. -/
noncomputable def I (D : PhiPsiData B) (X : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..X, D.f t

/-- Split `I D X` at an intermediate point. -/
theorem I_eq_I_add_integral (D : PhiPsiData B) (a X : ℝ) :
    I D X = I D a + ∫ x in a..X, D.f x := by
  unfold I
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (D.f_intervalIntegrable 0 a) (D.f_intervalIntegrable a X)]

/-- `G_X(t) = ∫_{t-X}^t f`. -/
noncomputable def GX (D : PhiPsiData B) (X t : ℝ) : ℝ :=
  ∫ s in (t - X)..t, D.f s

/-- `G_X(t)` is nonnegative on nonnegative windows. -/
theorem GX_nonneg_of_nonneg_window
    {B : ℝ} (D : PhiPsiData B) {X t : ℝ}
    (hX : 0 ≤ X) (hlower : 0 ≤ t - X) :
    0 ≤ GX D X t := by
  have hle : t - X ≤ t := by linarith
  unfold GX
  exact intervalIntegral.integral_nonneg hle
    (fun s hs => D.f_nonneg (hlower.trans hs.1))

/-- A nonnegative shifted window of length `X` has at most the mass of `[0,X]`. -/
theorem GX_le_I_of_nonneg_window
    {B : ℝ} (D : PhiPsiData B) {X t : ℝ}
    (hX : 0 ≤ X) (hlower : 0 ≤ t - X) :
    GX D X t ≤ I D X := by
  let d : ℝ := t - X
  have hcomp :
      IntervalIntegrable (fun s : ℝ => D.f (s + d)) MeasureTheory.volume
        (0 : ℝ) X := by
    have hf : IntervalIntegrable D.f MeasureTheory.volume ((0 : ℝ) + d) (X + d) :=
      D.f_intervalIntegrable ((0 : ℝ) + d) (X + d)
    simpa using hf.comp_add_right d
  have hmono :
      ∫ s in (0 : ℝ)..X, D.f (s + d) ≤
        ∫ s in (0 : ℝ)..X, D.f s := by
    refine intervalIntegral.integral_mono_on hX hcomp
      (D.f_intervalIntegrable (0 : ℝ) X) ?_
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1
    have hd_nonneg : 0 ≤ d := by
      simpa [d] using hlower
    have hs_shift_nonneg : 0 ≤ s + d := by positivity
    have hs_le_shift : s ≤ s + d := by linarith
    exact D.f_antitone hs_nonneg hs_shift_nonneg hs_le_shift
  have hshift :
      ∫ s in (0 : ℝ)..X, D.f (s + d) = GX D X t := by
    have hleft : (0 : ℝ) + d = t - X := by
      dsimp [d]
      ring
    have hright : X + d = t := by
      dsimp [d]
      ring
    unfold GX
    rw [intervalIntegral.integral_comp_add_right]
    rw [hleft, hright]
  rw [hshift] at hmono
  simpa [I] using hmono

/-- Sliding the fixed-length `G_X` window to the right can only decrease the integral. -/
theorem GX_antitoneOn_Ici
    {B : ℝ} (D : PhiPsiData B) {X : ℝ} (hX : 0 ≤ X) :
    AntitoneOn (fun t : ℝ => GX D X t) (Set.Ici X) := by
  intro t₁ ht₁ t₂ ht₂ ht₁₂
  let d : ℝ := t₂ - t₁
  have hd_nonneg : 0 ≤ d := sub_nonneg.mpr ht₁₂
  have hle_window : t₁ - X ≤ t₁ := by linarith
  have hlower_nonneg : 0 ≤ t₁ - X := sub_nonneg.mpr ht₁
  have hcomp :
      IntervalIntegrable (fun s : ℝ => D.f (s + d)) MeasureTheory.volume
        (t₁ - X) t₁ := by
    have hf :
        IntervalIntegrable D.f MeasureTheory.volume
          ((t₁ - X) + d) (t₁ + d) :=
      D.f_intervalIntegrable ((t₁ - X) + d) (t₁ + d)
    simpa using hf.comp_add_right d
  have hmono :
      ∫ s in (t₁ - X)..t₁, D.f (s + d) ≤
        ∫ s in (t₁ - X)..t₁, D.f s := by
    refine intervalIntegral.integral_mono_on hle_window hcomp
      (D.f_intervalIntegrable (t₁ - X) t₁) ?_
    intro s hs
    have hs_nonneg : 0 ≤ s := hlower_nonneg.trans hs.1
    have hs_shift_nonneg : 0 ≤ s + d := by positivity
    have hs_le_shift : s ≤ s + d := by linarith
    exact D.f_antitone hs_nonneg hs_shift_nonneg hs_le_shift
  have hshift :
      ∫ s in (t₁ - X)..t₁, D.f (s + d) = GX D X t₂ := by
    have hleft : (t₁ - X) + d = t₂ - X := by
      dsimp [d]
      ring
    have hright : t₁ + d = t₂ := by
      dsimp [d]
      ring
    unfold GX
    rw [intervalIntegral.integral_comp_add_right]
    rw [hleft, hright]
  rw [hshift] at hmono
  simpa [GX] using hmono

/-- The primitive `I(X) = ∫₀ˣ f` is continuous. -/
theorem I_continuous {B : ℝ} (D : PhiPsiData B) :
    Continuous (fun X : ℝ => I D X) := by
  simpa [I] using
    (intervalIntegral.continuous_primitive
      (μ := MeasureTheory.volume) (f := D.f) D.f_intervalIntegrable (0 : ℝ))

/-- `G_X(t)` is the difference of two primitive values. -/
theorem GX_eq_primitive_sub {B : ℝ} (D : PhiPsiData B) (X t : ℝ) :
    GX D X t = I D t - I D (t - X) := by
  unfold GX I
  exact (intervalIntegral.integral_interval_sub_left
    (D.f_intervalIntegrable (0 : ℝ) t)
    (D.f_intervalIntegrable (0 : ℝ) (t - X))).symm

/-- For fixed `X`, `G_X(t)` is continuous in `t`. -/
theorem GX_continuous_in_t {B : ℝ} (D : PhiPsiData B) (X : ℝ) :
    Continuous (fun t : ℝ => GX D X t) := by
  have hI := I_continuous D
  have hI_shift : Continuous (fun t : ℝ => I D (t - X)) :=
    hI.comp (continuous_id.sub continuous_const)
  rw [show (fun t : ℝ => GX D X t) =
      fun t : ℝ => I D t - I D (t - X) by
    funext t
    exact GX_eq_primitive_sub D X t]
  exact hI.sub hI_shift

/-- For fixed `X`, `G_X(t)` is measurable in `t`. -/
theorem GX_measurable_in_t {B : ℝ} (D : PhiPsiData B) (X : ℝ) :
    Measurable (fun t : ℝ => GX D X t) :=
  (GX_continuous_in_t D X).measurable

/-- Continuous majorant without the integer floor. -/
noncomputable def JB (D : PhiPsiData B) (X : ℝ) : ℝ :=
  (1 / 2) * (I D X) ^ 2 +
    ∫ t in X..D.Phi X, D.f t * GX D X t

/-- Fractional part using mathlib's integer-floor fractional part.

Endpoint values are immaterial for integrals, but using `Int.fract` keeps the floor API available.
-/
noncomputable def fract (x : ℝ) : ℝ :=
  Int.fract x

@[simp]
theorem fract_eq_Int_fract (x : ℝ) :
    fract x = Int.fract x := rfl

@[simp]
theorem fract_nonneg (x : ℝ) :
    0 ≤ fract x := by
  simp [fract]

theorem fract_lt_one (x : ℝ) :
    fract x < 1 := by
  simpa [fract] using Int.fract_lt_one x

theorem fract_mem_Ico (x : ℝ) :
    fract x ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨fract_nonneg x, fract_lt_one x⟩

theorem fract_measurable :
    Measurable fract := by
  simpa [fract] using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))

@[simp]
theorem sub_fract_eq_floor (x : ℝ) :
    x - fract x = ((⌊x⌋ : ℤ) : ℝ) := by
  simp [fract]

theorem floor_eq_self_sub_fract (x : ℝ) :
    ((⌊x⌋ : ℤ) : ℝ) = x - fract x := by
  rw [sub_fract_eq_floor]

theorem floor_GX_eq_GX_sub_fract {B : ℝ} (D : PhiPsiData B) (X t : ℝ) :
    ((⌊GX D X t⌋ : ℤ) : ℝ) = GX D X t - fract (GX D X t) := by
  exact floor_eq_self_sub_fract (GX D X t)

theorem floor_GX_le_GX {B : ℝ} (D : PhiPsiData B) (X t : ℝ) :
    ((⌊GX D X t⌋ : ℤ) : ℝ) ≤ GX D X t :=
  Int.floor_le (GX D X t)

/-- The integer-floor endpoint loss is bounded by the first primitive. -/
theorem floor_GX_le_I_of_nonneg_window
    {B : ℝ} (D : PhiPsiData B) {X t : ℝ}
    (hX : 0 ≤ X) (hlower : 0 ≤ t - X) :
    ((⌊GX D X t⌋ : ℤ) : ℝ) ≤ I D X :=
  (floor_GX_le_GX D X t).trans (GX_le_I_of_nonneg_window D hX hlower)

theorem floor_GX_nonneg_of_nonneg_window
    {B : ℝ} (D : PhiPsiData B) {X t : ℝ}
    (hX : 0 ≤ X) (hlower : 0 ≤ t - X) :
    0 ≤ ((⌊GX D X t⌋ : ℤ) : ℝ) := by
  have hGX : 0 ≤ GX D X t :=
    GX_nonneg_of_nonneg_window D hX hlower
  have hfloor : (0 : ℤ) ≤ ⌊GX D X t⌋ :=
    (Int.floor_nonneg).2 hGX
  exact_mod_cast hfloor

theorem floor_GX_antitoneOn_Ici
    {B : ℝ} (D : PhiPsiData B) {X : ℝ} (hX : 0 ≤ X) :
    AntitoneOn (fun t : ℝ => ((⌊GX D X t⌋ : ℤ) : ℝ)) (Set.Ici X) := by
  intro t₁ ht₁ t₂ ht₂ ht₁₂
  have hGX : GX D X t₂ ≤ GX D X t₁ :=
    GX_antitoneOn_Ici D hX ht₁ ht₂ ht₁₂
  have hfloor : ⌊GX D X t₂⌋ ≤ ⌊GX D X t₁⌋ :=
    Int.floor_le_floor hGX
  change ((⌊GX D X t₂⌋ : ℤ) : ℝ) ≤ ((⌊GX D X t₁⌋ : ℤ) : ℝ)
  exact_mod_cast hfloor

/-- Product integrability for the continuous large-integral integrand on a nonnegative tail. -/
theorem f_mul_GX_intervalIntegrable
    {B : ℝ} (D : PhiPsiData B) {X Y : ℝ}
    (hX : 0 ≤ X) (hXY : X ≤ Y) :
    IntervalIntegrable (fun t : ℝ => D.f t * GX D X t)
      MeasureTheory.volume X Y := by
  refine AntitoneOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hXY]
  intro x hx y hy hxy
  have hx_nonneg : 0 ≤ x := hX.trans hx.1
  have hy_nonneg : 0 ≤ y := hX.trans hy.1
  have hf_anti : D.f y ≤ D.f x :=
    D.f_antitone hx_nonneg hy_nonneg hxy
  have hGX_anti : GX D X y ≤ GX D X x :=
    GX_antitoneOn_Ici D hX hx.1 hy.1 hxy
  have hGX_y_nonneg : 0 ≤ GX D X y :=
    GX_nonneg_of_nonneg_window D hX (sub_nonneg.mpr hy.1)
  have hf_x_nonneg : 0 ≤ D.f x :=
    D.f_nonneg hx_nonneg
  exact mul_le_mul hf_anti hGX_anti hGX_y_nonneg hf_x_nonneg

/-- Product integrability for the continuous floor-integral integrand on a nonnegative tail. -/
theorem f_mul_floor_GX_intervalIntegrable
    {B : ℝ} (D : PhiPsiData B) {X Y : ℝ}
    (hX : 0 ≤ X) (hXY : X ≤ Y) :
    IntervalIntegrable
      (fun t : ℝ => D.f t * ((⌊GX D X t⌋ : ℤ) : ℝ))
      MeasureTheory.volume X Y := by
  refine AntitoneOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hXY]
  intro x hx y hy hxy
  have hx_nonneg : 0 ≤ x := hX.trans hx.1
  have hy_nonneg : 0 ≤ y := hX.trans hy.1
  have hf_anti : D.f y ≤ D.f x :=
    D.f_antitone hx_nonneg hy_nonneg hxy
  have hfloor_anti :
      ((⌊GX D X y⌋ : ℤ) : ℝ) ≤ ((⌊GX D X x⌋ : ℤ) : ℝ) :=
    floor_GX_antitoneOn_Ici D hX hx.1 hy.1 hxy
  have hfloor_y_nonneg : 0 ≤ ((⌊GX D X y⌋ : ℤ) : ℝ) :=
    floor_GX_nonneg_of_nonneg_window D hX (sub_nonneg.mpr hy.1)
  have hf_x_nonneg : 0 ≤ D.f x :=
    D.f_nonneg hx_nonneg
  exact mul_le_mul hf_anti hfloor_anti hfloor_y_nonneg hf_x_nonneg

/--
Product integrability for the floor-integral integrand on any interval to the right of the
window start.
-/
theorem f_mul_floor_GX_intervalIntegrable_of_le
    {B : ℝ} (D : PhiPsiData B) {X a b : ℝ}
    (hX : 0 ≤ X) (hXa : X ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => D.f t * ((⌊GX D X t⌋ : ℤ) : ℝ))
      MeasureTheory.volume a b := by
  refine AntitoneOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  intro x hx y hy hxy
  have hx_tail : X ≤ x := hXa.trans hx.1
  have hy_tail : X ≤ y := hXa.trans hy.1
  have hx_nonneg : 0 ≤ x := hX.trans hx_tail
  have hy_nonneg : 0 ≤ y := hX.trans hy_tail
  have hf_anti : D.f y ≤ D.f x :=
    D.f_antitone hx_nonneg hy_nonneg hxy
  have hfloor_anti :
      ((⌊GX D X y⌋ : ℤ) : ℝ) ≤ ((⌊GX D X x⌋ : ℤ) : ℝ) :=
    floor_GX_antitoneOn_Ici D hX hx_tail hy_tail hxy
  have hfloor_y_nonneg : 0 ≤ ((⌊GX D X y⌋ : ℤ) : ℝ) :=
    floor_GX_nonneg_of_nonneg_window D hX (sub_nonneg.mpr hy_tail)
  have hf_x_nonneg : 0 ≤ D.f x :=
    D.f_nonneg hx_nonneg
  exact mul_le_mul hf_anti hfloor_anti hfloor_y_nonneg hf_x_nonneg

theorem floor_integrand_eq_sub {B : ℝ} (D : PhiPsiData B) (X t : ℝ) :
    D.f t * ((⌊GX D X t⌋ : ℤ) : ℝ) =
      D.f t * GX D X t - D.f t * fract (GX D X t) := by
  rw [floor_GX_eq_GX_sub_fract]
  ring

/-- The fractional part of the moving-window integral is measurable in the endpoint. -/
theorem fract_GX_measurable {B : ℝ} (D : PhiPsiData B) (X : ℝ) :
    Measurable (fun t : ℝ => fract (GX D X t)) :=
  fract_measurable.comp (GX_measurable_in_t D X)

/--
Product integrability for the fractional floor-error integrand on a nonnegative interval.

The proof uses `0 ≤ fract < 1`, so the product is dominated by the already-integrable `D.f`.
-/
theorem f_mul_fract_GX_intervalIntegrable
    {B : ℝ} (D : PhiPsiData B) {X Y : ℝ}
    (hX : 0 ≤ X) (hXY : X ≤ Y) :
    IntervalIntegrable
      (fun t : ℝ => D.f t * fract (GX D X t))
      MeasureTheory.volume X Y := by
  have hmeas :
      Measurable (fun t : ℝ => D.f t * fract (GX D X t)) :=
    D.f_measurable.mul (fract_GX_measurable D X)
  have hsm :
      AEStronglyMeasurable
        (fun t : ℝ => D.f t * fract (GX D X t))
        (MeasureTheory.volume.restrict (Set.uIoc X Y)) :=
    hmeas.aestronglyMeasurable
  refine (D.f_intervalIntegrable X Y).mono_fun' hsm ?_
  rw [Filter.EventuallyLE]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  refine ae_of_all MeasureTheory.volume ?_
  intro t ht
  rw [Set.uIoc_of_le hXY] at ht
  have ht_nonneg : 0 ≤ t := hX.trans ht.1.le
  have hf_nonneg : 0 ≤ D.f t := D.f_nonneg ht_nonneg
  have hfract_nonneg : 0 ≤ fract (GX D X t) :=
    fract_nonneg (GX D X t)
  have hfract_le_one : fract (GX D X t) ≤ 1 :=
    (fract_lt_one (GX D X t)).le
  calc
    ‖D.f t * fract (GX D X t)‖ = D.f t * fract (GX D X t) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hf_nonneg hfract_nonneg)]
    _ ≤ D.f t * 1 := mul_le_mul_of_nonneg_left hfract_le_one hf_nonneg
    _ = D.f t := by ring

/-- The floor-saving integral. -/
noncomputable def Efloor (D : PhiPsiData B) (X : ℝ) : ℝ :=
  ∫ t in X..D.Phi X, D.f t * fract (GX D X t)

/--
Algebraic form of the continuous floor contribution.

The hypotheses are only the product-integrability facts needed to use interval-integral
subtraction; later analytic files should prove these on the relevant intervals.
-/
theorem JB_sub_Efloor_sub_half_I_sq_eq_floor_integral
    {B : ℝ} (D : PhiPsiData B) (X : ℝ)
    (hGX :
      IntervalIntegrable (fun t : ℝ => D.f t * GX D X t)
        MeasureTheory.volume X (D.Phi X))
    (hfract :
      IntervalIntegrable (fun t : ℝ => D.f t * fract (GX D X t))
        MeasureTheory.volume X (D.Phi X)) :
    JB D X - Efloor D X - (1 / 2 : ℝ) * (I D X) ^ 2 =
      ∫ t in X..D.Phi X, D.f t * ((⌊GX D X t⌋ : ℤ) : ℝ) := by
  have hsub :
      ∫ t in X..D.Phi X,
          (D.f t * GX D X t - D.f t * fract (GX D X t)) =
        (∫ t in X..D.Phi X, D.f t * GX D X t) -
          ∫ t in X..D.Phi X, D.f t * fract (GX D X t) := by
    exact intervalIntegral.integral_sub hGX hfract
  have hcongr :
      ∫ t in X..D.Phi X,
          (D.f t * GX D X t - D.f t * fract (GX D X t)) =
        ∫ t in X..D.Phi X, D.f t * ((⌊GX D X t⌋ : ℤ) : ℝ) := by
    refine intervalIntegral.integral_congr ?_
    intro t _ht
    simpa using (floor_integrand_eq_sub D X t).symm
  unfold JB Efloor
  rw [← hcongr, hsub]
  ring

/--
Tail version of `JB_sub_Efloor_sub_half_I_sq_eq_floor_integral` where the two product
integrability hypotheses are discharged from the structural monotonicity/integrability facts.
-/
theorem JB_sub_Efloor_sub_half_I_sq_eq_floor_integral_of_nonneg
    {B : ℝ} (D : PhiPsiData B) {X : ℝ}
    (hX : 0 ≤ X) (hXPhi : X ≤ D.Phi X) :
    JB D X - Efloor D X - (1 / 2 : ℝ) * (I D X) ^ 2 =
      ∫ t in X..D.Phi X, D.f t * ((⌊GX D X t⌋ : ℤ) : ℝ) :=
  JB_sub_Efloor_sub_half_I_sq_eq_floor_integral D X
    (f_mul_GX_intervalIntegrable D hX hXPhi)
    (f_mul_fract_GX_intervalIntegrable D hX hXPhi)

end FloorSaving
