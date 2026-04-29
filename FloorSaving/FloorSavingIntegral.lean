import FloorSaving.ContinuousMajorant
import FloorSaving.FractionalIntegral

noncomputable section

open Classical
open Filter Topology MeasureTheory Asymptotics
open scoped Real BigOperators

namespace FloorSaving

variable {B : ℝ}

/-- Fixed-`X` change-of-variables coordinate `q = X / psi(t)`. -/
noncomputable def qOf (D : PhiPsiData B) (X t : ℝ) : ℝ :=
  X / D.psi t

/-- Main fixed-`Q` part of the floor-error integral. -/
noncomputable def EfloorMain (D : PhiPsiData B) (Q X : ℝ) : ℝ :=
  ∫ t in D.Phi (X / Q)..D.Phi X, D.f t * fract (GX D X t)

/-- Initial fixed-`Q` tail part of the floor-error integral. -/
noncomputable def EfloorTail (D : PhiPsiData B) (Q X : ℝ) : ℝ :=
  ∫ t in X..D.Phi (X / Q), D.f t * fract (GX D X t)

/-- Truncated fractional-part model integral. -/
noncomputable def IfractQ (Q : ℝ) : ℝ :=
  ∫ q in (1 : ℝ)..Q, fract q / q ^ 2

/-- Infinite fractional-part model integral. -/
noncomputable def IfractInf : ℝ :=
  ∫ q in Set.Ioi (1 : ℝ), fract q / q ^ 2

/-- Integer indices whose neighborhoods can affect fractional-part stability on `[1,Q]`. -/
def integerWindowIndex (Q : ℝ) : Finset ℤ :=
  Finset.Icc (1 : ℤ) ⌈Q⌉

/-- Open `η`-neighborhood of an integer. -/
def integerWindow (η : ℝ) (m : ℤ) : Set ℝ :=
  Set.Ioo ((m : ℝ) - η) ((m : ℝ) + η)

/-- Union of the finitely many integer neighborhoods relevant to `[1,Q]`. -/
def integerWindowUnion (Q η : ℝ) : Set ℝ :=
  ⋃ m : ℤ, if m ∈ integerWindowIndex Q then integerWindow η m else ∅

/-- Bad set where a point of `[1,Q]` lies too close to an integer discontinuity. -/
def intBadSet (Q η : ℝ) : Set ℝ :=
  Set.Icc (1 : ℝ) Q ∩ integerWindowUnion Q η

/-- Good set where a point of `[1,Q]` stays away from all relevant integer discontinuities. -/
def intGoodSet (Q η : ℝ) : Set ℝ :=
  Set.Icc (1 : ℝ) Q \ integerWindowUnion Q η

@[simp] theorem mem_integerWindow {η : ℝ} {m : ℤ} {q : ℝ} :
    q ∈ integerWindow η m ↔ (m : ℝ) - η < q ∧ q < (m : ℝ) + η := by
  rfl

@[simp] theorem mem_integerWindowUnion {Q η q : ℝ} :
    q ∈ integerWindowUnion Q η ↔
      ∃ m ∈ integerWindowIndex Q, q ∈ integerWindow η m := by
  unfold integerWindowUnion
  constructor
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨m, hm⟩
    by_cases hmem : m ∈ integerWindowIndex Q
    · exact ⟨m, hmem, by simpa [hmem] using hm⟩
    · simp [hmem] at hm
  · rintro ⟨m, hm, hwin⟩
    exact Set.mem_iUnion.mpr ⟨m, by simpa [hm] using hwin⟩

/-- Integer windows are measurable. -/
theorem measurableSet_integerWindow {η : ℝ} {m : ℤ} :
    MeasurableSet (integerWindow η m) := by
  unfold integerWindow
  exact measurableSet_Ioo

/-- The finite union of integer windows is measurable. -/
theorem measurableSet_integerWindowUnion {Q η : ℝ} :
    MeasurableSet (integerWindowUnion Q η) := by
  unfold integerWindowUnion
  refine MeasurableSet.iUnion fun m : ℤ => ?_
  by_cases hm : m ∈ integerWindowIndex Q
  · simpa [hm] using (measurableSet_integerWindow (η := η) (m := m))
  · simp [hm]

/-- The integer-neighborhood bad set is measurable. -/
theorem measurableSet_intBadSet {Q η : ℝ} :
    MeasurableSet (intBadSet Q η) := by
  unfold intBadSet
  exact (measurableSet_Icc : MeasurableSet (Set.Icc (1 : ℝ) Q)).inter
    measurableSet_integerWindowUnion

/-- The complement good set is measurable. -/
theorem measurableSet_intGoodSet {Q η : ℝ} :
    MeasurableSet (intGoodSet Q η) := by
  unfold intGoodSet
  exact (measurableSet_Icc : MeasurableSet (Set.Icc (1 : ℝ) Q)).diff
    measurableSet_integerWindowUnion

@[simp] theorem mem_intBadSet {Q η q : ℝ} :
    q ∈ intBadSet Q η ↔
      q ∈ Set.Icc (1 : ℝ) Q ∧ ∃ m ∈ integerWindowIndex Q, q ∈ integerWindow η m := by
  simp [intBadSet]

@[simp] theorem mem_intGoodSet {Q η q : ℝ} :
    q ∈ intGoodSet Q η ↔
      q ∈ Set.Icc (1 : ℝ) Q ∧ ∀ m ∈ integerWindowIndex Q, q ∉ integerWindow η m := by
  simp [intGoodSet]

/-- The lower floor of a good point belongs to the finite integer-window index set. -/
theorem floor_mem_integerWindowIndex_of_mem_intGoodSet {Q η q : ℝ}
    (hq : q ∈ intGoodSet Q η) :
    ⌊q⌋ ∈ integerWindowIndex Q := by
  have hq' := (mem_intGoodSet (Q := Q) (η := η) (q := q)).mp hq
  rw [integerWindowIndex, Finset.mem_Icc]
  constructor
  · exact (Int.le_floor (z := 1) (a := q)).2 (by exact_mod_cast hq'.1.1)
  · exact (Int.floor_le_floor hq'.1.2).trans (Int.floor_le_ceil Q)

/-- The upper ceiling of a good point belongs to the finite integer-window index set. -/
theorem ceil_mem_integerWindowIndex_of_mem_intGoodSet {Q η q : ℝ}
    (hq : q ∈ intGoodSet Q η) :
    ⌈q⌉ ∈ integerWindowIndex Q := by
  have hq' := (mem_intGoodSet (Q := Q) (η := η) (q := q)).mp hq
  rw [integerWindowIndex, Finset.mem_Icc]
  constructor
  · have hone_le_q : ((1 : ℤ) : ℝ) ≤ q := by exact_mod_cast hq'.1.1
    have hreal : ((1 : ℤ) : ℝ) ≤ ((⌈q⌉ : ℤ) : ℝ) :=
      hone_le_q.trans (Int.le_ceil q)
    exact Int.cast_le.mp hreal
  · exact Int.ceil_mono hq'.1.2

/-- Off the integer-neighborhood bad set, an `η`-small perturbation does not change the floor. -/
theorem floor_eq_of_mem_intGoodSet_of_abs_sub_lt {Q η q y : ℝ}
    (hη : 0 < η) (hq : q ∈ intGoodSet Q η) (hy : |y - q| < η) :
    ⌊y⌋ = ⌊q⌋ := by
  have hq' := (mem_intGoodSet (Q := Q) (η := η) (q := q)).mp hq
  have hfloor_mem := floor_mem_integerWindowIndex_of_mem_intGoodSet (Q := Q) (η := η) hq
  have hceil_mem := ceil_mem_integerWindowIndex_of_mem_intGoodSet (Q := Q) (η := η) hq
  have hnot_floor : q ∉ integerWindow η ⌊q⌋ := hq'.2 ⌊q⌋ hfloor_mem
  have hnot_ceil : q ∉ integerWindow η ⌈q⌉ := hq'.2 ⌈q⌉ hceil_mem
  have hfloor_left : ((⌊q⌋ : ℤ) : ℝ) - η < q :=
    (sub_lt_self ((⌊q⌋ : ℤ) : ℝ) hη).trans_le (Int.floor_le q)
  have hfloor_eta_le : ((⌊q⌋ : ℤ) : ℝ) + η ≤ q := by
    by_contra hcontra
    exact hnot_floor ⟨hfloor_left, lt_of_not_ge hcontra⟩
  have hceil_right : q < ((⌈q⌉ : ℤ) : ℝ) + η :=
    (Int.le_ceil q).trans_lt (lt_add_of_pos_right _ hη)
  have hq_le_ceil_sub : q ≤ ((⌈q⌉ : ℤ) : ℝ) - η := by
    by_contra hcontra
    exact hnot_ceil ⟨lt_of_not_ge hcontra, hceil_right⟩
  have hy_bounds := abs_sub_lt_iff.mp hy
  have hy_lower : ((⌊q⌋ : ℤ) : ℝ) ≤ y := by linarith
  have hy_upper_ceil : y < ((⌈q⌉ : ℤ) : ℝ) := by linarith
  have hceil_le_floor_add_one : ((⌈q⌉ : ℤ) : ℝ) ≤ ((⌊q⌋ : ℤ) : ℝ) + 1 := by
    exact_mod_cast Int.ceil_le_floor_add_one q
  have hy_upper : y < ((⌊q⌋ : ℤ) : ℝ) + 1 :=
    hy_upper_ceil.trans_le hceil_le_floor_add_one
  exact Int.floor_eq_iff.mpr ⟨hy_lower, hy_upper⟩

/-- Off the integer-neighborhood bad set, fractional parts vary by the underlying perturbation. -/
theorem fract_sub_fract_eq_of_mem_intGoodSet_of_abs_sub_lt {Q η q y : ℝ}
    (hη : 0 < η) (hq : q ∈ intGoodSet Q η) (hy : |y - q| < η) :
    fract y - fract q = y - q := by
  have hfloor := floor_eq_of_mem_intGoodSet_of_abs_sub_lt (Q := Q) (η := η) hη hq hy
  unfold fract Int.fract
  rw [hfloor]
  ring

/-- Absolute-value form of fractional-part stability off the bad set. -/
theorem abs_fract_sub_fract_eq_of_mem_intGoodSet_of_abs_sub_lt {Q η q y : ℝ}
    (hη : 0 < η) (hq : q ∈ intGoodSet Q η) (hy : |y - q| < η) :
    |fract y - fract q| = |y - q| := by
  rw [fract_sub_fract_eq_of_mem_intGoodSet_of_abs_sub_lt (Q := Q) (η := η) hη hq hy]

/-- The integer-neighborhood good and bad sets partition `[1,Q]`. -/
theorem intGoodSet_union_intBadSet (Q η : ℝ) :
    intGoodSet Q η ∪ intBadSet Q η = Set.Icc (1 : ℝ) Q := by
  ext q
  simp [intGoodSet, intBadSet]

/-- The integer-neighborhood good and bad sets are disjoint. -/
theorem disjoint_intGoodSet_intBadSet (Q η : ℝ) :
    Disjoint (intGoodSet Q η) (intBadSet Q η) := by
  rw [Set.disjoint_left]
  intro q hgood hbad
  rw [mem_intGoodSet] at hgood
  rw [mem_intBadSet] at hbad
  rcases hbad with ⟨_, m, hm, hwin⟩
  exact hgood.2 m hm hwin

/-- The bad set has measure at most the total length of the integer windows. -/
theorem volume_intBadSet_toReal_le {Q η : ℝ} (hη : 0 ≤ η) :
    (MeasureTheory.volume (intBadSet Q η)).toReal ≤
      ((integerWindowIndex Q).card : ℝ) * (2 * η) := by
  have hsubset : intBadSet Q η ⊆ ⋃ m ∈ integerWindowIndex Q, integerWindow η m := by
    intro q hq
    rcases (mem_intBadSet (Q := Q) (η := η) (q := q)).mp hq with ⟨_, m, hm, hwin⟩
    exact Set.mem_iUnion₂.mpr ⟨m, hm, hwin⟩
  have hmeasure_le :
      MeasureTheory.volume (intBadSet Q η) ≤
        MeasureTheory.volume (⋃ m ∈ integerWindowIndex Q, integerWindow η m) :=
    MeasureTheory.measure_mono hsubset
  have hUnion_le :
      MeasureTheory.volume (⋃ m ∈ integerWindowIndex Q, integerWindow η m) ≤
        ∑ m ∈ integerWindowIndex Q, MeasureTheory.volume (integerWindow η m) :=
    MeasureTheory.measure_biUnion_finset_le (μ := MeasureTheory.volume)
      (integerWindowIndex Q) (fun m => integerWindow η m)
  have hsum_ne_top :
      (∑ m ∈ integerWindowIndex Q, MeasureTheory.volume (integerWindow η m)) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro m hm
    rw [integerWindow, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  calc
    (MeasureTheory.volume (intBadSet Q η)).toReal ≤
        (∑ m ∈ integerWindowIndex Q, MeasureTheory.volume (integerWindow η m)).toReal :=
      ENNReal.toReal_mono hsum_ne_top (hmeasure_le.trans hUnion_le)
    _ = ∑ m ∈ integerWindowIndex Q, (MeasureTheory.volume (integerWindow η m)).toReal := by
      exact ENNReal.toReal_sum (fun m hm => by
        rw [integerWindow, Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top)
    _ = ∑ m ∈ integerWindowIndex Q, 2 * η := by
      refine Finset.sum_congr rfl ?_
      intro m hm
      rw [integerWindow, Real.volume_Ioo]
      have hnonneg : 0 ≤ ((m : ℝ) + η) - ((m : ℝ) - η) := by linarith
      rw [ENNReal.toReal_ofReal hnonneg]
      ring
    _ = ((integerWindowIndex Q).card : ℝ) * (2 * η) := by
      simp

/--
On the good set, a small `GX` perturbation produces a small weighted fractional-part
perturbation.
-/
theorem fract_integrand_close_on_good (D : PhiPsiData B) {Q η X q : ℝ}
    (hη : 0 < η) (hq : q ∈ intGoodSet Q η)
    (hGX : |GX D X (D.Phi (X / q)) - q| < η) :
    |fract (GX D X (D.Phi (X / q))) / q ^ 2 - fract q / q ^ 2| ≤ η := by
  have hq' := (mem_intGoodSet (Q := Q) (η := η) (q := q)).mp hq
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq'.1.1
  have hq_sq_pos : 0 < q ^ 2 := sq_pos_of_ne_zero (ne_of_gt hq_pos)
  have hq_sq_ne : q ^ 2 ≠ 0 := ne_of_gt hq_sq_pos
  have hfract_eq := abs_fract_sub_fract_eq_of_mem_intGoodSet_of_abs_sub_lt
    (Q := Q) (η := η) (q := q) (y := GX D X (D.Phi (X / q))) hη hq hGX
  have hinv_nonneg : 0 ≤ 1 / q ^ 2 := by positivity
  have hinv_le_one : 1 / q ^ 2 ≤ 1 := by
    rw [div_le_iff₀ hq_sq_pos]
    have hsq_ge_one : (1 : ℝ) ≤ q ^ 2 := by
      have hsq := (sq_le_sq₀ zero_le_one (le_of_lt hq_pos)).2 hq'.1.1
      simpa using hsq
    nlinarith
  have hinv_abs : |1 / q ^ 2| ≤ 1 := by
    rw [abs_of_nonneg hinv_nonneg]
    exact hinv_le_one
  calc
    |fract (GX D X (D.Phi (X / q))) / q ^ 2 - fract q / q ^ 2|
        = |(fract (GX D X (D.Phi (X / q))) - fract q) * (1 / q ^ 2)| := by
          congr 1
          field_simp [hq_sq_ne]
    _ = |fract (GX D X (D.Phi (X / q))) - fract q| * |1 / q ^ 2| := by
      rw [abs_mul]
    _ = |GX D X (D.Phi (X / q)) - q| * |1 / q ^ 2| := by
      rw [hfract_eq]
    _ ≤ η * 1 :=
      mul_le_mul (le_of_lt hGX) hinv_abs (abs_nonneg _) (le_of_lt hη)
    _ = η := by ring

/-- Derivative value of the explicit `PhiFormula` branch. -/
noncomputable def PhiDerivFormula (B r : ℝ) : ℝ :=
  lam * r * (2 * H B (Real.log r) - Hderiv (Real.log r)) /
    (H B (Real.log r)) ^ 2

/-- Derivative value normalized by the branch parameter `r`. -/
noncomputable def PhiDerivOverR (B r : ℝ) : ℝ :=
  PhiDerivFormula B r / r

/-- Measurability of `H B`. -/
theorem H_measurable (B : ℝ) :
    Measurable (H B) := by
  unfold H
  fun_prop

/-- Measurability of the explicit `PhiFormula`. -/
theorem PhiFormula_measurable (B : ℝ) :
    Measurable (PhiFormula B) := by
  unfold PhiFormula H
  fun_prop

/-- Measurability of the data-level `Phi`. -/
theorem PhiPsiData.Phi_measurable (D : PhiPsiData B) :
    Measurable D.Phi := by
  rw [show D.Phi = PhiFormula B by
    funext x
    exact D.Phi_eq x]
  exact PhiFormula_measurable B

/-- Measurability of the explicit `Phi` derivative value. -/
theorem PhiDerivFormula_measurable (B : ℝ) :
    Measurable (PhiDerivFormula B) := by
  unfold PhiDerivFormula H Hderiv
  fun_prop

/-- Measurability of the normalized explicit `Phi` derivative. -/
theorem PhiDerivOverR_measurable (B : ℝ) :
    Measurable (PhiDerivOverR B) := by
  unfold PhiDerivOverR
  exact (PhiDerivFormula_measurable B).div measurable_id

/-- Continuity of the composed denominator on sets where the logarithms are regular. -/
theorem H_log_continuousOn {s : Set ℝ} {B : ℝ}
    (hone : ∀ x ∈ s, (1 : ℝ) < x) :
    ContinuousOn (fun x : ℝ => H B (Real.log x)) s := by
  have hid : ContinuousOn (fun x : ℝ => x) s := continuous_id.continuousOn
  have hlog : ContinuousOn (fun x : ℝ => Real.log x) s :=
    hid.log (fun x hx => ne_of_gt (lt_trans zero_lt_one (hone x hx)))
  have hloglog : ContinuousOn (fun x : ℝ => Real.log (Real.log x)) s :=
    hlog.log (fun x hx => ne_of_gt (Real.log_pos (hone x hx)))
  simpa [H] using (hlog.sub hloglog).add continuousOn_const

/-- Continuity of `PhiFormula` on sets contained in a regular positive tail. -/
theorem PhiFormula_continuousOn {s : Set ℝ} {B : ℝ}
    (hone : ∀ x ∈ s, (1 : ℝ) < x)
    (hH : ∀ x ∈ s, H B (Real.log x) ≠ 0) :
    ContinuousOn (PhiFormula B) s := by
  have hnum : ContinuousOn (fun x : ℝ => lam * x ^ 2) s := by fun_prop
  have hden : ContinuousOn (fun x : ℝ => H B (Real.log x)) s :=
    H_log_continuousOn hone
  simpa [PhiFormula] using hnum.div hden hH

/-- Tail estimate form of `H B w ~ w`. -/
theorem eventually_abs_H_sub_self_le_mul (B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ w : ℝ in Filter.atTop, |H B w - w| ≤ δ * w := by
  have hlog : (fun w : ℝ => Real.log w) =o[Filter.atTop] fun w : ℝ => w :=
    Real.isLittleO_log_id_atTop
  have hsmall : (fun w : ℝ => -Real.log w + B) =o[Filter.atTop] fun w : ℝ => w :=
    hlog.neg_left.add (isLittleO_const_id_atTop B)
  filter_upwards [hsmall.def hδ, eventually_ge_atTop (0 : ℝ)] with w hsmallw hw
  have heq : H B w - w = -Real.log w + B := by
    rw [H]
    ring
  calc
    |H B w - w| = ‖(-Real.log w + B)‖ := by
      rw [heq, Real.norm_eq_abs]
    _ ≤ δ * ‖w‖ := hsmallw
    _ = δ * w := by rw [Real.norm_eq_abs, abs_of_nonneg hw]

/-- `PhiDerivFormula` is the derivative value of `PhiFormula` on its regular domain. -/
theorem PhiDerivFormula_hasDerivAt {B r : ℝ}
    (hr : r ≠ 0) (hlogr : Real.log r ≠ 0) (hH : H B (Real.log r) ≠ 0) :
    HasDerivAt (PhiFormula B) (PhiDerivFormula B r) r := by
  simpa [PhiDerivFormula] using PhiFormula_hasDerivAt (B := B) (x := r) hr hlogr hH

/-- The data-level `Phi` has the same derivative as its explicit formula. -/
theorem PhiPsiData.Phi_hasDerivAt {B r : ℝ} (D : PhiPsiData B)
    (hr : r ≠ 0) (hlogr : Real.log r ≠ 0) (hH : H B (Real.log r) ≠ 0) :
    HasDerivAt D.Phi (PhiDerivFormula B r) r := by
  have hformula : D.Phi = PhiFormula B := by
    funext x
    exact D.Phi_eq x
  rw [hformula]
  exact PhiDerivFormula_hasDerivAt hr hlogr hH

/-- Algebraic simplification of the derivative normalized by `r`. -/
theorem PhiDerivOverR_eq {B r : ℝ} (hr : r ≠ 0) :
    PhiDerivOverR B r =
      lam * (2 * H B (Real.log r) - Hderiv (Real.log r)) /
        (H B (Real.log r)) ^ 2 := by
  rw [PhiDerivOverR, PhiDerivFormula]
  field_simp [hr]

/-- Undo the normalization in `PhiDerivOverR`. -/
theorem PhiDerivFormula_eq_mul_PhiDerivOverR {B r : ℝ} (hr : r ≠ 0) :
    PhiDerivFormula B r = r * PhiDerivOverR B r := by
  rw [PhiDerivOverR]
  field_simp [hr]

/-- Eventually, the data-level `Phi` has the explicit derivative. -/
theorem eventually_Phi_hasDerivAt (D : PhiPsiData B) :
    ∀ᶠ r : ℝ in Filter.atTop,
      HasDerivAt D.Phi (PhiDerivFormula B r) r := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_H_log_ne_zero_atTop B] with r hr hH
  have hr_ne : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
  have hlog_ne : Real.log r ≠ 0 := ne_of_gt (Real.log_pos hr)
  exact D.Phi_hasDerivAt hr_ne hlog_ne hH

/-- For fixed `Q`, eventually `Phi` is differentiable at every `X/q`, `q ∈ [1,Q]`. -/
theorem eventually_Phi_hasDerivAt_X_div_q_on_Icc (D : PhiPsiData B) {Q : ℝ}
    (hQ : 0 < Q) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ q ∈ Set.Icc (1 : ℝ) Q,
        HasDerivAt D.Phi (PhiDerivFormula B (X / q)) (X / q) := by
  rcases Filter.eventually_atTop.mp (eventually_Phi_hasDerivAt D) with ⟨T, hder⟩
  have hX_div_Q_ge_T :
      ∀ᶠ X : ℝ in Filter.atTop, T ≤ X / Q :=
    (Filter.Tendsto.atTop_div_const hQ tendsto_id).eventually_ge_atTop T
  filter_upwards [hX_div_Q_ge_T, eventually_ge_atTop (0 : ℝ)] with
    X hX_div_Q hX_nonneg q hq
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq.1
  have hdiv_le : X / Q ≤ X / q :=
    div_le_div_of_nonneg_left hX_nonneg hq_pos hq.2
  exact hder (X / q) (hX_div_Q.trans hdiv_le)

/-- For fixed `Q`, eventually the q-parametrized branch is continuous on `[1,Q]`. -/
theorem eventually_Phi_comp_X_div_continuousOn (D : PhiPsiData B) {Q : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ContinuousOn (fun q : ℝ => D.Phi (X / q)) (Set.uIcc (1 : ℝ) Q) := by
  rcases Filter.eventually_atTop.mp (eventually_H_log_ne_zero_atTop B) with ⟨TH, hHtail⟩
  let T : ℝ := max TH 2
  have hT_gt_one : (1 : ℝ) < T := by
    dsimp [T]
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right TH 2)
  have hTH_le_T : TH ≤ T := by
    dsimp [T]
    exact le_max_left TH 2
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hX_div_Q_ge_T : ∀ᶠ X : ℝ in Filter.atTop, T ≤ X / Q :=
    (Filter.Tendsto.atTop_div_const hQ_pos tendsto_id).eventually_ge_atTop T
  filter_upwards [hX_div_Q_ge_T, eventually_ge_atTop (0 : ℝ)] with X hXdiv hXnonneg
  have harg : Set.MapsTo (fun q : ℝ => X / q) (Set.uIcc (1 : ℝ) Q) (Set.Ici T) := by
    intro q hq
    have hqI : q ∈ Set.Icc (1 : ℝ) Q := by
      simpa [Set.uIcc_of_le hQ] using hq
    have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hqI.1
    have hdiv_le : X / Q ≤ X / q :=
      div_le_div_of_nonneg_left hXnonneg hq_pos hqI.2
    exact hXdiv.trans hdiv_le
  have hdiv_cont : ContinuousOn (fun q : ℝ => X / q) (Set.uIcc (1 : ℝ) Q) := by
    refine continuousOn_const.div continuousOn_id ?_
    intro q hq
    have hqI : q ∈ Set.Icc (1 : ℝ) Q := by
      simpa [Set.uIcc_of_le hQ] using hq
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hqI.1)
  have hPhi_formula_cont : ContinuousOn (PhiFormula B) (Set.Ici T) := by
    refine PhiFormula_continuousOn ?_ ?_
    · intro r hr
      exact hT_gt_one.trans_le hr
    · intro r hr
      exact hHtail r (hTH_le_T.trans hr)
  have hPhi_cont : ContinuousOn D.Phi (Set.Ici T) := by
    refine hPhi_formula_cont.congr ?_
    intro r _hr
    exact D.Phi_eq r
  exact hPhi_cont.comp hdiv_cont harg

/-- For fixed `Q`, the explicit derivative of `Phi` is eventually nonnegative on `X/q`. -/
theorem eventually_PhiDerivFormula_nonneg_X_div_q_on_Icc {B Q : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ q ∈ Set.Icc (1 : ℝ) Q, 0 ≤ PhiDerivFormula B (X / q) := by
  rcases Filter.eventually_atTop.mp (eventually_PhiFormula_deriv_value_pos_atTop B) with
    ⟨T, hpos⟩
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hX_div_Q_ge_T : ∀ᶠ X : ℝ in Filter.atTop, T ≤ X / Q :=
    (Filter.Tendsto.atTop_div_const hQ_pos tendsto_id).eventually_ge_atTop T
  filter_upwards [hX_div_Q_ge_T, eventually_ge_atTop (0 : ℝ)] with X hXdiv hXnonneg q hq
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq.1
  have hdiv_le : X / Q ≤ X / q :=
    div_le_div_of_nonneg_left hXnonneg hq_pos hq.2
  exact le_of_lt (hpos (X / q) (hXdiv.trans hdiv_le))

/-- Derivative of the decreasing map `q ↦ X/q`. -/
theorem hasDerivAt_X_div (X q : ℝ) (hq : q ≠ 0) :
    HasDerivAt (fun u : ℝ => X / u) (-X / q ^ 2) q := by
  have hmul : HasDerivAt (fun y : ℝ => X * y⁻¹) (X * (-(q ^ 2)⁻¹)) q :=
    (hasDerivAt_inv hq).const_mul X
  rw [show (fun y : ℝ => X / y) = fun y : ℝ => X * y⁻¹ by
    funext y
    rw [div_eq_mul_inv]]
  convert hmul using 1
  field_simp [hq]

/-- Derivative of the q-parametrized branch map `q ↦ Phi (X/q)`. -/
theorem Phi_comp_X_div_hasDerivAt (D : PhiPsiData B) {X q : ℝ}
    (hq : q ≠ 0)
    (hXq_ne : X / q ≠ 0)
    (hlog_ne : Real.log (X / q) ≠ 0)
    (hH : H B (Real.log (X / q)) ≠ 0) :
    HasDerivAt (fun u : ℝ => D.Phi (X / u))
      (PhiDerivFormula B (X / q) * (-X / q ^ 2)) q := by
  exact (D.Phi_hasDerivAt hXq_ne hlog_ne hH).comp q (hasDerivAt_X_div X q hq)

theorem qOf_eq_X_mul_f_of_tail (D : PhiPsiData B) {X t : ℝ}
    (ht : D.Tstar ≤ t) :
    qOf D X t = X * D.f t := by
  rw [qOf, D.f_eq_tail t ht]
  ring

/-- On the inverse branch, the majorant at `Phi r` is exactly `1/r`. -/
theorem f_Phi_eq_inv_of_tail (D : PhiPsiData B) {r : ℝ}
    (hr : (D.N0 : ℝ) ≤ r) :
    D.f (D.Phi r) = 1 / r := by
  rw [D.f_eq_tail (D.Phi r) (D.Phi_maps_tail r hr), D.psi_right_inv r hr]

/-- On the inverse branch, `qOf` at `Phi r` is exactly `X/r`. -/
theorem qOf_Phi_eq_div_of_tail (D : PhiPsiData B) {X r : ℝ}
    (hr : (D.N0 : ℝ) ≤ r) :
    qOf D X (D.Phi r) = X / r := by
  rw [qOf, D.psi_right_inv r hr]

theorem qOf_Phi_div (D : PhiPsiData B) {X Q : ℝ}
    (hX : X ≠ 0) (hQ : Q ≠ 0) (hbranch : (D.N0 : ℝ) ≤ X / Q) :
    qOf D X (D.Phi (X / Q)) = Q := by
  rw [qOf, D.psi_right_inv (X / Q) hbranch]
  field_simp [hX, hQ]

theorem qOf_Phi_X_div_q (D : PhiPsiData B) {X q : ℝ}
    (hX : X ≠ 0) (hq : q ≠ 0) (hbranch : (D.N0 : ℝ) ≤ X / q) :
    qOf D X (D.Phi (X / q)) = q :=
  qOf_Phi_div D hX hq hbranch

/-- The branch value of `f` at `Phi (X/q)` is `q/X`. -/
theorem f_Phi_X_div_q_eq_q_div_X (D : PhiPsiData B) {X q : ℝ}
    (hX : X ≠ 0) (hq : q ≠ 0) (hbranch : (D.N0 : ℝ) ≤ X / q) :
    D.f (D.Phi (X / q)) = q / X := by
  rw [f_Phi_eq_inv_of_tail D hbranch]
  field_simp [hX, hq]

/-- Multiplying the previous branch identity by `X` gives the q-coordinate. -/
theorem X_mul_f_Phi_X_div_q_eq_q (D : PhiPsiData B) {X q : ℝ}
    (hX : X ≠ 0) (hq : q ≠ 0) (hbranch : (D.N0 : ℝ) ≤ X / q) :
    X * D.f (D.Phi (X / q)) = q := by
  rw [f_Phi_X_div_q_eq_q_div_X D hX hq hbranch]
  field_simp [hX]

theorem qOf_Phi_self (D : PhiPsiData B) {X : ℝ}
    (hX : X ≠ 0) (hbranch : (D.N0 : ℝ) ≤ X) :
    qOf D X (D.Phi X) = 1 := by
  rw [qOf, D.psi_right_inv X hbranch]
  field_simp [hX]

/-- Eventually, the lower fixed-`Q` branch input `X/Q` lies in the selected tail. -/
theorem eventually_X_div_Q_ge_N0 (D : PhiPsiData B) {Q : ℝ} (hQ : 0 < Q) :
    ∀ᶠ X : ℝ in Filter.atTop, (D.N0 : ℝ) ≤ X / Q := by
  exact (Filter.Tendsto.atTop_div_const hQ tendsto_id).eventually_ge_atTop (D.N0 : ℝ)

/-- Eventually, the lower fixed-`Q` cutoff lies in the inverse-branch target range. -/
theorem eventually_Tstar_le_Phi_X_div_Q (D : PhiPsiData B) {Q : ℝ} (hQ : 0 < Q) :
    ∀ᶠ X : ℝ in Filter.atTop, D.Tstar ≤ D.Phi (X / Q) := by
  filter_upwards [eventually_X_div_Q_ge_N0 D hQ] with X hbranch
  exact D.Phi_maps_tail (X / Q) hbranch

/-- The lower fixed-`Q` cutoff eventually lies to the right of `X`. -/
theorem eventually_X_le_Phi_X_div_Q (D : PhiPsiData B) {Q : ℝ} (hQ : 0 < Q) :
    ∀ᶠ X : ℝ in Filter.atTop, X ≤ D.Phi (X / Q) := by
  have hdiv_atTop : Tendsto (fun X : ℝ => X / Q) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hQ tendsto_id
  filter_upwards [hdiv_atTop.eventually (Phi_dominates_fixed_multiple D Q)] with X hdom
  have hQ_ne : Q ≠ 0 := ne_of_gt hQ
  calc
    X = Q * (X / Q) := by
      field_simp [hQ_ne]
    _ ≤ D.Phi (X / Q) := hdom

/-- The lower fixed-`Q` cutoff eventually lies before the full endpoint. -/
theorem eventually_Phi_X_div_Q_le_Phi_X (D : PhiPsiData B) {Q : ℝ} (hQ : (1 : ℝ) ≤ Q) :
    ∀ᶠ X : ℝ in Filter.atTop, D.Phi (X / Q) ≤ D.Phi X := by
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  filter_upwards [eventually_ge_atTop (0 : ℝ), eventually_X_div_Q_ge_N0 D hQ_pos] with
    X hX_nonneg hbranch
  have hdiv_le : X / Q ≤ X := by
    rw [div_le_iff₀ hQ_pos]
    have hmul := mul_le_mul_of_nonneg_left hQ hX_nonneg
    simpa using hmul
  have hX_branch : (D.N0 : ℝ) ≤ X := hbranch.trans hdiv_le
  exact D.Phi_mono_tail hbranch hX_branch hdiv_le

/-- Packaged fixed-`Q` branch and endpoint order facts for the main interval. -/
theorem eventually_Phi_X_div_Q_between (D : PhiPsiData B) {Q : ℝ} (hQ : (1 : ℝ) ≤ Q) :
    ∀ᶠ X : ℝ in Filter.atTop,
      (D.N0 : ℝ) ≤ X / Q ∧
        D.Tstar ≤ D.Phi (X / Q) ∧
          0 ≤ X ∧
            X ≤ D.Phi (X / Q) ∧
              D.Phi (X / Q) ≤ D.Phi X := by
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  filter_upwards [eventually_X_div_Q_ge_N0 D hQ_pos,
      eventually_Tstar_le_Phi_X_div_Q D hQ_pos, eventually_ge_atTop (0 : ℝ),
      eventually_X_le_Phi_X_div_Q D hQ_pos,
      eventually_Phi_X_div_Q_le_Phi_X D hQ] with X hbranch hTstar hX hleft hright
  exact ⟨hbranch, hTstar, hX, hleft, hright⟩

/-- Uniform fixed-`Q` branch fact for all `q ∈ [1,Q]`. -/
theorem eventually_X_div_q_ge_N0_on_Icc (D : PhiPsiData B) {Q : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ q ∈ Set.Icc (1 : ℝ) Q, (D.N0 : ℝ) ≤ X / q := by
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  filter_upwards [eventually_X_div_Q_ge_N0 D hQ_pos,
      eventually_ge_atTop (0 : ℝ)] with X hbranch hX_nonneg q hq
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq.1
  have hdiv_le : X / Q ≤ X / q :=
    div_le_div_of_nonneg_left hX_nonneg hq_pos hq.2
  exact hbranch.trans hdiv_le

/-- Uniform fixed-`Q` branch and endpoint order for all `q ∈ [1,Q]`. -/
theorem eventually_Phi_X_div_q_between_on_Icc (D : PhiPsiData B) {Q : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ q ∈ Set.Icc (1 : ℝ) Q,
        (D.N0 : ℝ) ≤ X / q ∧
          D.Tstar ≤ D.Phi (X / q) ∧
            0 ≤ X ∧
              X ≤ D.Phi (X / q) ∧
                D.Phi (X / q) ≤ D.Phi X := by
  filter_upwards [eventually_Phi_X_div_Q_between D hQ,
      eventually_X_div_q_ge_N0_on_Icc D hQ] with X hQorder hbranch_q q hq
  rcases hQorder with ⟨hbranch_Q, _hTstar_Q, hX_nonneg, hXcut_Q, _hcutPhi_Q⟩
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq.1
  have hdiv_Q_le_div_q : X / Q ≤ X / q :=
    div_le_div_of_nonneg_left hX_nonneg hq_pos hq.2
  have hPhi_Q_le_Phi_q : D.Phi (X / Q) ≤ D.Phi (X / q) :=
    D.Phi_mono_tail hbranch_Q (hbranch_q q hq) hdiv_Q_le_div_q
  have hX_div_q_le_X : X / q ≤ X := by
    rw [div_le_iff₀ hq_pos]
    have hmul := mul_le_mul_of_nonneg_left hq.1 hX_nonneg
    simpa using hmul
  have hbranch_X : (D.N0 : ℝ) ≤ X :=
    (hbranch_q q hq).trans hX_div_q_le_X
  refine ⟨hbranch_q q hq, D.Phi_maps_tail (X / q) (hbranch_q q hq),
    hX_nonneg, hXcut_Q.trans hPhi_Q_le_Phi_q, ?_⟩
  exact D.Phi_mono_tail (hbranch_q q hq) hbranch_X hX_div_q_le_X

/-- Uniform fixed-`Q` domination placing the correction window inside `[t/2,t]`. -/
theorem eventually_two_mul_X_le_Phi_X_div_q_on_Icc (D : PhiPsiData B) {Q : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ q ∈ Set.Icc (1 : ℝ) Q, 2 * X ≤ D.Phi (X / q) := by
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hdiv_atTop : Tendsto (fun X : ℝ => X / Q) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hQ_pos tendsto_id
  filter_upwards [hdiv_atTop.eventually (Phi_dominates_fixed_multiple D (2 * Q)),
      eventually_X_div_Q_ge_N0 D hQ_pos, eventually_X_div_q_ge_N0_on_Icc D hQ,
      eventually_ge_atTop (0 : ℝ)] with X hdom hbranch_Q hbranch_q hX_nonneg q hq
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq.1
  have hdiv_Q_le_div_q : X / Q ≤ X / q :=
    div_le_div_of_nonneg_left hX_nonneg hq_pos hq.2
  have hPhi_Q_le_Phi_q : D.Phi (X / Q) ≤ D.Phi (X / q) :=
    D.Phi_mono_tail hbranch_Q (hbranch_q q hq) hdiv_Q_le_div_q
  have hQ_ne : Q ≠ 0 := ne_of_gt hQ_pos
  calc
    2 * X = (2 * Q) * (X / Q) := by
      field_simp [hQ_ne]
    _ ≤ D.Phi (X / Q) := hdom
    _ ≤ D.Phi (X / q) := hPhi_Q_le_Phi_q

/-- Fixed-`Q` branch and order package under the strict hypothesis used in the TeX proof. -/
theorem eventually_fixedQ_branch_order (D : PhiPsiData B) {Q : ℝ} (hQ : (1 : ℝ) < Q) :
    ∀ᶠ X : ℝ in Filter.atTop,
      (D.N0 : ℝ) ≤ X / Q ∧
        D.Tstar ≤ D.Phi (X / Q) ∧
          0 ≤ X ∧
            X ≤ D.Phi (X / Q) ∧
              D.Phi (X / Q) ≤ D.Phi X :=
  eventually_Phi_X_div_Q_between D hQ.le

/-- For fixed positive `Q`, eventually `log (X/Q)` is at least half of `log X`. -/
theorem eventually_half_log_le_log_X_div_Q {Q : ℝ} (hQ : 0 < Q) :
    ∀ᶠ X : ℝ in Filter.atTop,
      (1 / 2 : ℝ) * Real.log X ≤ Real.log (X / Q) := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log Q),
      eventually_gt_atTop (0 : ℝ)] with X hlog hX
  rw [Real.log_div (ne_of_gt hX) (ne_of_gt hQ)]
  nlinarith

/-- Uniform control of `log X / log (X/q)` for `q ∈ [1,Q]`. -/
theorem log_div_log_X_div_q_uniform_sub_one_le {Q c : ℝ}
    (hQ : (1 : ℝ) ≤ Q) (hc : 0 < c) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ q ∈ Set.Icc (1 : ℝ) Q,
      |Real.log X / Real.log (X / q) - 1| ≤ c := by
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hε_pos : 0 < (1 / Q : ℝ) := one_div_pos.mpr hQ_pos
  have hεU : (1 / Q : ℝ) ≤ 1 := by
    have h := one_div_le_one_div_of_le zero_lt_one hQ
    simpa using h
  filter_upwards [log_div_log_mul_uniform_sub_one_le hε_pos hεU hc] with X hX q hq
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq.1
  have hv_mem : q⁻¹ ∈ Set.Icc (1 / Q : ℝ) 1 := by
    constructor
    · have hinv := (inv_le_inv₀ hQ_pos hq_pos).2 hq.2
      simpa [one_div] using hinv
    · have h := one_div_le_one_div_of_le zero_lt_one hq.1
      simpa [one_div] using h
  simpa [div_eq_mul_inv] using hX q⁻¹ hv_mem

/-- Uniform fixed-`Q` form of `H(log (X/q)) = log (X/q) + o(log (X/q))`. -/
theorem eventually_abs_H_log_X_div_q_sub_le_mul {B Q δ : ℝ}
    (hQ : (1 : ℝ) ≤ Q) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ q ∈ Set.Icc (1 : ℝ) Q,
      |H B (Real.log (X / q)) - Real.log (X / q)| ≤ δ * Real.log (X / q) := by
  rcases Filter.eventually_atTop.mp (eventually_abs_H_sub_self_le_mul B hδ) with ⟨T, hT⟩
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hlog_atTop : Tendsto (fun X : ℝ => Real.log (X / Q)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Filter.Tendsto.atTop_div_const hQ_pos tendsto_id)
  filter_upwards [hlog_atTop.eventually_ge_atTop T, eventually_gt_atTop (0 : ℝ)] with
    X hlogQ hX_pos q hq
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq.1
  have hX_nonneg : 0 ≤ X := le_of_lt hX_pos
  have hdiv_le : X / Q ≤ X / q := div_le_div_of_nonneg_left hX_nonneg hq_pos hq.2
  have hXQ_pos : 0 < X / Q := div_pos hX_pos hQ_pos
  have hlog_le : Real.log (X / Q) ≤ Real.log (X / q) :=
    Real.log_le_log hXQ_pos hdiv_le
  exact hT (Real.log (X / q)) (hlogQ.trans hlog_le)

set_option maxHeartbeats 800000 in
-- The proof is a long explicit real-inequality normalization of the exact Jacobian.
/--
Uniform fixed-`Q` first-order Jacobian estimate for the exact q-change weight.

This is intentionally proved as an eventual epsilon statement: it is the form needed to replace
the exact Jacobian in `eventually_q_change_exact_fixed_Q`.
-/
theorem eventually_jacobian_weight_uniform_fixed_Q {B Q ε : ℝ}
    (hQ : (1 : ℝ) ≤ Q) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ q ∈ Set.Icc (1 : ℝ) Q,
      |Real.log X / (2 * lam) * PhiDerivOverR B (X / q) - 1| ≤ ε := by
  let δ : ℝ := min (1 / 4) (ε / 16)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (by positivity)
  have hδ_le_quarter : δ ≤ (1 / 4 : ℝ) := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_eps : δ ≤ ε / 16 := by
    dsimp [δ]
    exact min_le_right _ _
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  filter_upwards [log_div_log_X_div_q_uniform_sub_one_le hQ hδ_pos,
      eventually_abs_H_log_X_div_q_sub_le_mul (B := B) hQ hδ_pos,
      eventually_half_log_le_log_X_div_Q hQ_pos,
      Real.tendsto_log_atTop.eventually_ge_atTop (max 4 (16 / ε)),
      eventually_gt_atTop (0 : ℝ)] with X hlogratio hHclose hhalf hloglarge hX_pos q hq
  let L : ℝ := Real.log (X / q)
  let HX : ℝ := H B L
  let HD : ℝ := Hderiv L
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq.1
  have hXq_pos : 0 < X / q := div_pos hX_pos hq_pos
  have hXq_ne : X / q ≠ 0 := ne_of_gt hXq_pos
  have hX_gt_one : 1 < X := by
    have hlog_ge_four : (4 : ℝ) ≤ Real.log X := (le_max_left _ _).trans hloglarge
    have hlog_pos : 0 < Real.log X := by linarith
    have hexp : Real.exp 0 < X := (Real.lt_log_iff_exp_lt hX_pos).1 hlog_pos
    simpa using hexp
  have hlogX_pos : 0 < Real.log X := Real.log_pos hX_gt_one
  have hL_pos : 0 < L := by
    dsimp [L]
    have hL_ge : (1 / 2 : ℝ) * Real.log X ≤ Real.log (X / q) := by
      have hdiv_Q_le_div_q : X / Q ≤ X / q :=
        div_le_div_of_nonneg_left (le_of_lt hX_pos) hq_pos hq.2
      have hXQ_pos : 0 < X / Q := div_pos hX_pos hQ_pos
      exact hhalf.trans (Real.log_le_log hXQ_pos hdiv_Q_le_div_q)
    nlinarith
  have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
  have hHclose' : |HX - L| ≤ δ * L := by
    simpa [L, HX] using hHclose q hq
  have hH_lower : (1 / 2 : ℝ) * L ≤ HX := by
    have habs := abs_le.mp hHclose'
    have hleft : - (δ * L) ≤ HX - L := habs.1
    have hδL_le_half : δ * L ≤ (1 / 2 : ℝ) * L := by
      exact mul_le_mul_of_nonneg_right (by nlinarith : δ ≤ (1 / 2 : ℝ)) hL_nonneg
    nlinarith
  have hH_pos : 0 < HX := lt_of_lt_of_le (by nlinarith : 0 < (1 / 2 : ℝ) * L) hH_lower
  have hH_ne : HX ≠ 0 := ne_of_gt hH_pos
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have hratio_LH_abs : |L / HX - 1| ≤ 2 * δ := by
    have hnum : |L - HX| ≤ δ * L := by
      simpa [abs_sub_comm] using hHclose'
    have hcalc : |L / HX - 1| = |L - HX| / HX := by
      have heq : L / HX - 1 = (L - HX) / HX := by
        field_simp [hH_ne]
      rw [heq, abs_div, abs_of_pos hH_pos]
    rw [hcalc]
    have hden : δ * L / HX ≤ 2 * δ := by
      rw [div_le_iff₀ hH_pos]
      nlinarith
    exact (div_le_div_of_nonneg_right hnum (le_of_lt hH_pos)).trans hden
  have hLH_abs_le_two : |L / HX| ≤ 2 := by
    have hpos : 0 ≤ L / HX := div_nonneg hL_nonneg (le_of_lt hH_pos)
    rw [abs_of_nonneg hpos]
    rw [div_le_iff₀ hH_pos]
    nlinarith
  have hlogX_H_abs : |Real.log X / HX - 1| ≤ 4 * δ := by
    let a : ℝ := Real.log X / L
    let b : ℝ := L / HX
    have ha : |a - 1| ≤ δ := by simpa [a, L] using hlogratio q hq
    have hb : |b - 1| ≤ 2 * δ := by simpa [b] using hratio_LH_abs
    have hb_abs : |b| ≤ 2 := by simpa [b] using hLH_abs_le_two
    have hprod : |a * b - 1| ≤ |a - 1| * |b| + |b - 1| := by
      have heq : a * b - 1 = (a - 1) * b + (b - 1) := by ring
      rw [heq]
      calc
        |(a - 1) * b + (b - 1)| = |(a - 1) * b - (-(b - 1))| := by ring_nf
        _ ≤ |(a - 1) * b| + |-(b - 1)| := abs_sub _ _
        _ = |a - 1| * |b| + |b - 1| := by rw [abs_mul, abs_neg]
    have hbound : |a - 1| * |b| + |b - 1| ≤ δ * 2 + 2 * δ := by
      exact add_le_add (mul_le_mul ha hb_abs (abs_nonneg _) (le_of_lt hδ_pos)) hb
    have hab := hprod.trans hbound
    have hab4 : |a * b - 1| ≤ 4 * δ := by nlinarith
    have heq_ab : a * b = Real.log X / HX := by
      dsimp [a, b]
      field_simp [hL_ne, hH_ne]
    simpa [heq_ab] using hab4
  have hHD_abs_le_one : |HD| ≤ 1 := by
    have hL_ge_one : 1 ≤ L := by
      have hlog_ge_four : (4 : ℝ) ≤ Real.log X := (le_max_left _ _).trans hloglarge
      have hL_ge_half : (1 / 2 : ℝ) * Real.log X ≤ L := by
        dsimp [L]
        have hdiv_Q_le_div_q : X / Q ≤ X / q :=
          div_le_div_of_nonneg_left (le_of_lt hX_pos) hq_pos hq.2
        have hXQ_pos : 0 < X / Q := div_pos hX_pos hQ_pos
        exact hhalf.trans (Real.log_le_log hXQ_pos hdiv_Q_le_div_q)
      nlinarith
    dsimp [HD, Hderiv]
    rw [abs_le]
    constructor <;> field_simp [ne_of_gt hL_pos] <;> nlinarith
  have htail_abs : |Real.log X * HD / (2 * HX ^ 2)| ≤ ε / 2 := by
    have hH_ge_log : (1 / 4 : ℝ) * Real.log X ≤ HX := by
      have hL_ge_half : (1 / 2 : ℝ) * Real.log X ≤ L := by
        dsimp [L]
        have hdiv_Q_le_div_q : X / Q ≤ X / q :=
          div_le_div_of_nonneg_left (le_of_lt hX_pos) hq_pos hq.2
        have hXQ_pos : 0 < X / Q := div_pos hX_pos hQ_pos
        exact hhalf.trans (Real.log_le_log hXQ_pos hdiv_Q_le_div_q)
      nlinarith
    have hHsq_ge : ((1 / 4 : ℝ) * Real.log X) ^ 2 ≤ HX ^ 2 := by
      exact (sq_le_sq₀ (by positivity) (le_of_lt hH_pos)).2 hH_ge_log
    have hden_pos : 0 < 2 * HX ^ 2 := by positivity
    have hbasic : |Real.log X * HD / (2 * HX ^ 2)| ≤ Real.log X / (2 * HX ^ 2) := by
      rw [abs_div, abs_mul, abs_of_pos hlogX_pos, abs_of_pos hden_pos]
      have hden_nonneg : 0 ≤ 2 * HX ^ 2 := le_of_lt hden_pos
      calc
        Real.log X * |HD| / (2 * HX ^ 2) ≤ Real.log X * 1 / (2 * HX ^ 2) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hHD_abs_le_one (le_of_lt hlogX_pos)) hden_nonneg
        _ = Real.log X / (2 * HX ^ 2) := by ring
    have hle8 : Real.log X / (2 * HX ^ 2) ≤ 8 / Real.log X := by
      rw [div_le_div_iff₀ hden_pos hlogX_pos]
      have htmp : (Real.log X) ^ 2 / 16 ≤ HX ^ 2 := by nlinarith
      nlinarith
    have h8le : 8 / Real.log X ≤ ε / 2 := by
      have hlog_ge : 16 / ε ≤ Real.log X := (le_max_right _ _).trans hloglarge
      have h16le : (16 : ℝ) ≤ ε * Real.log X := by
        rw [div_le_iff₀ hε] at hlog_ge
        nlinarith
      rw [div_le_iff₀ hlogX_pos]
      nlinarith
    exact hbasic.trans (hle8.trans h8le)
  have hW_eq :
      Real.log X / (2 * lam) * PhiDerivOverR B (X / q) - 1 =
        (Real.log X / HX - 1) - Real.log X * HD / (2 * HX ^ 2) := by
    have hlam_pos : 0 < lam := by
      unfold lam
      positivity
    have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
    rw [PhiDerivOverR_eq hXq_ne]
    change Real.log X / (2 * lam) * (lam * (2 * HX - HD) / HX ^ 2) - 1 =
      (Real.log X / HX - 1) - Real.log X * HD / (2 * HX ^ 2)
    field_simp [hlam_ne, hH_ne]
    ring
  rw [hW_eq]
  calc
    |(Real.log X / HX - 1) - Real.log X * HD / (2 * HX ^ 2)|
        ≤ |Real.log X / HX - 1| + |Real.log X * HD / (2 * HX ^ 2)| :=
          abs_sub (Real.log X / HX - 1) (Real.log X * HD / (2 * HX ^ 2))
    _ ≤ 4 * δ + ε / 2 := add_le_add hlogX_H_abs htail_abs
    _ ≤ ε := by nlinarith

/-- Uniform fixed-`Q` first-order form of `PhiDerivOverR`. -/
theorem eventually_PhiDerivOverR_uniform_fixed_Q {B Q ε : ℝ}
    (hQ : (1 : ℝ) ≤ Q) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ q ∈ Set.Icc (1 : ℝ) Q,
      |Real.log X * PhiDerivOverR B (X / q) - 2 * lam| ≤ ε := by
  have hlam_pos : 0 < 2 * lam := by
    unfold lam
    positivity
  have hscaled_pos : 0 < ε / (2 * lam) := div_pos hε hlam_pos
  have hlam_ne : lam ≠ 0 := by
    unfold lam
    positivity
  filter_upwards [eventually_jacobian_weight_uniform_fixed_Q (B := B) (Q := Q)
      hQ hscaled_pos] with X hX q hq
  have h := hX q hq
  have hfactor :
      |Real.log X * PhiDerivOverR B (X / q) - 2 * lam| =
        (2 * lam) * |Real.log X / (2 * lam) * PhiDerivOverR B (X / q) - 1| := by
    have heq : Real.log X * PhiDerivOverR B (X / q) - 2 * lam =
        (2 * lam) * (Real.log X / (2 * lam) * PhiDerivOverR B (X / q) - 1) := by
      field_simp [ne_of_gt hlam_pos, hlam_ne]
    rw [heq, abs_mul, abs_of_pos hlam_pos]
  rw [hfactor]
  calc
    (2 * lam) * |Real.log X / (2 * lam) * PhiDerivOverR B (X / q) - 1| ≤
        (2 * lam) * (ε / (2 * lam)) :=
      mul_le_mul_of_nonneg_left h (le_of_lt hlam_pos)
    _ = ε := by
      field_simp [ne_of_gt hlam_pos, hlam_ne]

/-- Uniform fixed-`Q` lower bound for the q-parametrized branch point. -/
theorem eventually_Phi_X_div_q_lower_uniform_fixed_Q
    (D : PhiPsiData B) {Q : ℝ} (hQ : (1 : ℝ) ≤ Q) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ q ∈ Set.Icc (1 : ℝ) Q,
        (lam / 2) * X ^ 2 / (q ^ 2 * Real.log X) ≤ D.Phi (X / q) := by
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  filter_upwards [eventually_abs_H_log_X_div_q_sub_le_mul (B := B) (Q := Q)
      hQ (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_half_log_le_log_X_div_Q hQ_pos,
      eventually_gt_atTop (1 : ℝ)] with X hHclose hhalf hX_one q hq
  have hX_pos : 0 < X := lt_trans zero_lt_one hX_one
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq.1
  have hXq_pos : 0 < X / q := div_pos hX_pos hq_pos
  have hlogX_pos : 0 < Real.log X := Real.log_pos hX_one
  have hX_div_q_le_X : X / q ≤ X := by
    rw [div_le_iff₀ hq_pos]
    have hmul := mul_le_mul_of_nonneg_left hq.1 (le_of_lt hX_pos)
    simpa using hmul
  have hlog_le : Real.log (X / q) ≤ Real.log X :=
    Real.log_le_log hXq_pos hX_div_q_le_X
  have hL_pos : 0 < Real.log (X / q) := by
    have hdiv_Q_le_div_q : X / Q ≤ X / q :=
      div_le_div_of_nonneg_left (le_of_lt hX_pos) hq_pos hq.2
    have hXQ_pos : 0 < X / Q := div_pos hX_pos hQ_pos
    have hlog_Q_le : Real.log (X / Q) ≤ Real.log (X / q) :=
      Real.log_le_log hXQ_pos hdiv_Q_le_div_q
    have hhalf_pos : 0 < (1 / 2 : ℝ) * Real.log X := by positivity
    exact lt_of_lt_of_le hhalf_pos (hhalf.trans hlog_Q_le)
  have hH_abs := hHclose q hq
  have hH_upper : H B (Real.log (X / q)) ≤ 2 * Real.log (X / q) := by
    have habs := abs_le.mp hH_abs
    have hright : H B (Real.log (X / q)) - Real.log (X / q) ≤
        (1 / 2 : ℝ) * Real.log (X / q) := habs.2
    nlinarith
  have hH_pos : 0 < H B (Real.log (X / q)) := by
    have habs := abs_le.mp hH_abs
    have hleft : - ((1 / 2 : ℝ) * Real.log (X / q)) ≤
        H B (Real.log (X / q)) - Real.log (X / q) := habs.1
    nlinarith
  have hnum_nonneg : 0 ≤ lam * (X / q) ^ 2 := by
    unfold lam
    positivity
  have hH_le_logX : H B (Real.log (X / q)) ≤ 2 * Real.log X := by nlinarith
  calc
    (lam / 2) * X ^ 2 / (q ^ 2 * Real.log X)
        = lam * (X / q) ^ 2 / (2 * Real.log X) := by
      have hq_ne : q ≠ 0 := ne_of_gt hq_pos
      have hlog_ne : Real.log X ≠ 0 := ne_of_gt hlogX_pos
      field_simp [hq_ne, hlog_ne]
    _ ≤ lam * (X / q) ^ 2 / H B (Real.log (X / q)) :=
      div_le_div_of_nonneg_left hnum_nonneg hH_pos hH_le_logX
    _ = D.Phi (X / q) := by
      rw [D.Phi_eq, PhiFormula]

/-- Uniform fixed-`Q` upper bound for the lower cutoff, with constant independent of `Q`. -/
theorem Phi_X_div_Q_upper_uniform (D : PhiPsiData B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : ℝ, (2 : ℝ) ≤ Q →
        ∀ᶠ X : ℝ in Filter.atTop,
          D.Phi (X / Q) ≤ C * X ^ 2 / (Q ^ 2 * Real.log X) := by
  let C : ℝ := 4 * lam
  have hC_pos : 0 < C := by
    dsimp [C]
    unfold lam
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro Q hQ_two
  have hQ_pos : 0 < Q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hQ_two
  have hlog_div_atTop :
      Tendsto (fun X : ℝ => Real.log (X / Q)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Filter.Tendsto.atTop_div_const hQ_pos tendsto_id)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
      hlog_div_atTop.eventually (eventually_half_self_le_H B),
      eventually_half_log_le_log_X_div_Q hQ_pos] with X hX_one hH_half hlog_half
  have hlogX_pos : 0 < Real.log X := Real.log_pos hX_one
  have hquarter_pos : 0 < (1 / 4 : ℝ) * Real.log X := by positivity
  have hH_ge_quarter :
      (1 / 4 : ℝ) * Real.log X ≤ H B (Real.log (X / Q)) := by
    nlinarith
  have hH_pos : 0 < H B (Real.log (X / Q)) :=
    lt_of_lt_of_le hquarter_pos hH_ge_quarter
  have hnum_nonneg : 0 ≤ lam * (X / Q) ^ 2 := by
    unfold lam
    positivity
  calc
    D.Phi (X / Q) = lam * (X / Q) ^ 2 / H B (Real.log (X / Q)) := by
      rw [D.Phi_eq, PhiFormula]
    _ ≤ lam * (X / Q) ^ 2 / ((1 / 4 : ℝ) * Real.log X) :=
      div_le_div_of_nonneg_left hnum_nonneg hquarter_pos hH_ge_quarter
    _ = C * X ^ 2 / (Q ^ 2 * Real.log X) := by
      have hQ_ne : Q ≠ 0 := ne_of_gt hQ_pos
      have hlog_ne : Real.log X ≠ 0 := ne_of_gt hlogX_pos
      dsimp [C]
      field_simp [hQ_ne, hlog_ne]

/--
The elementary primitive at the lower fixed-`Q` cutoff is
`O(X / (Q log X))`, uniformly in `Q ≥ 2`.
-/
theorem sqrtLogPrimitive_Phi_X_div_Q_bound_uniform (D : PhiPsiData B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : ℝ, (2 : ℝ) ≤ Q →
        ∀ᶠ X : ℝ in Filter.atTop,
          sqrtLogPrimitive (D.Phi (X / Q)) ≤ C * X / (Q * Real.log X) := by
  rcases Phi_X_div_Q_upper_uniform D with ⟨Cphi, hCphi_pos, hPhi_bound⟩
  let C : ℝ := Cphi + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro Q hQ_two
  have hQ_pos : 0 < Q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hQ_two
  filter_upwards [eventually_gt_atTop (1 : ℝ),
      eventually_X_le_Phi_X_div_Q D hQ_pos,
      hPhi_bound Q hQ_two] with X hX_one hXcut hPhi_upper
  let V : ℝ := D.Phi (X / Q)
  have hX_pos : 0 < X := lt_trans zero_lt_one hX_one
  have hX_nonneg : 0 ≤ X := le_of_lt hX_pos
  have hlogX_pos : 0 < Real.log X := Real.log_pos hX_one
  have hlogX_nonneg : 0 ≤ Real.log X := le_of_lt hlogX_pos
  have hV_ge_one : 1 < V := lt_of_lt_of_le hX_one hXcut
  have hV_pos : 0 < V := lt_trans zero_lt_one hV_ge_one
  have hlogV_pos : 0 < Real.log V := Real.log_pos hV_ge_one
  have hlogX_le_logV : Real.log X ≤ Real.log V :=
    Real.log_le_log hX_pos hXcut
  have hV_div_log_le :
      V / Real.log V ≤ Cphi * X ^ 2 / (Q ^ 2 * Real.log X ^ 2) := by
    calc
      V / Real.log V ≤ V / Real.log X :=
        div_le_div_of_nonneg_left (le_of_lt hV_pos) hlogX_pos hlogX_le_logV
      _ ≤ (Cphi * X ^ 2 / (Q ^ 2 * Real.log X)) / Real.log X :=
        div_le_div_of_nonneg_right (by simpa [V] using hPhi_upper) (le_of_lt hlogX_pos)
      _ = Cphi * X ^ 2 / (Q ^ 2 * Real.log X ^ 2) := by
        have hlog_ne : Real.log X ≠ 0 := ne_of_gt hlogX_pos
        field_simp [hlog_ne]
  have harg_nonneg : 0 ≤ V / Real.log V := div_nonneg (le_of_lt hV_pos) (le_of_lt hlogV_pos)
  have hright_nonneg : 0 ≤ C * X / (Q * Real.log X) := by
    positivity
  have hsq :
      (sqrtLogPrimitive V) ^ 2 ≤ (C * X / (Q * Real.log X)) ^ 2 := by
    rw [sqrtLogPrimitive, Real.sq_sqrt harg_nonneg]
    calc
      V / Real.log V ≤ Cphi * X ^ 2 / (Q ^ 2 * Real.log X ^ 2) := hV_div_log_le
      _ ≤ C ^ 2 * X ^ 2 / (Q ^ 2 * Real.log X ^ 2) := by
        have hCphi_le_C_sq : Cphi ≤ C ^ 2 := by
          dsimp [C]
          nlinarith
        have hden_pos : 0 < Q ^ 2 * Real.log X ^ 2 := by positivity
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCphi_le_C_sq (sq_nonneg X)) (le_of_lt hden_pos)
      _ = (C * X / (Q * Real.log X)) ^ 2 := by
        have hQ_ne : Q ≠ 0 := ne_of_gt hQ_pos
        have hlog_ne : Real.log X ≠ 0 := ne_of_gt hlogX_pos
        field_simp [hQ_ne, hlog_ne]
  simpa [V, sqrtLogPrimitive] using
    (sq_le_sq₀ (Real.sqrt_nonneg (V / Real.log V)) hright_nonneg).1 hsq

/-- Uniform fixed-`Q` bound for the `f` integral over the initial tail interval. -/
theorem integral_f_X_to_Phi_X_div_Q_bound_uniform (D : PhiPsiData B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : ℝ, (2 : ℝ) ≤ Q →
        ∀ᶠ X : ℝ in Filter.atTop,
          ∫ t in X..D.Phi (X / Q), D.f t ≤ C * X / (Q * Real.log X) := by
  rcases D.f_upper_bound with ⟨C₀, T₀, hC₀_pos, hbound⟩
  rcases sqrtLogPrimitive_Phi_X_div_Q_bound_uniform D with ⟨Cs, hCs_pos, hsqrt_bound⟩
  let C : ℝ := 4 * C₀ * Cs
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro Q hQ_two
  have hQ_pos : 0 < Q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hQ_two
  filter_upwards [eventually_Phi_X_div_Q_between D (le_trans (by norm_num : (1 : ℝ) ≤ 2) hQ_two),
      eventually_ge_atTop (max T₀ (Real.exp 2)),
      hsqrt_bound Q hQ_two] with X horder hXlarge hsqrt
  rcases horder with ⟨_hbranch, _hTstar, hX_nonneg, hXcut, _hcutPhi⟩
  let V : ℝ := D.Phi (X / Q)
  have hT₀X : T₀ ≤ X := (le_max_left T₀ (Real.exp 2)).trans hXlarge
  have hX_exp : Real.exp 2 ≤ X := (le_max_right T₀ (Real.exp 2)).trans hXlarge
  have hf_int : IntervalIntegrable D.f MeasureTheory.volume X V :=
    D.f_intervalIntegrable X V
  have hmodel_int :
      IntervalIntegrable (fun t : ℝ => C₀ * invSqrtLogModel t)
        MeasureTheory.volume X V := by
    have hcont : ContinuousOn invSqrtLogModel (Set.Icc X V) :=
      invSqrtLogModel_continuousOn_Icc_of_exp_two_le hX_exp
    exact (hcont.intervalIntegrable_of_Icc (by simpa [V] using hXcut)).const_mul C₀
  have hmono :
      ∫ t in X..V, D.f t ≤ ∫ t in X..V, C₀ * invSqrtLogModel t := by
    refine intervalIntegral.integral_mono_on (by simpa [V] using hXcut) hf_int hmodel_int ?_
    intro t ht
    have hT₀t : T₀ ≤ t := hT₀X.trans ht.1
    have hdf := hbound t hT₀t
    simpa [invSqrtLogModel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdf
  have htail := elementary_integral_bound (T := X) (V := V) hX_exp (by simpa [V] using hXcut)
  have hlogX_pos : 0 < Real.log X := by
    have hX_gt_one : 1 < X := by
      have hexp_gt_one : (1 : ℝ) < Real.exp 2 := by
        calc
          (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
          _ < Real.exp 2 := Real.exp_strictMono (by norm_num)
      exact lt_of_lt_of_le hexp_gt_one hX_exp
    exact Real.log_pos hX_gt_one
  calc
    ∫ t in X..D.Phi (X / Q), D.f t = ∫ t in X..V, D.f t := by rfl
    _ ≤ ∫ t in X..V, C₀ * invSqrtLogModel t := hmono
    _ = C₀ * ∫ t in X..V, invSqrtLogModel t := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ C₀ * (4 * sqrtLogPrimitive V) :=
      mul_le_mul_of_nonneg_left htail (le_of_lt hC₀_pos)
    _ = 4 * C₀ * sqrtLogPrimitive V := by ring
    _ ≤ 4 * C₀ * (Cs * X / (Q * Real.log X)) :=
      mul_le_mul_of_nonneg_left (by simpa [V] using hsqrt) (by positivity)
    _ = C * X / (Q * Real.log X) := by
      dsimp [C]
      ring

/-- On the fixed-`Q` main interval, the change-of-variables coordinate stays in `[1,Q]`. -/
theorem qOf_mem_Icc_of_mem_main_interval (D : PhiPsiData B) {Q X t : ℝ}
    (hQ : 0 < Q) (hX : 0 < X)
    (hbranch_left : (D.N0 : ℝ) ≤ X / Q)
    (hbranch_right : (D.N0 : ℝ) ≤ X)
    (ht : t ∈ Set.Icc (D.Phi (X / Q)) (D.Phi X)) :
    qOf D X t ∈ Set.Icc (1 : ℝ) Q := by
  have hTstar_left : D.Tstar ≤ D.Phi (X / Q) :=
    D.Phi_maps_tail (X / Q) hbranch_left
  have hTstar_right : D.Tstar ≤ D.Phi X :=
    D.Phi_maps_tail X hbranch_right
  have hTstar_t : D.Tstar ≤ t := hTstar_left.trans ht.1
  have hpsi_pos : 0 < D.psi t := D.psi_pos_tail t hTstar_t
  have hpsi_lower : X / Q ≤ D.psi t := by
    calc
      X / Q = D.psi (D.Phi (X / Q)) :=
        (D.psi_right_inv (X / Q) hbranch_left).symm
      _ ≤ D.psi t := D.psi_mono_tail hTstar_left hTstar_t ht.1
  have hpsi_upper : D.psi t ≤ X := by
    calc
      D.psi t ≤ D.psi (D.Phi X) := D.psi_mono_tail hTstar_t hTstar_right ht.2
      _ = X := D.psi_right_inv X hbranch_right
  constructor
  · rw [qOf]
    exact (le_div_iff₀ hpsi_pos).2 (by simpa using hpsi_upper)
  · rw [qOf]
    have hQ_ne : Q ≠ 0 := ne_of_gt hQ
    have hX_le_Qpsi : X ≤ Q * D.psi t := by
      calc
        X = Q * (X / Q) := by
          field_simp [hQ_ne]
        _ ≤ Q * D.psi t := mul_le_mul_of_nonneg_left hpsi_lower (le_of_lt hQ)
    exact (div_le_iff₀ hpsi_pos).2 hX_le_Qpsi

/-- Eventually, all `qOf` values on the fixed-`Q` main interval lie in `[1,Q]`. -/
theorem eventually_qOf_mem_Icc_on_main_interval (D : PhiPsiData B) {Q : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ t ∈ Set.Icc (D.Phi (X / Q)) (D.Phi X),
        qOf D X t ∈ Set.Icc (1 : ℝ) Q := by
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_X_div_Q_ge_N0 D hQ_pos,
      eventually_ge_atTop (D.N0 : ℝ)] with X hX_pos hbranch_left hbranch_right t ht
  exact qOf_mem_Icc_of_mem_main_interval D hQ_pos hX_pos hbranch_left hbranch_right ht

theorem f_mul_fract_GX_nonneg_of_le (D : PhiPsiData B) {X t : ℝ}
    (hX : 0 ≤ X) (hXt : X ≤ t) :
    0 ≤ D.f t * fract (GX D X t) := by
  exact mul_nonneg (D.f_nonneg (hX.trans hXt)) (fract_nonneg (GX D X t))

theorem f_mul_fract_GX_le_f_of_le (D : PhiPsiData B) {X t : ℝ}
    (hX : 0 ≤ X) (hXt : X ≤ t) :
    D.f t * fract (GX D X t) ≤ D.f t := by
  have hf_nonneg : 0 ≤ D.f t := D.f_nonneg (hX.trans hXt)
  calc
    D.f t * fract (GX D X t) ≤ D.f t * 1 :=
      mul_le_mul_of_nonneg_left (fract_lt_one (GX D X t)).le hf_nonneg
    _ = D.f t := by ring

/--
Product integrability for the fractional floor-error integrand on an interval lying to the right
of the moving-window length.
-/
theorem f_mul_fract_GX_intervalIntegrable_of_le
    (D : PhiPsiData B) {X a b : ℝ}
    (hX : 0 ≤ X) (hXa : X ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => D.f t * fract (GX D X t))
      MeasureTheory.volume a b := by
  have hmeas :
      Measurable (fun t : ℝ => D.f t * fract (GX D X t)) :=
    D.f_measurable.mul (fract_GX_measurable D X)
  have hsm :
      AEStronglyMeasurable
        (fun t : ℝ => D.f t * fract (GX D X t))
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    hmeas.aestronglyMeasurable
  refine (D.f_intervalIntegrable a b).mono_fun' hsm ?_
  rw [Filter.EventuallyLE]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  refine ae_of_all MeasureTheory.volume ?_
  intro t ht
  rw [Set.uIoc_of_le hab] at ht
  have htX : X ≤ t := hXa.trans ht.1.le
  rw [Real.norm_eq_abs,
    abs_of_nonneg (f_mul_fract_GX_nonneg_of_le D hX htX)]
  exact f_mul_fract_GX_le_f_of_le D hX htX

/-- The floor-error integral is nonnegative on the ordered tail interval. -/
theorem Efloor_nonneg_of_order (D : PhiPsiData B) {X : ℝ}
    (hX : 0 ≤ X) (hXPhi : X ≤ D.Phi X) :
    0 ≤ Efloor D X := by
  unfold Efloor
  exact intervalIntegral.integral_nonneg hXPhi
    (fun t ht => f_mul_fract_GX_nonneg_of_le D hX ht.1)

/-- The fixed-`Q` tail part is nonnegative when its endpoints are ordered. -/
theorem EfloorTail_nonneg_of_order (D : PhiPsiData B) {Q X : ℝ}
    (hX : 0 ≤ X) (hXcut : X ≤ D.Phi (X / Q)) :
    0 ≤ EfloorTail D Q X := by
  unfold EfloorTail
  exact intervalIntegral.integral_nonneg hXcut
    (fun t ht => f_mul_fract_GX_nonneg_of_le D hX ht.1)

/-- The fixed-`Q` main part is nonnegative when its endpoints are ordered. -/
theorem EfloorMain_nonneg_of_order (D : PhiPsiData B) {Q X : ℝ}
    (hX : 0 ≤ X) (hXcut : X ≤ D.Phi (X / Q))
    (hcutPhi : D.Phi (X / Q) ≤ D.Phi X) :
    0 ≤ EfloorMain D Q X := by
  unfold EfloorMain
  exact intervalIntegral.integral_nonneg hcutPhi
    (fun t ht => f_mul_fract_GX_nonneg_of_le D hX (hXcut.trans ht.1))

/-- The fixed-`Q` tail part is bounded above by the corresponding `f` integral. -/
theorem EfloorTail_le_f_integral_of_order (D : PhiPsiData B) {Q X : ℝ}
    (hX : 0 ≤ X) (hXcut : X ≤ D.Phi (X / Q)) :
    EfloorTail D Q X ≤ ∫ t in X..D.Phi (X / Q), D.f t := by
  unfold EfloorTail
  refine intervalIntegral.integral_mono_on hXcut
    (f_mul_fract_GX_intervalIntegrable D hX hXcut)
    (D.f_intervalIntegrable X (D.Phi (X / Q))) ?_
  intro t ht
  exact f_mul_fract_GX_le_f_of_le D hX ht.1

/-- Uniform normalized large-`q` tail bound for the floor-saving error. -/
theorem EfloorTail_bound_uniform_Q (D : PhiPsiData B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : ℝ, (2 : ℝ) ≤ Q →
        ∀ᶠ X : ℝ in Filter.atTop,
          0 ≤ EfloorTail D Q X ∧
          Real.log X * EfloorTail D Q X / (2 * lam * X) ≤ C / Q := by
  rcases integral_f_X_to_Phi_X_div_Q_bound_uniform D with ⟨Cint, hCint_pos, hInt⟩
  have hlam_pos : 0 < 2 * lam := by
    unfold lam
    positivity
  let C : ℝ := Cint / (2 * lam)
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro Q hQ_two
  have hQ_one : (1 : ℝ) ≤ Q := le_trans (by norm_num : (1 : ℝ) ≤ 2) hQ_two
  have hQ_pos : 0 < Q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hQ_two
  filter_upwards [eventually_Phi_X_div_Q_between D hQ_one,
      hInt Q hQ_two, eventually_gt_atTop (1 : ℝ)] with X horder hIntX hX_one
  rcases horder with ⟨_hbranch, _hTstar, hX_nonneg, hXcut, _hcutPhi⟩
  have htail_nonneg : 0 ≤ EfloorTail D Q X :=
    EfloorTail_nonneg_of_order D hX_nonneg hXcut
  have htail_le :
      EfloorTail D Q X ≤ Cint * X / (Q * Real.log X) :=
    (EfloorTail_le_f_integral_of_order D hX_nonneg hXcut).trans hIntX
  constructor
  · exact htail_nonneg
  · have hX_pos : 0 < X := lt_trans zero_lt_one hX_one
    have hlog_pos : 0 < Real.log X := Real.log_pos hX_one
    have hfactor_nonneg : 0 ≤ Real.log X / (2 * lam * X) := by
      exact div_nonneg (le_of_lt hlog_pos)
        (mul_nonneg (le_of_lt hlam_pos) (le_of_lt hX_pos))
    calc
      Real.log X * EfloorTail D Q X / (2 * lam * X) =
          (Real.log X / (2 * lam * X)) * EfloorTail D Q X := by
        ring
      _ ≤ (Real.log X / (2 * lam * X)) *
          (Cint * X / (Q * Real.log X)) :=
        mul_le_mul_of_nonneg_left htail_le hfactor_nonneg
      _ = C / Q := by
        have hQ_ne : Q ≠ 0 := ne_of_gt hQ_pos
        have hX_ne : X ≠ 0 := ne_of_gt hX_pos
        have hlog_ne : Real.log X ≠ 0 := ne_of_gt hlog_pos
        have hlam_ne : 2 * lam ≠ 0 := ne_of_gt hlam_pos
        dsimp [C]
        field_simp [hQ_ne, hX_ne, hlog_ne, hlam_ne]

/-- Exact `GX` split at the fixed-`Q` q-parametrized point. -/
theorem GX_Phi_X_div_q_eq_q_add_correction (D : PhiPsiData B) {X q : ℝ}
    (hX : X ≠ 0) (hq : q ≠ 0) (hbranch : (D.N0 : ℝ) ≤ X / q) :
    GX D X (D.Phi (X / q)) =
      q + ∫ s in (D.Phi (X / q) - X)..D.Phi (X / q),
        (D.f s - D.f (D.Phi (X / q))) := by
  rw [GX_eq_X_mul_f_add_correction, X_mul_f_Phi_X_div_q_eq_q D hX hq hbranch]

/-- Difference form of `GX_Phi_X_div_q_eq_q_add_correction`. -/
theorem GX_Phi_X_div_q_sub_eq_correction (D : PhiPsiData B) {X q : ℝ}
    (hX : X ≠ 0) (hq : q ≠ 0) (hbranch : (D.N0 : ℝ) ≤ X / q) :
    GX D X (D.Phi (X / q)) - q =
      ∫ s in (D.Phi (X / q) - X)..D.Phi (X / q),
        (D.f s - D.f (D.Phi (X / q))) := by
  rw [GX_Phi_X_div_q_eq_q_add_correction D hX hq hbranch]
  ring

/-- Fixed-`Q` uniform estimate for `GX` on the q-parametrized main branch. -/
theorem GX_Phi_X_div_q_uniform_fixed_Q
    (D : PhiPsiData B) {Q : ℝ} (hQ : (1 : ℝ) ≤ Q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℝ in Filter.atTop,
        ∀ q ∈ Set.Icc (1 : ℝ) Q,
          |GX D X (D.Phi (X / q)) - q| ≤ C * Real.log X / X := by
  rcases D.f_local_lipschitz (by norm_num : 0 < (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1) with ⟨CL, TL, hCL_pos, hLip⟩
  let C : ℝ := (2 * CL / lam) * Q ^ 3
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hC_pos : 0 < C := by
    dsimp [C]
    unfold lam
    positivity
  refine ⟨C, hC_pos, ?_⟩
  filter_upwards [eventually_gt_atTop (max 1 TL),
      eventually_X_div_q_ge_N0_on_Icc D hQ,
      eventually_two_mul_X_le_Phi_X_div_q_on_Icc D hQ,
      eventually_Phi_X_div_q_lower_uniform_fixed_Q D hQ] with
    X hXlarge hbranch htwo hlower q hq
  let t : ℝ := D.Phi (X / q)
  have hX_one : 1 < X := lt_of_le_of_lt (le_max_left (1 : ℝ) TL) hXlarge
  have hX_pos : 0 < X := lt_trans zero_lt_one hX_one
  have hX_nonneg : 0 ≤ X := le_of_lt hX_pos
  have hX_ne : X ≠ 0 := ne_of_gt hX_pos
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq.1
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hlogX_pos : 0 < Real.log X := Real.log_pos hX_one
  have ht_two : 2 * X ≤ t := by simpa [t] using htwo q hq
  have hXt : X ≤ t := by nlinarith
  have hTLX : TL < X := lt_of_le_of_lt (le_max_right (1 : ℝ) TL) hXlarge
  have hTLt : TL ≤ t := (le_of_lt hTLX).trans hXt
  have hbranch_q : (D.N0 : ℝ) ≤ X / q := hbranch q hq
  have hcorr := GX_Phi_X_div_q_sub_eq_correction D hX_ne hq_ne hbranch_q
  have hinner_nonneg : 0 ≤ ∫ s in (t - X)..t, (D.f s - D.f t) :=
    Rcorr_inner_nonneg_of_le D hX_nonneg hXt
  have hinner_le :
      ∫ s in (t - X)..t, (D.f s - D.f t) ≤ CL * D.f t / t * X ^ 2 := by
    exact Rcorr_inner_lipschitz_bound D hCL_pos hX_pos hTLt ht_two hLip
  have hf_t : D.f t = q / X := by
    simpa [t] using f_Phi_X_div_q_eq_q_div_X D hX_ne hq_ne hbranch_q
  have ht_lower : (lam / 2) * X ^ 2 / (q ^ 2 * Real.log X) ≤ t := by
    simpa [t] using hlower q hq
  have ht_lower_pos : 0 < (lam / 2) * X ^ 2 / (q ^ 2 * Real.log X) := by
    unfold lam
    positivity
  have hnum_nonneg : 0 ≤ CL * q * X := by positivity
  have hq3_le_Q3 : q ^ 3 ≤ Q ^ 3 := pow_le_pow_left₀ hq_nonneg hq.2 3
  have hfactor_nonneg : 0 ≤ (2 * CL / lam) * Real.log X / X := by
    unfold lam
    positivity
  have habs_eq : |GX D X (D.Phi (X / q)) - q| =
      ∫ s in (t - X)..t, (D.f s - D.f t) := by
    rw [hcorr]
    simpa [t] using abs_of_nonneg hinner_nonneg
  rw [habs_eq]
  calc
    ∫ s in (t - X)..t, (D.f s - D.f t) ≤ CL * D.f t / t * X ^ 2 := hinner_le
    _ = CL * q * X / t := by
      rw [hf_t]
      field_simp [hX_ne]
    _ ≤ CL * q * X / ((lam / 2) * X ^ 2 / (q ^ 2 * Real.log X)) :=
      div_le_div_of_nonneg_left hnum_nonneg ht_lower_pos ht_lower
    _ = (2 * CL / lam) * q ^ 3 * Real.log X / X := by
      have hlam_ne : lam ≠ 0 := by
        unfold lam
        positivity
      field_simp [hlam_ne, hX_ne, hq_ne, ne_of_gt hlogX_pos]
    _ ≤ (2 * CL / lam) * Q ^ 3 * Real.log X / X := by
      calc
        (2 * CL / lam) * q ^ 3 * Real.log X / X =
            q ^ 3 * ((2 * CL / lam) * Real.log X / X) := by ring
        _ ≤ Q ^ 3 * ((2 * CL / lam) * Real.log X / X) :=
            mul_le_mul_of_nonneg_right hq3_le_Q3 hfactor_nonneg
        _ = (2 * CL / lam) * Q ^ 3 * Real.log X / X := by ring
    _ = C * Real.log X / X := by
      dsimp [C]

/-- Pointwise-to-integral bound for replacing the fixed-`Q` q-change Jacobian by `1/q²`. -/
theorem q_change_error_integral_bound {B Q X δ : ℝ} {F : ℝ → ℝ}
    (hQ : (1 : ℝ) ≤ Q) (hδ_nonneg : 0 ≤ δ)
    (hF : ∀ q ∈ Set.Icc (1 : ℝ) Q, |F q| ≤ 1)
    (hW : ∀ q ∈ Set.Icc (1 : ℝ) Q,
      |Real.log X / (2 * lam) * PhiDerivOverR B (X / q) - 1| ≤ δ) :
    |∫ q in (1 : ℝ)..Q,
      (F q * ((Real.log X / (2 * lam) * PhiDerivOverR B (X / q)) / q ^ 2) -
        F q / q ^ 2)| ≤ δ * |Q - 1| := by
  rw [← Real.norm_eq_abs]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 : ℝ)) (b := Q) (C := δ) (by
    intro q hq_uIoc
    have hqIcc : q ∈ Set.Icc (1 : ℝ) Q := by
      rw [Set.uIoc_of_le hQ] at hq_uIoc
      exact ⟨le_of_lt hq_uIoc.1, hq_uIoc.2⟩
    have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hqIcc.1
    have hq_sq_pos : 0 < q ^ 2 := sq_pos_of_ne_zero (ne_of_gt hq_pos)
    let W : ℝ := Real.log X / (2 * lam) * PhiDerivOverR B (X / q)
    have heq :
        F q * ((Real.log X / (2 * lam) * PhiDerivOverR B (X / q)) / q ^ 2) -
            F q / q ^ 2 = F q * (W - 1) * (1 / q ^ 2) := by
      dsimp [W]
      field_simp [ne_of_gt hq_sq_pos]
    have hinv_nonneg : 0 ≤ 1 / q ^ 2 := by positivity
    have hinv_le_one : 1 / q ^ 2 ≤ 1 := by
      rw [div_le_iff₀ hq_sq_pos]
      have hsq_ge_one : (1 : ℝ) ≤ q ^ 2 := by
        have hsq := (sq_le_sq₀ zero_le_one (le_of_lt hq_pos)).2 hqIcc.1
        simpa using hsq
      nlinarith
    have h_abs_inv : |1 / q ^ 2| ≤ 1 := by
      rw [abs_of_nonneg hinv_nonneg]
      exact hinv_le_one
    have hWq : |W - 1| ≤ δ := by
      simpa [W] using hW q hqIcc
    have hmul1 : |F q| * |W - 1| ≤ 1 * δ :=
      mul_le_mul (hF q hqIcc) hWq (abs_nonneg _) zero_le_one
    calc
      ‖F q * ((Real.log X / (2 * lam) * PhiDerivOverR B (X / q)) / q ^ 2) -
          F q / q ^ 2‖ = |F q * (W - 1) * (1 / q ^ 2)| := by
        rw [Real.norm_eq_abs, heq]
      _ = |F q| * |W - 1| * |1 / q ^ 2| := by
        rw [abs_mul, abs_mul]
      _ ≤ 1 * δ * 1 :=
        mul_le_mul hmul1 h_abs_inv (abs_nonneg _) (mul_nonneg zero_le_one hδ_nonneg)
      _ = δ := by ring)

/-- Eventual fixed-`Q` q-change Jacobian replacement for any bounded test function. -/
theorem eventually_q_change_uniform_fixed_Q_core {B Q ε : ℝ} {F : ℝ → ℝ}
    (hQ : (1 : ℝ) ≤ Q) (hε : 0 < ε)
    (hF : ∀ q ∈ Set.Icc (1 : ℝ) Q, |F q| ≤ 1) :
    ∀ᶠ X : ℝ in Filter.atTop,
      |∫ q in (1 : ℝ)..Q,
        (F q * ((Real.log X / (2 * lam) * PhiDerivOverR B (X / q)) / q ^ 2) -
          F q / q ^ 2)| ≤ ε := by
  let δ : ℝ := ε / (|Q - 1| + 1)
  have hden_pos : 0 < |Q - 1| + 1 := by positivity
  have hδ_pos : 0 < δ := div_pos hε hden_pos
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  filter_upwards [eventually_jacobian_weight_uniform_fixed_Q (B := B) (Q := Q) hQ hδ_pos] with
    X hW
  calc
    |∫ q in (1 : ℝ)..Q,
        (F q * ((Real.log X / (2 * lam) * PhiDerivOverR B (X / q)) / q ^ 2) -
          F q / q ^ 2)| ≤ δ * |Q - 1| :=
      q_change_error_integral_bound hQ hδ_nonneg hF hW
    _ ≤ ε := by
      dsimp [δ]
      calc
        ε / (|Q - 1| + 1) * |Q - 1| ≤
            ε / (|Q - 1| + 1) * (|Q - 1| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (Q - 1)]) (by positivity)
        _ = ε := by
          field_simp [ne_of_gt hden_pos]

/-- Measurability of the raw q-side floor-saving fractional term. -/
theorem q_fract_GX_Phi_raw_measurable (D : PhiPsiData B) (X : ℝ) :
    Measurable (fun q : ℝ => fract (GX D X (D.Phi (X / q)))) := by
  have hPhi_comp : Measurable (fun q : ℝ => D.Phi (X / q)) :=
    D.Phi_measurable.comp (by fun_prop)
  have hGX : Measurable (fun q : ℝ => GX D X (D.Phi (X / q))) :=
    (GX_measurable_in_t D X).comp hPhi_comp
  exact fract_measurable.comp hGX

/-- Measurability of the q-side floor-saving fractional integrand. -/
theorem q_fract_GX_Phi_measurable (D : PhiPsiData B) (X : ℝ) :
    Measurable (fun q : ℝ => fract (GX D X (D.Phi (X / q))) / q ^ 2) := by
  exact (q_fract_GX_Phi_raw_measurable D X).div (by fun_prop)

/-- The q-side fractional integrand is interval-integrable on every fixed `[1,Q]`. -/
theorem q_fract_GX_Phi_intervalIntegrable (D : PhiPsiData B) {X Q : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    IntervalIntegrable
      (fun q : ℝ => fract (GX D X (D.Phi (X / q))) / q ^ 2)
      MeasureTheory.volume 1 Q := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hQ]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := (1 : ℝ)) measure_Ioc_lt_top.ne
    (q_fract_GX_Phi_measurable D X).aestronglyMeasurable ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  refine ae_of_all MeasureTheory.volume ?_
  intro q hq
  have hq_pos : 0 < q := lt_trans zero_lt_one hq.1
  have hden_pos : 0 < q ^ 2 := sq_pos_of_ne_zero (ne_of_gt hq_pos)
  have hfract_nonneg : 0 ≤ fract (GX D X (D.Phi (X / q))) := fract_nonneg _
  have hfract_le_one : fract (GX D X (D.Phi (X / q))) ≤ 1 := (fract_lt_one _).le
  have hdiv_nonneg : 0 ≤ fract (GX D X (D.Phi (X / q))) / q ^ 2 :=
    div_nonneg hfract_nonneg (le_of_lt hden_pos)
  rw [Real.norm_eq_abs, abs_of_nonneg hdiv_nonneg]
  calc
    fract (GX D X (D.Phi (X / q))) / q ^ 2 ≤ 1 / q ^ 2 :=
      div_le_div_of_nonneg_right hfract_le_one (le_of_lt hden_pos)
    _ ≤ 1 := by
      rw [div_le_iff₀ hden_pos]
      have hsq_ge_one : (1 : ℝ) ≤ q ^ 2 := by
        have hsq := (sq_le_sq₀ zero_le_one (le_of_lt hq_pos)).2 (le_of_lt hq.1)
        simpa using hsq
      nlinarith

/-- The model q-side fractional integrand is interval-integrable on every fixed `[1,Q]`. -/
theorem q_fract_intervalIntegrable {Q : ℝ} (hQ : (1 : ℝ) ≤ Q) :
    IntervalIntegrable (fun q : ℝ => fract q / q ^ 2) MeasureTheory.volume 1 Q := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hQ]
  have hmeas : Measurable (fun q : ℝ => fract q / q ^ 2) :=
    fract_measurable.div (by fun_prop)
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := (1 : ℝ)) measure_Ioc_lt_top.ne
    hmeas.aestronglyMeasurable ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  refine ae_of_all MeasureTheory.volume ?_
  intro q hq
  have hq_pos : 0 < q := lt_trans zero_lt_one hq.1
  have hden_pos : 0 < q ^ 2 := sq_pos_of_ne_zero (ne_of_gt hq_pos)
  have hfract_nonneg : 0 ≤ fract q := fract_nonneg _
  have hfract_le_one : fract q ≤ 1 := (fract_lt_one _).le
  have hdiv_nonneg : 0 ≤ fract q / q ^ 2 := div_nonneg hfract_nonneg (le_of_lt hden_pos)
  rw [Real.norm_eq_abs, abs_of_nonneg hdiv_nonneg]
  calc
    fract q / q ^ 2 ≤ 1 / q ^ 2 :=
      div_le_div_of_nonneg_right hfract_le_one (le_of_lt hden_pos)
    _ ≤ 1 := by
      rw [div_le_iff₀ hden_pos]
      have hsq_ge_one : (1 : ℝ) ≤ q ^ 2 := by
        have hsq := (sq_le_sq₀ zero_le_one (le_of_lt hq_pos)).2 (le_of_lt hq.1)
        simpa using hsq
      nlinarith

/-- A coarse pointwise bound for the difference of two q-side fractional integrands. -/
theorem fract_integrand_diff_le_two (D : PhiPsiData B) {X q : ℝ} (hq : (1 : ℝ) < q) :
    |fract (GX D X (D.Phi (X / q))) / q ^ 2 - fract q / q ^ 2| ≤ 2 := by
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hden_pos : 0 < q ^ 2 := sq_pos_of_ne_zero (ne_of_gt hq_pos)
  have hden_nonneg : 0 ≤ q ^ 2 := le_of_lt hden_pos
  have hsq_ge_one : (1 : ℝ) ≤ q ^ 2 := by
    have hsq := (sq_le_sq₀ zero_le_one (le_of_lt hq_pos)).2 (le_of_lt hq)
    simpa using hsq
  have hinv_le_one : 1 / q ^ 2 ≤ 1 := by
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have hterm_le (z : ℝ) : |fract z / q ^ 2| ≤ 1 := by
    have hfract_nonneg : 0 ≤ fract z := fract_nonneg _
    have hfract_le_one : fract z ≤ 1 := (fract_lt_one _).le
    have hdiv_nonneg : 0 ≤ fract z / q ^ 2 := div_nonneg hfract_nonneg hden_nonneg
    rw [abs_of_nonneg hdiv_nonneg]
    calc
      fract z / q ^ 2 ≤ 1 / q ^ 2 := div_le_div_of_nonneg_right hfract_le_one hden_nonneg
      _ ≤ 1 := hinv_le_one
  calc
    |fract (GX D X (D.Phi (X / q))) / q ^ 2 - fract q / q ^ 2|
        ≤ |fract (GX D X (D.Phi (X / q))) / q ^ 2| + |fract q / q ^ 2| :=
      abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (hterm_le _) (hterm_le q)
    _ = 2 := by norm_num

/-- The good part of the q interval has measure at most the interval length. -/
theorem volume_Ioc_inter_intGoodSet_toReal_le {Q η : ℝ} (hQ : (1 : ℝ) ≤ Q) :
    (MeasureTheory.volume (Set.Ioc (1 : ℝ) Q ∩ intGoodSet Q η)).toReal ≤ |Q - 1| := by
  have hsubset : Set.Ioc (1 : ℝ) Q ∩ intGoodSet Q η ⊆ Set.Ioc (1 : ℝ) Q := by
    intro q hq
    exact hq.1
  have hIoc_ne_top : MeasureTheory.volume (Set.Ioc (1 : ℝ) Q) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  calc
    (MeasureTheory.volume (Set.Ioc (1 : ℝ) Q ∩ intGoodSet Q η)).toReal ≤
        (MeasureTheory.volume (Set.Ioc (1 : ℝ) Q)).toReal :=
      ENNReal.toReal_mono hIoc_ne_top (MeasureTheory.measure_mono hsubset)
    _ = Q - 1 := by
      rw [Real.volume_Ioc, ENNReal.toReal_ofReal]
      exact sub_nonneg.mpr hQ
    _ ≤ |Q - 1| := le_abs_self _

/-- The bad part of the q interval has measure controlled by the integer-window total length. -/
theorem volume_Ioc_inter_intBadSet_toReal_le {Q η : ℝ} (hη : 0 ≤ η) :
    (MeasureTheory.volume (Set.Ioc (1 : ℝ) Q ∩ intBadSet Q η)).toReal ≤
      ((integerWindowIndex Q).card : ℝ) * (2 * η) := by
  have hsubset : Set.Ioc (1 : ℝ) Q ∩ intBadSet Q η ⊆
      ⋃ m ∈ integerWindowIndex Q, integerWindow η m := by
    intro q hq
    rcases (mem_intBadSet (Q := Q) (η := η) (q := q)).mp hq.2 with ⟨_, m, hm, hwin⟩
    exact Set.mem_iUnion₂.mpr ⟨m, hm, hwin⟩
  have hmeasure_le :
      MeasureTheory.volume (Set.Ioc (1 : ℝ) Q ∩ intBadSet Q η) ≤
        MeasureTheory.volume (⋃ m ∈ integerWindowIndex Q, integerWindow η m) :=
    MeasureTheory.measure_mono hsubset
  have hUnion_le :
      MeasureTheory.volume (⋃ m ∈ integerWindowIndex Q, integerWindow η m) ≤
        ∑ m ∈ integerWindowIndex Q, MeasureTheory.volume (integerWindow η m) :=
    MeasureTheory.measure_biUnion_finset_le (μ := MeasureTheory.volume)
      (integerWindowIndex Q) (fun m => integerWindow η m)
  have hsum_ne_top :
      (∑ m ∈ integerWindowIndex Q, MeasureTheory.volume (integerWindow η m)) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro m hm
    rw [integerWindow, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  calc
    (MeasureTheory.volume (Set.Ioc (1 : ℝ) Q ∩ intBadSet Q η)).toReal ≤
        (∑ m ∈ integerWindowIndex Q, MeasureTheory.volume (integerWindow η m)).toReal :=
      ENNReal.toReal_mono hsum_ne_top (hmeasure_le.trans hUnion_le)
    _ = ∑ m ∈ integerWindowIndex Q, (MeasureTheory.volume (integerWindow η m)).toReal := by
      exact ENNReal.toReal_sum (fun m hm => by
        rw [integerWindow, Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top)
    _ = ∑ m ∈ integerWindowIndex Q, 2 * η := by
      refine Finset.sum_congr rfl ?_
      intro m hm
      rw [integerWindow, Real.volume_Ioo]
      have hnonneg : 0 ≤ ((m : ℝ) + η) - ((m : ℝ) - η) := by linarith
      rw [ENNReal.toReal_ofReal hnonneg]
      ring
    _ = ((integerWindowIndex Q).card : ℝ) * (2 * η) := by
      simp

/-- The good and bad parts partition the q interval. -/
theorem Ioc_inter_intGood_union_intBad (Q η : ℝ) :
    (Set.Ioc (1 : ℝ) Q ∩ intGoodSet Q η) ∪
        (Set.Ioc (1 : ℝ) Q ∩ intBadSet Q η) = Set.Ioc (1 : ℝ) Q := by
  ext q
  constructor
  · intro h
    rcases h with h | h <;> exact h.1
  · intro hIoc
    have hIcc : q ∈ Set.Icc (1 : ℝ) Q := ⟨le_of_lt hIoc.1, hIoc.2⟩
    have hmem : q ∈ intGoodSet Q η ∪ intBadSet Q η := by
      rw [intGoodSet_union_intBadSet]
      exact hIcc
    rcases hmem with hgood | hbad
    · exact Or.inl ⟨hIoc, hgood⟩
    · exact Or.inr ⟨hIoc, hbad⟩

/--
If `GX(D.Phi(X/q))` is uniformly `η`-close to `q`, then the q-side fractional
integral is close to its fixed model integral.
-/
theorem fract_integral_close_fixed_Q_of_uniform_close (D : PhiPsiData B) {Q η X : ℝ}
    (hQ : (1 : ℝ) ≤ Q) (hη : 0 < η)
    (hGX : ∀ q ∈ Set.Icc (1 : ℝ) Q, |GX D X (D.Phi (X / q)) - q| < η) :
    |(∫ q in (1 : ℝ)..Q,
        fract (GX D X (D.Phi (X / q))) / q ^ 2) - IfractQ Q| ≤
      η * |Q - 1| + 2 * (((integerWindowIndex Q).card : ℝ) * (2 * η)) := by
  let fX : ℝ → ℝ := fun q => fract (GX D X (D.Phi (X / q))) / q ^ 2
  let f0 : ℝ → ℝ := fun q => fract q / q ^ 2
  let diff : ℝ → ℝ := fun q => fX q - f0 q
  let good : Set ℝ := Set.Ioc (1 : ℝ) Q ∩ intGoodSet Q η
  let bad : Set ℝ := Set.Ioc (1 : ℝ) Q ∩ intBadSet Q η
  have hη_nonneg : 0 ≤ η := le_of_lt hη
  have hfX_int : IntervalIntegrable fX MeasureTheory.volume 1 Q := by
    simpa [fX] using q_fract_GX_Phi_intervalIntegrable D (X := X) hQ
  have hf0_int : IntervalIntegrable f0 MeasureTheory.volume 1 Q := by
    simpa [f0] using q_fract_intervalIntegrable (Q := Q) hQ
  have hdiff_int : IntervalIntegrable diff MeasureTheory.volume 1 Q := by
    simpa [diff] using hfX_int.sub hf0_int
  have hdiff_Ioc : IntegrableOn diff (Set.Ioc (1 : ℝ) Q) MeasureTheory.volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hQ).mp hdiff_int
  have hgood_subset_Ioc : good ⊆ Set.Ioc (1 : ℝ) Q := by intro q hq; exact hq.1
  have hbad_subset_Ioc : bad ⊆ Set.Ioc (1 : ℝ) Q := by intro q hq; exact hq.1
  have hgood_int : IntegrableOn diff good MeasureTheory.volume :=
    hdiff_Ioc.mono_set hgood_subset_Ioc
  have hbad_int : IntegrableOn diff bad MeasureTheory.volume :=
    hdiff_Ioc.mono_set hbad_subset_Ioc
  have hbad_meas : MeasurableSet bad := measurableSet_Ioc.inter measurableSet_intBadSet
  have hgood_finite : MeasureTheory.volume good < ⊤ :=
    (MeasureTheory.measure_mono hgood_subset_Ioc).trans_lt measure_Ioc_lt_top
  have hbad_finite : MeasureTheory.volume bad < ⊤ :=
    (MeasureTheory.measure_mono hbad_subset_Ioc).trans_lt measure_Ioc_lt_top
  have hdisj : Disjoint good bad := by
    exact Disjoint.mono (by intro q hq; exact hq.2) (by intro q hq; exact hq.2)
      (disjoint_intGoodSet_intBadSet Q η)
  have hunion : good ∪ bad = Set.Ioc (1 : ℝ) Q := by
    simpa [good, bad] using Ioc_inter_intGood_union_intBad Q η
  have hsplit :
      ∫ q in (1 : ℝ)..Q, diff q =
        (∫ q in good, diff q) + (∫ q in bad, diff q) := by
    rw [intervalIntegral.integral_of_le hQ]
    rw [← hunion]
    simpa using MeasureTheory.setIntegral_union hdisj hbad_meas hgood_int hbad_int
  have hgood_measure_le : MeasureTheory.volume.real good ≤ |Q - 1| := by
    simpa [good, MeasureTheory.Measure.real] using
      volume_Ioc_inter_intGoodSet_toReal_le (Q := Q) (η := η) hQ
  have hbad_measure_le : MeasureTheory.volume.real bad ≤
      ((integerWindowIndex Q).card : ℝ) * (2 * η) := by
    simpa [bad, MeasureTheory.Measure.real] using
      volume_Ioc_inter_intBadSet_toReal_le (Q := Q) (η := η) hη_nonneg
  have hgood_bound : ‖∫ q in good, diff q‖ ≤ η * |Q - 1| := by
    calc
      ‖∫ q in good, diff q‖ ≤ η * MeasureTheory.volume.real good := by
        refine MeasureTheory.norm_setIntegral_le_of_norm_le_const hgood_finite ?_
        intro q hq
        rw [Real.norm_eq_abs]
        dsimp [diff, fX, f0]
        exact fract_integrand_close_on_good D hη hq.2 (hGX q ((mem_intGoodSet.mp hq.2).1))
      _ ≤ η * |Q - 1| :=
        mul_le_mul_of_nonneg_left hgood_measure_le hη_nonneg
  have hbad_bound : ‖∫ q in bad, diff q‖ ≤
      2 * (((integerWindowIndex Q).card : ℝ) * (2 * η)) := by
    calc
      ‖∫ q in bad, diff q‖ ≤ 2 * MeasureTheory.volume.real bad := by
        refine MeasureTheory.norm_setIntegral_le_of_norm_le_const hbad_finite ?_
        intro q hq
        rw [Real.norm_eq_abs]
        dsimp [diff, fX, f0]
        exact fract_integrand_diff_le_two D hq.1.1
      _ ≤ 2 * (((integerWindowIndex Q).card : ℝ) * (2 * η)) :=
        mul_le_mul_of_nonneg_left hbad_measure_le (by norm_num)
  unfold IfractQ
  change |(∫ q in (1 : ℝ)..Q, fX q) - ∫ q in (1 : ℝ)..Q, f0 q| ≤
    η * |Q - 1| + 2 * (((integerWindowIndex Q).card : ℝ) * (2 * η))
  rw [← intervalIntegral.integral_sub hfX_int hf0_int]
  change |∫ q in (1 : ℝ)..Q, diff q| ≤
    η * |Q - 1| + 2 * (((integerWindowIndex Q).card : ℝ) * (2 * η))
  rw [← Real.norm_eq_abs]
  rw [hsplit]
  calc
    ‖(∫ q in good, diff q) + (∫ q in bad, diff q)‖ ≤
        ‖∫ q in good, diff q‖ + ‖∫ q in bad, diff q‖ := norm_add_le _ _
    _ ≤ η * |Q - 1| + 2 * (((integerWindowIndex Q).card : ℝ) * (2 * η)) :=
      add_le_add hgood_bound hbad_bound

/-- Eventual fixed-`Q` closeness of the q-parametrized `GX` branch. -/
theorem eventually_GX_Phi_X_div_q_close_fixed_Q (D : PhiPsiData B) {Q η : ℝ}
    (hQ : (1 : ℝ) ≤ Q) (hη : 0 < η) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ q ∈ Set.Icc (1 : ℝ) Q, |GX D X (D.Phi (X / q)) - q| < η := by
  obtain ⟨C, _, hGX_ev⟩ := GX_Phi_X_div_q_uniform_fixed_Q D hQ
  have hsmall_ev : ∀ᶠ X : ℝ in Filter.atTop, C * Real.log X / X < η := by
    have htend : Tendsto (fun X : ℝ => C * Real.log X / X) Filter.atTop (𝓝 0) := by
      have h := Real.isLittleO_log_id_atTop.const_mul_left C
      simpa [div_eq_mul_inv, mul_assoc] using h.tendsto_div_nhds_zero
    have hmetric := (Metric.tendsto_nhds.mp htend) η hη
    filter_upwards [hmetric] with X hX
    rw [Real.dist_eq] at hX
    have habs_lt : |C * Real.log X / X| < η := by
      simpa [sub_eq_add_neg] using hX
    exact lt_of_le_of_lt (le_abs_self _) habs_lt
  filter_upwards [hGX_ev, hsmall_ev] with X hGX_bound hsmall q hq
  exact lt_of_le_of_lt (hGX_bound q hq) hsmall

/-- Fixed-`Q` convergence of the q-side fractional-part model. -/
theorem fract_integral_convergence_fixed_Q (D : PhiPsiData B) {Q : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    Tendsto
      (fun X : ℝ =>
        ∫ q in (1 : ℝ)..Q,
          fract (GX D X (D.Phi (X / q))) / q ^ 2)
      Filter.atTop
      (𝓝 (IfractQ Q)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let K : ℝ := |Q - 1| + 4 * ((integerWindowIndex Q).card : ℝ)
  have hK_pos : 0 < K + 1 := by
    dsimp [K]
    positivity
  let η : ℝ := ε / (K + 1)
  have hη_pos : 0 < η := div_pos hε hK_pos
  filter_upwards [eventually_GX_Phi_X_div_q_close_fixed_Q D hQ hη_pos] with X hGX
  rw [Real.dist_eq]
  have hclose := fract_integral_close_fixed_Q_of_uniform_close D hQ hη_pos hGX
  calc
    |(∫ q in (1 : ℝ)..Q,
          fract (GX D X (D.Phi (X / q))) / q ^ 2) - IfractQ Q| ≤
        η * |Q - 1| + 2 * (((integerWindowIndex Q).card : ℝ) * (2 * η)) := hclose
    _ = η * K := by
      dsimp [K]
      ring
    _ < η * (K + 1) := by
      exact mul_lt_mul_of_pos_left (by linarith) hη_pos
    _ = ε := by
      dsimp [η]
      field_simp [ne_of_gt hK_pos]

/--
A bounded fixed-`Q` Jacobian weight makes the dynamic weighted q-side fractional
integrand interval-integrable.
-/
theorem q_fract_GX_Phi_weight_intervalIntegrable_of_jacobian_bound
    (D : PhiPsiData B) {Q X δ : ℝ} (hQ : (1 : ℝ) ≤ Q) (hδ_nonneg : 0 ≤ δ)
    (hW : ∀ q ∈ Set.Icc (1 : ℝ) Q,
      |Real.log X / (2 * lam) * PhiDerivOverR B (X / q) - 1| ≤ δ) :
    IntervalIntegrable
      (fun q : ℝ =>
        fract (GX D X (D.Phi (X / q))) *
          ((Real.log X / (2 * lam) * PhiDerivOverR B (X / q)) / q ^ 2))
      MeasureTheory.volume 1 Q := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hQ]
  have hweight_meas : Measurable (fun q : ℝ =>
      (Real.log X / (2 * lam) * PhiDerivOverR B (X / q)) / q ^ 2) := by
    have hderiv : Measurable (fun q : ℝ => PhiDerivOverR B (X / q)) :=
      (PhiDerivOverR_measurable B).comp (by fun_prop)
    exact ((measurable_const.mul hderiv).div (by fun_prop))
  have hmeas : Measurable (fun q : ℝ =>
      fract (GX D X (D.Phi (X / q))) *
        ((Real.log X / (2 * lam) * PhiDerivOverR B (X / q)) / q ^ 2)) :=
    (q_fract_GX_Phi_raw_measurable D X).mul hweight_meas
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := δ + 1) measure_Ioc_lt_top.ne
    hmeas.aestronglyMeasurable ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  refine ae_of_all MeasureTheory.volume ?_
  intro q hq
  have hqIcc : q ∈ Set.Icc (1 : ℝ) Q := ⟨le_of_lt hq.1, hq.2⟩
  have hq_pos : 0 < q := lt_trans zero_lt_one hq.1
  have hq_sq_pos : 0 < q ^ 2 := sq_pos_of_ne_zero (ne_of_gt hq_pos)
  let W : ℝ := Real.log X / (2 * lam) * PhiDerivOverR B (X / q)
  have hWq : |W - 1| ≤ δ := by simpa [W] using hW q hqIcc
  have hW_abs : |W| ≤ δ + 1 := by
    calc
      |W| = |(W - 1) + 1| := by ring_nf
      _ ≤ |W - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ δ + 1 := by
        have hone : |(1 : ℝ)| = 1 := by norm_num
        rw [hone]
        linarith
  have hfract_abs : |fract (GX D X (D.Phi (X / q)))| ≤ 1 := by
    have hnonneg : 0 ≤ fract (GX D X (D.Phi (X / q))) := fract_nonneg _
    rw [abs_of_nonneg hnonneg]
    exact (fract_lt_one _).le
  have hinv_nonneg : 0 ≤ 1 / q ^ 2 := by positivity
  have hinv_le_one : 1 / q ^ 2 ≤ 1 := by
    rw [div_le_iff₀ hq_sq_pos]
    have hsq_ge_one : (1 : ℝ) ≤ q ^ 2 := by
      have hsq := (sq_le_sq₀ zero_le_one (le_of_lt hq_pos)).2 (le_of_lt hq.1)
      simpa using hsq
    nlinarith
  have hinv_abs : |1 / q ^ 2| ≤ 1 := by
    rw [abs_of_nonneg hinv_nonneg]
    exact hinv_le_one
  have hδ1_nonneg : 0 ≤ δ + 1 := by positivity
  calc
    ‖fract (GX D X (D.Phi (X / q))) *
        ((Real.log X / (2 * lam) * PhiDerivOverR B (X / q)) / q ^ 2)‖
        = |fract (GX D X (D.Phi (X / q))) * (W * (1 / q ^ 2))| := by
          rw [Real.norm_eq_abs]
          congr 1
          dsimp [W]
          field_simp [ne_of_gt hq_sq_pos]
    _ = |fract (GX D X (D.Phi (X / q)))| * |W| * |1 / q ^ 2| := by
      rw [abs_mul, abs_mul, mul_assoc]
    _ ≤ 1 * (δ + 1) * 1 :=
      mul_le_mul (mul_le_mul hfract_abs hW_abs (abs_nonneg _) zero_le_one) hinv_abs
        (abs_nonneg _) (mul_nonneg zero_le_one hδ1_nonneg)
    _ = δ + 1 := by ring

/--
Exact fixed-`Q` q-change for the main floor-saving integral, assuming the
q-parametrized branch is differentiable and decreasing on `[1,Q]`.
-/
theorem q_change_exact_fixed_Q_of_deriv_nonpos (D : PhiPsiData B) {Q X : ℝ}
    (hQ : (1 : ℝ) ≤ Q) (hX : X ≠ 0)
    (hcont : ContinuousOn (fun q : ℝ => D.Phi (X / q)) (Set.uIcc (1 : ℝ) Q))
    (hderiv : ∀ q ∈ Set.Ioo (min (1 : ℝ) Q) (max (1 : ℝ) Q),
      HasDerivAt (fun u : ℝ => D.Phi (X / u))
        (PhiDerivFormula B (X / q) * (-X / q ^ 2)) q)
    (hnonpos : ∀ q ∈ Set.Ioo (min (1 : ℝ) Q) (max (1 : ℝ) Q),
      PhiDerivFormula B (X / q) * (-X / q ^ 2) ≤ 0)
    (hbranch : ∀ q ∈ Set.Icc (1 : ℝ) Q, (D.N0 : ℝ) ≤ X / q) :
    EfloorMain D Q X =
      ∫ q in (1 : ℝ)..Q,
        fract (GX D X (D.Phi (X / q))) *
          (X / q ^ 2 * PhiDerivOverR B (X / q)) := by
  let g : ℝ → ℝ := fun t => D.f t * fract (GX D X t)
  let tau : ℝ → ℝ := fun q => D.Phi (X / q)
  let tau' : ℝ → ℝ := fun q => PhiDerivFormula B (X / q) * (-X / q ^ 2)
  have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := (1 : ℝ)) (b := Q) (f := tau) (f' := tau') (g := g)
    hcont hderiv hnonpos
  have hsubst' :
      ∫ q in (1 : ℝ)..Q, (g ∘ tau) q * tau' q =
        ∫ u in D.Phi X..D.Phi (X / Q), g u := by
    simpa [g, tau, tau', Function.comp_def] using hsubst
  unfold EfloorMain
  change ∫ t in D.Phi (X / Q)..D.Phi X, g t =
    ∫ q in (1 : ℝ)..Q,
      fract (GX D X (D.Phi (X / q))) *
        (X / q ^ 2 * PhiDerivOverR B (X / q))
  calc
    ∫ t in D.Phi (X / Q)..D.Phi X, g t
        = - ∫ t in D.Phi X..D.Phi (X / Q), g t := by
          rw [intervalIntegral.integral_symm]
    _ = - ∫ q in (1 : ℝ)..Q, (g ∘ tau) q * tau' q := by
          rw [hsubst']
    _ = ∫ q in (1 : ℝ)..Q, -((g ∘ tau) q * tau' q) := by
          rw [intervalIntegral.integral_neg]
    _ = ∫ q in (1 : ℝ)..Q,
          fract (GX D X (D.Phi (X / q))) *
            (X / q ^ 2 * PhiDerivOverR B (X / q)) := by
          refine intervalIntegral.integral_congr ?_
          intro q hq
          have hqI : q ∈ Set.Icc (1 : ℝ) Q := by
            simpa [Set.uIcc_of_le hQ] using hq
          have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hqI.1
          have hq_ne : q ≠ 0 := ne_of_gt hq_pos
          have hXq_ne : X / q ≠ 0 := div_ne_zero hX hq_ne
          have hf := f_Phi_X_div_q_eq_q_div_X D hX hq_ne (hbranch q hqI)
          dsimp [g, tau, tau', Function.comp_def]
          rw [hf]
          rw [PhiDerivOverR]
          field_simp [hX, hq_ne, hXq_ne]

/-- Eventual exact fixed-`Q` q-change for the main floor-saving integral. -/
theorem eventually_q_change_exact_fixed_Q (D : PhiPsiData B) {Q : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    ∀ᶠ X : ℝ in Filter.atTop,
      EfloorMain D Q X =
        ∫ q in (1 : ℝ)..Q,
          fract (GX D X (D.Phi (X / q))) *
            (X / q ^ 2 * PhiDerivOverR B (X / q)) := by
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  filter_upwards [eventually_Phi_comp_X_div_continuousOn D hQ,
      eventually_Phi_hasDerivAt_X_div_q_on_Icc D hQ_pos,
      eventually_PhiDerivFormula_nonneg_X_div_q_on_Icc (B := B) hQ,
      eventually_X_div_q_ge_N0_on_Icc D hQ,
      eventually_gt_atTop (0 : ℝ)] with X hcont hPhiDer hPhiDer_nonneg hbranch hX_pos
  have hX_ne : X ≠ 0 := ne_of_gt hX_pos
  refine q_change_exact_fixed_Q_of_deriv_nonpos D hQ hX_ne hcont ?_ ?_ hbranch
  · intro q hq
    have hqI : q ∈ Set.Icc (1 : ℝ) Q := by
      rw [min_eq_left hQ, max_eq_right hQ] at hq
      exact ⟨le_of_lt hq.1, le_of_lt hq.2⟩
    have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hqI.1
    exact (hPhiDer q hqI).comp q (hasDerivAt_X_div X q (ne_of_gt hq_pos))
  · intro q hq
    have hqI : q ∈ Set.Icc (1 : ℝ) Q := by
      rw [min_eq_left hQ, max_eq_right hQ] at hq
      exact ⟨le_of_lt hq.1, le_of_lt hq.2⟩
    have hfactor_nonpos : -X / q ^ 2 ≤ 0 := by
      have hden_nonneg : 0 ≤ q ^ 2 := sq_nonneg q
      have hneg_nonpos : -X ≤ 0 := by linarith
      exact div_nonpos_of_nonpos_of_nonneg hneg_nonpos hden_nonneg
    exact mul_nonpos_of_nonneg_of_nonpos (hPhiDer_nonneg q hqI) hfactor_nonpos

/-- Eventual fixed-`Q` normalized q-change for the main floor-saving integral. -/
theorem eventually_q_change_uniform_fixed_Q (D : PhiPsiData B) {Q ε : ℝ}
    (hQ : (1 : ℝ) ≤ Q) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      |(Real.log X / (2 * lam * X)) * EfloorMain D Q X -
        ∫ q in (1 : ℝ)..Q,
          fract (GX D X (D.Phi (X / q))) / q ^ 2| ≤ ε := by
  let δ : ℝ := ε / (|Q - 1| + 1)
  have hden_pos : 0 < |Q - 1| + 1 := by positivity
  have hδ_pos : 0 < δ := div_pos hε hden_pos
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  filter_upwards [eventually_q_change_exact_fixed_Q D hQ,
      eventually_jacobian_weight_uniform_fixed_Q (B := B) (Q := Q) hQ hδ_pos,
      eventually_gt_atTop (1 : ℝ)] with X hExact hW hX_gt
  let F : ℝ → ℝ := fun q : ℝ => fract (GX D X (D.Phi (X / q)))
  let W : ℝ → ℝ := fun q : ℝ => Real.log X / (2 * lam) * PhiDerivOverR B (X / q)
  have hX_pos : 0 < X := lt_trans zero_lt_one hX_gt
  have hX_ne : X ≠ 0 := ne_of_gt hX_pos
  have hlam_ne : lam ≠ 0 := by
    unfold lam
    positivity
  have hF : ∀ q ∈ Set.Icc (1 : ℝ) Q, |F q| ≤ 1 := by
    intro q hq
    have hnonneg : 0 ≤ F q := by
      dsimp [F]
      exact fract_nonneg _
    rw [abs_of_nonneg hnonneg]
    dsimp [F]
    exact (fract_lt_one _).le
  have hweighted_int : IntervalIntegrable
      (fun q : ℝ => F q * (W q / q ^ 2)) MeasureTheory.volume 1 Q := by
    simpa [F, W] using
      (q_fract_GX_Phi_weight_intervalIntegrable_of_jacobian_bound D hQ hδ_nonneg hW)
  have hmodel_int : IntervalIntegrable
      (fun q : ℝ => F q / q ^ 2) MeasureTheory.volume 1 Q := by
    simpa [F] using q_fract_GX_Phi_intervalIntegrable D (X := X) hQ
  have hweighted_eq :
      (Real.log X / (2 * lam * X)) * EfloorMain D Q X =
        ∫ q in (1 : ℝ)..Q, F q * (W q / q ^ 2) := by
    rw [hExact]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro q hq
    have hqIcc : q ∈ Set.Icc (1 : ℝ) Q := by
      simpa [Set.uIcc_of_le hQ] using hq
    have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hqIcc.1
    have hq_ne : q ≠ 0 := ne_of_gt hq_pos
    have hq_sq_ne : q ^ 2 ≠ 0 := pow_ne_zero 2 hq_ne
    dsimp [F, W]
    field_simp [hX_ne, hq_ne, hq_sq_ne, hlam_ne]
  have hdiff_eq :
      (Real.log X / (2 * lam * X)) * EfloorMain D Q X -
          ∫ q in (1 : ℝ)..Q, F q / q ^ 2 =
        ∫ q in (1 : ℝ)..Q, (F q * (W q / q ^ 2) - F q / q ^ 2) := by
    rw [hweighted_eq]
    rw [← intervalIntegral.integral_sub hweighted_int hmodel_int]
  have hbound :
      |∫ q in (1 : ℝ)..Q,
        (F q * ((Real.log X / (2 * lam) * PhiDerivOverR B (X / q)) / q ^ 2) -
          F q / q ^ 2)| ≤ δ * |Q - 1| :=
    q_change_error_integral_bound hQ hδ_nonneg hF hW
  rw [show (∫ q in (1 : ℝ)..Q,
          fract (GX D X (D.Phi (X / q))) / q ^ 2) =
        ∫ q in (1 : ℝ)..Q, F q / q ^ 2 by rfl]
  rw [hdiff_eq]
  calc
    |∫ q in (1 : ℝ)..Q, (F q * (W q / q ^ 2) - F q / q ^ 2)|
        ≤ δ * |Q - 1| := by simpa [W] using hbound
    _ ≤ ε := by
      dsimp [δ]
      calc
        ε / (|Q - 1| + 1) * |Q - 1| ≤
            ε / (|Q - 1| + 1) * (|Q - 1| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (Q - 1)]) (by positivity)
        _ = ε := by
          field_simp [ne_of_gt hden_pos]

/-- Fixed-`Q` normalized asymptotic for the main floor-saving term. -/
theorem floor_main_truncation_fixed_Q (D : PhiPsiData B) {Q : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    Tendsto
      (fun X : ℝ => Real.log X * EfloorMain D Q X / (2 * lam * X))
      Filter.atTop
      (𝓝 (IfractQ Q)) := by
  have hfract := fract_integral_convergence_fixed_Q D hQ
  rw [Metric.tendsto_nhds] at hfract ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [eventually_q_change_uniform_fixed_Q D hQ hhalf,
      hfract (ε / 2) hhalf] with X hmain hfrac
  rw [Real.dist_eq] at hfrac ⊢
  have hmain' :
      |Real.log X * EfloorMain D Q X / (2 * lam * X) -
        ∫ q in (1 : ℝ)..Q,
          fract (GX D X (D.Phi (X / q))) / q ^ 2| ≤ ε / 2 := by
    convert hmain using 1
    ring_nf
  calc
    |Real.log X * EfloorMain D Q X / (2 * lam * X) - IfractQ Q| ≤
        |Real.log X * EfloorMain D Q X / (2 * lam * X) -
          ∫ q in (1 : ℝ)..Q,
            fract (GX D X (D.Phi (X / q))) / q ^ 2| +
        |(∫ q in (1 : ℝ)..Q,
          fract (GX D X (D.Phi (X / q))) / q ^ 2) - IfractQ Q| := by
      exact abs_sub_le _ _ _
    _ < ε := by linarith

/-- The fixed-`Q` main part is bounded above by the corresponding `f` integral. -/
theorem EfloorMain_le_f_integral_of_order (D : PhiPsiData B) {Q X : ℝ}
    (hX : 0 ≤ X) (hXcut : X ≤ D.Phi (X / Q))
    (hcutPhi : D.Phi (X / Q) ≤ D.Phi X) :
    EfloorMain D Q X ≤ ∫ t in D.Phi (X / Q)..D.Phi X, D.f t := by
  unfold EfloorMain
  refine intervalIntegral.integral_mono_on hcutPhi
    (f_mul_fract_GX_intervalIntegrable_of_le D hX hXcut hcutPhi)
    (D.f_intervalIntegrable (D.Phi (X / Q)) (D.Phi X)) ?_
  intro t ht
  exact f_mul_fract_GX_le_f_of_le D hX (hXcut.trans ht.1)

/-- Exact fixed-`Q` split of `Efloor` into the initial tail and main pieces. -/
theorem Efloor_eq_tail_add_main_of_order (D : PhiPsiData B) {Q X : ℝ}
    (hX : 0 ≤ X) (hXcut : X ≤ D.Phi (X / Q))
    (hcutPhi : D.Phi (X / Q) ≤ D.Phi X) :
    Efloor D X = EfloorTail D Q X + EfloorMain D Q X := by
  let cut : ℝ := D.Phi (X / Q)
  have hleft :
      IntervalIntegrable (fun t : ℝ => D.f t * fract (GX D X t))
        MeasureTheory.volume X cut :=
    f_mul_fract_GX_intervalIntegrable D hX (by simpa [cut] using hXcut)
  have hright :
      IntervalIntegrable (fun t : ℝ => D.f t * fract (GX D X t))
        MeasureTheory.volume cut (D.Phi X) :=
    f_mul_fract_GX_intervalIntegrable_of_le D hX
      (by simpa [cut] using hXcut) (by simpa [cut] using hcutPhi)
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals hleft hright
  unfold Efloor EfloorTail EfloorMain
  change
    ∫ t in X..D.Phi X, D.f t * fract (GX D X t) =
      (∫ t in X..cut, D.f t * fract (GX D X t)) +
        ∫ t in cut..D.Phi X, D.f t * fract (GX D X t)
  exact hsplit.symm

/-- Commuted form of the fixed-`Q` split. -/
theorem Efloor_eq_main_add_tail_of_order (D : PhiPsiData B) {Q X : ℝ}
    (hX : 0 ≤ X) (hXcut : X ≤ D.Phi (X / Q))
    (hcutPhi : D.Phi (X / Q) ≤ D.Phi X) :
    Efloor D X = EfloorMain D Q X + EfloorTail D Q X := by
  rw [Efloor_eq_tail_add_main_of_order D hX hXcut hcutPhi, add_comm]

/-- Eventual fixed-`Q` split of `Efloor` into the initial tail and main pieces. -/
theorem eventually_Efloor_eq_tail_add_main_fixed_Q (D : PhiPsiData B) {Q : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    ∀ᶠ X : ℝ in Filter.atTop,
      Efloor D X = EfloorTail D Q X + EfloorMain D Q X := by
  filter_upwards [eventually_Phi_X_div_Q_between D hQ] with X horder
  rcases horder with ⟨_hbranch, _hTstar, hX, hXcut, hcutPhi⟩
  exact Efloor_eq_tail_add_main_of_order D hX hXcut hcutPhi

/-- Eventual fixed-`Q` split with the main term written first. -/
theorem eventually_Efloor_eq_main_add_tail_fixed_Q (D : PhiPsiData B) {Q : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    ∀ᶠ X : ℝ in Filter.atTop,
      Efloor D X = EfloorMain D Q X + EfloorTail D Q X := by
  filter_upwards [eventually_Phi_X_div_Q_between D hQ] with X horder
  rcases horder with ⟨_hbranch, _hTstar, hX, hXcut, hcutPhi⟩
  exact Efloor_eq_main_add_tail_of_order D hX hXcut hcutPhi

/-- Eventual nonnegativity of the fixed-`Q` tail part. -/
theorem eventually_EfloorTail_nonneg_fixed_Q (D : PhiPsiData B) {Q : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    ∀ᶠ X : ℝ in Filter.atTop, 0 ≤ EfloorTail D Q X := by
  filter_upwards [eventually_Phi_X_div_Q_between D hQ] with X horder
  rcases horder with ⟨_hbranch, _hTstar, hX, hXcut, _hcutPhi⟩
  exact EfloorTail_nonneg_of_order D hX hXcut

/-- Eventual nonnegativity of the fixed-`Q` main part. -/
theorem eventually_EfloorMain_nonneg_fixed_Q (D : PhiPsiData B) {Q : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    ∀ᶠ X : ℝ in Filter.atTop, 0 ≤ EfloorMain D Q X := by
  filter_upwards [eventually_Phi_X_div_Q_between D hQ] with X horder
  rcases horder with ⟨_hbranch, _hTstar, hX, hXcut, hcutPhi⟩
  exact EfloorMain_nonneg_of_order D hX hXcut hcutPhi

/-- The truncated model fractional-part integral is nonnegative on ordered intervals. -/
theorem IfractQ_nonneg {Q : ℝ} (hQ : (1 : ℝ) ≤ Q) :
    0 ≤ IfractQ Q := by
  unfold IfractQ
  exact intervalIntegral.integral_nonneg hQ
    (fun q _hq => div_nonneg (fract_nonneg q) (sq_nonneg q))

/-- Truncated fractional-part model integrals exhaust the improper integral. -/
theorem IfractQ_tendsto_IfractInf :
    Tendsto IfractQ Filter.atTop (𝓝 IfractInf) := by
  unfold IfractQ IfractInf
  simpa using
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      (μ := MeasureTheory.volume)
      (a := (1 : ℝ))
      (f := fun q : ℝ => fract q / q ^ 2)
      integrableOn_fract_div_sq_Ioi_one
      tendsto_id)

/-- The improper fractional-part model integral has the Euler-constant value. -/
theorem IfractInf_eq_one_sub_euler :
    IfractInf = 1 - Real.eulerMascheroniConstant := by
  unfold IfractInf
  exact integral_fract_div_sq_Ioi

/-- Normalized floor-saving limit with the improper fractional-integral constant. -/
theorem floor_saving_normalized_limit_to_IfractInf (D : PhiPsiData B) :
    Tendsto
      (fun X : ℝ => Real.log X * Efloor D X / (2 * lam * X))
      Filter.atTop
      (𝓝 IfractInf) := by
  rcases EfloorTail_bound_uniform_Q D with ⟨C, _hC_pos, htail_bound⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  have hI_ev := (Metric.tendsto_nhds.mp IfractQ_tendsto_IfractInf) (ε / 3) hthird
  have hC_tend : Tendsto (fun Q : ℝ => C / Q) Filter.atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C)).div_atTop tendsto_id
  have hC_ev := (Metric.tendsto_nhds.mp hC_tend) (ε / 3) hthird
  rcases (hI_ev.and (hC_ev.and (eventually_ge_atTop (2 : ℝ)))).exists with
    ⟨Q, hIQ_dist, hC_dist, hQ_two⟩
  have hQ_one : (1 : ℝ) ≤ Q := le_trans (by norm_num : (1 : ℝ) ≤ 2) hQ_two
  have hmain_ev := (Metric.tendsto_nhds.mp (floor_main_truncation_fixed_Q D hQ_one))
    (ε / 3) hthird
  filter_upwards [hmain_ev, eventually_Efloor_eq_main_add_tail_fixed_Q D hQ_one,
      htail_bound Q hQ_two, eventually_gt_atTop (1 : ℝ)] with X hmain_dist hsplit htail hX_one
  rw [Real.dist_eq] at hmain_dist hIQ_dist hC_dist ⊢
  let M : ℝ := Real.log X * EfloorMain D Q X / (2 * lam * X)
  let T : ℝ := Real.log X * EfloorTail D Q X / (2 * lam * X)
  have hnorm_eq : Real.log X * Efloor D X / (2 * lam * X) = M + T := by
    dsimp [M, T]
    rw [hsplit]
    ring
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    have hlog_pos : 0 < Real.log X := Real.log_pos hX_one
    have hX_pos : 0 < X := lt_trans zero_lt_one hX_one
    have hlam_pos : 0 < lam := by
      unfold lam
      positivity
    have hden_pos : 0 < 2 * lam * X := by positivity
    exact div_nonneg (mul_nonneg (le_of_lt hlog_pos) htail.1) (le_of_lt hden_pos)
  have hT_abs : |T| = T := abs_of_nonneg hT_nonneg
  have hC_small : C / Q < ε / 3 := by
    have hC_dist' : |C / Q| < ε / 3 := by simpa using hC_dist
    exact lt_of_le_of_lt (le_abs_self _) hC_dist'
  have htail_small : T < ε / 3 := by
    exact lt_of_le_of_lt htail.2 hC_small
  have hmainM : |M - IfractQ Q| < ε / 3 := by
    simpa [M] using hmain_dist
  have htri : |M + T - IfractInf| ≤ |M - IfractQ Q| + |IfractQ Q - IfractInf| + |T| := by
    calc
      |M + T - IfractInf| =
          |(M - IfractQ Q) + (IfractQ Q - IfractInf) + T| := by ring_nf
      _ ≤ |(M - IfractQ Q) + (IfractQ Q - IfractInf)| + |T| := abs_add_le _ _
      _ ≤ |M - IfractQ Q| + |IfractQ Q - IfractInf| + |T| := by
        linarith [abs_add_le (M - IfractQ Q) (IfractQ Q - IfractInf)]
  rw [hnorm_eq]
  calc
    |M + T - IfractInf| ≤ |M - IfractQ Q| + |IfractQ Q - IfractInf| + |T| := htri
    _ < ε := by
      rw [hT_abs]
      linarith

/-- Normalized floor-saving limit with the Euler-constant value. -/
theorem floor_saving_normalized_limit (D : PhiPsiData B) :
    Tendsto
      (fun X : ℝ => Real.log X * Efloor D X / (2 * lam * X))
      Filter.atTop
      (𝓝 (1 - Real.eulerMascheroniConstant)) := by
  simpa [IfractInf_eq_one_sub_euler] using floor_saving_normalized_limit_to_IfractInf D

/-- Convert the normalized floor-saving limit into the small-o asymptotic. -/
theorem floor_saving_asymptotic_of_normalized (D : PhiPsiData B)
    (hnorm :
      Tendsto (fun X : ℝ => Real.log X * Efloor D X / (2 * lam * X))
        Filter.atTop (𝓝 (1 - Real.eulerMascheroniConstant))) :
    (fun X : ℝ =>
      Efloor D X - 2 * lam * (1 - Real.eulerMascheroniConstant) * X / Real.log X)
      =o[Filter.atTop] scaleReal := by
  refine isLittleO_of_tendsto' ?hzero ?htend
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX hscale
    exfalso
    have hX_ne : X ≠ 0 := ne_of_gt (lt_trans zero_lt_one hX)
    have hlog_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
    have hscale_ne : scaleReal X ≠ 0 := by
      rw [scaleReal]
      exact div_ne_zero hX_ne hlog_ne
    exact hscale_ne hscale
  · have hsub :
        Tendsto
          (fun X : ℝ => Real.log X * Efloor D X / (2 * lam * X) -
            (1 - Real.eulerMascheroniConstant))
          Filter.atTop (𝓝 0) := by
      simpa using hnorm.sub (tendsto_const_nhds (x := 1 - Real.eulerMascheroniConstant))
    have hmul0 :
        Tendsto
          (fun X : ℝ =>
            (2 * lam) *
              (Real.log X * Efloor D X / (2 * lam * X) -
                (1 - Real.eulerMascheroniConstant)))
          Filter.atTop (𝓝 0) := by
      simpa using hsub.const_mul (2 * lam)
    refine hmul0.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hX_ne : X ≠ 0 := ne_of_gt (lt_trans zero_lt_one hX)
    have hlog_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
    have hlam_ne : 2 * lam ≠ 0 := by
      unfold lam
      positivity
    have hlam_ne' : lam ≠ 0 := by
      intro h
      exact hlam_ne (by rw [h, mul_zero])
    change (2 * lam) *
        (Real.log X * Efloor D X / (2 * lam * X) -
          (1 - Real.eulerMascheroniConstant)) =
      (Efloor D X - 2 * lam * (1 - Real.eulerMascheroniConstant) * X / Real.log X) /
        scaleReal X
    rw [scaleReal]
    field_simp [hX_ne, hlog_ne, hlam_ne, hlam_ne']

end FloorSaving
