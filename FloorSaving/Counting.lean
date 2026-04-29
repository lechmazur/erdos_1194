import FloorSaving.UniqueDiff
import FloorSaving.AnalyticInterfaces

noncomputable section

open Classical
open Filter Topology MeasureTheory Asymptotics
open scoped Real BigOperators

namespace FloorSaving

/-- Pointwise upper-bound predicate. It is vacuous at `n = 0`. -/
def UpperBoundAt
    (A : Set ℕ) (hA : UniquePositiveDiffs A) (B : ℝ) (n : ℕ) : Prop :=
  ∀ hn : 0 < n,
    0 < denom B n →
      (top A hA ⟨n, hn⟩ : ℝ) ≤
        lowerBoundRHS B n

/-- Eventual non-strict upper bound whose negation gives the main theorem. -/
def EventuallyUpperBound
    (A : Set ℕ) (hA : UniquePositiveDiffs A) (B : ℝ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, UpperBoundAt A hA B n

/-- Finite cut of `A` by a real upper bound. Used on nonnegative cutoffs. -/
noncomputable def natCut (A : Set ℕ) (T : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (Nat.floor T + 1)).filter (fun a : ℕ => a ∈ A)

/-- Counting function `N(T) = |A ∩ [1,T]|` on the positive ranges used in the proof. -/
noncomputable def Ncount (A : Set ℕ) (T : ℝ) : ℕ :=
  (natCut A T).card

/-- Bottoms in the window `t-X ≤ b < t`, restricted to `A`. -/
noncomputable def bottomWindow (A : Set ℕ) (X t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range t).filter (fun b : ℕ => b ∈ A ∧ t - X ≤ b)

/-- Membership in `bottomWindow`. Prove this before the counting identity. -/
theorem mem_bottomWindow_iff
    {A : Set ℕ} {X t b : ℕ} :
    b ∈ bottomWindow A X t ↔ b ∈ A ∧ t - X ≤ b ∧ b < t := by
  unfold bottomWindow
  simp [and_assoc, and_left_comm, and_comm]

/-- Membership in `natCut`. The exact floor theorem names should be verified locally. -/
theorem mem_natCut_iff
    {A : Set ℕ} {T : ℝ} {a : ℕ} (hT : 0 ≤ T) :
    a ∈ natCut A T ↔ a ∈ A ∧ (a : ℝ) ≤ T := by
  constructor
  · intro ha
    rcases Finset.mem_filter.mp ha with ⟨ha_range, haA⟩
    have ha_le_floor : a ≤ Nat.floor T := by
      exact Nat.lt_add_one_iff.mp (Finset.mem_range.mp ha_range)
    have ha_le_T : (a : ℝ) ≤ T := by
      exact (Nat.cast_le.mpr ha_le_floor).trans (Nat.floor_le hT)
    exact ⟨haA, ha_le_T⟩
  · rintro ⟨haA, haT⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr (Nat.le_floor haT)), haA⟩

/-- TeX Part 1: spacing from the eventual upper-bound assumption. -/
theorem spacing
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∃ Z0 : ℕ, ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        D.psi (z : ℝ) ≤ ((z - y : ℕ) : ℝ) := by
  classical
  rcases (Filter.eventually_atTop.mp hupper) with ⟨Nupper, hNupper⟩
  rcases (Filter.eventually_atTop.mp (eventually_denom_pos B)) with ⟨Ndenom, hNdenom⟩
  rcases exists_nat_gt D.Tstar with ⟨Tbound, hTbound⟩
  let Ncut : ℕ := max D.N0 (max Nupper Ndenom)
  let topImage : Finset ℕ :=
    (Finset.range Ncut).image
      (fun d : ℕ => if hd : 0 < d then top A hA ⟨d, hd⟩ else 0)
  let topSet : Finset ℕ := insert 0 topImage
  let topSmall : ℕ := topSet.max' (Finset.insert_nonempty 0 topImage)
  refine ⟨max Tbound topSmall, ?_⟩
  intro y z hyA hzA hyz hZz
  let d : ℕ := z - y
  have hdpos : 0 < d := by
    exact Nat.sub_pos_of_lt hyz
  have hp : RepresentsDiff A d (z, y) := by
    exact ⟨hzA, hyA, hyz, rfl⟩
  have hz_eq_top : z = top A hA ⟨d, hdpos⟩ := by
    exact congrArg Prod.fst (repPair_eq_of_represents hA hdpos hp)
  have hsmall_top_le (hdlt : d < Ncut) :
      top A hA ⟨d, hdpos⟩ ≤ topSmall := by
    have hmem_image : top A hA ⟨d, hdpos⟩ ∈ topImage := by
      dsimp [topImage]
      refine Finset.mem_image.mpr ⟨d, Finset.mem_range.mpr hdlt, ?_⟩
      simp [hdpos]
    have hmem_topSet : top A hA ⟨d, hdpos⟩ ∈ topSet := by
      dsimp [topSet]
      exact Finset.mem_insert.mpr (Or.inr hmem_image)
    dsimp [topSmall]
    exact Finset.le_max' topSet (top A hA ⟨d, hdpos⟩) hmem_topSet
  have hNcut_le_d : Ncut ≤ d := by
    by_contra hnot
    have hdlt : d < Ncut := Nat.lt_of_not_ge hnot
    have htop_le : top A hA ⟨d, hdpos⟩ ≤ topSmall := hsmall_top_le hdlt
    have hz_le_topSmall : z ≤ topSmall := by
      simpa [hz_eq_top] using htop_le
    have hz_le_Z0 : z ≤ max Tbound topSmall :=
      hz_le_topSmall.trans (le_max_right Tbound topSmall)
    exact (Nat.not_lt_of_ge hz_le_Z0) hZz
  have hTstar_le_z : D.Tstar ≤ (z : ℝ) := by
    have hT_lt_Z0 : D.Tstar < ((max Tbound topSmall : ℕ) : ℝ) := by
      exact hTbound.trans_le (Nat.cast_le.mpr (le_max_left Tbound topSmall))
    have hZ0_lt_z : ((max Tbound topSmall : ℕ) : ℝ) < (z : ℝ) := by
      exact Nat.cast_lt.mpr hZz
    exact le_of_lt (hT_lt_Z0.trans hZ0_lt_z)
  have hNupper_le_Ncut : Nupper ≤ Ncut := by
    exact (le_max_left Nupper Ndenom).trans (le_max_right D.N0 (max Nupper Ndenom))
  have hNdenom_le_Ncut : Ndenom ≤ Ncut := by
    exact (le_max_right Nupper Ndenom).trans (le_max_right D.N0 (max Nupper Ndenom))
  have hN0_le_Ncut : D.N0 ≤ Ncut := by
    exact le_max_left D.N0 (max Nupper Ndenom)
  have hupper_d : UpperBoundAt A hA B d :=
    hNupper d (hNupper_le_Ncut.trans hNcut_le_d)
  have hdenom_d : 0 < denom B d :=
    hNdenom d (hNdenom_le_Ncut.trans hNcut_le_d)
  have hN0_le_d : D.N0 ≤ d :=
    hN0_le_Ncut.trans hNcut_le_d
  have hN0_le_real : (D.N0 : ℝ) ≤ (d : ℝ) := by
    exact Nat.cast_le.mpr hN0_le_d
  have hz_le_phi : (z : ℝ) ≤ D.Phi (d : ℝ) := by
    calc
      (z : ℝ) = (top A hA ⟨d, hdpos⟩ : ℝ) := by
        exact_mod_cast hz_eq_top
      _ ≤ lowerBoundRHS B d := hupper_d hdpos hdenom_d
      _ = PhiFormula B (d : ℝ) := (PhiFormula_nat_eq_lowerBoundRHS B d).symm
      _ = D.Phi (d : ℝ) := (D.Phi_eq (d : ℝ)).symm
  exact (by simpa [d] using D.psi_le_of_le_Phi hTstar_le_z hN0_le_real hz_le_phi)

/-- Lower bound an interval integral by a constant lower bound on the interval. -/
theorem intervalIntegral_const_mul_le_of_forall_le
    {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (h : ∀ x ∈ Set.Icc a b, c ≤ f x) :
    (b - a) * c ≤ ∫ x in a..b, f x := by
  have hc : IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a b := by
    exact intervalIntegral.intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hab hc hf h
  simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono

/-- TeX Part 1: integral domination across large gaps. -/
theorem gap_integral_ge_one
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∃ Z0 : ℕ, ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s := by
  rcases spacing A hA D hupper with ⟨Zsp, hspacing⟩
  rcases exists_nat_gt D.Tstar with ⟨Tbound, hTbound⟩
  refine ⟨max Zsp Tbound, ?_⟩
  intro y z hyA hzA hyz hZz
  have hZsp_lt_z : Zsp < z :=
    lt_of_le_of_lt (le_max_left Zsp Tbound) hZz
  have hTbound_lt_z : Tbound < z :=
    lt_of_le_of_lt (le_max_right Zsp Tbound) hZz
  have hTstar_le_z : D.Tstar ≤ (z : ℝ) := by
    have hTbound_lt_z_real : (Tbound : ℝ) < (z : ℝ) := by
      exact Nat.cast_lt.mpr hTbound_lt_z
    exact le_of_lt (hTbound.trans hTbound_lt_z_real)
  have hpsi_le_gap :
      D.psi (z : ℝ) ≤ ((z - y : ℕ) : ℝ) :=
    hspacing y z hyA hzA hyz hZsp_lt_z
  have hpsi_pos : 0 < D.psi (z : ℝ) :=
    D.psi_pos_tail (z : ℝ) hTstar_le_z
  have hgap_pos : 0 < ((z - y : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hyz
  have hinv_gap_le_fz :
      1 / ((z - y : ℕ) : ℝ) ≤ D.f (z : ℝ) := by
    have hinv_gap_le_inv_psi :
        1 / ((z - y : ℕ) : ℝ) ≤ 1 / D.psi (z : ℝ) :=
      one_div_le_one_div_of_le hpsi_pos hpsi_le_gap
    simpa [D.f_eq_tail (z : ℝ) hTstar_le_z] using hinv_gap_le_inv_psi
  have hone_le_gap_mul_fz :
      1 ≤ ((z - y : ℕ) : ℝ) * D.f (z : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hinv_gap_le_fz hgap_pos.le
    have hcancel :
        ((z - y : ℕ) : ℝ) * (((z - y : ℕ) : ℝ))⁻¹ = 1 := by
      exact mul_inv_cancel₀ (ne_of_gt hgap_pos)
    simpa [one_div, hcancel] using hmul
  have hyz_real : (y : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast le_of_lt hyz
  have hpoint :
      ∀ s ∈ Set.Icc (y : ℝ) (z : ℝ), D.f (z : ℝ) ≤ D.f s := by
    intro s hs
    have hs_nonneg : s ∈ Set.Ici (0 : ℝ) := by
      exact (Nat.cast_nonneg y).trans hs.1
    have hz_nonneg : (z : ℝ) ∈ Set.Ici (0 : ℝ) := by
      simp
    exact D.f_antitone hs_nonneg hz_nonneg hs.2
  have hconst_le_integral :
      ((z : ℝ) - (y : ℝ)) * D.f (z : ℝ) ≤
        ∫ s in (y : ℝ)..(z : ℝ), D.f s :=
    intervalIntegral_const_mul_le_of_forall_le
      hyz_real (D.f_intervalIntegrable (y : ℝ) (z : ℝ)) hpoint
  have hgap_eq : ((z - y : ℕ) : ℝ) = (z : ℝ) - (y : ℝ) := by
    exact Nat.cast_sub (Nat.le_of_lt hyz)
  have hone_le_sub_mul_fz :
      1 ≤ ((z : ℝ) - (y : ℝ)) * D.f (z : ℝ) := by
    simpa [hgap_eq] using hone_le_gap_mul_fz
  exact hone_le_sub_mul_fz.trans hconst_le_integral

/-- A finite set whose elements are all beyond `Z0` is bounded by one plus the integral. -/
theorem large_finset_card_le_one_add_integral
    {B : ℝ} {A : Set ℕ} {Z0 : ℕ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s) :
    ∀ S : Finset ℕ,
      (∀ a ∈ S, a ∈ A) →
      (∀ a ∈ S, Z0 < a) →
      ∀ T : ℝ,
        0 ≤ T →
        (∀ a ∈ S, (a : ℝ) ≤ T) →
          (S.card : ℝ) ≤ 1 + ∫ s in (0 : ℝ)..T, D.f s := by
  classical
  intro S
  refine Finset.induction_on_max (s := S) ?_ ?_
  · intro _hmem _hlarge T hT _hle
    have hint_nonneg : 0 ≤ ∫ s in (0 : ℝ)..T, D.f s := by
      exact intervalIntegral.integral_nonneg hT (fun s hs => D.f_nonneg hs.1)
    have hone_nonneg : (0 : ℝ) ≤ 1 + ∫ s in (0 : ℝ)..T, D.f s :=
      add_nonneg zero_le_one hint_nonneg
    simpa using hone_nonneg
  · intro a S hlt ih hmem hlarge T hT hle
    have ha_not_mem : a ∉ S := by
      intro ha
      exact (Nat.lt_irrefl a) (hlt a ha)
    have hcard_insert :
        ((insert a S).card : ℝ) = (S.card : ℝ) + 1 := by
      rw [Finset.card_insert_of_notMem ha_not_mem, Nat.cast_add]
      norm_num
    have ha_mem_insert : a ∈ insert a S := Finset.mem_insert_self a S
    have haA : a ∈ A := hmem a ha_mem_insert
    have hZ0a : Z0 < a := hlarge a ha_mem_insert
    have ha_le_T : (a : ℝ) ≤ T := hle a ha_mem_insert
    by_cases hS : S.Nonempty
    · let y : ℕ := S.max' hS
      have hyS : y ∈ S := by
        dsimp [y]
        exact Finset.max'_mem S hS
      have hyA : y ∈ A := hmem y (Finset.mem_insert.mpr (Or.inr hyS))
      have hy_lt_a : y < a := hlt y hyS
      have hy_nonneg : 0 ≤ (y : ℝ) := Nat.cast_nonneg y
      have hS_le_y : ∀ x ∈ S, (x : ℝ) ≤ (y : ℝ) := by
        intro x hx
        exact Nat.cast_le.mpr (Finset.le_max' S x hx)
      have hih_y :
          (S.card : ℝ) ≤ 1 + ∫ s in (0 : ℝ)..(y : ℝ), D.f s :=
        ih
          (fun x hx => hmem x (Finset.mem_insert.mpr (Or.inr hx)))
          (fun x hx => hlarge x (Finset.mem_insert.mpr (Or.inr hx)))
          (y : ℝ) hy_nonneg hS_le_y
      have hgap_y_a : 1 ≤ ∫ s in (y : ℝ)..(a : ℝ), D.f s :=
        hgap y a hyA haA hy_lt_a hZ0a
      have hadd_0_y_a :
          (∫ s in (0 : ℝ)..(y : ℝ), D.f s) +
              (∫ s in (y : ℝ)..(a : ℝ), D.f s) =
            ∫ s in (0 : ℝ)..(a : ℝ), D.f s :=
        intervalIntegral.integral_add_adjacent_intervals
          (D.f_intervalIntegrable (0 : ℝ) (y : ℝ))
          (D.f_intervalIntegrable (y : ℝ) (a : ℝ))
      have hcard_le_a :
          ((insert a S).card : ℝ) ≤
            1 + ∫ s in (0 : ℝ)..(a : ℝ), D.f s := by
        calc
          ((insert a S).card : ℝ) = (S.card : ℝ) + 1 := hcard_insert
          _ ≤ (1 + ∫ s in (0 : ℝ)..(y : ℝ), D.f s) +
                (∫ s in (y : ℝ)..(a : ℝ), D.f s) := by
              exact add_le_add hih_y hgap_y_a
          _ = 1 + ∫ s in (0 : ℝ)..(a : ℝ), D.f s := by
              rw [← hadd_0_y_a]
              ring
      have ha_nonneg : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
      have hint_a_T_nonneg : 0 ≤ ∫ s in (a : ℝ)..T, D.f s := by
        exact intervalIntegral.integral_nonneg ha_le_T
          (fun s hs => D.f_nonneg (ha_nonneg.trans hs.1))
      have hadd_0_a_T :
          (∫ s in (0 : ℝ)..(a : ℝ), D.f s) +
              (∫ s in (a : ℝ)..T, D.f s) =
            ∫ s in (0 : ℝ)..T, D.f s :=
        intervalIntegral.integral_add_adjacent_intervals
          (D.f_intervalIntegrable (0 : ℝ) (a : ℝ))
          (D.f_intervalIntegrable (a : ℝ) T)
      have hextend :
          1 + ∫ s in (0 : ℝ)..(a : ℝ), D.f s ≤
            1 + ∫ s in (0 : ℝ)..T, D.f s := by
        have hmono :
            ∫ s in (0 : ℝ)..(a : ℝ), D.f s ≤
              ∫ s in (0 : ℝ)..T, D.f s := by
          have hle_add :
              (∫ s in (0 : ℝ)..(a : ℝ), D.f s) ≤
                (∫ s in (0 : ℝ)..(a : ℝ), D.f s) +
                  (∫ s in (a : ℝ)..T, D.f s) :=
            le_add_of_nonneg_right hint_a_T_nonneg
          exact hle_add.trans_eq hadd_0_a_T
        exact add_le_add_right hmono 1
      exact hcard_le_a.trans hextend
    · have hS_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      have hcard_one : ((insert a S).card : ℝ) = 1 := by
        rw [hcard_insert, hS_empty]
        simp
      have hint_nonneg : 0 ≤ ∫ s in (0 : ℝ)..T, D.f s := by
        exact intervalIntegral.integral_nonneg hT (fun s hs => D.f_nonneg hs.1)
      calc
        ((insert a S).card : ℝ) = 1 := hcard_one
        _ ≤ 1 + ∫ s in (0 : ℝ)..T, D.f s :=
          le_add_of_nonneg_right hint_nonneg

/-- TeX Part 1: counting-function majorant. -/
theorem counting_function_bound
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∃ C : ℝ, ∀ T : ℝ,
      0 ≤ T →
        (Ncount A T : ℝ) ≤ C + ∫ s in (0 : ℝ)..T, D.f s := by
  classical
  rcases gap_integral_ge_one A hA D hupper with ⟨Z0, hgap⟩
  refine ⟨(Z0 : ℝ) + 2, ?_⟩
  intro T hT
  let S : Finset ℕ := natCut A T
  let Ssmall : Finset ℕ := S.filter (fun a : ℕ => a ≤ Z0)
  let Slarge : Finset ℕ := S.filter (fun a : ℕ => ¬ a ≤ Z0)
  have hsplit_nat : Ssmall.card + Slarge.card = S.card := by
    simpa [Ssmall, Slarge] using
      (Finset.card_filter_add_card_filter_not
        (s := S) (p := fun a : ℕ => a ≤ Z0))
  have hsplit_real :
      (S.card : ℝ) = (Ssmall.card : ℝ) + (Slarge.card : ℝ) := by
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hsplit_nat
    simpa [Nat.cast_add] using hcast.symm
  have hsmall_subset : Ssmall ⊆ Finset.range (Z0 + 1) := by
    intro a ha
    have ha_le : a ≤ Z0 := (Finset.mem_filter.mp ha).2
    exact Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr ha_le)
  have hsmall_card_le_nat : Ssmall.card ≤ Z0 + 1 := by
    have hcard := Finset.card_le_card hsmall_subset
    simpa [Finset.card_range] using hcard
  have hsmall_card_le_real : (Ssmall.card : ℝ) ≤ (Z0 : ℝ) + 1 := by
    exact_mod_cast hsmall_card_le_nat
  have hlarge_memA : ∀ a ∈ Slarge, a ∈ A := by
    intro a ha
    have haS : a ∈ S := (Finset.mem_filter.mp ha).1
    have haCut : a ∈ natCut A T := by
      simpa [S] using haS
    exact ((mem_natCut_iff (A := A) (T := T) (a := a) hT).mp haCut).1
  have hlarge_gt : ∀ a ∈ Slarge, Z0 < a := by
    intro a ha
    exact Nat.lt_of_not_ge (Finset.mem_filter.mp ha).2
  have hlarge_leT : ∀ a ∈ Slarge, (a : ℝ) ≤ T := by
    intro a ha
    have haS : a ∈ S := (Finset.mem_filter.mp ha).1
    have haCut : a ∈ natCut A T := by
      simpa [S] using haS
    exact ((mem_natCut_iff (A := A) (T := T) (a := a) hT).mp haCut).2
  have hlarge_bound :
      (Slarge.card : ℝ) ≤ 1 + ∫ s in (0 : ℝ)..T, D.f s :=
    large_finset_card_le_one_add_integral D hgap
      Slarge hlarge_memA hlarge_gt T hT hlarge_leT
  calc
    (Ncount A T : ℝ) = (S.card : ℝ) := by
      simp [Ncount, S]
    _ = (Ssmall.card : ℝ) + (Slarge.card : ℝ) := hsplit_real
    _ ≤ ((Z0 : ℝ) + 1) + (1 + ∫ s in (0 : ℝ)..T, D.f s) := by
      exact add_le_add hsmall_card_le_real hlarge_bound
    _ = (Z0 : ℝ) + 2 + ∫ s in (0 : ℝ)..T, D.f s := by
      ring

/-- Eventually, all selected tops for `1 ≤ n ≤ X` lie below `D.Phi X`. -/
theorem eventually_top_le_Phi
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∀ᶠ X : ℕ in Filter.atTop,
      0 ≤ D.Phi (X : ℝ) ∧
        ∀ n : ℕ, (hn : 0 < n) → n ≤ X →
          (top A hA ⟨n, hn⟩ : ℝ) ≤ D.Phi (X : ℝ) := by
  classical
  rcases (Filter.eventually_atTop.mp hupper) with ⟨Nupper, hNupper⟩
  rcases (Filter.eventually_atTop.mp (eventually_denom_pos B)) with ⟨Ndenom, hNdenom⟩
  let Ncut : ℕ := max D.N0 (max Nupper Ndenom)
  let topImage : Finset ℕ :=
    (Finset.range Ncut).image
      (fun d : ℕ => if hd : 0 < d then top A hA ⟨d, hd⟩ else 0)
  let topSet : Finset ℕ := insert 0 topImage
  let topSmall : ℕ := topSet.max' (Finset.insert_nonempty 0 topImage)
  have hPhi_nat :
      Tendsto (fun X : ℕ => D.Phi (X : ℝ)) Filter.atTop Filter.atTop := by
    exact D.Phi_tendsto_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hPhi_nat.eventually_ge_atTop (max (0 : ℝ) (topSmall : ℝ))] with X hPhi_ge
  constructor
  · exact (le_max_left (0 : ℝ) (topSmall : ℝ)).trans hPhi_ge
  · intro n hn hnX
    have hNupper_le_Ncut : Nupper ≤ Ncut := by
      exact (le_max_left Nupper Ndenom).trans (le_max_right D.N0 (max Nupper Ndenom))
    have hNdenom_le_Ncut : Ndenom ≤ Ncut := by
      exact (le_max_right Nupper Ndenom).trans (le_max_right D.N0 (max Nupper Ndenom))
    have hN0_le_Ncut : D.N0 ≤ Ncut := by
      exact le_max_left D.N0 (max Nupper Ndenom)
    by_cases hNcut_le_n : Ncut ≤ n
    · have hupper_n : UpperBoundAt A hA B n :=
        hNupper n (hNupper_le_Ncut.trans hNcut_le_n)
      have hdenom_n : 0 < denom B n :=
        hNdenom n (hNdenom_le_Ncut.trans hNcut_le_n)
      have hN0_le_n : D.N0 ≤ n :=
        hN0_le_Ncut.trans hNcut_le_n
      have hN0_le_X : D.N0 ≤ X :=
        hN0_le_n.trans hnX
      have hphi_mono :
          D.Phi (n : ℝ) ≤ D.Phi (X : ℝ) :=
        D.Phi_mono_tail
          (show (D.N0 : ℝ) ≤ (n : ℝ) from Nat.cast_le.mpr hN0_le_n)
          (show (D.N0 : ℝ) ≤ (X : ℝ) from Nat.cast_le.mpr hN0_le_X)
          (Nat.cast_le.mpr hnX)
      calc
        (top A hA ⟨n, hn⟩ : ℝ) ≤ lowerBoundRHS B n := hupper_n hn hdenom_n
        _ = PhiFormula B (n : ℝ) := (PhiFormula_nat_eq_lowerBoundRHS B n).symm
        _ = D.Phi (n : ℝ) := (D.Phi_eq (n : ℝ)).symm
        _ ≤ D.Phi (X : ℝ) := hphi_mono
    · have hnlt : n < Ncut := Nat.lt_of_not_ge hNcut_le_n
      have htop_le_topSmall :
          top A hA ⟨n, hn⟩ ≤ topSmall := by
        have hmem_image : top A hA ⟨n, hn⟩ ∈ topImage := by
          dsimp [topImage]
          refine Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hnlt, ?_⟩
          simp [hn]
        have hmem_topSet : top A hA ⟨n, hn⟩ ∈ topSet := by
          dsimp [topSet]
          exact Finset.mem_insert.mpr (Or.inr hmem_image)
        dsimp [topSmall]
        exact Finset.le_max' topSet (top A hA ⟨n, hn⟩) hmem_topSet
      have htopSmall_le_phi : (topSmall : ℝ) ≤ D.Phi (X : ℝ) :=
        (le_max_right (0 : ℝ) (topSmall : ℝ)).trans hPhi_ge
      exact (Nat.cast_le.mpr htop_le_topSmall).trans htopSmall_le_phi

/-- On the same tail, `Phi(X)` dominates the natural cutoff `X`. -/
theorem eventually_natCast_le_Phi
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (X : ℝ) ≤ D.Phi (X : ℝ) := by
  filter_upwards [eventually_top_le_Phi A hA D hupper, Ici_mem_atTop (1 : ℕ)]
    with X hPhi hX_one
  rcases hPhi with ⟨_hPhi_nonneg, htop_le⟩
  have hX_pos : 0 < X := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hX_one
  have hX_le_top : X ≤ top A hA ⟨X, hX_pos⟩ :=
    diff_le_top hA ⟨X, hX_pos⟩
  exact (Nat.cast_le.mpr hX_le_top).trans (htop_le X hX_pos le_rfl)

/-- If a represented difference is at most a cutoff, the bottom lies in the cutoff window. -/
theorem top_sub_cutoff_le_bot_of_sub_eq_of_le
    {t b n X : ℕ} (hsub : t - b = n) (hnpos : 0 < n) (hnX : n ≤ X) :
    t - X ≤ b := by
  rw [Nat.sub_le_iff_le_add]
  have hbt : b < t := Nat.lt_of_sub_pos (by simpa [hsub] using hnpos)
  have ht_eq : t = n + b := Nat.eq_add_of_sub_eq (le_of_lt hbt) hsub
  calc
    t = n + b := ht_eq
    _ ≤ X + b := Nat.add_le_add_right hnX b
    _ = b + X := by rw [add_comm]

/-- A bottom-window lower bound gives an upper bound on the represented difference. -/
theorem sub_le_of_cutoff_sub_le
    {t b X : ℕ} (hwin : t - X ≤ b) :
    t - b ≤ X := by
  rw [Nat.sub_le_iff_le_add]
  have ht : t ≤ b + X := Nat.sub_le_iff_le_add.mp hwin
  simpa [add_comm] using ht

/-- In a finite linearly ordered set, summing predecessors counts two-element subsets. -/
theorem sum_card_filter_lt_eq_choose_two (S : Finset ℕ) :
    (∑ t ∈ S, (S.filter fun b : ℕ => b < t).card) = S.card.choose 2 := by
  classical
  refine Finset.induction_on_max (s := S) ?_ ?_
  · simp
  · intro a S hlt ih
    have ha_not_mem : a ∉ S := by
      intro ha
      exact (Nat.lt_irrefl a) (hlt a ha)
    have hfilter_a : (insert a S).filter (fun b : ℕ => b < a) = S := by
      ext b
      constructor
      · intro hb
        rcases Finset.mem_filter.mp hb with ⟨hb_insert, hba⟩
        rcases Finset.mem_insert.mp hb_insert with hb_eq | hbS
        · subst b
          omega
        · exact hbS
      · intro hbS
        exact Finset.mem_filter.mpr ⟨Finset.mem_insert.mpr (Or.inr hbS), hlt b hbS⟩
    have hfilter_t : ∀ t ∈ S,
        (insert a S).filter (fun b : ℕ => b < t) = S.filter (fun b : ℕ => b < t) := by
      intro t ht
      ext b
      constructor
      · intro hb
        rcases Finset.mem_filter.mp hb with ⟨hb_insert, hbt⟩
        rcases Finset.mem_insert.mp hb_insert with hb_eq | hbS
        · subst b
          have hta : t < a := hlt t ht
          omega
        · exact Finset.mem_filter.mpr ⟨hbS, hbt⟩
      · intro hb
        rcases Finset.mem_filter.mp hb with ⟨hbS, hbt⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_insert.mpr (Or.inr hbS), hbt⟩
    calc
      (∑ t ∈ insert a S, ((insert a S).filter fun b : ℕ => b < t).card)
          = ((insert a S).filter fun b : ℕ => b < a).card +
              ∑ t ∈ S, ((insert a S).filter fun b : ℕ => b < t).card := by
            rw [Finset.sum_insert ha_not_mem]
      _ = S.card + ∑ t ∈ S, (S.filter fun b : ℕ => b < t).card := by
            rw [hfilter_a]
            congr 1
            exact Finset.sum_congr rfl (fun t ht => by rw [hfilter_t t ht])
      _ = S.card + S.card.choose 2 := by
            rw [ih]
      _ = (insert a S).card.choose 2 := by
            rw [Finset.card_insert_of_notMem ha_not_mem]
            rw [Nat.choose_succ_succ']
            simp [Nat.choose_one_right]

/-- TeX Part 3: exact counting identity by tops. -/
theorem top_counting_identity
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∀ᶠ X : ℕ in Filter.atTop,
      X = (∑ t ∈ natCut A (D.Phi (X : ℝ)), (bottomWindow A X t).card) := by
  filter_upwards [eventually_top_le_Phi A hA D hupper] with X hX
  rcases hX with ⟨hPhi_nonneg, htop_le⟩
  let S : Finset ℕ := Finset.Icc 1 X
  let P : Finset (Sigma fun _ : ℕ => ℕ) :=
    (natCut A (D.Phi (X : ℝ))).sigma fun t => bottomWindow A X t
  let posOfMem (n : ℕ) (hnS : n ∈ S) : 0 < n := by
    rcases Finset.mem_Icc.mp hnS with ⟨hn1, _hnX⟩
    exact lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn1
  let selected (n : ℕ) (hnS : n ∈ S) : Sigma fun _ : ℕ => ℕ :=
    ⟨top A hA ⟨n, posOfMem n hnS⟩, bot A hA ⟨n, posOfMem n hnS⟩⟩
  have hcard : S.card = P.card := by
    refine Finset.card_bij
      (s := S) (t := P)
      selected
      ?_ ?_ ?_
    · intro n hnS
      have hnpos : 0 < n := posOfMem n hnS
      have hnX : n ≤ X := (Finset.mem_Icc.mp hnS).2
      have htop_cut :
          (selected n hnS).fst ∈ natCut A (D.Phi (X : ℝ)) := by
        dsimp [selected]
        exact (mem_natCut_iff (A := A) (T := D.Phi (X : ℝ))
            (a := top A hA ⟨n, hnpos⟩) hPhi_nonneg).mpr
          ⟨top_mem hA ⟨n, hnpos⟩, htop_le n hnpos hnX⟩
      have hbot_win :
          (selected n hnS).snd ∈ bottomWindow A X (selected n hnS).fst := by
        dsimp [selected]
        exact mem_bottomWindow_iff.mpr
          ⟨bot_mem hA ⟨n, hnpos⟩,
            top_sub_cutoff_le_bot_of_sub_eq_of_le
              (top_sub_bot hA ⟨n, hnpos⟩) hnpos hnX,
            bot_lt_top hA ⟨n, hnpos⟩⟩
      exact Finset.mem_sigma.mpr ⟨htop_cut, hbot_win⟩
    · intro n hnS m hmS hEq
      have hnpos : 0 < n := posOfMem n hnS
      have hmpos : 0 < m := posOfMem m hmS
      have htop_eq :
          top A hA ⟨n, hnpos⟩ = top A hA ⟨m, hmpos⟩ := by
        simpa [selected] using congrArg Sigma.fst hEq
      have hbot_eq :
          bot A hA ⟨n, hnpos⟩ = bot A hA ⟨m, hmpos⟩ := by
        simpa [selected] using congrArg Sigma.snd hEq
      have hdiff :
          top A hA ⟨n, hnpos⟩ - bot A hA ⟨n, hnpos⟩ =
            top A hA ⟨m, hmpos⟩ - bot A hA ⟨m, hmpos⟩ := by
        rw [htop_eq, hbot_eq]
      simpa [top_sub_bot hA ⟨n, hnpos⟩, top_sub_bot hA ⟨m, hmpos⟩] using hdiff
    · intro p hp
      rcases p with ⟨t, b⟩
      rcases Finset.mem_sigma.mp hp with ⟨htCut, hbWin⟩
      rcases mem_bottomWindow_iff.mp hbWin with ⟨hbA, hwin, hbt⟩
      let n := t - b
      have hnpos : 0 < n := by
        exact Nat.sub_pos_of_lt hbt
      have hnX : n ≤ X := by
        simpa [n] using sub_le_of_cutoff_sub_le hwin
      have hnS : n ∈ S := by
        exact Finset.mem_Icc.mpr ⟨hnpos, hnX⟩
      have htA : t ∈ A :=
        ((mem_natCut_iff (A := A) (T := D.Phi (X : ℝ)) (a := t) hPhi_nonneg).mp htCut).1
      have hrep : RepresentsDiff A n (t, b) := by
        exact ⟨htA, hbA, hbt, rfl⟩
      refine ⟨n, hnS, ?_⟩
      have heqpair : (t, b) = (repPair A hA ⟨n, hnpos⟩).1 :=
        repPair_eq_of_represents hA hnpos hrep
      have htop_eq : top A hA ⟨n, posOfMem n hnS⟩ = t := by
        simpa [top] using congrArg Prod.fst heqpair.symm
      have hbot_eq : bot A hA ⟨n, posOfMem n hnS⟩ = b := by
        simpa [bot] using congrArg Prod.snd heqpair.symm
      exact Sigma.ext htop_eq (heq_of_eq hbot_eq)
  calc
    X = S.card := by
      simp [S]
    _ = P.card := hcard
    _ = (∑ t ∈ natCut A (D.Phi (X : ℝ)), (bottomWindow A X t).card) := by
      simp [P, Finset.card_sigma]

/-- For a top `t ≤ X`, the bottom window is exactly the previous cut elements. -/
theorem bottomWindow_eq_filter_natCut_of_le
    {A : Set ℕ} {X t : ℕ} (htX : t ≤ X) :
    bottomWindow A X t = (natCut A (X : ℝ)).filter (fun b : ℕ => b < t) := by
  classical
  have hX_nonneg : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  ext b
  constructor
  · intro hb
    rcases mem_bottomWindow_iff.mp hb with ⟨hbA, _hwin, hbt⟩
    have hbX : b ≤ X := (Nat.le_of_lt hbt).trans htX
    have hbCut : b ∈ natCut A (X : ℝ) := by
      exact (mem_natCut_iff (A := A) (T := (X : ℝ)) (a := b) hX_nonneg).mpr
        ⟨hbA, by exact_mod_cast hbX⟩
    exact Finset.mem_filter.mpr ⟨hbCut, hbt⟩
  · intro hb
    rcases Finset.mem_filter.mp hb with ⟨hbCut, hbt⟩
    have hbA : b ∈ A :=
      ((mem_natCut_iff (A := A) (T := (X : ℝ)) (a := b) hX_nonneg).mp hbCut).1
    exact mem_bottomWindow_iff.mpr
      ⟨hbA, by simp [Nat.sub_eq_zero_of_le htX], hbt⟩

/-- A cut member is small enough for the exact bottom-window rewrite. -/
theorem bottomWindow_eq_filter_natCut_of_mem_natCut
    {A : Set ℕ} {X t : ℕ}
    (ht : t ∈ natCut A (X : ℝ)) :
    bottomWindow A X t = (natCut A (X : ℝ)).filter (fun b : ℕ => b < t) := by
  have hX_nonneg : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  have htX_real :
      (t : ℝ) ≤ (X : ℝ) :=
    ((mem_natCut_iff (A := A) (T := (X : ℝ)) (a := t) hX_nonneg).mp ht).2
  have htX : t ≤ X := by
    exact_mod_cast htX_real
  exact bottomWindow_eq_filter_natCut_of_le (A := A) htX

/-- TeX Part 4: the small-top contribution is exactly a binomial coefficient. -/
theorem small_top_sum_eq_choose (A : Set ℕ) (X : ℕ) :
    (∑ t ∈ natCut A (X : ℝ), (bottomWindow A X t).card) =
      (Ncount A (X : ℝ)).choose 2 := by
  classical
  let S : Finset ℕ := natCut A (X : ℝ)
  calc
    (∑ t ∈ natCut A (X : ℝ), (bottomWindow A X t).card)
        = ∑ t ∈ S, (S.filter fun b : ℕ => b < t).card := by
          dsimp [S]
          exact Finset.sum_congr rfl (fun t ht => by
            rw [bottomWindow_eq_filter_natCut_of_mem_natCut (A := A) (X := X) ht])
    _ = S.card.choose 2 := sum_card_filter_lt_eq_choose_two S
    _ = (Ncount A (X : ℝ)).choose 2 := by
      simp [S, Ncount]

/-- TeX Part 4: a coarse real upper bound for the small-top contribution. -/
theorem small_top_sum_le_half_ncount_sq (A : Set ℕ) (X : ℕ) :
    ((∑ t ∈ natCut A (X : ℝ), (bottomWindow A X t).card : ℕ) : ℝ) ≤
      (1 / 2 : ℝ) * (Ncount A (X : ℝ) : ℝ) ^ 2 := by
  rw [small_top_sum_eq_choose]
  have hchoose := Nat.choose_le_pow_div (α := ℝ) 2 (Ncount A (X : ℝ))
  norm_num at hchoose
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hchoose

/-- A bottom window below a top `t ≤ T` injects into the cutoff `A ∩ [1,T]`. -/
theorem bottomWindow_card_le_ncount_of_top_le
    (A : Set ℕ) {X T t : ℕ} (htT : t ≤ T) :
    (bottomWindow A X t).card ≤ Ncount A (T : ℝ) := by
  classical
  have hT_nonneg : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
  have hsubset : bottomWindow A X t ⊆ natCut A (T : ℝ) := by
    intro b hb
    rcases mem_bottomWindow_iff.mp hb with ⟨hbA, _hwin, hbt⟩
    have hbT : b ≤ T := (Nat.le_of_lt hbt).trans htT
    exact (mem_natCut_iff (A := A) (T := (T : ℝ)) (a := b) hT_nonneg).mpr
      ⟨hbA, by exact_mod_cast hbT⟩
  simpa [Ncount] using Finset.card_le_card hsubset

/-- There are at most `Z` integer tops in the short interval `(X, X+Z]`. -/
theorem short_top_count_le (A : Set ℕ) (X Z : ℕ) (M : ℝ) :
    ((natCut A M).filter (fun t : ℕ => X < t ∧ t ≤ X + Z)).card ≤ Z := by
  classical
  let short : Finset ℕ := (natCut A M).filter (fun t : ℕ => X < t ∧ t ≤ X + Z)
  have hsubset : short ⊆ Finset.Ioc X (X + Z) := by
    intro t ht
    exact Finset.mem_Ioc.mpr (Finset.mem_filter.mp ht).2
  have hcard := Finset.card_le_card hsubset
  simpa [short, Nat.card_Ioc] using hcard

/-- TeX Part 5: finite bound for the short top interval `X < t ≤ X+Z`. -/
theorem short_top_sum_le_mul_ncount (A : Set ℕ) (X Z : ℕ) (M : ℝ) :
    (∑ t ∈ (natCut A M).filter (fun t : ℕ => X < t ∧ t ≤ X + Z),
        (bottomWindow A X t).card) ≤
      Z * Ncount A ((X + Z : ℕ) : ℝ) := by
  classical
  let short : Finset ℕ := (natCut A M).filter (fun t : ℕ => X < t ∧ t ≤ X + Z)
  have hterm : ∀ t ∈ short,
      (bottomWindow A X t).card ≤ Ncount A ((X + Z : ℕ) : ℝ) := by
    intro t ht
    have htXZ : t ≤ X + Z := (Finset.mem_filter.mp ht).2.2
    exact bottomWindow_card_le_ncount_of_top_le (A := A) htXZ
  have hcard : short.card ≤ Z := short_top_count_le A X Z M
  calc
    (∑ t ∈ (natCut A M).filter (fun t : ℕ => X < t ∧ t ≤ X + Z),
        (bottomWindow A X t).card)
        = ∑ t ∈ short, (bottomWindow A X t).card := by rfl
    _ ≤ ∑ t ∈ short, Ncount A ((X + Z : ℕ) : ℝ) := Finset.sum_le_sum hterm
    _ = short.card * Ncount A ((X + Z : ℕ) : ℝ) := by simp
    _ ≤ Z * Ncount A ((X + Z : ℕ) : ℝ) := Nat.mul_le_mul_right _ hcard

/--
A single large gap pays for the right endpoint's floor value in the weighted floor integral.
-/
theorem floor_GX_le_floor_integral_on_gap
    {B : ℝ} (D : PhiPsiData B) {X y z : ℕ}
    (hXy : X ≤ y) (hyz : y < z)
    (hgap : 1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s) :
    ((⌊GX D (X : ℝ) (z : ℝ)⌋ : ℤ) : ℝ) ≤
      ∫ s in (y : ℝ)..(z : ℝ),
        D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) := by
  let gz : ℝ := ((⌊GX D (X : ℝ) (z : ℝ)⌋ : ℤ) : ℝ)
  have hyz_le_real : (y : ℝ) ≤ (z : ℝ) := Nat.cast_le.mpr hyz.le
  have hXz : X ≤ z := hXy.trans hyz.le
  have hXy_real : (X : ℝ) ≤ (y : ℝ) := Nat.cast_le.mpr hXy
  have hXz_real : (X : ℝ) ≤ (z : ℝ) := Nat.cast_le.mpr hXz
  have hgz_nonneg : 0 ≤ gz := by
    dsimp [gz]
    exact floor_GX_nonneg_of_nonneg_window D (Nat.cast_nonneg X)
      (sub_nonneg.mpr hXz_real)
  have hconst_le :
      gz ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s * gz := by
    calc
      gz = gz * 1 := by ring
      _ ≤ gz * (∫ s in (y : ℝ)..(z : ℝ), D.f s) :=
        mul_le_mul_of_nonneg_left hgap hgz_nonneg
      _ = ∫ s in (y : ℝ)..(z : ℝ), gz * D.f s := by
        rw [intervalIntegral.integral_const_mul]
      _ = ∫ s in (y : ℝ)..(z : ℝ), D.f s * gz := by
        refine intervalIntegral.integral_congr ?_
        intro s _hs
        ring
  have hmono :
      (∫ s in (y : ℝ)..(z : ℝ), D.f s * gz) ≤
        ∫ s in (y : ℝ)..(z : ℝ),
          D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) := by
    have hconst_int :
        IntervalIntegrable (fun s : ℝ => D.f s * gz)
          MeasureTheory.volume (y : ℝ) (z : ℝ) :=
      (D.f_intervalIntegrable (y : ℝ) (z : ℝ)).mul_const gz
    have hprod_int :
        IntervalIntegrable
          (fun s : ℝ => D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ))
          MeasureTheory.volume (y : ℝ) (z : ℝ) :=
      f_mul_floor_GX_intervalIntegrable_of_le D (Nat.cast_nonneg X) hXy_real hyz_le_real
    refine intervalIntegral.integral_mono_on hyz_le_real hconst_int hprod_int ?_
    intro s hs
    have hs_nonneg : 0 ≤ s := (Nat.cast_nonneg y).trans hs.1
    have hXs : (X : ℝ) ≤ s := hXy_real.trans hs.1
    have hfloor_le :
        gz ≤ ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) := by
      dsimp [gz]
      exact floor_GX_antitoneOn_Ici D (Nat.cast_nonneg X) hXs hXz_real hs.2
    exact mul_le_mul_of_nonneg_left hfloor_le (D.f_nonneg hs_nonneg)
  exact hconst_le.trans hmono

/--
Weighted finite-chain domination: all floor values in a nonempty chain are controlled by the
first floor value plus the weighted floor integral over the chain span.
-/
theorem finite_chain_floor_sum_le_endpoint_add_integral_min_to_max
    {B : ℝ} {A : Set ℕ} {Z0 X : ℕ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s) :
    ∀ S : Finset ℕ,
      ∀ hS : S.Nonempty,
      (∀ a ∈ S, a ∈ A) →
      (∀ a ∈ S, X + Z0 < a) →
        (∑ t ∈ S, ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ)) ≤
          ((⌊GX D (X : ℝ) (S.min' hS : ℝ)⌋ : ℤ) : ℝ) +
            ∫ s in (S.min' hS : ℝ)..(S.max' hS : ℝ),
              D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) := by
  classical
  intro S
  refine Finset.induction_on_max (s := S)
      (motive := fun S => ∀ hS : S.Nonempty,
        (∀ a ∈ S, a ∈ A) →
        (∀ a ∈ S, X + Z0 < a) →
          (∑ t ∈ S, ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ)) ≤
            ((⌊GX D (X : ℝ) (S.min' hS : ℝ)⌋ : ℤ) : ℝ) +
              ∫ s in (S.min' hS : ℝ)..(S.max' hS : ℝ),
                D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ)) ?_ ?_
  · intro hS
    rcases hS with ⟨x, hx⟩
    exact False.elim (Finset.notMem_empty x hx)
  · intro a S hlt ih hIns hmem hlarge
    have ha_not_mem : a ∉ S := by
      intro ha
      exact (Nat.lt_irrefl a) (hlt a ha)
    have ha_mem : a ∈ insert a S := Finset.mem_insert_self a S
    by_cases hS : S.Nonempty
    · have hmemS : ∀ x ∈ S, x ∈ A := by
        intro x hx
        exact hmem x (Finset.mem_insert.mpr (Or.inr hx))
      have hlargeS : ∀ x ∈ S, X + Z0 < x := by
        intro x hx
        exact hlarge x (Finset.mem_insert.mpr (Or.inr hx))
      have hih := ih hS hmemS hlargeS
      have hsum_insert :
          (∑ t ∈ insert a S, ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ)) =
            (∑ t ∈ S, ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ)) +
              ((⌊GX D (X : ℝ) (a : ℝ)⌋ : ℤ) : ℝ) := by
        rw [Finset.sum_insert ha_not_mem]
        ring
      have hmax_lt_a : S.max' hS < a :=
        hlt (S.max' hS) (Finset.max'_mem S hS)
      have hX_le_max : X ≤ S.max' hS := by
        have hlarge_max : X + Z0 < S.max' hS :=
          hlargeS (S.max' hS) (Finset.max'_mem S hS)
        exact (Nat.le_add_right X Z0).trans (le_of_lt hlarge_max)
      have hgap_floor :
          ((⌊GX D (X : ℝ) (a : ℝ)⌋ : ℤ) : ℝ) ≤
            ∫ s in (S.max' hS : ℝ)..(a : ℝ),
              D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) := by
        have hZ0a : Z0 < a := by
          have hXa : X + Z0 < a := hlarge a ha_mem
          exact lt_of_le_of_lt (Nat.le_add_left Z0 X) hXa
        exact floor_GX_le_floor_integral_on_gap D hX_le_max hmax_lt_a
          (hgap (S.max' hS) a
            (hmemS (S.max' hS) (Finset.max'_mem S hS))
            (hmem a ha_mem) hmax_lt_a hZ0a)
      have hmin_insert :
          (insert a S).min' hIns = S.min' hS := by
        rw [Finset.min'_insert a S hS]
        have hmin_lt_a : S.min' hS < a :=
          hlt (S.min' hS) (Finset.min'_mem S hS)
        exact min_eq_right (le_of_lt hmin_lt_a)
      have hmax_insert :
          (insert a S).max' hIns = a := by
        rw [Finset.max'_insert a S hS]
        exact max_eq_left (le_of_lt hmax_lt_a)
      have hX_le_min : X ≤ S.min' hS := by
        have hlarge_min : X + Z0 < S.min' hS :=
          hlargeS (S.min' hS) (Finset.min'_mem S hS)
        exact (Nat.le_add_right X Z0).trans (le_of_lt hlarge_min)
      have hmin_le_max : S.min' hS ≤ S.max' hS :=
        Finset.min'_le_max' S hS
      have hmax_le_a : S.max' hS ≤ a := le_of_lt hmax_lt_a
      have hint₁ :
          IntervalIntegrable
            (fun s : ℝ => D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ))
            MeasureTheory.volume (S.min' hS : ℝ) (S.max' hS : ℝ) :=
        f_mul_floor_GX_intervalIntegrable_of_le D (Nat.cast_nonneg X)
          (Nat.cast_le.mpr hX_le_min) (Nat.cast_le.mpr hmin_le_max)
      have hint₂ :
          IntervalIntegrable
            (fun s : ℝ => D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ))
            MeasureTheory.volume (S.max' hS : ℝ) (a : ℝ) :=
        f_mul_floor_GX_intervalIntegrable_of_le D (Nat.cast_nonneg X)
          (Nat.cast_le.mpr hX_le_max) (Nat.cast_le.mpr hmax_le_a)
      have hadd :
          (∫ s in (S.min' hS : ℝ)..(S.max' hS : ℝ),
              D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ)) +
            (∫ s in (S.max' hS : ℝ)..(a : ℝ),
              D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ)) =
          ∫ s in (S.min' hS : ℝ)..(a : ℝ),
              D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) :=
        intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂
      calc
        (∑ t ∈ insert a S, ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ))
            = (∑ t ∈ S, ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ)) +
                ((⌊GX D (X : ℝ) (a : ℝ)⌋ : ℤ) : ℝ) := hsum_insert
        _ ≤ (((⌊GX D (X : ℝ) (S.min' hS : ℝ)⌋ : ℤ) : ℝ) +
              ∫ s in (S.min' hS : ℝ)..(S.max' hS : ℝ),
                D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ)) +
              ∫ s in (S.max' hS : ℝ)..(a : ℝ),
                D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) :=
            add_le_add hih hgap_floor
        _ = ((⌊GX D (X : ℝ) (S.min' hS : ℝ)⌋ : ℤ) : ℝ) +
              ∫ s in (S.min' hS : ℝ)..(a : ℝ),
                D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) := by
            rw [← hadd]
            ring
        _ = ((⌊GX D (X : ℝ) ((insert a S).min' hIns : ℝ)⌋ : ℤ) : ℝ) +
              ∫ s in ((insert a S).min' hIns : ℝ)..((insert a S).max' hIns : ℝ),
                D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) := by
            rw [hmin_insert, hmax_insert]
    · have hS_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      simp

/-- Ordered large elements of `A` contribute at least one integral unit per element. -/
theorem finite_chain_card_le_integral_min_to_endpoint
    {B : ℝ} {A : Set ℕ} {Z0 : ℕ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s) :
    ∀ S : Finset ℕ,
      ∀ hS : S.Nonempty,
      (∀ a ∈ S, a ∈ A) →
      (∀ a ∈ S, Z0 < a) →
      ∀ z : ℕ,
        z ∈ A →
        (∀ a ∈ S, a < z) →
          (S.card : ℝ) ≤ ∫ s in (S.min' hS : ℝ)..(z : ℝ), D.f s := by
  classical
  intro S
  refine Finset.induction_on_max (s := S)
      (motive := fun S => ∀ hS : S.Nonempty,
        (∀ a ∈ S, a ∈ A) →
        (∀ a ∈ S, Z0 < a) →
        ∀ z : ℕ, z ∈ A → (∀ a ∈ S, a < z) →
          (S.card : ℝ) ≤ ∫ s in (S.min' hS : ℝ)..(z : ℝ), D.f s) ?_ ?_
  · intro hS
    rcases hS with ⟨x, hx⟩
    exact False.elim (Finset.notMem_empty x hx)
  · intro a S hlt ih hIns hmem hlarge z hzA htop
    have ha_not_mem : a ∉ S := by
      intro ha
      exact (Nat.lt_irrefl a) (hlt a ha)
    have ha_mem : a ∈ insert a S := Finset.mem_insert_self a S
    have haA : a ∈ A := hmem a ha_mem
    have hZ0a : Z0 < a := hlarge a ha_mem
    have ha_lt_z : a < z := htop a ha_mem
    have hgap_a_z : 1 ≤ ∫ s in (a : ℝ)..(z : ℝ), D.f s :=
      hgap a z haA hzA ha_lt_z (lt_trans hZ0a ha_lt_z)
    by_cases hS : S.Nonempty
    · have hcard_insert : ((insert a S).card : ℝ) = (S.card : ℝ) + 1 := by
        rw [Finset.card_insert_of_notMem ha_not_mem, Nat.cast_add]
        norm_num
      have hmemS : ∀ x ∈ S, x ∈ A := by
        intro x hx
        exact hmem x (Finset.mem_insert.mpr (Or.inr hx))
      have hlargeS : ∀ x ∈ S, Z0 < x := by
        intro x hx
        exact hlarge x (Finset.mem_insert.mpr (Or.inr hx))
      have hih_a :
          (S.card : ℝ) ≤ ∫ s in (S.min' hS : ℝ)..(a : ℝ), D.f s :=
        ih hS hmemS hlargeS a haA hlt
      have hadd :
          (∫ s in (S.min' hS : ℝ)..(a : ℝ), D.f s) +
              (∫ s in (a : ℝ)..(z : ℝ), D.f s) =
            ∫ s in (S.min' hS : ℝ)..(z : ℝ), D.f s :=
        intervalIntegral.integral_add_adjacent_intervals
          (D.f_intervalIntegrable (S.min' hS : ℝ) (a : ℝ))
          (D.f_intervalIntegrable (a : ℝ) (z : ℝ))
      have hmin_insert :
          (insert a S).min' hIns = S.min' hS := by
        rw [Finset.min'_insert a S hS]
        have hmin_lt_a : S.min' hS < a :=
          hlt (S.min' hS) (Finset.min'_mem S hS)
        exact min_eq_right (le_of_lt hmin_lt_a)
      calc
        ((insert a S).card : ℝ) = (S.card : ℝ) + 1 := hcard_insert
        _ ≤ (∫ s in (S.min' hS : ℝ)..(a : ℝ), D.f s) +
              (∫ s in (a : ℝ)..(z : ℝ), D.f s) := add_le_add hih_a hgap_a_z
        _ = ∫ s in (S.min' hS : ℝ)..(z : ℝ), D.f s := hadd
        _ = ∫ s in ((insert a S).min' hIns : ℝ)..(z : ℝ), D.f s := by
          rw [hmin_insert]
    · have hS_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      have hcard_one : ((insert a S).card : ℝ) = 1 := by
        simp [hS_empty]
      have hmin_insert : (insert a S).min' hIns = a := by
        subst S
        simp
      calc
        ((insert a S).card : ℝ) = 1 := hcard_one
        _ ≤ ∫ s in (a : ℝ)..(z : ℝ), D.f s := hgap_a_z
        _ = ∫ s in ((insert a S).min' hIns : ℝ)..(z : ℝ), D.f s := by
          rw [hmin_insert]

/-- Extend the finite-chain integral bound down to any lower endpoint below the chain. -/
theorem finite_chain_card_le_integral_lower_to_endpoint
    {B : ℝ} {A : Set ℕ} {Z0 z : ℕ} {L : ℝ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s)
    (S : Finset ℕ)
    (hmem : ∀ a ∈ S, a ∈ A)
    (hlarge : ∀ a ∈ S, Z0 < a)
    (hzA : z ∈ A)
    (hSz : ∀ a ∈ S, a < z)
    (hL_nonneg : 0 ≤ L)
    (hLz : L ≤ (z : ℝ))
    (hL_le : ∀ a ∈ S, L ≤ (a : ℝ)) :
    (S.card : ℝ) ≤ ∫ s in L..(z : ℝ), D.f s := by
  classical
  by_cases hS : S.Nonempty
  · have hchain_le :
        (S.card : ℝ) ≤ ∫ s in (S.min' hS : ℝ)..(z : ℝ), D.f s :=
      finite_chain_card_le_integral_min_to_endpoint D hgap S hS hmem hlarge z hzA hSz
    have hmin_mem : S.min' hS ∈ S := Finset.min'_mem S hS
    have hL_le_min : L ≤ (S.min' hS : ℝ) := hL_le (S.min' hS) hmin_mem
    have hint_L_min_nonneg :
        0 ≤ ∫ s in L..(S.min' hS : ℝ), D.f s :=
      intervalIntegral.integral_nonneg hL_le_min
        (fun s hs => D.f_nonneg (hL_nonneg.trans hs.1))
    have hadd :
        (∫ s in L..(S.min' hS : ℝ), D.f s) +
            (∫ s in (S.min' hS : ℝ)..(z : ℝ), D.f s) =
          ∫ s in L..(z : ℝ), D.f s :=
      intervalIntegral.integral_add_adjacent_intervals
        (D.f_intervalIntegrable L (S.min' hS : ℝ))
        (D.f_intervalIntegrable (S.min' hS : ℝ) (z : ℝ))
    have hle_total :
        (∫ s in (S.min' hS : ℝ)..(z : ℝ), D.f s) ≤
          ∫ s in L..(z : ℝ), D.f s := by
      have hle_add :
          (∫ s in (S.min' hS : ℝ)..(z : ℝ), D.f s) ≤
            (∫ s in L..(S.min' hS : ℝ), D.f s) +
              (∫ s in (S.min' hS : ℝ)..(z : ℝ), D.f s) :=
        le_add_of_nonneg_left hint_L_min_nonneg
      exact hle_add.trans_eq hadd
    exact hchain_le.trans hle_total
  · have hS_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hcard_zero : (S.card : ℝ) = 0 := by
      simp [hS_empty]
    have hint_nonneg : 0 ≤ ∫ s in L..(z : ℝ), D.f s :=
      intervalIntegral.integral_nonneg hLz
        (fun s hs => D.f_nonneg (hL_nonneg.trans hs.1))
    simpa [hcard_zero] using hint_nonneg

/-- TeX Part 5: a large top has at most the integral mass in its bottom window. -/
theorem bottomWindow_card_le_GX_of_large_top
    {B : ℝ} {A : Set ℕ} {Z0 X t : ℕ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s)
    (htA : t ∈ A) (hlarge : X + Z0 < t) :
    ((bottomWindow A X t).card : ℝ) ≤ GX D (X : ℝ) (t : ℝ) := by
  classical
  let S : Finset ℕ := bottomWindow A X t
  have hX_le_t : X ≤ t :=
    le_of_lt (lt_of_le_of_lt (Nat.le_add_right X Z0) hlarge)
  have hlower_eq : ((t - X : ℕ) : ℝ) = (t : ℝ) - (X : ℝ) :=
    Nat.cast_sub hX_le_t
  have hle_lower_t : (t : ℝ) - (X : ℝ) ≤ (t : ℝ) := by
    have hX_nonneg : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    linarith
  have hlower_nonneg : 0 ≤ (t : ℝ) - (X : ℝ) :=
    sub_nonneg.mpr (Nat.cast_le.mpr hX_le_t)
  have hmemA : ∀ a ∈ S, a ∈ A := by
    intro a ha
    exact (mem_bottomWindow_iff.mp (by simpa [S] using ha)).1
  have hlargeS : ∀ a ∈ S, Z0 < a := by
    intro a ha
    rcases mem_bottomWindow_iff.mp (by simpa [S] using ha) with ⟨_haA, hwin, _hat⟩
    have hZX_lt_tX : Z0 < t - X := by
      rw [Nat.lt_sub_iff_add_lt]
      simpa [add_comm] using hlarge
    exact lt_of_lt_of_le hZX_lt_tX hwin
  have htop : ∀ a ∈ S, a < t := by
    intro a ha
    exact (mem_bottomWindow_iff.mp (by simpa [S] using ha)).2.2
  have hlower_le : ∀ a ∈ S, (t : ℝ) - (X : ℝ) ≤ (a : ℝ) := by
    intro a ha
    have hwin : t - X ≤ a :=
      (mem_bottomWindow_iff.mp (by simpa [S] using ha)).2.1
    rw [← hlower_eq]
    exact Nat.cast_le.mpr hwin
  simpa [S, GX] using
    (finite_chain_card_le_integral_lower_to_endpoint
      D hgap S hmemA hlargeS htA htop hlower_nonneg hle_lower_t hlower_le)

/-- Integer-floor form of the large-top bottom-window bound. -/
theorem bottomWindow_card_le_floor_GX_of_large_top
    {B : ℝ} {A : Set ℕ} {Z0 X t : ℕ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s)
    (htA : t ∈ A) (hlarge : X + Z0 < t) :
    ((bottomWindow A X t).card : ℤ) ≤
      ⌊GX D (X : ℝ) (t : ℝ)⌋ := by
  exact Int.le_floor.mpr
    (bottomWindow_card_le_GX_of_large_top D hgap htA hlarge)

/-- Sum the pointwise large-top floor bound over a finite cutoff. -/
theorem large_top_sum_le_sum_floor_GX
    {B : ℝ} (A : Set ℕ) (D : PhiPsiData B) (X Z0 : ℕ) (M : ℝ)
    (hpoint : ∀ t : ℕ, t ∈ natCut A M → X + Z0 < t →
      ((bottomWindow A X t).card : ℤ) ≤
        ⌊GX D (X : ℝ) (t : ℝ)⌋) :
    ((∑ t ∈ (natCut A M).filter (fun t : ℕ => X + Z0 < t),
        (bottomWindow A X t).card : ℕ) : ℝ) ≤
      ∑ t ∈ (natCut A M).filter (fun t : ℕ => X + Z0 < t),
        ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ) := by
  classical
  have hint :
      (∑ t ∈ (natCut A M).filter (fun t : ℕ => X + Z0 < t),
          ((bottomWindow A X t).card : ℤ)) ≤
        ∑ t ∈ (natCut A M).filter (fun t : ℕ => X + Z0 < t),
          ⌊GX D (X : ℝ) (t : ℝ)⌋ := by
    exact Finset.sum_le_sum (fun t ht => by
      have htCut : t ∈ natCut A M := (Finset.mem_filter.mp ht).1
      have htLarge : X + Z0 < t := (Finset.mem_filter.mp ht).2
      exact hpoint t htCut htLarge)
  exact_mod_cast hint

/-- TeX Part 5: finite large-top contribution bounded by the floor sum. -/
theorem large_top_sum_le_sum_floor_GX_of_gap
    {B : ℝ} {A : Set ℕ} {Z0 : ℕ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s)
    (X : ℕ) (M : ℝ) :
    ((∑ t ∈ (natCut A M).filter (fun t : ℕ => X + Z0 < t),
        (bottomWindow A X t).card : ℕ) : ℝ) ≤
      ∑ t ∈ (natCut A M).filter (fun t : ℕ => X + Z0 < t),
        ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ) := by
  classical
  exact large_top_sum_le_sum_floor_GX A D X Z0 M (fun t htCut htLarge => by
    have htA : t ∈ A := by
      simpa [natCut] using (Finset.mem_filter.mp htCut).2
    exact bottomWindow_card_le_floor_GX_of_large_top D hgap htA htLarge)

/-- Split a natural-valued finite sum into small, short, and large top ranges. -/
theorem finset_sum_nat_split_three
    (S : Finset ℕ) (X Z : ℕ) (f : ℕ → ℕ) :
    (∑ t ∈ S, f t) =
      (∑ t ∈ S.filter (fun t : ℕ => t ≤ X), f t) +
        (∑ t ∈ S.filter (fun t : ℕ => X < t ∧ t ≤ X + Z), f t) +
          (∑ t ∈ S.filter (fun t : ℕ => X + Z < t), f t) := by
  classical
  let small : Finset ℕ := S.filter (fun t : ℕ => t ≤ X)
  let rest : Finset ℕ := S.filter (fun t : ℕ => ¬ t ≤ X)
  let short : Finset ℕ := rest.filter (fun t : ℕ => t ≤ X + Z)
  let large : Finset ℕ := rest.filter (fun t : ℕ => ¬ t ≤ X + Z)
  have hsplit_small :
      (∑ t ∈ small, f t) + (∑ t ∈ rest, f t) = ∑ t ∈ S, f t := by
    simpa [small, rest] using
      (Finset.sum_filter_add_sum_filter_not
        (s := S) (p := fun t : ℕ => t ≤ X) (f := f))
  have hsplit_rest :
      (∑ t ∈ short, f t) + (∑ t ∈ large, f t) = ∑ t ∈ rest, f t := by
    simpa [short, large] using
      (Finset.sum_filter_add_sum_filter_not
        (s := rest) (p := fun t : ℕ => t ≤ X + Z) (f := f))
  have hshort :
      short = S.filter (fun t : ℕ => X < t ∧ t ≤ X + Z) := by
    ext t
    simp [short, rest, not_le, and_assoc]
  have hlarge :
      large = S.filter (fun t : ℕ => X + Z < t) := by
    ext t
    constructor
    · intro ht
      rcases Finset.mem_filter.mp ht with ⟨htRest, htNotLe⟩
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp htRest).1, Nat.lt_of_not_ge htNotLe⟩
    · intro ht
      rcases Finset.mem_filter.mp ht with ⟨htS, htLarge⟩
      have hXlt : X < t := lt_of_le_of_lt (Nat.le_add_right X Z) htLarge
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨htS, Nat.not_le_of_gt hXlt⟩,
          Nat.not_le_of_gt htLarge⟩
  calc
    (∑ t ∈ S, f t) =
        (∑ t ∈ small, f t) + (∑ t ∈ rest, f t) := hsplit_small.symm
    _ = (∑ t ∈ small, f t) +
          ((∑ t ∈ short, f t) + (∑ t ∈ large, f t)) := by
        rw [hsplit_rest]
    _ = (∑ t ∈ small, f t) + (∑ t ∈ short, f t) +
          (∑ t ∈ large, f t) := by
        rw [add_assoc]
    _ = (∑ t ∈ S.filter (fun t : ℕ => t ≤ X), f t) +
          (∑ t ∈ S.filter (fun t : ℕ => X < t ∧ t ≤ X + Z), f t) +
            (∑ t ∈ S.filter (fun t : ℕ => X + Z < t), f t) := by
        simp [small, hshort, hlarge]

/-- TeX Parts 3--5: finite top counting bounded by the three component estimates. -/
theorem top_counting_three_part_bound
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B)
    {Z0 : ℕ}
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (X : ℝ) ≤
        (1 / 2 : ℝ) * (Ncount A (X : ℝ) : ℝ) ^ 2 +
          (Z0 : ℝ) * (Ncount A (((X + Z0 : ℕ) : ℝ)) : ℝ) +
            ∑ t ∈ (natCut A (D.Phi (X : ℝ))).filter (fun t : ℕ => X + Z0 < t),
              ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ) := by
  classical
  filter_upwards [top_counting_identity A hA D hupper] with X hident
  let M : ℝ := D.Phi (X : ℝ)
  let S : Finset ℕ := natCut A M
  let f : ℕ → ℕ := fun t => (bottomWindow A X t).card
  let small : Finset ℕ := S.filter (fun t : ℕ => t ≤ X)
  let short : Finset ℕ := S.filter (fun t : ℕ => X < t ∧ t ≤ X + Z0)
  let large : Finset ℕ := S.filter (fun t : ℕ => X + Z0 < t)
  have hsmall_subset : small ⊆ natCut A (X : ℝ) := by
    intro t ht
    have hX_nonneg : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
    rcases Finset.mem_filter.mp ht with ⟨htS, htX⟩
    have htA : t ∈ A := by
      simpa [S, M, natCut] using (Finset.mem_filter.mp htS).2
    exact (mem_natCut_iff (A := A) (T := (X : ℝ)) (a := t) hX_nonneg).mpr
      ⟨htA, by exact_mod_cast htX⟩
  have hsmall_nat :
      (∑ t ∈ small, f t) ≤
        ∑ t ∈ natCut A (X : ℝ), (bottomWindow A X t).card := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsmall_subset
      (fun _t _ht _hnot => Nat.zero_le _)
  have hsmall_real :
      ((∑ t ∈ small, f t : ℕ) : ℝ) ≤
        (1 / 2 : ℝ) * (Ncount A (X : ℝ) : ℝ) ^ 2 := by
    have h1 :
        ((∑ t ∈ small, f t : ℕ) : ℝ) ≤
          ((∑ t ∈ natCut A (X : ℝ), (bottomWindow A X t).card : ℕ) : ℝ) := by
      exact_mod_cast hsmall_nat
    exact h1.trans (small_top_sum_le_half_ncount_sq A X)
  have hshort_nat :
      (∑ t ∈ short, f t) ≤
        Z0 * Ncount A (((X + Z0 : ℕ) : ℝ)) := by
    simpa [short, S, M, f] using short_top_sum_le_mul_ncount A X Z0 M
  have hshort_real :
      ((∑ t ∈ short, f t : ℕ) : ℝ) ≤
        (Z0 : ℝ) * (Ncount A (((X + Z0 : ℕ) : ℝ)) : ℝ) := by
    exact_mod_cast hshort_nat
  have hlarge_real :
      ((∑ t ∈ large, f t : ℕ) : ℝ) ≤
        ∑ t ∈ (natCut A (D.Phi (X : ℝ))).filter (fun t : ℕ => X + Z0 < t),
          ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ) := by
    simpa [large, S, M, f] using
      large_top_sum_le_sum_floor_GX_of_gap (A := A) D hgap X M
  have hsplit :
      (∑ t ∈ S, f t) =
        (∑ t ∈ small, f t) + (∑ t ∈ short, f t) + (∑ t ∈ large, f t) := by
    simpa [small, short, large] using finset_sum_nat_split_three S X Z0 f
  have hidentS : X = ∑ t ∈ S, f t := by
    simpa [S, M, f] using hident
  calc
    (X : ℝ) =
        (((∑ t ∈ small, f t) + (∑ t ∈ short, f t) + (∑ t ∈ large, f t) : ℕ) : ℝ) := by
      exact_mod_cast (by rw [hidentS, hsplit])
    _ = ((∑ t ∈ small, f t : ℕ) : ℝ) +
          ((∑ t ∈ short, f t : ℕ) : ℝ) +
            ((∑ t ∈ large, f t : ℕ) : ℝ) := by
        norm_num [Nat.cast_add]
    _ ≤ (1 / 2 : ℝ) * (Ncount A (X : ℝ) : ℝ) ^ 2 +
          (Z0 : ℝ) * (Ncount A (((X + Z0 : ℕ) : ℝ)) : ℝ) +
            ∑ t ∈ (natCut A (D.Phi (X : ℝ))).filter (fun t : ℕ => X + Z0 < t),
              ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ) := by
        exact add_le_add (add_le_add hsmall_real hshort_real) hlarge_real

/-- Three-part top-counting bound with the gap threshold supplied by `gap_integral_ge_one`. -/
theorem exists_top_counting_three_part_bound
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∃ Z0 : ℕ,
      ∀ᶠ X : ℕ in Filter.atTop,
        (X : ℝ) ≤
          (1 / 2 : ℝ) * (Ncount A (X : ℝ) : ℝ) ^ 2 +
            (Z0 : ℝ) * (Ncount A (((X + Z0 : ℕ) : ℝ)) : ℝ) +
              ∑ t ∈ (natCut A (D.Phi (X : ℝ))).filter (fun t : ℕ => X + Z0 < t),
                ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ) := by
  rcases gap_integral_ge_one A hA D hupper with ⟨Z0, hgap⟩
  exact ⟨Z0, top_counting_three_part_bound A hA D hupper hgap⟩

/-- The finite small-top and short-interval part after splitting by top size. -/
noncomputable def smallShortMajorant
    (A : Set ℕ) (Z0 X : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (Ncount A (X : ℝ) : ℝ) ^ 2 +
    (Z0 : ℝ) * (Ncount A (((X + Z0 : ℕ) : ℝ)) : ℝ)

/-- The finite large-top floor sum after splitting by top size. -/
noncomputable def largeFloorSum
    {B : ℝ} (A : Set ℕ) (D : PhiPsiData B) (Z0 X : ℕ) : ℝ :=
  ∑ t ∈ (natCut A (D.Phi (X : ℝ))).filter (fun t : ℕ => X + Z0 < t),
    ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ)

/-- The large-top floor sum has nonnegative terms on its defining range. -/
theorem largeFloorSum_nonneg
    {B : ℝ} (A : Set ℕ) (D : PhiPsiData B) (Z0 X : ℕ) :
    0 ≤ largeFloorSum A D Z0 X := by
  classical
  unfold largeFloorSum
  refine Finset.sum_nonneg ?_
  intro t ht
  have hlarge : X + Z0 < t := (Finset.mem_filter.mp ht).2
  have hXt : X ≤ t :=
    le_of_lt (lt_of_le_of_lt (Nat.le_add_right X Z0) hlarge)
  have hlower : 0 ≤ (t : ℝ) - (X : ℝ) :=
    sub_nonneg.mpr (Nat.cast_le.mpr hXt)
  exact floor_GX_nonneg_of_nonneg_window D (Nat.cast_nonneg X) hlower

/-- Dropping the floor only increases each term of the large-top sum. -/
theorem largeFloorSum_le_largeGXSum
    {B : ℝ} (A : Set ℕ) (D : PhiPsiData B) (Z0 X : ℕ) :
    largeFloorSum A D Z0 X ≤
      ∑ t ∈ (natCut A (D.Phi (X : ℝ))).filter (fun t : ℕ => X + Z0 < t),
        GX D (X : ℝ) (t : ℝ) := by
  classical
  unfold largeFloorSum
  exact Finset.sum_le_sum (fun t _ht => floor_GX_le_GX D (X : ℝ) (t : ℝ))

/--
The large finite floor sum is bounded by the continuous floor integral, losing only the first
endpoint term.
-/
theorem largeFloorSum_le_I_add_floor_integral
    {B : ℝ} {A : Set ℕ} {Z0 X : ℕ}
    (D : PhiPsiData B)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s)
    (hXPhi : (X : ℝ) ≤ D.Phi (X : ℝ)) :
    largeFloorSum A D Z0 X ≤
      I D (X : ℝ) +
        ∫ s in (X : ℝ)..D.Phi (X : ℝ),
          D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) := by
  classical
  let S : Finset ℕ :=
    (natCut A (D.Phi (X : ℝ))).filter (fun t : ℕ => X + Z0 < t)
  have hPhi_nonneg : 0 ≤ D.Phi (X : ℝ) :=
    (Nat.cast_nonneg X).trans hXPhi
  have hI_nonneg : 0 ≤ I D (X : ℝ) := by
    unfold I
    exact intervalIntegral.integral_nonneg (Nat.cast_nonneg X)
      (fun s hs => D.f_nonneg hs.1)
  have hfloor_integrand_nonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (X : ℝ) (D.Phi (X : ℝ)))]
        fun s : ℝ => D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) := by
    rw [Filter.EventuallyLE]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine ae_of_all MeasureTheory.volume ?_
    intro s hs
    have hs_nonneg : 0 ≤ s := (Nat.cast_nonneg X).trans hs.1.le
    have hfloor_nonneg :
        0 ≤ ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) :=
      floor_GX_nonneg_of_nonneg_window D (Nat.cast_nonneg X)
        (sub_nonneg.mpr hs.1.le)
    exact mul_nonneg (D.f_nonneg hs_nonneg) hfloor_nonneg
  have hfloor_int :
      IntervalIntegrable
        (fun s : ℝ => D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ))
        MeasureTheory.volume (X : ℝ) (D.Phi (X : ℝ)) :=
    f_mul_floor_GX_intervalIntegrable D (Nat.cast_nonneg X) hXPhi
  by_cases hS : S.Nonempty
  · have hmemS : ∀ a ∈ S, a ∈ A := by
      intro a ha
      have haCut : a ∈ natCut A (D.Phi (X : ℝ)) := (Finset.mem_filter.mp ha).1
      exact ((mem_natCut_iff (A := A) (T := D.Phi (X : ℝ)) (a := a) hPhi_nonneg).mp
        haCut).1
    have hlargeS : ∀ a ∈ S, X + Z0 < a := by
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    have hchain :=
      finite_chain_floor_sum_le_endpoint_add_integral_min_to_max
        D hgap S hS hmemS hlargeS
    have hmin_mem : S.min' hS ∈ S := Finset.min'_mem S hS
    have hmax_mem : S.max' hS ∈ S := Finset.max'_mem S hS
    have hX_le_min : X ≤ S.min' hS := by
      have hlarge_min : X + Z0 < S.min' hS := hlargeS (S.min' hS) hmin_mem
      exact (Nat.le_add_right X Z0).trans (le_of_lt hlarge_min)
    have hmin_le_max : S.min' hS ≤ S.max' hS :=
      Finset.min'_le_max' S hS
    have hmax_le_Phi : (S.max' hS : ℝ) ≤ D.Phi (X : ℝ) := by
      have hmaxCut : S.max' hS ∈ natCut A (D.Phi (X : ℝ)) :=
        (Finset.mem_filter.mp hmax_mem).1
      exact ((mem_natCut_iff (A := A) (T := D.Phi (X : ℝ))
        (a := S.max' hS) hPhi_nonneg).mp hmaxCut).2
    have hendpoint :
        ((⌊GX D (X : ℝ) (S.min' hS : ℝ)⌋ : ℤ) : ℝ) ≤ I D (X : ℝ) :=
      floor_GX_le_I_of_nonneg_window D (Nat.cast_nonneg X)
        (sub_nonneg.mpr (Nat.cast_le.mpr hX_le_min))
    have hintegral_mono :
        (∫ s in (S.min' hS : ℝ)..(S.max' hS : ℝ),
          D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ)) ≤
        ∫ s in (X : ℝ)..D.Phi (X : ℝ),
          D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) := by
      exact intervalIntegral.integral_mono_interval
        (Nat.cast_le.mpr hX_le_min)
        (Nat.cast_le.mpr hmin_le_max)
        hmax_le_Phi
        hfloor_integrand_nonneg
        hfloor_int
    calc
      largeFloorSum A D Z0 X =
          ∑ t ∈ S, ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ) := by
        rfl
      _ ≤ ((⌊GX D (X : ℝ) (S.min' hS : ℝ)⌋ : ℤ) : ℝ) +
            ∫ s in (S.min' hS : ℝ)..(S.max' hS : ℝ),
              D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) := hchain
      _ ≤ I D (X : ℝ) +
            ∫ s in (X : ℝ)..D.Phi (X : ℝ),
              D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) :=
        add_le_add hendpoint hintegral_mono
  · have hS_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hlarge_zero : largeFloorSum A D Z0 X = 0 := by
      unfold largeFloorSum
      simpa [S] using congrArg (fun T : Finset ℕ =>
        ∑ t ∈ T, ((⌊GX D (X : ℝ) (t : ℝ)⌋ : ℤ) : ℝ)) hS_empty
    have hintegral_nonneg :
        0 ≤ ∫ s in (X : ℝ)..D.Phi (X : ℝ),
          D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) := by
      exact intervalIntegral.integral_nonneg hXPhi (fun s hs => by
        have hs_nonneg : 0 ≤ s := (Nat.cast_nonneg X).trans hs.1
        have hfloor_nonneg :
            0 ≤ ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) :=
          floor_GX_nonneg_of_nonneg_window D (Nat.cast_nonneg X)
            (sub_nonneg.mpr hs.1)
        exact mul_nonneg (D.f_nonneg hs_nonneg) hfloor_nonneg)
    rw [hlarge_zero]
    exact add_nonneg hI_nonneg hintegral_nonneg

/-- Natural-tail form of the exact continuous floor-integral identity. -/
theorem eventually_JB_sub_Efloor_nat_eq_floor_integral
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    ∀ᶠ X : ℕ in Filter.atTop,
      JB D (X : ℝ) - Efloor D (X : ℝ) -
          (1 / 2 : ℝ) * (I D (X : ℝ)) ^ 2 =
        ∫ t in (X : ℝ)..D.Phi (X : ℝ),
          D.f t * ((⌊GX D (X : ℝ) t⌋ : ℤ) : ℝ) := by
  filter_upwards [eventually_natCast_le_Phi A hA D hupper] with X hXPhi
  exact JB_sub_Efloor_sub_half_I_sq_eq_floor_integral_of_nonneg D
    (Nat.cast_nonneg X) hXPhi

/-- The full right side after finite small/short/large top splitting. -/
noncomputable def threePartMajorant
    {B : ℝ} (A : Set ℕ) (D : PhiPsiData B) (Z0 X : ℕ) : ℝ :=
  smallShortMajorant A Z0 X + largeFloorSum A D Z0 X

/-- The natural scale `X / log X` tends to infinity. -/
theorem scaleNat_tendsto_atTop :
    Tendsto scaleNat Filter.atTop Filter.atTop := by
  have hreal : Tendsto (fun x : ℝ => x / Real.log x) Filter.atTop Filter.atTop := by
    have hratio0 : Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (𝓝 0) := by
      simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hratio_pos : ∀ᶠ x : ℝ in Filter.atTop, 0 < Real.log x / x := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact div_pos (Real.log_pos hx) (by linarith)
    have hratioGT : Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (𝓝[>] 0) := by
      exact tendsto_inf.2 ⟨hratio0, tendsto_principal.mpr hratio_pos⟩
    have hinv : Tendsto (fun x : ℝ => (Real.log x / x)⁻¹) Filter.atTop Filter.atTop :=
      hratioGT.inv_tendsto_nhdsGT_zero
    refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    field_simp [hx0, hlog0]
  simpa [scaleNat] using hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Constants are negligible compared to `scaleNat`. -/
theorem const_isLittleO_scaleNat (c : ℝ) :
    (fun _ : ℕ => c) =o[Filter.atTop] scaleNat := by
  exact isLittleO_const_left.mpr
    (Or.inr (tendsto_norm_atTop_atTop.comp scaleNat_tendsto_atTop))

/-- The real square-root function is `o(id)` at infinity. -/
theorem sqrt_isLittleO_id_atTop :
    Real.sqrt =o[Filter.atTop] (fun x : ℝ => x) := by
  refine IsLittleO.of_tendsto_div_atTop ?_
  refine Real.tendsto_sqrt_atTop.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have h : x / Real.sqrt x = Real.sqrt x := by
    rw [div_eq_iff (Real.sqrt_ne_zero'.mpr hx)]
    rw [mul_comm, ← sq]
    exact (Real.sq_sqrt hx.le).symm
  exact h.symm

/-- Consequently, `sqrt scaleNat` is negligible compared to `scaleNat`. -/
theorem sqrt_scaleNat_isLittleO :
    (fun X : ℕ => Real.sqrt (scaleNat X)) =o[Filter.atTop] scaleNat := by
  simpa [Function.comp_def] using
    sqrt_isLittleO_id_atTop.comp_tendsto scaleNat_tendsto_atTop

/-- The first-order model for `I(X)` is negligible compared to `scaleNat X`. -/
theorem integral_model_nat_isLittleO_scaleNat :
    (fun X : ℕ => 2 * Real.sqrt (2 * lam * (X : ℝ) / Real.log (X : ℝ)))
      =o[Filter.atTop] scaleNat := by
  have hconst :
      (fun X : ℕ => (2 * Real.sqrt (2 * lam)) * Real.sqrt (scaleNat X))
        =o[Filter.atTop] scaleNat := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      sqrt_scaleNat_isLittleO.const_smul_left (2 * Real.sqrt (2 * lam))
  refine hconst.congr' ?_ Filter.EventuallyEq.rfl
  have hlam_nonneg : 0 ≤ 2 * lam := by
    have : 0 < lam := by
      unfold lam
      positivity
    positivity
  filter_upwards with X
  have harg : 2 * lam * (X : ℝ) / Real.log (X : ℝ) = (2 * lam) * scaleNat X := by
    rw [scaleNat]
    ring
  rw [harg, Real.sqrt_mul hlam_nonneg]
  ring

/-- The integral `I(X)` is negligible compared to `scaleNat X` on natural inputs. -/
theorem integral_nat_isLittleO_scaleNat
    {B : ℝ} (D : PhiPsiData B) :
    (fun X : ℕ => I D (X : ℝ)) =o[Filter.atTop] scaleNat := by
  have hI_equiv :
      (fun X : ℕ => I D (X : ℝ)) ~[Filter.atTop]
        (fun X : ℕ => 2 * Real.sqrt (2 * lam * (X : ℝ) / Real.log (X : ℝ))) := by
    simpa [Function.comp_def] using
      (integral_f_asymptotic D).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  exact hI_equiv.trans_isLittleO integral_model_nat_isLittleO_scaleNat

/-- A fixed natural shift preserves the natural scale up to big-O. -/
theorem scaleNat_add_isBigO (Z0 : ℕ) :
    (fun X : ℕ => scaleNat (X + Z0)) =O[Filter.atTop] scaleNat := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [Ici_mem_atTop (max 2 Z0)] with X hX
  have htwo_le_X : 2 ≤ X := (le_max_left 2 Z0).trans hX
  have hZ_le_X : Z0 ≤ X := (le_max_right 2 Z0).trans hX
  have hX_pos_real : 0 < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) htwo_le_X)
  have hone_lt_X_real : (1 : ℝ) < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) htwo_le_X)
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos hone_lt_X_real
  have hX_le_shift_nat : X ≤ X + Z0 := Nat.le_add_right X Z0
  have hX_le_shift : (X : ℝ) ≤ ((X + Z0 : ℕ) : ℝ) := by
    exact_mod_cast hX_le_shift_nat
  have hlog_le : Real.log (X : ℝ) ≤ Real.log ((X + Z0 : ℕ) : ℝ) :=
    Real.log_le_log hX_pos_real hX_le_shift
  have hnum_le_nat : X + Z0 ≤ 2 * X := by omega
  have hnum_le : ((X + Z0 : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
    exact_mod_cast hnum_le_nat
  have hnum_nonneg : 0 ≤ 2 * (X : ℝ) := by positivity
  have hshift_le : scaleNat (X + Z0) ≤ 2 * scaleNat X := by
    rw [scaleNat, scaleNat]
    calc
      (((X + Z0 : ℕ) : ℝ)) / Real.log (((X + Z0 : ℕ) : ℝ))
          ≤ (2 * (X : ℝ)) / Real.log (((X + Z0 : ℕ) : ℝ)) :=
            div_le_div_of_nonneg_right hnum_le (le_of_lt (lt_of_lt_of_le hlogX_pos hlog_le))
      _ ≤ (2 * (X : ℝ)) / Real.log (X : ℝ) :=
            div_le_div_of_nonneg_left hnum_nonneg hlogX_pos hlog_le
      _ = 2 * ((X : ℝ) / Real.log (X : ℝ)) := by ring
  have hshift_pos : 0 ≤ scaleNat (X + Z0) := by
    rw [scaleNat]
    positivity
  have hscale_pos : 0 ≤ scaleNat X := by
    rw [scaleNat]
    positivity
  rw [Real.norm_of_nonneg hshift_pos, Real.norm_of_nonneg hscale_pos]
  exact hshift_le

/-- The integral `I(X+Z0)` is negligible compared to the unshifted natural scale. -/
theorem integral_nat_add_isLittleO_scaleNat
    {B : ℝ} (D : PhiPsiData B) (Z0 : ℕ) :
    (fun X : ℕ => I D (((X + Z0 : ℕ) : ℝ))) =o[Filter.atTop] scaleNat := by
  have hcomp :=
    (integral_nat_isLittleO_scaleNat D).comp_tendsto (Filter.tendsto_add_atTop_nat Z0)
  exact hcomp.trans_isBigO (scaleNat_add_isBigO Z0)

/--
Named interface for the small-top and fixed-width short-top error estimates.

This packages:

* `(1/2) * N(X)^2 ≤ (1/2) * I(X)^2 + o(scaleNat)`;
* `Z0 * N(X+Z0) = o(scaleNat)`.
-/
theorem small_short_error_bound
    {B : ℝ} (A : Set ℕ) (_hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (_hupper : EventuallyUpperBound A _hA B)
    (Z0 : ℕ) :
    ∃ err : ℕ → ℝ,
      err =o[Filter.atTop] scaleNat ∧
      ∀ᶠ X : ℕ in Filter.atTop,
        smallShortMajorant A Z0 X ≤
          (1 / 2 : ℝ) * (I D (X : ℝ)) ^ 2 + err X := by
  rcases counting_function_bound A _hA D _hupper with ⟨C, hcount⟩
  let err : ℕ → ℝ := fun X =>
    C * I D (X : ℝ) + (1 / 2 : ℝ) * C ^ 2 +
      (Z0 : ℝ) * (C + I D (((X + Z0 : ℕ) : ℝ)))
  refine ⟨err, ?_, ?_⟩
  · have hI_o : (fun X : ℕ => I D (X : ℝ)) =o[Filter.atTop] scaleNat :=
      integral_nat_isLittleO_scaleNat D
    have hIshift_o :
        (fun X : ℕ => I D (((X + Z0 : ℕ) : ℝ))) =o[Filter.atTop] scaleNat :=
      integral_nat_add_isLittleO_scaleNat D Z0
    have hC_I : (fun X : ℕ => C * I D (X : ℝ)) =o[Filter.atTop] scaleNat :=
      hI_o.const_mul_left C
    have hC2 : (fun _ : ℕ => (1 / 2 : ℝ) * C ^ 2) =o[Filter.atTop] scaleNat :=
      const_isLittleO_scaleNat _
    have hshort_const : (fun _ : ℕ => (Z0 : ℝ) * C) =o[Filter.atTop] scaleNat :=
      const_isLittleO_scaleNat _
    have hshort_I :
        (fun X : ℕ => (Z0 : ℝ) * I D (((X + Z0 : ℕ) : ℝ)))
          =o[Filter.atTop] scaleNat :=
      hIshift_o.const_mul_left (Z0 : ℝ)
    have hshort :
        (fun X : ℕ => (Z0 : ℝ) * (C + I D (((X + Z0 : ℕ) : ℝ))))
          =o[Filter.atTop] scaleNat := by
      simpa [mul_add] using hshort_const.add hshort_I
    simpa [err, add_assoc] using (hC_I.add hC2).add hshort
  · filter_upwards with X
    have hX_nonneg : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
    have hshift_nonneg : 0 ≤ (((X + Z0 : ℕ) : ℝ)) := Nat.cast_nonneg (X + Z0)
    have hN_le : (Ncount A (X : ℝ) : ℝ) ≤ C + I D (X : ℝ) :=
      hcount (X : ℝ) hX_nonneg
    have hN_nonneg : 0 ≤ (Ncount A (X : ℝ) : ℝ) := Nat.cast_nonneg _
    have hsq :
        (1 / 2 : ℝ) * (Ncount A (X : ℝ) : ℝ) ^ 2 ≤
          (1 / 2 : ℝ) * (I D (X : ℝ)) ^ 2 +
            (C * I D (X : ℝ) + (1 / 2 : ℝ) * C ^ 2) := by
      have hCI_nonneg : 0 ≤ C + I D (X : ℝ) := hN_nonneg.trans hN_le
      have hsquare :
          (Ncount A (X : ℝ) : ℝ) ^ 2 ≤ (C + I D (X : ℝ)) ^ 2 :=
        (sq_le_sq₀ hN_nonneg hCI_nonneg).mpr hN_le
      nlinarith
    have hNshift_le :
        (Ncount A (((X + Z0 : ℕ) : ℝ)) : ℝ) ≤
          C + I D (((X + Z0 : ℕ) : ℝ)) :=
      hcount (((X + Z0 : ℕ) : ℝ)) hshift_nonneg
    have hshort :
        (Z0 : ℝ) * (Ncount A (((X + Z0 : ℕ) : ℝ)) : ℝ) ≤
          (Z0 : ℝ) * (C + I D (((X + Z0 : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hNshift_le (Nat.cast_nonneg Z0)
    calc
      smallShortMajorant A Z0 X =
          (1 / 2 : ℝ) * (Ncount A (X : ℝ) : ℝ) ^ 2 +
            (Z0 : ℝ) * (Ncount A (((X + Z0 : ℕ) : ℝ)) : ℝ) := rfl
      _ ≤ ((1 / 2 : ℝ) * (I D (X : ℝ)) ^ 2 +
            (C * I D (X : ℝ) + (1 / 2 : ℝ) * C ^ 2)) +
            (Z0 : ℝ) * (C + I D (((X + Z0 : ℕ) : ℝ))) := add_le_add hsq hshort
      _ = (1 / 2 : ℝ) * (I D (X : ℝ)) ^ 2 + err X := by
        dsimp [err]
        ring

/--
Named interface for replacing the large finite floor sum by the continuous floor contribution.
-/
theorem large_floor_sum_error_bound
    {B : ℝ} (A : Set ℕ) (_hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (_hupper : EventuallyUpperBound A _hA B)
    (Z0 : ℕ)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s) :
    ∃ err : ℕ → ℝ,
      err =o[Filter.atTop] scaleNat ∧
      ∀ᶠ X : ℕ in Filter.atTop,
        largeFloorSum A D Z0 X ≤
          JB D (X : ℝ) - Efloor D (X : ℝ) -
              (1 / 2 : ℝ) * (I D (X : ℝ)) ^ 2 + err X := by
  refine ⟨fun X : ℕ => I D (X : ℝ), integral_nat_isLittleO_scaleNat D, ?_⟩
  filter_upwards
    [eventually_natCast_le_Phi A _hA D _hupper,
      eventually_JB_sub_Efloor_nat_eq_floor_integral A _hA D _hupper]
    with X hXPhi hfloor_identity
  have hlarge : largeFloorSum A D Z0 X ≤
      I D (X : ℝ) +
        ∫ s in (X : ℝ)..D.Phi (X : ℝ),
          D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) :=
    largeFloorSum_le_I_add_floor_integral D hgap hXPhi
  calc
    largeFloorSum A D Z0 X ≤
        I D (X : ℝ) +
          ∫ s in (X : ℝ)..D.Phi (X : ℝ),
            D.f s * ((⌊GX D (X : ℝ) s⌋ : ℤ) : ℝ) := hlarge
    _ = JB D (X : ℝ) - Efloor D (X : ℝ) -
          (1 / 2 : ℝ) * (I D (X : ℝ)) ^ 2 + I D (X : ℝ) := by
      rw [hfloor_identity]
      ring

/--
Assembly of the remaining M5 error estimates.

This packages the small-top replacement error, fixed-width short-top contribution, and
large floor-sum/integral replacement into the error-function form required by
`FundamentalUpperBound`.
-/
theorem three_part_error_bound
    {B : ℝ} (A : Set ℕ) (_hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (_hupper : EventuallyUpperBound A _hA B)
    (Z0 : ℕ)
    (hgap : ∀ y z : ℕ,
      y ∈ A → z ∈ A → y < z → Z0 < z →
        1 ≤ ∫ s in (y : ℝ)..(z : ℝ), D.f s) :
    ∃ err : ℕ → ℝ,
      err =o[Filter.atTop] scaleNat ∧
      ∀ᶠ X : ℕ in Filter.atTop,
        threePartMajorant A D Z0 X ≤
          JB D (X : ℝ) - Efloor D (X : ℝ) + err X := by
  rcases small_short_error_bound A _hA D _hupper Z0 with ⟨errSmall, hsmall_o, hsmall⟩
  rcases large_floor_sum_error_bound A _hA D _hupper Z0 hgap with
    ⟨errLarge, hlarge_o, hlarge⟩
  refine ⟨fun X => errSmall X + errLarge X, hsmall_o.add hlarge_o, ?_⟩
  filter_upwards [hsmall, hlarge] with X hsmallX hlargeX
  calc
    threePartMajorant A D Z0 X =
        smallShortMajorant A Z0 X + largeFloorSum A D Z0 X := rfl
    _ ≤ ((1 / 2 : ℝ) * (I D (X : ℝ)) ^ 2 + errSmall X) +
          (JB D (X : ℝ) - Efloor D (X : ℝ) -
              (1 / 2 : ℝ) * (I D (X : ℝ)) ^ 2 + errLarge X) :=
        add_le_add hsmallX hlargeX
    _ = JB D (X : ℝ) - Efloor D (X : ℝ) + (errSmall X + errLarge X) := by
        ring

/-- Error-function form of TeX equation `(17)`: `X ≤ J_B(X) - E(X) + o(X/log X)`. -/
def FundamentalUpperBound
    {B : ℝ} (D : PhiPsiData B) : Prop :=
  ∃ err : ℕ → ℝ,
    err =o[Filter.atTop] scaleNat ∧
    ∀ᶠ X : ℕ in Filter.atTop,
      (X : ℝ) ≤ JB D (X : ℝ) - Efloor D (X : ℝ) + err X

/-- TeX Parts 3--5: fundamental upper bound. -/
theorem fundamental_upper_bound
    {B : ℝ} (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (D : PhiPsiData B)
    (hupper : EventuallyUpperBound A hA B) :
    FundamentalUpperBound D := by
  rcases gap_integral_ge_one A hA D hupper with ⟨Z0, hgap⟩
  have hthree := top_counting_three_part_bound A hA D hupper hgap
  rcases three_part_error_bound A hA D hupper Z0 hgap with ⟨err, herr_o, herr_bound⟩
  refine ⟨err, herr_o, ?_⟩
  have hthree' :
      ∀ᶠ X : ℕ in Filter.atTop,
        (X : ℝ) ≤ threePartMajorant A D Z0 X := by
    simpa [threePartMajorant, smallShortMajorant, largeFloorSum] using hthree
  filter_upwards [hthree', herr_bound] with X hX hbound
  exact hX.trans hbound

end FloorSaving
