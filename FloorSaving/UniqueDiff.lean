import FloorSaving.Basic

noncomputable section

open Classical
open Filter Topology MeasureTheory Asymptotics
open scoped Real BigOperators

namespace FloorSaving

variable {A : Set ℕ}

/-- The selected representative pair satisfies its defining predicate. -/
theorem repPair_spec (hA : UniquePositiveDiffs A) (n : PosNat) :
    RepresentsDiff A n.1 (repPair A hA n).1 :=
  (repPair A hA n).2

/-- The top is in `A`. -/
theorem top_mem (hA : UniquePositiveDiffs A) (n : PosNat) :
    top A hA n ∈ A := by
  exact (repPair_spec hA n).1

/-- The bottom is in `A`. -/
theorem bot_mem (hA : UniquePositiveDiffs A) (n : PosNat) :
    bot A hA n ∈ A := by
  exact (repPair_spec hA n).2.1

/-- The bottom is strictly less than the top. -/
theorem bot_lt_top (hA : UniquePositiveDiffs A) (n : PosNat) :
    bot A hA n < top A hA n := by
  exact (repPair_spec hA n).2.2.1

/-- The selected pair has difference `n`. -/
theorem top_sub_bot (hA : UniquePositiveDiffs A) (n : PosNat) :
    top A hA n - bot A hA n = n.1 := by
  exact (repPair_spec hA n).2.2.2

/-- The selected top is at least the represented positive difference. -/
theorem diff_le_top (hA : UniquePositiveDiffs A) (n : PosNat) :
    n.1 ≤ top A hA n := by
  rw [← top_sub_bot hA n]
  exact Nat.sub_le _ _

/-- Two pairs representing the same positive difference are equal. -/
theorem same_diff_pair_unique
    (hA : UniquePositiveDiffs A) {n : ℕ} (hn : 0 < n) {p q : ℕ × ℕ}
    (hp : RepresentsDiff A n p) (hq : RepresentsDiff A n q) :
    p = q := by
  rcases hA.2 n hn with ⟨r, hr, huniq⟩
  have hp_eq : p = r := huniq p hp
  have hq_eq : q = r := huniq q hq
  exact hp_eq.trans hq_eq.symm

/-- A pair representing a difference is the selected representative pair for that difference. -/
theorem repPair_eq_of_represents
    (hA : UniquePositiveDiffs A) {n : ℕ} (hn : 0 < n) {p : ℕ × ℕ}
    (hp : RepresentsDiff A n p) :
    p = (repPair A hA ⟨n, hn⟩).1 := by
  exact same_diff_pair_unique hA hn hp (repPair_spec hA ⟨n, hn⟩)

/-- `A` is nonempty. -/
theorem A_nonempty (hA : UniquePositiveDiffs A) : ∃ a : ℕ, a ∈ A := by
  rcases hA.2 1 (by norm_num) with ⟨p, hp, _huniq⟩
  exact ⟨p.1, hp.1⟩

/-- `A` is unbounded. This is enough for the counting-function majorant. -/
theorem A_unbounded (hA : UniquePositiveDiffs A) :
    ∀ N : ℕ, ∃ a : ℕ, a ∈ A ∧ N ≤ a := by
  intro N
  rcases hA.2 (N + 1) (Nat.succ_pos N) with ⟨p, hp, _huniq⟩
  refine ⟨p.1, hp.1, ?_⟩
  have hN1_le : N + 1 ≤ p.1 := by
    rw [← hp.2.2.2]
    exact Nat.sub_le p.1 p.2
  exact Nat.le_trans (Nat.le_succ N) hN1_le

end FloorSaving
