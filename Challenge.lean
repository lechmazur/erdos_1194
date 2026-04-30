import Mathlib

noncomputable section

open Classical
open Filter Topology MeasureTheory Asymptotics
open scoped Real BigOperators

namespace FloorSaving

/-- Positive natural numbers, used because the theorem's `n` starts at `1`. -/
abbrev PosNat := { n : ℕ // 0 < n }

/-- All elements of `A` are positive. -/
def PositiveSet (A : Set ℕ) : Prop :=
  ∀ a : ℕ, a ∈ A → 0 < a

/-- The ordered pair `p = (a,b)` represents the positive difference `n` in `A`. -/
def RepresentsDiff (A : Set ℕ) (n : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 ∈ A ∧ p.2 ∈ A ∧ p.2 < p.1 ∧ p.1 - p.2 = n

/-- The unique-positive-difference hypothesis. -/
def UniquePositiveDiffs (A : Set ℕ) : Prop :=
  PositiveSet A ∧
    ∀ n : ℕ, 0 < n → ∃! p : ℕ × ℕ, RepresentsDiff A n p

/-- The unique representative pair for a positive difference. -/
noncomputable def repPair
    (A : Set ℕ) (hA : UniquePositiveDiffs A) (n : PosNat) :
    { p : ℕ × ℕ // RepresentsDiff A n.1 p } := by
  classical
  let hUnique := hA.2 n.1 n.2
  let hExists : ∃ p : ℕ × ℕ, RepresentsDiff A n.1 p := by
    rcases hUnique with ⟨p, hp, _huniq⟩
    exact ⟨p, hp⟩
  exact ⟨Classical.choose hExists, Classical.choose_spec hExists⟩

/-- The top element `u(n)` of the unique representative pair for `n`. -/
noncomputable def top
    (A : Set ℕ) (hA : UniquePositiveDiffs A) (n : PosNat) : ℕ :=
  (repPair A hA n).1.1

/-- The bottom element `v(n)` of the unique representative pair for `n`. -/
noncomputable def bot
    (A : Set ℕ) (hA : UniquePositiveDiffs A) (n : PosNat) : ℕ :=
  (repPair A hA n).1.2

/-- `λ = 1/(2 log 2)`. -/
noncomputable def lam : ℝ :=
  1 / (2 * Real.log 2)

/-- The endpoint constant `B₁ = 1/2 + γ - log(log 2)`. -/
noncomputable def B₁ : ℝ :=
  (1 / 2) + Real.eulerMascheroniConstant - Real.log (Real.log 2)

/-- Denominator from the lower-bound expression. `Real.log` is total in Lean. -/
def denom (B : ℝ) (n : ℕ) : ℝ :=
  Real.log (n : ℝ) - Real.log (Real.log (n : ℝ)) + B

/-- Right-hand side of the final lower-bound expression. -/
def lowerBoundRHS (B : ℝ) (n : ℕ) : ℝ :=
  lam * ((n : ℝ) ^ 2) / denom B n

/--
Main theorem statement.

If `A` is a set of positive integers with a unique ordered representation
`n = u(n) - v(n)` for every `n >= 1`, then for every `B > B₁` the displayed
floor-saving lower bound is beaten for arbitrarily large positive differences.
-/
theorem floor_saving_lower_bound
    (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (B : ℝ) (hB : B₁ < B) :
    ∀ N : ℕ, ∃ n : PosNat,
      N ≤ n.1 ∧
      0 < denom B n.1 ∧
      (top A hA n : ℝ) > lowerBoundRHS B n.1 := by
  sorry

/-- The normalized endpoint sequence, totalized at `0` for a natural-number limsup. -/
noncomputable def endpointSeq (A : Set ℕ) (hA : UniquePositiveDiffs A) (n : ℕ) : ℝ :=
  if hn : 0 < n then
    (top A hA ⟨n, hn⟩ : ℝ) * denom B₁ n / (n : ℝ) ^ 2
  else 0

/-- Endpoint limsup consequence of the lower bound. -/
theorem endpoint_limsup
    (A : Set ℕ) (hA : UniquePositiveDiffs A) :
    (lam : EReal) ≤ Filter.limsup
      (fun n : ℕ => (endpointSeq A hA n : EReal)) Filter.atTop := by
  sorry

end FloorSaving
