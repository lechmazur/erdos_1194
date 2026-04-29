import Mathlib

noncomputable section

open Classical
open Filter Topology MeasureTheory Asymptotics
open scoped Real BigOperators

namespace FloorSaving

/-- Positive natural numbers, used because the paper's `ℕ` starts at `1`. -/
abbrev PosNat := { n : ℕ // 0 < n }

/-- All elements of `A` are positive. -/
def PositiveSet (A : Set ℕ) : Prop :=
  ∀ a : ℕ, a ∈ A → 0 < a

/-- The ordered pair `p = (a,b)` represents the positive difference `n` in `A`. -/
def RepresentsDiff (A : Set ℕ) (n : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 ∈ A ∧ p.2 ∈ A ∧ p.2 < p.1 ∧ p.1 - p.2 = n

/-- The unique-positive-difference hypothesis from the TeX proof. -/
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

/-- The top element `a_n` of the unique representative pair for `n`. -/
noncomputable def top
    (A : Set ℕ) (hA : UniquePositiveDiffs A) (n : PosNat) : ℕ :=
  (repPair A hA n).1.1

/-- The bottom element `b_n` of the unique representative pair for `n`. -/
noncomputable def bot
    (A : Set ℕ) (hA : UniquePositiveDiffs A) (n : PosNat) : ℕ :=
  (repPair A hA n).1.2

/-- `λ = 1/(2 log 2)`. Named `lam` rather than `lambda`. -/
noncomputable def lam : ℝ :=
  1 / (2 * Real.log 2)

/-- The endpoint constant `B₁ = 1/2 + γ - log(log 2)`. -/
noncomputable def B₁ : ℝ :=
  (1 / 2) + Real.eulerMascheroniConstant - Real.log (Real.log 2)

/-- Denominator from the final lower bound. `Real.log` is total; positivity is separate. -/
def denom (B : ℝ) (n : ℕ) : ℝ :=
  Real.log (n : ℝ) - Real.log (Real.log (n : ℝ)) + B

/-- Right-hand side of the final upper-bound expression. -/
def lowerBoundRHS (B : ℝ) (n : ℕ) : ℝ :=
  lam * ((n : ℝ) ^ 2) / denom B n

/-- Real-valued scale for second-order asymptotics. -/
def scaleReal (X : ℝ) : ℝ :=
  X / Real.log X

/-- Natural-indexed scale for integer-parameter asymptotics. -/
def scaleNat (X : ℕ) : ℝ :=
  (X : ℝ) / Real.log (X : ℝ)

end FloorSaving
