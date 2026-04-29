# Statement contract

This file records the intended public statements. Do not change these without recording a decision in `docs/DECISIONS.md`.

## Natural-number convention

The TeX proof uses:

```text
ℕ = {1,2,3,...}
```

Lean's `ℕ` includes `0`, so the project uses:

```lean
abbrev PosNat := { n : ℕ // 0 < n }
```

A set `A : Set ℕ` is required to be positive:

```lean
def PositiveSet (A : Set ℕ) : Prop :=
  ∀ a : ℕ, a ∈ A → 0 < a
```

The unique-difference hypothesis is:

```lean
def RepresentsDiff (A : Set ℕ) (n : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 ∈ A ∧ p.2 ∈ A ∧ p.2 < p.1 ∧ p.1 - p.2 = n

def UniquePositiveDiffs (A : Set ℕ) : Prop :=
  PositiveSet A ∧
    ∀ n : ℕ, 0 < n → ∃! p : ℕ × ℕ, RepresentsDiff A n p
```

## Selected representative pair

For `n : PosNat`, define:

```lean
noncomputable def repPair
    (A : Set ℕ) (hA : UniquePositiveDiffs A) (n : PosNat) :
    { p : ℕ × ℕ // RepresentsDiff A n.1 p }

noncomputable def top
    (A : Set ℕ) (hA : UniquePositiveDiffs A) (n : PosNat) : ℕ

noncomputable def bot
    (A : Set ℕ) (hA : UniquePositiveDiffs A) (n : PosNat) : ℕ
```

The TeX notation `a_n` is `top A hA n`; `b_n` is `bot A hA n`.

## Constants

```lean
noncomputable def lam : ℝ :=
  1 / (2 * Real.log 2)

noncomputable def B₁ : ℝ :=
  (1 / 2) + Real.eulerMascheroniConstant - Real.log (Real.log 2)

def denom (B : ℝ) (n : ℕ) : ℝ :=
  Real.log (n : ℝ) - Real.log (Real.log (n : ℝ)) + B

def lowerBoundRHS (B : ℝ) (n : ℕ) : ℝ :=
  lam * ((n : ℝ) ^ 2) / denom B n
```

`Real.log` is total. Domain conditions are expressed by hypotheses, usually `0 < denom B n` or eventual positivity.

## Main theorem

Target shape:

```lean
theorem floor_saving_lower_bound
    (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (B : ℝ) (hB : B₁ < B) :
    ∀ N : ℕ, ∃ n : PosNat,
      N ≤ n.1 ∧
      0 < denom B n.1 ∧
      (top A hA n : ℝ) > lowerBoundRHS B n.1
```

This is the primary theorem. It asserts the strict lower-bound violation for arbitrarily large positive differences.

## Equivalent non-eventual form

The contradiction is easier to prove through:

```lean
def UpperBoundAt
    (A : Set ℕ) (hA : UniquePositiveDiffs A) (B : ℝ) (n : ℕ) : Prop :=
  ∀ hn : 0 < n,
    0 < denom B n →
      (top A hA ⟨n, hn⟩ : ℝ) ≤ lowerBoundRHS B n

def EventuallyUpperBound
    (A : Set ℕ) (hA : UniquePositiveDiffs A) (B : ℝ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, UpperBoundAt A hA B n

theorem not_eventually_upper_bound
    (A : Set ℕ) (hA : UniquePositiveDiffs A)
    (B : ℝ) (hB : B₁ < B) :
    ¬ EventuallyUpperBound A hA B
```

Then derive the main theorem by combining non-eventuality with eventual denominator positivity.

## Endpoint theorem

The TeX reference states the endpoint consequence explicitly. In Lean it is proved downstream of
`floor_saving_lower_bound` and the analytic asymptotics in `FloorSaving/EndpointLimsup.lean`.

Mathematical target:

```text
limsup_{n→∞}
  top(A,hA,n) * (log n - log log n + B₁) / n^2
  ≥ lam
```

Finite omissions do not matter: the limsup is unchanged after discarding the initial range where
the displayed logarithmic denominator is not in the intended positive domain. Lean's `Real.log` is
total, so this is a proof-side eventual-domain condition rather than a partial-function issue.

Lean target:

```lean
noncomputable def endpointSeq
    (A : Set ℕ) (hA : UniquePositiveDiffs A) (n : ℕ) : ℝ :=
  if hn : 0 < n then
    (top A hA ⟨n, hn⟩ : ℝ) * denom B₁ n / (n : ℝ)^2
  else 0

theorem endpoint_limsup
    (A : Set ℕ) (hA : UniquePositiveDiffs A) :
    (lam : EReal) ≤ Filter.limsup
      (fun n : ℕ => (endpointSeq A hA n : EReal)) Filter.atTop
```

The endpoint limsup is stated in `EReal`. The local real-valued `Filter.limsup` API carries
boundedness side conditions and returns `0` for unbounded real sequences, while the theorem is an
extended-limsup lower bound and needs no upper boundedness hypothesis.

## Non-goals

The theorem is conditional. Do not try to prove existence of a set `A` satisfying `UniquePositiveDiffs A`.

Do not try to prove the pointwise infinitely-often inequality at `B = B₁`; the TeX proof explicitly does not claim it.
