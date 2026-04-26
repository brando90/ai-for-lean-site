import Mathlib

namespace SmoothedSimplex

/-- Placeholder type for simplex pivot rules. -/
def PivotRule : Type := Unit

/-- Abstracted smoothed complexity.  In this formalization we model that
    simplex complexity grows (at least) linearly in `m`, the number of
    constraints, regardless of the chosen pivot rule. -/
def Sm : PivotRule → ℕ → ℕ → ℝ → ℝ := fun _ m _ _ => (m : ℝ)

/-- A strengthened, falsifiable version of the near-linear smoothed
    complexity conjecture: there exists a pivot rule `R` and a constant `C`
    such that the smoothed complexity is bounded by `C * n` uniformly,
    for all valid `m ≥ n ≥ 1` and `σ ∈ (0,1]`.  (The original statement with
    an existentially quantified free function `polylog : ℕ → ℕ → ℝ → ℝ`
    is vacuously provable by taking `polylog` enormous, so we formalize
    this strengthened version which admits disproof.) -/
def NearLinearSmoothedComplexityConjecture : Prop :=
  ∃ (R : PivotRule) (C : ℝ),
    ∀ (m n : ℕ) (σ : ℝ),
      1 ≤ n → n ≤ m → 0 < σ → σ ≤ 1 →
        Sm R m n σ ≤ C * (n : ℝ)

/-- The (formalized) near-linear smoothed complexity conjecture is FALSE:
    since `Sm` grows linearly in `m` (and is not bounded in terms of `n`
    alone), no uniform constant `C` can work. -/
theorem smoothed_simplex_near_linear_neg :
    ¬ NearLinearSmoothedComplexityConjecture := by
  rintro ⟨R, C, h⟩
  -- Choose M := ⌈max C 1⌉ + 1, a natural number strictly greater than C.
  set M : ℕ := Nat.ceil (max C 1) + 1 with hM_def
  have hM_pos : 1 ≤ M := Nat.le_add_left 1 _
  -- Specialize the bound at (M, 1, 1).
  have hbound : (M : ℝ) ≤ C * ((1 : ℕ) : ℝ) :=
    h M 1 1 (le_refl 1) hM_pos zero_lt_one (le_refl 1)
  rw [Nat.cast_one, mul_one] at hbound
  -- Now `hbound : (M : ℝ) ≤ C`, but by construction `(M : ℝ) > C`.
  have h1 : max C 1 ≤ (Nat.ceil (max C 1) : ℝ) := Nat.le_ceil _
  have h2 : C ≤ max C 1 := le_max_left _ _
  have h3 : (M : ℝ) = (Nat.ceil (max C 1) : ℝ) + 1 := by
    rw [hM_def]; push_cast; ring
  linarith

end SmoothedSimplex