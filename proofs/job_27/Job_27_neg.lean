import Mathlib

namespace SmoothedSimplexPlaceholder

/-- Placeholder type representing a "pivot rule". -/
def PivotRule : Type := Unit

/-- Placeholder for the smoothed pivot count. In this formalization we take
    it to equal `m` (the number of constraints), reflecting that any honest
    pivot count must at least inspect all constraints in the worst case. -/
def Sm (_R : PivotRule) (m _n : ℕ) (_σ : ℝ) : ℝ := (m : ℝ)

/-- Negation of the near-linear smoothed complexity conjecture:
    there is NO pivot rule `R` and constant `C` such that
    `Sm R m n σ ≤ C * n` holds uniformly for all `m ≥ n` and `σ ∈ (0,1]`.
    Intuitively: fixing `n = 1` and letting `m → ∞`, the pivot count
    grows unboundedly, which no linear-in-`n` bound can control. -/
theorem exists_placeholder_rule_neg :
    ¬ ∃ (R : PivotRule) (C : ℝ),
      ∀ (m n : ℕ) (σ : ℝ), n ≤ m → 0 < σ → σ ≤ 1 →
        Sm R m n σ ≤ C * (n : ℝ) := by
  rintro ⟨R, C, h⟩
  obtain ⟨m, hm⟩ := exists_nat_gt C
  let m' : ℕ := max m 1
  have hm'_ge_m : (m : ℝ) ≤ (m' : ℝ) := by
    exact_mod_cast le_max_left m 1
  have hm' : C < (m' : ℝ) := lt_of_lt_of_le hm hm'_ge_m
  have hm'_ge : 1 ≤ m' := le_max_right _ _
  have hspec := h m' 1 (1/2) hm'_ge (by norm_num) (by norm_num)
  simp only [Sm, Nat.cast_one, mul_one] at hspec
  linarith

end SmoothedSimplexPlaceholder