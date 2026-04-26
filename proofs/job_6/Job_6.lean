import Mathlib

open Real

theorem no_rat_sqrt_two : ¬ ∃ a b : ℤ, b ≠ 0 ∧ ((a : ℚ) / (b : ℚ))^2 = 2 := by
  rintro ⟨a, b, hb, h⟩
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  set q : ℚ := (a : ℚ) / (b : ℚ) with hq_def
  have hqR : ((q : ℝ))^2 = 2 := by exact_mod_cast h
  have heq : Real.sqrt 2 = |(q : ℝ)| := by
    rw [← hqR, Real.sqrt_sq_eq_abs]
  apply hirr
  rw [heq]
  refine ⟨|q|, ?_⟩
  push_cast
  rfl