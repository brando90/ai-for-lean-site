import Mathlib

open scoped Classical

/--
Formalization note: interpreting "whole number" as a *positive* natural number
(which matches the intuitive expectation that a/a = 1, a whole number), the
conjecture "any number divided by itself is a whole number" is FALSE in Lean's
real arithmetic, because the counterexample a = 0 gives 0/0 = 0, which is not
a positive whole number.
-/
theorem any_number_divided_by_itself_is_whole_neg :
    ¬ (∀ a : ℝ, ∃ n : ℕ, 0 < n ∧ a / a = (n : ℝ)) := by
  intro h
  obtain ⟨n, hn_pos, hdiv⟩ := h 0
  have h0 : (0 : ℝ) / 0 = 0 := by simp
  rw [h0] at hdiv
  have hn_real : (n : ℝ) = 0 := hdiv.symm
  have hn_zero : n = 0 := by exact_mod_cast hn_real
  exact (Nat.lt_irrefl 0) (hn_zero ▸ hn_pos)