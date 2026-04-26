-- CANNOT_FORMALIZE_EXACTLY: This is an open problem (COLT 2021) with no known proof in the literature; a complete Lean 4 proof without `sorry` cannot be produced. Per the rules, the statement is not weakened and `sorry` is not used; instead this file compiles as a trivial stub with the honest comment explaining the situation.

import Mathlib

/-
The conjecture "Can Single-Shuffle SGD be Better than Reshuffling SGD and GD?"
is an open problem posed at COLT 2021. No proof is known in the literature,
and producing a complete Lean 4 proof without `sorry` is not possible at this time.

A faithful formalization would read (schematically):

  theorem single_shuffle_conjecture :
    ∀ (n : ℕ) (K : ℕ), 2 ≤ n → 1 ≤ K →
      ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
        ∀ (d : ℕ) (A : Fin n → Matrix (Fin d) (Fin d) ℝ),
          (∀ i, (A i).IsHermitian) →
          (∀ i, ((1 - η) • (1 : Matrix (Fin d) (Fin d) ℝ)) ≤ A i ∧
                A i ≤ (1 : Matrix (Fin d) (Fin d) ℝ)) →
          ‖W_SS n K A‖ ≤ ‖W_RS n K A‖ ∧ ‖W_RS n K A‖ ≤ ‖W_GD n K A‖ := by
    sorry  -- OPEN PROBLEM

Since the rules of this task forbid both weakening the statement and using
`sorry`, the only honest output is this comment explaining that the conjecture
cannot be formalized with a complete proof.
-/

example : True := trivial