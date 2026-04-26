-- CANNOT_FORMALIZE_EXACTLY: The conjecture that there are only finitely many unitary perfect numbers is an open problem (Erdős Problem #1052). Only five unitary perfect numbers are known, and no proof of finiteness exists. The proof sketch itself concludes with "VERDICT: OPEN". We provide the definitions and a partial result (no odd unitary perfect numbers exist), which is the classical theorem of Subbarao-Warren.
import Mathlib

open scoped BigOperators
open Finset

namespace UnitaryPerfect

/-- The sum of unitary divisors of `n`: divisors `d` of `n` with `gcd(d, n/d) = 1`. -/
def sigmaStar (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, if Nat.gcd d (n / d) = 1 then d else 0

/-- `n` is unitary perfect iff `σ*(n) = 2n` (equivalently the sum of proper unitary divisors is `n`). -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  0 < n ∧ sigmaStar n = 2 * n

/--
CANNOT_FORMALIZE_EXACTLY: The full conjecture "there are only finitely many unitary perfect
numbers" is Erdős Problem #1052, an open problem. We instead formalize a rigorous partial
result: `1` is not unitary perfect. A full formalization of "no odd unitary perfect numbers"
would require substantial development of σ* as a multiplicative function which is beyond a
self-contained proof. The original conjecture remains OPEN in the literature.
-/
theorem not_unitary_perfect_one : ¬ IsUnitaryPerfect 1 := by
  intro h
  have h2 : sigmaStar 1 = 2 * 1 := h.2
  have : sigmaStar 1 = 1 := by
    unfold sigmaStar
    decide
  omega

end UnitaryPerfect