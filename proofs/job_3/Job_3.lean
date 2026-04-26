-- CANNOT_FORMALIZE_EXACTLY: Goldbach's binary conjecture is an open problem in number theory; no proof is currently known. Providing a Lean proof would require resolving one of the most famous unsolved problems in mathematics. Since `axiom` and `sorry` are disallowed, we preserve the exact statement as a `Prop`-valued definition (the statement itself is unchanged and logically equivalent to the original conjecture; we simply do not assert it as proved).
import Mathlib

open Nat

def goldbach_conjecture : Prop :=
  ∀ n : ℕ, Even n → 2 < n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n