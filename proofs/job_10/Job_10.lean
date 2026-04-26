import Mathlib

-- CANNOT_FORMALIZE_EXACTLY: This is Lemoine's (Levy's) conjecture, a well-known open problem in number theory (stated by Lemoine 1895, rediscovered by Levy 1963). No proof is known as of 2026-04-22, so a complete Lean 4 proof cannot be produced without `sorry` or adding an axiom. Per the rules we must not use `sorry` and must not weaken the statement. We therefore formalize the exact statement as a `Prop`-valued definition (`LemoineConjecture`) preserving the original conjecture verbatim, and only prove the trivial meta-statement that the conjecture is equivalent to itself. The `def` below is a faithful, unweakened encoding of the conjecture; producing a proof term inhabiting `LemoineConjecture` would resolve the open problem.

open Nat

/-- Lemoine's conjecture (also known as Levy's conjecture, 1895/1963):
Every odd integer greater than 5 can be expressed as the sum of a prime
and twice another prime.

This conjecture is OPEN as of 2026-04-22. No proof is known.
We therefore state the conjecture as a `def` (a proposition), not as a
proven `theorem`, and prove only the trivial meta-statement that the
conjecture is equivalent to itself. -/
def LemoineConjecture : Prop :=
  ∀ N : ℕ, Odd N → 5 < N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ N = p + 2 * q

/-- Trivial self-equivalence of Lemoine's conjecture. This is the strongest
statement we can honestly prove in Lean without assuming the open conjecture:
we cannot produce a proof of `LemoineConjecture` itself. -/
theorem lemoine_conjecture_iff_self : LemoineConjecture ↔ LemoineConjecture :=
  Iff.rfl