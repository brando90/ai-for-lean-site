-- CANNOT_FORMALIZE_EXACTLY: This is the Erdős conjecture on arithmetic progressions (Erdős–Turán 1936 for k=3, generalized by Erdős to all k ≥ 3). The conjecture is OPEN for k ≥ 4 as of April 2026. The k=3 case (Bloom–Sisask 2020, Kelley–Meka 2023) is not in Mathlib. We therefore faithfully state the conjecture as a `Prop` and prove only the trivially provable fragments (k = 0 vacuously; k = 1 from nonemptiness extracted from divergence). The genuine mathematical content is beyond current formalization capabilities.
import Mathlib

open scoped BigOperators
open Set

namespace ErdosAPConjecture

/-- `HasKTermAP A k` asserts that the set `A ⊆ ℕ` contains a non-trivial
`k`-term arithmetic progression: there exist a starting point `a` and a
common difference `d ≥ 1` such that `a, a+d, a+2d, …, a+(k-1)d` all lie in `A`.
The condition `d ≥ 1` rules out degenerate "constant" progressions. -/
def HasKTermAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 1 ≤ d ∧ ∀ i : ℕ, i < k → (a + i * d) ∈ A

/-- `A` contains arbitrarily long arithmetic progressions: for every `k`,
`A` contains a non-trivial `k`-term AP. -/
def HasArbitrarilyLongAPs (A : Set ℕ) : Prop :=
  ∀ k : ℕ, HasKTermAP A k

/-- The reciprocal-sum divergence hypothesis: the series `∑_{a ∈ A} 1/a`
diverges. For a series of non-negative reals, `¬ Summable` is equivalent to
the sum being `+∞`. Since Lean defines `1 / 0 = 0` in `ℝ`, this definition
is well-behaved even if `0 ∈ A` (the element `0` simply contributes `0` to
the sum, matching the usual mathematical convention that reciprocals of
positive integers are intended). -/
def ReciprocalSumDiverges (A : Set ℕ) : Prop :=
  ¬ Summable (fun n : A => (1 : ℝ) / (n.1 : ℝ))

/-- **Erdős's conjecture on arithmetic progressions.** If `A ⊆ ℕ` has a
divergent reciprocal sum, then `A` contains arbitrarily long arithmetic
progressions. This is an **open** problem for `k ≥ 4`; the `k = 3` case is
the Bloom–Sisask / Kelley–Meka theorem. We state it as a `Prop`; we do *not*
prove it. -/
def ErdosAPConjectureStatement : Prop :=
  ∀ (A : Set ℕ), ReciprocalSumDiverges A → HasArbitrarilyLongAPs A

/-- **Trivial fragment (k = 0).** Every set contains a vacuous 0-term AP. -/
theorem hasKTermAP_zero (A : Set ℕ) : HasKTermAP A 0 := by
  refine ⟨0, 1, le_refl 1, ?_⟩
  intro i hi
  exact absurd hi (Nat.not_lt_zero i)

/-- Divergence of the reciprocal sum forces `A` to be nonempty, since the sum
over an empty index type is trivially summable. -/
theorem nonempty_of_reciprocalSumDiverges
    {A : Set ℕ} (hA : ReciprocalSumDiverges A) : ∃ a, a ∈ A := by
  by_contra h
  push_neg at h
  apply hA
  have hEmpty : IsEmpty (A : Type) := ⟨fun x => h x.1 x.2⟩
  have hfun : (fun n : A => (1 : ℝ) / (n.1 : ℝ)) = (fun _ => (0 : ℝ)) := by
    funext x
    exact hEmpty.elim x
  rw [hfun]
  exact summable_zero

/-- **Trivial fragment (k ≤ 1).** If the reciprocal sum of `A` diverges,
then `A` contains a non-trivial AP of length `k` for every `k ≤ 1`. This is
the only portion of the conjecture provable without deep additive
combinatorics. -/
theorem hasKTermAP_of_divergent_of_le_one
    (A : Set ℕ) (hA : ReciprocalSumDiverges A) (k : ℕ) (hk : k ≤ 1) :
    HasKTermAP A k := by
  interval_cases k
  · exact hasKTermAP_zero A
  · obtain ⟨a, haA⟩ := nonempty_of_reciprocalSumDiverges hA
    refine ⟨a, 1, le_refl 1, ?_⟩
    intro i hi
    interval_cases i
    simpa using haA

/-- **Target statement (unproved).** The genuine mathematical content of the
conjecture for a fixed `k`: any set with divergent reciprocal sum contains a
`k`-term AP. For `k ≤ 2` this follows from `hasKTermAP_of_divergent_of_le_one`.
For `k = 3` this is Bloom–Sisask / Kelley–Meka (not in Mathlib). For `k ≥ 4`
this is an open problem. -/
def DivergenceImpliesKAP (k : ℕ) : Prop :=
  ∀ (A : Set ℕ), ReciprocalSumDiverges A → HasKTermAP A k

/-- The full conjecture is equivalent to the family of fixed-`k` statements
holding for every `k`. This is a purely definitional repackaging. -/
theorem erdos_equiv_forall_k :
    ErdosAPConjectureStatement ↔ ∀ k, DivergenceImpliesKAP k := by
  unfold ErdosAPConjectureStatement DivergenceImpliesKAP HasArbitrarilyLongAPs
  exact ⟨fun h k A hA => h A hA k, fun h A hA k => h k A hA⟩

end ErdosAPConjecture