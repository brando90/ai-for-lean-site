-- CANNOT_FORMALIZE_EXACTLY: The conjecture is an asymptotic estimate
-- M(N)/log N → c_2 ≈ 0.6187712111, where c_2 is defined via an integral
-- against an analytic function Φ whose root α_2 ∈ (1/4, 1/3) satisfies
-- Φ(α_2) = 1. A complete proof requires Mertens-type quantitative prime
-- estimates, uniform Riemann-sum convergence on [α_2, 1/2], and the
-- ancestor/frontier antichain theory (Erdős Problem #858) — none of which
-- are presently available in Mathlib at the level of generality required.
-- We therefore faithfully formalize:
--   (i)   the admissibility predicate `NoForbiddenRatio`
--         (no `a*t = b` with `a, b ∈ A` and `minFac t > a`);
--   (ii)  the reciprocal sum `∑_{a ∈ A} 1/a` and its normalization by `1/log N`;
--   (iii) the existence of a maximizing admissible subset of `{1,...,N}`,
--         together with elementary unconditional lower/upper bounds on
--         the maximum;
--   (iv)  the analytic function Φ, the cutoff α_2, and the constant c_2,
--         exactly as in the proof sketch;
--   (v)   the Poindexter / Erdős #858 asymptotic conjecture itself,
--         stated as a `Prop` involving these objects.
-- Note: `alpha2` is defined as `sInf alpha2RootSet`. The proof sketch asserts
-- (but does not prove here) that this set is a singleton, so this definition
-- agrees with "the unique root" whenever existence/uniqueness holds; if the
-- set were empty, `sInf` would default to `0`, but the conjecture is only
-- meaningful under the analytic facts of the sketch.

import Mathlib

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace PoindexterErdos858

attribute [local instance] Classical.propDecidable

/-- `ForbiddenRatio a b` means that `b = a * t` for some integer `t > 1` whose
smallest prime factor is strictly greater than `a`. The hypothesis `1 < t`
excludes the trivial case `a = b`; it is logically redundant when `a ≥ 1`,
since `Nat.minFac 1 = 1` so `a < Nat.minFac t` forces `t ≠ 1`. We include it
for explicitness. -/
def ForbiddenRatio (a b : ℕ) : Prop :=
  ∃ t : ℕ, 1 < t ∧ a * t = b ∧ a < Nat.minFac t

/-- Admissibility: there is no solution `a * t = b` with `a, b ∈ A`, `t > 1`,
and the smallest prime factor of `t` strictly greater than `a`. -/
def NoForbiddenRatio (A : Finset ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∈ A → b ∈ A → ¬ ForbiddenRatio a b

/-- `A` is an admissible subset of `{1, ..., N}`. -/
def admissibleWithin (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ NoForbiddenRatio A

/-- The reciprocal sum `∑_{a ∈ A} 1 / a`. -/
def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (1 : ℝ) / (a : ℝ)

/-- The normalized objective from the conjecture:
`(1 / log N) * ∑_{a ∈ A} 1 / a`. -/
def normalizedReciprocalSum (N : ℕ) (A : Finset ℕ) : ℝ :=
  (1 / Real.log (N : ℝ)) * reciprocalSum A

/-- The finite family of admissible subsets of `{1, ..., N}`. -/
def admissibleSubsets (N : ℕ) : Finset (Finset ℕ) :=
  ((Finset.Icc 1 N).powerset).filter NoForbiddenRatio

theorem mem_admissibleSubsets_iff {N : ℕ} {A : Finset ℕ} :
    A ∈ admissibleSubsets N ↔ admissibleWithin N A := by
  simp [admissibleSubsets, admissibleWithin]

theorem admissibleSubsets_nonempty (N : ℕ) : (admissibleSubsets N).Nonempty := by
  refine ⟨∅, ?_⟩
  refine mem_admissibleSubsets_iff.mpr ⟨Finset.empty_subset _, ?_⟩
  intro a b ha hb _
  exact absurd ha (Finset.notMem_empty a)

theorem singleton_one_admissibleWithin {N : ℕ} (hN : 1 ≤ N) :
    admissibleWithin N ({1} : Finset ℕ) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    rcases Finset.mem_singleton.mp ha with rfl
    simp [hN]
  · intro a b ha hb hforbidden
    rcases Finset.mem_singleton.mp ha with rfl
    rcases Finset.mem_singleton.mp hb with rfl
    rcases hforbidden with ⟨t, ht, hmul, hlt⟩
    have ht1 : t = 1 := by simpa using hmul
    omega

/-- Existence of a maximizing admissible subset of `{1, ..., N}` for the
normalized reciprocal sum. -/
theorem exists_maximizing_subset (N : ℕ) :
    ∃ A : Finset ℕ,
      admissibleWithin N A ∧
      ∀ B : Finset ℕ,
        admissibleWithin N B →
        normalizedReciprocalSum N B ≤ normalizedReciprocalSum N A := by
  obtain ⟨A, hA, hmax⟩ :=
    (admissibleSubsets N).exists_max_image (normalizedReciprocalSum N)
      (admissibleSubsets_nonempty N)
  refine ⟨A, mem_admissibleSubsets_iff.mp hA, ?_⟩
  intro B hB
  exact hmax B (mem_admissibleSubsets_iff.mpr hB)

/-- A chosen maximizing admissible subset of `{1, ..., N}`. -/
def maximizingSubset (N : ℕ) : Finset ℕ :=
  Classical.choose (exists_maximizing_subset N)

theorem maximizingSubset_spec (N : ℕ) :
    admissibleWithin N (maximizingSubset N) ∧
      ∀ B : Finset ℕ,
        admissibleWithin N B →
        normalizedReciprocalSum N B ≤ normalizedReciprocalSum N (maximizingSubset N) :=
  Classical.choose_spec (exists_maximizing_subset N)

/-- The maximum of `(1 / log N) * ∑_{a ∈ A} 1/a` over admissible subsets of
`{1,...,N}`. -/
def maxNormalizedReciprocalSum (N : ℕ) : ℝ :=
  normalizedReciprocalSum N (maximizingSubset N)

theorem le_maxNormalizedReciprocalSum {N : ℕ} {A : Finset ℕ}
    (hA : admissibleWithin N A) :
    normalizedReciprocalSum N A ≤ maxNormalizedReciprocalSum N :=
  (maximizingSubset_spec N).2 A hA

theorem exists_subset_realizing_max (N : ℕ) :
    ∃ A : Finset ℕ,
      admissibleWithin N A ∧
      normalizedReciprocalSum N A = maxNormalizedReciprocalSum N ∧
      ∀ B : Finset ℕ,
        admissibleWithin N B →
        normalizedReciprocalSum N B ≤ maxNormalizedReciprocalSum N := by
  refine ⟨maximizingSubset N, (maximizingSubset_spec N).1, rfl, ?_⟩
  intro B hB
  exact (maximizingSubset_spec N).2 B hB

theorem reciprocalSum_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    reciprocalSum A ≤ reciprocalSum B := by
  unfold reciprocalSum
  refine Finset.sum_le_sum_of_subset_of_nonneg hAB ?_
  intro x _ _
  positivity

theorem normalizedReciprocalSum_le_Icc {N : ℕ} (hN : 1 < N) {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) :
    normalizedReciprocalSum N A ≤ normalizedReciprocalSum N (Finset.Icc 1 N) := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hcoeff : 0 ≤ 1 / Real.log (N : ℝ) := by positivity
  unfold normalizedReciprocalSum
  exact mul_le_mul_of_nonneg_left (reciprocalSum_mono hA) hcoeff

theorem zero_le_maxNormalizedReciprocalSum (N : ℕ) :
    0 ≤ maxNormalizedReciprocalSum N := by
  have hEmpty : admissibleWithin N (∅ : Finset ℕ) := by
    refine ⟨Finset.empty_subset _, ?_⟩
    intro a b ha _ _
    exact absurd ha (Finset.notMem_empty a)
  have hle := le_maxNormalizedReciprocalSum hEmpty
  simpa [normalizedReciprocalSum, reciprocalSum] using hle

theorem one_div_log_le_maxNormalizedReciprocalSum {N : ℕ} (hN : 1 < N) :
    (1 / Real.log (N : ℝ)) ≤ maxNormalizedReciprocalSum N := by
  have hOne : admissibleWithin N ({1} : Finset ℕ) :=
    singleton_one_admissibleWithin (le_of_lt hN)
  have hle := le_maxNormalizedReciprocalSum hOne
  simpa [normalizedReciprocalSum, reciprocalSum] using hle

theorem maxNormalizedReciprocalSum_le_Icc {N : ℕ} (hN : 1 < N) :
    maxNormalizedReciprocalSum N ≤ normalizedReciprocalSum N (Finset.Icc 1 N) :=
  normalizedReciprocalSum_le_Icc hN (maximizingSubset_spec N).1.1

/-- The analytic function `Φ` from the proof sketch.
For `u ∈ [1/4, 1/3)`:
`Φ(u) = log((1-u)/u) + ∫_u^{(1-u)/2} (1/v) · log((1-u-v)/v) dv`.
For `u ∈ [1/3, 1/2]`:
`Φ(u) = log((1-u)/u)`. -/
def Phi (u : ℝ) : ℝ :=
  Real.log ((1 - u) / u) +
    (if u < (1 : ℝ) / 3 then
      ∫ v in u..((1 - u) / 2), (1 / v) * Real.log ((1 - u - v) / v)
    else
      0)

/-- The set of roots of `Φ(u) = 1` in `[1/4, 1/3]`. -/
def alpha2RootSet : Set ℝ :=
  {u : ℝ | (1 : ℝ) / 4 ≤ u ∧ u ≤ (1 : ℝ) / 3 ∧ Phi u = 1}

/-- The cutoff exponent `α_2` from the proof sketch: the unique root of
`Φ(u) = 1` in `(1/4, 1/3)`, taken here as the infimum of the root set.
The proof sketch asserts (but does not prove here) that this set is a
singleton, in which case `sInf` agrees with "the unique root". -/
def alpha2 : ℝ :=
  sInf alpha2RootSet

/-- Existence/uniqueness of `α_2`, asserted by the proof sketch and required
for `c_2` to denote the conjectured constant. -/
def Alpha2ExistsUnique : Prop :=
  ∃! u : ℝ, (1 : ℝ) / 4 ≤ u ∧ u ≤ (1 : ℝ) / 3 ∧ Phi u = 1

/-- The conjectured asymptotic constant
`c_2 = 1/2 + ∫_{α_2}^{1/2} (1 - Φ(u)) du ≈ 0.6187712111`. -/
def c2 : ℝ :=
  (1 : ℝ) / 2 + ∫ u in alpha2..((1 : ℝ) / 2), (1 - Phi u)

/-- The Poindexter / Erdős #858 conjecture: the maximum of
`(1 / log N) · ∑_{a ∈ A} 1/a` over admissible subsets `A ⊆ {1,...,N}`
tends to the analytic constant `c_2` as `N → ∞`. -/
def PoindexterConjecture : Prop :=
  Tendsto (fun N : ℕ => maxNormalizedReciprocalSum N) atTop (𝓝 c2)

end PoindexterErdos858

end