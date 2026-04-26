-- CANNOT_FORMALIZE_EXACTLY: The finiteness of unitary perfect numbers is an open
-- problem (OEIS A002827); only five examples are known as of 2026-04-25 and no
-- proof of finiteness exists. We therefore formalize the *statement* of the
-- conjecture exactly, prove the equivalence between the literal definition
-- ("sum of proper unitary divisors equals n") and the standard reformulation
-- ("σ*(n) = 2n"), and verify a sanity check (6 is unitary perfect). We do not
-- prove the conjecture itself.
import Mathlib

open scoped BigOperators

namespace UnitaryPerfect

/-- A positive divisor `d` of `n` is a *unitary divisor* if `d` and `n / d`
are coprime. -/
def IsUnitaryDivisor (d n : ℕ) : Prop :=
  0 < n ∧ d ∣ n ∧ Nat.Coprime d (n / d)

/-- The finset of unitary divisors of `n` (including `n` itself when `0 < n`). -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => Nat.Coprime d (n / d)

/-- The finset of *proper* unitary divisors of `n`, i.e. unitary divisors
strictly less than `n`. -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  n.properDivisors.filter fun d => Nat.Coprime d (n / d)

/-- `σ*(n)`: the sum of all unitary divisors of `n`. -/
def sigmaStar (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

/-- The literal definition: `n` is *unitary perfect* iff it equals the sum of
its unitary divisors other than `n` itself. -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  0 < n ∧ ∑ d ∈ properUnitaryDivisors n, d = n

theorem mem_unitaryDivisors_iff {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ IsUnitaryDivisor d n := by
  unfold unitaryDivisors IsUnitaryDivisor
  constructor
  · intro hd
    rcases Finset.mem_filter.mp hd with ⟨hmem, hcop⟩
    refine ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hmem),
            Nat.dvd_of_mem_divisors hmem, hcop⟩
  · rintro ⟨hn, hdvd, hcop⟩
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, hn.ne'⟩, hcop⟩

theorem mem_properUnitaryDivisors_iff {n d : ℕ} :
    d ∈ properUnitaryDivisors n ↔ d ∣ n ∧ d < n ∧ Nat.Coprime d (n / d) := by
  simp [properUnitaryDivisors, Nat.mem_properDivisors, and_assoc]

/-- For `0 < n`, the unitary divisors decompose as the proper unitary divisors
together with `n` itself (since `gcd n 1 = 1`). -/
theorem unitaryDivisors_eq_insert {n : ℕ} (hn : 0 < n) :
    unitaryDivisors n = insert n (properUnitaryDivisors n) := by
  ext d
  simp only [unitaryDivisors, properUnitaryDivisors, Finset.mem_insert,
             Finset.mem_filter, Nat.mem_divisors, Nat.mem_properDivisors]
  constructor
  · rintro ⟨⟨hdvd, hne⟩, hcop⟩
    rcases lt_or_eq_of_le (Nat.le_of_dvd hn hdvd) with hlt | heq
    · exact Or.inr ⟨⟨hdvd, hlt⟩, hcop⟩
    · exact Or.inl heq
  · rintro (rfl | ⟨⟨hdvd, hlt⟩, hcop⟩)
    · refine ⟨⟨dvd_refl _, hn.ne'⟩, ?_⟩
      have : d / d = 1 := Nat.div_self hn
      simp [this]
    · exact ⟨⟨hdvd, hn.ne'⟩, hcop⟩

/-- Equivalence between the literal definition of unitary perfectness and the
standard formulation `σ*(n) = 2n`. -/
theorem isUnitaryPerfect_iff_sigmaStar {n : ℕ} :
    IsUnitaryPerfect n ↔ 0 < n ∧ sigmaStar n = 2 * n := by
  unfold IsUnitaryPerfect sigmaStar
  refine ⟨?_, ?_⟩
  · rintro ⟨hn, hsum⟩
    refine ⟨hn, ?_⟩
    rw [unitaryDivisors_eq_insert hn]
    have hnot : n ∉ properUnitaryDivisors n := by
      simp [properUnitaryDivisors, Nat.mem_properDivisors]
    rw [Finset.sum_insert hnot, hsum, two_mul]
  · rintro ⟨hn, hsum⟩
    refine ⟨hn, ?_⟩
    rw [unitaryDivisors_eq_insert hn] at hsum
    have hnot : n ∉ properUnitaryDivisors n := by
      simp [properUnitaryDivisors, Nat.mem_properDivisors]
    rw [Finset.sum_insert hnot, two_mul] at hsum
    exact Nat.add_left_cancel hsum

/-- Sanity check: `6` is a unitary perfect number. Its proper unitary divisors
are `1, 2, 3` (note `6/6 = 1` excludes `6`; `gcd(2,3) = 1`, `gcd(3,2) = 1`,
`gcd(1,6) = 1`), summing to `6`. -/
theorem six_isUnitaryPerfect : IsUnitaryPerfect 6 := by
  refine ⟨by decide, ?_⟩
  decide

/-- **Conjecture (Poindexter).** There are only finitely many unitary perfect
numbers. As of 2026-04-25 this is an open problem; the only known examples are
`6, 60, 90, 87360, 146361946186458562560000`. We record the statement as a
`Prop` without proof. -/
def UnitaryPerfectFinitenessConjecture : Prop :=
  Set.Finite {n : ℕ | IsUnitaryPerfect n}

end UnitaryPerfect