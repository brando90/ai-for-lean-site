import Mathlib

open scoped BigOperators

/-!
# Poindexter's Harmonic gcd Conjecture

For each `n ≥ 1`, let `L_n = lcm(1,…,n)` and let `a_n` be the integer such that
`a_n / L_n = H_n` (the `n`-th harmonic number). The conjecture asserts that
each of the following holds for infinitely many `n`:

1. `gcd(a_n, L_n) = 1` — OPEN, related to the Eswarathasan–Levine problem (1991).
2. `gcd(a_n, L_n) > 1` — proved here unconditionally.
-/

namespace PoindexterHarmonic

/-- The `n`-th harmonic number, viewed as a rational number. -/
noncomputable def harmonicQ (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / k

/-- `L_n = lcm(1, 2, …, n)`. -/
def lcmUpTo : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (lcmUpTo n) (n + 1)

/-- `a_n = ∑_{k=1}^n L_n / k`. -/
def harmonicNumer (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, lcmUpTo n / k

lemma lcmUpTo_pos (n : ℕ) : 0 < lcmUpTo n := by
  induction n with
  | zero => simp [lcmUpTo]
  | succ n ih =>
      simpa [lcmUpTo] using Nat.lcm_pos ih (Nat.succ_pos n)

lemma dvd_lcmUpTo {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) : k ∣ lcmUpTo n := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      by_cases h : k = n + 1
      · simpa [lcmUpTo, h] using Nat.dvd_lcm_right (lcmUpTo n) (n + 1)
      · have hkn' : k ≤ n := by omega
        exact (ih hk1 hkn').trans (Nat.dvd_lcm_left (lcmUpTo n) (n + 1))

/-- The defining identity: `a_n / L_n = H_n` as rationals. -/
theorem harmonicNumer_spec (n : ℕ) :
    (harmonicNumer n : ℚ) / lcmUpTo n = harmonicQ n := by
  unfold harmonicNumer harmonicQ
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
  have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk1
  have hkq0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk_ne
  have hL_ne : lcmUpTo n ≠ 0 := Nat.pos_iff_ne_zero.mp (lcmUpTo_pos n)
  have hLq0 : (lcmUpTo n : ℚ) ≠ 0 := by exact_mod_cast hL_ne
  have hdvd : k ∣ lcmUpTo n := dvd_lcmUpTo hk1 hkn
  rw [Nat.cast_div hdvd hkq0]
  field_simp

/-- The exact natural-language conjecture. -/
def PoindexterConjecture : Prop :=
  Set.Infinite {n : ℕ | 0 < n ∧ Nat.Coprime (harmonicNumer n) (lcmUpTo n)} ∧
    Set.Infinite {n : ℕ | 0 < n ∧ 1 < Nat.gcd (harmonicNumer n) (lcmUpTo n)}

/-- For every `k`, the integer `n = 2 · 3^(k+1)` satisfies `gcd(a_n, L_n) > 1`. -/
lemma gcd_gt_one_family (k : ℕ) :
    1 < Nat.gcd (harmonicNumer (2 * 3 ^ (k + 1))) (lcmUpTo (2 * 3 ^ (k + 1))) := by
  set p : ℕ := 3 ^ (k + 1) with hp_def
  set n : ℕ := 2 * p with hn_def
  set L : ℕ := lcmUpTo n with hL_def
  have hp_pos : 0 < p := by rw [hp_def]; positivity
  have hn_pos : 0 < n := by
    rw [hn_def]; exact Nat.mul_pos (by norm_num) hp_pos
  have hp_le_n : p ≤ n := by rw [hn_def]; linarith
  have hp_mem : p ∈ Finset.Icc 1 n :=
    Finset.mem_Icc.mpr ⟨hp_pos, hp_le_n⟩
  have hn_mem : n ∈ Finset.Icc 1 n :=
    Finset.mem_Icc.mpr ⟨hn_pos, le_rfl⟩
  have hp_ne_n : p ≠ n := by rw [hn_def]; intro h; linarith
  have hp_dvd_L : p ∣ L := dvd_lcmUpTo hp_pos hp_le_n
  have hn_dvd_L : n ∣ L := dvd_lcmUpTo hn_pos le_rfl
  have hpair_eq : L / p + L / n = 3 * (L / n) := by
    obtain ⟨m, hm⟩ := hn_dvd_L
    have hLnm : L = m * n := by rw [hm]; ring
    have hL2mp : L = (2 * m) * p := by rw [hm, hn_def]; ring
    have hdiv_n : L / n = m := by
      rw [hLnm]; exact Nat.mul_div_cancel m hn_pos
    have hdiv_p : L / p = 2 * m := by
      rw [hL2mp]; exact Nat.mul_div_cancel (2 * m) hp_pos
    rw [hdiv_p, hdiv_n]; ring
  have hpair_dvd : 3 ∣ L / p + L / n := by
    rw [hpair_eq]; exact dvd_mul_right 3 (L / n)
  have hrest_dvd : 3 ∣ ∑ j ∈ ((Finset.Icc 1 n).erase p).erase n, L / j := by
    refine Finset.dvd_sum ?_
    intro j hj
    have hj_mem : j ∈ Finset.Icc 1 n :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj)
    have hj_ne_p : j ≠ p :=
      Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
    have hj_ne_n : j ≠ n := Finset.ne_of_mem_erase hj
    have hj_dvd_L : j ∣ L :=
      dvd_lcmUpTo (Finset.mem_Icc.mp hj_mem).1 (Finset.mem_Icc.mp hj_mem).2
    have hnot_p_dvd_j : ¬ p ∣ j := by
      intro hpj
      obtain ⟨m, hm⟩ := hpj
      have hj_pos : 0 < j :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hj_mem).1
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · exfalso
          rw [hm, h0, Nat.mul_zero] at hj_pos
          exact lt_irrefl 0 hj_pos
        · exact hpos
      have hm_le_two : m ≤ 2 := by
        have hjle : j ≤ n := (Finset.mem_Icc.mp hj_mem).2
        rw [hm, hn_def] at hjle
        have hp1 : 1 ≤ p := hp_pos
        nlinarith
      interval_cases m
      · exact hj_ne_p (by rw [hm]; ring)
      · exact hj_ne_n (by rw [hm, hn_def]; ring)
    have hterm_dvd : 3 ∣ L / j := by
      by_contra hnot
      have hpow_mul : p ∣ j * (L / j) := by
        rw [Nat.mul_div_cancel' hj_dvd_L]
        exact hp_dvd_L
      have h3cop : Nat.Coprime 3 (L / j) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnot
      have hpcop : Nat.Coprime p (L / j) := by
        rw [hp_def]
        exact Nat.Coprime.pow_left (k + 1) h3cop
      exact hnot_p_dvd_j (hpcop.dvd_of_dvd_mul_right hpow_mul)
    exact hterm_dvd
  have hs_p :
      ∑ j ∈ Finset.Icc 1 n, L / j =
        L / p + ∑ j ∈ (Finset.Icc 1 n).erase p, L / j := by
    rw [← Finset.sum_erase_add (Finset.Icc 1 n) (fun j => L / j) hp_mem]
    ring
  have hn_mem_erase : n ∈ (Finset.Icc 1 n).erase p :=
    Finset.mem_erase.mpr ⟨fun h => hp_ne_n h.symm, hn_mem⟩
  have hs_n :
      ∑ j ∈ (Finset.Icc 1 n).erase p, L / j =
        L / n + ∑ j ∈ ((Finset.Icc 1 n).erase p).erase n, L / j := by
    rw [← Finset.sum_erase_add ((Finset.Icc 1 n).erase p)
          (fun j => L / j) hn_mem_erase]
    ring
  have hthree_dvd_a : 3 ∣ harmonicNumer n := by
    show 3 ∣ ∑ k ∈ Finset.Icc 1 n, L / k
    rw [hs_p, hs_n, ← add_assoc]
    exact Nat.dvd_add hpair_dvd hrest_dvd
  have hthree_dvd_p : 3 ∣ p := by
    rw [hp_def]; exact dvd_pow_self 3 (Nat.succ_ne_zero k)
  have hthree_dvd_L : 3 ∣ L := hthree_dvd_p.trans hp_dvd_L
  have hthree_dvd_gcd : 3 ∣ Nat.gcd (harmonicNumer n) L :=
    Nat.dvd_gcd hthree_dvd_a hthree_dvd_L
  have hgcd_pos : 0 < Nat.gcd (harmonicNumer n) L :=
    Nat.gcd_pos_of_pos_right _ (lcmUpTo_pos n)
  have hge : 3 ≤ Nat.gcd (harmonicNumer n) L :=
    Nat.le_of_dvd hgcd_pos hthree_dvd_gcd
  omega

/-- Part (2) of the conjecture: there are infinitely many positive integers `n`
    for which `gcd(a_n, L_n) > 1`. -/
theorem infinitely_many_gcd_gt_one :
    Set.Infinite {n : ℕ | 0 < n ∧ 1 < Nat.gcd (harmonicNumer n) (lcmUpTo n)} := by
  refine (Set.infinite_range_of_injective
    (f := fun k : ℕ => 2 * 3 ^ (k + 1)) ?_).mono ?_
  · intro a b hab
    simp only at hab
    have hpow : 3 ^ (a + 1) = 3 ^ (b + 1) :=
      Nat.eq_of_mul_eq_mul_left (by norm_num : (0:ℕ) < 2) hab
    have heq : a + 1 = b + 1 :=
      Nat.pow_right_injective (by decide : 2 ≤ 3) hpow
    omega
  · rintro n ⟨k, rfl⟩
    exact ⟨by positivity, gcd_gt_one_family k⟩

/-- The Poindexter conjecture follows from a proof of Part (1). -/
theorem poindexterConjecture_of_infinitely_many_coprime
    (h : Set.Infinite {n : ℕ | 0 < n ∧ Nat.Coprime (harmonicNumer n) (lcmUpTo n)}) :
    PoindexterConjecture :=
  ⟨h, infinitely_many_gcd_gt_one⟩

end PoindexterHarmonic