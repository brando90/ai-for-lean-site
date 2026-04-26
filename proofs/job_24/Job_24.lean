-- CANNOT_FORMALIZE_EXACTLY: The conjecture has two parts: (A) gcd(a_n, L_n) = 1 for infinitely many n, and (B) gcd(a_n, L_n) > 1 for infinitely many n. Part (A) is equivalent to a well-known open problem (Shiu's conjecture that the reduced denominator of H_n equals lcm(1,...,n) infinitely often); hence a complete proof of the full conjecture is not currently known. Below we faithfully state the full conjecture as `PoindexterConjecture`, prove that the integer `harmonicNumer n / lcmUpTo n` really equals the n-th harmonic number in ℚ (so the setup is faithful), and prove part (B) via the 3-adic cancellation argument on `n = 2·3^(k+1)` from the proof sketch.

import Mathlib

open scoped BigOperators

namespace PoindexterHarmonic

/-- `L n = lcm(1, 2, …, n)`, defined via `Finset.lcm`. -/
def lcmUpTo (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

/-- The numerator `a_n = ∑_{k=1}^n L_n / k`, an integer because each `1 ≤ k ≤ n`
divides `L_n`.  Then `a_n / L_n = H_n`. -/
def harmonicNumer (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, lcmUpTo n / k

/-- The `n`-th harmonic number, viewed as a rational number. -/
noncomputable def harmonicQ (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / k

lemma lcmUpTo_pos (n : ℕ) : 0 < lcmUpTo n := by
  suffices h : ∀ s : Finset ℕ, (∀ i ∈ s, 0 < i) → 0 < s.lcm id from
    h _ (fun i hi => (Finset.mem_Icc.mp hi).1)
  intro s hs
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.lcm_empty]
      exact Nat.one_pos
  | @insert a t hat ih =>
      have ha : 0 < a := hs a (Finset.mem_insert_self _ _)
      have ht : 0 < t.lcm id :=
        ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
      rw [Finset.lcm_insert]
      simp only [id_eq]
      rw [Nat.pos_iff_ne_zero]
      intro heq
      have heqn : Nat.lcm a (t.lcm id) = 0 := heq
      have hgl : Nat.gcd a (t.lcm id) * Nat.lcm a (t.lcm id) = a * t.lcm id :=
        Nat.gcd_mul_lcm a (t.lcm id)
      rw [heqn, Nat.mul_zero] at hgl
      rcases Nat.mul_eq_zero.mp hgl.symm with h | h
      · exact ha.ne' h
      · exact ht.ne' h

lemma dvd_lcmUpTo {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) : k ∣ lcmUpTo n := by
  have hmem : k ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hk1, hkn⟩
  simpa [lcmUpTo] using Finset.dvd_lcm (s := Finset.Icc 1 n) (f := id) hmem

/-- Bridge lemma: `harmonicNumer n / lcmUpTo n = H_n` as rationals. -/
theorem harmonicNumer_div_lcmUpTo_eq_harmonicQ (n : ℕ) :
    (harmonicNumer n : ℚ) / lcmUpTo n = harmonicQ n := by
  rw [harmonicNumer, harmonicQ, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
  have hkq0 : (k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk1))
  have hLq0 : (lcmUpTo n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lcmUpTo_pos n))
  have hdvd : k ∣ lcmUpTo n := dvd_lcmUpTo hk1 hkn
  rw [Nat.cast_div hdvd hkq0]
  field_simp

/-- The full conjecture as stated: for positive integers `n`, both
"`a_n` coprime to `L_n`" and "`gcd(a_n, L_n) > 1`" occur for infinitely many `n`. -/
def PoindexterConjecture : Prop :=
  Set.Infinite {n : ℕ | 0 < n ∧ Nat.Coprime (harmonicNumer n) (lcmUpTo n)} ∧
    Set.Infinite {n : ℕ | 0 < n ∧ 1 < Nat.gcd (harmonicNumer n) (lcmUpTo n)}

/-- For each `k ≥ 0`, the index `n = 2 · 3^(k+1)` produces a witness with
`gcd(a_n, L_n) > 1`.  Proof via the 3-adic cancellation argument from the sketch. -/
lemma gcd_gt_one_family (k : ℕ) :
    1 < Nat.gcd (harmonicNumer (2 * 3 ^ (k + 1))) (lcmUpTo (2 * 3 ^ (k + 1))) := by
  set p : ℕ := 3 ^ (k + 1) with hp_def
  set n : ℕ := 2 * p with hn_def
  set L : ℕ := lcmUpTo n with hL_def
  have hp_pos : 0 < p := by
    simp [hp_def]
  have hn_pos : 0 < n := by
    simp only [hn_def]; positivity
  have hp_le_n : p ≤ n := by
    simp only [hn_def]; nlinarith
  have hp_mem : p ∈ Finset.Icc 1 n :=
    Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hp_pos, hp_le_n⟩
  have hn_mem : n ∈ Finset.Icc 1 n :=
    Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hn_pos, le_rfl⟩
  have hp_ne_n : p ≠ n := by
    have hn_eq : n = 2 * p := hn_def
    omega
  have hp_dvd_L : p ∣ L :=
    dvd_lcmUpTo (Nat.succ_le_of_lt hp_pos) hp_le_n
  have hn_dvd_L : n ∣ L :=
    dvd_lcmUpTo (Nat.succ_le_of_lt hn_pos) le_rfl
  have hpair_eq : L / p + L / n = 3 * (L / n) := by
    obtain ⟨m, hm⟩ := hn_dvd_L
    have hdiv_n : L / n = m :=
      Nat.div_eq_of_eq_mul_left hn_pos (by simpa [Nat.mul_comm] using hm)
    have hdiv_p : L / p = 2 * m := by
      refine Nat.div_eq_of_eq_mul_left hp_pos ?_
      calc
        L = n * m := hm
        _ = (2 * m) * p := by rw [hn_def]; ring
    rw [hdiv_p, hdiv_n]; omega
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
    have hj_lo : 1 ≤ j := (Finset.mem_Icc.mp hj_mem).1
    have hj_hi : j ≤ n := (Finset.mem_Icc.mp hj_mem).2
    have hj_pos : 0 < j := hj_lo
    have hj_dvd_L : j ∣ L := dvd_lcmUpTo hj_lo hj_hi
    have hnot_p_dvd_j : ¬ p ∣ j := by
      intro hpj
      obtain ⟨m, hm⟩ := hpj
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with hm0 | hm0
        · exact absurd (by simp [hm, hm0] : j = 0) hj_pos.ne'
        · exact hm0
      have hm_le_two : m ≤ 2 := by
        have hmul : p * m ≤ p * 2 := by
          have : j ≤ 2 * p := hj_hi
          simpa [hm, Nat.mul_comm] using this
        exact Nat.le_of_mul_le_mul_left hmul hp_pos
      interval_cases m
      · exact hj_ne_p (by simp [hm])
      · exact hj_ne_n (by simp [hm, hn_def, Nat.mul_comm])
    have hterm_dvd : 3 ∣ L / j := by
      by_contra hnot
      have hj_mul : j * (L / j) = L := Nat.mul_div_cancel' hj_dvd_L
      have hpow_mul : p ∣ j * (L / j) := by rw [hj_mul]; exact hp_dvd_L
      have hprime : Prime (3 : ℕ) := Nat.prime_iff.mp Nat.prime_three
      have hpow_j : p ∣ j := by
        have := hprime.pow_dvd_of_dvd_mul_right (k + 1) hnot hpow_mul
        simpa [hp_def] using this
      exact hnot_p_dvd_j hpow_j
    exact hterm_dvd
  have hs_p :
      ∑ j ∈ Finset.Icc 1 n, L / j =
        L / p + ∑ j ∈ (Finset.Icc 1 n).erase p, L / j := by
    simpa [add_comm] using
      (Finset.sum_erase_add (s := Finset.Icc 1 n) (a := p)
        (f := fun j => L / j) hp_mem).symm
  have hn_mem_erase : n ∈ (Finset.Icc 1 n).erase p := by
    have hn_ne_p : n ≠ p := fun h => hp_ne_n h.symm
    simp [hn_mem, hn_ne_p]
  have hs_n :
      ∑ j ∈ (Finset.Icc 1 n).erase p, L / j =
        L / n + ∑ j ∈ ((Finset.Icc 1 n).erase p).erase n, L / j := by
    simpa [add_comm] using
      (Finset.sum_erase_add (s := (Finset.Icc 1 n).erase p) (a := n)
        (f := fun j => L / j) hn_mem_erase).symm
  have hthree_dvd_a : 3 ∣ harmonicNumer n := by
    show 3 ∣ ∑ k ∈ Finset.Icc 1 n, lcmUpTo n / k
    have hL_eq : lcmUpTo n = L := rfl
    rw [hL_eq, hs_p, hs_n]
    have h1 : 3 ∣ (L / p + L / n) +
        ∑ j ∈ ((Finset.Icc 1 n).erase p).erase n, L / j :=
      dvd_add hpair_dvd hrest_dvd
    simpa [add_assoc] using h1
  have hthree_dvd_L : 3 ∣ L :=
    (dvd_pow_self 3 (Nat.succ_ne_zero k)).trans hp_dvd_L
  have hthree_dvd_gcd : 3 ∣ Nat.gcd (harmonicNumer n) L :=
    Nat.dvd_gcd hthree_dvd_a hthree_dvd_L
  have hgcd_pos : 0 < Nat.gcd (harmonicNumer n) L :=
    Nat.gcd_pos_of_pos_right _ (lcmUpTo_pos n)
  have hge : 3 ≤ Nat.gcd (harmonicNumer n) L :=
    Nat.le_of_dvd hgcd_pos hthree_dvd_gcd
  have hfinal : 1 < Nat.gcd (harmonicNumer n) L := by omega
  simpa [hn_def, hp_def, hL_def] using hfinal

/-- Part (B) of the conjecture: `gcd(a_n, L_n) > 1` for infinitely many positive `n`. -/
theorem infinitely_many_gcd_gt_one :
    Set.Infinite {n : ℕ | 0 < n ∧ 1 < Nat.gcd (harmonicNumer n) (lcmUpTo n)} := by
  refine (Set.infinite_range_of_injective
      (f := fun k : ℕ => 2 * 3 ^ (k + 1)) ?_).mono ?_
  · intro a b hab
    have hpow : 3 ^ (a + 1) = 3 ^ (b + 1) := by nlinarith
    have h := (Nat.pow_right_injective (by decide : 2 ≤ 3)) hpow
    exact Nat.succ.inj h
  · rintro n ⟨k, rfl⟩
    refine ⟨by positivity, gcd_gt_one_family k⟩

end PoindexterHarmonic